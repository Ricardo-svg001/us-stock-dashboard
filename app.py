#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""美股咖啡館 US Stock Coffee — 強勢股與拉回選股（資料層＋篩選邏輯）

架構刻意與台股版對齊，方便日後兩邊互相移植：
  · 單一 Flask 檔 + 內嵌前端（前端稍後補）
  · 檔案快取 _load_cache / _save_cache，帶 TTL
  · 背景 JOBS + 輪詢，避免長時間請求卡住

資料來源（皆免費、免金鑰，各自封裝成獨立函式，日後要換來源只改那一支）：
  · 股票清單／市值／產業 → Nasdaq 官方篩選器 API
  · 每日收盤價           → Stooq CSV

均線採美股習慣：10 / 20 / 50 / 150
  50MA  ≈ 台股季線的地位
  150MA 用來看中長期趨勢（歐尼爾／Minervini 的趨勢模板也用這條）
"""

import csv
import hashlib
import hmac
import io
import json
import math
import os
import re
import threading
import time
import uuid
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta, timezone
from urllib.parse import quote

import requests
from flask import Flask, jsonify, request, render_template_string

# ---------------------------------------------------------------- 基本設定

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
CACHE_DIR = os.environ.get("CACHE_DIR") or os.path.join(BASE_DIR, "cache")
os.makedirs(CACHE_DIR, exist_ok=True)

# 清掉先前異常中斷留下的暫存檔（舊版共用檔名時會留下垃圾）
for _f in os.listdir(CACHE_DIR):
    if _f.endswith(".tmp"):
        try:
            os.remove(os.path.join(CACHE_DIR, _f))
        except Exception:
            pass

HEADERS = {
    "User-Agent": ("Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
                   "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0 Safari/537.36"),
    "Accept": "application/json, text/plain, */*",
    "Accept-Language": "en-US,en;q=0.9",
}

# 美股均線組合。改這裡即可，align_label 與前端選項都跟著走。
MA_SET = (10, 20, 50, 150)
MA_NAMES = {10: "10-day", 20: "20-day", 50: "50-day", 150: "150-day"}
MA_NAMES_ZH = {10: "10日線", 20: "20日線", 50: "50日線", 150: "150日線"}

# 要保留幾個交易日的歷史。
# 3 年 ≈ 756 個交易日 —— 支援到「3 年新高」，也涵蓋所有均線需求。
# ⚠️ 加大這個值只影響「第一次抓取」；之後每天只補新的交易日（見 get_history）。
HIST_DAYS = 780


# ---------------------------------------------------------------- 中文對照

# 產業與公司名稱的中英對照。放在外部 JSON，改完重啟即可，不必動程式。
# 找不到對照就回退英文原名 —— 不會空白，也不會擋住新上市的公司。
TRANS_FILE = os.path.join(BASE_DIR, "translations.json")
_TRANS = {"sectors": {}, "companies": {}}


def load_translations():
    global _TRANS
    try:
        with open(TRANS_FILE, "r", encoding="utf-8") as f:
            d = json.load(f)
        _TRANS = {"sectors": d.get("sectors") or {},
                  "companies": d.get("companies") or {}}
    except Exception:
        _TRANS = {"sectors": {}, "companies": {}}
    return _TRANS


def zh_sector(en):
    return _TRANS["sectors"].get(en) or en


def zh_company(symbol, en):
    return _TRANS["companies"].get(symbol.upper()) or en


load_translations()


# ---------------------------------------------------------------- 快取

def _load_cache(name, max_age_hours):
    """max_age_hours=None 表示不管多舊都讀出來（增量更新時要拿舊資料來接）。"""
    p = os.path.join(CACHE_DIR, name)
    if not os.path.exists(p):
        return None
    if max_age_hours is None or time.time() - os.path.getmtime(p) < max_age_hours * 3600:
        try:
            with open(p, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            return None
    return None


def _save_cache(name, data):
    """原子寫入快取。

    ⚠️ **暫存檔名必須唯一**。背景預抓與使用者的篩選可能同時處理同一檔股票
    （兩邊都會呼叫 get_history / get_fundamentals），若共用 `name + ".tmp"`，
    先完成的那個會把暫存檔 rename 走，後完成的 `os.replace` 就會丟
    `FileNotFoundError: … fund_KO.json.tmp -> fund_KO.json`，整個篩選失敗。
    加上 uuid 讓每次寫入有自己的暫存檔，就不會互相搶。
    """
    dst = os.path.join(CACHE_DIR, name)
    tmp = "%s.%s.tmp" % (dst, uuid.uuid4().hex[:8])
    try:
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False)
        os.replace(tmp, dst)
    except Exception:
        # 寫快取失敗不該讓整個篩選壞掉 —— 下次再抓就好
        try:
            os.remove(tmp)
        except Exception:
            pass


# 同一檔股票可能被「背景預抓」與「使用者篩選」同時要求。
# 讓第一個進來的去抓，其他人等它抓完再讀快取 —— 省掉一半的網路請求，
# 也避免對 Nasdaq 造成不必要的壓力。
_INFLIGHT = {}
_INFLIGHT_LOCK = threading.Lock()


def _fetch_once(key, fetch, read_cache):
    """key 相同時只執行一次 fetch()；後到的執行緒等完再讀快取。"""
    with _INFLIGHT_LOCK:
        ev = _INFLIGHT.get(key)
        first = ev is None
        if first:
            ev = threading.Event()
            _INFLIGHT[key] = ev

    if not first:
        ev.wait(timeout=90)
        cached = read_cache()
        if cached is not None:
            return cached
        # 對方失敗或逾時，自己再試一次
    try:
        return fetch()
    finally:
        if first:
            with _INFLIGHT_LOCK:
                _INFLIGHT.pop(key, None)
            ev.set()


def _clear_cache(name):
    try:
        os.remove(os.path.join(CACHE_DIR, name))
    except Exception:
        pass


# ---------------------------------------------------------------- 網路

def _get(url, timeout=30, tries=3, wait=1.2):
    """帶重試的 GET，回傳 requests.Response；全部失敗才拋出。"""
    last = None
    for i in range(tries):
        try:
            r = requests.get(url, headers=HEADERS, timeout=timeout)
            r.raise_for_status()
            return r
        except Exception as e:
            last = e
            if i < tries - 1:
                time.sleep(wait * (i + 1))
    raise last


def _utcnow():
    """現在時刻，**帶時區的 UTC**。

    ⚠️ 不要用 `datetime.utcnow()`。它回傳的是 naive datetime，
    「代表 UTC」只存在於命名，物件本身不知道自己是什麼時區。
    後果是 `.timestamp()` 會被當成本地時間換算（台灣差 8 小時），
    跟 `datetime.now()` 比較也會**安靜地算錯**而不是報錯。
    Python 3.12 起已標記 deprecated，未來會移除。

    ⚠️ 換成 aware 之後，**全檔都必須一致**。混用 naive 與 aware 會丟
    `TypeError: can't compare offset-naive and offset-aware datetimes`。
    特別注意 `datetime(...)` 直接建構與 `strptime()` 預設都是 naive，
    要記得補 `tzinfo=timezone.utc`。
    """
    return datetime.now(timezone.utc)


def _num(x):
    """把 '$1,234.50'、'12.3%'、'--' 這類字串轉成 float，失敗回 None。"""
    if x is None:
        return None
    s = str(x).strip().replace(",", "").replace("$", "").replace("%", "")
    if s in ("", "--", "N/A", "NA", "nan"):
        return None
    try:
        return float(s)
    except ValueError:
        return None


# ---------------------------------------------------------------- 來源一：股票清單

NASDAQ_SCREENER = ("https://api.nasdaq.com/api/screener/stocks"
                   "?tableonly=true&limit=25000&offset=0&download=true")


def _pick(row, *names):
    """從 dict 取值，忽略大小寫與底線差異（Nasdaq 偶爾會改欄位名）。"""
    norm = {str(k).lower().replace("_", ""): v for k, v in row.items()}
    for n in names:
        v = norm.get(n.lower().replace("_", ""))
        if v not in (None, "", "--"):
            return v
    return None


# 非普通股的證券類型。這些不該進選股器，而且會嚴重污染市值排名 ——
# 例如 GOOGM 是 Alphabet 的特別股（5,918 億），等於把 Alphabet 重複計算一次。
_NOT_STOCK = ("preferred stock", "preferred shares", "notes due", "corporate units",
              "tangible equity unit", "zones", "perpetual", "mandatory convertible")


def _not_common_stock(name):
    """判斷是不是特別股／公司債／單位信託這類非普通股。

    ⚠️ 只看**括號外**的證券類型描述。因為外國股票的 ADR 常在括號裡寫
    「(Each repstg 500 Preferred shares)」—— 例如 ITUB（伊塔烏銀行），
    那是正常可交易的 ADR，不能濾掉。
    """
    t = re.sub(r"\([^)]*\)", " ", name).lower()
    return any(w in t for w in _NOT_STOCK)


def get_universe(n=500):
    """市值前 n 大的美股，回傳 [{symbol, name, mktcap, sector, industry, price}, …]。

    來源：Nasdaq 官方篩選器（涵蓋 NYSE / NASDAQ / AMEX）。
    已排除：市值缺漏、ETF/基金、含 '^' 或 '/' 的特殊代號。
    快取 12 小時（市值排名不需要更頻繁）。
    """
    cached = _load_cache("universe.json", 12)
    if cached is None:
        r = _get(NASDAQ_SCREENER, timeout=60)
        j = r.json()
        rows = (((j or {}).get("data") or {}).get("rows")
                or ((j or {}).get("data") or {}).get("table", {}).get("rows") or [])
        out = []
        for row in rows:
            sym = (_pick(row, "symbol") or "").strip().upper()
            cap = _num(_pick(row, "marketCap"))
            if not sym or not cap or cap <= 0:
                continue
            if any(c in sym for c in ("^", "/", " ", ".")):
                continue                      # 權證、指數等特殊代號
            name = (_pick(row, "name") or sym).strip()
            if any(w in name.lower() for w in (" etf", " fund", " trust ")):
                continue
            if _not_common_stock(name):
                continue
            out.append({
                "symbol": sym,
                "name": name,
                "mktcap": round(cap / 1e9, 2),          # 十億美元
                "sector": (_pick(row, "sector") or "—").strip(),
                "industry": (_pick(row, "industry") or "—").strip(),
                "price": _num(_pick(row, "lastsale")),
            })
        out.sort(key=lambda x: -x["mktcap"])
        cached = out[:1000]
        _save_cache("universe.json", cached)
    return cached[:n]


# ---------------------------------------------------------------- 來源二：日線收盤

STOOQ = "https://stooq.com/q/d/l/?s={sym}.us&i=d"
YAHOO = ("https://query{n}.finance.yahoo.com/v8/finance/chart/{sym}"
         "?range=2y&interval=1d")

# 最近一次成功的來源，供 /api/prefetch-status 顯示
LAST_SOURCE = {"name": None, "fails": 0, "incremental": False}


NASDAQ_HIST = ("https://api.nasdaq.com/api/quote/{sym}/historical"
               "?assetclass=stocks&fromdate={frm}&todate={to}&limit=9999")


def _hist_nasdaq(symbol, frm_date=None):
    """Nasdaq 官方歷史報價。

    與股票清單同一台主機——實測那台對我們沒有設限，所以列為首選。
    回傳格式：data.tradesTable.rows[]，日期是 MM/DD/YYYY、價格帶 $ 與逗號，
    且**由新到舊**排列，這裡會轉成由舊到新。

    frm_date（"YYYY-MM-DD"）只抓該日之後 —— 增量更新用，避免每天重抓三年份。
    """
    to = _utcnow()
    if frm_date:
        frm = datetime.strptime(frm_date, "%Y-%m-%d").replace(tzinfo=timezone.utc)
    else:
        frm = to - timedelta(days=int(HIST_DAYS * 1.5))   # 交易日換算日曆天
    j = _get(NASDAQ_HIST.format(sym=symbol.upper(),
                                frm=frm.strftime("%Y-%m-%d"),
                                to=to.strftime("%Y-%m-%d")), timeout=40, tries=2).json()
    tbl = ((j or {}).get("data") or {}).get("tradesTable") or {}
    raw = tbl.get("rows") or []
    if not raw:
        raise ValueError("沒有 tradesTable.rows（%s）" % str(j)[:80])
    rows = []
    for r in raw:
        d, c = (r.get("date") or "").strip(), _num(r.get("close"))
        if not d or c is None:
            continue
        try:                                   # MM/DD/YYYY → YYYY-MM-DD
            mm, dd, yy = d.split("/")
            rows.append(("%s-%s-%s" % (yy, mm, dd), c))
        except ValueError:
            continue
    rows.sort(key=lambda x: x[0])              # 由舊到新
    return rows


def _hist_stooq(symbol, frm_date=None):
    """Stooq CSV：Date,Open,High,Low,Close,Volume"""
    txt = _get(STOOQ.format(sym=symbol.lower()), timeout=25, tries=2).text
    if not txt.lstrip().lower().startswith("date"):
        raise ValueError("非 CSV 回應：%s" % txt[:80].replace("\n", " "))
    rows = []
    for rec in csv.DictReader(io.StringIO(txt)):
        d = (rec.get("Date") or "").strip()
        c = _num(rec.get("Close"))
        if d and c:
            rows.append((d, c))
    return rows


def _hist_yahoo(symbol, frm_date=None):
    """Yahoo Finance chart API：JSON，含時間戳與收盤價。"""
    last = None
    for n in (1, 2):                       # query1 擋了就換 query2
        try:
            j = _get(YAHOO.format(n=n, sym=symbol.upper()), timeout=25, tries=2).json()
            res = j["chart"]["result"][0]
            ts = res["timestamp"]
            q = res["indicators"]["quote"][0]["close"]
            rows = []
            for t, c in zip(ts, q):
                if c is None:
                    continue               # 停牌日
                rows.append((datetime.fromtimestamp(t, timezone.utc).strftime("%Y-%m-%d"),
                             float(c)))
            if rows:
                return rows
            raise ValueError("回應沒有收盤價")
        except Exception as e:
            last = e
    raise last


# 依序嘗試；哪個先成功就用哪個。要停用某個來源，把它從清單移除即可。
#
# 2026-07-30 實測：
#   nasdaq ✅ 可用（與股票清單同一台主機，沒有設限）
#   stooq  ❌ 回 JavaScript 反爬蟲挑戰頁，純 HTTP 過不了
#   yahoo  ❌ 未帶 cookie/crumb 一律回 429
# 後兩者留著當備援（它們的政策可能再變），但排在後面。
HIST_SOURCES = [("nasdaq", _hist_nasdaq), ("stooq", _hist_stooq), ("yahoo", _hist_yahoo)]


def _expected_last_session():
    """理論上「應該已經有收盤價」的最後一個交易日（YYYY-MM-DD，美東）。

    ⚠️ 收盤後要留緩衝：Nasdaq 的當日 K 線要等官方結算寫入，
       收盤瞬間去抓常常只回到前一交易日。用跟排程同一個 18:00 ET。
    ⚠️ **不處理國定假日**（美股假日表會變，寫死會過期）。
       假日時這個函式會回一個「不存在的交易日」，快取永遠追不上 ——
       所以呼叫端一定要另外加時間下限，否則會變成每次請求都重抓。
    """
    et = _utcnow() - timedelta(hours=_et_offset_hours(_utcnow()))
    if et.hour < UPDATE_HOUR_ET:      # 今天的收盤還沒寫入，往前一天
        et -= timedelta(days=1)
    while et.weekday() >= 5:          # 週六日往前推到週五
        et -= timedelta(days=1)
    return et.strftime("%Y-%m-%d")


def _hist_is_stale(key):
    """快取的最後一個交易日是不是落後了？

    ⚠️ **這才是日 K 該用的判斷，不是 mtime。**
       原本用 12 小時 TTL：`_load_cache` 問「檔案多久沒寫」，
       而每次預抓都會重寫檔案 —— 只要 12 小時內有任何一次預抓
       （重啟、部署、本機開一下都算），收盤後的更新就整批命中快取、
       **一筆都不抓，然後回報成功**。資料因此卡在舊日期不動。

    ⚠️ 回 True 之後呼叫端仍要壓一個「最短重試間隔」：
       遇到國定假日時 `_expected_last_session()` 會指向一個不存在的交易日，
       快取永遠追不上，沒有下限就會變成每次請求都去抓。
    """
    rows = _load_cache(key, None) or []
    if not rows:
        return True
    return str(rows[-1][0]) < _expected_last_session()


HIST_RETRY_MIN_HOURS = 1.0     # 落後時最快多久重試一次（擋掉國定假日的無限重抓）

# ⚠️ 「上次嘗試時間」必須跟「快取檔 mtime」分開記。
#    用 mtime 當重試基準會連第一次都擋掉：抓回來的資料若沒有新的交易日，
#    檔案還是會被重寫，mtime 立刻變新 → 永遠不到重試門檻 → 一次都不抓。
#    放記憶體就好，重啟後重試一次是我們要的行為。
_STALE_TRY = {}
_STALE_LOCK = threading.Lock()

# ⚠️ 「抓失敗」與「抓成功但沒有新交易日」要用不同的退避時間。
#    兩者症狀一樣（快取日期沒前進），但成因完全相反：
#      · 國定假日 —— API 本來就沒有新資料，一小時後再試很合理
#      · 抓失敗（限流、逾時）—— 應該幾分鐘後就重試
#    共用一小時的話，300 檔裡零星失敗的那幾檔會被鎖住整整一小時，
#    結果就是**篩選結果同時混著新舊兩個日期**。（2026-08-04 實測）
HIST_RETRY_FAIL_MINUTES = 5.0
_HIST_FAILED = set()


def _stale_should_try(key):
    """資料落後時，這一次要不要真的去抓？（壓最短重試間隔）

    上一次是「抓失敗」的話用短退避，是「抓成功但沒有新交易日」才用長退避。
    """
    now = time.time()
    with _STALE_LOCK:
        gap = (HIST_RETRY_FAIL_MINUTES * 60 if key in _HIST_FAILED
               else HIST_RETRY_MIN_HOURS * 3600)
        if now - _STALE_TRY.get(key, 0) < gap:
            return False
        _STALE_TRY[key] = now
        _HIST_FAILED.discard(key)      # 這次的結果會重新決定退避長度
        return True


def get_history(symbol, max_age_hours=12, debug=False):
    """單一個股的收盤價序列，回傳 [(YYYY-MM-DD, close), …]，由舊到新。

    來源依 HIST_SOURCES 順序嘗試，任一成功即回傳。
    每檔一個快取檔，所以每天只需補抓一次；全部失敗回空清單，呼叫端自行忽略。
    debug=True 會把各來源的錯誤印出來（診斷用）。
    """
    key = "hist_%s.json" % symbol.upper()
    # ⚠️ 資料已經落後最新交易日 → 不管 mtime 多新都要重抓，
    #    但至少隔 HIST_RETRY_MIN_HOURS，免得國定假日時每次請求都打 API。
    if max_age_hours and _hist_is_stale(key) and _stale_should_try(key):
        max_age_hours = 0
    cached = _load_cache(key, max_age_hours)
    if cached is not None:
        return cached
    return _fetch_once(key,
                       lambda: _get_history_now(symbol, key, debug),
                       lambda: _load_cache(key, max_age_hours))


def _get_history_now(symbol, key, debug=False):
    """實際去抓。**已經有的歷史不重抓，只補新的交易日。**

    這是把歷史從 1 年拉長到 3 年之後的關鍵優化：
    一次抓 3 年約 85 KB，300 檔就是 26 MB —— 每天全部重抓很浪費，
    而且會讓每日更新的時間跟第一次一樣久。

    做法：
      1. 讀出快取（**不管多舊**，`max_age_hours=None`）
      2. 若舊資料的起點夠早（涵蓋 HIST_DAYS 所需區間），只抓「最後一天之後」的資料
      3. 合併、去重（以日期為鍵，新的覆蓋舊的）、排序、裁到 HIST_DAYS
      4. 若舊資料太短（例如剛把 HIST_DAYS 從 320 調到 780），就整段重抓

    只有 Nasdaq 支援指定起始日；備援來源一律整段抓。
    """
    old = _load_cache(key, None) or []
    # JSON 讀回來是 [[date, close], …]，統一轉成 tuple 才能進 dict
    old = [(r[0], r[1]) for r in old if r and len(r) >= 2 and r[0] and r[1]]

    # 是否已經抓過完整區間？
    # ⚠️ 不能用「舊資料起點是否早於某個日曆日」來判斷 —— 資料裁到 HIST_DAYS 筆之後，
    #    起點必然晚於用日曆天推估的區間開頭，會導致永遠判定「不足」而每次全抓。
    #    改為：① 已經有滿額筆數，或 ② meta 記錄了上次完整抓取的起始日且涵蓋現在的需求。
    meta_key = "histmeta_%s.json" % symbol.upper()
    meta = _load_cache(meta_key, None) or {}
    need_from = (_utcnow() - timedelta(days=int(HIST_DAYS * 1.5))).strftime("%Y-%m-%d")
    have_full = bool(old) and (len(old) >= HIST_DAYS
                               or str(meta.get("full_from", "9999")) <= need_from)
    frm = old[-1][0] if have_full else None   # 從最後一天開始抓（含當天，讓當日收盤有機會更新）

    rows, errs = [], []
    for name, fn in HIST_SOURCES:
        try:
            got = fn(symbol, frm) if name == "nasdaq" else fn(symbol)
            if got:
                LAST_SOURCE["name"] = name
                LAST_SOURCE["incremental"] = bool(frm) and name == "nasdaq"
                if frm:                       # 增量：與舊資料合併
                    merged = dict(old)
                    merged.update(dict(got))  # 同一天以新抓到的為準
                    rows = sorted(merged.items())
                else:
                    rows = sorted(dict(got).items())
                rows = rows[-HIST_DAYS:]
                break
        except Exception as e:
            errs.append("%s: %s %s" % (name, type(e).__name__, str(e)[:90]))

    if not rows:
        _HIST_FAILED.add(key)          # ⚠️ 讓退避縮短成幾分鐘，不要跟假日共用一小時
        if old:
            # 抓不到新資料但有舊的 —— 用舊的，總比整個消失好
            LAST_SOURCE["fails"] += 1
            return old[-HIST_DAYS:]
        LAST_SOURCE["fails"] += 1
        if debug:
            for e in errs:
                print("    ⚠️ ", e)

    _save_cache(key, rows)
    if not frm and rows:
        # 剛做完一次完整抓取，記下起始日 —— 下次就能安心走增量
        _save_cache(meta_key, {"full_from": need_from, "at": rows[-1][0]})
    return rows


def load_histories(symbols, status_cb=None, workers=8, force=False):
    """並行抓多檔歷史。回傳 {symbol: [(date, close), …]}。
    Stooq 沒有批次端點，只能逐檔抓，所以第一次會比較久（之後吃快取）。

    ⚠️ **force=True 會繞過 12 小時 TTL。收盤後的每日更新一定要用它。**
       `_load_cache` 是看檔案 mtime，而每一次預抓都會重寫檔案 ——
       只要 12 小時內有任何一次預抓（重啟、部署都會觸發），
       收盤後的更新就會全部命中快取、一筆都不抓，而且**回報成功**。
       這是「安靜地不做事」，比直接失敗難查得多。
    """
    out, done = {}, [0]
    lock = threading.Lock()

    def work(sym):
        h = get_history(sym, max_age_hours=0 if force else 12)
        with lock:
            if len(h) >= max(MA_SET):
                out[sym] = h
            done[0] += 1
            if status_cb and done[0] % 25 == 0:
                status_cb(done[0], len(symbols))

    with ThreadPoolExecutor(max_workers=workers) as ex:
        list(ex.map(work, symbols))
    if status_cb:
        status_cb(len(symbols), len(symbols))
    return out


# ---------------------------------------------------------------- 基本面

# 本益比與季報年增率。美股沒有月營收，也沒有像證交所那種一次拿全市場的端點，
# 只能逐檔抓 —— 所以快取放長（24 小時），並在部署時先預抓。
#
# ⚠️ 解析器依 Nasdaq 實際回應撰寫。若哪天格式改了，抓不到就回 None，
#    表格顯示「—」，不會讓篩選壞掉。要重新確認格式請跑 診斷基本面來源.command。

FUND_SUMMARY = "https://api.nasdaq.com/api/quote/{sym}/summary?assetclass=stocks"
FUND_REV = "https://api.nasdaq.com/api/company/{sym}/revenue?limit=1"

_MONTHS = ("January", "February", "March", "April", "May", "June", "July",
           "August", "September", "October", "November", "December")


def _yoy(cur, prev):
    """年增率（%）。前期為零或負數時不計算 —— 由虧轉盈算出來的百分比沒有意義
    （去年 -0.01、今年 0.38 會算成「+3900%」，那個數字會誤導人）。"""
    if cur is None or prev is None or prev <= 0:
        return None
    return round((cur / prev - 1) * 100, 1)


def _paren_date(txt):
    """從 '$2.01 (03/28/2026)' 取出 (2.01, '2026-03-28')。"""
    m = re.search(r"\(([\d/]+)\)", str(txt or ""))
    d = None
    if m:
        try:
            mm, dd, yy = m.group(1).split("/")
            d = "%s-%s-%s" % (yy, mm.zfill(2), dd.zfill(2))
        except ValueError:
            d = None
    return _num(re.sub(r"\(.*?\)", "", str(txt or ""))), d


def get_fundamentals(symbol, max_age_hours=24):
    """季報年增率。回傳 {"eps_yoy", "rev_yoy", "period", "eps", "rev"}。

    來源：`company/{sym}/revenue?limit=1`。它的表格結構是
    **同一季跨三個會計年度並排**，正好是年增率需要的：

        表頭   Fiscal Quarter: │ 2026 (FY) │ 2025 (FY) │ 2024 (FY)
        March
          Revenue              │ $111,184(m)│ $95,359(m)│ $90,753(m)
          EPS                  │ $2.01 (03/28/2026) │ $1.65 (03/29/2025) │ …

    所以 value2 vs value3 就是「最新季 vs 去年同季」。
    已與 `earnings-surprise` 交叉驗證：AAPL Mar 2026 EPS 兩邊都是 2.01。

    解析方式：以月份名稱當作區塊起點，往下收 Revenue 與 EPS 兩列；
    用 EPS 欄括號裡的日期判斷哪一季最新（不同公司會計年度起訖不同，
    不能假設順序）。尚未公布的季度 value2 是空的，會自動跳過。
    """
    key = "fund_%s.json" % symbol.upper()
    cached = _load_cache(key, max_age_hours)
    if cached is not None:
        return cached
    return _fetch_once(key,
                       lambda: _get_fundamentals_now(symbol, key),
                       lambda: _load_cache(key, max_age_hours))


def _get_fundamentals_now(symbol, key):
    out = {"eps_yoy": None, "rev_yoy": None, "period": None,
           "eps": None, "rev": None}
    try:
        j = _get(FUND_REV.format(sym=symbol.upper()), timeout=25, tries=2).json()
        rows = (((j or {}).get("data") or {}).get("revenueTable") or {}).get("rows") or []

        quarters, cur = [], None
        for r in rows:
            label = str(r.get("value1") or "").strip()
            base = label.replace("(FYE)", "").strip()
            if base in _MONTHS:
                cur = {"q": base}
                quarters.append(cur)
            elif cur is not None and label == "Revenue":
                cur["rev"] = _num(str(r.get("value2") or "").replace("(m)", ""))
                cur["rev_prev"] = _num(str(r.get("value3") or "").replace("(m)", ""))
            elif cur is not None and label == "EPS":
                cur["eps"], cur["date"] = _paren_date(r.get("value2"))
                cur["eps_prev"], _ = _paren_date(r.get("value3"))

        # 挑「已公布且有去年同季可比」的最新一季
        usable = [q for q in quarters if q.get("date")
                  and (q.get("eps") is not None or q.get("rev") is not None)]
        if usable:
            q = max(usable, key=lambda x: x["date"])
            out["period"] = "%s %s" % (q["q"], q["date"][:4])
            out["eps"] = q.get("eps")
            out["rev"] = q.get("rev")
            out["eps_yoy"] = _yoy(q.get("eps"), q.get("eps_prev"))
            out["rev_yoy"] = _yoy(q.get("rev"), q.get("rev_prev"))
    except Exception:
        pass

    _save_cache(key, out)
    return out


def load_fundamentals(symbols, status_cb=None, workers=8, force=False):
    """並行抓基本面。抓不到的給空值，不影響篩選。
    ⚠️ force=True 繞過 24 小時 TTL，理由同 load_histories。"""
    out, done = {}, [0]
    lock = threading.Lock()

    def work(sym):
        f = get_fundamentals(sym, max_age_hours=0 if force else 24)
        with lock:
            out[sym] = f
            done[0] += 1
            if status_cb and done[0] % 25 == 0:
                status_cb(done[0], len(symbols))

    with ThreadPoolExecutor(max_workers=workers) as ex:
        list(ex.map(work, symbols))
    return out


# ---------------------------------------------------------------- 即時報價
#
# 為什麼需要這條獨立的資料路：
#   美股有盤前盤後交易、又沒有漲跌幅限制，財報後隔夜跳空 10% 很常見
#   （2026-07-31 實測 AAPL 從 333.43 → 302.50，-9.27%）。
#   只看收盤價篩選，隔天可能已經是完全不同的價位。
#
# ⚠️ **盤中重抓歷史端點是沒用的**（2026-07-31 實測）：
#   `/quote/{SYM}/historical` 在盤中**不會回傳當日未完成的 bar**，
#   盤中重抓 300 檔會拿到跟早上一模一樣的資料，白跑 90 秒。
#   要拿盤中價格只能走 `/quote/{SYM}/info` —— 這是兩條不同的資料路。
#   （好處是：歷史快取不可能被未完成的 bar 污染。）
#
# ⚠️ **現價絕對不可以寫進 hist_ 快取**。均線與創新高必須建立在
#   「完整收盤價」之上，定義才穩定、結果才可重現。混入盤中價會讓
#   同一組條件在不同時間篩出不同結果，而且創新高會被盤中衝高誤判。
#
# 成本控制：**只對「篩選結果」抓現價，不是全部 300 檔**。
#   單檔約 2.4 秒，300 檔 / 8 併發要 90 秒，但結果通常只有 10～50 檔 → 5～15 秒。

QUOTE_URL = "https://api.nasdaq.com/api/quote/%s/info?assetclass=stocks"
QUOTE_TTL_H = 5.0 / 60.0        # 5 分鐘。報價變動快，但也不必每次篩選都重抓


def _quote_now(symbol):
    """抓一次即時報價。回傳 dict；任何失敗都回 {} 而不是拋例外。

    Nasdaq 的回應結構：
      data.primaryData    盤中報價（marketStatus=Open 時有效）
      data.secondaryData  盤前／盤後報價（休市時才有內容）
      data.marketStatus   Open / Closed / Pre-Market / After Hours
      data.keyStats.fiftyTwoWeekHighLow.value  "201.50 - 344.57"

    ⚠️ 欄位名以實測為準（2026-07-31 盤中），不要照 API 文件猜。

    ⚠️ **secondaryData 這條路現在很少走到，但不是死碼**：
       `attach_quotes()` 只在 09:30–16:00 ET 呼叫，所以正常日子都是 primaryData。
       但**半日交易**（感恩節隔天、平安夜等，13:00 ET 就收盤，一年約 3 天）
       在 13:00–16:00 這段我們的時間窗說「盤中」、Nasdaq 卻已回報 After Hours，
       這時就會走到 secondaryData。欄位名假設與 primaryData 相同，
       **這個假設沒有實測過**（需要挑半日交易當天才驗得到）。
       真的出錯也只是該檔顯示「—」，不影響篩選。
    """
    try:
        j = _get(QUOTE_URL % symbol.upper(), timeout=20, tries=2).json()
    except Exception:
        return {}
    d = (j or {}).get("data") or {}
    if not d:
        return {}

    status = str(d.get("marketStatus") or "").strip()
    primary = d.get("primaryData") or {}
    secondary = d.get("secondaryData") or {}

    def take(blk):
        px = _num((blk or {}).get("lastSalePrice"))
        if not px:
            return None
        return {"price": px,
                "pct": _num((blk or {}).get("percentageChange")),
                "ts": ((blk or {}).get("lastTradeTimestamp") or "").strip()}

    # 盤中用 primaryData；休市時 primaryData 是最後收盤，secondaryData 才是盤前／盤後
    reg, ext = take(primary), take(secondary)
    is_open = status.lower() == "open"
    use, kind = (reg, "regular") if is_open else ((ext, "extended") if ext else (reg, "close"))
    if not use:
        return {}

    out = {"price": use["price"], "pct": use["pct"], "ts": use["ts"],
           "kind": kind, "status": status}
    # 52 週高低是同一個請求免費附贈的，拿來當創新高的即時佐證
    try:
        rng = ((d.get("keyStats") or {}).get("fiftyTwoWeekHighLow") or {}).get("value") or ""
        lo, hi = [_num(x) for x in str(rng).split("-")[:2]]
        if lo and hi:
            out["w52_low"], out["w52_high"] = lo, hi
    except Exception:
        pass
    return out


def get_quote(symbol):
    key = "quote_%s.json" % symbol.upper()
    return _fetch_once(key,
                       lambda: _cache_quote(symbol, key),
                       lambda: _load_cache(key, QUOTE_TTL_H)) or {}


def _cache_quote(symbol, key):
    cached = _load_cache(key, QUOTE_TTL_H)
    if cached is not None:
        return cached
    q = _quote_now(symbol)
    if q:                       # 抓不到就不要寫空的進去蓋掉還堪用的舊值
        _save_cache(key, q)
    return q


def load_quotes(symbols, workers=8):
    """並行抓現價。抓不到的整檔略過 —— 現價是加值資訊，不能拖垮篩選。"""
    out = {}
    lock = threading.Lock()

    def work(sym):
        try:
            q = get_quote(sym)
        except Exception:
            q = {}
        if q:
            with lock:
                out[sym] = q

    with ThreadPoolExecutor(max_workers=workers) as ex:
        list(ex.map(work, symbols))
    return out


def _is_regular_session(now_utc=None):
    """現在是不是美股**正常交易時段**（09:30–16:00 ET 的平日）。

    盤前（04:00–09:30）與盤後（16:00–20:00）刻意回 False —— 見 attach_quotes()。
    純時間計算，不打任何 API。`_et_offset_hours()` 定義在下面的排程區塊，
    Python 是呼叫時才解析名稱，所以順序沒問題。

    ⚠️ **美股國定假日不會被排除**（沒有假日表）。那幾天（一年約 9 天）
    會照常抓一次現價，拿到的是前一日收盤。成本可接受，
    不值得為此維護一份每年要更新的假日清單。
    """
    now_utc = now_utc or _utcnow()
    et = now_utc - timedelta(hours=_et_offset_hours(now_utc))
    if et.weekday() >= 5:
        return False
    return 570 <= et.hour * 60 + et.minute < 960      # 09:30 – 16:00 ET


def attach_quotes(rows):
    """把現價附加到篩選結果上。就地修改並回傳 (rows, 報價中繼資料)。

    `last_pct` 是**與前一日收盤的差幅**，用我們自己的收盤價算 ——
    不直接用 API 的 percentageChange，因為那是它自己的基準，
    跟我們表格上顯示的收盤價未必是同一天（例如我們的資料還沒更新到最新交易日）。
    """
    if not rows or os.environ.get("ENABLE_QUOTES", "1") != "1":
        return rows, {}
    # ⚠️ 只在**盤中**抓現價。
    #    盤前／盤後抓到的價格意義不大（成交量薄、價差大），
    #    但要付出完整的等待成本（每檔約 2.4 秒，50 檔就是 15 秒）。
    #    台灣早上看盤前計畫時美股已休市，這時篩選應該要**立刻**回來。
    #    時間判斷是純計算、不花任何網路請求。
    if not _is_regular_session():
        return rows, {"open": False}
    quotes = load_quotes([r["symbol"] for r in rows])
    meta = {}
    for r in rows:
        q = quotes.get(r["symbol"])
        if not q:
            continue
        r["last"] = q["price"]
        base = r.get("price")
        if base:
            r["last_pct"] = round((q["price"] - base) / base * 100, 2)
        r["last_ts"] = q.get("ts")
        if not meta:
            meta = {"status": q.get("status"), "kind": q.get("kind"), "ts": q.get("ts")}
    return rows, meta


# 年增率級距（給結果太多時的下拉篩選用）
def yoy_bucket(y):
    if y is None:
        return None
    if y < 0:
        return "neg"
    if y < 20:
        return "lo"
    if y < 50:
        return "mid"
    return "hi"


# ---------------------------------------------------------------- 均線計算

def _sma(closes, period):
    """最後一筆的簡單移動平均；資料不足回 None。"""
    if len(closes) < period:
        return None
    return sum(closes[-period:]) / period


def _ma_series(closes, period, back):
    """回傳最近 back 天的均線值（由舊到新）；不足回 []。"""
    if len(closes) < period + back - 1:
        return []
    return [sum(closes[i - period:i]) / period
            for i in range(len(closes) - back + 1, len(closes) + 1)]


# 創新高：與台股版同一套設計 —— **容忍 2% 誤差**。
# 理由（見台股版文章 040）：貼近前高但差一點點，意義跟剛好突破幾乎相同，
# 硬要「嚴格超越」會漏掉一堆正在測試前高的股票。
NH_TOL = 0.02
NH_TIERS = [("3y", 756, "3年新高"), ("2y", 504, "2年新高"), ("1y", 252, "1年新高"),
            ("6m", 126, "半年新高"), ("3m", 63, "3個月新高")]
NH_LABEL = {"3y": "3年新高", "2y": "2年新高", "1y": "1年新高",
            "6m": "半年新高", "3m": "3個月新高", "": "—"}
NH_ORDER = ["3y", "2y", "1y", "6m", "3m"]


def new_high_label(closes):
    """回傳最強的創新高級距 key（"1y"/"6m"/"3m"），都不符合回 ""。

    判定：最新收盤 >= 該期間最高收盤 × (1 - 2%)。
    由長到短檢查，取最長的那個 —— 創 1 年新高當然也創了 3 個月新高，
    顯示最長的才有資訊量。
    資料不足該期間長度時跳過該級距（不會用不完整的區間硬算）。
    """
    if not closes:
        return ""
    last = closes[-1]
    for key, n, _ in NH_TIERS:
        if len(closes) < n:
            continue
        if last >= max(closes[-n:]) * (1 - NH_TOL):
            return key
    return ""


def align_label(mas):
    """由 {10:值, 20:值, 50:值, 200:值} 判定均線排列。

    與台股版同一套分類，只是週期換成美股習慣：
      strict_bull  嚴格多頭  10 > 20 > 50 > 150
      loose_bull   寬鬆多頭  10 > 20 > 50
      squeeze      均線糾結  四線收斂在 5% 內（優先判斷）
      loose_bear   寬鬆空頭  10 < 20 < 50
      strict_bear  嚴格空頭  10 < 20 < 50 < 150
      none         無序
    條件是照 MA_SET 的順序比較，所以改 MA_SET 這裡不必動。
    """
    vals = [mas.get(p) for p in MA_SET]
    if any(v is None for v in vals):
        return "none"
    lo, hi = min(vals), max(vals)
    if lo > 0 and (hi - lo) / lo <= 0.05:
        return "squeeze"
    a, b, c, d = vals                       # 依 MA_SET 順序：短 → 長
    if a > b > c > d:
        return "strict_bull"
    if a < b < c < d:
        return "strict_bear"
    if a > b > c:
        return "loose_bull"
    if a < b < c:
        return "loose_bear"
    return "none"


def _ma_desc(sign):
    """由 MA_SET 產生排列說明，例如 '10>20>50>150'。"""
    return sign.join(str(p) for p in MA_SET)


ALIGN_NAMES = {
    "strict_bull": ("嚴格多頭（%s）" % _ma_desc(">"), "Strict bullish (%s)" % _ma_desc(">")),
    "loose_bull": ("寬鬆多頭（%s）" % ">".join(str(p) for p in MA_SET[:3]),
                   "Loose bullish (%s)" % ">".join(str(p) for p in MA_SET[:3])),
    "squeeze": ("均線糾結（四線收斂 5% 內）", "MA squeeze (within 5%)"),
    "loose_bear": ("寬鬆空頭（%s）" % "<".join(str(p) for p in MA_SET[:3]),
                   "Loose bearish (%s)" % "<".join(str(p) for p in MA_SET[:3])),
    "strict_bear": ("嚴格空頭（%s）" % _ma_desc("<"), "Strict bearish (%s)" % _ma_desc("<")),
    "none": ("無序", "Unordered"),
}


# ---------------------------------------------------------------- 觀察清單篩選

def screen_watchlist(universe_n=150, ma=50, direction="above", days=1,
                     match="any", align="none", status_cb=None):
    """觀察清單策略。

    universe_n  股票範圍：市值前 N 大（150 / 300）
    ma          均線週期：10 / 20 / 50 / 200
    direction   "above" 站上 ／ "below" 跌破
    days        檢查最近 1 天或 3 天
    match       days=3 時，"any" 部分符合（任一日）／"all" 完全符合（每日）
    align       均線排列條件；"none" 表示不限
    回傳 {"rows": [...], "as_of": 最新資料日期}
    """
    uni = get_universe(universe_n)
    symbols = [u["symbol"] for u in uni]
    if status_cb:
        status_cb(0, len(symbols))
    hist = load_histories(symbols, status_cb=status_cb)
    if status_cb:
        status_cb(len(symbols), len(symbols))
    fund = load_fundamentals(list(hist.keys()), status_cb=status_cb)

    meta = {u["symbol"]: u for u in uni}
    rank = {s: i + 1 for i, s in enumerate(symbols)}   # 市值排名，O(1) 查找
    rows, as_of = [], ""

    for sym, h in hist.items():
        dates = [d for d, _ in h]
        closes = [c for _, c in h]
        if len(closes) < max(MA_SET):
            continue

        ma_line = _ma_series(closes, ma, days)
        if len(ma_line) < days:
            continue
        px = closes[-days:]

        hits = [(p > m) if direction == "above" else (p < m)
                for p, m in zip(px, ma_line)]
        ok = all(hits) if (days > 1 and match == "all") else any(hits)
        if not ok:
            continue

        mas = {p: _sma(closes, p) for p in MA_SET}
        lab = align_label(mas)
        if align != "none" and lab != align:
            continue
        nh = new_high_label(closes)

        # 最後一個符合條件的日期，以及「幾天中符合幾天」
        # （選「部分符合」時，只顯示一個日期看不出符合了幾天）
        hit_idx = max(i for i, v in enumerate(hits) if v)
        hit_date = dates[-days:][hit_idx]
        hit_days = sum(1 for v in hits if v)
        as_of = max(as_of, dates[-1])

        m = meta.get(sym, {})
        last = closes[-1]
        en_name, en_sector = m.get("name", sym), m.get("sector", "—")
        rows.append({
            "rank": rank.get(sym, 9999),
            "symbol": sym,
            # 中英兩份都給，前端依語言挑 —— 日後加語言切換不必改後端
            "name": en_name,
            "name_zh": zh_company(sym, en_name),
            "sector": en_sector,
            "sector_zh": zh_sector(en_sector),
            "price": round(last, 2),
            "ma": round(ma_line[-1], 2),
            "gap": round((last / ma_line[-1] - 1) * 100, 2),
            "align": lab,
            "hit_date": hit_date,
            "new_high": nh,
            "hit_days": hit_days,
            "days": days,
            "mktcap": m.get("mktcap"),
            "eps_yoy": (fund.get(sym) or {}).get("eps_yoy"),
            "rev_yoy": (fund.get(sym) or {}).get("rev_yoy"),
            "period": (fund.get(sym) or {}).get("period"),
        })

    rows.sort(key=lambda r: r["rank"])
    rows, qmeta = attach_quotes(rows)      # 只抓結果那幾檔，不是全部 300 檔
    return {"rows": rows, "as_of": as_of, "quote": qmeta,
            "ma_name": MA_NAMES.get(ma, str(ma)),
            "ma_name_zh": MA_NAMES_ZH.get(ma, str(ma))}


def screen_pullback(universe_n=150, ma=50, band=3.0, align="strict_bull",
                    status_cb=None):
    """飆股拉回找買點。

    找出**最近一日收盤價回到指定均線 ±band%** 範圍內的股票。
    用意不是預測底部，是給一個相對可控的進場位置：不追在最高點，
    而且停損點明確（跌破那條均線）。

    universe_n  市值前 N 大
    ma          回測均線（10 / 20 / 50 / 150）
    band        容忍區間，預設 ±3%
    align       均線排列條件；"none" 表示不限
    """
    uni = get_universe(universe_n)
    symbols = [u["symbol"] for u in uni]
    if status_cb:
        status_cb(0, len(symbols))
    hist = load_histories(symbols, status_cb=status_cb)
    if status_cb:
        status_cb(len(symbols), len(symbols))
    fund = load_fundamentals(list(hist.keys()), status_cb=status_cb)

    meta = {u["symbol"]: u for u in uni}
    rank = {s: i + 1 for i, s in enumerate(symbols)}
    rows, as_of = [], ""

    for sym, h in hist.items():
        closes = [c for _, c in h]
        if len(closes) < max(MA_SET):
            continue
        m = _sma(closes, ma)
        if not m:
            continue
        last = closes[-1]
        gap = (last / m - 1) * 100
        if abs(gap) > band:                 # 不在 ±band% 內就跳過
            continue

        mas = {p: _sma(closes, p) for p in MA_SET}
        lab = align_label(mas)
        if align != "none" and lab != align:
            continue
        nh = new_high_label(closes)

        as_of = max(as_of, h[-1][0])
        u = meta.get(sym, {})
        en_name, en_sector = u.get("name", sym), u.get("sector", "—")
        rows.append({
            "rank": rank.get(sym, 9999),
            "symbol": sym,
            "name": en_name,
            "name_zh": zh_company(sym, en_name),
            "sector": en_sector,
            "sector_zh": zh_sector(en_sector),
            "price": round(last, 2),
            "ma": round(m, 2),
            "gap": round(gap, 2),
            "align": lab,
            "hit_date": h[-1][0],
            "new_high": nh,
            "hit_days": 1,
            "days": 1,
            "mktcap": u.get("mktcap"),
            "eps_yoy": (fund.get(sym) or {}).get("eps_yoy"),
            "rev_yoy": (fund.get(sym) or {}).get("rev_yoy"),
            "period": (fund.get(sym) or {}).get("period"),
        })

    # 越貼近均線的排越前面（乖離絕對值小 → 拉回得剛剛好）
    rows.sort(key=lambda r: abs(r["gap"]))
    rows, qmeta = attach_quotes(rows)      # 只抓結果那幾檔，不是全部 300 檔
    return {"rows": rows, "as_of": as_of, "band": band, "quote": qmeta,
            "ma_name": MA_NAMES.get(ma, str(ma)),
            "ma_name_zh": MA_NAMES_ZH.get(ma, str(ma))}


# ---------------------------------------------------------------- 專業版試作：創新高／RS

RS_PERIODS = (20, 60, 120, 250)
RS_CACHE_FILE = "rs_scores_v1.json"


def _percentile_scores(values):
    """把 {symbol: return} 換成 1～99 的市場百分位；同報酬者使用平均名次。"""
    ordered = sorted(values.items(), key=lambda x: x[1])
    n, out, i = len(ordered), {}, 0
    if n == 1:
        return {ordered[0][0]: 99}
    while i < n:
        j = i + 1
        while j < n and ordered[j][1] == ordered[i][1]:
            j += 1
        avg_rank = ((i + 1) + j) / 2.0
        score = int(round(1 + (avg_rank - 1) / (n - 1) * 98))
        for k in range(i, j):
            out[ordered[k][0]] = max(1, min(99, score))
        i = j
    return out


def build_rs_cache(universe=None, histories=None):
    """用已預抓的 hist 快取計算四種 RS，頁面查詢時不重跑 250 日。"""
    universe = universe or get_universe(300)
    if histories is None:
        histories = {}
        for u in universe:
            sym = u["symbol"]
            h = _load_cache("hist_%s.json" % sym, None) or []
            if h:
                histories[sym] = h
    latest = [h[-1][0] for h in histories.values() if h]
    if not latest:
        raise RuntimeError("尚無股價快取可建立 RS")
    as_of = max(set(latest), key=latest.count)
    periods = {}
    for period in RS_PERIODS:
        returns, detail = {}, {}
        for sym, h in histories.items():
            closes = [float(x[1]) for x in h if x and len(x) >= 2 and x[1] is not None]
            if len(closes) < period + 1 or closes[-period - 1] <= 0:
                continue
            gain = (closes[-1] / closes[-period - 1] - 1) * 100
            returns[sym] = gain
            detail[sym] = {"gain": round(gain, 2), "close": round(closes[-1], 2),
                           "date": h[-1][0]}
        scores = _percentile_scores(returns) if returns else {}
        for sym, score in scores.items():
            detail[sym]["rs"] = score
        periods[str(period)] = detail
    out = {"as_of": as_of, "universe": len(universe), "periods": periods,
           "updated_at": _utcnow().strftime("%Y-%m-%d %H:%M UTC")}
    _save_cache(RS_CACHE_FILE, out)
    return out


def screen_pro_rs(period=60, threshold=90, status_cb=None):
    """市值前 300 大指定期間價格報酬的 1～99 市場百分位。"""
    period, threshold = int(period), int(threshold)
    if period not in RS_PERIODS:
        raise ValueError("RS 期間只支援 20、60、120 或 250 日")
    if threshold not in (80, 90, 95):
        raise ValueError("RS 門檻只支援 80、90 或 95")
    universe = get_universe(300)
    cache = _load_cache(RS_CACHE_FILE, None) or {}
    target = _home_screen_target_date()
    if not cache.get("periods") or (target and cache.get("as_of") != target):
        # 只讀本機 hist 快取重建，不呼叫 300 次外部 API；正常每日預抓已完成這步。
        cache = build_rs_cache(universe=universe)
    data = (cache.get("periods") or {}).get(str(period)) or {}
    rows = []
    for rank, u in enumerate(universe, 1):
        sym, d = u["symbol"], data.get(u["symbol"])
        if not d or int(d.get("rs") or 0) < threshold:
            continue
        rows.append({"rank": rank, "symbol": sym, "name": u["name"],
                     "name_zh": zh_company(sym, u["name"]), "sector": u["sector"],
                     "sector_zh": zh_sector(u["sector"]), "close": d["close"],
                     "gain": d["gain"], "rs": d["rs"]})
    rows.sort(key=lambda r: (-r["rs"], -r["gain"], r["rank"]))
    return {"rows": rows, "results": rows, "scanned": len(data), "period": period,
            "threshold": threshold, "as_of": cache.get("as_of")}


def screen_pro_new_high(days=1, status_cb=None):
    """市值前 300 大，最近 1／3／5 日任一天符合既有創新高級距。"""
    days = int(days)
    if days not in (1, 3, 5):
        raise ValueError("篩選日數只支援近一日、近三日或近五日")
    universe = get_universe(300)
    histories = load_histories([u["symbol"] for u in universe], status_cb=status_cb)
    strength = {k: len(NH_ORDER) - i for i, k in enumerate(NH_ORDER)}
    rows, latest = [], []
    for rank, u in enumerate(universe, 1):
        h = histories.get(u["symbol"]) or []
        if h:
            latest.append(h[-1][0])
        best = None
        for offset in range(min(days, len(h))):
            segment = h[:len(h) - offset]
            label = new_high_label([x[1] for x in segment])
            if not label:
                continue
            event = {"label": label, "date": segment[-1][0]}
            if (best is None or strength.get(label, 0) > strength.get(best["label"], 0)
                    or (label == best["label"] and event["date"] > best["date"])):
                best = event
        if best:
            sym = u["symbol"]
            rows.append({"rank": rank, "symbol": sym, "name": u["name"],
                         "name_zh": zh_company(sym, u["name"]), "sector": u["sector"],
                         "sector_zh": zh_sector(u["sector"]), "new_high": best["label"],
                         "hit_date": best["date"]})
    rows.sort(key=lambda r: (-strength.get(r["new_high"], 0), r["rank"]))
    as_of = max(set(latest), key=latest.count) if latest else None
    return {"rows": rows, "results": rows, "scanned": len(histories),
            "days": days, "as_of": as_of}


# ---------------------------------------------------------------- 背景工作

JOBS = {}


def start_job(fn, params):
    jid = uuid.uuid4().hex[:12]
    JOBS[jid] = {"status": "排隊中…", "done": False, "progress": 0}

    def run():
        try:
            def cb(i, total):
                JOBS[jid]["status"] = "讀取股價資料 %d / %d" % (i, total)
                JOBS[jid]["progress"] = int(i * 100 / max(1, total))
            JOBS[jid]["result"] = fn(status_cb=cb, **params)
            JOBS[jid].update(status="完成", done=True, progress=100)
        except Exception as e:
            JOBS[jid].update(status="失敗", done=True, error=str(e)[:200])

    threading.Thread(target=run, daemon=True).start()
    return jid


# ---------------------------------------------------------------- 預抓

PREFETCH_STATE = {"stage": "尚未開始", "done": False}


# ---------------------------------------------------------------- 市場階段
#
# 台股版用「融資張數 vs 歷史最高」判斷市場位置。美股**沒有對應物**：
#   FINRA margin debt 是月頻、而且是金額 —— 金額會隨股價膨脹，
#   正是台股當初刻意避開、改用張數的問題。
#
# 改用**市場寬度**：多少比例的個股站上自己的 150MA。
# 概念一樣（「多數人已在場內」vs「籌碼洗乾淨了」），而且**用現有的 hist_ 快取就能算**。
#
# 2026-08-05 改成三者分工：50MA 看順風／正常回檔，100MA 看真正逆風，
# 150MA 寬度只看市場是否被充分洗過。10 年納斯達克回測中，跌破 100MA 後
# 未來 20 日跌逾 10% 的比例約 16.7%，健康趨勢只有約 4.0%；首次回測 50MA
# 與均線糾結則沒有穩定的看空預測力，所以不能直接標成逆風或崩盤警訊。

BREADTH_MA = 150            # 個股用幾日均線算寬度
BREADTH_TOP = 85.0          # 當下寬度 ≥ 這個 → 頂部區（≈ P90）
BREADTH_WASH = 30.0         # 近 N 日最低寬度 ≤ 這個 → 洗過盤（≈ P7）
WASH_LOOKBACK = 90          # 「最近」是幾個交易日（≈ 半年的交易日數的一半，見下）
PHASE_FAST_MA = 50          # 指數短中期趨勢：相當於台股季線
PHASE_SLOW_MA = 100         # 指數中期風險線：跌破才視為真正逆風
PHASE_STICKY = 3            # 連續幾天成立才切換狀態

# 首頁折線圖保留 5 年（約 1,260 個交易日）。日常 `hist_` 仍只留 780 天；
# 較早的區段由隨程式部署的彙總種子檔提供，之後每日預抓用現行資料覆蓋／追加。
# ⚠️ 種子檔只有每天一個百分比，不會把 300 檔長歷史帶進正式環境。
BREADTH_KEEP = 5 * 252
BREADTH_SEED_FILE = os.path.join(BASE_DIR, "breadth_5y_seed.json")

# 洗盤記憶維持近 90 日最低寬度 ≤30%。收復 50MA 是初步復甦，收復 100MA
# 是復甦確認；三日黏著消除單日假突破。歷史寬度以今日前 300 大回算，仍有
# 存活者偏誤，門檻只應保守解讀。

NASDAQ_FRED = "https://fred.stlouisfed.org/graph/fredgraph.csv?id=NASDAQCOM"


def _idx_from_fred():
    """FRED NASDAQCOM：納斯達克綜合指數，免金鑰、回溯到 1971。
    ⚠️ 假日那幾列的值是 '.'，要跳過。"""
    out = {}
    r = _get(NASDAQ_FRED, timeout=60, tries=2)
    for ln in r.text.splitlines()[1:]:
        p = ln.split(",")
        if len(p) < 2:
            continue
        d, v = p[0].strip(), p[1].strip()
        if len(d) != 10 or v in (".", "", "NA"):
            continue
        try:
            out[d] = float(v)
        except ValueError:
            continue
    return out


def _idx_from_nasdaq(sym, asset):
    """Nasdaq API。COMP 走 assetclass=index，ONEQ 走 stocks。
    ⚠️ 只回得到近幾年，但我們只算 50MA，夠用。"""
    frm = (_utcnow() - timedelta(days=900)).strftime("%Y-%m-%d")
    to = _utcnow().strftime("%Y-%m-%d")
    url = ("https://api.nasdaq.com/api/quote/%s/historical"
           "?assetclass=%s&fromdate=%s&todate=%s&limit=9999" % (sym, asset, frm, to))
    j = _get(url, timeout=60, tries=2).json()
    rows = ((j or {}).get("data") or {}).get("tradesTable", {}).get("rows") or []
    out = {}
    for r in rows:
        d, c = (r.get("date") or "").strip(), _num(r.get("close"))
        if not d or c is None:
            continue
        mm, dd, yy = d.split("/")
        out["%s-%s-%s" % (yy, mm, dd)] = c
    return out


def _idx_latest_close():
    """Nasdaq COMP info：補 historical 尚未發布的最新正式收盤。

    `/historical` 實測可能在收盤翌日仍慢一個交易日，但 `/info` 已有
    `marketStatus=Closed`、正式日期與收盤值。只接受 Closed 且日期不晚於
    `_expected_last_session()`，避免把盤中價混進日線。
    """
    url = "https://api.nasdaq.com/api/quote/COMP/info?assetclass=index"
    j = _get(url, timeout=30, tries=2).json()
    data = (j or {}).get("data") or {}
    p = data.get("primaryData") or {}
    if str(data.get("marketStatus") or "").lower() != "closed":
        return None
    price = _num(p.get("lastSalePrice"))
    raw = str(p.get("lastTradeTimestamp") or "").strip()
    if price is None or not raw:
        return None
    d = None
    for fmt in ("%b %d, %Y", "%B %d, %Y", "%m/%d/%Y"):
        try:
            d = datetime.strptime(raw, fmt).strftime("%Y-%m-%d")
            break
        except ValueError:
            continue
    if not d or d > _expected_last_session():
        return None
    return d, price


# ⚠️ 診斷用：記下實際用了哪個來源、各來源為什麼失敗。
#    這個欄位存在的理由：FRED **會擋機房 IP**（Render 上實測 0 筆，本機正常），
#    跟 stooq / yahoo 是同一類問題，而那在本機測不出來。
INDEX_SOURCES = [
    ("FRED NASDAQCOM", lambda: _idx_from_fred()),
    ("Nasdaq COMP",    lambda: _idx_from_nasdaq("COMP", "index")),
    ("ONEQ (ETF 代理)", lambda: _idx_from_nasdaq("ONEQ", "stocks")),
]
_INDEX_SRC = {"name": None, "n": 0, "errs": []}


_IDX_TOPUP = {"at": 0, "note": "—"}
IDX_TOPUP_MIN_HOURS = 1.0
IDX_SCALE_TOL = 0.05      # 兩個來源在同一天的價差容忍度


def _idx_topup(idx):
    """FRED 落後時，用 Nasdaq COMP 把最新幾天補上。

    FRED 的 NASDAQCOM 通常慢一個交易日，個股卻已經有當日收盤 ——
    差一天對 50MA 幾乎沒影響，但會讓「指數日期」和「寬度日期」對不齊，
    最近 30 天裡少掉一天可判定。

    ⚠️ **合併兩個來源前一定要對帳。** 兩邊都該是納斯達克綜合指數，
       但只要哪天其中一邊換了口徑（除權、改成報酬指數、單位不同），
       混進來的值會安靜地扭曲 50MA。所以先比對重疊日期，
       差距超過 IDX_SCALE_TOL 就整批不採用。
    """
    if not idx:
        return idx
    last = max(idx)
    if last >= _expected_last_session():
        _IDX_TOPUP["note"] = "不需要（FRED 已是最新）"
        return idx
    now = time.time()
    if now - _IDX_TOPUP["at"] < IDX_TOPUP_MIN_HOURS * 3600:
        return idx
    _IDX_TOPUP["at"] = now
    try:
        comp = _idx_from_nasdaq("COMP", "index")
    except Exception as e:
        _IDX_TOPUP["note"] = "COMP 抓取失敗 %s" % type(e).__name__
        return idx
    if not comp:
        _IDX_TOPUP["note"] = "COMP 沒有資料"
        return idx
    # 對帳：找重疊日期比價
    both = [d for d in comp if d in idx]
    if not both:
        _IDX_TOPUP["note"] = "❌ 兩個來源沒有重疊日期，不敢合併"
        return idx
    ref = max(both)
    diff = abs(comp[ref] - idx[ref]) / max(idx[ref], 1e-9)
    if diff > IDX_SCALE_TOL:
        _IDX_TOPUP["note"] = ("❌ 口徑不符：%s FRED %.1f vs COMP %.1f（差 %.1f%%），不合併"
                              % (ref, idx[ref], comp[ref], diff * 100))
        return idx
    add = {d: v for d, v in comp.items() if d > last}
    # historical 可能仍慢一天；Closed 的 info 已是正式收盤，可安全補入。
    try:
        latest = _idx_latest_close()
        if latest and latest[0] > last:
            add[latest[0]] = latest[1]
    except Exception as e:
        if not add:
            _IDX_TOPUP["note"] = "COMP info 補抓失敗 %s" % type(e).__name__
    if not add:
        _IDX_TOPUP["note"] = "COMP historical / info 都沒有更新的交易日"
        return idx
    idx.update(add)
    _save_cache("nasdaq_index.json", idx)
    _IDX_TOPUP["note"] = ("✅ 用 COMP 補了 %d 天（%s → %s，對帳差 %.2f%%）"
                          % (len(add), last, max(add), diff * 100))
    return idx


def get_nasdaq_index():
    """納斯達克**綜合**指數日收盤 {date: close}。

    ⚠️ 不是 QQQ 的納斯達克 100。
    ⚠️ IXIC 是指數不是股票，`/historical?assetclass=stocks` 抓不到。
    ⚠️ **一定要有備援**：FRED 在 Render 上抓不到（機房 IP），
       本機卻正常 —— 只留單一來源等於線上永遠 unknown。
    """
    cached = _load_cache("nasdaq_index.json", 12)
    if cached is not None:
        # ⚠️ 命中快取要標記，否則診斷會誤報「全部失敗」——
        #    來源是上一個行程抓的，_INDEX_SRC 是行程內的變數。
        if not _INDEX_SRC["name"]:
            _INDEX_SRC.update({"name": "快取（上次成功的來源）", "n": len(cached)})
        return _idx_topup(cached)
    errs = []
    for name, fn in INDEX_SOURCES:
        try:
            out = fn()
        except Exception as e:
            errs.append("%s: %s" % (name, str(e)[:60]))
            continue
        if len(out) >= 300:          # 至少要能算 50MA 還有餘裕
            _save_cache("nasdaq_index.json", out)
            _INDEX_SRC.update({"name": name, "n": len(out), "errs": errs})
            return _idx_topup(out)
        errs.append("%s: 只有 %d 筆" % (name, len(out)))
    _INDEX_SRC.update({"name": None, "n": 0, "errs": errs})
    return cached or {}       # ⚠️ 抓不到別寫空的蓋掉舊資料


def build_breadth():
    """從 hist_ 快取算市場寬度，存成 breadth.json。

    ⚠️ **只能在預抓流程裡呼叫。** 要讀幾百個快取檔、每檔算 BREADTH_MA，
       首頁每個訪客都跑會出事。首頁只讀 breadth.json。
    """
    out = {}
    try:
        files = [f for f in os.listdir(CACHE_DIR)
                 if f.startswith("hist_") and f.endswith(".json")]
        above, total = {}, {}
        for f in files:
            try:
                rows = _load_cache(f, 24 * 365) or []
            except Exception:
                continue
            if len(rows) < BREADTH_MA + 20:
                continue
            run = 0.0
            for i, r in enumerate(rows):
                if not r or len(r) < 2 or r[1] is None:
                    continue
                run += r[1]
                if i >= BREADTH_MA:
                    run -= rows[i - BREADTH_MA][1]
                if i >= BREADTH_MA - 1:
                    d = r[0]
                    total[d] = total.get(d, 0) + 1
                    if r[1] > run / BREADTH_MA:
                        above[d] = above.get(d, 0) + 1
        for d, n in total.items():
            if n >= 60:          # 樣本太少的日子不算，免得比例失真
                out[d] = round(above.get(d, 0) / n * 100, 1)
    except Exception:
        return None
    if out:
        # 5 年種子只負責 `hist_` 觸及不到的舊區段；當前 `out` 永遠優先，
        # 因此成分股或最新價格更新後，重疊日期會被正式環境的現值覆蓋。
        seed = {}
        try:
            with open(BREADTH_SEED_FILE, "r", encoding="utf-8") as f:
                seed = json.load(f) or {}
        except Exception:
            pass                 # 種子缺失時安全降級成現有約 2.3 年
        seed.update(out)
        keep = dict(sorted(seed.items())[-BREADTH_KEEP:])
        _save_cache("breadth.json", keep)
        return keep
    return None


# ---------------------------------------------------------------- 本日推薦
#
# 首頁的「本日推薦」＝ 市值前 300 大 ＋ 均線嚴格多頭 ＋ 站上 10 日線。
#
# ⚠️⚠️ **首頁絕對不能即時跑篩選。**
#    `screen_watchlist()` 會呼叫 `load_histories()`，遇到落後的股票就**連網去抓**。
#    首頁每個訪客都跑一次會直接把站打掛，而且會拖垮 Nasdaq 的額度。
#    所以這裡在**預抓流程裡算好存檔**，首頁只讀 `home_screen.json`。
#    （台股版踩過同樣的坑，見台股 PROJECT_CONTEXT 4.3-6。）
#
# ⚠️ 條件是**寫死的**，不吃使用者參數 —— 首頁要的是「今天有沒有東西可看」，
#    不是另一個篩選器。想調條件請到 /screener。

HOME_SCREEN_PARAMS = {"universe_n": 300, "ma": 10, "direction": "above",
                      "days": 1, "match": "any", "align": "strict_bull"}
HOME_SCREEN_MAX = 6         # 首頁只列前幾檔，其餘請到篩選器看
_HOME_REBUILD = {"at": 0, "running": False, "note": "—"}
_HOME_REBUILD_LOCK = threading.Lock()
HOME_REBUILD_MIN_HOURS = 1.0


def build_home_screen():
    """算「本日推薦」並存檔。**只能在預抓流程裡呼叫。**"""
    res = screen_watchlist(**HOME_SCREEN_PARAMS)
    rows = res.get("rows") or []
    _save_cache("home_screen.json", {
        "n": len(rows),
        "as_of": res.get("as_of", ""),
        # ⚠️ 只存顯示要用的欄位。整包 rows 存下來會讓檔案又肥又容易過期，
        #    而且首頁本來就只需要代號與名稱。
        "top": [{"symbol": r["symbol"], "name": r.get("name", ""),
                 "name_zh": r.get("name_zh", "")} for r in rows[:HOME_SCREEN_MAX]],
    })
    return rows


def _home_screen_target_date():
    """本日推薦應該追到哪一天：以已算好的市場寬度最新日為準。

    不直接用 `_expected_last_session()`：美股假日沒有寫死日曆，假日會指向
    不存在的交易日。breadth 是同一批前 300 大個股快取算出的，日期既便宜又可靠。
    """
    br = _load_cache("breadth.json", 24 * 365) or {}
    return max(br) if br else ""


def _maybe_rebuild_home_screen():
    """本日推薦落後就在背景重算；首頁請求本身不連網、不等待篩選。"""
    try:
        old = _load_cache("home_screen.json", 24 * 365) or {}
        have = str(old.get("as_of") or "")
        target = _home_screen_target_date()
        if not target or have >= target:
            return False
        now = time.time()
        with _HOME_REBUILD_LOCK:
            if (_HOME_REBUILD["running"] or
                    now - _HOME_REBUILD["at"] < HOME_REBUILD_MIN_HOURS * 3600):
                return False
            _HOME_REBUILD.update(at=now, running=True,
                                 note="背景重算中（%s → %s）" % (have or "無", target))

        def job():
            try:
                build_home_screen()
                new = _load_cache("home_screen.json", 24 * 365) or {}
                _HOME_REBUILD["note"] = "完成（%s）" % (new.get("as_of") or "無日期")
            except Exception as e:
                _HOME_REBUILD["note"] = "失敗 %s: %s" % (type(e).__name__, str(e)[:80])
            finally:
                _HOME_REBUILD["running"] = False

        threading.Thread(target=job, daemon=True).start()
        return True
    except Exception as e:
        _HOME_REBUILD["note"] = "判斷失敗 %s" % type(e).__name__
        return False


def _home_screen_html():
    """首頁「本日推薦」區塊。**只讀快取**，讀不到就回空字串。

    ⚠️ 讀不到時回空字串（整塊不出現），**不要顯示「無法判斷」或「載入失敗」**——
       那看起來像壞掉。寧可少一塊。
    """
    import html as _h
    _maybe_rebuild_home_screen()
    d = _load_cache("home_screen.json", 24 * 365) or {}
    target = _home_screen_target_date()
    # 舊推薦比不顯示更誤導；背景已在上面啟動，下一次重新整理就會出現新結果。
    if target and str(d.get("as_of") or "") < target:
        return ""
    n = d.get("n")
    if n is None:
        return ""
    as_of = _h.escape(str(d.get("as_of") or ""))

    # ⚠️ **掛零是有意義的結論，不是故障。** 空頭市場裡「四線嚴格多頭又站上 10 日線」
    #    本來就可能一檔都沒有 —— 直接顯示「0 檔」會像壞掉，所以換一句話講清楚。
    if n == 0:
        return (
            '<a class="hs-box" href="/screener">'
            '<span class="hs-head">'
            '<b class="q-zh">今天沒有符合條件的股票</b>'
            '<b class="q-en" style="display:none">Nothing matches today</b>'
            '</span>'
            '<span class="hs-list q-zh">'
            '嚴格多頭排列又站上 10 日線的個股掛零，'
            '通常出現在跌深或趨勢轉折的時候。</span>'
            '<span class="hs-list q-en" style="display:none">'
            'No stock is in a strict bullish alignment and above its 10-day line — '
            'this usually happens after a sharp drop or at a turning point.</span>'
            '</a>')

    names_zh = "、".join(_h.escape("%s %s" % (r["symbol"], r.get("name_zh") or ""))
                         .strip() for r in d.get("top", []))
    names_en = ", ".join(_h.escape("%s" % r["symbol"]) for r in d.get("top", []))
    more_zh = " 等" if n > len(d.get("top", [])) else ""
    return (
        '<a class="hs-box" href="/screener">'
        '<span class="hs-head">'
        '<b class="q-zh">本日推薦</b>'
        '<b class="q-en" style="display:none">Today\'s picks</b>'
        '<span class="hs-n">' + str(n) + '</span>'
        '<span class="hs-unit q-zh">檔</span>'
        '<span class="hs-unit q-en" style="display:none">stocks</span>'
        '</span>'
        '<span class="hs-list q-zh">' + names_zh + more_zh + '</span>'
        '<span class="hs-list q-en" style="display:none">' + names_en + '</span>'
        '<span class="hs-sub q-zh">市值前 300 大 · 均線嚴格多頭 · 站上 10 日線'
        + ('（' + as_of + ' 收盤）' if as_of else '') + '</span>'
        '<span class="hs-sub q-en" style="display:none">Top 300 by cap · strict bullish '
        'alignment · above the 10-day line'
        + ((' (as of ' + as_of + ')') if as_of else '') + '</span>'
        '</a>')


PHASE_UI = {
    "tailwind": {"dot": "🟢", "zh": "順風趨勢", "en": "Tailwind",
                 "zh_do": "趨勢完整，順勢尋找主流股",
                 "en_do": "Trend intact — focus on market leaders"},
    "pullback": {"dot": "🟡", "zh": "多頭回檔", "en": "Bull-market Pullback",
                 "zh_do": "中期趨勢未破壞，降低追價",
                 "en_do": "The medium-term trend is intact — avoid chasing"},
    "transition": {"dot": "🟠", "zh": "方向整理", "en": "Trend Transition",
                   "zh_do": "多週期方向衝突，等待確認",
                   "en_do": "Timeframes conflict — wait for confirmation"},
    "riskoff": {"dot": "🔴", "zh": "逆風市場", "en": "Headwind",
                "zh_do": "中期風險升高，控制部位",
                "en_do": "Medium-term risk is elevated — control exposure"},
    "recovery_early": {"dot": "🔵", "zh": "初步復甦", "en": "Early Recovery",
                       "zh_do": "市場洗過並收復 50MA，開始觀察",
                       "en_do": "Washed out and above 50MA — start watching"},
    "recovery_confirmed": {"dot": "🔵", "zh": "復甦確認", "en": "Recovery Confirmed",
                           "zh_do": "市場洗過並收復 100MA，中期改善",
                           "en_do": "Washed out and above 100MA — trend improving"},
}


def _phase_raw(close, ma50, ma100, breadth, wash_min):
    """單日市場狀態：50MA 看順風、100MA 看逆風、150MA 寬度看洗盤。"""
    if close is None or ma50 is None or ma100 is None or breadth is None:
        return None
    washed = wash_min is not None and wash_min <= BREADTH_WASH
    if washed and close > ma100:
        return "recovery_confirmed"
    if washed and close > ma50:
        return "recovery_early"
    if close > ma50 and ma50 > ma100:
        return "tailwind"
    if ma50 > ma100 and ma100 < close <= ma50:
        return "pullback"
    if close < ma100:
        return "riskoff"
    return "transition"


def _phase_sticky(seq, n=PHASE_STICKY):
    """連續 n 天成立才換狀態，消掉一兩天的雜訊。"""
    if not seq:
        return None
    cur, pend, cnt = seq[0], None, 0
    for x in seq:
        if x == cur:
            pend, cnt = None, 0
            continue
        cnt = cnt + 1 if x == pend else 1
        pend = x
        if cnt >= n:
            cur, pend, cnt = x, None, 0
    return cur


_PHASE_MEMO = {"at": 0.0, "val": None}


def market_phase_cached():
    """首頁用：**只讀快取、絕不連網**。回傳 (phase, 說明, 資料日期, 寬度)。"""
    now = time.time()
    if _PHASE_MEMO["val"] is not None and now - _PHASE_MEMO["at"] < 300:
        return _PHASE_MEMO["val"]
    _maybe_rebuild_breadth()      # 落後的話在背景補算，這次先用舊的
    _maybe_topup_index()
    val = _phase_compute()
    _PHASE_MEMO.update(at=now, val=val)
    return val


# ⚠️ 為什麼是 unknown —— 這個欄位存在的理由：
#    `_phase_compute()` 整包在 except 裡，任何失敗都長得一模一樣（unknown）。
#    沒有這個就只能猜，而線上與本機的差異永遠猜不到。
_PHASE_WHY = {"why": "還沒算過", "steps": []}


# ⚠️ breadth.json 只在預抓流程裡算。但歷史資料是「落後就重抓」、
#    可能在預抓結束**很久之後**才補上新的交易日 —— 那時沒有任何東西
#    會回頭通知寬度重算，首頁就會卡在舊日期，而篩選結果卻是新的。
#    （2026-08-04 實測：篩選 8/3、首頁 7/31。）
_BREADTH_REBUILD = {"at": 0, "running": False}
_BREADTH_LOCK = threading.Lock()
BREADTH_REBUILD_MIN_HOURS = 1.0


def _maybe_rebuild_breadth():
    """寬度落後就在背景重算。**首頁只做一次日期比對，不會被拖慢。**

    ⚠️ 一定要背景執行：build_breadth() 要讀幾百個快取檔算 BREADTH_MA。
    ⚠️ 一定要壓最短間隔：國定假日時永遠追不上，否則每次請求都重算一輪。
    """
    try:
        br = _load_cache("breadth.json", 24 * 365) or {}
        if br and max(br) >= _expected_last_session():
            return
        now = time.time()
        with _BREADTH_LOCK:
            if (_BREADTH_REBUILD["running"] or
                    now - _BREADTH_REBUILD["at"] < BREADTH_REBUILD_MIN_HOURS * 3600):
                return
            _BREADTH_REBUILD.update(at=now, running=True)

        def job():
            try:
                build_breadth()
                _PHASE_MEMO.update(at=0, val=None)   # 讓下一次讀到新結果
            except Exception as e:
                _PHASE_WHY.update(why="背景重算寬度失敗 %s: %s"
                                      % (type(e).__name__, str(e)[:80]))
            finally:
                _BREADTH_REBUILD["running"] = False

        threading.Thread(target=job, daemon=True).start()
    except Exception:
        pass


def _maybe_topup_index():
    """指數落後就在背景補最新幾天。首頁只做一次日期比對，不會被拖慢。"""
    try:
        idx = _load_cache("nasdaq_index.json", 24 * 365) or {}
        if not idx or max(idx) >= _expected_last_session():
            return
        if time.time() - _IDX_TOPUP["at"] < IDX_TOPUP_MIN_HOURS * 3600:
            return

        def job():
            try:
                _idx_topup(_load_cache("nasdaq_index.json", 24 * 365) or {})
                _PHASE_MEMO.update(at=0, val=None)
            except Exception:
                pass
        threading.Thread(target=job, daemon=True).start()
    except Exception:
        pass


def _phase_compute():
    st = []
    try:
        br = _load_cache("breadth.json", 24 * 365) or {}
        idx = _load_cache("nasdaq_index.json", 24 * 365) or {}
        st.append("breadth %d 天%s｜指數 %d 天%s"
                  % (len(br), ("（~%s）" % max(br)) if br else "",
                     len(idx), ("（~%s）" % max(idx)) if idx else ""))
        if not br or not idx:
            _PHASE_WHY.update(why="缺 breadth.json 或 nasdaq_index.json", steps=st)
            return "unknown", "", "", None
        bd = sorted(br)
        ids = sorted(idx)
        px = [idx[d] for d in ids]
        mas = {}
        for n in (PHASE_FAST_MA, PHASE_SLOW_MA):
            out, run = {}, 0.0
            for i, d in enumerate(ids):
                run += px[i]
                if i >= n:
                    run -= px[i - n]
                if i >= n - 1:
                    out[d] = run / n
            mas[n] = out
        ma50, ma100 = mas[PHASE_FAST_MA], mas[PHASE_SLOW_MA]
        st.append("指數 %dMA／%dMA 可算 %d／%d 天"
                  % (PHASE_FAST_MA, PHASE_SLOW_MA, len(ma50), len(ma100)))
        recent = bd[-30:]
        hit = [d for d in recent if d in ma50 and d in ma100]
        st.append("breadth 最近 30 天有 %d 天對得上指數日期" % len(hit))
        if not hit:
            # ⚠️ 兩邊日期完全沒交集：通常是指數來源的交易日曆或格式不同
            _PHASE_WHY.update(
                # ⚠️ 均線天數都要帶常數，避免畫面與實際計算口徑不同。
                why="日期對不上：breadth 最新 %s，指數均線最新 %s"
                    % (max(bd), max(ma100) if ma100 else "—"), steps=st)
            return "unknown", "", "", None
        seq = []
        bpos = {d: i for i, d in enumerate(bd)}
        for d in recent:
            if d not in ma50 or d not in ma100:
                continue
            i = bpos[d]
            window = [br[x] for x in bd[max(0, i - WASH_LOOKBACK + 1):i + 1]]
            p = _phase_raw(idx.get(d), ma50.get(d), ma100.get(d), br[d],
                           min(window) if window else None)
            if p:
                seq.append(p)
        st.append("判定出 %d 天的狀態，最後 5 天：%s"
                  % (len(seq), " ".join(seq[-5:]) or "—"))
        phase = _phase_sticky(seq)
        if not phase:
            _PHASE_WHY.update(
                why="黏著條件不成立：需要連續 %d 天同一狀態，實際只有 %d 天可判"
                    % (PHASE_STICKY, len(seq)), steps=st)
            return "unknown", "", "", None
        last = bd[-1]
        _PHASE_WHY.update(why="正常", steps=st)
        return (phase, (PHASE_UI.get(phase) or {}).get("zh_do", ""),
                last, br[last])
    except Exception as e:
        _PHASE_WHY.update(why="%s: %s" % (type(e).__name__, str(e)[:100]), steps=st)
        return "unknown", "", "", None


def prefetch(universe_n=300, force=False):
    """啟動時先把清單與歷史抓好，使用者才不用等。

    ⚠️ **force=True 表示「這次一定要真的去抓」**，給收盤後的每日更新用。
       平常的啟動預抓維持 force=False，才不會每次重啟都重抓 300 檔。
    """
    # 指數放最前面：首頁第一眼就會用到，不能排在 300 檔個股與基本面之後。
    PREFETCH_STATE.update(stage="納斯達克綜合指數", done=False)
    try:
        get_nasdaq_index()          # 內容日期落後時 `_idx_topup` 會補，不看 mtime
    except Exception:
        pass
    PREFETCH_STATE["stage"] = "取得股票清單"
    uni = get_universe(universe_n)
    PREFETCH_STATE["stage"] = "讀取股價資料"

    def cb(i, total):
        PREFETCH_STATE["stage"] = "讀取股價資料 %d / %d" % (i, total)
    syms = [u["symbol"] for u in uni]
    histories = load_histories(syms, status_cb=cb, force=force)
    # RS 最長需要 251 個收盤；hist 本來就保留 780 日。這裡一次算好四種
    # 百分位並寫快取，使用者開 RS 頁時不必再掃 300 檔 × 250 日。
    PREFETCH_STATE["stage"] = "計算 RS 排名"
    try:
        build_rs_cache(universe=uni, histories=histories)
    except Exception:
        pass
    PREFETCH_STATE["stage"] = "讀取基本面資料"

    def cb2(i, total):
        PREFETCH_STATE["stage"] = "讀取基本面資料 %d / %d" % (i, total)
    load_fundamentals(syms, status_cb=cb2, force=force)   # 預抓時不算本益比，篩選時才用當下價格重算
    # ⚠️ 市場階段要用的兩份資料，都在這裡算好存檔 —— 首頁只讀快取、絕不自己算
    PREFETCH_STATE["stage"] = "計算市場寬度"
    try:
        build_breadth()
    except Exception:
        pass
    PREFETCH_STATE["stage"] = "本日推薦"
    try:
        build_home_screen()
    except Exception:
        pass                      # 算不出來就讓首頁少一塊，不能拖垮整個預抓
    PREFETCH_STATE.update(stage="完成", done=True,
                          finished_at=_utcnow().strftime("%Y-%m-%d %H:%M UTC"))


# ---------------------------------------------------------------- 每日自動更新
#
# 為什麼需要這個：原本只有「程式啟動時預抓一次」。Render 不會每天重啟，
# 所以服務跑一週之後，使用者看到的還是一週前的收盤價。
#
# 時間怎麼定的：
#   美股 16:00 ET 收盤 → 台灣 04:00（夏令）／05:00（冬令）
#   但 Nasdaq historical API 的當日 K 線要等官方結算寫入，
#   收盤瞬間去抓常常只到前一交易日。實測穩定要收盤後約 1.5～2 小時。
#   因此固定用 **18:00 ET**（收盤後 2 小時），換算台灣時間是
#   夏令 06:00、冬令 07:00。留 2 小時緩衝，比壓在 05:00 安全得多。
#
# ⚠️ 不要把觸發時間改早到 16:00～17:00 ET。那時 API 常只回到前一交易日，
#    histmeta 的增量判斷會認定「今天沒有新資料」，要等隔天才補上，
#    等於整天資料都慢一天。這個坑不要踩。
#
# ⚠️ 刻意不裝 pytz / 不依賴系統 tzdata。美國 DST 規則是固定的
#    （3 月第 2 個週日 ～ 11 月第 1 個週日），自己算 15 行就好，
#    符合本專案「只用 flask/requests/gunicorn」的相依原則。

UPDATE_HOUR_ET = int(os.environ.get("UPDATE_HOUR_ET", "18"))
# ⚠️ 行程啟動時刻。診斷要靠它判斷「是不是每次看都剛重啟」——
#    gunicorn 的 --timeout 太短時 worker 會被反覆砍掉，PID 每次都不同。
PROCESS_STARTED_TS = time.time()

# ⚠️⚠️ import 當下的 PID。**背景執行緒的存亡全看這一個數字。**
#    gunicorn 開 --preload 時，master 先 import（背景執行緒在 master 裡起來），
#    再 fork 出 worker —— 而 **fork 不會複製執行緒**。
#    worker 繼承了「執行緒跑過」的所有痕跡（enabled=True、心跳、entered_at），
#    執行緒本身卻留在 master。症狀是：旗標正常、心跳有值、但執行緒早就不在，
#    預抓永遠停在 fork 當下那一格，而且**不會有任何錯誤訊息**。
#    IMPORT_PID != os.getpid() 就是鐵證。
IMPORT_PID = os.getpid()

SCHED_STATE = {"enabled": False, "next_run": "—", "last_run": "—", "last_result": "—",
               "alerts_result": "—", "loop_error": "", "heartbeat": "—", "heartbeat_ts": 0}

# 上次更新紀錄寫在持久化磁碟，重啟後仍看得到。
# 只存 last_run / last_result 兩個欄位 —— next_run 每次啟動都會重算，存了反而會誤導。
SCHED_FILE = os.path.join(CACHE_DIR, ".sched_state.json")


def _sched_load():
    try:
        with open(SCHED_FILE, "r", encoding="utf-8") as f:
            d = json.load(f)
        for k in ("last_run", "last_result"):
            if d.get(k):
                SCHED_STATE[k] = d[k]
    except Exception:
        pass        # 檔案不存在或壞掉都不影響運作，維持預設的「—」


def _sched_save():
    """⚠️ 沿用專案慣例：uuid 暫存檔 + os.replace 原子寫入。

    不要改成固定的 .tmp 檔名 —— 快取寫入曾因此互相覆蓋，坑踩過（見變更紀錄）。
    """
    try:
        tmp = SCHED_FILE + "." + uuid.uuid4().hex + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump({"last_run": SCHED_STATE["last_run"],
                       "last_result": SCHED_STATE["last_result"]}, f, ensure_ascii=False)
        os.replace(tmp, SCHED_FILE)
    except Exception:
        pass        # 寫不進去頂多是紀錄不見，不能因此讓排程掛掉


def _nth_weekday_utc(year, month, weekday, n):
    """該月第 n 個 weekday（Monday=0 … Sunday=6）的 00:00。"""
    first = datetime(year, month, 1, tzinfo=timezone.utc)
    return first + timedelta(days=(weekday - first.weekday()) % 7 + 7 * (n - 1))


def _et_offset_hours(dt_utc):
    """美東相對 UTC 的時差（小時）。夏令 4、冬令 5。

    夏令起：3 月第 2 個週日 02:00 EST = 07:00 UTC
    夏令迄：11 月第 1 個週日 02:00 EDT = 06:00 UTC
    """
    y = dt_utc.year
    start = _nth_weekday_utc(y, 3, 6, 2) + timedelta(hours=7)
    end = _nth_weekday_utc(y, 11, 6, 1) + timedelta(hours=6)
    return 4 if start <= dt_utc < end else 5


def _next_update_utc(now_utc=None):
    """下一次該跑更新的 UTC 時間：最近一個「美東平日 UPDATE_HOUR_ET 整點」。

    週六、週日的美東日期直接跳過（沒有收盤）。
    美股國定假日不特別排除 —— 那天 API 只會回到前一交易日，
    增量抓取本來就會判定沒有新資料，多跑一次的成本很低。
    """
    now_utc = now_utc or _utcnow()
    et_today = (now_utc - timedelta(hours=_et_offset_hours(now_utc))).date()
    for d in range(0, 8):
        day = et_today + timedelta(days=d)
        if day.weekday() >= 5:          # 週六 / 週日
            continue
        # 美東牆上時間。標成 UTC 只是為了讓型別一致（aware），
        # 加上時差之後才是真正的 UTC 瞬間，數值完全相同。
        et_wall = datetime(day.year, day.month, day.day,
                           UPDATE_HOUR_ET, 0, tzinfo=timezone.utc)
        # 先用冬令時差估一次，再用估出來的 UTC 時間決定真正的時差
        guess = et_wall + timedelta(hours=5)
        run_utc = et_wall + timedelta(hours=_et_offset_hours(guess))
        if run_utc > now_utc:
            return run_utc
    return now_utc + timedelta(days=1)   # 理論上到不了


def _fmt_et(dt):
    off = _et_offset_hours(dt)
    tw = dt + timedelta(hours=8)
    return "%s UTC（台灣 %s・美東 %s）" % (
        dt.strftime("%Y-%m-%d %H:%M"),
        tw.strftime("%m-%d %H:%M"),
        (dt - timedelta(hours=off)).strftime("%m-%d %H:%M"))


def _beat():
    """心跳。用來判斷執行緒還活著 —— 只靠 enabled 旗標看不出來，
    那個旗標設過一次就不會變，執行緒死掉了它還是顯示「是」。"""
    SCHED_STATE["heartbeat_ts"] = time.time()
    SCHED_STATE["heartbeat"] = _fmt_et(_utcnow())


def _daily_updater():
    """外層只做一件事：**確保沒有任何例外能無聲逃走**。

    ⚠️ 執行緒裡的未捕捉例外只會印到 stderr 就消失，
       診斷頁看到的永遠只是「enabled 還是 False」，查不出原因。
    """
    try:
        _daily_updater_inner()
    except BaseException as e:      # ⚠️ 連 SystemExit / KeyboardInterrupt 都要留紀錄
        SCHED_STATE["loop_error"] = "執行緒死亡 %s: %s" % (type(e).__name__, str(e)[:100])
        raise


def _daily_updater_inner():
    """背景執行緒：每個美東交易日收盤後重跑一次 prefetch。

    ⚠️ **整個迴圈骨幹都必須包在 try 裡。**
    原本只有 prefetch() 有保護，時間計算（`_next_update_utc`／`_fmt_et`）
    與睡眠迴圈都是裸的。那幾行只要丟一次例外，執行緒就直接死掉 ——
    **每日更新永遠停止，而且沒有任何跡象**：`enabled` 旗標設過就不會變，
    診斷頁還是顯示「排程執行中：是」。
    這種「安靜地不做事」比直接壞掉難查得多，所以寧可無限重試。

    典型的觸發情境：naive 與 aware datetime 混用會丟 `TypeError`
    （例如日後把 `utcnow()` 換成 `now(timezone.utc)` 只換了一半）。
    """
    # 迴圈「之前」的準備動作也要保護 —— 它們在 try 外面的話，
    # 一樣會讓執行緒還沒進迴圈就死掉，症狀完全一樣（安靜地不更新）。
    # ⚠️ 這三個標記是為了分辨「執行緒沒進來」「進來但 _sched_load 卡住」
    #    「設好旗標後才死」—— 三種原因症狀都是 enabled=False。
    SCHED_STATE["entered_at"] = _utcnow().strftime("%H:%M:%S UTC")
    try:
        _sched_load()
        SCHED_STATE["loaded_at"] = _utcnow().strftime("%H:%M:%S UTC")
    except Exception as e:
        SCHED_STATE["loop_error"] = "_sched_load %s: %s" % (type(e).__name__, str(e)[:80])
    SCHED_STATE["enabled"] = True
    _beat()
    while True:
        try:
            nxt = _next_update_utc()
            SCHED_STATE["next_run"] = _fmt_et(nxt)
            # 分段睡眠：一次睡太久遇到系統時間調整會失準；順便定期更新心跳
            while True:
                remain = (nxt - _utcnow()).total_seconds()
                if remain <= 0:
                    break
                time.sleep(min(300.0, remain))
                _beat()
            try:
                prefetch(300, force=True)   # ⚠️ 收盤後必須繞過 TTL，見 load_histories
                SCHED_STATE["last_result"] = "成功"
                # 價格快取已更新完才檢查提醒，避免用舊收盤價發通知。
                # 推播失敗不反過來把整個每日預抓標成失敗。
                try:
                    ar = _run_alert_checks()
                    SCHED_STATE["alerts_result"] = (
                        "檢查 %(checked)s／送出 %(sent)s／過期 %(expired)s／舊資料 %(skipped_stale)s"
                        % ar)
                except Exception as alert_error:
                    SCHED_STATE["alerts_result"] = "失敗：%s" % str(alert_error)[:100]
            except Exception as e:
                SCHED_STATE["last_result"] = "失敗：%s" % str(e)[:120]
            SCHED_STATE["last_run"] = _fmt_et(_utcnow())
            SCHED_STATE["loop_error"] = ""
            _beat()
            _sched_save()
            time.sleep(90)   # 跨過觸發點，避免同一分鐘內重複觸發
        except Exception as e:
            # 排程骨幹自己出錯。**絕對不能讓執行緒結束** —— 記下來、等一分鐘再試。
            SCHED_STATE["loop_error"] = "%s: %s" % (type(e).__name__, str(e)[:120])
            SCHED_STATE["next_run"] = "計算失敗，60 秒後重試"
            _beat()
            time.sleep(60)


PAGE = r"""<!DOCTYPE html>
<html lang="zh-Hant-TW">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>美股咖啡館 US Stock Coffee｜美股選股工具・均線篩選</title>
<meta name="description" content="免費美股選股工具。用 10/20/50/150 日均線與均線排列篩選市值前 300 大美股，找出強勢股與轉弱股。免註冊、開啟即用。">
<meta name="theme-color" content="#33241A">
<link rel="icon" href="/icon.png?v=2" type="image/png" sizes="any">
<link rel="shortcut icon" href="/icon.png?v=2" type="image/png">
<link rel="apple-touch-icon" href="/icon.png?v=2">
<link rel="manifest" href="/manifest.json">
<script>
/* 判斷是不是在 App（加入主畫面／TWA）裡開啟。
   台股是不同來源，從 App 點過去會跳出帶網址列的分頁，所以 App 裡不顯示這顆鈕。
   在 <head> 就把 class 掛上去，CSS 才來得及在畫面出現前隱藏，不會閃一下才消失。 */
(function(){
  try {
    var inApp = window.matchMedia('(display-mode: standalone)').matches
             || window.matchMedia('(display-mode: fullscreen)').matches
             || window.navigator.standalone === true
             || document.referrer.indexOf('android-app://') === 0;
    if (inApp) document.documentElement.classList.add('in-app');
  } catch (e) {}
})();
</script>
<meta name="apple-mobile-web-app-capable" content="yes">
<meta name="apple-mobile-web-app-status-bar-style" content="default">
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Noto+Sans+TC:wght@400;500;700&family=Noto+Serif+TC:wght@600;700;900&family=Space+Mono:wght@400;700&display=swap" rel="stylesheet">
<style>

  :root{
    /* 咖啡館色系（介面外觀） */
    --milk:#F1EAD9; --foam:#FBF6EC; --grounds:#E4D7C1;
    --espresso:#33241A; --mocha:#6B5540; --caramel:#C68A3E; --caramel-2:#A56C24;
    --primary:#C68A3E;         /* 主色別名＝焦糖，讓既有 var(--primary) 全部沿用 */
    --bg:#F1EAD9;
    /* 行情紅綠（只給數據） */
    --up:#CB4B3A; --down:#4A7C64;
    --font-brand:"Noto Serif TC",serif;
    --font-head:"Noto Serif TC",serif;
    --font-body:"Noto Sans TC",sans-serif;
    --font-num:"Space Mono",ui-monospace,monospace;
    --shadow:0 14px 34px -20px rgba(51,36,26,.45);
  }
  * { box-sizing:border-box; font-family:var(--font-body); }
  body { margin:0; color:var(--espresso);
    background:radial-gradient(120% 80% at 50% -10%, #F7F1E4 0%, var(--milk) 55%, #EADFC9 100%);
    min-height:100vh;            /* 舊瀏覽器 fallback */
    min-height:100dvh;           /* 手機：跟著網址列伸縮的實際可視高度 */
    -webkit-font-smoothing:antialiased; }
  .wrap { max-width:960px; margin:0 auto; padding:16px; padding-top:70px;
          padding-bottom:calc(24px + env(safe-area-inset-bottom)); }
  h1, .ptitle { text-align:center; font-family:var(--font-head); font-weight:900; font-size:24px;
       color:var(--espresso); letter-spacing:.04em; margin:0 0 6px; }
  h1::after, .ptitle::after { content:"☕"; display:block; font-size:16px; margin-top:2px; opacity:.7; }
  .artbox .resfilter { margin:14px 0 4px; }
  .alinks { list-style:none; padding:0; margin:0; }
  .alinks li { border-top:1.5px solid var(--grounds); }
  .alinks li:first-child { border-top:none; }
  .alinks a { display:block; text-decoration:none; color:inherit; padding:13px 4px; }
  .alinks a:hover { background:var(--milk); border-radius:12px; }
  .alinks .atag { display:inline-block; font-size:11px; font-weight:700; color:#fff;
                  background:var(--caramel); border-radius:999px; padding:2px 10px; }
  .alinks .atitle { font-weight:800; font-size:16px; color:var(--espresso);
                    margin:6px 0 3px; line-height:1.5; }
  .alinks .asum { font-size:13.5px; color:var(--mocha); line-height:1.75; margin:0; }
  .alinks .adate { font-family:var(--font-num); font-size:11px; color:var(--caramel-2); }
  /* 功能頁的收合說明：預設收起，點一下展開。內容在 HTML 裡，爬蟲照樣讀得到 */
  .pgintro { max-width:560px; margin:0 auto 14px; background:var(--foam);
             border:1.5px solid var(--grounds); border-radius:18px; overflow:hidden; }
  .pgintro > summary { list-style:none; cursor:pointer; padding:13px 44px 13px 18px;
             position:relative; font-family:var(--font-head); font-weight:700;
             font-size:14.5px; color:var(--espresso); line-height:1.6; }
  .pgintro > summary::-webkit-details-marker { display:none; }
  .pgintro > summary::after { content:"▸"; position:absolute; right:18px; top:50%;
             transform:translateY(-50%); color:var(--caramel); font-size:17px;
             transition:transform .18s; }
  .pgintro[open] > summary::after { transform:translateY(-50%) rotate(90deg); }
  .pgintro > summary:hover { background:var(--milk); }
  .pgintro-b { padding:2px 18px 16px; border-top:1px solid var(--grounds); }
  .pgintro-b p { margin:11px 0 0; font-size:14px; color:#555; line-height:1.95; }
  .pgintro-b b { color:var(--espresso); }
  .card { background:var(--foam); border:1.5px solid var(--grounds); border-radius:20px;
          padding:16px 18px; margin-bottom:14px; box-shadow:var(--shadow);
          max-width:560px; margin-left:auto; margin-right:auto; }
  .card h2 { font-family:var(--font-head); font-size:16px; font-weight:700; margin:0 0 12px;
             color:var(--espresso); border-left:4px solid var(--caramel); padding-left:10px; }
  /* 選項＝點餐票 chip */
  label.opt { display:inline-flex; align-items:center; gap:6px; padding:9px 14px;
              margin:0 8px 8px 0; border-radius:12px; cursor:pointer; font-size:13.5px;
              color:var(--mocha); background:var(--milk); border:1.5px solid var(--grounds);
              transition:all .15s ease; }
  label.opt:hover { border-color:var(--caramel); }
  label.opt input[type=radio] { position:absolute; opacity:0; width:0; height:0; }
  label.opt:has(input:checked) { background:var(--caramel); border-color:var(--caramel);
              color:#fff; font-weight:500; box-shadow:0 6px 16px -8px rgba(165,108,36,.7); }
  label.opt:has(input:checked)::before { content:"✓"; font-size:11px; }
  /* 步驟編號徽章 */
  .stepno { font-family:var(--font-num); font-weight:700; font-size:12px; color:var(--caramel);
            border:1.5px solid var(--caramel); border-radius:8px; padding:1px 7px; margin-right:9px; }
  /* 豆子強度 */
  .beans { display:inline-flex; gap:3px; vertical-align:middle; }
  .beans i { width:7px; height:7px; border-radius:50%; background:var(--grounds); display:inline-block; }
  .beans i.on { background:var(--caramel); }
  /* 菜單首頁 */
  .brandhead { text-align:center; padding:8px 0 4px; }
  .brandhead .cup { font-size:34px; }
  .brandhead .btitle { font-family:var(--font-head); font-weight:900; font-size:26px;
                       text-align:center; letter-spacing:.02em; }
  .brandhead .btitle::after { content:none; }
  .brandhead .btitle {
            letter-spacing:.05em; margin-top:2px; }
  .brandhead .bsub { font-family:var(--font-num); font-size:11px; letter-spacing:.22em;
            text-transform:uppercase; color:var(--caramel-2); margin-top:4px; }
  .brandhead .bstatus { display:inline-flex; align-items:center; gap:8px; margin-top:10px;
            font-family:var(--font-num); font-size:12px; color:var(--mocha); }
  .brandhead .bstatus .dot { width:9px; height:9px; border-radius:50%; background:var(--down);
            box-shadow:0 0 0 3px rgba(74,124,100,.18); }
  .brandhead .bstatus .stat { font-weight:700; letter-spacing:.14em; color:var(--down); }
  .brandhead .bstatus .sep { color:var(--grounds); }
  .brandhead .bstatus.closed .dot { background:var(--caramel-2);
            box-shadow:0 0 0 3px rgba(165,108,36,.16); }
  .brandhead .bstatus.closed .stat { color:var(--caramel-2); }
  .menu-label { display:flex; align-items:center; gap:12px; max-width:560px; margin:22px auto 12px;
            font-family:var(--font-head); font-weight:700; font-size:13px; color:var(--mocha);
            letter-spacing:.16em; }
  .menu-label::after { content:""; flex:1; height:1px; background:var(--grounds); }
  .menu-item { display:flex; align-items:center; gap:14px; width:100%; max-width:560px;
            margin:0 auto 12px; text-align:left; background:var(--foam);
            border:1.5px solid var(--grounds); border-radius:20px; padding:15px 16px; cursor:pointer;
            transition:transform .18s ease, border-color .18s ease, box-shadow .18s ease; }
  .menu-item:hover { transform:translateY(-2px); border-color:var(--caramel); box-shadow:var(--shadow); }
  .menu-item .ic { width:46px; height:46px; flex:0 0 46px; border-radius:14px; display:grid;
            place-items:center; font-size:23px; background:rgba(198,138,62,.12); }
  .menu-item .body { flex:1; min-width:0; }
  .menu-item .nm { font-family:var(--font-head); font-weight:700; font-size:17px; letter-spacing:.02em; }
  .menu-item .ds { font-size:12.5px; color:var(--mocha); margin-top:2px; }
  .menu-item .mt { display:flex; align-items:center; gap:8px; margin-top:8px; }
  .menu-item .st { font-family:var(--font-num); font-size:10.5px; color:var(--mocha); letter-spacing:.06em; }
  .menu-item .chev { color:var(--caramel); font-size:22px; }
  /* 會員專區：Discord 按鈕與文章卡 */
  .dc-btn { display:inline-block; background:var(--caramel); color:#fff; font-family:var(--font-head);
            font-weight:700; font-size:16px; padding:12px 26px; border-radius:12px; text-decoration:none; }
  .dc-btn:hover { background:var(--caramel-2); }
  .art { border:1px solid var(--grounds); border-radius:12px; padding:12px 14px; margin-top:12px; background:var(--foam); }
  .art .atag { display:inline-block; font-family:var(--font-num); font-size:11px; color:var(--caramel-2);
            border:1px solid var(--caramel); border-radius:8px; padding:1px 8px; margin-bottom:7px; }
  .art h3 { margin:0 0 6px; font-size:16px; color:var(--espresso); }
  .art p { margin:0; font-size:14px; color:#555; line-height:1.85; }
  details.art > summary { list-style:none; cursor:pointer; position:relative; padding-right:22px; }
  details.art > summary::-webkit-details-marker { display:none; }
  details.art > summary::after { content:"▸"; position:absolute; right:2px; top:2px;
            color:var(--caramel); font-size:14px; transition:transform .15s; }
  details.art[open] > summary::after { transform:rotate(90deg); }
  .art .asum { color:var(--mocha); font-size:13.5px; }
  .art .adate { display:block; margin-top:6px; font-family:var(--font-num);
            font-size:11.5px; color:var(--mocha); }
  .artbody { margin-top:12px; padding-top:12px; border-top:1px solid var(--grounds); }
  .artbody h3 { font-size:16px; color:var(--caramel-2); margin:16px 0 8px; }
  .artbody h4 { font-size:14.5px; color:var(--espresso); margin:14px 0 6px; }
  .artbody p { margin:0 0 10px; font-size:14.5px; color:#555; line-height:1.9; }
  .artbody ul { margin:0 0 12px; padding-left:20px; }
  .artbody li { font-size:14.5px; color:#555; line-height:1.9; margin-bottom:4px; }
  .artbody b { color:var(--espresso); }
  .alinks { list-style:none; padding:0; margin:14px 0 0; }
  .alinks li { margin:0 0 12px; }
  .alinks a { display:block; padding:14px 16px; border:1.5px solid var(--grounds);
              border-radius:14px; background:var(--foam); color:inherit; text-decoration:none;
              transition:border-color .15s,transform .15s; }
  .alinks a:hover { border-color:var(--caramel); transform:translateY(-1px); }
  .alinks .atag { display:inline-block; font-family:var(--font-num); font-size:11px;
                  color:var(--caramel-2); border:1px solid var(--caramel);
                  border-radius:999px; padding:1px 8px; margin-bottom:7px; }
  .alinks .atitle { font-family:var(--font-head); font-weight:800; font-size:17px; }
  .alinks .asum { margin:6px 0 0; color:var(--mocha); font-size:13.5px; line-height:1.8; }
  .alinks .adate { display:block; margin-top:7px; color:var(--mocha);
                   font-family:var(--font-num); font-size:11.5px; }
  /* 總體經濟數據 */
  .macro-grid { display:grid; grid-template-columns:repeat(auto-fit,minmax(150px,1fr)); gap:12px; }
  .mstat { background:var(--milk); border:1px solid var(--grounds); border-radius:12px; padding:12px 14px; }
  .mstat .ml { font-size:12.5px; color:var(--mocha); }
  .mstat .mv { font-family:var(--font-num); font-size:22px; font-weight:700; color:var(--espresso); margin-top:4px; }
  .mstat .mv small { font-size:12px; color:var(--mocha); font-weight:400; margin-left:3px; }
  .mstat .msub { font-family:var(--font-num); font-size:11.5px; color:var(--mocha); margin-top:5px; }
  .mstat .mnote { font-family:var(--font-head); font-weight:700; font-size:14px; margin-top:3px; }
  /* 推播：股票搜尋選擇器 */
  .stockpick { position:relative; }
  .stockpick input { width:100%; padding:11px; font-size:15px; border:1.5px solid var(--grounds);
            border-radius:10px; background:#fff; box-sizing:border-box; font-family:inherit; }
  .stockpick input:focus { outline:none; border-color:var(--caramel); }
  .suggest { display:none; position:absolute; z-index:30; left:0; right:0; top:100%;
            margin-top:4px; max-height:240px; overflow-y:auto; background:#fff;
            border:1.5px solid var(--grounds); border-radius:10px; box-shadow:var(--shadow); }
  .suggest.show { display:block; }
  .suggest div { padding:10px 12px; cursor:pointer; font-size:14.5px; color:var(--espresso);
            border-bottom:1px solid var(--milk); }
  .suggest div:last-child { border-bottom:none; }
  .suggest div:hover, .suggest div.on { background:var(--milk); }
  .suggest div b { font-family:var(--font-num); margin-right:8px; color:var(--caramel-2); }
  .suggest .empty { color:var(--mocha); cursor:default; }
  .picked { margin-top:8px; padding:9px 12px; background:var(--milk); border-radius:10px;
            font-size:14.5px; color:var(--espresso); display:flex; justify-content:space-between;
            align-items:center; }
  .picked .clr { color:var(--caramel-2); cursor:pointer; font-size:13px; }
  /* 載入中：泡咖啡冒煙動畫 */
  .brewbox { position:relative; width:64px; height:60px; }
  .brewbox .steam { position:absolute; top:0; width:5px; height:20px; border-radius:3px;
             background:linear-gradient(to top, rgba(107,85,64,.42), rgba(107,85,64,0));
             animation:steamUp 2.4s ease-in-out infinite; }
  .brewbox .steam.s1 { left:17px; animation-delay:0s; }
  .brewbox .steam.s2 { left:29px; animation-delay:.5s; height:24px; }
  .brewbox .steam.s3 { left:41px; animation-delay:1s; }
  .brewbox .cup { position:absolute; bottom:6px; left:8px; width:40px; height:28px;
             background:var(--espresso); border-radius:0 0 16px 16px; }
  .brewbox .cup::before { content:""; position:absolute; top:-4px; left:0; width:40px; height:8px;
             border-radius:50%; background:var(--coffee, #6F4A2E); }
  .brewbox .handle { position:absolute; bottom:12px; left:47px; width:13px; height:14px;
             border:3.5px solid var(--espresso); border-left:none; border-radius:0 9px 9px 0; }
  .brewbox .saucer { position:absolute; bottom:0; left:2px; width:52px; height:5px;
             border-radius:3px; background:var(--grounds); }
  @keyframes steamUp {
    0%   { opacity:0; transform:translateY(6px) scaleX(.8); }
    35%  { opacity:.9; }
    100% { opacity:0; transform:translateY(-14px) scaleX(1.3); }
  }
  @media (prefers-reduced-motion: reduce) {
    .brewbox .steam { animation:none; opacity:.5; }
  }
  /* 載入中彈窗 */
  #brewModal { display:none; position:fixed; inset:0; z-index:200;
            background:rgba(51,36,26,.45); align-items:center; justify-content:center;
            padding:24px; backdrop-filter:blur(2px); }
  #brewModal.show { display:flex; }
  #brewModal .bm-box { background:var(--foam); border:1.5px solid var(--grounds);
            border-radius:20px; box-shadow:0 12px 40px rgba(51,36,26,.28);
            padding:22px 26px 20px; width:100%; max-width:330px; text-align:center; }
  #brewModal .bm-title { font-family:var(--font-head); font-weight:700; font-size:16px;
            color:var(--espresso); }
  #brewModal .bm-msg { font-size:14px; color:var(--mocha); line-height:1.7; margin-top:2px;
            min-height:44px; display:flex; align-items:center; justify-content:center; }
  #brewModal .bar { margin-top:12px; }
  #brewModal .bm-pct { font-family:var(--font-num); font-weight:700; font-size:13px;
            color:var(--caramel-2); margin-top:6px; }
  .menu-item.beta .nm::after { content:"測試中"; font-family:var(--font-body); font-weight:500;
            font-size:10px; color:var(--caramel-2); background:rgba(198,138,62,.14); border-radius:6px;
            padding:2px 6px; margin-left:8px; vertical-align:2px; }
  .gobtn { display:block; width:100%; max-width:560px; margin:0 auto; padding:15px; font-size:16px;
        font-family:var(--font-head); font-weight:700; letter-spacing:.08em; color:#fff;
        background:linear-gradient(135deg,var(--caramel),var(--caramel-2)); border:none;
        border-radius:16px; cursor:pointer; box-shadow:0 12px 26px -12px rgba(165,108,36,.8);
        transition:transform .15s ease; }
  .gobtn:hover { transform:translateY(-1px); }
  .gobtn:disabled { background:#cbb18a; box-shadow:none; transform:none; }
  .status { text-align:center; margin:14px 0; color:var(--mocha); font-size:14px; min-height:20px; }
  table { width:100%; border-collapse:collapse; font-size:13px; background:var(--foam);
          border-radius:14px; overflow:hidden; box-shadow:var(--shadow); }
  /* 結果版面：桌機用表格(窄時可橫向捲動)；手機改成可點開卡片 */
  .res-wide { overflow-x:auto; -webkit-overflow-scrolling:touch; max-width:100%; }
  .res-wide table { min-width:640px; }
  .res-cards { display:none; }
  @media (max-width:640px){
    .res-wide { display:none; }
    .res-cards { display:block; }
  }
  .scard { background:var(--foam); border:1px solid var(--grounds); border-radius:12px;
           margin-bottom:8px; overflow:hidden; box-shadow:var(--shadow); }
  .scard > summary { list-style:none; cursor:pointer; padding:11px 12px; display:flex;
           justify-content:space-between; align-items:center; font-size:14px; color:var(--espresso); }
  .scard > summary::-webkit-details-marker { display:none; }
  .scard .sc-l b, .scard .sc-r { font-family:var(--font-num); }
  .scard .sc-r { color:var(--espresso); display:flex; align-items:center; gap:8px; }
  .scard .sc-r::after { content:"▸"; color:var(--caramel-2); font-size:12px; transition:transform .15s; }
  .scard[open] .sc-r::after { transform:rotate(90deg); }
  .scard[open] > summary { border-bottom:1px solid var(--grounds); }
  .scard-body { padding:10px 12px; display:grid; grid-template-columns:1fr 1fr; gap:6px 14px; }
  .scard-body .kv { font-size:12.5px; color:var(--mocha); display:flex; justify-content:space-between; gap:8px; }
  .scard-body .kv b { color:var(--espresso); font-family:var(--font-num); font-weight:700; }
  /* 結果產業二次篩選 */
  .resfilter { display:flex; align-items:center; gap:10px; margin:0 0 12px; flex-wrap:wrap; }
  .resfilter .rflabel { font-size:13px; color:var(--mocha); font-weight:700; }
  .resfilter select { font-family:var(--font-num); font-size:14px; padding:8px 12px;
           border:1.5px solid var(--grounds); border-radius:10px; background:var(--foam);
           color:var(--espresso); min-width:170px; }
  .resfilter select:focus { outline:none; border-color:var(--caramel); }
  th,td { padding:9px 7px; text-align:right; border-bottom:1px solid var(--grounds); white-space:nowrap; }
  th { background:var(--espresso); color:var(--milk); font-family:var(--font-head); font-weight:700; }
  td { font-family:var(--font-num); color:var(--espresso); }
  td:nth-child(-n+4), th:nth-child(-n+4) { text-align:left; }
  .count { font-family:var(--font-num); font-weight:700; color:var(--caramel-2); }
  /* 行情紅綠：僅用於數字 */
  .pos { color:var(--up); font-family:var(--font-num); }
  .neg { color:var(--down); font-family:var(--font-num); }
  .rs-score { display:inline-flex; min-width:40px; justify-content:center; padding:3px 8px;
             border-radius:999px; background:var(--caramel); color:#fff; font-weight:800;
             font-family:var(--font-num); }

  /* ---- 側邊選單 ---- */
  #menuBtn { position:fixed; top:16px; left:16px; z-index:100; width:46px; height:46px;
             border-radius:50%; background:linear-gradient(135deg,var(--caramel),var(--caramel-2));
             border:none; cursor:pointer; box-shadow:0 6px 16px -6px rgba(51,36,26,.5);
             display:flex; flex-direction:column; justify-content:center; align-items:center; gap:5px; }
  #menuBtn span { display:block; width:20px; height:2.5px; background:#fff; border-radius:2px; }
  /* 公司名稱欄：限寬並在過長時省略，避免撐爆表格；title 屬性可看全名 */
  td.coname { max-width:180px; overflow:hidden; text-overflow:ellipsis;
              white-space:nowrap; font-family:var(--font-body); }
  td.sector { max-width:120px; overflow:hidden; text-overflow:ellipsis;
              white-space:nowrap; font-family:var(--font-body); }
  @media (max-width:640px){
    td.coname { max-width:120px; }
    td.sector { max-width:84px; }
  }
  #langBtn { position:fixed; top:16px; right:16px; z-index:100; height:46px; min-width:52px;
             padding:0 14px; border-radius:23px; background:var(--foam);
             border:1.5px solid var(--grounds); cursor:pointer;
             box-shadow:0 6px 16px -6px rgba(51,36,26,.35);
             font-family:var(--font-num); font-weight:700; font-size:14px;
             color:var(--caramel-2); letter-spacing:.06em; }
  #langBtn:hover { background:var(--caramel); color:#fff; border-color:var(--caramel); }
  #sidebar { position:fixed; top:0; left:-300px; width:280px; height:100%; background:var(--foam);
             z-index:99; box-shadow:2px 0 20px rgba(51,36,26,.2); transition:left .25s;
             padding-top:78px; border-right:1.5px solid var(--grounds); }
  #sidebar .sbTitle { position:absolute; top:24px; left:22px;
             font-family:var(--font-brand); font-weight:600; font-size:19px; color:var(--espresso); }
  #sidebar.open { left:0; }
  #overlay { position:fixed; inset:0; background:rgba(51,36,26,.4); z-index:98; display:none; }
  #overlay.show { display:block; }
  .navitem { display:block; padding:15px 22px; font-family:var(--font-head); font-size:16px;
             font-weight:700; color:var(--espresso); cursor:pointer; border-left:4px solid transparent; }
  .navitem:hover { background:var(--milk); }
  .navitem.active { border-left-color:var(--caramel); color:var(--caramel-2); background:var(--milk); }
  .navitem small { display:block; color:var(--mocha); font-size:12px; margin-top:2px;
             font-weight:400; font-family:var(--font-body); }
  /* 選股菜單群組（可收合） */
  .navgroup summary { display:block; padding:15px 22px; font-family:var(--font-head);
             font-size:16px; color:var(--espresso); cursor:pointer; list-style:none;
             border-left:3px solid transparent; position:relative; }
  .navgroup summary::-webkit-details-marker { display:none; }
  .navgroup summary:hover { background:var(--milk); }
  .navgroup summary::after { content:"▸"; position:absolute; right:20px; top:16px;
             color:var(--caramel); font-size:14px; transition:transform .15s; }
  .navgroup[open] summary::after { transform:rotate(90deg); }
  .navgroup summary small { display:block; color:var(--mocha); font-size:12px; margin-top:2px;
             font-weight:400; font-family:var(--font-body); }
  .navgroup .navitem.sub { padding-left:34px; }
  .navitem i, .navgroup summary i { font-style:normal; display:inline-block;
            width:22px; margin-right:8px; text-align:center; font-size:15px; }
  .navitem b, .navgroup summary b { font-weight:inherit; font-family:inherit; }
  .navitem small, .navgroup summary small { padding-left:30px; }
  .navgroup .navitem.sub small { padding-left:30px; }
  /* 首頁：科斯托蘭尼名言卡 */
  .qhead { display:flex; align-items:center; gap:12px; max-width:560px;
           margin:26px auto 14px; font-family:var(--font-head); font-weight:700;
           font-size:13px; color:var(--mocha); letter-spacing:.16em; }
  .qhead::after { content:""; flex:1; height:1px; background:var(--grounds); }
  /* 今日市場：市場階段（可展開看說明） */
  /* 到價提醒的股票選擇器（自台股版移植） */
  .stockpick { position:relative; }
  .stockpick input { width:100%; padding:11px; font-size:15px; border:1.5px solid var(--grounds);
            border-radius:10px; background:#fff; box-sizing:border-box; font-family:inherit; }
  .stockpick input:focus { outline:none; border-color:var(--caramel); }
  .suggest { display:none; position:absolute; z-index:30; left:0; right:0; top:100%;
            margin-top:4px; max-height:240px; overflow-y:auto; background:#fff;
            border:1.5px solid var(--grounds); border-radius:10px; box-shadow:var(--shadow); }
  .suggest.show { display:block; }
  .suggest div { padding:10px 12px; cursor:pointer; font-size:14.5px; color:var(--espresso);
            border-bottom:1px solid var(--milk); }
  .suggest div:last-child { border-bottom:none; }
  .suggest div:hover, .suggest div.on { background:var(--milk); }
  .suggest div b { font-family:var(--font-num); margin-right:8px; color:var(--caramel-2); }
  .suggest .empty { color:var(--mocha); cursor:default; }
  .picked { margin-top:8px; padding:9px 12px; background:var(--milk); border-radius:10px;
            font-size:14.5px; color:var(--espresso); display:flex; justify-content:space-between;
            align-items:center; }
  .picked .clr { color:var(--caramel-2); cursor:pointer; font-size:13px; }
  .mk-box { max-width:560px; margin:0 auto 16px; background:var(--foam);
           border:1.5px solid var(--grounds); border-radius:18px; overflow:hidden; }
  .mk-box > summary { list-style:none; cursor:pointer; display:flex; align-items:center;
           gap:12px; padding:14px 42px 14px 16px; position:relative; }
  .mk-box > summary::-webkit-details-marker { display:none; }
  .mk-box > summary::after { content:"▸"; position:absolute; right:16px; top:50%;
           transform:translateY(-50%); color:var(--caramel); font-size:17px;
           transition:transform .18s; }
  .mk-box[open] > summary::after { transform:translateY(-50%) rotate(90deg); }
  .mk-box > summary:hover { background:var(--milk); }
  .mk-dot { font-size:17px; line-height:1; }
  .mk-main { display:flex; align-items:baseline; gap:10px; flex:1; min-width:0; }
  .mk-main b { font-family:var(--font-head); font-size:16px; font-weight:700;
           color:var(--espresso); }
  .mk-do { font-size:13px; color:var(--mocha); overflow:hidden;
           text-overflow:ellipsis; white-space:nowrap; }
  /* 本日推薦：沿用市場階段卡片的寬度與圓角，讓兩者看起來是同一組東西 */
  .hs-box { max-width:560px; margin:0 auto 16px; display:block;
           background:var(--foam); border:1.5px solid var(--grounds);
           border-radius:14px; padding:14px 18px; box-shadow:var(--shadow);
           text-decoration:none; color:var(--espresso);
           transition:border-color .15s, transform .15s; }
  .hs-box:hover { border-color:var(--caramel); transform:translateY(-1px); }
  .hs-head { display:flex; align-items:baseline; gap:8px; }
  .hs-head b { font-family:var(--font-head); font-size:15px; }
  .hs-n { font-family:var(--font-num); font-size:26px; color:var(--caramel-2);
           font-weight:700; margin-left:auto; }
  .hs-unit { font-size:13px; color:var(--mocha); }
  .hs-list { display:block; margin-top:8px; font-size:13px; color:var(--mocha);
           line-height:1.7; }
  .hs-sub { display:block; margin-top:8px; font-size:11.5px; color:#a99; }
  .mk-body { padding:2px 16px 14px; border-top:1px solid var(--grounds);
           font-size:14px; color:#555; line-height:1.9; }
  .mk-body b { color:var(--espresso); }
  .mk-num { font-family:var(--font-num); font-size:12px; color:var(--mocha);
           flex-shrink:0; }
  @media(max-width:520px){
    .mk-main { flex-direction:column; align-items:flex-start; gap:2px; }
    .mk-num { display:none; }
  }
  .qcard { max-width:560px; margin:0 auto 16px; background:var(--foam);
           border:1.5px solid var(--grounds); border-radius:20px;
           padding:22px 24px 20px; box-shadow:var(--shadow); position:relative;
           overflow:hidden; }
  .qcard::before { content:"\\201C"; position:absolute; top:-18px; right:14px;
           font-family:var(--font-head); font-size:110px; line-height:1;
           color:var(--grounds); opacity:.55; }
  .qcard .qtag { display:inline-block; font-size:11.5px; color:var(--caramel-2);
           border:1px solid var(--caramel); border-radius:8px; padding:2px 9px;
           margin-bottom:12px; position:relative; }
  .qcard .qtext { font-family:var(--font-head); font-weight:500; font-size:17.5px;
           line-height:2; color:var(--espresso); position:relative; }
  .qcard .qlist { position:relative; margin:0; padding:0; list-style:none; }
  .qcard .qlist li { font-family:var(--font-head); font-weight:500; font-size:16.5px;
           line-height:1.9; color:var(--espresso); padding-left:20px; position:relative;
           margin-bottom:10px; }
  .qcard .qlist li:last-child { margin-bottom:0; }
  .qcard .qlist li::before { content:"—"; position:absolute; left:0; top:0;
           color:var(--caramel); }
  .qcard .qfoot { display:flex; justify-content:space-between; align-items:center;
           margin-top:16px; padding-top:12px; border-top:1px solid var(--grounds);
           font-size:12px; color:var(--mocha); position:relative; }
  .qcard .qnum { font-family:var(--font-num); }
  .qmore-wrap { max-width:560px; margin:2px auto 18px; text-align:center; }
  .qmore { font-family:var(--font-head); font-weight:700; font-size:14.5px;
           color:var(--caramel-2); background:var(--milk);
           border:1.5px solid var(--grounds); border-radius:12px;
           padding:10px 22px; cursor:pointer; transition:all .15s; }
  .qmore:hover { background:var(--caramel); color:#fff; border-color:var(--caramel); }
  .qmore:disabled { opacity:.5; cursor:default; background:var(--milk);
           color:var(--mocha); border-color:var(--grounds); }
  .qcard.qnew { animation:qFadeIn .45s ease-out; }
  @keyframes qFadeIn {
    from { opacity:0; transform:translateY(10px); }
    to   { opacity:1; transform:translateY(0); }
  }
  @media (prefers-reduced-motion: reduce){ .qcard.qnew { animation:none; } }
  .qsrc { max-width:560px; margin:4px auto 0; text-align:center; font-size:12.5px;
          color:var(--mocha); line-height:1.9; }
  @media (max-width:520px){
    .qcard { padding:18px 18px 16px; border-radius:16px; }
    .qcard .qtext { font-size:16.5px; line-height:1.95; }
  }
  .page { display:none; } .page.show { display:block; }

  /* ---- 晴雨表 ---- */
  .baro-num { font-family:var(--font-num); font-size:26px; font-weight:700; color:var(--caramel-2); }
  .baro-row { display:flex; justify-content:space-between; padding:8px 0; font-size:14px;
              border-bottom:1px dashed var(--grounds); }
  .badge { display:inline-block; padding:3px 10px; border-radius:20px; font-size:13px;
           font-weight:700; background:rgba(198,138,62,.16); color:var(--caramel-2);
           font-family:var(--font-num); }
  .badge.off { background:var(--milk); color:var(--mocha); font-weight:400; }
  .bar { height:10px; background:var(--milk); border-radius:6px; overflow:hidden; margin:8px 0 4px;
         border:1px solid var(--grounds); }
  .bar > div { height:100%; background:linear-gradient(90deg,var(--caramel),var(--caramel-2)); border-radius:6px; }
  .concl { margin:12px 0; padding:14px 16px; border-radius:12px; font-size:17px;
           font-weight:700; line-height:1.8; }
  .concl.red { background:rgba(203,75,58,.1); color:var(--up); border-left:5px solid var(--up); }
  .concl.blue { background:rgba(198,138,62,.12); color:var(--caramel-2); border-left:5px solid var(--caramel); }
  .concl.gray { background:var(--milk); color:var(--mocha); border-left:5px solid var(--grounds); }
  #langBtn { position:fixed; top:14px; right:14px; z-index:100; height:40px; min-width:46px;
             padding:0 14px; border-radius:20px; border:1.5px solid var(--grounds);
             background:var(--foam); color:var(--espresso); cursor:pointer;
             font-family:var(--font-head); font-weight:700; font-size:13px;
             box-shadow:var(--shadow); }
  #langBtn:hover { border-color:var(--caramel); color:var(--caramel-2); }

  /* 右上角按鈕列：市場切換 ＋ 語言。用 flex 排，寬度變動不會互相蓋到 */
  #topBtns { position:fixed; top:14px; right:14px; z-index:100;
             display:flex; gap:8px; align-items:center; }
  #topBtns #langBtn, #topBtns #mktBtn { position:static; top:auto; right:auto; }
  #mktBtn { height:40px; padding:0 14px; border-radius:20px;
            border:1.5px solid var(--grounds); background:var(--foam);
            color:var(--espresso); cursor:pointer; display:inline-flex;
            align-items:center; gap:5px; text-decoration:none; white-space:nowrap;
            font-family:var(--font-head); font-weight:700; font-size:13px;
            box-shadow:var(--shadow); }
  #mktBtn:hover { border-color:var(--caramel); color:var(--caramel-2); }
  /* App 裡隱藏跨網域的台股入口 —— 見 <head> 的 in-app 偵測 */
  html.in-app #mktBtn { display:none; }
  @media(max-width:420px){ #mktBtn, #topBtns #langBtn { padding:0 11px; font-size:12.5px; } }
</style>
</head>
<body>

<button id="menuBtn" aria-label="選單" data-i18n-aria="ui.menu"><span></span><span></span><span></span></button>
<div id="topBtns">
  <a id="mktBtn" href="__TW_URL__" title="切換到台股咖啡館" aria-label="切換到台股咖啡館" data-i18n-aria="ui.mkt.aria">🇹🇼 <span data-i18n="ui.mkt">台股</span></a>
  <button id="langBtn" title="切換公司與產業的顯示語言">EN</button>
</div>
<div id="overlay"></div>

<div id="brewModal">
  <div class="bm-box">
    <div class="brewbox" style="margin:0 auto 10px">
      <span class="steam s1"></span><span class="steam s2"></span><span class="steam s3"></span>
      <span class="cup"></span><span class="handle"></span><span class="saucer"></span>
    </div>
    <div class="bm-title" data-i18n="brew.title">沖泡中，請稍候</div>
    <div class="bm-msg" id="bmMsg" data-i18n="brew.wait">準備中…</div>
    <div class="bar" id="bmBarWrap" style="display:none"><div id="bmBar" style="width:0%"></div></div>
    <div class="bm-pct" id="bmPct" style="display:none">0%</div>
  </div>
</div>

<nav id="sidebar">
  <div class="sbTitle">☕ <span data-i18n="brand.name">美股咖啡館</span></div>
  <a class="navitem active" data-page="home" href="/"><i>☕</i><b data-i18n="nav.home">菜單首頁</b><small>US Stock Coffee</small></a>
  <details class="navgroup">
    <summary><i>📋</i><b data-i18n="nav.group">選股菜單</b><small data-i18n="nav.group.sub">強勢股・拉回買點・績效</small></summary>
    <a class="navitem sub" data-page="p1" href="/screener"><i>🔥</i><b data-i18n="p1.title">找強勢股</b><small data-i18n="nav.screen.sub">找出強勢主流題材股</small></a>
    <a class="navitem sub" data-page="p3" href="/pullback"><i>⭐</i><b data-i18n="p3.title">拉回找買點</b><small data-i18n="nav.pull.sub">收盤回到均線±3%</small></a>
    <a class="navitem sub" data-page="p7" href="/twr"><i>📈</i><b data-i18n="p7.title">我的績效</b><small data-i18n="nav.twr.sub">TWR 報酬率試算</small></a>
  </details>
  <details class="navgroup">
    <summary><i>⭐</i><b data-i18n="nav.mine">我的自選股</b><small data-i18n="nav.mine.sub">風控管理・到價提醒</small></summary>
    <a class="navitem sub" data-page="p8" href="/risk"><i>🛡️</i><b data-i18n="p8.title">風控管理</b><small data-i18n="nav.risk.sub">ATR・波動率・趨勢・Beta</small></a>
    <a class="navitem sub" data-page="p4" href="/alerts"><i>🔔</i><b data-i18n="p4.title">推播通知</b><small data-i18n="nav.alert.sub">收盤到價提醒（測試中）</small></a>
  </details>
  <a class="navitem" data-page="pm" href="/articles"><i>📚</i><b data-i18n="pm.title">文章區</b><small data-i18n="pm.sub">美股大盤與動量交易教學</small></a>
  <details class="navgroup">
    <summary><i>☕</i><b data-i18n="nav.pro">升級專業版</b><small data-i18n="nav.pro.sub">創新高・RS 指數</small></summary>
    <a class="navitem sub" data-page="p5" href="/pro"><i>🚀</i><b data-i18n="nav.proHigh">創新高</b><small data-i18n="nav.proHigh.sub">近期強勢突破股票</small></a>
    <a class="navitem sub" data-page="p9" href="/pro/rs"><i>🏆</i><b data-i18n="nav.proRs">RS 指數</b><small data-i18n="nav.proRs.sub">市場相對強弱排名</small></a>
  </details>
</nav>

<div class="wrap">

<!-- ============ 菜單首頁 ============ -->
<div class="page show" id="home">
  <div class="brandhead">
    <div class="cup">☕</div>
    <h1 class="btitle" data-i18n="brand.name">美股咖啡館</h1>
    <div class="bsub">US Stock Coffee</div>
    <div class="bstatus" id="bstatus">
      <span class="dot"></span><span class="stat" id="bstat">OPEN</span>
      <span class="sep">·</span><span id="bdate">—</span>
    </div>
  </div>

  <!-- 「關於這個工具」放最上面、**預設收合**。
       ⚠️ 它是給第一次來的人看的，回訪者每天都要滑過去很煩 ——
          所以位置在最前面（第一次看得到），但收起來（回訪不擋路）。
          用 <details> 而不是永遠展開的 card，就是這個取捨。 -->
  <details class="mk-box">
    <summary><span class="mk-main"><b data-i18n="home.about">關於這個工具</b></span></summary>
    <div class="mk-body">
      <div style="font-size:14.5px;color:#555;line-height:1.95" data-i18n-html="home.aboutBody">
        台股咖啡館的美股版。用<b>均線</b>從市值前 300 大的美股裡，
        篩出站上或跌破指定均線、以及符合特定均線排列的股票。<br><br>
        均線採美股習慣的 <b>10 / 20 / 50 / 150 日</b>——
        50 日線相當於台股季線的地位，150 日線用來看中長期趨勢。<br><br>
        資料為每日收盤價，非即時報價。
      </div>
    </div>
  </details>

  <!-- ============ 今日市場（版面照台股版）============
       結論秒開、細節手動：
         · __PHASE_BAR__ 只讀快取、零成本，一進來就看得到答案
         · 「大盤詳細數據」要展開才去打 /api/breadth，
           不讓每個訪客都觸發後端工作（台股版踩過，見台股 5.4） -->
  <div class="qhead" data-i18n="home.mhead">今日市場 · MARKET</div>

__PHASE_BAR__

  <details class="mk-box" id="brBox">
    <summary><span class="mk-main"><b data-i18n="br.open">大盤詳細數據</b></span></summary>
    <div class="mk-body">
      <div class="status" id="brStatus"></div>
      <div id="brBody"></div>
    </div>
  </details>

__HOME_SCREEN__

  <a class="menu-item" href="/screener" style="text-decoration:none;color:inherit">
    <span class="ic">📈</span>
    <span class="body"><span class="nm" data-i18n="p1.title">找強勢股</span>
      <span class="ds" data-i18n="home.c1">依均線與均線排列篩選個股</span></span>
    <span class="chev">›</span>
  </a>
  <a class="menu-item" href="/pullback" style="text-decoration:none;color:inherit">
    <span class="ic">🎯</span>
    <span class="body"><span class="nm" data-i18n="p3.title">拉回找買點</span>
      <span class="ds" data-i18n="home.c2">收盤回到指定均線 ±3%</span></span>
    <span class="chev">›</span>
  </a>
</div>

<!-- ============ 找強勢股 ============ -->
<div class="page" id="p1">
  <h2 class="ptitle" data-i18n="p1.title">找強勢股</h2>
  <details class="pgintro">
    <summary data-i18n="p1.introT">用均線找出「現在正在漲」的股票</summary>
    <div class="pgintro-b" data-i18n-html="p1.intro">
      <p>均線是一群人的平均成本。股價站上 50 日線，代表最近這一季買進的人平均在賺錢；
      跌破 150 日線，代表過去大半年的買方普遍套牢。所以均線不預測未來，
      它告訴你市場參與者現在的處境——而處境會影響他們的行為。</p>
      <p>這個功能從市值前 150 或 300 大的美股裡，篩出符合你設定的標的：
      可以指定站上或跌破 10、20、50、150 日均線，也可以直接用<b>均線排列</b>篩選——
      嚴格多頭（10&gt;20&gt;50&gt;150）代表越晚買的人成本越高卻還願意買，通常是趨勢正在走的股票。</p>
      <p>篩完如果檔數太多，上方的產業下拉可以繼續縮小範圍。
      <b>產業分布本身就是訊息</b>——如果三十檔裡有十二檔是同一個產業，
      那多半就是當下的主流題材。</p>
      <p><b>適合誰</b>：持有數個月的動量交易者。這裡是收盤資料，做不了當沖。</p>
    </div>
  </details>

  <div class="card"><h2><span class="stepno">01</span><span data-i18n="step.universe">股票範圍</span></h2>
    <label class="opt"><input type="radio" name="universe" value="150" checked><span data-i18n="opt.u150">市值前150大</span></label>
    <label class="opt"><input type="radio" name="universe" value="300"><span data-i18n="opt.u300">市值前300大</span></label>
  </div>

  <div class="card"><h2><span class="stepno">02</span><span data-i18n="step.days">篩選日數</span></h2>
    <label class="opt"><input type="radio" name="days" value="1" checked><span data-i18n="opt.d1">近一日</span></label>
    <label class="opt"><input type="radio" name="days" value="3"><span data-i18n="opt.d3">近三日</span></label>
  </div>

  <div class="card" id="modeCard" style="display:none"><h2 data-i18n="step.mode">符合方式（近三日）</h2>
    <label class="opt"><input type="radio" name="mode" value="any" checked><span data-i18n="opt.any">部分符合（三日內任一日符合）</span></label>
    <label class="opt"><input type="radio" name="mode" value="all"><span data-i18n="opt.all">完全符合（三日每日都符合）</span></label>
  </div>

  <div class="card"><h2><span class="stepno">03</span><span data-i18n="step.ma">均線條件</span></h2>
    <label class="opt"><input type="radio" name="ma" value="10"><span data-i18n="opt.ma10">10 日線 (10MA)</span></label>
    <label class="opt"><input type="radio" name="ma" value="20"><span data-i18n="opt.ma20">20 日線 (20MA)</span></label>
    <label class="opt"><input type="radio" name="ma" value="50" checked><span data-i18n="opt.ma50">50 日線 (50MA)</span></label>
    <label class="opt"><input type="radio" name="ma" value="150"><span data-i18n="opt.ma150">150 日線 (150MA)</span></label>
  </div>

  <div class="card"><h2><span class="stepno">04</span><span data-i18n="step.dir">方向</span></h2>
    <label class="opt"><input type="radio" name="direction" value="above" checked><span data-i18n="opt.above">站上</span></label>
    <label class="opt"><input type="radio" name="direction" value="below"><span data-i18n="opt.below">跌破</span></label>
  </div>

  <div class="card"><h2><span class="stepno">05</span><span data-i18n="step.align">均線排列</span></h2>
    <label class="opt"><input type="radio" name="align" value="strict_bull" checked><span data-i18n="opt.sbull1">嚴格多頭（10&gt;20&gt;50&gt;150）（用於強勢股）</span></label>
    <label class="opt"><input type="radio" name="align" value="strict_bear"><span data-i18n="opt.sbear1">嚴格空頭（10&lt;20&lt;50&lt;150）（用於長空）</span></label>
    <label class="opt"><input type="radio" name="align" value="loose_bull"><span data-i18n="opt.lbull">寬鬆多頭（10&gt;20&gt;50）</span></label>
    <label class="opt"><input type="radio" name="align" value="loose_bear"><span data-i18n="opt.lbear">寬鬆空頭（10&lt;20&lt;50）</span></label>
    <label class="opt"><input type="radio" name="align" value="squeeze"><span data-i18n="opt.squeeze">均線糾結（四線收斂於 5% 內）</span></label>
    <label class="opt"><input type="radio" name="align" value="none"><span data-i18n="opt.none">不限</span></label>
  </div>

  <button class="gobtn" id="go1" data-i18n="btn.screen">開始篩選</button>
  <div class="status" id="status1"></div>
  <div id="result1"></div>
</div>

<!-- ============ 拉回找買點 ============ -->
<div class="page" id="p3">
  <h2 class="ptitle" data-i18n="p3.title">拉回找買點</h2>
  <details class="pgintro">
    <summary data-i18n="p3.introT">等強勢股回頭，而不是追在最高點</summary>
    <div class="pgintro-b" data-i18n-html="p3.intro">
      <p>強勢股不會天天漲。上漲一段之後會有整理，而整理常常停在某條均線附近
      ——因為那是一群人的平均成本，形成心理上的支撐。</p>
      <p>這個功能找出<b>最近一日收盤價回到你指定均線 ±3% 範圍內</b>的股票。
      用意不是預測底部，是給你一個相對可控的進場位置：你不是追在最高點，
      萬一看錯，停損點也很明確（跌破那條均線）。</p>
      <p>均線怎麼選看你的操作週期——短線看 20 日線，波段看 50 或 150 日線。
      搭配<b>均線排列</b>條件，可以只找「趨勢還在、只是短暫休息」的股票。</p>
      <p>結果依<b>貼近均線的程度</b>排序，最上面的就是拉回得最剛好的。</p>
    </div>
  </details>

  <div class="card"><h2><span class="stepno">01</span><span data-i18n="step.universe">股票範圍</span></h2>
    <label class="opt"><input type="radio" name="universe3" value="150" checked><span data-i18n="opt.u150">市值前150大</span></label>
    <label class="opt"><input type="radio" name="universe3" value="300"><span data-i18n="opt.u300">市值前300大</span></label>
  </div>

  <div class="card"><h2><span class="stepno">02</span><span data-i18n="step.ma3">回測均線（收盤回到該線 ±3%）</span></h2>
    <label class="opt"><input type="radio" name="ma3" value="10"><span data-i18n="opt.ma10">10 日線 (10MA)</span></label>
    <label class="opt"><input type="radio" name="ma3" value="20"><span data-i18n="opt.ma20">20 日線 (20MA)</span></label>
    <label class="opt"><input type="radio" name="ma3" value="50" checked><span data-i18n="opt.ma50">50 日線 (50MA)</span></label>
    <label class="opt"><input type="radio" name="ma3" value="150"><span data-i18n="opt.ma150">150 日線 (150MA)</span></label>
  </div>

  <div class="card"><h2><span class="stepno">03</span><span data-i18n="step.align">均線排列</span></h2>
    <label class="opt"><input type="radio" name="align3" value="strict_bull" checked><span data-i18n="opt.sbull">嚴格多頭（10&gt;20&gt;50&gt;150）</span></label>
    <label class="opt"><input type="radio" name="align3" value="strict_bear"><span data-i18n="opt.sbear">嚴格空頭（10&lt;20&lt;50&lt;150）</span></label>
    <label class="opt"><input type="radio" name="align3" value="squeeze"><span data-i18n="opt.squeeze">均線糾結（四線收斂於 5% 內）</span></label>
    <label class="opt"><input type="radio" name="align3" value="none"><span data-i18n="opt.none">不限</span></label>
  </div>

  <button class="gobtn" id="go3" data-i18n="btn.screen">開始篩選</button>
  <div class="status" id="status3"></div>
  <div id="result3"></div>
</div>

<!-- ============ 我的績效（TWR）============ -->
<div class="page" id="p7">
  <h2 class="ptitle" data-i18n="p7.title">我的績效</h2>

  <div class="card" style="background:#eef4fc">
    <div style="font-size:14px;color:#333;line-height:1.9" data-i18n="twr.intro">
      使用時間加權報酬率（TWR），扣除中途存入或提出資金的影響，較能反映你的操作績效。逐月填入淨存入與月底總資產即可，資料只會儲存在這台裝置的瀏覽器。
    </div>
  </div>

  <div class="card">
    <h2 data-i18n="twr.basic">基本設定</h2>
    <div style="display:flex;gap:10px;flex-wrap:wrap">
      <div style="flex:1;min-width:120px">
        <div style="font-size:13px;color:#666;margin-bottom:4px" data-i18n="twr.year">年度</div>
        <input id="twYear" type="number" value="2026"
          style="width:100%;padding:11px;font-size:15px;border:1px solid #ddd;border-radius:10px;box-sizing:border-box">
      </div>
      <div style="flex:2;min-width:180px">
        <div style="font-size:13px;color:#666;margin-bottom:4px" data-i18n="twr.start">期初總資產（現金＋持股市值）</div>
        <input id="twStart" type="number" step="0.01" placeholder="例如 100000"
          style="width:100%;padding:11px;font-size:15px;border:1px solid #ddd;border-radius:10px;box-sizing:border-box">
      </div>
    </div>
  </div>

  <div class="card">
    <h2 data-i18n="twr.monthly">逐月填寫</h2>
    <div style="font-size:12px;color:#888;line-height:1.7;margin-bottom:8px" data-i18n="twr.note">
      當月淨存入＝存入－提出（提出請填負數）；月底總資產＝現金加所有持股市值。尚未到的月份留白即可。
    </div>
    <div style="overflow-x:auto">
      <table id="twTable" style="font-size:13px">
        <tr><th data-i18n="twr.col.m">月份</th><th data-i18n="twr.col.in">當月淨存入</th><th data-i18n="twr.col.tot">月底總資產</th><th data-i18n="twr.col.ret">當月報酬</th><th data-i18n="twr.col.cum">累積報酬</th></tr>
      </table>
    </div>
  </div>

  <button class="gobtn" id="twCalc" data-i18n="twr.calc">計算績效</button>
  <div style="text-align:center;margin-top:10px">
    <span id="twSaved" style="font-size:12px;color:#A56C24"></span>
    <a id="twClear" style="font-size:13px;color:#c0392b;cursor:pointer;margin-left:12px;text-decoration:underline" data-i18n="twr.clear">清空所有資料</a>
  </div>
  <div class="status" id="statusTw"></div>
  <div id="twResult"></div>
</div>

<!-- ============ 我的自選股：風控管理 ============ -->
<div class="page" id="p8">
  <h2 class="ptitle" data-i18n="p8.title">風控管理</h2>
  <div class="card" style="text-align:center;padding:30px 22px">
    <div style="font-size:42px;margin-bottom:10px">🛡️</div>
    <h2 data-i18n="risk.preparing">美股風控資料準備中</h2>
    <div style="font-size:14px;color:#666;line-height:1.9" data-i18n="risk.preparingNote">
      將提供自選股 ATR、波動率、均線趨勢與 Beta，並搭配進場價計算初始停損與移動停損。美股 OHLC 資料口徑確認後開放。
    </div>
  </div>
</div>

<!-- ============ 我的自選股：推播通知 ============ -->
<div class="page" id="p4">
  <h2 class="ptitle" data-i18n="p4.title">推播通知</h2>

  <div class="card" style="background:#fff8e6;border:1px solid #f0d98a">
    <div style="font-size:14px;color:#8a6d00;line-height:1.8">
      <span data-i18n-html="alert.note">⚠️ 本功能尚在測試中。每天美股收盤後以<b>收盤價</b>檢查一次，不是盤中即時服務。可從市值前 300 大裡選最多 3 檔，收盤價落在你設定價位的 ±2% 時發送通知，期限一個月。</span>
    </div>
  </div>

  <div class="card">
    <h2 data-i18n="alert.add">新增提醒</h2>
    <div style="margin-bottom:10px">
      <div style="font-size:13px;color:#666;margin-bottom:4px" data-i18n="alert.pick">選擇股票（市值前 300 大）</div>
      <div class="stockpick">
        <input id="alSearch" type="text" autocomplete="off" placeholder="輸入代號或名稱，例如 AAPL 或 蘋果" data-i18n-ph="alert.ph">
        <div id="alSuggest" class="suggest"></div>
        <div id="alPicked" class="picked" style="display:none"></div>
      </div>
      <input type="hidden" id="alStock" value="">
    </div>
    <div style="margin-bottom:10px">
      <div style="font-size:13px;color:#666;margin-bottom:4px" data-i18n="alert.target">目標價位（收盤價落在此價 ±2% 時通知）</div>
      <input id="alPrice" type="number" step="0.01" placeholder="150.5"
        style="width:100%;padding:11px;font-size:15px;border:1px solid #ddd;border-radius:10px;box-sizing:border-box">
    </div>
  </div>
  <button class="gobtn" id="alAdd" data-i18n="alert.btn">開啟通知並新增提醒</button>
  <div class="status" id="status4"></div>

  <div class="card" style="margin-top:16px">
    <h2 data-i18n="alert.test">推播測試</h2>
    <div style="font-size:13px;color:#666;margin-bottom:10px">
      <span data-i18n="alert.testNote">按下後立即發送一則測試通知到本裝置，用來確認伺服器金鑰與通知權限是否正常。</span>
    </div>
    <button class="gobtn" id="alTest" style="background:#6B5540" data-i18n="alert.testBtn">發送測試推播</button>
    <div class="status" id="statusTest"></div>
  </div>

  <div class="card" style="margin-top:16px">
    <h2 data-i18n="alert.list">已設定的提醒</h2>
    <div id="alList" style="font-size:14px;color:#999" data-i18n="alert.none">尚無提醒</div>
  </div>
</div>

<!-- ============ 升級專業版：創新高 ============ -->
<div class="page" id="p5">
  <h2 class="ptitle" data-i18n="p5.title">專業版｜創新高</h2>
  <div class="card">
    <div style="display:flex;align-items:center;gap:9px;margin-bottom:8px">
      <h2 style="margin:0" data-i18n="pro.nhTitle">創新高股票篩選</h2>
      <span class="badge" data-i18n="pro.beta">功能試作</span>
    </div>
    <div style="font-size:14px;color:#666;line-height:1.8;margin-bottom:14px" data-i18n-html="pro.nhBody">
      從市值前 300 大美股中，找出最近指定期間任一天符合<b>3 個月、半年、1 年、2 年或3 年新高</b>的股票。創新高採 2% 容差，避免只差一點就漏掉正在測試前高的股票。
    </div>
    <div style="display:flex;gap:8px;flex-wrap:wrap;margin:0 0 14px">
      <label class="opt" style="margin:0"><input type="radio" name="proHighDays" value="1" checked><span data-i18n="pro.nh1">近一日</span></label>
      <label class="opt" style="margin:0"><input type="radio" name="proHighDays" value="3"><span data-i18n="pro.nh3">近三日</span></label>
      <label class="opt" style="margin:0"><input type="radio" name="proHighDays" value="5"><span data-i18n="pro.nh5">近五日</span></label>
    </div>
    <button class="gobtn" id="proHighBtn" data-i18n="pro.nhBtn">篩選創新高</button>
    <div class="status" id="proHighStatus"></div><div id="proHighResult"></div>
  </div>
</div>

<!-- ============ 升級專業版：RS 指數 ============ -->
<div class="page" id="p9">
  <h2 class="ptitle" data-i18n="p9.title">專業版｜RS 指數</h2>
  <div class="card">
    <div style="display:flex;align-items:center;gap:9px;margin-bottom:8px">
      <h2 style="margin:0" data-i18n="rs.title">RS 相對強弱排名</h2>
      <span class="badge" data-i18n="pro.beta">功能試作</span>
    </div>
    <div style="font-size:14px;color:#666;line-height:1.85;margin-bottom:14px" data-i18n-html="rs.body">
      <b>RS 不是 RSI。</b>這裡比較市值前 300 大美股在指定期間的價格漲幅，換算為 1～99 分市場百分位。RS 90 代表表現約勝過九成可計算股票；這是本站價格百分位，不是 IBD 官方 RS Rating。
    </div>
    <div style="font-size:13px;color:var(--mocha);font-weight:700;margin-bottom:6px" data-i18n="rs.period">比較期間</div>
    <div style="display:flex;gap:8px;flex-wrap:wrap;margin:0 0 14px">
      <label class="opt" style="margin:0"><input type="radio" name="proRsPeriod" value="20"><span data-i18n="rs.p20">20 日（短線）</span></label>
      <label class="opt" style="margin:0"><input type="radio" name="proRsPeriod" value="60" checked><span data-i18n="rs.p60">60 日（波段）</span></label>
      <label class="opt" style="margin:0"><input type="radio" name="proRsPeriod" value="120"><span data-i18n="rs.p120">120 日（中期）</span></label>
      <label class="opt" style="margin:0"><input type="radio" name="proRsPeriod" value="250"><span data-i18n="rs.p250">250 日（長期）</span></label>
    </div>
    <div style="font-size:13px;color:var(--mocha);font-weight:700;margin-bottom:6px" data-i18n="rs.threshold">最低 RS</div>
    <div style="display:flex;gap:8px;flex-wrap:wrap;margin:0 0 14px">
      <label class="opt" style="margin:0"><input type="radio" name="proRsThreshold" value="80"><span>RS ≥ 80</span></label>
      <label class="opt" style="margin:0"><input type="radio" name="proRsThreshold" value="90" checked><span>RS ≥ 90</span></label>
      <label class="opt" style="margin:0"><input type="radio" name="proRsThreshold" value="95"><span>RS ≥ 95</span></label>
    </div>
    <button class="gobtn" id="proRsBtn" data-i18n="rs.btn">顯示 RS 排名</button>
    <div class="status" id="proRsStatus"></div><div id="proRsResult"></div>
  </div>
</div>

<!-- ============ 文章區 ============ -->
<div class="page" id="pm">
  <h2 class="ptitle" data-i18n="pm.title">文章區</h2>
  <div class="card">
    <h2 data-i18n="pm.head">美股大盤・入門教學</h2>
    <div style="font-size:14px;color:var(--mocha);line-height:1.9" data-i18n="pm.note">
      免費公開，從市場環境開始理解本站的篩選邏輯。
    </div>
    <ul class="alinks">__ART_LINKS__</ul>
  </div>
</div>

</div><!-- /wrap -->

<script>
const $ = s => document.querySelector(s);
const APP_TOKEN = "__APP_TOKEN__";
const START_PAGE = "__START_PAGE__";

/* ---- 顯示語言（機制與台股版相同）----
   data-i18n      → 換 textContent（中文原文自動備份在 data-zh，不會遺失）
   data-i18n-html → 換 innerHTML（保留 <b>/<p> 格式）
   JS 產生的字串   → 用 t(key, 中文預設)
   公司名稱與產業則由後端提供中英兩份，用 coName()/coSector() 挑。 */
let LANG = localStorage.getItem("us_lang") || "zh";

const I18N = { en: {
  "ui.menu": "Menu",
  "brew.title": "Brewing, please wait", "brew.wait": "Getting ready…",
  "brand.name": "US Stock Coffee",
  "nav.home": "Menu", "nav.group": "Stock Screeners",
  "nav.group.sub": "Leaders · Pullbacks · Performance",
  "nav.screen.sub": "Find leading stocks",
  "nav.pull.sub": "Close back within ±3% of an MA",
  "nav.twr.sub": "TWR performance calculator",
  "nav.mine": "My Watchlist", "nav.mine.sub": "Risk & price alerts",
  "nav.risk.sub": "ATR · Volatility · Trend · Beta",
  "nav.alert.sub": "Close-price alerts (beta)",
  "nav.pro": "Upgrade to Pro", "nav.pro.sub": "New highs · RS ranking",
  "nav.proHigh": "New Highs", "nav.proHigh.sub": "Recent breakout leaders",
  "nav.proRs": "RS Ranking", "nav.proRs.sub": "Market relative-strength percentile",
  "pm.title": "Articles", "pm.sub": "US market and momentum guides",
  "pm.head": "US Market · Beginner Guides",
  "pm.note": "Free to read. Start with the market environment behind this screener.",
  "nav.tw": "Taiwan Stock Coffee", "nav.tw.sub": "Stock Coffee · TW screener",
  "ui.mkt": "TW", "ui.mkt.aria": "Switch to Taiwan Stock Coffee",
  "alert.note": "⚠️ This feature is in beta. Alerts are checked once a day after the US close, using the <b>closing price</b> — it is not an intraday service. Pick up to 3 stocks from the top 300 by market cap; when the close lands within ±2% of your target, you get a notification. Alerts expire after one month.",
  "alert.add": "Add an alert", "alert.pick": "Choose a stock (top 300 by market cap)",
  "alert.ph": "Ticker or name, e.g. AAPL or Apple",
  "alert.target": "Target price (notify when the close is within ±2%)",
  "alert.btn": "Enable notifications and add alert",
  "alert.test": "Push test",
  "alert.testNote": "Sends a test notification to this device right now, to confirm the server keys and your notification permission are working.",
  "alert.testBtn": "Send test push",
  "alert.list": "Your alerts", "alert.none": "No alerts yet",
  "alert.picked": "Selected", "alert.repick": "Change ✕",
  "alert.notFound": "No match (top 300 by market cap only)",
  "alert.loadFail": "Could not load the stock list — please refresh",
  "alert.needStock": "Please pick a stock first",
  "alert.needPrice": "Please enter a valid price",
  "alert.added": "Alert added", "alert.tgt": "target", "alert.exp": "expires",
  "alert.asking": "Requesting notification permission…",
  "alert.sending": "Sending test push…",
  "alert.sentOk": "Sent — your device should show a notification shortly",
  "alert.sentNo": "Server did not send it",
  "alert.eNoSupport": "This browser does not support push (on iPhone, add to Home Screen first and open from the icon)",
  "alert.eNoKey": "Push keys (VAPID) are not configured on the server",
  "alert.ePerm": "Notifications are blocked — allow them in your system/browser settings",
  "alert.eSub": "Subscription failed: ",
  "home.mhead": "TODAY'S MARKET",
  "br.open": "Market detail", "br.loading": "Loading…",
  "home.about": "About this tool",
  "home.aboutBody": "The US edition of Stock Coffee. Screen the top 300 US companies by market cap using <b>moving averages</b> \u2014 crossing above or below a chosen MA, or matching a specific MA alignment.<br><br>The MA set follows US convention: <b>10 / 20 / 50 / 150-day</b>. The 50-day line plays the role Taiwan's 60-day line does; the 150-day tracks the intermediate trend.<br><br>Data is daily closing prices, not real-time quotes.",
  "home.c1": "Screen by moving average and MA alignment",
  "home.c2": "Close back within ±3% of a chosen MA",
  "home.c3": "The Taiwan edition — same logic, already live",
  "p1.title": "Find Strong Stocks", "p3.title": "Find Pullback Entries",
  "p7.title": "My Performance",
  "p8.title": "Risk Dashboard", "p4.title": "Price Alerts",
  "risk.preparing": "US risk data is being prepared",
  "risk.preparingNote": "This page will provide ATR, volatility, moving-average trend and Beta for your watchlist, plus initial and trailing stops based on your entry price. It will open after the US OHLC data definition is verified.",
  "alert.preparing": "US close-price alerts are being prepared",
  "alert.preparingNote": "Alerts will check official US closing prices against your targets and notify this device. The feature will open after push keys, subscription storage and the US close schedule are ready.",
  "p5.title": "Pro｜New Highs", "p9.title": "Pro｜RS Ranking",
  "pro.beta": "Beta", "pro.nhTitle": "New-high stock screener",
  "pro.nhBody": "Find top-300 US stocks that reached a <b>3-month, 6-month, 1-year, 2-year or 3-year high</b> on any day in the selected window. A 2% tolerance avoids missing stocks that are effectively retesting a prior high.",
  "pro.nh1": "Last day", "pro.nh3": "Last 3 days", "pro.nh5": "Last 5 days",
  "pro.nhBtn": "Screen new highs",
  "rs.title": "RS relative-strength ranking",
  "rs.body": "<b>RS is not RSI.</b> It compares price gains among the top 300 US stocks over the selected period and converts them to a 1–99 market percentile. RS 90 means the stock outperformed roughly 90% of calculable peers. This is Stock Coffee's price percentile, not IBD's proprietary RS Rating.",
  "rs.period": "Comparison period", "rs.p20": "20 days (short term)",
  "rs.p60": "60 days (swing)", "rs.p120": "120 days (intermediate)",
  "rs.p250": "250 days (long term)", "rs.threshold": "Minimum RS",
  "rs.btn": "Show RS ranking",
  "p1.introT": "Find stocks that are moving right now — using moving averages",
  "p1.intro": "<p>A moving average is the average cost of a group of buyers. Above the 50-day line, the people who bought this quarter are in profit; below the 150-day line, most buyers of the past half-year are underwater. Moving averages don't predict — they tell you where market participants stand, and that shapes what they do next.</p><p>This screener filters the top 150 or 300 US companies by market cap: crossing above or below the 10, 20, 50 or 150-day moving average, or screening directly by <b>MA alignment</b> — strict bullish (10&gt;20&gt;50&gt;150) means later buyers paid more and still bought, which usually marks a trend in progress.</p><p>If the screen returns too many names, the dropdowns above narrow it further. <b>The sector distribution is itself a signal</b> — when twelve of thirty results share an industry, that's where money is going.</p><p><b>Who it's for</b>: momentum traders holding for several months. This is closing data — not built for day trading.</p>",
  "p3.introT": "Wait for a strong stock to come back, instead of chasing the high",
  "p3.intro": "<p>Leading stocks don't rise every day. After a run they consolidate, and that consolidation often stalls near a moving average — because that line is a group's average cost, which becomes psychological support.</p><p>This screen finds stocks whose <b>latest close has returned to within ±3% of the moving average you choose</b>. The point isn't to call the bottom; it's an entry with controlled risk — you're not buying the high, and if you're wrong the stop is obvious (a break of that line).</p><p>Which average to use depends on your holding period — the 20-day for shorter trades, the 50 or 150-day for swings. Combined with the <b>MA alignment</b> filter, you can look only for stocks whose trend is intact and merely resting.</p><p>Results are sorted by <b>how close price is to the line</b> — the top of the list pulled back the most precisely.</p>",
  "twr.intro": "Time-weighted return (TWR) removes the effect of deposits and withdrawals, giving a clearer view of your investing performance. Enter each month's net cash flow and ending portfolio value. Data stays in this browser on this device.",
  "twr.basic": "Basic settings", "twr.year": "Year",
  "twr.start": "Starting portfolio value (cash + holdings)",
  "twr.monthly": "Monthly entries",
  "twr.note": "Net deposit = deposits minus withdrawals (enter withdrawals as negative). Ending value = cash plus all holdings. Leave future months blank.",
  "twr.col.m": "Month", "twr.col.in": "Net deposit", "twr.col.tot": "Ending value",
  "twr.col.ret": "Monthly return", "twr.col.cum": "Cumulative return",
  "twr.calc": "Calculate performance", "twr.clear": "Clear all data",
  "step.universe": "Universe", "step.days": "Days checked",
  "step.mode": "Match mode (3 days)", "step.ma": "Moving average",
  "step.dir": "Direction", "step.align": "MA alignment",
  "step.ma3": "Moving average (close back within ±3%)",
  "opt.u150": "Top 150 by market cap", "opt.u300": "Top 300 by market cap",
  "opt.d1": "Latest day", "opt.d3": "Last 3 days",
  "opt.any": "Partial (any of the 3 days)", "opt.all": "Full (all 3 days)",
  "opt.ma10": "10-day (10MA)", "opt.ma20": "20-day (20MA)",
  "opt.ma50": "50-day (50MA)", "opt.ma150": "150-day (150MA)",
  "opt.above": "Above", "opt.below": "Below",
  "opt.sbull1": "Strict bullish (10&gt;20&gt;50&gt;150) — for leaders",
  "opt.sbear1": "Strict bearish (10&lt;20&lt;50&lt;150) — for downtrends",
  "opt.sbull": "Strict bullish (10&gt;20&gt;50&gt;150)",
  "opt.sbear": "Strict bearish (10&lt;20&lt;50&lt;150)",
  "opt.lbull": "Loose bullish (10&gt;20&gt;50)", "opt.lbear": "Loose bearish (10&lt;20&lt;50)",
  "opt.squeeze": "MA squeeze (within 5%)", "opt.none": "Any",
  "btn.screen": "Run screen",
  /* --- JS 產生的字串 --- */
  "st.asof": "Data as of", "st.quarter": "Fiscal quarter",
  "st.match": "matches", "st.unit": "",
  "st.above": "above", "st.below": "below",
  "st.backto": "close back within",
  "st.none": "No stocks match these conditions.",
  "st.send": "Submitting…", "st.nojob": "Could not start the job",
  "st.failed": "Screen failed: ", "st.conn": "Connection failed: ",
  "st.lost": "Connection lost: ",
  "th.rank": "Rank", "th.sym": "Symbol", "th.name": "Company", "th.sector": "Sector",
  "th.price": "Price", "th.ma": "MA", "th.gap": "MA Gap%",
  "th.close": "Close", "th.last": "Last", "th.lastgap": "vs Close%",
  "q.last": "Last", "q.regular": "market hours",
  "q.extended": "pre/after-hours", "q.close": "at close",
  "q.closed": "Market closed — showing last close",
  "th.eps": "Q EPS YoY", "th.rev": "Q Rev YoY", "th.nh": "New high",
  "th.align": "MA alignment", "th.hit": "Match date", "th.asof": "Data date",
  "flt.sector": "Sector", "flt.allSector": "All sectors",
  "flt.eps": "Q EPS YoY", "flt.align": "MA alignment", "flt.nh": "New high",
  "flt.any": "Any", "flt.hasNH": "Made a new high",
  "yoy.neg": "Negative", "yoy.lo": "0–20%", "yoy.mid": "20–50%", "yoy.hi": "Over 50%",
  "nh.3y": "3-year high", "nh.2y": "2-year high", "nh.1y": "1-year high",
  "nh.6m": "6-month high", "nh.3m": "3-month high",
  "al.strict_bull": "Strict bullish", "al.loose_bull": "Loose bullish",
  "al.squeeze": "MA squeeze", "al.loose_bear": "Loose bearish",
  "al.strict_bear": "Strict bearish", "al.none": "Unordered"
}};

function t(key, zh){
  if (LANG === "zh") return zh;
  const v = (I18N.en || {})[key];
  return (v === undefined) ? zh : v;
}

/* 套用語言到所有標記過的元素。
   中文原文第一次會備份到 data-zh / data-zh-html，切回中文時還原，不會遺失。 */
function applyLang(){
  document.querySelectorAll("[data-i18n]").forEach(el => {
    if (!el.dataset.zh) el.dataset.zh = el.textContent;
    el.textContent = t(el.dataset.i18n, el.dataset.zh);
  });
  document.querySelectorAll("[data-i18n-aria]").forEach(el => {
    if (!el.dataset.zhAria) el.dataset.zhAria = el.getAttribute("aria-label") || "";
    el.setAttribute("aria-label", t(el.dataset.i18nAria, el.dataset.zhAria));
  });
  document.querySelectorAll("[data-i18n-html]").forEach(el => {
    if (!el.dataset.zhHtml) el.dataset.zhHtml = el.innerHTML;
    el.innerHTML = t(el.dataset.i18nHtml, el.dataset.zhHtml);
  });
  document.documentElement.lang = (LANG === "zh") ? "zh-Hant-TW" : "en";
  document.title = (LANG === "zh")
    ? "美股咖啡館 US Stock Coffee｜美股選股工具・均線篩選"
    : "US Stock Coffee｜US Stock Screener · Moving-Average Filter";
}
function coName(s){ return LANG === "zh" ? (s.name_zh || s.name) : s.name; }
function coSector(s){ return LANG === "zh" ? (s.sector_zh || s.sector) : s.sector; }
function sectorKey(s){ return s.sector; }        /* 篩選一律用英文原值當 key，避免對不上 */

const langBtn = $("#langBtn");
if (langBtn){
  langBtn.textContent = (LANG === "zh") ? "EN" : "中";
  langBtn.onclick = () => {
    LANG = (LANG === "zh") ? "en" : "zh";
    localStorage.setItem("us_lang", LANG);
    langBtn.textContent = (LANG === "zh") ? "EN" : "中";
    applyLang();
    document.querySelectorAll(".tw-month").forEach(el => {
      el.textContent = twMonth(parseInt(el.dataset.month, 10));
    });
    if (lastRows.length) render({rows:lastRows, as_of:lastMeta.as_of,
        ma_name_zh:lastMeta.ma_name_zh, ma_name:lastMeta.ma_name});
    if (lastRows3.length) render3({rows:lastRows3, as_of:lastMeta3.as_of, band:lastMeta3.band,
        ma_name_zh:lastMeta3.ma_name_zh, ma_name:lastMeta3.ma_name});
    if (lastProHigh) renderProHigh(lastProHigh);
    if (lastProRs) renderProRs(lastProRs);
  };
}

/* ---- 側邊選單 ---- */
const sidebar = $("#sidebar"), overlay = $("#overlay");
$("#menuBtn").onclick = () => { sidebar.classList.toggle("open"); overlay.classList.toggle("show"); };
overlay.onclick = () => { sidebar.classList.remove("open"); overlay.classList.remove("show"); };
document.querySelectorAll(".navitem").forEach(i => i.onclick = () => {
  sidebar.classList.remove("open"); overlay.classList.remove("show");
});

/* ---- 美股開盤狀態（美東時間 9:30–16:00，週一至週五）---- */
(function(){
  function tick(){
    const el = $("#bstatus"); if (!el) return;
    const t = new Date(new Date().toLocaleString("en-US", {timeZone:"America/New_York"}));
    const wd = t.getDay(), mins = t.getHours()*60 + t.getMinutes();
    const open = wd >= 1 && wd <= 5 && mins >= 9*60+30 && mins < 16*60;
    el.classList.toggle("closed", !open);
    $("#bstat").textContent = open ? "OPEN" : "CLOSED";
    $("#bdate").textContent = t.toLocaleDateString("en-US",
      {month:"short", day:"numeric"}) + " 美東 " +
      String(t.getHours()).padStart(2,"0") + ":" + String(t.getMinutes()).padStart(2,"0");
  }
  tick(); setInterval(tick, 30000);
})();

/* ---- 沖泡中彈窗 ---- */
function brewOpen(msg){
  $("#bmMsg").textContent = msg || "準備中…";
  $("#bmBarWrap").style.display = "none";
  $("#bmPct").style.display = "none";
  $("#brewModal").classList.add("show");
  document.body.style.overflow = "hidden";
}
function brewProgress(pct, msg){
  if (msg) $("#bmMsg").textContent = msg;
  if (pct == null) return;
  $("#bmBarWrap").style.display = "";
  $("#bmPct").style.display = "";
  $("#bmBar").style.width = pct + "%";
  $("#bmPct").textContent = pct + "%";
}
function brewClose(){
  $("#brewModal").classList.remove("show");
  document.body.style.overflow = "";
}

/* 連線憑證過期時自動重新整理一次。
   會發生在：伺服器重啟換了密鑰，或分頁開太久（token 24 小時到期）。
   用 sessionStorage 記錄避免無限重整 —— 如果重整後還是失敗，就顯示訊息讓人知道。 */
function retryOnStaleToken(j){
  if (!j || !/憑證|token/i.test(j.error || "")) return false;
  if (sessionStorage.getItem("tokenRetry")) {
    sessionStorage.removeItem("tokenRetry");
    return false;                       /* 已經重整過還是不行 → 讓錯誤顯示出來 */
  }
  sessionStorage.setItem("tokenRetry", "1");
  location.reload();
  return true;
}

function val(name){
  const el = document.querySelector(`input[name=${name}]:checked`);
  return el ? el.value : "";
}
document.querySelectorAll("input[name=days]").forEach(r =>
  r.onchange = () => { const m = $("#modeCard"); if (m) m.style.display = val("days") === "3" ? "" : "none"; });

/* ---- 篩選 ---- */
const ALIGN_ZH = {
  strict_bull:"嚴格多頭", loose_bull:"寬鬆多頭", squeeze:"均線糾結",
  loose_bear:"寬鬆空頭", strict_bear:"嚴格空頭", none:"無序"
};
function alignName(k){ return t("al." + k, ALIGN_ZH[k] || k); }
function nhName(k){ return t("nh." + k, NH_LABEL[k] || k); }
function yoyName(k){ return t("yoy." + k, YOY_LABEL[k] || k); }
let lastRows = [], lastMeta = {};

if ($("#go1")) $("#go1").onclick = () => {
  const params = {
    universe_n: parseInt(val("universe"), 10),
    ma: parseInt(val("ma"), 10),
    direction: val("direction"),
    days: parseInt(val("days"), 10),
    match: val("mode") || "any",
    align: val("align")
  };
  $("#go1").disabled = true;
  $("#result1").innerHTML = "";
  $("#status1").textContent = "";
  brewOpen(t("st.send","送出篩選條件…"));
  fetch("/api/screen", {
    method:"POST", headers:{"Content-Type":"application/json","X-App-Token":APP_TOKEN},
    body: JSON.stringify(params)
  }).then(r => r.json()).then(j => {
    if (!j.job){
      brewClose(); $("#go1").disabled = false;
      if (retryOnStaleToken(j)) return;
      $("#status1").textContent = j.error || t("st.nojob","無法建立工作"); return; }
    poll(j.job);
  }).catch(e => { brewClose(); $("#go1").disabled = false;
    $("#status1").textContent = t("st.conn","連線失敗：") + e; });
};

function poll(id){
  fetch("/api/job/" + id).then(r => r.json()).then(j => {
    if (!j.done){
      brewProgress(j.progress, j.status);
      setTimeout(() => poll(id), 900);
      return;
    }
    brewClose();
    $("#go1").disabled = false;
    sessionStorage.removeItem("tokenRetry");
    if (j.error){ $("#status1").textContent = t("st.failed","篩選失敗：") + j.error; return; }
    render(j.result);
  }).catch(e => { brewClose(); $("#go1").disabled = false;
    $("#status1").textContent = t("st.lost","連線中斷：") + e; });
}

function render(res){
  lastRows = res.rows || [];
  lastMeta = {as_of: res.as_of, ma_name_zh: res.ma_name_zh, ma_name: res.ma_name};
  const showAlign = val("align") === "none";
  const showQ = hasQuote(res.quote);
  const per = lastRows.find(r => r.period);
  $("#status1").innerHTML = t("st.asof","資料日期") + " " + (res.as_of || "—")
    + (per ? "｜" + t("st.quarter","財報季") + " " + per.period : "")
    + "｜" + (LANG === "zh" ? res.ma_name_zh : res.ma_name)
    + "（" + (val("direction") === "above" ? t("st.above","站上") : t("st.below","跌破")) + "）"
    + "｜" + t("st.match","符合") + " <span class=\"count\">" + lastRows.length + "</span> "
    + t("st.unit","檔") + quoteNote(res.quote);
  if (!lastRows.length){ $("#result1").innerHTML = "<div class='status'>" + t("st.none","沒有符合條件的股票。") + "</div>"; return; }

  let h = "";
  if (lastRows.length > 15){
    const c = {}, label = {};
    lastRows.forEach(s => {
      const k = sectorKey(s);
      c[k] = (c[k] || 0) + 1;
      label[k] = coSector(s);
    });
    const names = Object.keys(c).sort((a,b) => c[b] - c[a]);
    h += "<div class='resfilter'><span class='rflabel'>" + t("flt.sector","產業") + "</span><select id='secFilter' onchange='applyFilter()'>"
       + "<option value=''>" + t("flt.allSector","全部產業") + "（" + lastRows.length + "）</option>"
       + names.map(n => "<option value=\"" + n + "\">" + label[n] + "（" + c[n] + "）</option>").join("")
       + "</select>"
       + bucketSelect("epsFilter", t("flt.eps","季EPS年增"), lastRows, r => yoyBucket(r.eps_yoy), YOY_LABEL, "applyFilter()")
       + (showAlign ? alignSelect("alignFilter", lastRows, "applyFilter()") : "")
       + nhSelect("nhFilter", lastRows, "applyFilter()")
       + "</div>";
  }
  h += "<div class='tblwrap res-wide'><table><thead><tr>"
     + "<th>" + t("th.rank","市值排名") + "</th><th>" + t("th.sym","代號")
     + "</th><th>" + t("th.name","公司名稱") + "</th><th>" + t("th.sector","產業") + "</th>"
     + "<th>" + t("th.close","收盤") + "</th>"
     + (showQ ? "<th>" + t("th.last","現價") + "</th><th>"
              + t("th.lastgap","與收盤差%") + "</th>" : "")
     + "<th>" + t("th.gap","均線乖離%") + "</th>"
     + "<th>" + t("th.eps","季EPS年增") + "</th><th>" + t("th.rev","季營收年增")
     + "</th><th>" + t("th.nh","創新高") + "</th>"
     + (showAlign ? "<th>" + t("th.align","均線排列") + "</th>" : "")
     + "<th>" + t("th.hit","符合日期") + "</th></tr></thead><tbody id='tb1'>" + rowsHtml(lastRows, showAlign, showQ)
     + "</tbody></table></div>";
  h += "<div id='cd1'>" + cardsHtml(lastRows, showAlign, t("th.hit","符合日期"), showQ) + "</div>";
  $("#result1").innerHTML = h;
}

/* ---- 創新高（與後端 NH_TIERS / NH_LABEL 對應）---- */
const NH_LABEL = {"3y": "3年新高", "2y": "2年新高", "1y": "1年新高",
                  "6m": "半年新高", "3m": "3個月新高"};
const NH_ORDER = ["3y", "2y", "1y", "6m", "3m"];
function fmtNH(v){
  if (!v) return "—";
  return "<b style='color:var(--caramel-2)'>" + nhName(v) + "</b>";
}

/* ---- 年增率級距（與後端 yoy_bucket 對應）---- */
const YOY_LABEL = {neg:"負成長", lo:"0～20%", mid:"20～50%", hi:"50% 以上"};
function yoyBucket(v){
  if (v == null) return null;
  return v < 0 ? "neg" : (v < 20 ? "lo" : (v < 50 ? "mid" : "hi"));
}

/* 均線排列下拉。只在「均線排列條件＝不限」時才出現 ——
   若使用者已經指定了排列，結果全都是同一種，再放一個選單沒有意義。
   選項依實際結果動態產生，排序固定為 多頭 → 糾結 → 空頭 → 無序。 */
const ALIGN_ORDER = ["strict_bull", "loose_bull", "squeeze", "loose_bear", "strict_bear", "none"];
function alignSelect(id, rows, handler){
  const c = {};
  rows.forEach(r => { c[r.align] = (c[r.align] || 0) + 1; });
  const keys = ALIGN_ORDER.filter(k => c[k]);
  if (keys.length <= 1) return "";          /* 只有一種就不必篩 */
  return "<span class='rflabel'>" + t("flt.align","均線排列") + "</span><select id='" + id
       + "' onchange='" + handler + "'><option value=''>" + t("flt.any","不限")
       + "（" + rows.length + "）</option>"
       + keys.map(k => "<option value='" + k + "'>" + alignName(k)
                     + "（" + c[k] + "）</option>").join("")
       + "</select>";
}

/* 創新高下拉。選「1年新高」時只顯示創 1 年新高的；
   另外提供「有創新高」把三種級距一起看。 */
function nhSelect(id, rows, handler){
  const c = {};
  rows.forEach(r => { if (r.new_high) c[r.new_high] = (c[r.new_high] || 0) + 1; });
  const keys = NH_ORDER.filter(k => c[k]);
  if (!keys.length) return "";
  const any = keys.reduce((a, k) => a + c[k], 0);
  return "<span class='rflabel'>" + t("flt.nh","創新高") + "</span><select id='" + id
       + "' onchange='" + handler + "'><option value=''>" + t("flt.any","不限")
       + "（" + rows.length + "）</option>"
       + "<option value='any'>" + t("flt.hasNH","有創新高") + "（" + any + "）</option>"
       + keys.map(k => "<option value='" + k + "'>" + nhName(k)
                     + "（" + c[k] + "）</option>").join("")
       + "</select>";
}

/* 產生一個級距下拉；該欄全部沒資料時回空字串（不要放一個沒用的選單） */
function bucketSelect(id, label, rows, fn, labels, handler){
  const c = {};
  rows.forEach(r => { const b = fn(r); if (b) c[b] = (c[b] || 0) + 1; });
  const keys = Object.keys(labels).filter(k => c[k]);
  if (!keys.length) return "";
  return "<span class='rflabel'>" + label + "</span><select id='" + id
       + "' onchange='" + handler + "'><option value=''>" + t("flt.any","不限") + "</option>"
       + keys.map(k => "<option value='" + k + "'>" + yoyName(k) + "（" + c[k] + "）</option>").join("")
       + "</select>";
}

/* ---- 現價 ----
   資料來自另一個端點（/quote/info），與收盤價是兩條獨立的路。
   均線與創新高一律用收盤價算，這裡只是把「隔夜跳空」變成看得見的資訊。
   抓不到現價的個股顯示「—」，不影響其他欄位。 */
const GAP_WARN = 3.0;                    /* 差幅超過這個百分比就標紅提醒 */
function fmtLast(s){
  return (s.last == null) ? "—" : s.last.toFixed(2);
}
function fmtLastPct(s){
  if (s.last_pct == null) return "—";
  const big = Math.abs(s.last_pct) >= GAP_WARN;
  return "<span class='" + (s.last_pct >= 0 ? "pos" : "neg") + "'>"
       + (s.last_pct >= 0 ? "+" : "") + s.last_pct.toFixed(2) + "%"
       + (big ? " ⚠️" : "") + "</span>";
}
/* 報價狀態：讓使用者一眼知道這個價格是什麼時候、哪個時段的。
   不標「延遲」——實測 isRealTime=True，標錯反而誤導。 */
function quoteNote(q){
  if (q && q.open === false) return "｜" + t("q.closed","美股休市中，顯示收盤價");
  if (!q || !q.ts) return "";
  const kind = {regular:  t("q.regular","盤中"),
                extended: t("q.extended","盤前／盤後"),
                close:    t("q.close","已收盤")}[q.kind] || "";
  return "｜" + t("q.last","現價") + " " + kind + " " + q.ts;
}
/* 休市時整組現價欄位都不要出現 —— 全是「—」的兩欄只是白佔寬度。
   ⚠️ 表頭、資料列、卡片三個地方都吃這個旗標，改的時候要一起改。 */
function hasQuote(q){ return !!(q && q.ts); }

/* 基本面欄位的顯示：抓不到就顯示「—」，不要留空白讓人以為壞掉 */
function fmtYoY(v){ return (v == null) ? "—" : (v >= 0 ? "+" : "") + v.toFixed(1) + "%"; }
function yoyCls(v){ return (v == null) ? "" : (v >= 0 ? "pos" : "neg"); }

/* 符合日期：檢查多天時一併顯示「符合幾天」，否則看不出「部分符合」的差別 */
function fmtHit(s){
  const d = (s.hit_date || "").slice(5);           /* MM-DD */
  if (!s.days || s.days <= 1) return d;
  return d + " <small style='color:var(--mocha)'>(" + s.hit_days + "/" + s.days + ")</small>";
}

function rowsHtml(rows, showAlign, showQ){
  return rows.map(s =>
    "<tr data-sector=\"" + sectorKey(s) + "\">"
    + "<td>" + s.rank + "</td><td><b>" + s.symbol + "</b></td>"
    + "<td class='coname' title=\"" + s.name + "\">" + coName(s) + "</td>"
    + "<td class='sector' title=\"" + s.sector + "\">" + coSector(s) + "</td>"
    + "<td>" + s.price.toFixed(2) + "</td>"
    + (showQ ? "<td>" + fmtLast(s) + "</td><td>" + fmtLastPct(s) + "</td>" : "")
    + "<td class='" + (s.gap >= 0 ? "pos" : "neg") + "'>" + (s.gap >= 0 ? "+" : "") + s.gap.toFixed(2) + "%</td>"
    + "<td class='" + yoyCls(s.eps_yoy) + "'>" + fmtYoY(s.eps_yoy) + "</td>"
    + "<td class='" + yoyCls(s.rev_yoy) + "'>" + fmtYoY(s.rev_yoy) + "</td>"
    + "<td>" + fmtNH(s.new_high) + "</td>"
    + (showAlign ? "<td>" + alignName(s.align) + "</td>" : "")
    + "<td>" + fmtHit(s) + "</td></tr>").join("");
}

/* ---- 手機版卡片 ----
   ⚠️ CSS 的 @media(max-width:640px) 會把 .res-wide 整個 display:none、
   改顯示 .res-cards。**所以每個輸出表格的地方都必須同時輸出卡片**，
   否則手機上會只剩狀態列、下面一片空白（狀態列還會顯示「符合 N 檔」，
   看起來像資料抓不到，其實是版面問題）。這個坑踩過，見變更紀錄。 */
function cardsHtml(rows, showAlign, lastLabel, showQ){
  return "<div class='res-cards'>" + rows.map((s, i) =>
    "<details class='scard' data-i='" + i + "'>"
    /* 卡片標題列優先顯示現價（手機上只看得到這一行，要放最新的那個數字） */
    + "<summary><span class='sc-l'><b>" + s.symbol + "</b> " + coName(s) + "</span>"
    + "<span class='sc-r'>" + (showQ && s.last != null ? fmtLast(s) : s.price.toFixed(2)) + "</span></summary>"
    + "<div class='scard-body'>"
    + "<div class='kv'><span>" + t("th.close","收盤") + "</span><b>" + s.price.toFixed(2) + "</b></div>"
    + (showQ ? "<div class='kv'><span>" + t("th.lastgap","與收盤差%")
             + "</span><b>" + fmtLastPct(s) + "</b></div>" : "")
    + "<div class='kv'><span>" + t("th.rank","市值排名") + "</span><b>" + s.rank + "</b></div>"
    + "<div class='kv'><span>" + t("th.sector","產業") + "</span><b>" + coSector(s) + "</b></div>"
    + "<div class='kv'><span>" + t("th.gap","均線乖離%") + "</span><b class='"
      + (s.gap >= 0 ? "pos" : "neg") + "'>" + (s.gap >= 0 ? "+" : "") + s.gap.toFixed(2) + "%</b></div>"
    + "<div class='kv'><span>" + t("th.eps","季EPS年增") + "</span><b class='"
      + yoyCls(s.eps_yoy) + "'>" + fmtYoY(s.eps_yoy) + "</b></div>"
    + "<div class='kv'><span>" + t("th.rev","季營收年增") + "</span><b class='"
      + yoyCls(s.rev_yoy) + "'>" + fmtYoY(s.rev_yoy) + "</b></div>"
    + "<div class='kv'><span>" + t("th.nh","創新高") + "</span><b>" + fmtNH(s.new_high) + "</b></div>"
    + (showAlign ? "<div class='kv'><span>" + t("th.align","均線排列")
                 + "</span><b>" + alignName(s.align) + "</b></div>" : "")
    + "<div class='kv'><span>" + lastLabel + "</span><b>" + fmtHit(s) + "</b></div>"
    + "</div></details>").join("") + "</div>";
}

function applyFilter(){ applyAll("tb1", "cd1", lastRows, "secFilter", "epsFilter", "alignFilter", "nhFilter"); }

/* ---- 飆股拉回找買點 ---- */
let lastRows3 = [], lastMeta3 = {};
if ($("#go3")) $("#go3").onclick = () => {
  const params = {
    universe_n: parseInt(val("universe3"), 10),
    ma: parseInt(val("ma3"), 10),
    align: val("align3")
  };
  $("#go3").disabled = true;
  $("#result3").innerHTML = "";
  $("#status3").textContent = "";
  brewOpen(t("st.send","送出篩選條件…"));
  fetch("/api/pullback", {
    method:"POST", headers:{"Content-Type":"application/json","X-App-Token":APP_TOKEN},
    body: JSON.stringify(params)
  }).then(r => r.json()).then(j => {
    if (!j.job){
      brewClose(); $("#go3").disabled = false;
      if (retryOnStaleToken(j)) return;
      $("#status3").textContent = j.error || t("st.nojob","無法建立工作"); return; }
    poll3(j.job);
  }).catch(e => { brewClose(); $("#go3").disabled = false;
    $("#status3").textContent = t("st.conn","連線失敗：") + e; });
};

function poll3(id){
  fetch("/api/job/" + id).then(r => r.json()).then(j => {
    if (!j.done){ brewProgress(j.progress, j.status); setTimeout(() => poll3(id), 900); return; }
    brewClose();
    $("#go3").disabled = false;
    sessionStorage.removeItem("tokenRetry");
    if (j.error){ $("#status3").textContent = t("st.failed","篩選失敗：") + j.error; return; }
    render3(j.result);
  }).catch(e => { brewClose(); $("#go3").disabled = false;
    $("#status3").textContent = t("st.lost","連線中斷：") + e; });
}

function render3(res){
  lastRows3 = res.rows || [];
  lastMeta3 = {as_of: res.as_of, band: res.band,
               ma_name_zh: res.ma_name_zh, ma_name: res.ma_name};
  const showAlign = val("align3") === "none";
  const showQ = hasQuote(res.quote);
  const per3 = lastRows3.find(r => r.period);
  $("#status3").innerHTML = t("st.asof","資料日期") + " " + (res.as_of || "—")
    + (per3 ? "｜" + t("st.quarter","財報季") + " " + per3.period : "")
    + "｜" + t("st.backto","收盤回到") + " "
    + (LANG === "zh" ? res.ma_name_zh : res.ma_name) + " ±" + res.band + "%"
    + "｜" + t("st.match","符合") + " <span class=\"count\">" + lastRows3.length + "</span> "
    + t("st.unit","檔") + quoteNote(res.quote);
  if (!lastRows3.length){
    $("#result3").innerHTML = "<div class='status'>" + t("st.none","沒有符合條件的股票。") + "</div>"; return; }

  let h = "";
  if (lastRows3.length > 15){
    const c = {}, label = {};
    lastRows3.forEach(s => {
      const k = sectorKey(s);
      c[k] = (c[k] || 0) + 1;
      label[k] = coSector(s);
    });
    const names = Object.keys(c).sort((a,b) => c[b] - c[a]);
    h += "<div class='resfilter'><span class='rflabel'>" + t("flt.sector","產業") + "</span><select id='secFilter3' onchange='applyFilter3()'>"
       + "<option value=''>" + t("flt.allSector","全部產業") + "（" + lastRows3.length + "）</option>"
       + names.map(n => "<option value=\"" + n + "\">" + label[n] + "（" + c[n] + "）</option>").join("")
       + "</select>"
       + bucketSelect("epsFilter3", t("flt.eps","季EPS年增"), lastRows3, r => yoyBucket(r.eps_yoy), YOY_LABEL, "applyFilter3()")
       + (showAlign ? alignSelect("alignFilter3", lastRows3, "applyFilter3()") : "")
       + nhSelect("nhFilter3", lastRows3, "applyFilter3()")
       + "</div>";
  }
  h += "<div class='tblwrap res-wide'><table><thead><tr>"
     + "<th>" + t("th.rank","市值排名") + "</th><th>" + t("th.sym","代號")
     + "</th><th>" + t("th.name","公司名稱") + "</th><th>" + t("th.sector","產業") + "</th>"
     + "<th>" + t("th.close","收盤") + "</th>"
     + (showQ ? "<th>" + t("th.last","現價") + "</th><th>"
              + t("th.lastgap","與收盤差%") + "</th>" : "")
     + "<th>" + t("th.gap","均線乖離%") + "</th>"
     + "<th>" + t("th.eps","季EPS年增") + "</th><th>" + t("th.rev","季營收年增")
     + "</th><th>" + t("th.nh","創新高") + "</th>"
     + (showAlign ? "<th>" + t("th.align","均線排列") + "</th>" : "")
     + "<th>" + t("th.asof","資料日期") + "</th></tr></thead><tbody id='tb3'>"
     + rowsHtml(lastRows3, showAlign, showQ) + "</tbody></table></div>";
  h += "<div id='cd3'>" + cardsHtml(lastRows3, showAlign, t("th.asof","資料日期"), showQ) + "</div>";
  $("#result3").innerHTML = h;
}

function applyFilter3(){ applyAll("tb3", "cd3", lastRows3, "secFilter3", "epsFilter3", "alignFilter3", "nhFilter3"); }

/* 三個條件同時成立才顯示（AND）。用列的索引對回原始資料，
   避免從 DOM 反推數值時被格式化字串（「—」「+12.3%」）搞混。

   ⚠️ **表格與卡片要一起篩**。只篩表格的話，手機上按下拉選單完全沒反應
   —— 因為手機看到的是卡片，表格早就被 CSS 隱藏了。 */
function applyAll(tbId, cdId, rows, secId, epsId, alignId, nhId){
  const sec = $("#" + secId) ? $("#" + secId).value : "";
  const eps = $("#" + epsId) ? $("#" + epsId).value : "";
  const alg = (alignId && $("#" + alignId)) ? $("#" + alignId).value : "";
  const nh  = (nhId && $("#" + nhId)) ? $("#" + nhId).value : "";

  function pass(r){
    if (!r) return true;
    if (sec && r.sector !== sec) return false;
    if (eps && yoyBucket(r.eps_yoy) !== eps) return false;
    if (alg && r.align !== alg) return false;
    if (nh === "any" && !r.new_high) return false;
    if (nh && nh !== "any" && r.new_high !== nh) return false;
    return true;
  }

  document.querySelectorAll("#" + tbId + " tr").forEach((tr, i) => {
    tr.style.display = pass(rows[i]) ? "" : "none";
  });
  document.querySelectorAll("#" + cdId + " .scard").forEach((cd, i) => {
    cd.style.display = pass(rows[i]) ? "" : "none";
  });
}

/* ---- 大盤詳細數據：市場寬度的歷史折線圖 ----
   ⚠️ **展開才抓**，收合再展開不重複請求（照台股版 baro-box 的做法）。
      首頁每個訪客都會載入，不能一進來就打 API。
   ⚠️ 折線圖用**內嵌 SVG 自己畫**，不引外部圖表庫 ——
      這個專案刻意只有 flask/requests/gunicorn，前端也維持零依賴。 */
const brBox = $("#brBox");
brBox && brBox.addEventListener("toggle", () => {
  if (!brBox.open || brBox.dataset.loaded) return;
  brBox.dataset.loaded = "1";
  $("#brStatus").textContent = t("br.loading", "載入中…");
  fetch("/api/breadth", { headers: { "X-App-Token": APP_TOKEN } })
    .then(r => r.json())
    .then(j => {
      if (!j.ok) throw new Error(j.error || "no data");
      $("#brStatus").textContent = "";
      $("#brBody").innerHTML = breadthHtml(j);
      wireBreadthHover(j);        /* ⚠️ innerHTML 之後才綁，元素這時才存在 */
    })
    .catch(() => {
      /* ⚠️ 讀不到就整塊收掉，**不要顯示「無法判斷」** —— 那看起來像壞掉。 */
      brBox.style.display = "none";
    });
});

/* 折線圖的游標互動：移到哪一天就顯示那天的日期與寬度。
   ⚠️ 用 pointer 事件（滑鼠與觸控共用一套），不要分別綁 mouse/touch。
   ⚠️ SVG 是 width:100% 縮放的，**client 座標不等於 viewBox 座標**，
      一定要用 getBoundingClientRect() 換算，否則在手機上會整個對不準。 */
function wireBreadthHover(j){
  const svg = $("#brSvg"), read = $("#brRead"),
        guide = $("#brGuide"), dot = $("#brDot");
  if (!svg || !read) return;
  const S = j.series || [];
  if (!S.length) return;
  const PAD_L = +svg.dataset.padl, PAD_R = +svg.dataset.padr,
        PAD_T = +svg.dataset.padt, PAD_B = +svg.dataset.padb,
        W = +svg.dataset.w, H = +svg.dataset.h;
  const iw = W - PAD_L - PAD_R, ih = H - PAD_T - PAD_B;
  const xOf = i => PAD_L + (S.length < 2 ? 0 : i / (S.length - 1) * iw);
  const yOf = v => PAD_T + (100 - v) / 100 * ih;

  const fmt = (d, v) => (LANG === "en")
    ? `${d} · ${v.toFixed(1)}% above ${j.breadth_ma}MA`
    : `${d} · ${v.toFixed(1)}% 站上 ${j.breadth_ma} 日均線`;
  /* 沒在指的時候顯示最新一天，不要留白 */
  const rest = () => {
    read.textContent = fmt(S[S.length - 1][0], S[S.length - 1][1]);
    guide.setAttribute("opacity", "0");
    dot.setAttribute("opacity", "0");
  };
  rest();

  function at(clientX){
    const r = svg.getBoundingClientRect();
    const vx = (clientX - r.left) / r.width * W;          // client → viewBox
    let i = Math.round((vx - PAD_L) / iw * (S.length - 1));
    i = Math.max(0, Math.min(S.length - 1, i));
    const [d, v] = S[i];
    read.textContent = fmt(d, v);
    const gx = xOf(i).toFixed(1);
    guide.setAttribute("x1", gx); guide.setAttribute("x2", gx);
    guide.setAttribute("opacity", ".35");
    dot.setAttribute("cx", gx); dot.setAttribute("cy", yOf(v).toFixed(1));
    dot.setAttribute("opacity", "1");
  }
  svg.addEventListener("pointermove", e => { e.preventDefault(); at(e.clientX); });
  svg.addEventListener("pointerdown", e => { e.preventDefault(); at(e.clientX); });
  svg.addEventListener("pointerleave", rest);
  svg.addEventListener("pointercancel", rest);
}

function breadthHtml(j){
  const S = j.series || [];
  if (!S.length) return "";
  const W = 560, H = 150, PAD_L = 30, PAD_R = 8, PAD_T = 10, PAD_B = 18;
  const iw = W - PAD_L - PAD_R, ih = H - PAD_T - PAD_B;
  const x = i => PAD_L + (S.length < 2 ? 0 : i / (S.length - 1) * iw);
  const y = v => PAD_T + (100 - v) / 100 * ih;   /* 寬度固定 0~100%，不自動縮放 */
  const pts = S.map((r, i) => x(i).toFixed(1) + "," + y(r[1]).toFixed(1)).join(" ");
  /* 頂部／洗盤兩條門檻線：折線圖的重點是「現在離門檻多遠」，不是絕對值 */
  const line = (v, c, lb) =>
    `<line x1="${PAD_L}" x2="${W - PAD_R}" y1="${y(v).toFixed(1)}" y2="${y(v).toFixed(1)}"
       stroke="${c}" stroke-width="1" stroke-dasharray="4 3" opacity=".7"/>
     <text x="${PAD_L - 4}" y="${(y(v) + 3).toFixed(1)}" text-anchor="end"
       font-size="9" fill="${c}" font-family="var(--font-num)">${lb}</text>`;
  const yr = v =>
    `<text x="${PAD_L - 4}" y="${(y(v) + 3).toFixed(1)}" text-anchor="end"
       font-size="9" fill="#aaa" font-family="var(--font-num)">${v}</text>`;
  const first = S[0][0], last = S[S.length - 1][0];
  const cur = S[S.length - 1][1];

  /* ⚠️ 幾何參數要交給 hover 用，寫成 data-* 掛在 svg 上，
     不要在兩處各算一次 —— 那遲早會不一致。 */
  const svg = `<div id="brRead" style="font-family:var(--font-num);font-size:12px;
      color:var(--mocha);height:16px;margin-bottom:2px"></div>
    <svg id="brSvg" viewBox="0 0 ${W} ${H}" style="width:100%;height:auto;display:block;
      touch-action:none"
      data-padl="${PAD_L}" data-padr="${PAD_R}" data-padt="${PAD_T}" data-padb="${PAD_B}"
      data-w="${W}" data-h="${H}">
    ${yr(0)}${yr(50)}${yr(100)}
    <line x1="${PAD_L}" x2="${W - PAD_R}" y1="${y(50)}" y2="${y(50)}"
      stroke="#ddd" stroke-width="1"/>
    ${line(j.top, "#CB4B3A", j.top + "%")}
    ${line(j.wash, "#4A7C64", j.wash + "%")}
    <polyline points="${pts}" fill="none" stroke="var(--caramel-2)"
      stroke-width="1.6" stroke-linejoin="round"/>
    <circle cx="${x(S.length - 1).toFixed(1)}" cy="${y(cur).toFixed(1)}" r="2.8"
      fill="var(--caramel-2)"/>
    <line id="brGuide" y1="${PAD_T}" y2="${H - PAD_B}" stroke="var(--mocha)"
      stroke-width="1" opacity="0"/>
    <circle id="brDot" r="3.2" fill="var(--espresso)" opacity="0"/>
    <text x="${PAD_L}" y="${H - 4}" font-size="9" fill="#aaa"
      font-family="var(--font-num)">${first}</text>
    <text x="${W - PAD_R}" y="${H - 4}" text-anchor="end" font-size="9" fill="#aaa"
      font-family="var(--font-num)">${last}</text>
  </svg>`;

  const kv = (k, v) =>
    `<div style="display:flex;justify-content:space-between;padding:3px 0;
       font-size:13px"><span style="color:var(--mocha)">${k}</span>
       <b style="font-family:var(--font-num)">${v}</b></div>`;

  const head = (LANG === "en")
    ? `% of constituents above their own ${j.breadth_ma}-day average`
    : `成分股站上自己 ${j.breadth_ma} 日均線的比例`;

  /* 指數收盤價。⚠️ 指數與寬度的日期常常差一天（FRED 慢一個交易日），
     所以**各自標各自的日期**，不要共用一個。 */
  let idxHtml = "";
  if (j.idx){
    const q = j.idx;
    const col = q.close > q.ma100 ? "#CB4B3A" : "#4A7C64";
    idxHtml =
      `<div style="font-size:12.5px;color:var(--mocha);margin:2px 0 6px">`
      + (LANG === "en" ? "Nasdaq Composite" : "納斯達克綜合指數")
      + ` <span style="font-family:var(--font-num)">${q.date}</span></div>`
      + `<div style="display:flex;align-items:baseline;gap:10px;margin-bottom:12px">`
      + `<b style="font-family:var(--font-num);font-size:24px;color:var(--espresso)">`
      + q.close.toLocaleString() + `</b>`
      + `<span style="font-size:12.5px;color:${col}">50MA ${q.ma50.toLocaleString()}`
      + ` (${q.gap50 > 0 ? "+" : ""}${q.gap50}%) · 100MA ${q.ma100.toLocaleString()}`
      + ` (${q.gap100 > 0 ? "+" : ""}${q.gap100}%)</span></div>`;
  }

  /* ⚠️ 分位數要一起顯示。單看「72%」不知道那是高是低。
     ⚠️⚠️ **但一定要把區間講出來。** 這裡的分位數只涵蓋圖上這 ${j.span_years} 年，
        而門檻 85%／30% 是用 **10 年回測**訂的 —— 母體不同。
        寫成「歷史中位數」會讓人拿短區間的分位數去比長區間的門檻，結論會錯。 */
  const span = (LANG === "en") ? `${j.span_years}y` : `近 ${j.span_years} 年`;
  const stats =
    kv(LANG === "en" ? "Current" : "目前寬度",
       j.cur + "%  (P" + j.cur_pct + " / " + span + ")") +
    kv(LANG === "en" ? `Lowest in ${j.wash_look} days` : `近 ${j.wash_look} 日最低`,
       j.wash_min + "%") +
    kv(LANG === "en" ? `Median (${span})` : `${span}中位數`, j.p["50"] + "%") +
    kv(LANG === "en" ? `P25 / P75 (${span})` : `${span} P25 ／ P75`,
       j.p["25"] + "% / " + j.p["75"] + "%");

  const note = (LANG === "en")
    ? `<p style="font-size:12px;color:var(--mocha);line-height:1.8;margin:10px 0 0">
       The red line is the <b>top threshold (${j.top}%)</b>; the green line is the
       <b>washout threshold (${j.wash}%)</b>. The index versus 50MA identifies a
       healthy trend or normal pullback; a break below 100MA marks a headwind.
       Breadth uses 150MA mainly to identify whether the market was washed out.<br>
       Percentiles above cover the ${j.span_years} years shown here; the
       ${j.top}%/${j.wash}% thresholds were set from a 10-year backtest.<br>
       Historical breadth is recalculated using today's constituents, so earlier
       values may be biased upward (survivorship bias).</p>`
    : `<p style="font-size:12px;color:var(--mocha);line-height:1.8;margin:10px 0 0">
       紅線是<b>頂部門檻 ${j.top}%</b>，綠線是<b>洗盤門檻 ${j.wash}%</b>。
       指數與 50MA 判斷順風或正常回檔，跌破 100MA 才進入逆風；
       150MA 寬度主要判斷市場是否曾被充分洗盤。近 ${j.wash_look} 日洗過後，
       收復 50MA 是初步復甦，收復 100MA 是復甦確認。<br>
       ⚠️ 上面的分位數只涵蓋圖上這 ${j.span_years} 年；
       ${j.top}%／${j.wash}% 的門檻是用 10 年回測訂的，兩者母體不同。<br>
       歷史寬度以今日成分股回算，較早數值可能因存活者偏誤而偏高。</p>`;

  return idxHtml
       + `<div style="font-size:12.5px;color:var(--mocha);margin:2px 0 6px">${head}</div>`
       + svg + `<div style="margin-top:10px">${stats}</div>` + note;
}

/* ---- 升級專業版：創新高／RS ---- */
let lastProHigh = null, lastProRs = null;
const proPct = v => `<span class="${Number(v) >= 0 ? 'pos' : 'neg'}">${Number(v) >= 0 ? '+' : ''}${Number(v).toFixed(2)}%</span>`;
const proKv = (k, v) => `<div class="kv"><span>${k}</span><b>${v}</b></div>`;

function runProJob(url, params, button, status, done){
  button.disabled = true; status.textContent = "";
  brewOpen(t("st.send","送出篩選條件…"));
  fetch(url, {method:"POST", headers:{"Content-Type":"application/json","X-App-Token":APP_TOKEN},
    body:JSON.stringify(params)}).then(r => r.json()).then(j => {
      if (!j.job){ brewClose(); button.disabled=false; if (retryOnStaleToken(j)) return;
        status.textContent=j.error||t("st.nojob","無法建立工作"); return; }
      const pollPro = () => fetch("/api/job/"+j.job).then(r=>r.json()).then(x => {
        if (!x.done){ brewProgress(x.progress,x.status); setTimeout(pollPro,500); return; }
        brewClose(); button.disabled=false;
        if (x.error){ status.textContent=t("st.failed","篩選失敗：")+x.error; return; }
        done(x.result);
      }).catch(e=>{ brewClose(); button.disabled=false; status.textContent=t("st.conn","連線失敗：")+e; });
      pollPro();
  }).catch(e=>{ brewClose(); button.disabled=false; status.textContent=t("st.conn","連線失敗：")+e; });
}

function proHighFilter(){
  const box=$("#proHighResult"); if(!box) return;
  const sec=box.querySelector('[data-pro-filter="sector"]')?.value||"";
  const high=box.querySelector('[data-pro-filter="high"]')?.value||"";
  let shown=0;
  box.querySelectorAll("[data-pro-row]").forEach(el=>{
    const ok=(!sec||el.dataset.sector===sec)&&(!high||el.dataset.high===high);
    el.style.display=ok?"":"none"; if(ok&&el.tagName==="TR") shown++;
  });
  const count=box.querySelector("[data-pro-count]"); if(count) count.textContent=(LANG==="en"?"Filtered: ":"篩選後：")+shown;
}

function renderProHigh(j){
  lastProHigh=j; const rows=j.rows||[];
  $("#proHighStatus").innerHTML=(LANG==="en"
    ? `Top ${j.scanned}, any of last ${j.days} day(s): <span class="count">${rows.length}</span> new-high stocks`
    : `掃描市值前 ${j.scanned} 大（近 ${j.days} 日任一天）：<span class="count">${rows.length}</span> 檔創新高`) + ` · ${j.as_of||"—"}`;
  if(!rows.length){ $("#proHighResult").innerHTML=`<div class="concl gray">${LANG==="en"?"No stocks match.":"目前沒有股票符合創新高條件。"}</div>`; return; }
  const sectors={}, highs={}; rows.forEach(s=>{sectors[s.sector]=(sectors[s.sector]||0)+1;highs[s.new_high]=(highs[s.new_high]||0)+1;});
  let so=`<option value="">${LANG==="en"?"All sectors":"全部產業"}（${rows.length}）</option>`;
  Object.keys(sectors).sort((a,b)=>sectors[b]-sectors[a]).forEach(k=>so+=`<option value="${k}">${LANG==="en"?k:zhSectorFromRows(rows,k)}（${sectors[k]}）</option>`);
  let ho=`<option value="">${LANG==="en"?"All high levels":"全部新高程度"}（${rows.length}）</option>`;
  ["3y","2y","1y","6m","3m"].filter(k=>highs[k]).forEach(k=>ho+=`<option value="${k}">${nhName(k)}（${highs[k]}）</option>`);
  const filters=`<div class="resfilter"><span class="rflabel">${t("flt.sector","產業")}</span><select data-pro-filter="sector" onchange="proHighFilter()">${so}</select>`
    + `<span class="rflabel">${t("flt.nh","新高程度")}</span><select data-pro-filter="high" onchange="proHighFilter()">${ho}</select><span class="rflabel" data-pro-count>${LANG==="en"?"Filtered: ":"篩選後："}${rows.length}</span></div>`;
  let trs="", cards=""; rows.forEach(s=>{const name=coName(s),sector=coSector(s),high=nhName(s.new_high);
    trs+=`<tr data-pro-row data-sector="${s.sector}" data-high="${s.new_high}"><td>${s.rank}</td><td><b>${s.symbol}</b></td><td>${name}</td><td>${sector}</td><td><b>${high}</b></td><td>${s.hit_date}</td></tr>`;
    cards+=`<details class="scard" data-pro-row data-sector="${s.sector}" data-high="${s.new_high}"><summary><span class="sc-l"><b>${s.symbol}</b> ${name}</span><span class="sc-r">${high}</span></summary><div class="scard-body">${proKv(t("th.rank","市值排名"),s.rank)}${proKv(t("th.sector","產業"),sector)}${proKv(t("th.nh","創新高"),high)}${proKv(LANG==="en"?"Matched on":"符合日期",s.hit_date)}</div></details>`;
  });
  $("#proHighResult").innerHTML=filters+`<div class="res-wide"><table><tr><th>${t("th.rank","排名")}</th><th>${t("th.sym","代號")}</th><th>${t("th.name","公司")}</th><th>${t("th.sector","產業")}</th><th>${t("th.nh","創新高")}</th><th>${LANG==="en"?"Matched on":"符合日期"}</th></tr>${trs}</table></div><div class="res-cards">${cards}</div>`;
}
function zhSectorFromRows(rows,key){ const x=rows.find(r=>r.sector===key); return x?(x.sector_zh||key):key; }

function renderProRs(j){
  lastProRs=j; const rows=j.rows||[];
  $("#proRsStatus").innerHTML=(LANG==="en"?`Compared ${j.scanned} stocks over ${j.period} days: `:`比較 ${j.scanned} 檔股票近 ${j.period} 日：`)+`<span class="count">${rows.length}</span> ${LANG==="en"?`scored RS ${j.threshold}+`:`檔 RS ≥ ${j.threshold}`} · ${j.as_of||"—"}`;
  if(!rows.length){$("#proRsResult").innerHTML=`<div class="concl gray">${LANG==="en"?"No stocks match.":"目前沒有股票符合這個 RS 門檻。"}</div>`;return;}
  const sectors={};rows.forEach(s=>sectors[s.sector]=(sectors[s.sector]||0)+1);
  let opts=`<option value="">${LANG==="en"?"All sectors":"全部產業"}（${rows.length}）</option>`;
  Object.keys(sectors).sort((a,b)=>sectors[b]-sectors[a]).forEach(k=>opts+=`<option value="${k}">${LANG==="en"?k:zhSectorFromRows(rows,k)}（${sectors[k]}）</option>`);
  let trs="",cards="";rows.forEach(s=>{const name=coName(s),sector=coSector(s),gain=proPct(s.gain);
    trs+=`<tr data-rs-row data-sector="${s.sector}"><td>${s.rank}</td><td><b>${s.symbol}</b></td><td>${name}</td><td>${sector}</td><td>${s.close}</td><td>${gain}</td><td><span class="rs-score">${s.rs}</span></td></tr>`;
    cards+=`<details class="scard" data-rs-row data-sector="${s.sector}"><summary><span class="sc-l"><b>${s.symbol}</b> ${name}</span><span class="sc-r"><span class="rs-score">${s.rs}</span></span></summary><div class="scard-body">${proKv(t("th.rank","市值排名"),s.rank)}${proKv(t("th.sector","產業"),sector)}${proKv(t("th.close","收盤"),s.close)}${proKv(`${j.period}${LANG==="en"?"-day gain":" 日漲幅"}`,gain)}${proKv("RS",s.rs)}</div></details>`;
  });
  $("#proRsResult").innerHTML=`<div class="resfilter"><span class="rflabel">${t("flt.sector","產業")}</span><select onchange="filterProRs(this.value)">${opts}</select></div><div class="res-wide"><table><tr><th>${t("th.rank","排名")}</th><th>${t("th.sym","代號")}</th><th>${t("th.name","公司")}</th><th>${t("th.sector","產業")}</th><th>${t("th.close","收盤")}</th><th>${j.period}${LANG==="en"?"-day gain":" 日漲幅"}</th><th>RS</th></tr>${trs}</table></div><div class="res-cards">${cards}</div>`;
}
function filterProRs(sector){$("#proRsResult").querySelectorAll("[data-rs-row]").forEach(el=>el.style.display=(!sector||el.dataset.sector===sector)?"":"none");}
if($("#proHighBtn")) $("#proHighBtn").onclick=()=>{ $("#proHighResult").innerHTML=""; runProJob("/api/pro/new-high",{days:Number(val("proHighDays")||1)},$("#proHighBtn"),$("#proHighStatus"),renderProHigh); };
if($("#proRsBtn")) $("#proRsBtn").onclick=()=>{ $("#proRsResult").innerHTML=""; runProJob("/api/pro/rs",{period:Number(val("proRsPeriod")||60),threshold:Number(val("proRsThreshold")||90)},$("#proRsBtn"),$("#proRsStatus"),renderProRs); };

/* ---- 我的績效：時間加權報酬率（TWR）---- */
let twBuilt = false;
const US_TWR_KEY = "us_twr_data";
const twPct = v => `<span class="${v >= 0 ? 'pos' : 'neg'}">${v >= 0 ? '+' : ''}${v.toFixed(2)}%</span>`;
const twMonth = i => LANG === "en"
  ? ["Jan","Feb","Mar","Apr","May","Jun","Jul","Aug","Sep","Oct","Nov","Dec"][i]
  : `${i + 1}月`;

function twSave(){
  if (!twBuilt) return;
  const d = {year: $("#twYear").value, start: $("#twStart").value, cf:[], ev:[]};
  for (let i=0;i<12;i++){
    d.cf[i] = $("#cf"+i).value;
    d.ev[i] = $("#ev"+i).value;
  }
  try { localStorage.setItem(US_TWR_KEY, JSON.stringify(d)); } catch(e){}
  const saved = $("#twSaved");
  saved.textContent = LANG === "en" ? "✓ Saved on this device" : "✓ 已自動儲存於本裝置";
  clearTimeout(window._usTwrSaved);
  window._usTwrSaved = setTimeout(() => { saved.textContent = ""; }, 2000);
}

function buildTwTable(){
  if (twBuilt || !$("#twTable")) return;
  const table = $("#twTable");
  for (let i=0;i<12;i++){
    const tr = document.createElement("tr");
    tr.innerHTML = `<td class="tw-month" data-month="${i}" style="text-align:left">${twMonth(i)}</td>
      <td><input id="cf${i}" type="number" step="0.01" placeholder="0" style="width:100px;padding:6px;border:1px solid #ddd;border-radius:6px"></td>
      <td><input id="ev${i}" type="number" step="0.01" placeholder="—" style="width:110px;padding:6px;border:1px solid #ddd;border-radius:6px"></td>
      <td id="mr${i}" style="text-align:right">—</td><td id="cr${i}" style="text-align:right">—</td>`;
    table.appendChild(tr);
  }
  twBuilt = true;
  $("#twYear").value = String(new Date().getFullYear());
  try {
    const d = JSON.parse(localStorage.getItem(US_TWR_KEY) || "null");
    if (d){
      if (d.year) $("#twYear").value = d.year;
      if (d.start) $("#twStart").value = d.start;
      for (let i=0;i<12;i++){
        if (d.cf && d.cf[i] != null) $("#cf"+i).value = d.cf[i];
        if (d.ev && d.ev[i] != null) $("#ev"+i).value = d.ev[i];
      }
    }
  } catch(e){}
  ["twYear","twStart"].forEach(id => $("#"+id).addEventListener("input", twSave));
  for (let i=0;i<12;i++){
    $("#cf"+i).addEventListener("input", twSave);
    $("#ev"+i).addEventListener("input", twSave);
  }
  $("#twClear").onclick = () => {
    const msg = LANG === "en" ? "Clear all saved performance data? This cannot be undone." : "確定清空所有已輸入的績效資料？此動作無法復原。";
    if (!confirm(msg)) return;
    try { localStorage.removeItem(US_TWR_KEY); } catch(e){}
    $("#twYear").value = String(new Date().getFullYear());
    $("#twStart").value = "";
    for (let i=0;i<12;i++){
      $("#cf"+i).value = ""; $("#ev"+i).value = "";
      $("#mr"+i).textContent = "—"; $("#cr"+i).textContent = "—";
    }
    $("#twResult").innerHTML = ""; $("#statusTw").textContent = "";
    $("#twSaved").textContent = LANG === "en" ? "Cleared" : "已清空";
  };
}

if ($("#twCalc")) $("#twCalc").onclick = () => {
  const start = parseFloat($("#twStart").value);
  if (!start || start <= 0){
    $("#statusTw").textContent = LANG === "en" ? "Enter a starting portfolio value first." : "請先填入期初總資產";
    return;
  }
  let beginning = start, product = 1, filled = 0;
  for (let i=0;i<12;i++){
    $("#mr"+i).textContent = "—"; $("#cr"+i).textContent = "—";
    const ending = parseFloat($("#ev"+i).value);
    if (isNaN(ending)) continue;
    const cashFlow = parseFloat($("#cf"+i).value) || 0;
    if (beginning <= 0){
      $("#statusTw").textContent = LANG === "en" ? `Month ${i+1} has no valid beginning value.` : `第 ${i+1} 月的期初資產為 0，無法計算`;
      return;
    }
    const monthly = (ending - cashFlow) / beginning - 1;
    product *= 1 + monthly; filled++; beginning = ending;
    $("#mr"+i).innerHTML = twPct(monthly * 100);
    $("#cr"+i).innerHTML = twPct((product - 1) * 100);
  }
  if (!filled){
    $("#statusTw").textContent = LANG === "en" ? "Enter at least one month-end portfolio value." : "請至少填入一個月的月底總資產";
    return;
  }
  const cumulative = product - 1;
  const annualized = Math.pow(1 + cumulative, 12 / filled) - 1;
  $("#statusTw").textContent = LANG === "en" ? `${filled} month(s) calculated` : `已統計 ${filled} 個月`;
  const estimated = filled < 12 ? (LANG === "en" ? " (estimated)" : "（依已填月份推估）") : "";
  $("#twResult").innerHTML = `<div class="card">
    <div class="baro-row"><span>${LANG === "en" ? "Cumulative TWR" : "累積報酬率（TWR）"}</span><b style="font-size:20px">${twPct(cumulative*100)}</b></div>
    <div class="baro-row"><span>${LANG === "en" ? "Annualized return" : "年化報酬率"}${estimated}</span><b style="font-size:24px">${twPct(annualized*100)}</b></div>
    <div style="font-size:12px;color:#888;margin-top:8px;line-height:1.7">${LANG === "en"
      ? "Monthly return = (ending value − net deposit) ÷ prior ending value − 1. Returns are geometrically linked; annualized results based on fewer than 12 months are estimates."
      : "每月報酬＝（月底總資產－當月淨存入）÷ 上月底總資產－1；各月以連乘串接。未滿 12 個月的年化數字為推估值。"}</div>
    </div>`;
};

/* ================= 到價提醒（推播）=================
   自台股版移植。⚠️ 沒有帳號：用 localStorage 的 cid 認人，
   訂閱資訊存在伺服器（因為推播必須由伺服器發起）。 */
const VAPID_PUBLIC_KEY = "__VAPID_PUBLIC__";

function clientId(){
  let id = localStorage.getItem("us_push_cid");
  if (!id){ id = "c" + Date.now() + Math.random().toString(36).slice(2, 8);
            localStorage.setItem("us_push_cid", id); }
  return id;
}
function urlB64ToUint8(b64){
  const pad = "=".repeat((4 - b64.length % 4) % 4);
  const s = (b64 + pad).replace(/-/g, "+").replace(/_/g, "/");
  const raw = atob(s);
  return Uint8Array.from([...raw].map(c => c.charCodeAt(0)));
}

let alStocksLoaded = false, alStockList = [], alSugIdx = -1;
async function loadAlertStocks(){
  if (alStocksLoaded) return;
  try {
    const r = await fetch("/api/stocklist", {headers: {"X-App-Token": APP_TOKEN}});
    if (!r.ok) throw new Error("stock list " + r.status);
    alStockList = await r.json();
    alStocksLoaded = true;
  } catch(e){
    $("#alSearch").placeholder = t("alert.loadFail", "股票清單載入失敗，請重新整理");
  }
}
function alRender(items){
  const box = $("#alSuggest");
  alSugIdx = -1;
  if (!items.length){
    box.innerHTML = '<div class="empty">'
      + t("alert.notFound", "找不到符合的股票（僅限市值前 300 大）") + "</div>";
    box.classList.add("show"); return;
  }
  box.innerHTML = items.map((s, i) => {
    const nm = (LANG === "en") ? s.name : (s.name_zh || s.name);
    return '<div data-i="' + i + '" onclick="alPick(\'' + s.code + "','"
      + String(nm).replace(/'/g, "") + '\')"><b>' + s.code + "</b>" + nm + "</div>";
  }).join("");
  box.classList.add("show");
}
async function alSearch(){
  await loadAlertStocks();
  const kw = ($("#alSearch").value || "").trim().toUpperCase();
  if (!kw){ alRender(alStockList.slice(0, 30)); return; }
  const hit = alStockList.filter(s =>
    s.code.indexOf(kw) === 0
    || (s.name || "").toUpperCase().indexOf(kw) >= 0
    || (s.name_zh || "").indexOf($("#alSearch").value.trim()) >= 0).slice(0, 30);
  alRender(hit);
}
function alPick(code, name){
  $("#alStock").value = code + "|" + name;
  $("#alSearch").value = "";
  $("#alSuggest").classList.remove("show");
  const p = $("#alPicked");
  p.innerHTML = "<span>" + t("alert.picked", "已選擇") + "：<b>" + code + " " + name
    + '</b></span><span class="clr" onclick="alClear()">'
    + t("alert.repick", "重新選擇 ✕") + "</span>";
  p.style.display = "flex";
}
function alClear(){
  $("#alStock").value = "";
  $("#alPicked").style.display = "none";
  $("#alSearch").value = "";
  $("#alSearch").focus();
}
function alKey(e){
  const box = $("#alSuggest");
  if (!box.classList.contains("show")) return;
  const rows = box.querySelectorAll("div[data-i]");
  if (!rows.length) return;
  if (e.key === "ArrowDown" || e.key === "ArrowUp"){
    e.preventDefault();
    alSugIdx += (e.key === "ArrowDown") ? 1 : -1;
    if (alSugIdx < 0) alSugIdx = rows.length - 1;
    if (alSugIdx >= rows.length) alSugIdx = 0;
    rows.forEach(r => r.classList.remove("on"));
    rows[alSugIdx].classList.add("on");
    rows[alSugIdx].scrollIntoView({block: "nearest"});
  } else if (e.key === "Enter"){
    e.preventDefault();
    (rows[alSugIdx >= 0 ? alSugIdx : 0]).click();
  } else if (e.key === "Escape"){
    box.classList.remove("show");
  }
}

async function loadAlerts(){
  try {
    const list = await (await fetch("/api/alerts?cid=" + clientId(),
      { headers: { "X-App-Token": APP_TOKEN } })).json();
    const box = $("#alList");
    if (!list.length || !list.map){
      box.innerHTML = '<span style="color:#999">'
        + t("alert.none", "尚無提醒") + "</span>"; return;
    }
    box.innerHTML = list.map(a => `
      <div style="display:flex;justify-content:space-between;align-items:center;
        padding:10px 4px;border-bottom:1px solid #eee">
        <div><b>${a.code} ${a.name}</b> ${t("alert.tgt","目標")} ${a.price}（±2%）<br>
          <span style="font-size:12px;color:#999">${t("alert.exp","到期")} ${a.expires}</span></div>
        <button onclick="delAlert('${a.id}')" title="delete"
          style="background:#c0392b;border:none;color:#fff;width:32px;height:32px;
          border-radius:8px;cursor:pointer;font-size:16px">🗑</button>
      </div>`).join("");
  } catch(e){}
}
async function delAlert(id){
  await fetch("/api/alerts/" + id + "?cid=" + clientId(),
    { method: "DELETE", headers: { "X-App-Token": APP_TOKEN } });
  loadAlerts();
}

/* 取得本裝置的推播訂閱（會要求通知權限）。
   ⚠️ 失敗時要回**具體原因**，不要只說「失敗」——
      iPhone 沒加到主畫面、權限沒開、伺服器沒設金鑰，處理方式完全不同。 */
async function getSubscription(){
  if (!("serviceWorker" in navigator) || !("PushManager" in window))
    return {sub: null, err: t("alert.eNoSupport",
      "此瀏覽器不支援推播（iPhone 請先「加入主畫面」再從桌面圖示開啟）")};
  if (!VAPID_PUBLIC_KEY || VAPID_PUBLIC_KEY.startsWith("__"))
    return {sub: null, err: t("alert.eNoKey", "伺服器尚未設定推播金鑰（VAPID）")};
  try {
    const reg = await navigator.serviceWorker.register("/sw.js");
    const perm = await Notification.requestPermission();
    if (perm !== "granted")
      return {sub: null, err: t("alert.ePerm",
        "通知權限未開啟（請到系統／瀏覽器設定允許通知）")};
    const old = await reg.pushManager.getSubscription();
    const sub = old || await reg.pushManager.subscribe({
        userVisibleOnly: true,
        applicationServerKey: urlB64ToUint8(VAPID_PUBLIC_KEY)
      });
    return {sub, err: null};
  } catch(e){
    return {sub: null, err: t("alert.eSub", "訂閱失敗：") + (e && e.message || e)};
  }
}

$("#alTest") && ($("#alTest").onclick = async () => {
  $("#alTest").disabled = true;
  $("#statusTest").textContent = t("alert.asking", "要求通知權限中…");
  const {sub, err} = await getSubscription();
  if (!sub){ $("#statusTest").textContent = "✗ " + err;
             $("#alTest").disabled = false; return; }
  $("#statusTest").textContent = t("alert.sending", "傳送測試推播中…");
  try {
    const r = await fetch("/api/test-push", { method: "POST",
      headers: {"Content-Type": "application/json", "X-App-Token": APP_TOKEN},
      body: JSON.stringify({subscription: sub, lang: LANG})});
    const j = await r.json();
    $("#statusTest").textContent = j.sent
      ? "✓ " + t("alert.sentOk", "已送出，稍候裝置應跳出通知")
      : "✗ " + (j.error || t("alert.sentNo", "伺服器未送出"));
  } catch(e){ $("#statusTest").textContent = "✗ " + t("msg.netFail", "連線失敗"); }
  $("#alTest").disabled = false;
});

if ($("#alSearch")){
  $("#alSearch").oninput = alSearch;
  $("#alSearch").onfocus = alSearch;
  $("#alSearch").onkeydown = alKey;
}
document.addEventListener("click", e => {
  const p = $(".stockpick"), sug = $("#alSuggest");
  if (p && sug && !p.contains(e.target)) sug.classList.remove("show");
});

$("#alAdd") && ($("#alAdd").onclick = async () => {
  const v = $("#alStock").value, price = parseFloat($("#alPrice").value);
  if (!v){ $("#status4").textContent = t("alert.needStock", "請先輸入並選擇股票"); return; }
  if (!price || price <= 0){
    $("#status4").textContent = t("alert.needPrice", "請輸入正確價位"); return; }
  const [code, name] = v.split("|");
  $("#alAdd").disabled = true;
  $("#status4").textContent = t("alert.asking", "要求通知權限中…");
  const {sub, err} = await getSubscription();
  if (!sub){ $("#status4").textContent = "✗ " + err;
             $("#alAdd").disabled = false; return; }
  try {
    const r = await fetch("/api/alerts", { method: "POST",
      headers: {"Content-Type": "application/json", "X-App-Token": APP_TOKEN},
      /* ⚠️ 把當下的介面語言一起送出：推播是伺服器發的，
            那時不可能知道使用者用什麼語言看網站。 */
      body: JSON.stringify({cid: clientId(), code, name, price,
                            lang: LANG, subscription: sub})});
    const j = await r.json();
    if (j.ok){
      $("#status4").textContent = "✓ " + t("alert.added", "已新增提醒");
      $("#alPrice").value = ""; alClear(); loadAlerts();
    } else $("#status4").textContent = "✗ " + (j.error || "");
  } catch(e){ $("#status4").textContent = "✗ " + t("msg.netFail", "連線失敗"); }
  $("#alAdd").disabled = false;
});

if ($("#alList")) loadAlerts();

/* 使用者已打開 App，代表已看到通知：清掉 iPhone 主畫面 badge
   與 service worker 裡的未讀計數，下一則推播再從 1 開始。 */
async function clearUsPushBadge(){
  if (navigator.clearAppBadge){ try { await navigator.clearAppBadge(); } catch(_){} }
  if ("caches" in window){
    try { const c = await caches.open("us-push-state"); await c.delete("/__us_badge"); }
    catch(_){}
  }
}
clearUsPushBadge();

/* ---- 依網址開對應分頁 ---- */
if (START_PAGE && $("#" + START_PAGE)){
  document.querySelectorAll(".page").forEach(p => p.classList.remove("show"));
  $("#" + START_PAGE).classList.add("show");
  document.querySelectorAll(".navitem").forEach(i =>
    i.classList.toggle("active", i.dataset.page === START_PAGE));
  const activeNav = document.querySelector(`.navitem[data-page="${START_PAGE}"]`);
  if (activeNav && activeNav.closest("details")) activeNav.closest("details").open = true;
}
if (START_PAGE === "p7") buildTwTable();
applyLang();
</script>
</body>
</html>
"""


# ---------------------------------------------------------------- Flask

app = Flask(__name__)
# ---- App token ----
# ⚠️ **不能用「每次啟動產生一組隨機值」**。Render 掛了磁碟就沒有零停機部署，
#    每次部署／重啟都是新 process；使用者開著的分頁裡是舊 token，
#    按下篩選就一律 403 —— 而且看起來像「網站壞了」，很難聯想到 token。
#    改用台股版那套：HMAC 簽發、帶到期時間，重啟後舊 token 依然有效。
#
# 密鑰存在快取目錄（有掛持久化磁碟就跨部署保留）。
# 沒有磁碟時會重新產生 —— 那種情況下 token 也只是防外站盜用，重簽即可。
def _app_secret():
    p = os.path.join(CACHE_DIR, ".app_secret")
    try:
        with open(p, "r") as f:
            v = f.read().strip()
            if v:
                return v
    except Exception:
        pass
    v = uuid.uuid4().hex
    try:
        with open(p, "w") as f:
            f.write(v)
    except Exception:
        pass
    return v


APP_SECRET = os.environ.get("APP_SECRET") or _app_secret()
TOKEN_TTL = 24 * 3600


def make_app_token():
    """簽發 24 小時有效的 token，隨頁面一起下發。"""
    exp = str(int(time.time()) + TOKEN_TTL)
    sig = hmac.new(APP_SECRET.encode(), exp.encode(), hashlib.sha256).hexdigest()[:32]
    return "%s.%s" % (exp, sig)


def _valid_app_token(tok):
    try:
        exp, sig = (tok or "").split(".", 1)
        if int(exp) < time.time():
            return False
        good = hmac.new(APP_SECRET.encode(), exp.encode(),
                        hashlib.sha256).hexdigest()[:32]
        return hmac.compare_digest(sig, good)
    except Exception:
        return False

# 網址 → 分頁 id（與台股版同一套：功能頁各有自己的網址）
# 姊妹站（台股咖啡館）。已經上線，所以直接給預設值；
# 要改網址時設環境變數 TW_URL 即可，不必動程式。
TW_URL = os.environ.get("TW_URL", "https://stock-coffee.com").strip()

PAGE_ROUTES = {
    "screener": "p1", "pullback": "p3", "twr": "p7",
    "risk": "p8", "alerts": "p4", "articles": "pm",
    "pro": "p5", "pro/rs": "p9",
}

# ---------------------------------------------------------------- 文章

ARTICLES_DIR = os.path.join(BASE_DIR, "articles")
SITE_URL = "https://us.stock-coffee.com"


def _md_to_html(md):
    """本站文章需要的輕量 Markdown：標題、粗體、清單、段落與連結。"""
    import html as _h
    out, list_kind = [], None

    def close_list():
        nonlocal list_kind
        if list_kind:
            out.append("</%s>" % list_kind)
            list_kind = None

    def inline(s):
        s = _h.escape(s)
        s = re.sub(r"\*\*(.+?)\*\*", r"<strong>\1</strong>", s)
        s = re.sub(r"\[(.+?)\]\((https?://[^\s)]+)\)",
                   r'<a href="\2" target="_blank" rel="noopener">\1</a>', s)
        s = re.sub(r"\[(.+?)\]\((/[^\s)]*)\)", r'<a href="\2">\1</a>', s)
        return s

    for raw in md.splitlines():
        s = raw.rstrip()
        if s.startswith("### "):
            close_list(); out.append("<h3>%s</h3>" % inline(s[4:]))
        elif s.startswith("## "):
            close_list(); out.append("<h2>%s</h2>" % inline(s[3:]))
        elif s.startswith("- "):
            if list_kind != "ul":
                close_list(); out.append("<ul>"); list_kind = "ul"
            out.append("<li>%s</li>" % inline(s[2:]))
        elif re.match(r"^\d+\.\s+", s):
            if list_kind != "ol":
                close_list(); out.append("<ol>"); list_kind = "ol"
            out.append("<li>%s</li>" % inline(re.sub(r"^\d+\.\s+", "", s)))
        elif not s.strip():
            close_list()
        else:
            close_list(); out.append("<p>%s</p>" % inline(s))
    close_list()
    return "\n".join(out)


def _load_articles():
    items = []
    if not os.path.isdir(ARTICLES_DIR):
        return items
    for fn in sorted(os.listdir(ARTICLES_DIR)):
        if not fn.endswith(".md"):
            continue
        try:
            with open(os.path.join(ARTICLES_DIR, fn), "r", encoding="utf-8") as f:
                raw = f.read()
        except Exception:
            continue
        meta, body = {}, raw
        if raw.startswith("---"):
            parts = raw.split("---", 2)
            if len(parts) == 3:
                for line in parts[1].strip().splitlines():
                    if ":" in line:
                        k, v = line.split(":", 1)
                        meta[k.strip()] = v.strip()
                body = parts[2].strip()
        aid = fn[:-3]
        items.append({"id": aid, "slug": meta.get("slug") or aid,
                      "title": meta.get("title") or aid,
                      "tag": meta.get("tag") or "文章",
                      "date": meta.get("date") or "",
                      "summary": meta.get("summary") or "",
                      "html": _md_to_html(body)})
    return items


def _art_links_html():
    import html as _h
    rows = []
    for a in _load_articles():
        rows.append(
            '<li><a href="/article/%s"><span class="atag">%s</span>'
            '<div class="atitle">%s</div><p class="asum">%s</p>'
            '<span class="adate">%s</span></a></li>' %
            (quote(a["slug"]), _h.escape(a["tag"]), _h.escape(a["title"]),
             _h.escape(a["summary"]), _h.escape(a["date"])))
    return "".join(rows)


def _find_article(aid):
    items = _load_articles()
    for a in items:
        if aid in (a["id"], a["slug"]):
            return a, [x for x in items if x["id"] != a["id"]][:5]
    return None, items[:5]


ARTICLE_PAGE = r"""<!doctype html><html lang="zh-Hant-TW"><head>
<meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>__TITLE__｜美股咖啡館 US Stock Coffee</title>
<meta name="description" content="__DESC__"><link rel="canonical" href="__URL__">
<meta name="robots" content="index,follow,max-image-preview:large">
<meta property="og:type" content="article"><meta property="og:site_name" content="美股咖啡館 US Stock Coffee">
<meta property="og:title" content="__TITLE__"><meta property="og:description" content="__DESC__">
<meta property="og:url" content="__URL__"><meta property="og:image" content="__SITE__/icon.png">
<script type="application/ld+json">__JSONLD__</script>
<style>
:root{--milk:#f1ead9;--foam:#fbf6ec;--grounds:#e4d7c1;--espresso:#33241a;--mocha:#6b5540;--caramel:#c68a3e;--caramel2:#a56c24}
*{box-sizing:border-box}body{margin:0;background:var(--milk);color:var(--espresso);font-family:-apple-system,BlinkMacSystemFont,"PingFang TC","Noto Sans TC",sans-serif;line-height:1.95}
.top{background:var(--espresso);padding:12px 18px;display:flex;justify-content:space-between}.top a{color:var(--foam);text-decoration:none;font-weight:800}.top .go{color:#f0c88a}
main{max-width:760px;margin:auto;padding:24px 18px 60px}.crumb{font-size:13px;color:var(--mocha)}.crumb a{color:var(--caramel2);text-decoration:none}.tag{display:inline-block;margin-top:18px;background:var(--caramel);color:white;border-radius:999px;padding:2px 11px;font-size:12px;font-weight:700}
h1{font-size:28px;line-height:1.45;margin:12px 0 5px}.meta{font-size:12px;color:var(--mocha)}.summary{margin:18px 0 28px;background:var(--foam);border:1px solid var(--grounds);border-left:4px solid var(--caramel);border-radius:0 12px 12px 0;padding:12px 16px;color:var(--mocha)}
article{font-size:16.5px}article h2{font-size:20px;margin:34px 0 10px;border-left:4px solid var(--caramel);padding-left:10px}article h3{font-size:17px;color:var(--caramel2);margin:26px 0 8px}article p{margin:12px 0}article li{margin:7px 0}article strong{color:var(--espresso)}
.cta{display:block;margin-top:36px;padding:13px;text-align:center;background:var(--caramel);color:white;border-radius:999px;text-decoration:none;font-weight:800}.more{margin-top:35px;border-top:1px solid var(--grounds);padding-top:18px}.more a{color:var(--caramel2);text-decoration:none}
</style></head><body><div class="top"><a href="/">☕ 美股咖啡館</a><a class="go" href="/">開啟選股工具</a></div>
<main><nav class="crumb"><a href="/">首頁</a> › <a href="/articles">文章區</a> › __TITLE__</nav>
<span class="tag">__TAG__</span><h1>__TITLE__</h1><div class="meta">__DATE__</div>
<div class="summary">__DESC__</div><article>__BODY__</article>
<a class="cta" href="/">免費使用美股選股工具，免註冊 →</a><div class="more"><b>其他文章</b><ul>__MORE__</ul></div></main></body></html>"""


@app.route("/article/<path:aid>")
def article_page(aid):
    import html as _h
    a, others = _find_article(aid)
    if not a:
        return _render("pm"), 404
    url = SITE_URL + "/article/" + quote(a["slug"])
    ld = {"@context": "https://schema.org", "@type": "Article",
          "headline": a["title"], "description": a["summary"], "url": url,
          "datePublished": a["date"], "dateModified": a["date"],
          "inLanguage": "zh-Hant-TW", "isAccessibleForFree": True,
          "author": {"@type": "Organization", "name": "美股咖啡館 US Stock Coffee"}}
    more = "".join('<li><a href="/article/%s">%s</a></li>' %
                   (quote(x["slug"]), _h.escape(x["title"])) for x in others)
    out = ARTICLE_PAGE
    vals = {"__TITLE__": _h.escape(a["title"]), "__DESC__": _h.escape(a["summary"]),
            "__TAG__": _h.escape(a["tag"]), "__DATE__": _h.escape(a["date"]),
            "__BODY__": a["html"], "__MORE__": more, "__URL__": url,
            "__SITE__": SITE_URL, "__JSONLD__": json.dumps(ld, ensure_ascii=False)}
    for k, v in vals.items():
        out = out.replace(k, v)
    return out


@app.after_request
def _compress(resp):
    """文字類回應做 gzip（HTML 約 70KB → 20KB），並禁止快取動態內容。"""
    try:
        ctype = (resp.headers.get("Content-Type") or "").split(";")[0]
        if ctype not in ("text/html", "application/json", "text/plain"):
            return resp

        # ⚠️⚠️ **HTML 與 JSON 一律不快取。**
        #   HTML 是伺服器端渲染的，裡面烤著 `APP_TOKEN`，**效期只有 24 小時**。
        #   分頁被快取過夜 → token 過期 → 所有篩選 403，症狀是「網站突然壞了」。
        #   ⚠️ `retryOnStaleToken()` 的「重整一次」在這種情況下**救不回來** ——
        #      重整拿到的還是同一份快取 HTML、同一個過期 token。
        #   ⚠️ 沒設 Cache-Control ≠ 不會被快取：瀏覽器會用「啟發式快取」自行決定，
        #      Cloudflare 與 App 內的 WebView 也可能存。一定要明講。
        #   （台股版 2026-08-04 實際發生過，症狀是首頁名言天天一樣。）
        if ctype in ("text/html", "application/json"):
            resp.headers["Cache-Control"] = "no-store, no-cache, must-revalidate"
            resp.headers["Pragma"] = "no-cache"

        if "gzip" not in (request.headers.get("Accept-Encoding") or "").lower():
            return resp
        if resp.direct_passthrough or resp.headers.get("Content-Encoding"):
            return resp
        data = resp.get_data()
        if len(data) < 1024:
            return resp
        import gzip as _gzip
        packed = _gzip.compress(data, 6)
        resp.set_data(packed)
        resp.headers["Content-Encoding"] = "gzip"
        resp.headers["Content-Length"] = str(len(packed))
        resp.headers.add("Vary", "Accept-Encoding")
    except Exception:
        pass
    return resp



def _phase_banner_html():
    """首頁的「今日市場」。**只讀快取**，讀不到就回空字串。

    ⚠️ 寧可少一塊，也不要顯示「無法判斷」—— 那看起來像壞掉。
    """
    import html as _h
    phase, do, date, breadth = market_phase_cached()
    ui = PHASE_UI.get(phase)
    if not ui:
        return ""
    b = ("%.0f%%" % breadth) if breadth is not None else "—"
    zh_rule = {
        "tailwind": "指數站上 50MA，且 50MA 在 100MA 之上",
        "pullback": "指數跌回 50MA 下方，但仍守在 100MA 之上",
        "transition": "指數仍在 100MA 之上，但 50MA／100MA 方向互相衝突",
        "riskoff": "指數跌破 100MA",
        "recovery_early": "近 90 日市場曾洗盤，指數已收復 50MA、尚未收復 100MA",
        "recovery_confirmed": "近 90 日市場曾洗盤，指數已收復 100MA",
    }.get(phase, "")
    en_rule = {
        "tailwind": "the index is above 50MA and 50MA is above 100MA",
        "pullback": "the index is below 50MA but still above 100MA",
        "transition": "the index is above 100MA while the 50MA/100MA signals conflict",
        "riskoff": "the index is below 100MA",
        "recovery_early": "the market washed out within 90 days and the index reclaimed 50MA",
        "recovery_confirmed": "the market washed out within 90 days and the index reclaimed 100MA",
    }.get(phase, "")
    return (
        '<details class="mk-box">'
        '<summary>'
        '<span class="mk-dot">' + ui["dot"] + '</span>'
        '<span class="mk-main">'
        '<b class="q-zh">' + _h.escape(ui["zh"]) + '</b>'
        '<b class="q-en" style="display:none">' + _h.escape(ui["en"]) + '</b>'
        '<span class="mk-do q-zh">' + _h.escape(do) + '</span>'
        '<span class="mk-do q-en" style="display:none">'
        + _h.escape(ui["en_do"]) + '</span>'
        '</span>'
        '<span class="mk-num">' + _h.escape(date) + '</span>'
        '</summary>'
        '<div class="mk-body">'
        '<span class="q-zh">依連續三日確認，目前維持<b>' + _h.escape(ui["zh"])
        + '</b>；這個狀態的判定條件是：' + _h.escape(zh_rule) + '。目前另有 <b>' + b
        + '</b> 的成分股站在自己的 ' + str(BREADTH_MA) + ' 日均線之上。<br><br>'
        '<b>50MA</b> 看順風與正常回檔，<b>100MA</b> 看是否進入逆風，'
        '<b>150MA 市場寬度</b>主要判斷市場是否曾被充分洗盤。'
        '這不預測行情，只描述環境。</span>'
        '<span class="q-en" style="display:none">After three-day confirmation, the market '
        'remains <b>' + _h.escape(ui["en"]) + '</b>; this state is defined when '
        + _h.escape(en_rule) + '. <b>' + b + '</b> of constituents are above their own '
        + str(BREADTH_MA) + '-day average.<br><br>'
        '<b>50MA</b> identifies tailwinds and normal pullbacks, <b>100MA</b> marks '
        'headwinds, and <b>150MA breadth</b> mainly identifies washouts. '
        'This describes the environment — it does not predict it.</span>'
        '</div></details>')


def _render(start_page="home"):
    html = PAGE.replace("__APP_TOKEN__", make_app_token())
    html = html.replace("__START_PAGE__", start_page, 1)
    html = html.replace("__TW_URL__", TW_URL)
    html = html.replace("__PHASE_BAR__", _phase_banner_html())
    html = html.replace("__HOME_SCREEN__", _home_screen_html())
    # ⚠️ 只放**公開**金鑰。VAPID_PRIVATE 絕對不能出現在頁面上。
    html = html.replace("__VAPID_PUBLIC__", VAPID_PUBLIC)
    html = html.replace("__ART_LINKS__", _art_links_html())
    return render_template_string(html)


@app.route("/api/breadth")
def api_breadth():
    """市場寬度的歷史序列 ＋ 分位數，給首頁「大盤詳細數據」的折線圖用。

    ⚠️ **只讀 `breadth.json`，絕不連網、也不重算。**
       重算要讀幾百個快取檔、每檔算 BREADTH_MA —— 那是預抓流程的工作。
       這支是使用者展開才呼叫的，必須便宜（台股版 5.4 的同一條原則）。

    ⚠️⚠️ **分位數只涵蓋 `breadth.json` 這段（約 5 年），不是 10 年。**
       門檻（85／30）是用**10 年回測**訂的，兩者的母體不一樣 ——
       所以回傳 `span_days` / `span_years`，前端**必須把區間講出來**。
       寫成「歷史中位數」會讓人以為那是 10 年的數字，
       然後拿它跟 85% 的門檻比，得到完全錯的結論。
       （這跟台股版把「現價」標成收盤價是同一類錯誤：數字對，標籤說謊。）

    ⚠️ 這支跟 `/api/screen` 一樣要驗 App token —— 這個專案沒有 `@guard` 裝飾器，
       慣例是**在函式開頭自己驗**。不要為了這一支引進新寫法。
    """
    if not _valid_app_token(request.headers.get("X-App-Token")):
        return jsonify(error="連線憑證已過期，請重新整理頁面"), 403
    br = _load_cache("breadth.json", 24 * 365) or {}
    if not br:
        return jsonify(ok=False, error="no breadth cache")
    days = sorted(br)
    vals = sorted(br[d] for d in days)

    def pct_of(v):
        """v 在歷史分布中的百分位。"""
        n = sum(1 for x in vals if x <= v)
        return round(n / len(vals) * 100)

    cur = br[days[-1]]
    look = days[-WASH_LOOKBACK:]

    # 納斯達克綜合指數的收盤價與 50MA／100MA。
    # ⚠️ 一樣**只讀快取**。算兩條均線只是對一串數字做滑動和，很便宜，
    #    但指數本身絕不在這裡連網補抓 —— 那是預抓流程的事。
    # ⚠️ 指數與寬度**日期未必對齊**（FRED 常慢一個交易日），
    #    所以回傳指數自己的日期，前端要照實顯示，不要沿用寬度的日期。
    idx_out = None
    try:
        idx = _load_cache("nasdaq_index.json", 24 * 365) or {}
        ids = sorted(idx)
        if len(ids) >= PHASE_SLOW_MA:
            d = ids[-1]
            ma50 = sum(idx[x] for x in ids[-PHASE_FAST_MA:]) / PHASE_FAST_MA
            ma100 = sum(idx[x] for x in ids[-PHASE_SLOW_MA:]) / PHASE_SLOW_MA
            idx_out = {"date": d, "close": round(idx[d], 2),
                       "ma50": round(ma50, 2), "ma100": round(ma100, 2),
                       "gap50": round((idx[d] - ma50) / ma50 * 100, 2),
                       "gap100": round((idx[d] - ma100) / ma100 * 100, 2)}
    except Exception:
        idx_out = None            # ⚠️ 指數讀不到不能影響寬度那半邊

    return jsonify(
        idx=idx_out,
        ok=True,
        series=[[d, br[d]] for d in days],
        cur=cur, cur_pct=pct_of(cur), date=days[-1],
        wash_min=round(min(br[d] for d in look), 1),
        wash_look=WASH_LOOKBACK,
        top=BREADTH_TOP, wash=BREADTH_WASH,
        breadth_ma=BREADTH_MA,
        phase_fast_ma=PHASE_FAST_MA, phase_slow_ma=PHASE_SLOW_MA,
        span_days=len(days), span_years=round(len(days) / 252.0, 1),
        p={str(p): round(vals[max(0, min(len(vals) - 1, int(len(vals) * p / 100)))], 1)
           for p in (10, 25, 50, 75, 90)},
    )


# ---------------------------------------------------------------- 推播通知（到價提醒）
#
# 從台股版移植（2026-08-05）。結構刻意保持一致，方便兩邊互相對照。
#
# ⚠️⚠️ **金鑰與台股版各自獨立，不要共用。**
#    VAPID 金鑰識別的是「應用伺服器」，技術上兩站可以共用同一組 ——
#    但**換金鑰會讓所有既有訂閱作廢**，共用等於把這個風險加倍：
#    哪天要輪替其中一站，另一站的訂閱會一起死。
#    所以美股用自己 `vapid --gen` 產的一組，填在**美股那個 Render 服務**的環境變數。
#    產生步驟見台股版的 `推播金鑰_重生成指令.txt`。
#
# ⚠️ `VAPID_PRIVATE` 只放環境變數，**絕不進 git**。
#
# 沒設金鑰時整個功能會安靜降級：前端顯示「伺服器尚未設定推播金鑰」，
# 不會拋例外、也不會擋住網站其他部分。

VAPID_PUBLIC = os.environ.get("VAPID_PUBLIC", "")
VAPID_PRIVATE = os.environ.get("VAPID_PRIVATE", "")
VAPID_EMAIL = os.environ.get("VAPID_EMAIL", "seer51000@gmail.com")

ALERTS_FILE = "us_alerts.json"
ALERTS_DB_KEY = "us_alerts_v1"
_ALERTS_LOCK = threading.RLock()
MAX_ALERTS_PER_USER = 3
ALERT_BAND = 0.02          # 收盤價落在目標價 ±2% 內就通知（與台股版一致）
ALERT_DAYS = 30            # 提醒保留天數

# 設了 DATABASE_URL 就用 PostgreSQL 永久保存，否則退回本機快取檔。
# ⚠️ 線上建議一定要設：快取目錄雖有持久化磁碟，但訂閱資料放 DB 比較穩，
#    而且「可安全刪除 cache/」這個慣例會不小心把訂閱一起刪掉。
DATABASE_URL = os.environ.get("DATABASE_URL", "")


def _db_conn():
    import psycopg2
    return psycopg2.connect(DATABASE_URL)


def _db_init():
    with _db_conn() as c:
        with c.cursor() as cur:
            cur.execute("CREATE TABLE IF NOT EXISTS kv (k text PRIMARY KEY, v text)")
        c.commit()


def _load_alerts():
    if DATABASE_URL:
        try:
            _db_init()
            with _db_conn() as c:
                with c.cursor() as cur:
                    cur.execute("SELECT v FROM kv WHERE k=%s", (ALERTS_DB_KEY,))
                    row = cur.fetchone()
            return json.loads(row[0]) if row and row[0] else []
        except Exception:
            pass          # DB 連線失敗就退回本機檔案，不要讓功能整個死掉
    return _load_cache(ALERTS_FILE, None) or []


def _save_alerts(alerts):
    if DATABASE_URL:
        try:
            _db_init()
            with _db_conn() as c:
                with c.cursor() as cur:
                    cur.execute(
                        "INSERT INTO kv (k, v) VALUES (%s, %s) "
                        "ON CONFLICT (k) DO UPDATE SET v = EXCLUDED.v",
                        (ALERTS_DB_KEY, json.dumps(alerts, ensure_ascii=False)))
                c.commit()
            return
        except Exception:
            pass
    _save_cache(ALERTS_FILE, alerts)


def _send_push(subscription, title, body):
    """送一則推播，回傳 ``(ok, reason)``。reason=gone 表示訂閱已失效。"""
    if not subscription or not VAPID_PUBLIC or not VAPID_PRIVATE:
        return False, "not_configured"
    try:
        from pywebpush import webpush, WebPushException
        webpush(
            subscription_info=subscription,
            data=json.dumps({"title": title, "body": body}),
            vapid_private_key=VAPID_PRIVATE,
            vapid_claims={"sub": "mailto:%s" % VAPID_EMAIL},
        )
        return True, ""
    except WebPushException as e:
        status = getattr(getattr(e, "response", None), "status_code", None)
        return False, "gone" if status in (404, 410) else "push_failed"
    except Exception:
        return False, "push_failed"


@app.route("/api/stocklist")
def api_stocklist():
    """給到價提醒的下拉選單用：市值前 300 大的代號與名稱。

    ⚠️ **只讀快取，不連網。** `get_universe()` 會打 Nasdaq，
       這支是使用者一進頁面就會呼叫的，不能讓它觸發外部請求。
       讀不到就回空陣列，前端會顯示「清單載入失敗」。
    """
    if not _valid_app_token(request.headers.get("X-App-Token")):
        return jsonify(error="連線憑證已過期，請重新整理頁面"), 403
    uni = _load_cache("universe.json", None) or []
    return jsonify([{"code": u.get("symbol", ""),
                     "name": u.get("name", ""),
                     "name_zh": zh_company(u.get("symbol", ""), u.get("name", ""))}
                    for u in uni[:300] if u.get("symbol")])


@app.route("/api/alerts", methods=["GET", "POST"])
def api_alerts():
    if not _valid_app_token(request.headers.get("X-App-Token")):
        return jsonify(error="連線憑證已過期，請重新整理頁面"), 403
    cid = str(request.args.get("cid", ""))[:120]
    if request.method == "GET":
        alerts = _load_alerts()
        mine = [{"id": a["id"], "code": a["code"], "name": a["name"],
                 "price": a["price"], "expires": a["expires"]}
                for a in alerts if a.get("cid") == cid]
        return jsonify(mine)

    d = request.get_json(silent=True) or {}
    cid = str(d.get("cid", ""))[:120]
    # ⚠️ 用 `is None` 判斷 price，不要用 falsy —— 0 也是 falsy，
    #    會被歸類成「資料不完整」，使用者看到的錯誤訊息就對不上實際問題。
    if not cid or not d.get("code") or d.get("price") is None:
        return jsonify(ok=False, error="資料不完整"), 400
    code = str(d.get("code", "")).strip().upper()
    if not re.fullmatch(r"[A-Z][A-Z0-9.\-]{0,9}", code):
        return jsonify(ok=False, error="股票代號格式不正確"), 400
    universe = _load_cache("universe.json", None) or []
    allowed = {str(u.get("symbol", "")).upper() for u in universe[:300]}
    if code not in allowed:
        return jsonify(ok=False, error="僅能設定市值前 300 大股票"), 400
    sub = d.get("subscription")
    if not isinstance(sub, dict) or not sub.get("endpoint") or not isinstance(sub.get("keys"), dict):
        return jsonify(ok=False, error="裝置推播訂閱無效，請重新允許通知"), 400
    try:
        price = round(float(d["price"]), 2)
    except (TypeError, ValueError):
        return jsonify(ok=False, error="價位格式不正確"), 400
    if not math.isfinite(price) or price <= 0:
        return jsonify(ok=False, error="價位要大於 0"), 400

    now = _utcnow()
    with _ALERTS_LOCK:
        alerts = _load_alerts()
        if sum(1 for a in alerts if a.get("cid") == cid) >= MAX_ALERTS_PER_USER:
            return jsonify(ok=False,
                           error="每人最多設定 %d 檔提醒" % MAX_ALERTS_PER_USER), 400
        alerts.append({
        # ⚠️ 用 uuid，不要用毫秒時戳。台股版是 `str(int(time.time()*1000))`，
        #    **同一毫秒內新增兩筆就會撞號** —— 實測會發生（連續兩次 POST）。
        #    撞號的後果是刪一筆會把同號的另一筆一起刪掉。
        "id": uuid.uuid4().hex[:12],
        "cid": cid,
        "code": code,
        "name": str(d.get("name") or code)[:120],
        "price": price,
        # ⚠️ 存下設定當下的介面語言。美股版是雙語站，而推播送出時
        #    伺服器不可能知道使用者的語言 —— 只能在這裡記下來。
        "lang": "en" if d.get("lang") == "en" else "zh",
        "created": now.strftime("%Y-%m-%d"),
        "expires": (now + timedelta(days=ALERT_DAYS)).strftime("%Y-%m-%d"),
        "subscription": sub,
        })
        _save_alerts(alerts)
    return jsonify(ok=True)


@app.route("/api/alerts/<alert_id>", methods=["DELETE"])
def api_alerts_delete(alert_id):
    if not _valid_app_token(request.headers.get("X-App-Token")):
        return jsonify(error="連線憑證已過期，請重新整理頁面"), 403
    cid = request.args.get("cid", "")
    with _ALERTS_LOCK:
        alerts = [a for a in _load_alerts()
                  if not (a["id"] == alert_id and a.get("cid") == cid)]
        _save_alerts(alerts)
    return jsonify(ok=True)


@app.route("/api/test-push", methods=["POST"])
def api_test_push():
    """立刻對本裝置送一則測試推播。**錯誤訊息要具體**，不要只說「失敗」。"""
    if not _valid_app_token(request.headers.get("X-App-Token")):
        return jsonify(error="連線憑證已過期，請重新整理頁面"), 403
    d = request.get_json(silent=True) or {}
    sub = d.get("subscription")
    if not sub:
        return jsonify(sent=False, error="沒有收到裝置的推播訂閱")
    if not VAPID_PUBLIC or not VAPID_PRIVATE:
        return jsonify(sent=False,
                       error="伺服器未設定 VAPID_PUBLIC / VAPID_PRIVATE"
                             "（請到 Render 設定並重新部署）")
    if d.get("lang") == "en":
        title, body = "US Stock Coffee", "Push test succeeded"
    else:
        title, body = "美股咖啡館", "推播測試成功"
    ok, _reason = _send_push(sub, title, body)
    return jsonify(sent=ok,
                   error="" if ok else "pywebpush 送出失敗（金鑰不正確或訂閱已失效）")


def _run_alert_checks():
    """只讀日 K 快取檢查全部提醒；供內部 18:00 ET 排程與手動 API 共用。"""
    with _ALERTS_LOCK:
        alerts = _load_alerts()
        want = _expected_last_session()
        today = _utcnow().strftime("%Y-%m-%d")
        result = {"ok": True, "expected_session": want, "checked": 0, "sent": 0,
                  "skipped_stale": 0, "expired": 0, "duplicate": 0,
                  "removed_gone": 0}
        kept = []
        for a in alerts:
            if a.get("expires", "9999") < today:
                result["expired"] += 1
                continue
            rows = _load_cache("hist_%s.json" % str(a.get("code", "")).upper(), None) or []
            if not rows or str(rows[-1][0]) != want:
                result["skipped_stale"] += 1
                kept.append(a)
                continue
            result["checked"] += 1
            last_d, last_c = str(rows[-1][0]), float(rows[-1][1])
            target = float(a.get("price") or 0)
            if not target or abs(last_c - target) / target > ALERT_BAND:
                kept.append(a)
                continue
            if a.get("last_sent_session") == want:
                result["duplicate"] += 1
                kept.append(a)
                continue
            if a.get("lang") == "en":
                title = "US Stock Coffee · Price alert"
                body = ("%s closed at %s on %s — within %.0f%% of your target %s"
                        % (a["code"], last_c, last_d, ALERT_BAND * 100, target))
            else:
                title = "美股咖啡館 · 到價提醒"
                body = ("%s %s 收盤 %s，已進入目標價 %s 的 ±%.0f%% 範圍"
                        % (last_d, a["code"], last_c, target, ALERT_BAND * 100))
            ok, reason = _send_push(a.get("subscription"), title, body)
            if ok:
                a["last_sent_session"] = want
                result["sent"] += 1
                kept.append(a)
            elif reason == "gone":
                result["removed_gone"] += 1
            else:
                kept.append(a)
        _save_alerts(kept)
        return result


@app.route("/api/run-alerts", methods=["GET", "POST"])
def api_run_alerts():
    """由**外部排程**於美股收盤後呼叫，以當日收盤價檢查提醒並推播。

    可設 `CRON_TOKEN` 環境變數，呼叫時帶 `?token=` 驗證。

    ⚠️ **只讀 `hist_` 快取，不主動抓價。** 這支應該排在每日更新之後跑；
       自己再抓一次不但慢，還可能拿到跟網站不一致的價格。
       快取還沒更新到最新交易日時**寧可不送**，並在回應裡講清楚 ——
       送出一則基於舊收盤價的提醒，比沒送更糟。
    """
    token = os.environ.get("CRON_TOKEN", "")
    if not token:
        return jsonify(ok=False, error="CRON_TOKEN is not configured"), 503
    if request.args.get("token") != token:
        return jsonify(ok=False, error="unauthorized"), 401
    return jsonify(_run_alert_checks())


@app.route("/sw.js")
def service_worker():
    """Service worker：瀏覽器靠它在背景收推播。

    ⚠️ 必須從**網站根目錄**提供（`/sw.js`），放子路徑會讓作用範圍不足。
    ⚠️ 回 `application/javascript`，而且**不要快取** ——
       改了推播行為卻被舊的 sw 擋住，是很難查的問題。
    """
    js = """
async function pushHandler(e){
  let d = {};
  try { d = e.data.json(); }
  catch(_){ d = {title:'US Stock Coffee', body: e.data ? e.data.text() : ''}; }
  await self.registration.showNotification(d.title || 'US Stock Coffee',
    {body: d.body || '', icon: '/icon.png', badge: '/icon.png',
     tag: 'us-alert-' + Date.now()});
  // iOS/iPadOS 主畫面 Web App badge：每收到一則就累加未讀數。
  // 使用者打開 App 時，前端 clearUsPushBadge() 會清為 0。
  try {
    const cache = await caches.open('us-push-state');
    const prev = await cache.match('/__us_badge');
    let count = prev ? parseInt(await prev.text(), 10) || 0 : 0;
    count += 1;
    await cache.put('/__us_badge', new Response(String(count)));
    if (self.navigator && self.navigator.setAppBadge){
      try { await self.navigator.setAppBadge(count); } catch(_){}
    }
  } catch(_){}
}
self.addEventListener('push', e => e.waitUntil(pushHandler(e)));
self.addEventListener('install', () => self.skipWaiting());
self.addEventListener('activate', e => e.waitUntil(self.clients.claim()));
self.addEventListener('notificationclick', e => {
  e.notification.close();
  e.waitUntil(clients.openWindow('/alerts'));
});
"""
    resp = app.response_class(js, mimetype="application/javascript")
    resp.headers["Cache-Control"] = "no-store"
    return resp


@app.route("/")
def index():
    return _render("home")


for _slug, _pid in PAGE_ROUTES.items():
    app.add_url_rule("/" + _slug, "page_" + _slug,
                     (lambda p=_pid: (lambda: _render(p)))())


@app.route("/api/diag")
def api_diag():
    """伺服器端診斷：一次查完「為什麼篩選不出來」的所有可能原因。

    回傳純文字（瀏覽器直接開得起來）。這比在本機猜有用得多 ——
    最關鍵的是**確認 Render 的機房 IP 能不能連上 Nasdaq**：
    Stooq 與 Yahoo 都擋機房 IP，Nasdaq 也可能一樣，
    而那在本機（家用 IP）測是測不出來的。
    """
    import io as _io
    import traceback
    out = _io.StringIO()

    def w(line=""):
        out.write(str(line) + "\n")

    w("=" * 60)
    w("  美股咖啡館 — 伺服器端診斷")
    w("  " + (_utcnow().strftime("%Y-%m-%d %H:%M UTC")))
    w("=" * 60)

    w("\n【環境】")
    w("  CACHE_DIR      : %s" % CACHE_DIR)
    w("  磁碟已掛載      : %s" % ("是" if "/opt/render" in CACHE_DIR else
                                  "否 ← 快取每次部署會消失"))
    w("  TW_URL         : %s" % TW_URL)
    try:
        files = os.listdir(CACHE_DIR)
        w("  快取 hist_     : %d 檔" % len([f for f in files if f.startswith("hist_")]))
        w("  快取 fund_     : %d 檔" % len([f for f in files if f.startswith("fund_")]))
        w("  快取大小        : %.1f MB" % (sum(
            os.path.getsize(os.path.join(CACHE_DIR, f)) for f in files) / 1e6))
    except Exception as e:
        w("  快取讀取失敗    : %s" % e)

    w("\n【預抓狀態】")
    for k, v in PREFETCH_STATE.items():
        w("  %-14s : %s" % (k, v))
    w("  最近來源        : %s" % LAST_SOURCE)

    _pft = PREFETCH_STATE.get("thread_obj")
    w("  預抓執行緒      : %s" % ("執行中" if (_pft is not None and _pft.is_alive())
                                 else "已結束／不存在" if _pft is not None else "沒有物件"))

    w("\n【市場階段】")
    try:
        _ph, _do, _d, _b = market_phase_cached()
        _ui = PHASE_UI.get(_ph)
        w("  目前階段        : %s" % ("%s %s（%s）" % (_ui["dot"], _ui["zh"], _do)
                                      if _ui else "unknown ← 缺 breadth 或指數快取"))
        w("  市場寬度        : %s（%% 成分股站上自身 %dMA）"
          % (("%.1f%%" % _b if _b is not None else "—"), BREADTH_MA))
        w("  資料日期        : %s%s"
          % (_d or "—", "" if (_d or "") >= _expected_last_session()
             else "  ← ⚠️ 落後（背景重算中或等下次重試）"))
        _br = _load_cache("breadth.json", 24 * 365) or {}
        _ix = _load_cache("nasdaq_index.json", 24 * 365) or {}
        w("  breadth.json    : %d 天%s" % (len(_br), "" if _br else "  ← 還沒算過"))
        _hs = _load_cache("home_screen.json", 24 * 365) or {}
        _hst = max(_br) if _br else ""
        _hsd = str(_hs.get("as_of") or "")
        w("  本日推薦        : %s%s" %
          (_hsd or "—", "" if not _hst or _hsd >= _hst else "  ← 落後，背景重算中"))
        w("  推薦重算        : %s" % _HOME_REBUILD["note"])
        w("  納斯達克指數     : %d 天%s" % (len(_ix), "" if _ix else "  ← 抓不到"))
        _ixd = max(_ix) if _ix else ""
        w("  指數來源        : %s" % (_INDEX_SRC["name"] or "全部失敗"))
        w("  指數最新日期     : %s%s"
          % (_ixd or "—",
             "" if _ixd >= _expected_last_session()
             else "  ← 落後（FRED 更新有延遲）"))
        w("  COMP 補資料      : %s" % _IDX_TOPUP["note"])
        for _e in _INDEX_SRC["errs"]:
            w("     ✗ %s" % _e)
        w("  判定過程        : %s" % _PHASE_WHY["why"])
        for _st in _PHASE_WHY["steps"]:
            w("     · %s" % _st)
        w("  規則            : 50MA 看順風　100MA 看逆風　寬度≤%.0f%%（近 %d 日）看洗盤　黏著 %d 天"
          % (BREADTH_WASH, WASH_LOOKBACK, PHASE_STICKY))
    except Exception as e:
        w("  ❌ %s: %s" % (type(e).__name__, str(e)[:80]))

    w("\n【每日自動更新】")
    # ⚠️ 不要只看 enabled —— 那個旗標設過一次就不會變，執行緒死了它還是「是」。
    #    要看心跳：正常情況每 5 分鐘內一定會更新一次。
    _hb_age = time.time() - (SCHED_STATE.get("heartbeat_ts") or 0)
    _raw = SCHED_STATE.get("env_raw")
    if not SCHED_STATE["enabled"]:
        if not SCHED_STATE.get("thread_started"):
            _health = ("否 ← 環境變數 ENABLE_DAILY_UPDATE=%r，執行緒沒有啟動" % _raw
                       if _raw is not None and _raw != "1"
                       else "否 ← 執行緒建立失敗（看下面骨幹錯誤）")
        else:
            _health = "否 ← 執行緒有啟動但還沒設旗標（剛重啟？或啟動時就死了）"
    elif _hb_age > 600:
        _health = "⚠️ 有啟動但心跳停了 %.0f 分鐘 ← 執行緒可能卡住" % (_hb_age / 60)
    else:
        _health = "是（心跳 %.0f 秒前）" % _hb_age
    w("  排程執行中      : %s" % _health)
    w("  環境變數原始值   : %s" % ("（未設定，預設開啟）" if _raw is None else repr(_raw)))
    w("  執行緒已建立     : %s" % ("是" if SCHED_STATE.get("thread_started") else "否"))
    _th = SCHED_STATE.get("thread_obj")
    w("  執行緒還活著     : %s" % ("是" if (_th is not None and _th.is_alive()) else
                                  "否 ← 已經死了" if _th is not None else "沒有物件"))
    w("  進入函式        : %s" % SCHED_STATE.get("entered_at", "❌ 從來沒進去"))
    w("  讀完紀錄檔      : %s" % SCHED_STATE.get("loaded_at", "❌ 沒讀完"))
    _now_pid = os.getpid()
    w("  import 時 PID   : %d" % IMPORT_PID)
    w("  現在的 PID      : %d（啟動至今 %.0f 秒）"
      % (_now_pid, time.time() - PROCESS_STARTED_TS))
    if _now_pid != IMPORT_PID:
        w("  ⚠️ PID 不一致 → import 之後發生過 fork。")
        w("     這本身沒關係：背景執行緒是在第一個請求時、於本行程啟動的。")
    else:
        w("  ✅ PID 一致（沒有 fork）")
    w("  背景執行緒行程   : %s" % (_BG_PID if _BG_PID else "❌ 還沒啟動"))
    if SCHED_STATE.get("loop_error"):
        w("  ⚠️ 骨幹錯誤     : %s" % SCHED_STATE["loop_error"])
    w("  觸發時間        : 每個美東交易日 %02d:00 ET（收盤後 %d 小時）"
      % (UPDATE_HOUR_ET, UPDATE_HOUR_ET - 16))
    w("  下次更新        : %s" % SCHED_STATE["next_run"])
    w("  上次更新        : %s" % SCHED_STATE["last_run"])
    w("  上次結果        : %s" % SCHED_STATE["last_result"])
    # ⚠️ 「成功」只代表沒拋例外，不代表真的抓到新資料 ——
    #    全部命中 TTL 快取也會回報成功。所以直接印資料本身有多新。
    try:
        _lat = {}
        for _sy in ("AAPL", "MSFT", "NVDA"):
            _h = _load_cache("hist_%s.json" % _sy, None) or []
            _lat[_sy] = _h[-1][0] if _h else "—"
        _fp = os.path.join(CACHE_DIR, "hist_AAPL.json")
        _age = (time.time() - os.path.getmtime(_fp)) / 3600 if os.path.exists(_fp) else -1
        _exp = _expected_last_session()
        w("  應該要有的交易日 : %s（美東 %02d:00 後才算）" % (_exp, UPDATE_HOUR_ET))
        # ⚠️ 只數「現在的股票池」。cache 裡會有以前抓過、現在已經跌出前 300 大的
        #    殘留檔案，它們永遠不會被更新 —— 一起算進來會虛報成「265 檔落後」。
        _uni = {u["symbol"].upper() for u in (get_universe(300) or [])}
        _behind, _orphan = [], 0
        for _f in os.listdir(CACHE_DIR):
            if not _f.startswith("hist_"):
                continue
            _sym = _f[5:-5]
            if _sym not in _uni:
                _orphan += 1
                continue
            _r = _load_cache(_f, None) or []
            if not _r or str(_r[-1][0]) < _exp:
                _behind.append(_sym)
        w("  股票池落後      : %d / %d 檔%s"
          % (len(_behind), len(_uni),
             ("　例如 " + "、".join(sorted(_behind)[:8])) if _behind else "  ✅ 全部到齊"))
        w("  池外殘留檔案     : %d 檔（已跌出前 300 大，不會更新也不影響篩選）" % _orphan)
        w("  等待重試        : %d 檔抓失敗（%.0f 分鐘後重試）"
          % (len(_HIST_FAILED), HIST_RETRY_FAIL_MINUTES))
        w("  快取最新交易日   : %s%s"
          % ("　".join("%s %s" % (k, v) for k, v in _lat.items()),
             "" if all(v >= _exp for v in _lat.values()) else "  ← ⚠️ 落後了"))
        # ⚠️ mtime 只是參考。新舊判斷已改成比對「最後一個交易日」，
        #    mtime 再新，只要日期落後一樣會重抓。
        w("  hist_AAPL 寫入   : %.1f 小時前（僅供參考，不是新舊判斷依據）" % _age)
    except Exception as _e:
        w("  快取新鮮度      : ❌ %s" % _e)
    w("  紀錄檔          : %s（%s）" % (
        SCHED_FILE,
        "已存在，重啟後仍看得到上次更新" if os.path.exists(SCHED_FILE)
        else "尚未產生 ← 還沒跑過第一次自動更新"))

    w("\n【對外連線】—— 這一段最關鍵")
    tests = [
        ("Nasdaq 股票清單", lambda: len(_get(NASDAQ_SCREENER, timeout=40, tries=1)
                                        .json().get("data", {}).get("rows", []))),
        # ⚠️ 印「最後三天」而不是筆數。筆數是 801 這種數字，看起來很健康，
        #    卻完全看不出資料停在哪一天 —— 資料卡在舊日期時筆數一樣正常。
        ("Nasdaq 歷史報價 AAPL（整段）",
         lambda: "…".join("%s %.2f" % r for r in _hist_nasdaq("AAPL")[-3:])),
        ("Nasdaq 歷史報價 AAPL（增量，從快取最後一天起）",
         lambda: (lambda _c: "…".join("%s %.2f" % r for r in
                                      _hist_nasdaq("AAPL", _c[-1][0])[-3:])
                  + "　（快取最後一天 %s）" % _c[-1][0]
                  if _c else "快取是空的")(_load_cache("hist_AAPL.json", None) or [])),
        # ⚠️ 伺服器是 UTC。UTC 的「今天」在美東還是昨天下午，
        #    抓資料時 todate 用哪一天會差一個交易日。
        ("伺服器現在時間",
         lambda: (lambda _u, _o: "UTC %s ／ 美東 %s（時差 %d 小時）"
                  % (_u.strftime("%Y-%m-%d %H:%M"),
                     (_u - timedelta(hours=_o)).strftime("%Y-%m-%d %H:%M"), _o))
                 (_utcnow(), _et_offset_hours(_utcnow()))),
        ("Nasdaq 季報 AAPL", lambda: str(get_fundamentals("AAPL", max_age_hours=0))[:90]),
    ]
    for name, fn in tests:
        t0 = time.time()
        try:
            r = fn()
            w("  ✅ %-22s %s（%.1f 秒）" % (name, r, time.time() - t0))
        except Exception as e:
            w("  ❌ %-22s %s: %s" % (name, type(e).__name__, str(e)[:120]))
            w("     %s" % traceback.format_exc().strip().split("\n")[-1][:120])

    w("\n【實跑一次小型篩選】市值前 150 大 / 50MA / 站上 / 不限排列")
    try:
        t0 = time.time()
        res = screen_watchlist(150, ma=50, direction="above", days=1, align="none")
        w("  耗時 %.0f 秒｜資料日期 %s｜符合 %d 檔"
          % (time.time() - t0, res.get("as_of"), len(res.get("rows", []))))
        w("  現價欄位        : %s"
          % ("已附加（盤中）" if res.get("quote", {}).get("ts")
             else "未附加（休市，符合預期）" if res.get("quote", {}).get("open") is False
             else "未附加 ← 盤中卻沒抓到，值得查"))
        w("    %-6s %-18.18s %8s %8s %7s  %s"
          % ("代號", "名稱", "收盤", "現價", "乖離", "創新高"))
        for r in res.get("rows", [])[:5]:
            w("    %-6s %-18.18s %8.2f %8s %+6.2f%%  %s"
              % (r["symbol"], r.get("name_zh") or r["name"], r["price"],
                 ("%.2f" % r["last"]) if r.get("last") is not None else "—",
                 r["gap"], r.get("new_high") or "-"))
        if not res.get("rows"):
            w("  ⚠️ 沒有任何結果 —— 多半是股價抓不到（看上面對外連線那段）")
    except Exception as e:
        w("  ❌ 篩選拋出例外: %s: %s" % (type(e).__name__, str(e)[:150]))
        w(traceback.format_exc()[-800:])

    w("\n" + "=" * 60)
    w("  把整份輸出貼給 Claude")
    w("=" * 60)
    return app.response_class(out.getvalue(), mimetype="text/plain; charset=utf-8")


@app.route("/icon.png")
def icon():
    """網站圖示。與台股版用同一張（咖啡杯 + 紅K笑臉）—— 同一個品牌家族。"""
    p = os.path.join(BASE_DIR, "icon.png")
    if not os.path.exists(p):
        return "", 404
    from flask import send_file
    resp = send_file(p, mimetype="image/png")
    # 長快取沒問題 —— 要換圖時把 head 裡的 ?v= 版本號加一即可。
    # ⚠️ Chrome 的 favicon 快取跟一般 HTTP 快取是分開的，強制重新整理清不掉，
    #    只有「換一個網址」才會讓它重抓，所以版本號是必要的。
    resp.headers["Cache-Control"] = "public, max-age=604800"
    return resp


@app.route("/.well-known/assetlinks.json")
def assetlinks():
    """Google Play TWA 的 Digital Asset Links 驗證檔。

    為什麼美股版也要有：TWA 只信任 assetlinks 驗證過的網域。
    us.stock-coffee.com 對 App 來說是**不同來源**，沒驗證過的話，
    從台股版點過來會被丟進 Custom Tab —— 那就是使用者看到的網址列。

    設定：Render → Environment 加上與台股版**完全相同**的
    TWA_PACKAGE 與 TWA_FINGERPRINT（同一個 App、同一組簽章）。
    另外 TWA 專案的 twa-manifest.json 要把本網域加進 additionalTrustedOrigins。
    """
    pkg = os.environ.get("TWA_PACKAGE", "")
    fps = []
    for k in sorted(os.environ):
        if k.startswith("TWA_FINGERPRINT"):
            fps += [f.strip() for f in os.environ[k].split(",") if f.strip()]
    seen = set()
    fps = [f for f in fps if not (f in seen or seen.add(f))]
    if not pkg or not fps:
        return jsonify([]), 200
    return jsonify([{
        "relation": ["delegate_permission/common.handle_all_urls"],
        "target": {"namespace": "android_app", "package_name": pkg,
                   "sha256_cert_fingerprints": fps},
    }])


@app.route("/manifest.json")
def manifest():
    return jsonify({
        "name": "美股咖啡館",
        "short_name": "美股咖啡館",
        "description": "美股選股工具：用 10/20/50/150 日均線與均線排列篩選市值前 300 大美股。",
        "start_url": "/",
        "id": "/",
        "scope": "/",
        "display": "standalone",
        "orientation": "portrait",
        "lang": "zh-Hant-TW",
        "categories": ["finance", "productivity"],
        "background_color": "#F1EAD9",
        "theme_color": "#33241A",
        "icons": [
            {"src": "/icon.png?v=2", "sizes": "192x192", "type": "image/png", "purpose": "any"},
            {"src": "/icon.png?v=2", "sizes": "512x512", "type": "image/png", "purpose": "any"},
            {"src": "/icon.png?v=2", "sizes": "512x512", "type": "image/png", "purpose": "maskable"},
        ],
    })


@app.route("/api/screen", methods=["POST"])
def api_screen():
    if not _valid_app_token(request.headers.get("X-App-Token")):
        return jsonify(error="連線憑證已過期，請重新整理頁面"), 403
    p = request.get_json(silent=True) or {}
    params = {
        "universe_n": int(p.get("universe_n") or 150),
        "ma": int(p.get("ma") or 50),
        "direction": "below" if p.get("direction") == "below" else "above",
        "days": 3 if int(p.get("days") or 1) == 3 else 1,
        "match": "all" if p.get("match") == "all" else "any",
        "align": p.get("align") or "none",
    }
    if params["universe_n"] not in (150, 300):
        return jsonify(error="股票範圍不支援"), 400
    if params["ma"] not in MA_SET:
        return jsonify(error="均線週期不支援"), 400
    if params["align"] not in ALIGN_NAMES:
        return jsonify(error="均線排列條件不支援"), 400
    return jsonify(job=start_job(screen_watchlist, params))


@app.route("/api/pullback", methods=["POST"])
def api_pullback():
    if not _valid_app_token(request.headers.get("X-App-Token")):
        return jsonify(error="連線憑證已過期，請重新整理頁面"), 403
    p = request.get_json(silent=True) or {}
    params = {
        "universe_n": int(p.get("universe_n") or 150),
        "ma": int(p.get("ma") or 50),
        "band": 3.0,
        "align": p.get("align") or "none",
    }
    if params["universe_n"] not in (150, 300):
        return jsonify(error="股票範圍不支援"), 400
    if params["ma"] not in MA_SET:
        return jsonify(error="均線週期不支援"), 400
    if params["align"] not in ALIGN_NAMES:
        return jsonify(error="均線排列條件不支援"), 400
    return jsonify(job=start_job(screen_pullback, params))


@app.route("/api/pro/new-high", methods=["POST"])
def api_pro_new_high():
    if not _valid_app_token(request.headers.get("X-App-Token")):
        return jsonify(error="連線憑證已過期，請重新整理頁面"), 403
    p = request.get_json(silent=True) or {}
    try:
        days = int(p.get("days") or 1)
    except (TypeError, ValueError):
        return jsonify(error="篩選日數格式錯誤"), 400
    if days not in (1, 3, 5):
        return jsonify(error="篩選日數只支援近一日、近三日或近五日"), 400
    return jsonify(job=start_job(screen_pro_new_high, {"days": days}))


@app.route("/api/pro/rs", methods=["POST"])
def api_pro_rs():
    if not _valid_app_token(request.headers.get("X-App-Token")):
        return jsonify(error="連線憑證已過期，請重新整理頁面"), 403
    p = request.get_json(silent=True) or {}
    try:
        period, threshold = int(p.get("period") or 60), int(p.get("threshold") or 90)
    except (TypeError, ValueError):
        return jsonify(error="RS 參數格式錯誤"), 400
    if period not in RS_PERIODS:
        return jsonify(error="RS 期間只支援 20、60、120 或 250 日"), 400
    if threshold not in (80, 90, 95):
        return jsonify(error="RS 門檻只支援 80、90 或 95"), 400
    return jsonify(job=start_job(screen_pro_rs, {"period": period, "threshold": threshold}))


@app.route("/api/job/<job_id>")
def api_job(job_id):
    j = JOBS.get(job_id)
    if not j:
        return jsonify(error="查無此工作"), 404
    return jsonify(j)


@app.route("/api/prefetch-status")
def api_prefetch_status():
    st = dict(PREFETCH_STATE)
    # 執行緒物件只供同一 process 的診斷，不能交給 jsonify；背景預抓啟動後若
    # 直接序列化會讓正式站這支端點固定回 500。
    st.pop("thread_obj", None)
    st["source"] = dict(LAST_SOURCE)
    # cache_dir 用來確認 Render 的持久化磁碟有沒有掛上 ——
    # 若顯示的是專案目錄而不是磁碟路徑，代表 CACHE_DIR 沒設，
    # 快取會在每次部署後消失，等於每次都要重新預抓 6 分鐘。
    st["cache_dir"] = CACHE_DIR
    st["disk_mounted"] = "/opt/render" in CACHE_DIR
    schedule = dict(SCHED_STATE)
    schedule.pop("thread_obj", None)
    st["schedule"] = schedule
    try:
        files = os.listdir(CACHE_DIR)
        st["cached_symbols"] = len([f for f in files if f.startswith("hist_")])
        st["cached_fundamentals"] = len([f for f in files if f.startswith("fund_")])
        st["cache_mb"] = round(sum(
            os.path.getsize(os.path.join(CACHE_DIR, f)) for f in files) / 1e6, 1)
    except Exception:
        pass
    return jsonify(st)


# ---------------------------------------------------------------- 背景執行緒
#
# ⚠️⚠️ **不要在模組載入時直接 start()。**
#
# 實測（2026-08-04，Render）：`import 時 PID 40 / 現在的 PID 43`。
# 也就是 import 之後發生了 fork —— 而 **fork 不會複製執行緒**。
# 子行程繼承了「執行緒跑過」的所有痕跡（enabled=True、心跳、entered_at），
# 執行緒本身卻留在父行程。症狀極度誤導：
#   · 旗標與心跳看起來正常，執行緒早就不在
#   · 預抓永遠停在 fork 當下那一格，done 永遠 False
#   · **完全沒有錯誤訊息**，因為沒有任何東西出錯，它只是不存在
#
# gunicorn `--preload` 是最常見的原因，但**這個服務沒有開 preload、
# 也沒有 gunicorn.conf.py**，代表 fork 來自平台包裝或其他我們控制不到的地方。
# 所以不要去猜是誰 fork 的 —— 改成「**在真正服務請求的行程裡才啟動**」，
# 不管中間 fork 幾次都不會有事。
#
# 用 PID 當鍵而不是布林旗標：布林值會被 fork 一起複製過去，
# 子行程會以為自己已經啟動過。

_BG_LOCK = threading.Lock()
_BG_PID = None


def _ensure_background():
    """在當前行程啟動背景執行緒。可重複呼叫，每個行程只會真的做一次。"""
    global _BG_PID
    pid = os.getpid()
    if _BG_PID == pid:
        return
    with _BG_LOCK:
        if _BG_PID == pid:          # 雙重檢查：多執行緒同時進來
            return
        _BG_PID = pid
        if os.environ.get("ENABLE_PREFETCH", "1") == "1":
            try:
                t = threading.Thread(target=lambda: prefetch(300), daemon=True)
                t.start()
                PREFETCH_STATE["thread_obj"] = t
            except Exception as e:
                PREFETCH_STATE["stage"] = "❌ 執行緒建立失敗 %s" % e
        if (ENV_DAILY_RAW or "1") == "1":
            try:
                t2 = threading.Thread(target=_daily_updater, daemon=True)
                t2.start()
                SCHED_STATE["thread_started"] = True
                SCHED_STATE["thread_obj"] = t2
            except Exception as e:
                SCHED_STATE["loop_error"] = "執行緒建立失敗 %s: %s" % (type(e).__name__, e)


@app.before_request
def _bg_boot():
    # ⚠️ 這裡要夠便宜：每個請求都會經過。命中時只是一次整數比較。
    if _BG_PID != os.getpid():
        _ensure_background()


ENV_DAILY_RAW = os.environ.get("ENABLE_DAILY_UPDATE")
SCHED_STATE["env_raw"] = ENV_DAILY_RAW
SCHED_STATE["thread_started"] = False

# 本機直接跑（python app.py）時沒有 fork，立刻啟動比等第一個請求好。
if __name__ == "__main__":
    _ensure_background()

# 每日自動更新。設 ENABLE_DAILY_UPDATE=0 可關閉（本機開發時通常會關）。
# ⚠️ 把「環境變數的原始值」與「執行緒有沒有真的啟動」分開記下來。
#    以前診斷只看得到 enabled 旗標，就自己推論成「一定是被設成 0」——
#    但旗標是 False 也可能是執行緒根本沒被建立、或建立了卻在設旗標前就死掉。
#    三種原因症狀一樣，不記錄就只能猜。



if __name__ == "__main__":
    port = int(os.environ.get("PORT", 5002))
    print("美股咖啡館 → http://127.0.0.1:%d" % port)
    app.run(host="0.0.0.0", port=port, debug=False)
