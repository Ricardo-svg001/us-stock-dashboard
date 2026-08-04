#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""美股咖啡館 US Stock Coffee — 觀察清單策略（資料層＋篩選邏輯）

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
import os
import re
import threading
import time
import uuid
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta, timezone

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


def get_history(symbol, max_age_hours=12, debug=False):
    """單一個股的收盤價序列，回傳 [(YYYY-MM-DD, close), …]，由舊到新。

    來源依 HIST_SOURCES 順序嘗試，任一成功即回傳。
    每檔一個快取檔，所以每天只需補抓一次；全部失敗回空清單，呼叫端自行忽略。
    debug=True 會把各來源的錯誤印出來（診斷用）。
    """
    key = "hist_%s.json" % symbol.upper()
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


def load_histories(symbols, status_cb=None, workers=8):
    """並行抓多檔歷史。回傳 {symbol: [(date, close), …]}。
    Stooq 沒有批次端點，只能逐檔抓，所以第一次會比較久（之後吃快取）。"""
    out, done = {}, [0]
    lock = threading.Lock()

    def work(sym):
        h = get_history(sym)
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


def load_fundamentals(symbols, status_cb=None, workers=8):
    """並行抓基本面。抓不到的給空值，不影響篩選。"""
    out, done = {}, [0]
    lock = threading.Lock()

    def work(sym):
        f = get_fundamentals(sym)
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
# 改用**市場寬度**：多少比例的個股站上自己的 200MA。
# 概念一樣（「多數人已在場內」vs「籌碼洗乾淨了」），而且**用現有的 hist_ 快取就能算**。
#
# ⚠️⚠️ **關鍵差異：融資是慢變數，寬度是快變數。**
#   台股的「底部」能佔 23%，是因為融資在價格反彈後還低迷好幾個月。
#   寬度卻跟價格幾乎同步恢復，所以「低寬度＋站上均線」極少同時發生 ——
#   直接照搬會讓底部只剩 1.4%（回測實測），整個狀態形同虛設。
#   解法：底部改看**近 60 日的最低寬度**（「這一季內被洗過」），
#   這個條件會持續好幾個月，行為才跟融資一致。修正後底部回到 10.7%。
#
# 10 年回測（2016-08~2026-07，納斯達克綜合指數 + 前 300 大）：
#   上升段 49.2%／高點警訊 10.2%／下跌段 29.9%／底部 10.7%
#   底部出現在 2019-01（2018Q4 急殺後）、2020-04~08（COVID 後）、
#   2022-07~2023-01（熊市打底）、2025-05~07（關稅急殺後）—— 全部對得上真實事件。
#
# ⚠️ 60 日這個數字**沒有最佳化過**，刻意不掃參數找最佳值（那只會過擬合這 10 年）。
#    60 天≈一季，理由是語意不是數據。

BREADTH_MA = 200            # 個股用幾日均線算寬度
BREADTH_TOP = 85.0          # 當下寬度 ≥ 這個 → 頂部區（約 P90）
BREADTH_WASH = 30.0         # 近 N 日最低寬度 ≤ 這個 → 洗過盤
WASH_LOOKBACK = 60          # 「最近」是幾個交易日
PHASE_MA = 50               # 指數用幾日均線定方向（對應台股的季線角色）
PHASE_STICKY = 3            # 連續幾天成立才切換狀態

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


# ⚠️ 診斷用：記下實際用了哪個來源、各來源為什麼失敗。
#    這個欄位存在的理由：FRED **會擋機房 IP**（Render 上實測 0 筆，本機正常），
#    跟 stooq / yahoo 是同一類問題，而那在本機測不出來。
INDEX_SOURCES = [
    ("FRED NASDAQCOM", lambda: _idx_from_fred()),
    ("Nasdaq COMP",    lambda: _idx_from_nasdaq("COMP", "index")),
    ("ONEQ (ETF 代理)", lambda: _idx_from_nasdaq("ONEQ", "stocks")),
]
_INDEX_SRC = {"name": None, "n": 0, "errs": []}


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
        return cached
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
            return out
        errs.append("%s: 只有 %d 筆" % (name, len(out)))
    _INDEX_SRC.update({"name": None, "n": 0, "errs": errs})
    return cached or {}       # ⚠️ 抓不到別寫空的蓋掉舊資料


def build_breadth():
    """從 hist_ 快取算市場寬度，存成 breadth.json。

    ⚠️ **只能在預抓流程裡呼叫。** 要讀幾百個快取檔、每檔算 200MA，
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
        # 只留最近 400 天，夠算洗盤回看期就好
        keep = dict(sorted(out.items())[-400:])
        _save_cache("breadth.json", keep)
        return keep
    return None


PHASE_UI = {
    "bull_up":   {"dot": "🟢", "zh": "順風・上升段", "en": "Tailwind · Uptrend",
                  "zh_do": "順勢操作，讓獲利跑",
                  "en_do": "Ride the trend, let winners run"},
    "bull_top":  {"dot": "🟠", "zh": "順風・高點警訊", "en": "Tailwind · Near a Top",
                  "zh_do": "多數股票都在高檔，開始想賣點",
                  "en_do": "Most stocks extended — think about exits"},
    "bear_down": {"dot": "🔴", "zh": "逆風・下跌段", "en": "Headwind · Declining",
                  "zh_do": "守紀律，不攤平",
                  "en_do": "Stay disciplined, never average down"},
    "bear_low":  {"dot": "🔵", "zh": "逆風・底部", "en": "Headwind · Basing",
                  "zh_do": "剛被洗過，可以開始留意",
                  "en_do": "Washed out — start watching"},
}


def _phase_raw(close, ma, breadth, wash_min):
    """單日的市場階段。**寬度定位置，指數 vs 50MA 定方向。**"""
    if close is None or ma is None or breadth is None:
        return None
    above = close > ma
    if breadth >= BREADTH_TOP:
        return "bull_top" if above else "bear_down"
    if wash_min is not None and wash_min <= BREADTH_WASH:
        return "bear_low" if above else "bear_down"
    return "bull_up" if above else "bear_down"


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
    val = _phase_compute()
    _PHASE_MEMO.update(at=now, val=val)
    return val


# ⚠️ 為什麼是 unknown —— 這個欄位存在的理由：
#    `_phase_compute()` 整包在 except 裡，任何失敗都長得一模一樣（unknown）。
#    沒有這個就只能猜，而線上與本機的差異永遠猜不到。
_PHASE_WHY = {"why": "還沒算過", "steps": []}


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
        ma, run = {}, 0.0
        for i, d in enumerate(ids):
            run += px[i]
            if i >= PHASE_MA:
                run -= px[i - PHASE_MA]
            if i >= PHASE_MA - 1:
                ma[d] = run / PHASE_MA
        st.append("指數 %dMA 可算 %d 天（~%s）"
                  % (PHASE_MA, len(ma), max(ma) if ma else "—"))
        recent = bd[-30:]
        hit = [d for d in recent if d in ma]
        st.append("breadth 最近 30 天有 %d 天對得上指數日期" % len(hit))
        if not hit:
            # ⚠️ 兩邊日期完全沒交集：通常是指數來源的交易日曆或格式不同
            _PHASE_WHY.update(
                why="日期對不上：breadth 最新 %s，指數 50MA 最新 %s"
                    % (max(bd), max(ma) if ma else "—"), steps=st)
            return "unknown", "", "", None
        seq = []
        bpos = {d: i for i, d in enumerate(bd)}
        for d in recent:
            if d not in ma:
                continue
            i = bpos[d]
            window = [br[x] for x in bd[max(0, i - WASH_LOOKBACK + 1):i + 1]]
            p = _phase_raw(idx.get(d), ma.get(d), br[d],
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


def prefetch(universe_n=300):
    """啟動時先把清單與歷史抓好，使用者才不用等。"""
    PREFETCH_STATE.update(stage="取得股票清單", done=False)
    uni = get_universe(universe_n)
    PREFETCH_STATE["stage"] = "讀取股價資料"

    def cb(i, total):
        PREFETCH_STATE["stage"] = "讀取股價資料 %d / %d" % (i, total)
    syms = [u["symbol"] for u in uni]
    load_histories(syms, status_cb=cb)
    PREFETCH_STATE["stage"] = "讀取基本面資料"

    def cb2(i, total):
        PREFETCH_STATE["stage"] = "讀取基本面資料 %d / %d" % (i, total)
    load_fundamentals(syms, status_cb=cb2)   # 預抓時不算本益比，篩選時才用當下價格重算
    # ⚠️ 市場階段要用的兩份資料，都在這裡算好存檔 —— 首頁只讀快取、絕不自己算
    PREFETCH_STATE["stage"] = "納斯達克綜合指數"
    try:
        get_nasdaq_index()
    except Exception:
        pass
    PREFETCH_STATE["stage"] = "計算市場寬度"
    try:
        build_breadth()
    except Exception:
        pass
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
SCHED_STATE = {"enabled": False, "next_run": "—", "last_run": "—", "last_result": "—",
               "loop_error": "", "heartbeat": "—", "heartbeat_ts": 0}

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
    try:
        _sched_load()
    except Exception:
        pass
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
                prefetch(300)
                SCHED_STATE["last_result"] = "成功"
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
  <a class="navitem" data-page="p1" href="/screener"><i>📈</i><b data-i18n="p1.title">觀察清單策略</b><small data-i18n="nav.screen.sub">找出強勢主流題材股</small></a>
  <a class="navitem" data-page="p3" href="/pullback"><i>🎯</i><b data-i18n="p3.title">飆股拉回找買點</b><small data-i18n="nav.pull.sub">收盤回到均線±3%</small></a>
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

__PHASE_BAR__

  <div class="card" style="max-width:560px">
    <h2 data-i18n="home.about">關於這個工具</h2>
    <div style="font-size:14.5px;color:#555;line-height:1.95" data-i18n-html="home.aboutBody">
      台股咖啡館的美股版。用<b>均線</b>從市值前 300 大的美股裡，
      篩出站上或跌破指定均線、以及符合特定均線排列的股票。<br><br>
      均線採美股習慣的 <b>10 / 20 / 50 / 150 日</b>——
      50 日線相當於台股季線的地位，150 日線用來看中長期趨勢。<br><br>
      資料為每日收盤價，非即時報價。
    </div>
  </div>

  <a class="menu-item" href="/screener" style="text-decoration:none;color:inherit">
    <span class="ic">📈</span>
    <span class="body"><span class="nm" data-i18n="p1.title">觀察清單策略</span>
      <span class="ds" data-i18n="home.c1">依均線與均線排列篩選個股</span></span>
    <span class="chev">›</span>
  </a>
  <a class="menu-item" href="/pullback" style="text-decoration:none;color:inherit">
    <span class="ic">🎯</span>
    <span class="body"><span class="nm" data-i18n="p3.title">飆股拉回找買點</span>
      <span class="ds" data-i18n="home.c2">收盤回到指定均線 ±3%</span></span>
    <span class="chev">›</span>
  </a>
</div>

<!-- ============ 觀察清單策略 ============ -->
<div class="page" id="p1">
  <h2 class="ptitle" data-i18n="p1.title">觀察清單策略</h2>
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
      <p><b>適合誰</b>：持有數天到數週的波段交易者。這裡是收盤資料，做不了當沖。</p>
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

<!-- ============ 飆股拉回找買點 ============ -->
<div class="page" id="p3">
  <h2 class="ptitle" data-i18n="p3.title">飆股拉回找買點</h2>
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
  "nav.home": "Menu", "nav.screen.sub": "Find leading stocks",
  "nav.pull.sub": "Close back within ±3% of an MA",
  "nav.tw": "Taiwan Stock Coffee", "nav.tw.sub": "Stock Coffee · TW screener",
  "ui.mkt": "TW", "ui.mkt.aria": "Switch to Taiwan Stock Coffee",
  "home.about": "About this tool",
  "home.aboutBody": "The US edition of Stock Coffee. Screen the top 300 US companies by market cap using <b>moving averages</b> \u2014 crossing above or below a chosen MA, or matching a specific MA alignment.<br><br>The MA set follows US convention: <b>10 / 20 / 50 / 150-day</b>. The 50-day line plays the role Taiwan's 60-day line does; the 150-day tracks the intermediate trend.<br><br>Data is daily closing prices, not real-time quotes.",
  "home.c1": "Screen by moving average and MA alignment",
  "home.c2": "Close back within ±3% of a chosen MA",
  "home.c3": "The Taiwan edition — same logic, already live",
  "p1.title": "Watchlist Screener", "p3.title": "Pullback Entry Finder",
  "p1.introT": "Find stocks that are moving right now — using moving averages",
  "p1.intro": "<p>A moving average is the average cost of a group of buyers. Above the 50-day line, the people who bought this quarter are in profit; below the 150-day line, most buyers of the past half-year are underwater. Moving averages don't predict — they tell you where market participants stand, and that shapes what they do next.</p><p>This screener filters the top 150 or 300 US companies by market cap: crossing above or below the 10, 20, 50 or 150-day moving average, or screening directly by <b>MA alignment</b> — strict bullish (10&gt;20&gt;50&gt;150) means later buyers paid more and still bought, which usually marks a trend in progress.</p><p>If the screen returns too many names, the dropdowns above narrow it further. <b>The sector distribution is itself a signal</b> — when twelve of thirty results share an industry, that's where money is going.</p><p><b>Who it's for</b>: swing traders holding days to weeks. This is closing data — not built for day trading.</p>",
  "p3.introT": "Wait for a strong stock to come back, instead of chasing the high",
  "p3.intro": "<p>Leading stocks don't rise every day. After a run they consolidate, and that consolidation often stalls near a moving average — because that line is a group's average cost, which becomes psychological support.</p><p>This screen finds stocks whose <b>latest close has returned to within ±3% of the moving average you choose</b>. The point isn't to call the bottom; it's an entry with controlled risk — you're not buying the high, and if you're wrong the stop is obvious (a break of that line).</p><p>Which average to use depends on your holding period — the 20-day for shorter trades, the 50 or 150-day for swings. Combined with the <b>MA alignment</b> filter, you can look only for stocks whose trend is intact and merely resting.</p><p>Results are sorted by <b>how close price is to the line</b> — the top of the list pulled back the most precisely.</p>",
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
    if (lastRows.length) render({rows:lastRows, as_of:lastMeta.as_of,
        ma_name_zh:lastMeta.ma_name_zh, ma_name:lastMeta.ma_name});
    if (lastRows3.length) render3({rows:lastRows3, as_of:lastMeta3.as_of, band:lastMeta3.band,
        ma_name_zh:lastMeta3.ma_name_zh, ma_name:lastMeta3.ma_name});
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

/* ---- 依網址開對應分頁 ---- */
if (START_PAGE && $("#" + START_PAGE)){
  document.querySelectorAll(".page").forEach(p => p.classList.remove("show"));
  $("#" + START_PAGE).classList.add("show");
  document.querySelectorAll(".navitem").forEach(i =>
    i.classList.toggle("active", i.dataset.page === START_PAGE));
}
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

PAGE_ROUTES = {"screener": "p1", "pullback": "p3"}


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
        '<span class="q-zh">目前 <b>' + b + '</b> 的成分股站在自己的 200 日均線之上，'
        '納斯達克綜合指數在 50 日均線'
        + ('<b>之上</b>' if phase.startswith("bull") else '<b>之下</b>') + '。<br><br>'
        '寬度告訴你<b>市場走到循環的哪個位置</b>，指數與均線告訴你<b>現在往哪走</b>。'
        '這不預測行情，只描述環境。</span>'
        '<span class="q-en" style="display:none"><b>' + b + '</b> of constituents are '
        'above their own 200-day average, and the Nasdaq Composite is '
        + ('<b>above</b>' if phase.startswith("bull") else '<b>below</b>')
        + ' its 50-day average.<br><br>'
        'Breadth tells you <b>where the market sits in the cycle</b>; '
        'the index versus its average tells you <b>which way it is going</b>. '
        'This describes the environment — it does not predict it.</span>'
        '</div></details>')


def _render(start_page="home"):
    html = PAGE.replace("__APP_TOKEN__", make_app_token())
    html = html.replace("__START_PAGE__", start_page, 1)
    html = html.replace("__TW_URL__", TW_URL)
    html = html.replace("__PHASE_BAR__", _phase_banner_html())
    return render_template_string(html)


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

    w("\n【市場階段】")
    try:
        _ph, _do, _d, _b = market_phase_cached()
        _ui = PHASE_UI.get(_ph)
        w("  目前階段        : %s" % ("%s %s（%s）" % (_ui["dot"], _ui["zh"], _do)
                                      if _ui else "unknown ← 缺 breadth 或指數快取"))
        w("  市場寬度        : %s（%% 成分股站上自身 200MA）"
          % ("%.1f%%" % _b if _b is not None else "—"))
        w("  資料日期        : %s" % (_d or "—"))
        _br = _load_cache("breadth.json", 24 * 365) or {}
        _ix = _load_cache("nasdaq_index.json", 24 * 365) or {}
        w("  breadth.json    : %d 天%s" % (len(_br), "" if _br else "  ← 還沒算過"))
        w("  納斯達克指數     : %d 天%s" % (len(_ix), "" if _ix else "  ← 抓不到"))
        w("  指數來源        : %s" % (_INDEX_SRC["name"] or "全部失敗"))
        for _e in _INDEX_SRC["errs"]:
            w("     ✗ %s" % _e)
        w("  判定過程        : %s" % _PHASE_WHY["why"])
        for _st in _PHASE_WHY["steps"]:
            w("     · %s" % _st)
        w("  門檻            : 頂部≥%.0f%%　洗盤≤%.0f%%（近 %d 日最低）　方向 %dMA　黏著 %d 天"
          % (BREADTH_TOP, BREADTH_WASH, WASH_LOOKBACK, PHASE_MA, PHASE_STICKY))
    except Exception as e:
        w("  ❌ %s: %s" % (type(e).__name__, str(e)[:80]))

    w("\n【每日自動更新】")
    # ⚠️ 不要只看 enabled —— 那個旗標設過一次就不會變，執行緒死了它還是「是」。
    #    要看心跳：正常情況每 5 分鐘內一定會更新一次。
    _hb_age = time.time() - (SCHED_STATE.get("heartbeat_ts") or 0)
    if not SCHED_STATE["enabled"]:
        _health = "否 ← ENABLE_DAILY_UPDATE=0，資料不會自動變新"
    elif _hb_age > 600:
        _health = "⚠️ 有啟動但心跳停了 %.0f 分鐘 ← 執行緒可能卡住" % (_hb_age / 60)
    else:
        _health = "是（心跳 %.0f 秒前）" % _hb_age
    w("  排程執行中      : %s" % _health)
    if SCHED_STATE.get("loop_error"):
        w("  ⚠️ 骨幹錯誤     : %s" % SCHED_STATE["loop_error"])
    w("  觸發時間        : 每個美東交易日 %02d:00 ET（收盤後 %d 小時）"
      % (UPDATE_HOUR_ET, UPDATE_HOUR_ET - 16))
    w("  下次更新        : %s" % SCHED_STATE["next_run"])
    w("  上次更新        : %s" % SCHED_STATE["last_run"])
    w("  上次結果        : %s" % SCHED_STATE["last_result"])
    w("  紀錄檔          : %s（%s）" % (
        SCHED_FILE,
        "已存在，重啟後仍看得到上次更新" if os.path.exists(SCHED_FILE)
        else "尚未產生 ← 還沒跑過第一次自動更新"))

    w("\n【對外連線】—— 這一段最關鍵")
    tests = [
        ("Nasdaq 股票清單", lambda: len(_get(NASDAQ_SCREENER, timeout=40, tries=1)
                                        .json().get("data", {}).get("rows", []))),
        ("Nasdaq 歷史報價 AAPL", lambda: len(_hist_nasdaq("AAPL"))),
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


@app.route("/api/job/<job_id>")
def api_job(job_id):
    j = JOBS.get(job_id)
    if not j:
        return jsonify(error="查無此工作"), 404
    return jsonify(j)


@app.route("/api/prefetch-status")
def api_prefetch_status():
    st = dict(PREFETCH_STATE)
    st["source"] = dict(LAST_SOURCE)
    # cache_dir 用來確認 Render 的持久化磁碟有沒有掛上 ——
    # 若顯示的是專案目錄而不是磁碟路徑，代表 CACHE_DIR 沒設，
    # 快取會在每次部署後消失，等於每次都要重新預抓 6 分鐘。
    st["cache_dir"] = CACHE_DIR
    st["disk_mounted"] = "/opt/render" in CACHE_DIR
    st["schedule"] = dict(SCHED_STATE)
    try:
        files = os.listdir(CACHE_DIR)
        st["cached_symbols"] = len([f for f in files if f.startswith("hist_")])
        st["cached_fundamentals"] = len([f for f in files if f.startswith("fund_")])
        st["cache_mb"] = round(sum(
            os.path.getsize(os.path.join(CACHE_DIR, f)) for f in files) / 1e6, 1)
    except Exception:
        pass
    return jsonify(st)


if os.environ.get("ENABLE_PREFETCH", "1") == "1":
    threading.Thread(target=lambda: prefetch(300), daemon=True).start()

# 每日自動更新。設 ENABLE_DAILY_UPDATE=0 可關閉（本機開發時通常會關）。
if os.environ.get("ENABLE_DAILY_UPDATE", "1") == "1":
    threading.Thread(target=_daily_updater, daemon=True).start()


if __name__ == "__main__":
    port = int(os.environ.get("PORT", 5002))
    print("美股咖啡館 → http://127.0.0.1:%d" % port)
    app.run(host="0.0.0.0", port=port, debug=False)
