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
import holidays
from flask import Flask, jsonify, request, render_template_string

# ---------------------------------------------------------------- 基本設定

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
CACHE_DIR = os.environ.get("CACHE_DIR") or os.path.join(BASE_DIR, "cache")
os.makedirs(CACHE_DIR, exist_ok=True)

APP_VERSION = "2026.08.28.2"
BUILD_COMMIT = (os.environ.get("RENDER_GIT_COMMIT") or "local")[:12]
BUILD_BRANCH = os.environ.get("RENDER_GIT_BRANCH") or "local"
BUILD_STARTED_AT = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")


def _build_info():
    return {"version": APP_VERSION, "commit": BUILD_COMMIT,
            "branch": BUILD_BRANCH, "started_at": BUILD_STARTED_AT}


def _build_badge_html():
    return ("<div class='site-version'>Version %s · commit %s · 本次服務啟動 %s</div>"
            % (APP_VERSION, BUILD_COMMIT, BUILD_STARTED_AT))

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
# 5 年 ≈ 1,260 個交易日 —— 支援到「5 年新高」，也涵蓋所有均線與 RS 需求。
#
# ⚠️ 加大這個值只影響「第一次抓取」；之後每天只補新的交易日（見 get_history）。
#    但**改這個常數會讓現有快取全部被判定為「太短」而整段重抓** ——
#    300 檔約 6 分鐘。這是一次性的，不是每天都會發生。
#
# ⚠️⚠️ **改這個值時，`NH_TIERS` 的最長級距必須跟著檢查。**
#    級距比 HIST_DAYS 長的話，`new_high_label()` 會因為 `len(closes) < n` 永遠跳過它，
#    結果是**那一級靜悄悄地永遠不會出現** —— 不會報錯，只是不見了。
#    2026-08-06 從 780（3 年）拉到 1260（5 年）就是為了讓「5 年新高」真的算得出來。
HIST_DAYS = 1260


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
# ⚠️ range 要 >= HIST_DAYS 換算的年數，否則備援回來的資料永遠達不到滿額，
#    「5 年新高」那一級就會在走備援的那幾檔上安靜地消失。
YAHOO = ("https://query{n}.finance.yahoo.com/v8/finance/chart/{sym}"
         "?range=5y&interval=1d")

# 最近一次成功的來源，供 /api/prefetch-status 顯示
LAST_SOURCE = {"name": None, "fails": 0, "incremental": False}


NASDAQ_HIST = ("https://api.nasdaq.com/api/quote/{sym}/historical"
               "?assetclass=stocks&fromdate={frm}&todate={to}&limit=9999")


def _hist_nasdaq(symbol, frm_date=None):
    """Nasdaq 官方歷史報價。

    與股票清單同一台主機——實測那台對我們沒有設限，所以列為首選。
    回傳格式：data.tradesTable.rows[]，日期是 MM/DD/YYYY、價格帶 $ 與逗號，
    且**由新到舊**排列，這裡會轉成由舊到新。

    frm_date（"YYYY-MM-DD"）只抓該日之後 —— 增量更新用，避免每天重抓五年份。
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


# ---------------------------------------------------------------- 拆股護欄
#
# ⚠️⚠️ **增量抓取遇上拆股，會安靜地毀掉一整檔股票的所有指標。**
#
# 機制：`_get_history_now()` 只抓「最後一天之後」的新資料再併回舊快取。
# 供應商在拆股後回的是**還原過**的新價格，但**舊的一千多列永遠不會被重抓** ——
# 於是同一條序列裡混著拆股前與拆股後兩種口徑。
#
# 具體後果（以 4 拆 1 為例）：序列上出現一根 −75% 的假崩盤，
# 50MA 還停在舊價位 → 這檔被判定「跌破所有均線」、創新高永遠不成立、
# RS 掉到最低百分位。**完全不會報錯，而且錯掉的列不會自我修復。**
# 前 300 大裡每年都有幾檔拆股（NVDA 2024-06 十拆一、AAPL 2020-08 四拆一）。
#
# 護欄做法：**比對跳動幅度是不是接近整數比例**，而不是只看「跌超過 N%」。
# 單日 −35% 在美股是可能的（財報爆雷），拿門檻硬切會把真崩盤誤判成拆股。
SPLIT_RATIOS = (1.5, 2, 3, 4, 5, 6, 7, 8, 10, 15, 20, 30)
SPLIT_TOL = 0.05                 # 比例容差 5%（拆股當天仍有正常漲跌）
_SPLIT_REFETCH = {}              # key → 已強制重抓的日期，同一天只做一次
SPLIT_NOTES = {}                 # key → 說明，給 /api/diag 看


def _split_ratio(prev, cur):
    """相鄰兩天的價格跳動像不像拆股？像的話回傳比例字串，否則回 None。"""
    try:
        prev, cur = float(prev), float(cur)
    except (TypeError, ValueError):
        return None
    if prev <= 0 or cur <= 0:
        return None
    r = prev / cur
    for n in SPLIT_RATIOS:
        if abs(r - n) <= n * SPLIT_TOL:          # 正拆：舊價高、新價低
            return "1:%g" % n
        if abs(r - 1.0 / n) <= (1.0 / n) * SPLIT_TOL:   # 反向拆股：舊價低、新價高
            return "%g:1" % n
    return None


def _find_split_breaks(rows):
    """整段掃描，回傳**所有**疑似拆股斷層 [(日期, 比例), …]。

    ⚠️ 掃全段而不是只看尾巴：程式可能好幾天沒跑，斷層不一定落在最近幾天。
       成本是每檔 1,260 次浮點比較，可以忽略。

    ⚠️⚠️ **一定要回傳全部，不能只回第一個。**
       同一檔股票可能先有一次真崩盤（查證後標記為「來源就長這樣」），
       之後才真的拆股。只回第一個的話，永遠回傳那個已查證的崩盤，
       **後來真正的拆股就被永久遮住了** —— 而那正是這個護欄要抓的東西。
    """
    out = []
    for i in range(1, len(rows)):
        ratio = _split_ratio(rows[i - 1][1], rows[i][1])
        if ratio:
            out.append((rows[i][0], ratio))
    return out


def _get_history_now(symbol, key, debug=False):
    """實際去抓。**已經有的歷史不重抓，只補新的交易日。**

    這是把歷史拉長（1 年 → 3 年 → 2026-08-06 起 5 年）之後的關鍵優化：
    一次抓 5 年約 140 KB，300 檔就是 40 MB —— 每天全部重抓很浪費，
    而且會讓每日更新的時間跟第一次一樣久。
    ⚠️ 那 40 MB 是**下載量**，不是存下來的大小；快取只留 [日期, 收盤價]。

    做法：
      1. 讀出快取（**不管多舊**，`max_age_hours=None`）
      2. 若舊資料的起點夠早（涵蓋 HIST_DAYS 所需區間），只抓「最後一天之後」的資料
      3. 合併、去重（以日期為鍵，新的覆蓋舊的）、排序、裁到 HIST_DAYS
      4. 若舊資料太短（例如剛把 HIST_DAYS 從 780 調到 1260），就整段重抓

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

    errs = []

    def _fetch(from_date):
        """跑一次來源鏈。from_date 為 None 代表整段重抓。"""
        for name, fn in HIST_SOURCES:
            try:
                got = fn(symbol, from_date) if name == "nasdaq" else fn(symbol)
                if got:
                    LAST_SOURCE["name"] = name
                    LAST_SOURCE["incremental"] = bool(from_date) and name == "nasdaq"
                    if from_date:                 # 增量：與舊資料合併
                        merged = dict(old)
                        merged.update(dict(got))  # 同一天以新抓到的為準
                        out = sorted(merged.items())
                    else:
                        out = sorted(dict(got).items())
                    return out[-HIST_DAYS:]
            except Exception as e:
                errs.append("%s: %s %s" % (name, type(e).__name__, str(e)[:90]))
        return []

    rows = _fetch(frm)

    # ---- 拆股護欄：只有「增量合併」的結果才可能混到兩種口徑 ----
    #
    # ⚠️ 比例比對必然會有偽陽性：單日 −50% 的財報爆雷跟 1:2 拆股在數字上長得一樣。
    #    偽陽性的代價只是「多抓一次完整歷史」，但**不能每天都多抓一次** ——
    #    所以確認過「來源本身就是這樣」之後，把結論記進 meta，日後直接跳過。
    #    📌 這條 memo 是整個護欄能不能長期存在的關鍵：
    #       沒有它，一檔五年前崩過盤的股票會被永遠每天多抓一次，
    #       而且 /api/diag 上會永遠掛著一個假警告。
    verified = {tuple(b) for b in (meta.get("verified_breaks") or [])}
    if frm and rows:
        fresh = [b for b in _find_split_breaks(rows) if b not in verified]
        if not fresh:
            SPLIT_NOTES.pop(key, None)
        elif _SPLIT_REFETCH.get(key) == _utcnow().strftime("%Y-%m-%d"):
            SPLIT_NOTES[key] = "%s 疑似拆股 %s，今日已重抓過，暫不重試" % fresh[0]
        else:
            _SPLIT_REFETCH[key] = _utcnow().strftime("%Y-%m-%d")
            full = _fetch(None)
            if full:
                rows, frm = full, None          # frm=None 讓下面重寫 meta
                again = [b for b in _find_split_breaks(rows) if b not in verified]
                if again:
                    # 整段重抓後仍有斷層 → 不是快取混到兩種口徑，
                    # 而是**來源本身就沒還原**（或那天真的暴跌）。記住，別再重抓。
                    meta["verified_breaks"] = sorted(
                        [list(b) for b in verified] + [list(b) for b in again])
                    _save_cache(meta_key, meta)
                    SPLIT_NOTES[key] = "%s 落差 %s：整段重抓後仍在，判定為來源原始資料" % again[0]
                else:
                    SPLIT_NOTES[key] = "%s 疑似拆股 %s，已整段重抓修正" % fresh[0]

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
        # 剛做完一次完整抓取，記下起始日 —— 下次就能安心走增量。
        # ⚠️ 用更新而不是整個蓋掉：`verified_break`（拆股護欄的查證結論）
        #    也存在這個檔裡，蓋掉的話那檔股票會每天被重抓一次，永遠好不了。
        meta.update({"full_from": need_from, "at": rows[-1][0]})
        _save_cache(meta_key, meta)
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
FUND_EARNINGS = "https://api.nasdaq.com/api/company/{sym}/earnings-surprise?limit=4"

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
    key = "fund_v2_%s.json" % symbol.upper()  # v2: 包含近兩年 H1／H2 EPS
    cached = _load_cache(key, max_age_hours)
    if cached is not None:
        return cached
    return _fetch_once(key,
                       lambda: _get_fundamentals_now(symbol, key),
                       lambda: _load_cache(key, max_age_hours))


def _get_fundamentals_now(symbol, key):
    out = {"eps_yoy": None, "rev_yoy": None, "period": None,
           "eps": None, "rev": None, "eps_halves": []}
    try:
        j = _get(FUND_REV.format(sym=symbol.upper()), timeout=25, tries=2).json()
        rows = (((j or {}).get("data") or {}).get("revenueTable") or {}).get("rows") or []

        quarters, cur, eps_points = [], None, []
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
                for col in ("value2", "value3", "value4"):
                    amount, report_date = _paren_date(r.get(col))
                    if amount is not None and report_date:
                        eps_points.append((report_date, amount))

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

        # 依實際財報日期整理自然年度 H1／H2；每個半年需有兩季才顯示。
        grouped = {}
        for report_date, amount in set(eps_points):
            year, month = int(report_date[:4]), int(report_date[5:7])
            half = 1 if month <= 6 else 2
            grouped.setdefault((year, half), []).append(amount)
        halves = []
        for (year, half), amounts in sorted(grouped.items(), reverse=True):
            if len(amounts) >= 2:
                halves.append({"label": "%d H%d" % (year, half),
                               "value": round(sum(amounts), 2)})
            if len(halves) >= 4:
                break
        out["eps_halves"] = halves
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


def get_valuation(symbol, max_age_hours=24):
    """Nasdaq 個股摘要中的本益比與殖利率；只供進階欄位勾選後使用。"""
    symbol = symbol.upper()
    key = "valuation_v2_%s.json" % symbol
    cached = _load_cache(key, max_age_hours)
    if cached is not None:
        return cached

    def fetch():
        out = {"per": None, "yield": None}
        try:
            j = _get(FUND_SUMMARY.format(sym=symbol), timeout=25, tries=2).json()
            data = (((j or {}).get("data") or {}).get("summaryData") or {})
            per = (data.get("PERatio") or {}).get("value")
            yld = (data.get("Yield") or {}).get("value")
            per_value = _num(per)
            # Nasdaq 目前的 summary 已不一定回傳 PERatio。缺值時以官方最近
            # 四季 EPS 合計（TTM）及最新收盤價計算，虧損公司不顯示本益比。
            if per_value is None:
                price = _num((data.get("PreviousClose") or {}).get("value"))
                earnings = _get(FUND_EARNINGS.format(sym=symbol), timeout=25, tries=2).json()
                rows = (((earnings or {}).get("data") or {})
                        .get("earningsSurpriseTable") or {}).get("rows") or []
                eps_values = [_num(row.get("eps")) for row in rows[:4]]
                if price is not None and len(eps_values) == 4 and all(v is not None for v in eps_values):
                    eps_ttm = sum(eps_values)
                    if eps_ttm > 0:
                        per_value = round(price / eps_ttm, 2)
            out = {"per": per_value, "yield": _num(yld)}
        except Exception:
            pass
        _save_cache(key, out)
        return out

    return _fetch_once(key, fetch, lambda: _load_cache(key, max_age_hours))


def load_valuations(symbols, status_cb=None, workers=8):
    out, done = {}, [0]
    lock = threading.Lock()

    def work(sym):
        value = get_valuation(sym)
        with lock:
            out[sym] = value
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
# ⚠️ 最長級距（1260）必須 <= HIST_DAYS，否則那一級永遠算不出來（見 HIST_DAYS 的註解）。
# ⚠️ **沒有「歷史新高」這一級，而且不該加。** 手上只有 5 年資料，
#    標成「歷史新高」等於宣稱一件我們沒有證據的事 —— 股價完全可能 6 年前更高。
#    台股版有這一級，是因為它有 6 年的 FinMind 資料。兩邊不要互相類比。
NH_TIERS = [("5y", 1260, "5年新高"), ("3y", 756, "3年新高"), ("2y", 504, "2年新高"),
            ("1y", 252, "1年新高"), ("6m", 126, "半年新高"), ("3m", 63, "3個月新高")]
NH_LABEL = {"5y": "5年新高", "3y": "3年新高", "2y": "2年新高", "1y": "1年新高",
            "6m": "半年新高", "3m": "3個月新高", "": "—"}
NH_ORDER = ["5y", "3y", "2y", "1y", "6m", "3m"]


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


# ---------------------------------------------------------------- 名言卡
#
# ⚠️⚠️ **`quotes/` 兩個專案共用同一份內容，新增名言必須兩邊一起加。**
#    來源是台股咖啡館（2026-08-07 複製過來，中英各 4 位作者、68 張卡）。
#    只加一邊的話，兩站的「第 N / 68」編號會對不上，
#    而且使用者在兩站之間切換時會發現內容不一樣 —— 那看起來像其中一站壞了。
#    📌 慣例寫在 `quotes/_如何新增名言.md.txt` 與兩邊的 PROJECT_CONTEXT。
QUOTES_DIR = os.environ.get("QUOTES_DIR") or os.path.join(BASE_DIR, "quotes")


def _load_quotes(lang="zh"):
    """讀名言檔，回傳 ([(作者, 主題, [句子...]), ...], [來源說明...])。

    front-matter：author（顯示名）、full（完整介紹）、
    mode（single＝一句一卡／group＝一主題一卡）。內文用 `## 主題` 分段。
    ⚠️ 中英**檔名必須完全一致**且主題數、句數相同 —— 系統是用「第幾張卡」
       對應翻譯的，數量不同會配到錯的句子（`檢查名言分類.command` 會驗）。
    """
    base = QUOTES_DIR if lang == "zh" else os.path.join(QUOTES_DIR, "en")
    cards, sources = [], []
    if not os.path.isdir(base):
        return cards, sources
    for fn in sorted(os.listdir(base)):
        if not fn.endswith(".md"):
            continue
        try:
            with open(os.path.join(base, fn), "r", encoding="utf-8") as f:
                raw = f.read()
        except Exception:
            continue
        meta, body = {}, raw
        if raw.startswith("---"):
            parts = raw.split("---", 2)
            if len(parts) >= 3:
                for ln in parts[1].strip().split("\n"):
                    if ":" in ln:
                        k, v = ln.split(":", 1)
                        meta[k.strip()] = v.strip()
                body = parts[2]
        author = meta.get("author", fn[:-3])
        mode = meta.get("mode", "single")
        if meta.get("full"):
            sources.append(meta["full"])
        tag, buf = None, []

        def flush():
            if not tag or not buf:
                return
            if mode == "group":
                cards.append((author, tag, list(buf)))
            else:
                for one in buf:
                    cards.append((author, tag, [one]))
        for ln in body.split("\n"):
            t = ln.strip()
            if t.startswith("## "):
                flush()
                tag, buf = t[3:].strip(), []
            elif t:
                buf.append(t)
        flush()
    return cards, sources


QUOTES, QUOTE_SOURCES = _load_quotes("zh")
QUOTES_EN, QUOTE_SOURCES_EN = _load_quotes("en")

# 市場階段 → 適合的名言主題。**key 與 PHASE_UI／MARKET_LIFECYCLE 完全相同**，
# 所以台股那份可以直接沿用（兩站的五個階段名一致）。
REGIME_TAGS = {
    "tailwind": ["上漲怎麼看", "持有贏家", "領導股", "CAN SLIM",
                 "只買突破", "研究歷史"],
    "transition": ["耐心與等待", "操作頻率", "紀律與節制", "等待的重要",
                   "等市場確認", "選擇戰場", "樂觀的代價", "賣出的重要"],
    "riskoff": ["下跌與虧損", "永遠不要攤平", "停損", "情緒管理", "快速停損"],
    "recovery_confirmed": ["趨勢才是真相", "順勢而為", "先勝後戰"],
}
# 不綁盤勢的通用主題。首頁固定會多顯示一張，每天輪替。
GENERIC_TAGS = ["投機者", "確定與隨機", "消息", "供需與市場", "市場的本質", "知己知彼"]


def _quote_set(lang):
    """對應語言的名言卡；英文缺檔時自動回退中文，不會空白。"""
    if lang == "en" and QUOTES_EN:
        return QUOTES_EN, QUOTE_SOURCES_EN
    return QUOTES, QUOTE_SOURCES


def _quote_day_no():
    """用**美東日期**當輪替基準（這個站講的是美股）。

    ⚠️ 不要用 UTC：美東下午還是同一個交易日，UTC 卻已經跳到隔天，
       名言會在盤中換掉 —— 使用者看到的是「早上一句、下午另一句」。
    """
    et = _utcnow() - timedelta(hours=_et_offset_hours(_utcnow()))
    return (et - datetime(2026, 1, 1, tzinfo=timezone.utc)).days


def _pick_by_tags(lang, tags, offset=0):
    """從指定主題挑一張當日名言；主題對不上就回 None。

    ⚠️⚠️ **池子一律用中文名言算索引。** 英文檔的主題是英文（`## Discipline`），
       各自比對會挑到不同索引 —— 切換語言就變成另一則，
       破壞「切語言看到的是同一則的翻譯」這個保證。
    """
    cards, _ = _quote_set(lang)
    if not cards:
        return None
    pool = [i for i, c in enumerate(QUOTES) if c[1] in tags and i < len(cards)]
    if not pool:
        return None
    idx = pool[(_quote_day_no() + offset) % len(pool)]
    author, tag, lines = cards[idx]
    return {"author": author, "tag": tag, "lines": lines,
            "no": idx + 1, "total": len(cards)}


def _daily_quotes(n=2, lang="zh"):
    """全庫每日輪替（最後防線）。同一天固定不變 —— 每次重整都換會顯得很隨便。"""
    cards, _ = _quote_set(lang)
    if not cards:
        return []
    out, total = [], len(cards)
    for i in range(n):
        idx = (_quote_day_no() * n + i) % total
        author, tag, lines = cards[idx]
        out.append({"author": author, "tag": tag, "lines": lines,
                    "no": idx + 1, "total": total})
    return out


def home_quotes(lang="zh", phase=None):
    """首頁兩張卡：**第一張跟著今天的市場階段，第二張每天輪一張通用**。

    ⚠️ 任何一張挑不到都安全降級：階段挑不到（unknown 或主題名打錯）→ 用通用補；
       通用也挑不到 → 退回全庫輪替。**首頁寧可少一張，也不要空白。**
    """
    out = []
    tags = REGIME_TAGS.get(phase or "")
    if tags:
        q = _pick_by_tags(lang, tags)
        if q:
            out.append(q)
    g = _pick_by_tags(lang, GENERIC_TAGS, offset=1 if out else 0)
    if g and (not out or g["no"] != out[0]["no"]):
        out.append(g)
    if len(out) < 2:
        for q in _daily_quotes(2, lang):
            if all(q["no"] != o["no"] for o in out):
                out.append(q)
            if len(out) == 2:
                break
    return out[:2]


# ---------------------------------------------------------------- 均線扣抵法
#
# 與台股版**同一套算法、同樣的函式名**（`_ma_deduction` / `_recent_slope`）——
# 兩邊要改就一起改。差別只有均線組合與資料來源。
#
# 「扣抵」是移動平均的算術性質，不是預測：
#   明日 MA = 今日 MA + (明日收盤 − 扣抵值) / N
#   扣抵值 = N 天前的那一筆收盤（明天會被移出視窗的那根 K 棒）
# 所以**扣抵值比現價低 → 均線必定上揚**，跟明天漲不漲沒有關係。
#
# ⚠️ **台股用 60／120（季線／半年線），美股用 50／150。**
#    50 日線在美股的地位相當於台股季線，150 日線是歐尼爾與 Minervini 的趨勢模板用的那條。
#    直接把 60／120 搬過來會變成「畫面說季線、實際算的是別的東西」。
# ⚠️⚠️ **為什麼是 50／100／150 三條，而不是選一條。**
#    2026-08-07 用 `回測跌破均線.command` 實測納斯達克綜合指數（1971 年以來）。
#    ⚠️⚠️ **那份回測有兩種問法，答案差一個量級：**
#      【A】每次穿越都當獨立事件 → 中位僅 −2%、七到九成在 20 日內收回
#      【B】用循環切段、只取底部前最後一次跌破 → 中位 −15%~−20%
#    **兩個都對，回答的是不同問題。**【B】用了「哪一次是最後一次」這個未來資訊，
#    不是即時訊號的期望值。
#
#    在【B】的定義下，100MA 三個期間都比 150MA 深 1.3~3 個百分點
#    （近 10 年 −19.8% vs −16.8%、近 25 年 −17.4% vs −15.3%、
#      1971 以來 −16.7% vs −15.4%），在【A】的假訊號率也不比 150MA 高。
#    **兩個角度都不輸** —— 這支持首頁市場階段用 100MA 當逆風線（PHASE_SLOW_MA），
#    也支持扣抵法把它納進來。
#
#    而 150MA 仍然要留：找強勢股的 MA_SET 與市場寬度都用它，
#    使用者在別的頁面看到的就是這條。三條都算，計算成本幾乎是零。
#
# 📌 **這一段的第一版寫成「100 與 150 分不出高下」，是因為只做了【A】。**
#    那正是台股 `台股大盤循環回測.md` 標為「已作廢的錯誤算法」的同一個坑。
#    改參數之前先確認你引用的數字回答的是哪一個問題。
#
# 📌 回測另一個重要發現：**單次跌破的假訊號率 71~93%** ——
#    所以扣抵法只回答「均線幾天後會走到這裡」，**不要延伸成買賣訊號**。
DEDUCT_MAS = (50, 100, 150)
# ⚠️⚠️ **這個值必須 >= 最長的均線天數。**
#    盤整情境下，N 日均線要「整個視窗都換成目標價」才會等於目標價 —— 也就是**剛好 N 天**。
#    往後推的天數若小於 N，那條均線的「盤整」那一列就會**永遠顯示「超過 N 個交易日」**，
#    而正確答案其實是算得出來的。使用者會以為那條線追不上，實際上只是我們沒算完。
DEDUCT_MAX_DAYS = max(DEDUCT_MAS)
DEDUCT_SLOPE_LOOKBACK = 20      # 「延續趨勢」用近幾日的實際斜率


def _ma_deduction(closes, target, days_ahead=DEDUCT_MAX_DAYS,
                  daily_change=0.0, periods=DEDUCT_MAS):
    """均線扣抵試算。回傳每條均線的現值、明日扣抵 K 棒、追上目標所需交易日。

    ⚠️ **「追上」要分兩個方向講清楚**：均線在價格下方時是均線往上追；
       在上方時是均線往下貼近。兩者意義完全相反。
    ⚠️ 均線**現在就已經到位**時天數是 0 不是 1 —— 顯示 1 會讓人以為還有一天。
    """
    out = {}
    for n in periods:
        if len(closes) < n:
            out[str(n)] = {"period": n, "ma": None, "error": "not_enough"}
            continue
        window = [float(x) for x in closes[-n:]]
        ma_now = sum(window) / n
        deduct_next = window[0]
        below = ma_now < target
        price = float(target)
        w = list(window)
        days, path, crossed = 0, [], None
        if (below and ma_now >= target) or (not below and ma_now <= target):
            crossed = 0
        for i in range(1, days_ahead + 1 if crossed is None else 1):
            price = price * (1 + daily_change)
            w = w[1:] + [price]
            ma = sum(w) / n
            days = i
            if i <= 30 or i % 5 == 0:
                path.append({"d": i, "ma": round(ma, 2), "price": round(price, 2)})
            if crossed is None and ((below and ma >= price) or (not below and ma <= price)):
                crossed = i
                break
        out[str(n)] = {
            "period": n,
            "ma": round(ma_now, 2),
            "gap_pct": round((target - ma_now) / ma_now * 100, 2) if ma_now else None,
            "deduct_next": round(deduct_next, 2),
            "rising": deduct_next < target,
            "side": "below" if below else "above",
            "days": crossed,
            "days_scanned": days,
            "path": path,
        }
    return out


def _recent_slope(closes, lookback=DEDUCT_SLOPE_LOOKBACK):
    """近 lookback 個交易日的平均每日變動比例。資料不足或算不出來回 0。

    ⚠️ 用頭尾的複合成長率，不是線性迴歸：使用者要的是「照最近的速度走下去」。
    """
    if len(closes) < lookback + 1:
        return 0.0
    a, b = float(closes[-lookback - 1]), float(closes[-1])
    if a <= 0 or b <= 0:
        return 0.0
    return (b / a) ** (1.0 / lookback) - 1.0


# ---------------------------------------------------------------- 風控頁
#
# 資料口徑已於 2026-08-07 用 `檢查資料口徑.command` 實測確認：
#   ・整合行情的成交（AAPL 單日 4,600 萬股，級距對）
#   ・高低價**不含盤前盤後**（70 次跳空只有 6% 被前一日高低涵蓋）
#   ・**只還原拆股、不還原配息**（KO／JNJ／PG 各 274 天重疊，差異 0.000%）
#
# ⚠️⚠️ **停損價是這個站上唯一一個使用者會直接照著下單的數字。**
#    其他欄位算錯，使用者頂多多看兩眼；停損算錯，他會真的把單掛在錯的價位。
#    所以這一區的任何一個數字，寧可顯示「—」也不要顯示可疑的值。
RISK_MAX = 3                    # 最多幾檔（跟台股版一致）
RISK_ATR_PERIOD = 14
RISK_VOL_SESSIONS = 126         # 半年年化波動率
RISK_BETA_SESSIONS = 252        # Beta 用近一年
RISK_OHLC_DAYS = 150            # 抓幾個日曆天的 OHLC（約 100 個交易日，ATR14 綽綽有餘）
RISK_OHLC_TTL_H = 12
RISK_STOP_MULTIPLES = (1.5, 2.0, 3.0)


def _hist_ohlc_nasdaq(symbol):
    """近三個多月的 OHLC。**只給風控頁用，不進 `hist_` 快取。**

    ⚠️ `hist_` 只存 [日期, 收盤價]，是均線／創新高／RS 的唯一來源，
       定義必須穩定。OHLC 另存一份，兩者不要混。
    ⚠️ `todate` 一定要用今天 —— 端點對「結束日在過去」的區間會回空
       （2026-08-07 實測，第一版檢查腳本就是栽在這裡）。
    """
    to = _utcnow()
    frm = to - timedelta(days=RISK_OHLC_DAYS)
    j = _get(NASDAQ_HIST.format(sym=symbol.upper(),
                                frm=frm.strftime("%Y-%m-%d"),
                                to=to.strftime("%Y-%m-%d")), timeout=40, tries=2).json()
    raw = (((j or {}).get("data") or {}).get("tradesTable") or {}).get("rows") or []
    out = []
    for r in raw:
        d = (r.get("date") or "").strip()
        o, h, l, c = (_num(r.get("open")), _num(r.get("high")),
                      _num(r.get("low")), _num(r.get("close")))
        if not d or None in (h, l, c):
            continue
        try:
            mm, dd, yy = d.split("/")
        except ValueError:
            continue
        out.append({"date": "%s-%s-%s" % (yy, mm, dd),
                    "open": o, "high": h, "low": l, "close": c})
    out.sort(key=lambda x: x["date"])
    return out


def get_risk_daily(symbol):
    """逐檔快取 12 小時的 OHLC。抓不到時**不寫空快取**（否則整天都是空的）。"""
    key = "risk_daily_%s.json" % symbol.upper()
    cached = _load_cache(key, RISK_OHLC_TTL_H)
    if cached is not None:
        return cached
    try:
        rows = _hist_ohlc_nasdaq(symbol)
    except Exception:
        rows = []
    if rows:
        _save_cache(key, rows)
    return rows


def _atr(records, period=RISK_ATR_PERIOD):
    """Wilder ATR。records 是依日期排序的 high/low/close 字典串列。

    ⚠️ 真實波幅 = max(當日高低, |高−前收|, |低−前收|)。
       **中間那兩項就是跳空。** 所以「高低價不含盤後」不代表財報跳空被忽略 ——
       跳空會完整反映在隔天的 TR 上，這正是 Wilder 這樣定義的原因。
    """
    trs, prev_close = [], None
    for row in records:
        try:
            high, low, close = float(row["high"]), float(row["low"]), float(row["close"])
        except (KeyError, TypeError, ValueError):
            continue
        tr = high - low if prev_close is None else max(
            high - low, abs(high - prev_close), abs(low - prev_close))
        trs.append(tr)
        prev_close = close
    if len(trs) < period:
        return None
    atr = sum(trs[:period]) / period
    for tr in trs[period:]:
        atr = (atr * (period - 1) + tr) / period
    return atr


def _daily_returns(closes):
    return [(closes[i] / closes[i - 1] - 1)
            for i in range(1, len(closes)) if closes[i - 1]]


def _annual_vol(closes, sessions=RISK_VOL_SESSIONS):
    """年化波動率（%）：日報酬標準差 × √252。資料不足回 None。"""
    if len(closes) < sessions + 1:
        return None
    rs = _daily_returns(closes[-(sessions + 1):])
    if len(rs) < 2:
        return None
    mean = sum(rs) / len(rs)
    var = sum((x - mean) ** 2 for x in rs) / (len(rs) - 1)
    return math.sqrt(var) * math.sqrt(252) * 100


def _beta(dated_closes, idx_map, sessions=RISK_BETA_SESSIONS):
    """對納斯達克綜合指數的 Beta。

    ⚠️ **一定要按日期對齊再算報酬**，不能各自取最後 N 筆。
       個股與指數的資料日期常常差一天（FRED 慢一個交易日），
       各取各的會把不同天的報酬配成一對 —— 算出來的 Beta 看起來正常，卻是錯的。
    """
    if not idx_map:
        return None
    pairs = [(d, c, idx_map[d]) for d, c in dated_closes if d in idx_map and c]
    if len(pairs) < 60:
        return None
    pairs = pairs[-(sessions + 1):]
    sr = _daily_returns([p[1] for p in pairs])
    ir = _daily_returns([p[2] for p in pairs])
    n = min(len(sr), len(ir))
    if n < 30:
        return None
    sr, ir = sr[-n:], ir[-n:]
    im = sum(ir) / n
    sm = sum(sr) / n
    var = sum((x - im) ** 2 for x in ir)
    if var <= 0:
        return None
    cov = sum((sr[i] - sm) * (ir[i] - im) for i in range(n))
    return cov / var


def risk_metrics(symbols):
    """回傳每一檔的風控指標。找不到資料的欄位一律 None，前端顯示「—」。"""
    idx = _load_cache("nasdaq_index.json", 24 * 365) or {}
    uni = {u.get("symbol"): u for u in (_load_cache("universe.json", None) or [])}
    out = []
    for sym in symbols[:RISK_MAX]:
        sym = (sym or "").upper().strip()
        if not sym:
            continue
        hist = get_history(sym) or []
        closes = [c for _d, c in hist]
        ohlc = get_risk_daily(sym)
        atr = _atr(ohlc)
        last = closes[-1] if closes else None
        # ⚠️ ATR 與收盤價要用**同一批資料的最後一天**才對得起來；
        #    OHLC 有抓到就以它為準，因為 ATR 是從它算的。
        if ohlc:
            last = ohlc[-1]["close"]
        mas = {p: _sma(closes, p) for p in MA_SET}
        vol, beta = _annual_vol(closes), _beta(hist, idx)
        u = uni.get(sym) or {}
        out.append({
            "symbol": sym,
            "name": u.get("name") or sym,
            "name_zh": zh_company(sym, u.get("name") or sym),
            "sector": u.get("sector") or "",
            "sector_zh": zh_sector(u.get("sector") or ""),
            "close": round(last, 2) if last else None,
            "as_of": (ohlc[-1]["date"] if ohlc else (hist[-1][0] if hist else None)),
            "atr": round(atr, 2) if atr else None,
            "atr_pct": round(atr / last * 100, 2) if (atr and last) else None,
            "vol": round(vol, 1) if vol else None,
            "align": align_label(mas),
            "beta": round(beta, 2) if beta is not None else None,
            "ma": {str(p): (round(v, 2) if v else None) for p, v in mas.items()},
            "sessions": len(ohlc),
        })
    return out


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


# ---------------------------------------------------------------- 飆股前期結構回溯

def _structure_shape_labels(prices):
    """只用收盤價輪廓做啟發式分類，不冒充 OHLCV 型態確認。"""
    vals = [float(x) for x in prices if x is not None]
    if len(vals) < 30:
        return []
    n, lo = len(vals), min(vals)
    trough = vals.index(lo)
    labels = []
    lows = []
    for i in range(10, n - 10):
        if vals[i] <= lo * 1.10 and vals[i] <= min(vals[i - 10:i + 11]):
            if not lows or i - lows[-1] >= 25:
                lows.append(i)
    if any(max(vals[a:b + 1]) >= max(vals[a], vals[b]) * 1.12
           for a, b in zip(lows, lows[1:])):
        labels.append("多重底")

    recent = vals[-min(120, n):]
    cuts = [recent[:len(recent) // 3],
            recent[len(recent) // 3:2 * len(recent) // 3],
            recent[2 * len(recent) // 3:]]
    amps = [(max(x) / min(x) - 1) for x in cuts if x and min(x) > 0]
    if len(amps) == 3 and amps[0] > amps[1] > amps[2] and amps[2] <= amps[0] * .72:
        labels.append("VCP 波動收縮")

    central = .18 <= trough / max(1, n - 1) <= .78
    if n >= 120 and central:
        labels.append("U 型底")
    if n >= 90 and central:
        tail = vals[-min(35, n // 4):]
        ceiling = max(vals[0], vals[-1])
        handle_dd = min(tail) / ceiling - 1 if ceiling else 0
        if -.20 <= handle_dd <= -.04:
            labels.append("杯柄")
    if n >= 240:
        middle = vals[int(n * .15):max(int(n * .85), int(n * .15) + 1)]
        if middle and min(middle) > 0 and max(middle) / min(middle) - 1 <= .50:
            labels.append("長期橫盤")
    return labels[:3]


def analyze_breakout_structure(rows):
    """辨識前高、至少 20% 回落、三個月整理與近期重回前高。"""
    clean = {}
    for row in rows or []:
        try:
            d, v = str(row[0])[:10], float(row[1])
            datetime.strptime(d, "%Y-%m-%d")
            if v > 0:
                clean[d] = v
        except (TypeError, ValueError, IndexError):
            continue
    points = sorted(clean.items())[-1260:]
    if len(points) < 252:
        return {"available": False, "matched": False,
                "reason": "長期資料不足 1 年", "chart": []}

    # 美股真實單日漲跌可超過 15%，只攔截接近整數比例的疑似未還原拆股。
    split_breaks = _find_split_breaks(points)
    if split_breaks:
        bad, ratio = split_breaks[-1]
        return {"available": False, "matched": False,
                "reason": "收盤價在 %s 有疑似拆股斷層（%s）" % (bad, ratio),
                "chart": []}

    dates = [x[0] for x in points]
    values = [float(x[1]) for x in points]
    n, current = len(values), values[-1]
    recent = {days: (current / values[-days - 1] - 1) * 100
              for days in (20, 40, 60)
              if n > days and values[-days - 1] > 0}
    recent_days, recent_gain = max(recent.items(), key=lambda x: x[1])
    candidates = []
    for i in range(40, n - 60):
        peak = values[i]
        if peak <= 0 or peak < max(values[i - 40:i + 1]) * .995:
            continue
        if current < peak * .90:
            continue
        trough_i = min(range(i + 1, n), key=lambda j: values[j])
        drawdown = (values[trough_i] / peak - 1) * 100
        if drawdown > -20:
            continue
        eligible = max(i + 60, trough_i + 1)
        near_i = next((j for j in range(eligible, n) if values[j] >= peak * .90), None)
        if near_i is None or near_i < n - 120:
            continue
        peak_dt = datetime.strptime(dates[i], "%Y-%m-%d")
        near_dt = datetime.strptime(dates[near_i], "%Y-%m-%d")
        months = (near_dt - peak_dt).days / 30.4375
        if months < 3:
            continue
        breakout_i = next((j for j in range(eligible, n) if values[j] >= peak * .98), None)
        closeness = min(current / peak, peak / current)
        candidates.append((closeness, months, peak, i, trough_i, near_i,
                           breakout_i, drawdown))

    weekly = {}
    for d, v in points:
        dt = datetime.strptime(d, "%Y-%m-%d")
        weekly[(dt.isocalendar()[0], dt.isocalendar()[1])] = [d, round(v, 2)]
    chart = list(weekly.values())
    first_dt = datetime.strptime(dates[0], "%Y-%m-%d")
    last_dt = datetime.strptime(dates[-1], "%Y-%m-%d")
    base = {"available": True, "matched": False,
            "as_of": dates[-1].replace("-", "/"),
            "recent_gain_pct": round(recent_gain, 1),
            "recent_period_days": recent_days, "chart": chart,
            "lookback_years": round((last_dt - first_dt).days / 365.25, 1)}
    if not candidates:
        base["reason"] = "未同時找到「回落 20%、整理 3 個月、近期重回前高」"
        return base

    _close, months, peak, peak_i, trough_i, near_i, breakout_i, drawdown = \
        max(candidates, key=lambda x: (x[0], x[1]))
    end_i = breakout_i if breakout_i is not None else near_i
    base.update({
        "matched": recent_gain > 30,
        "prior_high": round(peak, 2),
        "prior_high_date": dates[peak_i].replace("-", "/"),
        "trough": round(values[trough_i], 2),
        "trough_date": dates[trough_i].replace("-", "/"),
        "max_drawdown_pct": round(drawdown, 1),
        "consolidation_months": max(3, int(round(months))),
        "near_high_date": dates[near_i].replace("-", "/"),
        "breakout_date": (dates[breakout_i][:7].replace("-", "/")
                          if breakout_i is not None else None),
        "post_breakout_gain_pct": round((current / peak - 1) * 100, 1),
        "pattern_labels": _structure_shape_labels(values[peak_i:end_i + 1]),
        "markers": {"peak": dates[peak_i], "trough": dates[trough_i],
                    "breakout": dates[breakout_i] if breakout_i is not None else None},
    })
    if recent_gain <= 30:
        base["reason"] = "前期結構成立，但近 1～3 個月最大漲幅尚未超過 30%"
    return base


def get_breakout_structures(symbols, histories=None, status_cb=None):
    """只分析勾選後的結果股票；使用既有五年 hist 快取，不增加外部請求。"""
    histories, out = histories or {}, {}
    total = len(symbols)
    for i, symbol in enumerate(symbols, 1):
        if status_cb:
            status_cb(i, total)
        rows = histories.get(symbol)
        if rows is None:
            rows = _load_cache("hist_%s.json" % symbol.upper(), None) or []
        out[symbol] = analyze_breakout_structure(rows)
    return out


# ---------------------------------------------------------------- 觀察清單篩選

def screen_watchlist(universe_n=150, ma=50, direction="above", days=1,
                     match="any", align="none", eps_halves=False,
                     valuation=False, structure_history=False, status_cb=None):
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
            "ret20": round((last / closes[-21] - 1) * 100, 2),
            "ret60": round((last / closes[-61] - 1) * 100, 2),
            "ma": round(ma_line[-1], 2),
            "gap": round((last / ma_line[-1] - 1) * 100, 2),
            "align": lab,
            "hit_date": hit_date,
            "new_high": nh,
            "hit_days": hit_days,
            "days": days,
            "mktcap": m.get("mktcap"),
            "eps_yoy": (fund.get(sym) or {}).get("eps_yoy"),
            "eps_halves": (fund.get(sym) or {}).get("eps_halves", []),
            "rev_yoy": (fund.get(sym) or {}).get("rev_yoy"),
            "period": (fund.get(sym) or {}).get("period"),
        })

    if valuation and rows:
        values = load_valuations([r["symbol"] for r in rows], status_cb=status_cb)
        for r in rows:
            value = values.get(r["symbol"], {})
            r["per"] = value.get("per")
            r["yield"] = value.get("yield")

    rows.sort(key=lambda r: r["rank"])
    if structure_history:
        structures = get_breakout_structures(
            [r["symbol"] for r in rows], histories=hist, status_cb=status_cb)
        for row in rows:
            row["structure"] = structures.get(row["symbol"], {})
    rows, qmeta = attach_quotes(rows)      # 只抓結果那幾檔，不是全部 300 檔
    return {"rows": rows, "as_of": as_of, "quote": qmeta,
            "ma_name": MA_NAMES.get(ma, str(ma)),
            "ma_name_zh": MA_NAMES_ZH.get(ma, str(ma))}


def screen_pullback(universe_n=150, ma=50, band=3.0, align="strict_bull",
                    eps_halves=False, valuation=False, structure_history=False,
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
            "ret20": round((last / closes[-21] - 1) * 100, 2),
            "ret60": round((last / closes[-61] - 1) * 100, 2),
            "ma": round(m, 2),
            "gap": round(gap, 2),
            "align": lab,
            "hit_date": h[-1][0],
            "new_high": nh,
            "hit_days": 1,
            "days": 1,
            "mktcap": u.get("mktcap"),
            "eps_yoy": (fund.get(sym) or {}).get("eps_yoy"),
            "eps_halves": (fund.get(sym) or {}).get("eps_halves", []),
            "rev_yoy": (fund.get(sym) or {}).get("rev_yoy"),
            "period": (fund.get(sym) or {}).get("period"),
        })

    if valuation and rows:
        values = load_valuations([r["symbol"] for r in rows], status_cb=status_cb)
        for r in rows:
            value = values.get(r["symbol"], {})
            r["per"] = value.get("per")
            r["yield"] = value.get("yield")

    # 越貼近均線的排越前面（乖離絕對值小 → 拉回得剛剛好）
    rows.sort(key=lambda r: abs(r["gap"]))
    if structure_history:
        structures = get_breakout_structures(
            [r["symbol"] for r in rows], histories=hist, status_cb=status_cb)
        for row in rows:
            row["structure"] = structures.get(row["symbol"], {})
    rows, qmeta = attach_quotes(rows)      # 只抓結果那幾檔，不是全部 300 檔
    return {"rows": rows, "as_of": as_of, "band": band, "quote": qmeta,
            "ma_name": MA_NAMES.get(ma, str(ma)),
            "ma_name_zh": MA_NAMES_ZH.get(ma, str(ma))}


def _std(values):
    """樣本標準差；整理觀察只需要比例，避免為此增加 pandas/numpy 依賴。"""
    if len(values) < 2:
        return 0.0
    avg = sum(values) / len(values)
    return math.sqrt(sum((x - avg) ** 2 for x in values) / (len(values) - 1))


LEV_SYMBOL = "QLD"
LEV_NAME = "ProShares Ultra QQQ"


def get_leverage_monthly(months=24):
    """QLD（2 倍納斯達克100）與納斯達克綜合指數的逐月報酬。

    ⚠️⚠️ **這個檔案沒有 pandas，也不要為了這個功能加。**
    美股版刻意只裝 flask / requests / gunicorn（＋推播用的兩個），
    見 PROJECT_CONTEXT 5.2。第一版我用 pandas 寫，線上直接
    `name 'pd' is not defined` —— 純 Python 做逐月彙總並不難，寫在下面。

    ⚠️⚠️ **選 QLD 不是 SSO**：全站大盤基準是納斯達克綜合指數，不是標普。
    （SSO 是 2 倍標普 500、TQQQ 是 3 倍，都不對應本站。）

    ⚠️ **QLD 追蹤納斯達克100，不是綜合指數** —— 前者非金融前 100 大、
    後者三千多檔。所以「實際倍數」本來就不會乾淨，這不是資料錯誤。
    📌 台股的 00631L 對加權指數也是同一個問題。

    ⚠️⚠️ **2026-08-14 更正**：原本這裡寫「拆股／配息都處理過」，**配息那半是錯的**。
    實測結果：
      ・**拆股 → 已還原**：NVDA 2024-06-03 回傳 115.0，當時實際成交約 1150（10:1 拆股）。
      ・**配息 → 未還原**：AAPL 2023-06-27 回傳 188.06，就是當天實際收盤價。
    對本函式（QLD 逐月績效）影響很小 —— 槓桿 ETF 配息低、期間也只有兩年。
    📌 但**任何長期累計報酬的功能都必須自己處理配息**，否則會系統性偏袒
    低配息的成長股、低估高股息股。見 `長期成長股列表`。
    """
    cached = _load_cache("leverage_monthly_v2.json", 12)   # ⚠️ v2: 新增 years 年度分組
    if cached is not None:
        return cached

    end = _utcnow()
    start = end - timedelta(days=int(365 * (months / 12.0) + 150))
    url = ("https://api.nasdaq.com/api/quote/%s/historical"
           "?assetclass=etf&fromdate=%s&todate=%s&limit=9999"
           % (LEV_SYMBOL, start.strftime("%Y-%m-%d"), end.strftime("%Y-%m-%d")))
    etf_daily = {}
    try:
        r = _get(url)
        rows = ((r.json().get("data") or {}).get("tradesTable", {}) or {}).get("rows", [])
        for row in rows:
            try:
                d = datetime.strptime(row["date"], "%m/%d/%Y").strftime("%Y-%m-%d")
                v = _num(row["close"])
                if v:
                    etf_daily[d] = v
            except Exception:
                continue
    except Exception:
        return {}
    idx_daily = {k: float(v) for k, v in (get_nasdaq_index() or {}).items() if v}
    if not etf_daily or not idx_daily:
        return {}

    def month_end_closes(daily):
        """每月最後一個交易日的收盤 → {"YYYY-MM": close}。純 Python，不用 pandas。"""
        out = {}
        for d in sorted(daily):
            out[d[:7]] = daily[d]        # 後面的日期會覆蓋前面的 → 留下該月最後一筆
        return out

    last = min(max(etf_daily), max(idx_daily))          # 兩邊都有資料的最後一天
    me = month_end_closes({k: v for k, v in etf_daily.items() if k <= last})
    mi = month_end_closes({k: v for k, v in idx_daily.items() if k <= last})
    ms = sorted(set(me) & set(mi))[-(months + 1):]
    if len(ms) < 2:
        return {}

    rows_out = []
    for i in range(1, len(ms)):
        pm, cm = ms[i - 1], ms[i]
        er = me[cm] / me[pm] - 1
        ir = mi[cm] / mi[pm] - 1
        rows_out.append({"m": cm, "etf": round(er * 100, 2), "idx": round(ir * 100, 2),
                         "ratio": (round(er / ir, 2) if abs(ir) > 0.002 else None),
                         "_er": er, "_ir": ir,
                         # ⚠️ 最後一個月幾乎一定沒過完 —— 半個月跟整月放同一欄最容易被誤讀
                         "partial": (cm == last[:7])})
    full = [r for r in rows_out if not r["partial"]]
    if not full:
        return {}

    def cum(rs, key):
        v = 1.0
        for r in rs:
            v *= 1 + r[key]
        return v - 1

    def stdev(vals):
        if len(vals) < 2:
            return 0.0
        m = sum(vals) / len(vals)
        return (sum((x - m) ** 2 for x in vals) / (len(vals) - 1)) ** 0.5

    # ---- 按年度分組：每年一個彙總，月份收在底下 ----
    # ⚠️ 年度彙總只用**完整月份**算。把未完月混進年度報酬，
    #    會讓「今年到目前為止」看起來像一個完整年度，是最容易誤讀的呈現。
    years = []
    for y in sorted({r["m"][:4] for r in rows_out}, reverse=True):
        gm = [r for r in rows_out if r["m"].startswith(y)]
        gf = [r for r in gm if not r["partial"]]
        ye = cum(gf, "_er") if gf else None
        yi = cum(gf, "_ir") if gf else None
        years.append({
            "y": int(y), "months": [{k: v for k, v in r.items() if not k.startswith("_")}
                                    for r in gm],
            "etf": round(ye * 100, 2) if ye is not None else None,
            "idx": round(yi * 100, 2) if yi is not None else None,
            "ratio": (round(ye / yi, 2) if (ye is not None and yi and abs(yi) > 0.002) else None),
            "n": len(gf),
            "partial": len(gf) < 12,      # 不足 12 個完整月 → 不要跟完整年度直接比
        })

    ce, ci = cum(full, "_er"), cum(full, "_ir")
    ve = stdev([r["_er"] for r in full])
    vi = stdev([r["_ir"] for r in full])
    out = {"rows": [{k: v for k, v in r.items() if not k.startswith("_")} for r in rows_out],
           "years": years, "code": LEV_SYMBOL, "name": LEV_NAME, "data_date": last,
           "cum_etf": round(ce * 100, 1), "cum_idx": round(ci * 100, 1),
           "cum_ratio": round(ce / ci, 2) if ci else None,
           "up": sum(1 for r in full if r["_er"] > 0),
           "down": sum(1 for r in full if r["_er"] <= 0),
           "best": round(max(r["_er"] for r in full) * 100, 2),
           "worst": round(min(r["_er"] for r in full) * 100, 2),
           "vol_etf": round(ve * 100, 2), "vol_idx": round(vi * 100, 2),
           "months": len(full)}
    _save_cache("leverage_monthly_v2.json", out)
    return out



# ⚠️⚠️ 2026-08-14 事故：這兩個常數原本緊鄰 `screen_consolidation`，
#      刪除強勢股整理功能時被一起刪掉，但 5 處使用點還在 →
#      每次按 RS 篩選都 NameError → 500 HTML → 前端只顯示
#      「SyntaxError: Unexpected token '<'」，完全看不出真正原因。
#      📌 教訓：刪功能後要 grep 被刪區塊裡的**每個大寫常數**，確認沒有別處在用。
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


def screen_pro_rs(period=60, threshold=90, structure_history=False, status_cb=None):
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
    if structure_history:
        structures = get_breakout_structures(
            [r["symbol"] for r in rows], status_cb=status_cb)
        for row in rows:
            row["structure"] = structures.get(row["symbol"], {})
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
MARKET_PHASE_MAS = (5, 10, 20, 60, 120)
PHASE_GAP_PCT = 5.0
PHASE_RISKOFF_PCT = 3.0
PHASE_RECOVERY_PCT = 4.0
PHASE_CONFIRM_DAYS = 3

# 首頁折線圖保留 5 年（約 1,260 個交易日），與 `HIST_DAYS` 現在同長。
# ⚠️ 種子檔仍然要留著：新上市股票與剛加入股票池的個股不會有完整 5 年，
#    而且種子是「當時的成分股」算出來的，不是今天回算的。
# 較早的區段由隨程式部署的彙總種子檔提供，之後每日預抓用現行資料覆蓋／追加。
# ⚠️ 種子檔只有每天一個百分比，不會把 300 檔長歷史帶進正式環境。
BREADTH_KEEP = 5 * 252
BREADTH_SEED_FILE = os.path.join(BASE_DIR, "breadth_5y_seed.json")
MARKET_COUNT_KEEP = 3 * 252
MARKET_COUNT_CACHE = "market_count_3y.json"
MARKET_INDEX_KEEP = 3 * 252       # 首頁大盤折線圖：近三年納斯達克綜合指數

# 歷史寬度以今日前 300 大回算，仍有存活者偏誤；它只描述市場參與度，
# 不參與首頁四階段判斷，門檻應保守解讀。

# ---- 長期成長股列表 ----------------------------------------------------
# ⚠️⚠️ 這份資料**不在線上計算**，由本機 `研究/腳本/長期成長股列表.py` 算好、
#      隨程式一起部署。原因有兩個：
#        ① 線上沒有 `cache/long_term/`（300 檔十年報價，營運快取只留 1260 筆）。
#        ② 十年報酬變動極慢，每天重算沒有意義。
#      📌 所以更新流程是：本機重跑腳本 → `growth_seed.json` 更新 → 部署。
#      **忘了重跑腳本，網站顯示的就是舊數字**，所以頁面一定要顯示 `as_of`。
GROWTH_SEED_FILE = os.path.join(BASE_DIR, "growth_seed.json")
_GROWTH_CACHE = None


def get_growth():
    """讀取長期成長股種子檔。⚠️ 純讀檔 —— 不連網、不計算、不寫入。

    自我檢查：這個函式裡不應該出現 `requests.get`（見鐵律）。
    """
    global _GROWTH_CACHE
    if _GROWTH_CACHE is None:
        try:
            with open(GROWTH_SEED_FILE, encoding="utf-8") as f:
                _GROWTH_CACHE = json.load(f)
        except Exception as exc:
            # ⚠️ 不要回空清單假裝沒事 —— 那會讓頁面顯示「查無資料」，
            #    看起來像正常結果，實際上是檔案沒部署上去。
            _GROWTH_CACHE = {"error": "找不到 growth_seed.json（%s）"
                                      % type(exc).__name__}
    return _GROWTH_CACHE


NASDAQ_FRED = "https://fred.stlouisfed.org/graph/fredgraph.csv?id=NASDAQCOM"
MACRO_CACHE_FILE = "us_rate_inflation_v6.json"   # v6: 日債改用每日檔，並納入每小時新鮮度檢查
TREASURY_XML = "https://home.treasury.gov/resource-center/data-chart-center/interest-rates/pages/xml"
JGB_DAILY_CSV = "https://www.mof.go.jp/english/policy/jgbs/reference/interest_rate/jgbcme.csv"
JGB_HISTORY_CSV = "https://www.mof.go.jp/english/policy/jgbs/reference/interest_rate/historical/jgbcme_all.csv"
FED_POLICY_CACHE_FILE = "fed_treasury_policy_v1.json"
FRED_CSV = "https://fred.stlouisfed.org/graph/fredgraph.csv"
NYFED_EFFR_API = "https://markets.newyorkfed.org/api/rates/unsecured/effr/last/30.json"
FISCAL_DATA_API = "https://api.fiscaldata.treasury.gov/services/api/fiscal_service"
FOMC_CALENDAR_URL = "https://www.federalreserve.gov/monetarypolicy/fomccalendars.htm"
FED_POLICY_REFRESH_HOURS = 1
MACRO_REFRESH_HOURS = 1
MAX_BOND_LAG_DAYS = 1
HOLIDAY_CALENDAR_SPEC = {"us": "US+GoodFriday", "jp": "JP"}
QUALITY_STATUS_ZH = {
    "fresh": "資料最新", "pending": "尚待今日公布", "lag1": "落後一個交易日",
    "failed": "更新失敗，沿用舊資料", "overdue": "資料落後超過允許天數",
}
UPDATE_HISTORY_FILE = "update_history_v1.json"
UPDATE_HISTORY_LIMIT = 30
_MACRO_REFRESH_LOCK = threading.Lock()
_UPDATE_HISTORY_LOCK = threading.Lock()
MACRO_STATE = {"enabled": False, "last_run": "—", "last_result": "—",
               "latest_us_date": "—", "latest_jp_date": "—",
               "fed_policy_date": "—", "treasury_action_date": "—"}
# ⚠️ 新增欄位一定要換快取檔名。沿用舊檔會讓新那一格永遠讀到沒有它的舊快取，
#    畫面上少一列、卻不會報錯 —— 這是 5.5「看起來正常才最危險」的同一類。


_MARKET_HOLIDAY_CACHE = {}


def _record_update(source, latest_date, outcome, started, detail=""):
    """將最近 30 次外部資料抓取結果保存到持久化快取，供診斷頁追查。"""
    labels = {"success": "成功", "source_not_published": "來源未公布",
              "parse_failed": "解析失敗"}
    record = {
        "executed_at": _utcnow().strftime("%Y-%m-%d %H:%M:%S UTC"),
        "source": source,
        "latest_date": latest_date or "—",
        "outcome": outcome,
        "result": labels.get(outcome, outcome),
        "duration_sec": round(max(0.0, time.perf_counter() - started), 2),
    }
    if detail:
        record["detail"] = str(detail)[:160]
    with _UPDATE_HISTORY_LOCK:
        history = _load_cache(UPDATE_HISTORY_FILE, None) or []
        if not isinstance(history, list):
            history = []
        history.append(record)
        _save_cache(UPDATE_HISTORY_FILE, history[-UPDATE_HISTORY_LIMIT:])


def _source_outcome(latest_date, market):
    if not latest_date:
        return "parse_failed"
    return ("success" if _business_days_behind(latest_date, market=market) <= MAX_BOND_LAG_DAYS
            else "source_not_published")


def _easter_sunday(year):
    """Meeus/Jones/Butcher 演算法；用來補美國債市休市的 Good Friday。"""
    a, b, c = year % 19, year // 100, year % 100
    d, e = b // 4, b % 4
    f, g = (b + 8) // 25, (b - (b + 8) // 25 + 1) // 3
    h = (19 * a + b - d - g + 15) % 30
    i, k = c // 4, c % 4
    l = (32 + 2 * e + 2 * i - h - k) % 7
    m = (a + 11 * h + 22 * l) // 451
    month = (h + l - 7 * m + 114) // 31
    day = (h + l - 7 * m + 114) % 31 + 1
    return datetime(year, month, day).date()


def _market_holidays(market, years):
    """各市場官方假日；美債另補 Good Friday 休市。"""
    key = (market or "weekday", tuple(sorted(set(years))))
    if key in _MARKET_HOLIDAY_CACHE:
        return _MARKET_HOLIDAY_CACHE[key]
    if market not in ("tw", "us", "jp"):
        result = set()
    else:
        country = {"tw": "TW", "us": "US", "jp": "JP"}[market]
        result = set(holidays.country_holidays(country, years=key[1]).keys())
        if market == "us":
            result.update(_easter_sunday(year) - timedelta(days=2) for year in key[1])
    _MARKET_HOLIDAY_CACHE[key] = result
    return result


def _business_days_behind(date_text, today=None, market=None):
    """資料日期落後幾個該市場交易日；排除週末與當地休市日。"""
    try:
        current = datetime.strptime(str(date_text)[:10], "%Y-%m-%d").date()
    except (TypeError, ValueError):
        return 999
    if today is None:
        utc = _utcnow()
        if market == "jp":
            today = (utc + timedelta(hours=9)).date()
        elif market == "tw":
            today = (utc + timedelta(hours=8)).date()
        else:
            today = (utc - timedelta(hours=_et_offset_hours(utc))).date()
    closed = _market_holidays(market, range(current.year, today.year + 1))
    behind = 0
    while current < today:
        current += timedelta(days=1)
        if current.weekday() < 5 and current not in closed:
            behind += 1
    return behind


def _macro_bonds_are_current(data):
    """美國與日本 2Y／10Y／30Y 都不得落後超過一個平日。"""
    items = {it.get("key"): it for it in (data or {}).get("items", [])}
    for market, keys in (("us", ("us2y", "us10y", "us30y")),
                         ("jp", ("jp2y", "jp10y", "jp30y"))):
        if any(key not in items for key in keys):
            return False
        if (max(_business_days_behind(items[key].get("date"), market=market) for key in keys)
                > MAX_BOND_LAG_DAYS):
            return False
    return True


def _macro_refresh_due(data):
    """已追上時每天更新；仍落後或抓取失敗時，每小時重試。"""
    if not data:
        return True
    fetched = data.get("fetched_at")
    try:
        fetched_dt = datetime.strptime(fetched, "%Y-%m-%d %H:%M UTC").replace(tzinfo=timezone.utc)
        age = _utcnow() - fetched_dt
    except (TypeError, ValueError):
        return True
    hours = 24 if _macro_bonds_are_current(data) else MACRO_REFRESH_HOURS
    return age.total_seconds() >= hours * 3600


def _fred_series_raw(series_id, years=3):
    """FRED 官方 CSV；回傳已去除缺值的 (日期, 數值) 序列。"""
    start = (_utcnow() - timedelta(days=366 * years + 14)).strftime("%Y-%m-%d")
    r = requests.get(FRED_CSV, params={"id": series_id, "cosd": start},
                     headers=HEADERS, timeout=25)
    r.raise_for_status()
    rows = []
    for item in csv.DictReader(r.text.splitlines()):
        raw = str(item.get(series_id) or "").strip()
        if not raw or raw in (".", "NA"):
            continue
        try:
            rows.append((str(item.get("observation_date") or "")[:10], float(raw)))
        except (TypeError, ValueError):
            continue
    return [row for row in rows if len(row[0]) == 10]


def _fred_policy_series_raw():
    """一次下載政策序列 ZIP，避免同時對 FRED 發出九個請求而被節流。"""
    import zipfile
    ids = ("DFF", "DFEDTARL", "DFEDTARU", "IORB", "RRPONTSYD", "RPONTSYD",
           "WALCL", "TREAST", "WSHOMCB")
    start = (_utcnow() - timedelta(days=366 * 3 + 14)).strftime("%Y-%m-%d")
    # FRED 的批次 ZIP 對瀏覽器型 User-Agent 偶爾長時間掛住；官方下載端點用
    # 簡單的資料客戶端標頭反而穩定，且只需一個請求。
    r = requests.get(FRED_CSV, params={"id": ",".join(ids), "cosd": start},
                     headers={"User-Agent": "curl/8.7.1", "Accept": "*/*"}, timeout=45)
    r.raise_for_status()
    output = {key: [] for key in ids}
    with zipfile.ZipFile(io.BytesIO(r.content)) as archive:
        for name in archive.namelist():
            if not name.lower().endswith(".csv"):
                continue
            text = archive.read(name).decode("utf-8-sig", errors="replace")
            for item in csv.DictReader(text.splitlines()):
                date_text = str(item.get("observation_date") or "")[:10]
                if len(date_text) != 10:
                    continue
                for key in ids:
                    raw = str(item.get(key) or "").strip()
                    if not raw or raw in (".", "NA"):
                        continue
                    try:
                        output[key].append((date_text, float(raw)))
                    except ValueError:
                        continue
    return output


def _fiscal_tga_raw():
    """Daily Treasury Statement 的 TGA 收盤水位，單位百萬美元。

    Fiscal Data 目前把這一列的數值放在 open_today_bal；account_type 已明確標示
    Closing Balance，因此依官方欄位內容取值，避免誤拿整張表其他帳戶。
    """
    r = requests.get(
        FISCAL_DATA_API + "/v1/accounting/dts/operating_cash_balance",
        params={
            "filter": "account_type:eq:Treasury General Account (TGA) Closing Balance",
            "sort": "-record_date", "page[size]": 100,
        }, headers=HEADERS, timeout=25)
    r.raise_for_status()
    rows = []
    for item in r.json().get("data", []):
        raw = item.get("close_today_bal")
        if raw in (None, "", "null"):
            raw = item.get("open_today_bal")
        try:
            rows.append((str(item.get("record_date") or "")[:10], float(raw)))
        except (TypeError, ValueError):
            continue
    return sorted(set(rows))


def _nyfed_effr_raw():
    """紐約聯準銀行每日 EFFR；比 FRED 轉載通常早一個資料日。"""
    r = requests.get(NYFED_EFFR_API, headers=HEADERS, timeout=25)
    r.raise_for_status()
    rows = []
    for item in r.json().get("refRates", []):
        try:
            rows.append((str(item.get("effectiveDate") or "")[:10],
                         float(item.get("percentRate"))))
        except (TypeError, ValueError):
            continue
    return sorted(set(rows))


def _fiscal_auctions_raw():
    """未來 14 日美國國債標售；只讀官方已公告資料。"""
    et_today = (_utcnow() - timedelta(hours=_et_offset_hours(_utcnow()))).date()
    end = et_today + timedelta(days=14)
    fields = ("record_date,cusip,security_type,security_term,auction_date,issue_date,"
              "offering_amt,total_accepted,bid_to_cover_ratio,high_yield")
    r = requests.get(
        FISCAL_DATA_API + "/v1/accounting/od/auctions_query",
        params={"fields": fields,
                "filter": "auction_date:gte:%s,auction_date:lte:%s" % (et_today, end),
                "sort": "auction_date", "page[size]": 100},
        headers=HEADERS, timeout=25)
    r.raise_for_status()
    seen, rows = set(), []
    for item in r.json().get("data", []):
        key = (item.get("cusip"), item.get("auction_date"))
        if key in seen:
            continue
        seen.add(key)
        try:
            amount = float(item.get("offering_amt") or 0) / 1e9
        except (TypeError, ValueError):
            amount = 0
        rows.append({"auction_date": str(item.get("auction_date") or "")[:10],
                     "issue_date": str(item.get("issue_date") or "")[:10],
                     "type": str(item.get("security_type") or ""),
                     "term": str(item.get("security_term") or ""),
                     "offering_bn": round(amount, 1)})
    return rows


def _fomc_calendar_raw():
    """由聯準會官方行事曆找下一場已排定 FOMC 會議。"""
    import html as _html
    r = requests.get(FOMC_CALENDAR_URL, headers=HEADERS, timeout=25)
    r.raise_for_status()
    body = r.text
    et_today = (_utcnow() - timedelta(hours=_et_offset_hours(_utcnow()))).date()
    months = {name: i for i, name in enumerate(
        ("January", "February", "March", "April", "May", "June",
         "July", "August", "September", "October", "November", "December"), 1)}
    meetings = []
    for year in (et_today.year, et_today.year + 1):
        marker = re.search(r">%d FOMC Meetings<" % year, body)
        if not marker:
            continue
        block = body[marker.start():]
        nxt = re.search(r">%d FOMC Meetings<" % (year - 1), block[1:])
        if nxt:
            block = block[:nxt.start() + 1]
        for chunk in re.split(r'row fomc-meeting[^>]*>', block)[1:]:
            month_m = re.search(r'fomc-meeting__month[^>]*>\s*<strong>([^<]+)', chunk)
            date_m = re.search(r'fomc-meeting__date[^>]*>(.*?)</div>', chunk, re.S)
            if not month_m or not date_m:
                continue
            month = months.get(_html.unescape(month_m.group(1)).strip())
            days = re.findall(r"\d{1,2}", re.sub(r"<[^>]+>", "", date_m.group(1)))
            if not month or not days:
                continue
            try:
                start_day, end_day = int(days[0]), int(days[-1])
                start_date = datetime(year, month, start_day).date()
                decision_date = datetime(year, month, end_day).date()
            except ValueError:
                continue
            meetings.append({"start_date": str(start_date), "decision_date": str(decision_date),
                             "label": "%s %s" % (month_m.group(1).strip(),
                                                   re.sub(r"<[^>]+>", "", date_m.group(1)).strip())})
    return next((row for row in sorted(meetings, key=lambda x: x["decision_date"])
                 if row["decision_date"] >= str(et_today)), {})


def _series_change(rows, periods):
    if len(rows) <= periods:
        return None
    return round(rows[-1][1] - rows[-1 - periods][1], 3)


def _fed_policy_refresh_due(data):
    if not data:
        return True
    try:
        fetched = datetime.strptime(data.get("fetched_at"), "%Y-%m-%d %H:%M UTC").replace(tzinfo=timezone.utc)
        return (_utcnow() - fetched).total_seconds() >= FED_POLICY_REFRESH_HOURS * 3600
    except (TypeError, ValueError):
        return True


def _fed_treasury_policy_data(force=False):
    """首頁用聯準會與財政部快照。只在背景排程更新，首頁本身不連網。"""
    old = _load_cache(FED_POLICY_CACHE_FILE, None) or {}
    if not force and not _fed_policy_refresh_due(old):
        return old
    started = time.perf_counter()
    series = {}
    errors = []
    with ThreadPoolExecutor(max_workers=5) as ex:
        fred_future = ex.submit(_fred_policy_series_raw)
        effr_future = ex.submit(_nyfed_effr_raw)
        tga_future = ex.submit(_fiscal_tga_raw)
        auction_future = ex.submit(_fiscal_auctions_raw)
        fomc_future = ex.submit(_fomc_calendar_raw)
        try:
            series = fred_future.result(timeout=55)
        except Exception as exc:
            errors.append("FRED:%s" % type(exc).__name__)
        try:
            effr = effr_future.result(timeout=35)
            if effr and (not series.get("DFF") or effr[-1][0] >= series["DFF"][-1][0]):
                series["DFF"] = effr
        except Exception:
            pass  # FRED DFF 是備援；NY Fed 暫時失敗不讓整張政策卡變成失敗。
        try:
            tga = tga_future.result(timeout=35)
        except Exception as exc:
            tga, errors = [], errors + ["TGA:%s" % type(exc).__name__]
        try:
            auctions = auction_future.result(timeout=35)
        except Exception as exc:
            auctions, errors = [], errors + ["Auctions:%s" % type(exc).__name__]
        try:
            fomc = fomc_future.result(timeout=35)
        except Exception as exc:
            fomc, errors = {}, errors + ["FOMC:%s" % type(exc).__name__]

    def latest(key):
        rows = series.get(key) or []
        return ({"date": rows[-1][0], "value": rows[-1][1]} if rows else {})

    policy = {key.lower(): latest(key) for key in ("DFF", "DFEDTARL", "DFEDTARU", "IORB")}
    liquidity = {
        "on_rrp": {**latest("RRPONTSYD"), "change_20": _series_change(series.get("RRPONTSYD", []), 20)},
        "repo": {**latest("RPONTSYD"), "change_20": _series_change(series.get("RPONTSYD", []), 20)},
    }
    balance = {}
    for key, name in (("WALCL", "total_assets"), ("TREAST", "treasury_holdings"),
                      ("WSHOMCB", "mbs_holdings")):
        balance[name] = {**latest(key), "change_4w": _series_change(series.get(key, []), 4),
                         "change_13w": _series_change(series.get(key, []), 13)}
    treasury = {
        "tga": ({"date": tga[-1][0], "value": tga[-1][1],
                 "change_20": _series_change(tga, min(20, max(1, len(tga) - 1)))} if tga else {}),
        "auctions": auctions,
        "next_7d_offering_bn": round(sum(row["offering_bn"] for row in auctions
            if row.get("auction_date") <= str(((_utcnow() - timedelta(hours=_et_offset_hours(_utcnow()))).date()
                                               + timedelta(days=7)))), 1),
    }
    fresh_dates = [x.get("date") for x in (policy.get("dff"), liquidity.get("on_rrp"), treasury.get("tga"))
                   if x and x.get("date")]
    data = {"policy": policy, "liquidity": liquidity, "balance_sheet": balance,
            "treasury": treasury, "next_fomc": fomc,
            "as_of": max(fresh_dates) if fresh_dates else "",
            "fetched_at": _utcnow().strftime("%Y-%m-%d %H:%M UTC"), "errors": errors}
    # 部分來源失敗時保留前次完整子區塊；不能把正常畫面倒退成空白。
    def has_observation(value):
        if isinstance(value, dict):
            return (value.get("value") is not None or value.get("date") or value.get("decision_date") or
                    any(has_observation(v) for v in value.values()))
        if isinstance(value, list):
            return bool(value)
        return False
    for key in ("policy", "liquidity", "balance_sheet", "treasury", "next_fomc"):
        if not has_observation(data.get(key)) and old.get(key):
            data[key] = old[key]
    if any((data.get("policy"), data.get("liquidity"), data.get("balance_sheet"), data.get("treasury"))):
        _save_cache(FED_POLICY_CACHE_FILE, data)
    outcome = "success" if not errors else ("parse_failed" if not old else "source_not_published")
    _record_update("聯準會 FRED＋美國財政部 Fiscal Data", data.get("as_of"), outcome,
                   started, ", ".join(errors))
    return data or old


def _treasury_yields_raw():
    """美國財政部近三年 Daily Treasury Par Yield Curve Rates。"""
    import xml.etree.ElementTree as ET
    rows = []
    year = datetime.utcnow().year
    for target_year in range(year - 3, year + 1):
        r = requests.get(
            TREASURY_XML,
            params={"data": "daily_treasury_yield_curve", "field_tdr_date_value": target_year},
            headers=HEADERS, timeout=30,
        )
        r.raise_for_status()
        root = ET.fromstring(r.content)
        for entry in root.findall("{http://www.w3.org/2005/Atom}entry"):
            values = {node.tag.split("}")[-1]: (node.text or "").strip()
                      for node in entry.iter()}
            try:
                rows.append((values["NEW_DATE"][:10], float(values["BC_2YEAR"]),
                             float(values["BC_10YEAR"]), float(values["BC_30YEAR"])))
            except (KeyError, TypeError, ValueError):
                continue
    rows.sort()
    cutoff = (datetime.utcnow() - timedelta(days=365 * 3 + 10)).strftime("%Y-%m-%d")
    return [row for row in rows if row[0] >= cutoff]


def _treasury_yields():
    started = time.perf_counter()
    try:
        rows = _treasury_yields_raw()
        latest = rows[-1][0] if rows else ""
        _record_update("美國財政部 Daily Treasury XML", latest,
                       _source_outcome(latest, "us"), started)
        return rows
    except Exception as exc:
        _record_update("美國財政部 Daily Treasury XML", "", "parse_failed", started, exc)
        raise


def _jgb_yields_raw():
    """合併日本財務省歷史檔與當月每日檔，避免月底檔造成整月延遲。"""
    cutoff = (datetime.utcnow() - timedelta(days=365 * 3 + 10)).strftime("%Y-%m-%d")
    merged = {}
    errors = []
    for url, bust_cache in ((JGB_HISTORY_CSV, False), (JGB_DAILY_CSV, True)):
        try:
            params = {"_": int(time.time() // 3600)} if bust_cache else None
            r = requests.get(url, params=params,
                             headers={**HEADERS, "Cache-Control": "no-cache"}, timeout=30)
            r.raise_for_status()
            try:
                text = r.content.decode("utf-8-sig")
            except UnicodeDecodeError:
                text = r.content.decode("cp932", errors="replace")
            reader = csv.DictReader(text.splitlines()[1:])
            for item in reader:
                try:
                    date = datetime.strptime((item.get("Date") or "").strip(), "%Y/%m/%d").strftime("%Y-%m-%d")
                    row = (date, float(item["2Y"]), float(item["10Y"]), float(item["30Y"]))
                except (KeyError, TypeError, ValueError):
                    continue
                if date >= cutoff:
                    merged[date] = row
        except Exception as exc:
            errors.append(exc)
    if not merged and errors:
        raise errors[-1]
    return [merged[date] for date in sorted(merged)]


def _jgb_yields():
    started = time.perf_counter()
    try:
        rows = _jgb_yields_raw()
        latest = rows[-1][0] if rows else ""
        _record_update("日本財務省 JGB 每日檔＋歷史檔", latest,
                       _source_outcome(latest, "jp"), started)
        return rows
    except Exception as exc:
        _record_update("日本財務省 JGB 每日檔＋歷史檔", "", "parse_failed", started, exc)
        raise


def _yield_analysis(treasury):
    history = [{"date": r[0], "us2y": r[1], "us10y": r[2], "us30y": r[3]} for r in treasury]
    if len(history) < 21:
        return history, []
    findings = []
    labels = {"us2y": "2Y", "us10y": "10Y", "us30y": "30Y"}
    for key in labels:
        values = [r[key] for r in history]
        recent, previous = values[-1] - values[-11], values[-11] - values[-21]
        if recent * previous < 0 and abs(recent - previous) >= .12:
            findings.append({"level": "watch", "text": "%s 趨勢反轉：近 10 個交易日轉為%s。" % (labels[key], "上行" if recent > 0 else "下行")})
        if key == "us30y" and len(values) >= 6 and abs(values[-1] - values[-6]) >= .20:
            move = (values[-1] - values[-6]) * 100
            findings.append({"level": "alert", "text": "30Y 五個交易日%s %.0f bp，長端利率變動快速。" % ("上升" if move > 0 else "下降", abs(move))})
    for key in ("us10y", "us30y"):
        values = sorted(r[key] for r in history[:-1])
        lo, hi = values[max(0, int(len(values)*.2)-1)], values[min(len(values)-1, int(len(values)*.8))]
        current = history[-1][key]
        if current > hi:
            findings.append({"level": "alert", "text": "%s %.2f%% 突破近三年關鍵高檔區 %.2f%%。" % (labels[key], current, hi)})
        elif current < lo:
            findings.append({"level": "alert", "text": "%s %.2f%% 跌破近三年關鍵低檔區 %.2f%%。" % (labels[key], current, lo)})
    for name, long_key, short_key in (("10Y－2Y", "us10y", "us2y"), ("30Y－10Y", "us30y", "us10y")):
        current = (history[-1][long_key] - history[-1][short_key]) * 100
        old = (history[-21][long_key] - history[-21][short_key]) * 100
        change = current - old
        if current * old < 0:
            findings.append({"level": "alert", "text": "%s 利差跨越零軸：曲線由%s轉為%s。" % (name, "正斜率" if old > 0 else "倒掛", "正斜率" if current > 0 else "倒掛")})
        elif abs(change) >= 25:
            findings.append({"level": "watch", "text": "%s 近 20 個交易日%s %.0f bp，曲線明顯%s。" % (name, "擴大" if change > 0 else "縮小", abs(change), "陡峭化" if change > 0 else "平坦化／加深倒掛")})
    if not findings:
        findings.append({"level": "normal", "text": "目前未出現設定門檻內的重大反轉、區間突破或曲線急變。"})
    return history, findings[:6]


def _bls_cpi_series():
    """BLS 經季節調整全城市 CPI（CUSR0000SA0），涵蓋至少最近十年。"""
    year = datetime.utcnow().year
    ranges = ((year - 11, year - 6), (year - 5, year))
    rows = {}
    for start, end in ranges:
        r = requests.get(
            "https://api.bls.gov/publicAPI/v2/timeseries/data/CUSR0000SA0",
            params={"startyear": start, "endyear": end}, headers=HEADERS, timeout=25,
        )
        r.raise_for_status()
        payload = r.json()
        if payload.get("status") != "REQUEST_SUCCEEDED":
            continue
        for series in payload.get("Results", {}).get("series", []):
            for item in series.get("data", []):
                period = str(item.get("period") or "")
                if not re.fullmatch(r"M\d{2}", period) or period == "M13":
                    continue
                try:
                    date = "%s-%s-01" % (item["year"], period[1:])
                    rows[date] = float(item["value"])
                except (KeyError, TypeError, ValueError):
                    continue
    return sorted(rows.items())


def _cached_bls_cpi_series():
    """共用 BLS CPI 快取，避免總經頁與績效比較重複請求 BLS。"""
    cached = _load_cache("us_cpi_index_v1.json", 24)
    if cached is not None:
        return [(str(date), float(value)) for date, value in cached]
    rows = _bls_cpi_series()
    if rows:
        _save_cache("us_cpi_index_v1.json", rows)
    return rows


def _us_cpi_for_years(years):
    """各年度 CPI：12 月對前一年 12 月；未完年度用最新月份。"""
    rows = _cached_bls_cpi_series()
    by_date = {date: value for date, value in rows}
    answer = {}
    for year in years:
        candidates = [(date, value) for date, value in rows
                      if date.startswith("%04d-" % year)]
        base = by_date.get("%04d-12-01" % (year - 1))
        if not candidates or not base:
            continue
        date, value = candidates[-1]
        month = int(date[5:7])
        answer[str(year)] = {
            "value": round((value / base - 1) * 100, 2),
            "period": date[:7],
            "full_year": month == 12,
        }
    return answer


def _us_rate_inflation_data(force=False):
    """美日 2Y／10Y／30Y 公債、三年走勢與美國累積 CPI。"""
    previous_data = _load_cache(MACRO_CACHE_FILE, None)
    if not force and previous_data is not None and not _macro_refresh_due(previous_data):
        return previous_data

    now = datetime.utcnow()
    with ThreadPoolExecutor(max_workers=3) as ex:
        treasury_future = ex.submit(_treasury_yields)
        jgb_future = ex.submit(_jgb_yields)
        cpi_future = ex.submit(_cached_bls_cpi_series)
        try:
            treasury = treasury_future.result(timeout=40)
        except Exception:
            treasury = []
        try:
            jgb = jgb_future.result(timeout=40)
        except Exception:
            jgb = []
        try:
            cpi = cpi_future.result(timeout=60)
        except Exception:
            cpi = []

    items = []
    if treasury:
        date, value2, value10, value30 = treasury[-1]
        previous = treasury[-2] if len(treasury) > 1 else None
        for key, label, value, col in (("us2y", "美國 2 年期公債", value2, 1),
                                       ("us10y", "美國 10 年期公債", value10, 2),
                                       ("us30y", "美國 30 年期公債", value30, 3)):
            item = {"key": key, "label": label, "unit": "%",
                    "value": round(value, 2), "date": date}
            if previous:
                item["chg"] = round(value - previous[col], 2)
            items.append(item)

    if jgb:
        date, value2, value10, value30 = jgb[-1]
        previous = jgb[-2] if len(jgb) > 1 else None
        for key, label, value, col in (("jp2y", "日本 2 年期公債", value2, 1),
                                       ("jp10y", "日本 10 年期公債", value10, 2),
                                       ("jp30y", "日本 30 年期公債", value30, 3)):
            item = {"key": key, "label": label, "unit": "%",
                    "value": round(value, 2), "date": date}
            if previous:
                item["chg"] = round(value - previous[col], 2)
            items.append(item)

    if cpi:
        latest_date, latest_value = cpi[-1]
        latest_dt = datetime.strptime(latest_date, "%Y-%m-%d")
        by_date = {date: value for date, value in cpi}
        prev_dec = "%04d-12-01" % (latest_dt.year - 1)
        five_year = "%04d-%02d-01" % (latest_dt.year - 5, latest_dt.month)
        ten_year = "%04d-%02d-01" % (latest_dt.year - 10, latest_dt.month)

        def cumulative(key, label, base_date):
            base = by_date.get(base_date)
            if base:
                value = (latest_value / base - 1) * 100
                items.append({"key": key, "label": label, "unit": "%",
                              "value": round(value, 2), "date": latest_date,
                              "base_date": base_date})

        # ⚠️⚠️ **五年是 2026-08-13 新增的，而且它不是裝飾。**
        #    五年窗口把 2021~2023 那波通膨算滿，十年窗口把它稀釋掉，
        #    兩者年化可以差快一個百分點 —— **同一筆投資會得到不同的實質報酬結論**。
        #    所以三個期間都給，讓使用者自己跟持有期間對齊。
        cumulative("cpi_ytd", "本年度累積 CPI", prev_dec)
        cumulative("cpi_5y", "近五年累積 CPI", five_year)
        cumulative("cpi_10y", "近十年累積 CPI", ten_year)

    history, conclusions = _yield_analysis(treasury)
    jp_history = [{"date": r[0], "jp2y": r[1], "jp10y": r[2], "jp30y": r[3]}
                  for r in jgb]
    # 單一來源暫時失敗時保留上一版；新抓回來的日期較舊時也不得讓畫面倒退。
    if previous_data:
        merged = {it.get("key"): it for it in previous_data.get("items", []) if it.get("key")}
        for item in items:
            old = merged.get(item.get("key"))
            if not old or str(item.get("date", "")) >= str(old.get("date", "")):
                merged[item.get("key")] = item
        items = list(merged.values())
        old_history = previous_data.get("yield_history", [])
        if old_history and (not history or history[-1].get("date", "") < old_history[-1].get("date", "")):
            history = old_history
            conclusions = previous_data.get("yield_conclusions", [])
        old_jp = previous_data.get("jp_yield_history", [])
        if old_jp and (not jp_history or jp_history[-1].get("date", "") < old_jp[-1].get("date", "")):
            jp_history = old_jp
    data = {"items": items, "yield_history": history, "jp_yield_history": jp_history,
            "yield_conclusions": conclusions,
            "updated": now.strftime("%Y-%m-%d"),
            "fetched_at": _utcnow().strftime("%Y-%m-%d %H:%M UTC")}
    if items:
        _save_cache(MACRO_CACHE_FILE, data)
    return data


def _macro_updater():
    """美日公債、聯準會與財政部背景排程；落後時每小時重試。"""
    MACRO_STATE["enabled"] = True
    while True:
        try:
            cached = _load_cache(MACRO_CACHE_FILE, None)
            if _macro_refresh_due(cached):
                with _MACRO_REFRESH_LOCK:
                    data = _us_rate_inflation_data(force=True)
                us_items = {it.get("key"): it for it in data.get("items", [])
                            if it.get("key") in ("us2y", "us10y", "us30y")}
                dates = [it.get("date") for it in us_items.values() if it.get("date")]
                latest = min(dates) if len(dates) == 3 else "—"
                MACRO_STATE["latest_us_date"] = latest
                jp_items = {it.get("key"): it for it in data.get("items", [])
                            if it.get("key") in ("jp2y", "jp10y", "jp30y")}
                jp_dates = [it.get("date") for it in jp_items.values() if it.get("date")]
                MACRO_STATE["latest_jp_date"] = min(jp_dates) if len(jp_dates) == 3 else "—"
                MACRO_STATE["last_result"] = (
                    "更新完成" if _macro_bonds_are_current(data)
                    else "來源仍落後，1 小時後重試")
                MACRO_STATE["last_run"] = _utcnow().strftime("%Y-%m-%d %H:%M UTC")
            policy_cached = _load_cache(FED_POLICY_CACHE_FILE, None)
            if _fed_policy_refresh_due(policy_cached):
                policy_data = _fed_treasury_policy_data(force=True)
                MACRO_STATE["fed_policy_date"] = policy_data.get("as_of") or "—"
                MACRO_STATE["treasury_action_date"] = (
                    (policy_data.get("treasury") or {}).get("tga") or {}).get("date") or "—"
        except Exception as exc:
            MACRO_STATE["last_result"] = "更新失敗，1 小時後重試：%s" % str(exc)[:100]
            MACRO_STATE["last_run"] = _utcnow().strftime("%Y-%m-%d %H:%M UTC")
        time.sleep(MACRO_REFRESH_HOURS * 3600)


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
            # ⚠️⚠️ **合併，不要覆寫。**
            #   2026-08-13 實際發生：備援來源只回 618 筆（2024 起），
            #   通過了「>= 300」這道門檻，然後把快取裡 **13,992 筆（1971 起）**
            #   整個蓋掉 —— **不報錯、不留痕跡，55 年歷史就這樣沒了。**
            #   「>= 300」只擋得住「太少」，擋不住「比原本少很多」。
            #   合併之後，新資料只會延長尾端，永遠不會砍掉頭部。
            # ⚠️ 這裡不能用上面的 `cached` —— 它只在快取**沒過期**時才有值，
            #    而覆寫正好發生在過期的時候。要讀「不限年齡」的那份才擋得住。
            merged = dict(_load_cache("nasdaq_index.json", None) or {})
            merged.update(out)
            if len(merged) > len(out):
                _INDEX_SRC["merged_from_cache"] = len(merged) - len(out)
            out = merged
            _save_cache("nasdaq_index.json", out)
            _INDEX_SRC.update({"name": name, "n": len(out), "errs": errs})
            return _idx_topup(out)
        errs.append("%s: 只有 %d 筆" % (name, len(out)))
    _INDEX_SRC.update({"name": None, "n": 0, "errs": errs})
    return cached or {}       # ⚠️ 抓不到別寫空的蓋掉舊資料


# 站上均線的家數（首頁「大盤詳細數據」用）
# ⚠️⚠️ **這裡是美股的線，不是台股的。**
#   台股用 60／120／240（季線／半年線／年線），美股改成 **50／150／200**：
#     ・50MA  —— 美股慣例中相當於台股季線的地位
#     ・150MA —— 趨勢模板線，也是既有 breadth.json 用的那條（保持一致）
#     ・200MA —— 美股最經典的長期線，等同台股的年線
#   📌 直接照搬 60/120/240 會讓數字對不上美股讀者的既有認知，
#      也跟站上其他頁面（50/150）說的不是同一種語言。
SNAP_MAS = ((50, "50MA"), (150, "150MA"), (200, "200MA"))
SNAP_NH_WINDOW = 60          # 創新高看幾個交易日
SNAP_NH_TOL = 0.02           # 2% 容差，與創新高篩選頁一致
SNAP_CACHE = "ma_breadth_snapshot_v2.json"  # v2: 強制限定當前前 300 大


def build_ma_breadth_snapshot(universe=None, histories=None):
    """今天有多少家站上 50／150／200MA，以及多少家創 60 日新高。

    ⚠️ **只能在預抓流程裡呼叫**（同 `build_breadth()`）：要讀幾百個快取檔。
    ⚠️ **純 Python，不用 pandas** —— 這個專案沒裝（見 5.2）。

    ⚠️⚠️ **每條均線的分母不一樣，不可以共用一個總數。**
    新上市的股票湊不滿 200 天，算進 200MA 的分母會系統性低估比例。
    每條線各自回報「有足夠資料的家數」當分母。
    """
    above = {p: 0 for p, _ in SNAP_MAS}
    base = {p: 0 for p, _ in SNAP_MAS}
    nh_above = nh_base = 0
    last_date = None
    # 只算當前市值前 300 大。CACHE_DIR 會保留過去掉出榜外或曾經
    # 預抓前 500 大的 hist_ 檔，直接掃目錄會使家數超過 300。
    universe = universe or get_universe(300)
    histories = histories or {}
    for u in universe:
        sym = u["symbol"]
        try:
            rows = histories.get(sym) or _load_cache("hist_%s.json" % sym, 24 * 365) or []
        except Exception:
            continue
        closes = [r[1] for r in rows if r and len(r) >= 2 and r[1] is not None]
        if len(closes) < SNAP_NH_WINDOW:
            continue
        last = closes[-1]
        if rows and rows[-1] and rows[-1][0]:
            last_date = max(last_date or rows[-1][0], rows[-1][0])
        for period, _ in SNAP_MAS:
            if len(closes) < period:
                continue            # 資料不足 → 不列入分母（見上面的警告）
            base[period] += 1
            if last >= sum(closes[-period:]) / period:
                above[period] += 1
        nh_base += 1
        if last >= max(closes[-SNAP_NH_WINDOW:]) * (1 - SNAP_NH_TOL):
            nh_above += 1
    if not nh_base:
        return None
    data = {
        "universe": len(universe),
        "rows": [{"period": p, "label": lab, "above": above[p], "base": base[p],
                  "pct": round(above[p] / base[p] * 100, 1) if base[p] else None}
                 for p, lab in SNAP_MAS],
        "newhigh": {"window": SNAP_NH_WINDOW, "above": nh_above, "base": nh_base,
                    "tol": SNAP_NH_TOL * 100,
                    "pct": round(nh_above / nh_base * 100, 1)},
        "date": last_date,
    }
    _save_cache(SNAP_CACHE, data)
    return data


def get_ma_breadth_snapshot():
    """⚠️ 只讀快取，不計算、不連網。資料由預抓的 `build_ma_breadth_snapshot()` 產生。"""
    data = _load_cache(SNAP_CACHE, 24) or {}
    # 最後防線：即使持久化磁碟殘留了舊口徑快取，也不在首頁顯示
    # 不可能的 >300 家數。等背景預抓建好 v2 後再顯示正確數字。
    universe = data.get("universe")
    if universe != 300:
        return {}
    if any((r.get("base") or 0) > universe or (r.get("above") or 0) > universe
           for r in data.get("rows", [])):
        return {}
    return data


def build_breadth(universe=None, histories=None):
    """從 hist_ 快取算市場寬度，存成 breadth.json。

    ⚠️ **只能在預抓流程裡呼叫。** 要讀幾百個快取檔、每檔算 BREADTH_MA，
       首頁每個訪客都跑會出事。首頁只讀 breadth.json。
    """
    out = {}
    try:
        # 與選股器共用同一批當前市值前 300 大，不把殘留的 hist_
        # 快取（舊成分股／曾經的前 500 大）誤當成市場寬度成分股。
        universe = universe or get_universe(300)
        histories = histories or {}
        above, total = {}, {}
        for u in universe:
            sym = u["symbol"]
            try:
                rows = histories.get(sym) or _load_cache("hist_%s.json" % sym, 24 * 365) or []
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
            pass                 # 種子缺失時安全降級成現有 hist_ 能算出的長度
        seed.update(out)
        keep = dict(sorted(seed.items())[-BREADTH_KEEP:])
        _save_cache("breadth.json", keep)
        return keep
    return None


def build_market_count_history(universe=None, histories=None):
    """建立首頁三張「大盤家數」三年折線圖快取。

    三條序列固定使用同一批市值前 300 大股票與同一段交易日：
    ① 嚴格多頭排列（10>20>50>150）且收盤站上 10MA
    ② 收盤站上 100MA
    ③ 收盤站上 150MA

    只能由預抓／背景更新呼叫；首頁 API 只讀彙總快取。
    """
    universe = universe or get_universe(300)
    if histories is None:
        histories = {}
        for u in universe:
            sym = u["symbol"]
            h = _load_cache("hist_%s.json" % sym, None) or []
            if h:
                histories[sym] = h

    counts = {"strict10": {}, "above100": {}, "above150": {}}
    coverage = {}
    all_dates = set()
    for u in universe:
        rows = histories.get(u["symbol"]) or []
        clean = [(r[0], float(r[1])) for r in rows
                 if r and len(r) >= 2 and r[0] and r[1] is not None]
        if len(clean) < 100:
            continue
        dates = [r[0] for r in clean]
        closes = [r[1] for r in clean]
        sums = {p: 0.0 for p in (10, 20, 50, 100, 150)}
        for i, (d, close) in enumerate(clean):
            mas = {}
            for p in sums:
                sums[p] += close
                if i >= p:
                    sums[p] -= closes[i - p]
                if i >= p - 1:
                    mas[p] = sums[p] / p
            if i >= 99:
                all_dates.add(d)
                coverage[d] = coverage.get(d, 0) + 1
                if close > mas[100]:
                    counts["above100"][d] = counts["above100"].get(d, 0) + 1
            if i >= 149:
                if close > mas[150]:
                    counts["above150"][d] = counts["above150"].get(d, 0) + 1
                if (close > mas[10] and mas[10] > mas[20] > mas[50] > mas[150]):
                    counts["strict10"][d] = counts["strict10"].get(d, 0) + 1

    # 不把「只有少數股票已更新」的半成品交易日放進首頁。
    # 否則三條家數會在最後一天假性暴跌，近期報酬也只會算到少數檔。
    min_coverage = max(60, int(len(universe) * 0.8))
    days = [d for d in sorted(all_dates) if coverage.get(d, 0) >= min_coverage][-MARKET_COUNT_KEEP:]
    if not days:
        return None
    # 首頁評論只描述「已經發生」的選股環境：過去 20／60 日有多少檔
    # 上漲，以及全體個股報酬中位數。不把廣度寫成未來預測。
    recent_rows = []
    as_of = days[-1]
    for horizon in (20, 60):
        returns = []
        for u in universe:
            clean = [(r[0], float(r[1])) for r in (histories.get(u["symbol"]) or [])
                     if r and len(r) >= 2 and r[0] and r[1] is not None and r[0] <= as_of]
            if len(clean) <= horizon or clean[-1][1] <= 0 or clean[-1][0] != as_of:
                continue
            start, last = clean[-horizon - 1][1], clean[-1][1]
            if start > 0:
                returns.append((last / start - 1) * 100)
        if returns:
            ordered = sorted(returns)
            n = len(ordered)
            median = (ordered[n // 2] if n % 2 else
                      (ordered[n // 2 - 1] + ordered[n // 2]) / 2)
            winners = sum(v > 0 for v in returns)
            recent_rows.append({"days": horizon, "base": n, "winners": winners,
                                "win_pct": round(winners / n * 100, 1),
                                "median_return": round(median, 2)})

    out = {
        "years": 3,
        "universe": len(universe),
        "as_of": as_of,
        "recent_returns": {"as_of": as_of, "rows": recent_rows},
        "series": {key: [[d, values.get(d, 0)] for d in days]
                   for key, values in counts.items()},
    }
    _save_cache(MARKET_COUNT_CACHE, out)
    return out


INDUSTRY_CACHE = "industry_analysis_v2.json"  # v2: prior-period change, concentration and full sector list
INDUSTRY_MIN_SAMPLE = 5
INDUSTRY_MA = 50
INDUSTRY_NEW_HIGH_WINDOW = 60
INDUSTRY_NEW_HIGH_TOL = 0.02


def build_industry_analysis(universe=None, histories=None):
    """以目前市值前 300 大美股建立 Sector 強弱快取；只描述已實現報酬。"""
    universe = universe or get_universe(300)
    histories = histories or {
        u["symbol"]: (_load_cache("hist_%s.json" % u["symbol"], None) or [])
        for u in universe
    }
    coverage = {}
    for u in universe:
        seen = set()
        for row in histories.get(u["symbol"]) or []:
            if row and len(row) >= 2 and row[0] and row[1] is not None:
                seen.add(str(row[0]))
        for date in seen:
            coverage[date] = coverage.get(date, 0) + 1
    minimum_coverage = max(1, int(len(universe) * 0.8))
    complete = [date for date, count in coverage.items() if count >= minimum_coverage]
    if not complete:
        return None
    as_of = max(complete)

    raw = []
    for rank, u in enumerate(universe, 1):
        clean = [(str(row[0]), float(row[1])) for row in (histories.get(u["symbol"]) or [])
                 if row and len(row) >= 2 and row[0] and row[1] is not None
                 and str(row[0]) <= as_of]
        if len(clean) < 61 or clean[-1][0] != as_of:
            continue
        closes = [value for _date, value in clean]
        last = closes[-1]
        if last <= 0 or closes[-21] <= 0 or closes[-61] <= 0:
            continue
        sector = str(u.get("sector") or "").strip()
        if not sector or sector == "—":
            continue
        raw.append({
            "rank": rank, "symbol": u["symbol"], "name": u.get("name") or u["symbol"],
            "name_zh": zh_company(u["symbol"], u.get("name") or u["symbol"]),
            "sector": sector, "sector_zh": zh_sector(sector), "close": round(last, 2),
            "ret20": (last / closes[-21] - 1) * 100,
            "ret60": (last / closes[-61] - 1) * 100,
            "prev20": ((closes[-21] / closes[-41] - 1) * 100
                       if len(closes) >= 41 and closes[-41] > 0 else None),
            "prev60": ((closes[-61] / closes[-121] - 1) * 100
                       if len(closes) >= 121 and closes[-121] > 0 else None),
            "above50": last >= sum(closes[-INDUSTRY_MA:]) / INDUSTRY_MA,
            "newhigh": last >= max(closes[-INDUSTRY_NEW_HIGH_WINDOW:]) *
                        (1 - INDUSTRY_NEW_HIGH_TOL),
        })
    if not raw:
        return None

    rs_scores = _percentile_scores({r["symbol"]: r["ret60"] for r in raw})
    for row in raw:
        row["rs60"] = int(rs_scores.get(row["symbol"], 1))

    grouped = {}
    for row in raw:
        grouped.setdefault(row["sector"], []).append(row)

    def median(values):
        ordered = sorted(float(v) for v in values)
        n = len(ordered)
        return ordered[n // 2] if n % 2 else (ordered[n // 2 - 1] + ordered[n // 2]) / 2

    industries = []
    for name, rows in grouped.items():
        if len(rows) < INDUSTRY_MIN_SAMPLE:
            continue
        med20 = median(r["ret20"] for r in rows)
        med60 = median(r["ret60"] for r in rows)
        old20 = [r["prev20"] for r in rows if r.get("prev20") is not None]
        old60 = [r["prev60"] for r in rows if r.get("prev60") is not None]
        prev_med20 = median(old20) if old20 else None
        prev_med60 = median(old60) if old60 else None
        positive = sorted((max(0.0, r["ret20"]) for r in rows), reverse=True)
        positive_total = sum(positive)
        concentration = sum(positive[:3]) / positive_total * 100 if positive_total > 0 else 0.0
        quadrant = ("strong" if med20 >= 0 and med60 >= 0 else
                    "recovery" if med20 >= 0 else
                    "cooling" if med60 >= 0 else "weak")
        leaders = sorted(rows, key=lambda r: (-r["rs60"], r["rank"]))[:5]
        industries.append({
            "name": name, "name_zh": zh_sector(name), "count": len(rows),
            "median20": round(med20, 2), "median60": round(med60, 2),
            "previous20": round(prev_med20, 2) if prev_med20 is not None else None,
            "previous60": round(prev_med60, 2) if prev_med60 is not None else None,
            "change20": round(med20 - prev_med20, 2) if prev_med20 is not None else None,
            "change60": round(med60 - prev_med60, 2) if prev_med60 is not None else None,
            "leader_concentration_pct": round(concentration, 1),
            "winners20": sum(r["ret20"] > 0 for r in rows),
            "win20_pct": round(sum(r["ret20"] > 0 for r in rows) / len(rows) * 100, 1),
            "above50": sum(r["above50"] for r in rows),
            "above50_pct": round(sum(r["above50"] for r in rows) / len(rows) * 100, 1),
            "newhigh": sum(r["newhigh"] for r in rows),
            "newhigh_pct": round(sum(r["newhigh"] for r in rows) / len(rows) * 100, 1),
            "quadrant": quadrant,
            "leaders": [{
                "rank": r["rank"], "symbol": r["symbol"], "name": r["name"],
                "name_zh": r["name_zh"], "close": r["close"],
                "ret20": round(r["ret20"], 2), "ret60": round(r["ret60"], 2),
                "rs60": r["rs60"],
            } for r in leaders],
            "stocks": [{"rank": r["rank"], "symbol": r["symbol"], "name": r["name"],
                         "name_zh": r["name_zh"], "ret20": round(r["ret20"], 2),
                         "ret60": round(r["ret60"], 2), "rs60": r["rs60"]}
                        for r in sorted(rows, key=lambda x: (-x["ret20"], x["rank"]))],
        })
    industries.sort(key=lambda r: (-r["median20"], -r["median60"], r["name"]))
    data = {
        "as_of": as_of, "universe": len(universe), "sample": len(raw),
        "minimum_industry_sample": INDUSTRY_MIN_SAMPLE,
        "grouping": "Nasdaq sector", "moving_average": INDUSTRY_MA,
        "industries": industries,
    }
    _save_cache(INDUSTRY_CACHE, data)
    return data


def get_industry_analysis():
    """只讀背景預先建立的美股產業分析快取。"""
    return _load_cache(INDUSTRY_CACHE, 24) or {}


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
    sector_counts = {}
    for row in rows:
        sector = str(row.get("sector") or "").strip()
        if not sector or sector == "—":
            continue
        item = sector_counts.setdefault(sector, {
            "name": sector, "name_zh": row.get("sector_zh") or zh_sector(sector), "n": 0})
        item["n"] += 1
    sectors = sorted(sector_counts.values(), key=lambda x: (-x["n"], x["name"]))[:3]
    _save_cache("home_screen.json", {
        "n": len(rows),
        "as_of": res.get("as_of", ""),
        # 產業速報只描述這批「嚴格多頭＋站上 10 日線」結果的集中度，
        # 並不是完整產業強弱排名；首頁文案必須把口徑說清楚。
        "sectors": sectors,
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
        if not target or (have >= target and "sectors" in old):
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
            '<b class="q-zh">強勢股篩選：今天沒有符合條件</b>'
            '<b class="q-en" style="display:none">Momentum screen: no matches today</b>'
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
        '<b class="q-zh">強勢股篩選</b>'
        '<b class="q-en" style="display:none">Momentum screen</b>'
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
        '<span class="hs-go q-zh">查看全部 →</span>'
        '<span class="hs-go q-en" style="display:none">See all →</span>'
        '</a>')


def _home_industry_brief_html():
    """首頁產業速報：顯示完整產業分析的近期 20 日前三名。只讀快取。"""
    import html as _h
    d = get_industry_analysis()
    sectors = sorted(d.get("industries") or [],
                     key=lambda row: -float(row.get("median20") or 0))[:3]
    if not sectors:
        return ('<span class="q-zh">產業資料正在背景建立中。</span>'
                '<span class="q-en" style="display:none">Sector data is being prepared.</span>')
    out = []
    for index, item in enumerate(sectors):
        value = float(item.get("median20") or 0)
        sign = "+" if value >= 0 else ""
        out.append('<span class="q-zh">%s・<b>%s</b>　%s%.2f%%</span>'
                   % ("近期最強" if index == 0 else "強勢 %d" % (index + 1),
                      _h.escape(str(item.get("name_zh") or item.get("name") or "—")), sign, value))
        out.append('<span class="q-en" style="display:none">%s · <b>%s</b>　%s%.2f%%</span>'
                   % ("Strongest recently" if index == 0 else "Strong %d" % (index + 1),
                      _h.escape(str(item.get("name") or "—")), sign, value))
    out.append('<span class="q-zh">資料截至 %s</span>' % _h.escape(str(d.get("as_of") or "—")))
    out.append('<span class="q-en" style="display:none">As of %s</span>' % _h.escape(str(d.get("as_of") or "—")))
    return "".join(out)


PHASE_UI = {
    "tailwind": {"dot": "🟢", "zh": "順風趨勢", "en": "Tailwind",
                 "zh_do": "大盤均線呈多頭排列，允許5日線低於10日線",
                 "en_do": "The index has a bullish MA alignment, allowing the 5-day MA below the 10-day MA"},
    "transition": {"dot": "🟠", "zh": "多頭回檔", "en": "Bull-market Pullback",
                   "zh_do": "均線非多頭排列，短期均線連續三日靠近季線，且季線高於半年線",
                   "en_do": "MAs are not bullish; short MAs stayed near the 60-day MA for three sessions while 60MA remains above 120MA"},
    "riskoff": {"dot": "🔴", "zh": "逆風市場", "en": "Headwind",
                "zh_do": "大盤連續三日低於半年線3%以上",
                "en_do": "The index has stayed more than 3% below its 120-day MA for three sessions"},
    "recovery_confirmed": {"dot": "🔵", "zh": "復甦確認", "en": "Recovery Confirmed",
                           "zh_do": "廣義空頭啟動觀察後，大盤連續三日站上半年線4%以上",
                           "en_do": "After a broad bearish alignment triggered observation, the index stayed more than 4% above its 120-day MA for three sessions"},
}

# 首頁四階段依均線排列與乖離判斷；順序依使用者指定的判斷表呈現。
MARKET_LIFECYCLE = [
    ("tailwind", "順風趨勢", "5MA與10MA可互換，但都高於20MA；20MA>60MA>120MA", "Tailwind", "5MA/10MA may swap; both above 20MA, with 20MA > 60MA > 120MA"),
    ("transition", "多頭回檔", "非多頭排列；至少兩條短均線與季線乖離<5%連3日；季線>半年線", "Bull-market Pullback", "Not bullish; two short MAs within 5% of 60MA for 3 sessions; 60MA above 120MA"),
    ("riskoff", "逆風市場", "連三日低於半年線3%以上", "Headwind", "More than 3% below the 120-day MA for three sessions"),
    ("recovery_confirmed", "復甦確認", "120MA>20MA或60MA後啟動觀察；連三日站上120MA逾4%", "Recovery Confirmed", "Watch after 120MA rises above 20MA or 60MA; then 3 closes over 4% above 120MA"),
]
LIFECYCLE_STAGE = {phase: i for i, (phase, *_rest) in enumerate(MARKET_LIFECYCLE, 1)}


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
        snap = get_ma_breadth_snapshot()
        if br and max(br) >= _expected_last_session() and snap:
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
                # ⚠️ 順便算，因為讀的是同一批 hist_ 快取檔 —— 分開跑等於讀兩次。
                build_ma_breadth_snapshot()
                build_market_count_history()
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


def _market_stage_from_index(index_data):
    """以大盤 5/10/20/60/120MA 排列、乖離與連續三日條件判斷四階段。"""
    try:
        points = sorted((str(date), float(value)) for date, value in (index_data or {}).items())
    except (TypeError, ValueError):
        return "unknown", "", {}
    if len(points) < max(MARKET_PHASE_MAS) + PHASE_CONFIRM_DAYS - 1:
        return "unknown", "", {}
    values = [value for _date, value in points]
    prefix = [0.0]
    for value in values:
        prefix.append(prefix[-1] + value)

    def snapshot(pos):
        mas = {days: (prefix[pos + 1] - prefix[pos + 1 - days]) / days
               for days in MARKET_PHASE_MAS}
        close = values[pos]
        near_season = sum(abs(mas[days] / mas[60] - 1) * 100 < PHASE_GAP_PCT
                          for days in (5, 10, 20)) >= 2
        return close, mas, near_season

    phase, trigger_date = None, ""
    recovery_watch = False
    latest_detail = {}
    start = max(MARKET_PHASE_MAS) - 1 + PHASE_CONFIRM_DAYS - 1
    for pos in range(start, len(points)):
        close, mas, near_season = snapshot(pos)
        recent = [snapshot(i) for i in range(pos - PHASE_CONFIRM_DAYS + 1, pos + 1)]
        bullish = (mas[5] > mas[20] and mas[10] > mas[20] > mas[60] > mas[120])
        broad_bear = mas[120] > mas[20] or mas[120] > mas[60]
        if bullish:
            recovery_watch = False
        elif broad_bear:
            recovery_watch = True
        compressed_3d = all(row[2] for row in recent)
        above_120_4pct_3d = all(row[0] > row[1][120] * (1 + PHASE_RECOVERY_PCT / 100)
                               for row in recent)
        below_120_3pct_3d = all(row[0] < row[1][120] * (1 - PHASE_RISKOFF_PCT / 100)
                               for row in recent)
        signal = None
        if bullish:
            signal = "tailwind"
        elif recovery_watch and above_120_4pct_3d:
            signal = "recovery_confirmed"
        elif compressed_3d and mas[60] > mas[120]:
            signal = "transition"
        elif below_120_3pct_3d:
            signal = "riskoff"
        if signal:
            phase, trigger_date = signal, points[pos][0]
        if pos == len(points) - 1:
            latest_detail = {"close": round(close, 2),
                             "mas": {str(k): round(v, 2) for k, v in mas.items()},
                             "trigger_date": trigger_date,
                             "recovery_watch": recovery_watch,
                             "broad_bear": broad_bear,
                             "carried": signal is None and phase is not None}
    return phase or "unknown", points[-1][0], latest_detail


def _phase_compute():
    """以納斯達克指數均線排列與乖離判斷四階段。"""
    try:
        snap = get_ma_breadth_snapshot() or {}
        long_rows = [r for r in snap.get("rows", [])
                     if int(r.get("period") or 0) in (150, 200)]
        long_breadth = (sum(float(r.get("pct") or 0) for r in long_rows) / len(long_rows)
                        if long_rows else None)
        phase, date, detail = _market_stage_from_index(
            _load_cache("nasdaq_index.json", None) or {})
        if phase == "unknown":
            _PHASE_WHY.update(why="指數資料不足，無法計算120日線", steps=[])
            return "unknown", "", "", None
        _PHASE_WHY.update(why="依大盤均線排列與乖離判斷", steps=[
            "5／10／20／60／120日均線",
            "3日確認；最近觸發 %s" % (detail.get("trigger_date") or "—"),
        ])
        conclusion = (PHASE_UI.get(phase) or {}).get("zh_do", "")
        if detail.get("carried"):
            conclusion += "（不合條件，沿用舊狀態）"
        return (phase, conclusion,
                str(date), long_breadth)
    except Exception as e:
        _PHASE_WHY.update(why="%s: %s" % (type(e).__name__, str(e)[:100]), steps=[])
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
    # RS 最長需要 251 個收盤；hist 本來就保留 1,260 日。這裡一次算好四種
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
        build_breadth(universe=uni, histories=histories)
        # ⚠️ 順便算今日快照（50／150／200MA 家數 ＋ 創 60 日新高）——
        #    讀的是同一批 hist_ 快取檔，分開跑等於整批讀兩次。
        build_ma_breadth_snapshot(universe=uni, histories=histories)
        build_market_count_history(universe=uni, histories=histories)
        PREFETCH_STATE["stage"] = "計算產業分析"
        build_industry_analysis(universe=uni, histories=histories)
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

# ⚠️⚠️ **這是「開始嘗試」的時間，不是「一定會抓到」的時間。**
#
# 2026-08-07 從 18 提前到 17（收盤後 1 小時，台灣夏令 05:00／冬令 06:00）。
# 原本堅持 18:00 的理由是：Nasdaq 的當日 K 線要等官方結算寫入，
# 收盤瞬間去抓常常只回到前一交易日，而增量抓取會判定「今天沒有新資料」，
# **要等隔天才補上** —— 看起來有在更新，實際整天慢一天，比不排程更難察覺。
#
# 現在可以提前，是因為改成「**先探測、抓到才跑全量**」：
#   17:00 用單一檔股票探測今天的收盤有沒有出來（1 次請求，很便宜）
#   → 有：立刻跑全量 300 檔
#   → 沒有：每 UPDATE_RETRY_MINUTES 再探測一次，直到來源出現目標日收盤
#   → 有：跑全量更新；若全量更新失敗，一樣 20 分鐘後重試
#   國定假日不會有當日 K 線，排程會等到下個交易日出現較新日期後完成。
#
# 📌 所以提前的風險被吸收掉了：來源準備好就早一小時拿到，
#    來源還沒好也不會像以前那樣「錯過就等明天」。
UPDATE_HOUR_ET = int(os.environ.get("UPDATE_HOUR_ET", "17"))
UPDATE_RETRY_MINUTES = int(os.environ.get("UPDATE_RETRY_MINUTES", "20"))
PROBE_SYMBOL = os.environ.get("PROBE_SYMBOL", "AAPL")
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
               "completed_session": "", "completed_at_et": "",
               "alerts_result": "—", "loop_error": "", "heartbeat": "—", "heartbeat_ts": 0,
               "probe": "—", "probe_error": ""}

# 上次更新紀錄寫在持久化磁碟，重啟後仍看得到。
# next_run 每次啟動都會重算，不寫入磁碟；完成的資料日與美東時間則要保留。
SCHED_FILE = os.path.join(CACHE_DIR, ".sched_state.json")


def _sched_load():
    try:
        with open(SCHED_FILE, "r", encoding="utf-8") as f:
            d = json.load(f)
        for k in ("last_run", "last_result", "completed_session", "completed_at_et"):
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
                       "last_result": SCHED_STATE["last_result"],
                       "completed_session": SCHED_STATE["completed_session"],
                       "completed_at_et": SCHED_STATE["completed_at_et"]},
                      f, ensure_ascii=False)
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


def _completed_at_et(dt=None):
    """網站對外顯示的完成時間：美東日期與時分，含 EST/EDT。"""
    dt = dt or _utcnow()
    off = _et_offset_hours(dt)
    return "%s %s" % ((dt - timedelta(hours=off)).strftime("%Y-%m-%d %H:%M"),
                       "EDT" if off == 4 else "EST")


def _beat():
    """心跳。用來判斷執行緒還活著 —— 只靠 enabled 旗標看不出來，
    那個旗標設過一次就不會變，執行緒死掉了它還是顯示「是」。"""
    SCHED_STATE["heartbeat_ts"] = time.time()
    SCHED_STATE["heartbeat"] = _fmt_et(_utcnow())


def _sleep_beats(seconds):
    """分段睡眠並持續更新心跳。

    ⚠️ **背景執行緒裡不要一次睡很久。** 睡 20 分鐘期間心跳不會更新，
       診斷頁會顯示「有啟動但心跳停了 N 分鐘」—— 看起來像執行緒死了。
       把「等待」誤判成「死亡」會讓人去查一個根本不存在的問題。
    """
    end = time.time() + max(0.0, seconds)
    while True:
        remain = end - time.time()
        if remain <= 0:
            return
        time.sleep(min(60.0, remain))
        _beat()


def _target_session_et():
    """這次排程「應該要抓到」的交易日：美東今天（平日）。

    ⚠️ 不處理國定假日。假日時會持續等待，直到下個交易日的較新 K 線出現；
       這樣不需要在程式裡維護可能變動的美股休市表。
    """
    et = _utcnow() - timedelta(hours=_et_offset_hours(_utcnow()))
    return et.strftime("%Y-%m-%d") if et.weekday() < 5 else None


def _probe_last_session(symbol=None):
    """**單檔**探測：來源目前最新的交易日是哪一天。抓不到回 None。

    ⚠️ **只讀不寫，絕對不碰任何快取。** 這支的用途是「先問問看資料好了沒」，
       一次請求、只要最近幾天，成本大約是全量預抓的三百分之一。
    📌 有了它，排程才敢提前到收盤後一小時：探到才跑全量，
       探不到就等一下再探 —— 而不是像以前那樣「時間到就全量抓一次，錯過等明天」。
    """
    sym = symbol or PROBE_SYMBOL
    frm = (_utcnow() - timedelta(days=12)).strftime("%Y-%m-%d")
    try:
        rows = _hist_nasdaq(sym, frm)
    except Exception as e:
        SCHED_STATE["probe_error"] = "%s: %s" % (type(e).__name__, str(e)[:80])
        return None
    SCHED_STATE["probe_error"] = ""
    return max((d for d, _c in rows), default=None)


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
            # ---- 先探測：來源今天的收盤出來了沒 ----
            # ⚠️ 探測失敗不能讓這一輪結束。單檔請求可能剛好失敗，
            #    因此沒探到就繼續每 20 分鐘重試，不以一次失敗推論整個來源無資料。
            target = _target_session_et()
            probes, got = 0, None
            while target:
                got = _probe_last_session()
                probes += 1
                SCHED_STATE["probe"] = ("第 %d 次：來源最新 %s（目標 %s）"
                                        % (probes, got or "—", target))
                _beat()
                if got and got >= target:
                    break
                _sleep_beats(UPDATE_RETRY_MINUTES * 60)
            if target:
                SCHED_STATE["probe"] += "　✅ 探到當日收盤，開始全量更新"

            # 來源已就緒後，全量更新本身也要重試；不能因為一次網路錯誤
            # 就直接等到隔天。成功標準至少要求探測標的的本地快取到目標日。
            while True:
                try:
                    prefetch(300, force=True)   # ⚠️ 收盤後必須繞過 TTL
                    cached_probe = _load_cache("hist_%s.json" % PROBE_SYMBOL.upper(), None) or []
                    cached_last = cached_probe[-1][0] if cached_probe else None
                    if target and (not cached_last or cached_last < target):
                        raise RuntimeError("快取最新 %s，尚未到目標 %s"
                                           % (cached_last or "—", target))
                    break
                except Exception as e:
                    SCHED_STATE["last_result"] = "更新失敗，%d 分鐘後重試：%s" % (
                        UPDATE_RETRY_MINUTES, str(e)[:100])
                    SCHED_STATE["last_run"] = _fmt_et(_utcnow())
                    _sched_save()
                    _sleep_beats(UPDATE_RETRY_MINUTES * 60)

            try:
                # 「程式跑完」不等於「資料追到目標日」。以前這裡無條件寫成功，
                # 導致來源只到前一日卻顯示綠燈，使用者只能從頁面日期猜出有問題。
                completed_session = cached_last or got or target or ""
                SCHED_STATE["last_result"] = ("成功（無交易日目標）" if not target else
                                              "成功（資料到 %s）" % completed_session)
                SCHED_STATE["completed_session"] = completed_session
                SCHED_STATE["completed_at_et"] = _completed_at_et()
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
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
__SEO_HEAD__
<meta name="theme-color" content="#33241A">
<script>try{var savedTheme=localStorage.getItem('us-cafe-theme')||'b';document.documentElement.dataset.theme=['b','c','d'].includes(savedTheme)?savedTheme:'b'}catch(e){document.documentElement.dataset.theme='b'}</script>
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
    /* B 京都喫茶（預設） */
    --milk:#F3EFE2;--foam:#FFFDF7;--grounds:#BCC9B8;--espresso:#263A2D;--mocha:#607065;
    --caramel:#A45E2A;--caramel-2:#42664C;--primary:#A45E2A;--bg:#F3EFE2;--page-edge:#E3DDCB;--page-glow:#FAF7ED;
    /* 行情紅綠（只給數據） */
    --up:#CB4B3A; --down:#4A7C64;
    --font-brand:"Noto Serif TC",serif;
    --font-head:"Noto Serif TC",serif;
    --font-body:"Noto Sans TC",sans-serif;
    --font-num:"Space Mono",ui-monospace,monospace;
    --shadow:0 14px 34px -20px rgba(51,36,26,.45);
  }
  html[data-theme="c"]{--milk:#17252B;--foam:#21343A;--grounds:#466068;--espresso:#F5EAD7;--mocha:#C5B9A5;--caramel:#B98942;--caramel-2:#D2A65F;--primary:#D2A65F;--bg:#17252B;--page-edge:#101B20;--page-glow:#263B42;--shadow:0 14px 34px -20px rgba(0,0,0,.8)}
  html[data-theme="d"]{--milk:#F5EAE5;--foam:#FFF9F5;--grounds:#D8BBB3;--espresso:#50302F;--mocha:#7B675F;--caramel:#9B5148;--caramel-2:#7B6752;--primary:#9B5148;--bg:#F5EAE5;--page-edge:#E8D8D2;--page-glow:#FFF6F1}
  html{min-height:100%;background:var(--page-edge);overscroll-behavior-y:none}
  * { box-sizing:border-box; font-family:var(--font-body); }
  body { margin:0; color:var(--espresso);
    background:var(--page-edge) radial-gradient(120% 80% at 50% -10%,var(--page-glow) 0%,var(--milk) 55%,var(--page-edge) 100%);
    min-height:100vh;            /* 舊瀏覽器 fallback */
    min-height:100svh;           /* 手機：網址列展開時的穩定可視高度 */
    min-height:100dvh;           /* 手機：跟著網址列伸縮的實際可視高度 */
    overflow-x:clip;
    overscroll-behavior-y:none;
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
  .yield-chart { width:100%; height:auto; display:block; overflow:visible; }
  html[data-theme="c"] .yield-tip rect { fill:#101B20; stroke:#D2A65F; opacity:.98; }
  html[data-theme="c"] .yield-tip text { fill:#F5EAD7; }
  .yield-legend { display:flex; gap:16px; flex-wrap:wrap; margin:8px 0 2px; font-size:12px; color:var(--mocha); }
  .yield-legend i { display:inline-block; width:18px; height:3px; margin-right:5px; vertical-align:middle; border-radius:2px; }
  .yield-findings { margin:8px 0 0; padding-left:20px; }
  .yield-findings li { color:#555; line-height:1.7; margin:5px 0; }
  .yield-findings li.alert { color:#9b3f2d; font-weight:700; }
  .eps-half { margin-top:6px; }
  .eps-half summary { cursor:pointer; color:var(--caramel-2); font-size:11.5px; white-space:nowrap; }
  .eps-half-grid { display:grid; grid-template-columns:repeat(2,minmax(88px,1fr)); gap:5px; margin-top:6px; min-width:190px; }
  .eps-half-grid span { display:flex; justify-content:space-between; gap:8px; padding:5px 7px; border-radius:7px; background:var(--milk); color:var(--mocha); font-size:11.5px; }
  .eps-half-grid b { color:var(--espresso); font-family:var(--font-num); }
  /* 公司欄原本會裁切溢出內容；半年度面板改為撐開表格，外層可橫向捲動。 */
  .res-wide td:has(.eps-half) { max-width:none; overflow:visible; text-overflow:clip; }
  .res-wide .eps-half-grid { width:270px; min-width:270px; }
  .res-cards .eps-half-grid { width:100%; min-width:0; }
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
  /* ---- 名言卡（與台股版同一套樣式）---- */
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
  /* ---- 均線扣抵法 ---- */
  .ded-grid { display:grid; grid-template-columns:repeat(2,1fr); gap:10px; }
  .ded-i { background:var(--foam); border:1px solid var(--grounds);
           border-radius:10px; padding:9px 11px; }
  .ded-i .k { font-size:11.5px; color:var(--mocha); font-weight:700; }
  .ded-i .v { font-size:18px; font-weight:700; font-family:var(--font-num);
           color:var(--espresso); margin:2px 0 1px; }
  .ded-i .n { font-size:11.5px; color:var(--mocha); line-height:1.5; }
  .ded-note { font-size:13px; color:var(--mocha); margin:10px 0; line-height:1.7; }
  .ded-note b { color:var(--espresso); font-family:var(--font-num); }
  .ded-rows { background:var(--milk); border-radius:10px; padding:4px 12px; }
  .ded-rows div { display:flex; justify-content:space-between; align-items:baseline;
           gap:10px; padding:9px 0; border-bottom:1px solid rgba(107,85,64,.12);
           font-size:13.5px; color:var(--mocha); }
  .ded-rows div:last-child { border-bottom:none; }
  .ded-rows b { font-size:19px; color:var(--caramel-2); font-family:var(--font-num); }
  .ded-rows small.ded-pos { color:var(--up); font-weight:700; }
  .ded-rows small.ded-neg-v { color:var(--down); font-weight:700; }
  .ded-rows .ded-over { font-size:13.5px; color:var(--mocha); }
  .ded-rows b.ded-done { font-size:16px; color:var(--down); }
  .ded-neg { margin-top:9px; font-size:12px; color:var(--mocha); line-height:1.75;
           background:rgba(203,75,58,.07); border-radius:8px; padding:8px 11px; }
  .ded-warn { max-width:560px; margin:14px auto 0; font-size:12.5px; color:var(--mocha);
           line-height:1.8; background:var(--foam); border:1px solid var(--grounds);
           border-radius:10px; padding:10px 13px; }
  @media (max-width:640px){ .ded-grid { grid-template-columns:1fr; } }
  /* ---- 風控管理 ---- */
  .chip { display:inline-flex; align-items:center; gap:6px; padding:6px 10px;
            background:var(--milk); border:1px solid var(--grounds); border-radius:999px;
            font-family:var(--font-num); font-weight:700; font-size:14px; }
  .chip i { font-style:normal; cursor:pointer; color:var(--mocha); font-size:12px; }
  .chip i:hover { color:var(--up); }
  .rk-card { padding:16px 18px; }
  .rk-h { display:flex; align-items:baseline; gap:9px; }
  .rk-h b { font-family:var(--font-num); font-size:19px; color:var(--espresso); }
  .rk-h span { font-size:14px; color:var(--mocha); flex:1; }
  .rk-h i { font-style:normal; cursor:pointer; color:var(--mocha); font-size:13px; }
  .rk-sub { font-size:12.5px; color:var(--mocha); margin:3px 0 12px;
            font-family:var(--font-num); }
  .rk-grid { display:grid; grid-template-columns:repeat(2,1fr); gap:10px; }
  .rk-i { background:var(--foam); border:1px solid var(--grounds);
            border-radius:10px; padding:9px 11px; }
  .rk-i .k { font-size:11.5px; color:var(--mocha); font-weight:700; }
  .rk-i .v { font-size:17px; font-weight:700; font-family:var(--font-num);
            color:var(--espresso); margin:2px 0 1px; }
  .rk-i .v small { font-family:var(--font-num); font-size:12px; color:var(--mocha); }
  .rk-i .n { font-size:11px; color:var(--mocha); line-height:1.5; }
  .rk-entry { display:flex; align-items:center; gap:9px; margin-top:12px; }
  .rk-entry span { font-size:13px; color:var(--mocha); font-weight:700; white-space:nowrap; }
  .rk-entry input { flex:1; padding:9px 11px; font-size:15px; font-family:var(--font-num);
            border:1.5px solid var(--grounds); border-radius:10px; background:#fff;
            box-sizing:border-box; }
  .rk-entry input:focus { outline:none; border-color:var(--caramel); }
  .rk-stops { display:grid; grid-template-columns:repeat(2,1fr); gap:8px; margin-top:10px;
            background:var(--milk); border-radius:10px; padding:10px 12px; }
  .rk-stops div { display:flex; justify-content:space-between; align-items:baseline; gap:8px; }
  .rk-stops span { font-size:12px; color:var(--mocha); }
  .rk-stops b { font-family:var(--font-num); font-size:15px; color:var(--espresso); }
  .rk-hint { margin-top:10px; font-size:12.5px; color:var(--mocha); line-height:1.7; }
  @media (max-width:640px){
    .rk-grid, .rk-stops { grid-template-columns:1fr; }
  }
  /* 同期比較 */
  .cmp-form { display:grid; grid-template-columns:1fr 1fr; gap:12px; }
  .cmp-field label { display:block; margin-bottom:5px; color:var(--mocha);
           font-size:12.5px; font-weight:700; }
  .cmp-field input { width:100%; box-sizing:border-box; padding:10px 11px;
           border:1.5px solid var(--grounds); border-radius:10px; background:#fff;
           color:var(--espresso); font:14px var(--font-num); }
  .cmp-peers { display:flex; gap:8px; flex-wrap:wrap; margin-top:10px; }
  .cmp-chip { display:flex; align-items:center; gap:8px; background:var(--milk);
           border:1px solid var(--grounds); border-radius:999px; padding:7px 12px;
           font-size:14px; color:var(--espresso); }
  .cmp-chip b { font-family:var(--font-num); color:var(--caramel-2); }
  .cmp-chip .x { cursor:pointer; color:var(--mocha); }
  .cmp-grid { display:grid; grid-template-columns:repeat(2,minmax(0,1fr)); gap:12px;
           margin-top:14px; }
  .cmp-card { background:var(--foam); border:1.5px solid var(--grounds);
           border-radius:16px; padding:15px; box-shadow:var(--shadow); min-width:0; }
  .cmp-card.actual { border-color:var(--caramel); }
  .cmp-card.best { box-shadow:0 0 0 2px rgba(166,103,65,.16),var(--shadow); }
  .cmp-head { display:flex; align-items:flex-start; gap:8px; }
  .cmp-role { flex-shrink:0; border-radius:999px; padding:3px 8px;
           background:var(--milk); color:var(--caramel-2); font-size:11px; font-weight:700; }
  .cmp-code { font:700 17px var(--font-num); color:var(--espresso); }
  .cmp-name { color:var(--mocha); font-size:12px; overflow:hidden;
           white-space:nowrap; text-overflow:ellipsis; }
  .cmp-ret { margin:12px 0 8px; font:800 27px var(--font-num); }
  .cmp-ret.up { color:var(--up); } .cmp-ret.down { color:var(--down); }
  .cmp-kv { display:grid; grid-template-columns:auto 1fr; gap:5px 10px;
           border-top:1px solid var(--grounds); padding-top:9px; font-size:12px; }
  .cmp-kv span:nth-child(odd) { color:var(--mocha); }
  .cmp-kv span:nth-child(even) { text-align:right; font-family:var(--font-num);
           color:var(--espresso); overflow-wrap:anywhere; }
  @media(max-width:560px){ .cmp-form,.cmp-grid { grid-template-columns:1fr; } }
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
  #p1 > .status,#p3 > .status { max-width:560px; margin:14px auto; }
  table { width:100%; border-collapse:collapse; font-size:13px; background:var(--foam);
          border-radius:14px; overflow:hidden; box-shadow:var(--shadow); }
  /* 長期成長股列表的排序切換鈕 */
  .segbar { display:flex; gap:8px; margin:0 0 12px; flex-wrap:wrap; }
  .segbtn { padding:8px 14px; border:1px solid var(--grounds); background:var(--foam);
            border-radius:999px; font-size:13px; cursor:pointer; color:inherit;
            font-family:inherit; }
  .segbtn:hover { border-color:var(--caramel); }
  .segbtn.active { background:var(--caramel); border-color:var(--caramel); color:#fff; }
  /* ⚠️⚠️ 這裡**不用表格**。六欄的表格在手機上一定要左右橫拉，
     而 .res-wide 在 640px 以下是 display:none（要另外維護一套卡片版）。
     改用單列 grid：左邊名稱可省略號截斷、右邊數字靠右，
     **任何寬度都不需要橫向捲動**，桌機手機共用同一份版面。 */
  .growlist { display:flex; flex-direction:column; gap:6px; }
  .growrow { display:grid; grid-template-columns:30px minmax(0,1fr) auto;
             align-items:center; gap:10px; padding:10px 12px;
             background:var(--foam); border:1px solid var(--grounds);
             border-radius:12px; }
  .growrow.top { border-color:var(--caramel); }
  .growrk { font-size:12px; opacity:.5; text-align:right; font-variant-numeric:tabular-nums; }
  /* ⚠️ minmax(0,1fr) 不能寫成 1fr —— grid 項目的最小尺寸預設是內容寬度，
     寫 1fr 的話長公司名會把整列撐開，省略號永遠不會生效。 */
  .growmid { min-width:0; }
  .growsym { font-weight:700; font-size:14px; }
  .growname { font-size:12px; opacity:.6; overflow:hidden;
              text-overflow:ellipsis; white-space:nowrap; }
  .growval { text-align:right; font-variant-numeric:tabular-nums; }
  .growtot { font-weight:700; font-size:15px; }
  .growsub { font-size:11px; opacity:.6; margin-top:1px; }
  @media (max-width:420px){
    .growname { font-size:11px; }
    .growtot { font-size:14px; }
  }
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
  .structure-details { min-width:112px; text-align:left; }
  .structure-details > summary { display:inline-flex; align-items:center; gap:5px; cursor:pointer;
    list-style:none; white-space:nowrap; border:1px solid var(--grounds); border-radius:999px;
    padding:5px 9px; background:var(--milk); color:var(--mocha); font-size:12px; font-weight:700; }
  .structure-details > summary::-webkit-details-marker{display:none}
  .structure-details > summary::before{content:'▸';font-size:10px}.structure-details[open]>summary::before{content:'▾'}
  .structure-details > summary.structure-hit{background:rgba(61,139,103,.12);border-color:rgba(61,139,103,.42);color:#2f7657}
  .structure-details > summary.structure-near{background:rgba(211,154,44,.14);border-color:rgba(211,154,44,.48);color:#8a6200}
  .structure-details > summary.structure-miss{background:rgba(190,66,49,.10);border-color:rgba(190,66,49,.35);color:var(--up)}
  .structure-panel { width:min(680px,82vw); margin-top:8px; padding:13px; border-radius:14px;
    background:var(--foam); border:1px solid var(--grounds); box-shadow:var(--shadow); color:var(--espresso); }
  .structure-title { display:flex; justify-content:space-between; align-items:flex-start; gap:10px; margin-bottom:9px; }
  .structure-title b{font-family:var(--font-head);font-size:15px}.structure-title small{color:var(--mocha);line-height:1.5;text-align:right}
  .structure-tags{display:flex;gap:5px;flex-wrap:wrap;margin:0 0 9px}.structure-tags span{padding:3px 8px;border-radius:999px;background:var(--milk);border:1px solid var(--grounds);font-size:11px;color:var(--mocha)}
  .structure-metrics { display:grid; grid-template-columns:repeat(3,1fr); gap:7px; margin-bottom:10px; }
  .structure-metric { min-width:0; padding:8px 9px; border-radius:10px; background:var(--milk); }
  .structure-metric small{display:block;color:var(--mocha);font-size:10.5px}.structure-metric b{display:block;margin-top:3px;font:700 15px var(--font-num);overflow-wrap:anywhere}
  .structure-chart-head{display:flex;justify-content:space-between;align-items:center;gap:8px;margin:7px 0 2px}
  .structure-chart-range{font:11px var(--font-num);color:var(--mocha)}
  .structure-chart-buttons{display:flex}.structure-chart-buttons button{border:1px solid var(--grounds);border-right:0;background:var(--foam);color:var(--mocha);padding:4px 8px;cursor:pointer;font-size:11px}.structure-chart-buttons button:first-child{border-radius:7px 0 0 7px}.structure-chart-buttons button:last-child{border-right:1px solid var(--grounds);border-radius:0 7px 7px 0}.structure-chart-buttons button.on{background:var(--espresso);color:#fff}
  .structure-chart svg{width:100%;height:auto;display:block;touch-action:none;cursor:grab;user-select:none}.structure-chart svg.dragging{cursor:grabbing}
  .structure-chart-read{min-height:18px;margin-left:42px;font:11px var(--font-num);color:var(--mocha)}
  .structure-note{font-size:10.5px;color:var(--mocha);line-height:1.55;margin-top:5px}
  .structure-reason{padding:8px 10px;border-radius:9px;background:rgba(137,107,77,.08);color:var(--mocha);font-size:12px;line-height:1.6;margin-bottom:8px}
  .scard .structure-panel{width:100%;box-shadow:none}.scard .structure-details{grid-column:1/-1;margin-top:7px}
  /* RS 電腦版：股票摘要列搭配全寬結構面板，不把長期圖表塞進表格欄位。 */
  .rs-card{max-width:920px}.rs-structure-list{display:grid;gap:10px;overflow:visible}
  .rs-structure-item{min-width:0;padding:12px 14px;background:var(--foam);border:1px solid var(--grounds);border-radius:14px;box-shadow:var(--shadow)}
  .rs-structure-head{display:grid;grid-template-columns:72px minmax(180px,1.5fr) minmax(110px,1fr) repeat(3,minmax(88px,.7fr));gap:10px;align-items:center;padding-bottom:10px;border-bottom:1px solid var(--grounds)}
  .rs-structure-cell{min-width:0}.rs-structure-cell small{display:block;margin-bottom:2px;color:var(--mocha);font-size:10.5px}.rs-structure-cell b{display:block;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font:700 14px var(--font-num);color:var(--espresso)}
  .rs-structure-company b{font-family:var(--font-head);font-size:15px}.rs-structure-company span{margin-right:7px;font-family:var(--font-num);color:var(--caramel-2)}
  .rs-structure-item>.structure-details{margin-top:10px}.rs-structure-item .structure-panel{width:100%;box-sizing:border-box;box-shadow:none}.rs-structure-item .structure-details>summary{font-size:13px;padding:6px 11px}
  @media(min-width:1000px){.rs-structure-item .structure-metrics{grid-template-columns:repeat(6,minmax(0,1fr))}}
  /* 640px 以下只顯示既有手機卡片；此規則必須放在 rs-structure-list 的桌機 display:grid 之後。 */
  @media(max-width:640px){.res-wide.rs-structure-list{display:none}}
  @media(max-width:760px) and (min-width:641px){.rs-structure-head{grid-template-columns:62px minmax(160px,1.4fr) repeat(2,minmax(85px,.7fr))}.rs-structure-industry,.rs-structure-close{display:none}}
  @media(max-width:560px){.structure-panel{width:100%;padding:10px}.structure-metrics{grid-template-columns:1fr 1fr}.structure-title{display:block}.structure-title small{display:block;text-align:left;margin-top:3px}}
  .screen-tools { max-width:560px; margin:10px auto; padding:10px; border:1px solid var(--grounds); border-radius:12px; background:var(--foam); display:flex; gap:7px; flex-wrap:wrap; align-items:center; }
  .screen-tools input,.screen-tools select { min-width:0; height:38px; padding:7px 10px; border:1px solid var(--grounds); border-radius:9px; background:var(--milk); color:var(--espresso); font:inherit; }
  .screen-tools input { flex:1 1 145px; }.screen-tools select { flex:1 1 150px; }
  .screen-tools button { min-height:38px; padding:7px 11px; border:1px solid var(--grounds); border-radius:9px; background:var(--milk); color:var(--espresso); font-weight:700; cursor:pointer; }
  .screen-tools button:hover { border-color:var(--caramel); color:var(--caramel-2); }
  .screen-tools .export { background:var(--caramel); color:#fff; border-color:var(--caramel); }
  .screen-tools-status { flex-basis:100%; min-height:16px; color:var(--mocha); font-size:12px; }
  .sort-th { cursor:pointer; user-select:none; text-decoration:underline dotted; text-underline-offset:3px; }
  .momentum-badge { display:inline-flex; align-items:center; padding:3px 8px; border:1px solid currentColor;
           border-radius:999px; font-size:11px; font-weight:800; line-height:1.25; white-space:nowrap; }
  .momentum-badge.strong { color:var(--up); }
  .momentum-badge.consolidate { color:var(--caramel-2); }
  .momentum-badge.recovery { color:var(--primary); }
  .momentum-badge.weak { color:var(--down); }
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
  td.coname:has(.eps-half) { max-width:none; overflow:visible; text-overflow:clip; }
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
  #sidebar { overflow-y:auto; padding-bottom:calc(28px + env(safe-area-inset-bottom)); }
  .nav-section { padding:13px 22px 5px; font-size:10.5px; font-weight:700; letter-spacing:.14em; color:#9a8775; text-transform:uppercase; }
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
  .updnote { width:100%; max-width:920px; margin:0 auto 14px; padding:14px 18px;
            background:var(--foam); border:1px solid var(--grounds); border-radius:10px;
            font-size:14px; color:var(--mocha); line-height:1.75; }
  .updnote b { color:var(--espresso); font-family:var(--font-num); }
  .updnote small { display:block; font-size:12.5px; color:var(--mocha);
            opacity:.85; margin-top:3px; line-height:1.6; }
  .data-health-line{display:block;margin-top:8px;padding:7px 10px;border-radius:9px;font-size:12px;font-weight:700;line-height:1.55}
  .data-health-line.health-ok{color:#24734a;background:rgba(39,129,83,.10)}
  .data-health-line.health-stale{color:#9b3f2d;background:rgba(200,67,53,.10)}
  /* B／C／D 僅替換色票；版面、字級、間距及資訊層級固定共用。 */
  .data-quality-strip{display:flex;gap:8px;flex-wrap:wrap;align-items:center;margin:0 0 14px}.data-quality-chip{display:inline-flex;align-items:center;gap:6px;min-height:30px;padding:5px 10px;border:1px solid var(--grounds);border-radius:999px;background:var(--foam);color:var(--mocha);font-size:12px;font-weight:700;line-height:1.4}.data-quality-chip::before{content:"";width:8px;height:8px;border-radius:50%;background:var(--mocha)}.data-quality-chip.dq-ok::before{background:#278153}.data-quality-chip.dq-pending::before{background:#b8872e}.data-quality-chip.dq-warn::before{background:#d2782c}.data-quality-chip.dq-danger{border-color:#c84335;background:rgba(200,67,53,.13);color:#9b3026;font-weight:900}.data-quality-chip.dq-danger::before{background:#c84335;box-shadow:0 0 0 4px rgba(200,67,53,.14)}
  .reading-card{display:grid;gap:0;margin-top:14px;border:1px solid var(--grounds);border-radius:13px;overflow:hidden;background:var(--foam)}.reading-row{display:grid;grid-template-columns:68px 1fr;gap:12px;padding:10px 12px;font-size:13px;line-height:1.65;color:var(--mocha)}.reading-row+.reading-row{border-top:1px solid var(--grounds)}.reading-row b{color:var(--espresso);font-family:var(--font-head)}
  .ind-change-grid{display:grid;grid-template-columns:repeat(3,1fr);gap:8px;margin:10px 0}.ind-change{padding:9px;border:1px solid var(--grounds);border-radius:10px;background:var(--milk);font-size:12px}.ind-change b{display:block;margin-top:3px;font-family:var(--font-num)}.ind-stock-list{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:6px;margin-top:10px}.ind-stock{display:grid;grid-template-columns:1fr auto;gap:8px;padding:7px 9px;border:1px solid var(--grounds);border-radius:9px;color:inherit;text-decoration:none;font-size:12px;background:var(--foam)}
  html[data-theme="c"] .data-quality-chip.dq-danger{color:#ffb0a6;background:rgba(200,67,53,.23)}
  .qhead { display:flex; align-items:center; gap:12px; max-width:560px;
           margin:26px auto 14px; font-family:var(--font-head); font-weight:700;
           font-size:13px; color:var(--mocha); letter-spacing:.16em; }
  .qhead::after { content:""; flex:1; height:1px; background:var(--grounds); }
  /* 首頁新版市場儀表板：結構與台股同步，均線口徑保留美股 50／150／200MA。 */
  #home{max-width:920px;margin:0 auto}
  .home-dashboard{display:grid;gap:16px}.market-now{display:grid;gap:14px;margin-bottom:18px}
  .market-now-hero,.market-data-card{background:var(--foam);border:1px solid var(--grounds);border-radius:16px;box-shadow:var(--shadow)}
  .market-now-hero{padding:22px 28px;background:linear-gradient(135deg,#fffdf9,#f8f0e4);border-radius:18px}
  .market-now-title{display:flex;align-items:center;gap:18px;flex-wrap:wrap}.market-now-title h1{margin:0;font:900 32px var(--font-head);text-align:left}.market-now-title h1::after{display:none}
  .market-now-badge{display:inline-flex;padding:8px 20px;border-radius:999px;background:linear-gradient(135deg,var(--caramel),var(--caramel-2));color:#fff;font-weight:700}.market-now-hero p{margin:12px 0 0;color:var(--mocha);font-size:15px;line-height:1.7}
  .market-scope-note{margin-top:7px;color:var(--mocha);font-size:12px;line-height:1.65;opacity:.9}
  .market-now-grid{display:grid;grid-template-columns:1.15fr .85fr;gap:14px}.market-data-card{padding:16px;min-width:0}.market-data-card h2{margin:0 0 12px;font:700 18px var(--font-head)}
  .market-return-row{display:grid;grid-template-columns:150px 1fr 112px;align-items:center;border:1px solid var(--grounds);border-bottom:0}.market-return-row:last-child{border-bottom:1px solid var(--grounds)}.market-return-row>span{padding:13px}.market-return-row>span+span{border-left:1px solid var(--grounds)}
  .market-return-main{font-family:var(--font-num);text-align:right}.market-return-main b{font-size:20px;color:var(--up)}.market-return-med{text-align:right;color:var(--mocha)}.market-return-med b{display:block;font:700 20px var(--font-num)}
  .breadth-row{display:grid;grid-template-columns:58px 1fr 104px;align-items:center;gap:10px;margin:13px 0}.breadth-row b{font-family:var(--font-head)}.breadth-bar{display:flex;height:12px;overflow:hidden;border-radius:4px;background:var(--grounds)}.breadth-above{background:var(--up)}.breadth-below{background:var(--down)}
  .breadth-num{text-align:right;font:700 13px var(--font-num)}.breadth-num .up{color:var(--up)}.breadth-num .down{color:var(--down)}.breadth-legend{display:flex;gap:16px;margin-top:14px;color:var(--mocha);font-size:12px}.breadth-legend i{display:inline-block;width:9px;height:9px;margin-right:5px}
  .market-chart-card{padding-bottom:10px}.market-chart-head{display:flex;justify-content:space-between;gap:12px;align-items:center;margin-bottom:6px}.market-chart-head h2{margin:0}.market-periods{display:flex}.market-periods button{border:1px solid var(--grounds);border-right:0;background:var(--foam);padding:7px 14px;cursor:pointer;color:var(--mocha)}.market-periods button:first-child{border-radius:8px 0 0 8px}.market-periods button:last-child{border-right:1px solid var(--grounds);border-radius:0 8px 8px 0}.market-periods button.on{background:var(--espresso);color:#fff}
  #homeIndexChart svg{width:100%;height:auto;display:block;touch-action:none;cursor:grab;user-select:none}#homeIndexChart svg.dragging{cursor:grabbing}.home-chart-read{min-height:20px;font:12px var(--font-num);color:var(--mocha);margin:2px 0 0 45px}.market-chart-note{font-size:11px;color:var(--mocha);text-align:right;margin-top:-3px}
  /* 「今日觀察」只是區段標題與內容容器，不另外鋪一層卡片底色。 */
  .home-action-panel{padding:0;background:transparent;border:0;box-shadow:none}
  /* 與「今日市場」共用同一個 960px 首頁欄寬；不要再受舊版 560px 卡片寬度限制。 */
  .home-action-panel .qhead{max-width:none;margin:14px 0 8px}
  .home-action-panel .home-section-note{max-width:none;margin:0 0 12px}
  .home-action-panel .home-actions{max-width:none;grid-template-columns:1fr 1fr}
  #home>.qhead{max-width:920px}
  html[data-theme="c"] .home-action-panel{background:transparent!important;border:0;box-shadow:none}
  html[data-theme="c"] .data-health-line.health-ok{color:#75d7a2;background:rgba(39,129,83,.22)}
  html[data-theme="c"] .data-health-line.health-stale{color:#ff9b8f;background:rgba(200,67,53,.20)}
  .home-section-note{max-width:560px;margin:-6px auto 12px;color:var(--mocha);font-size:12px;line-height:1.65}
  .home-actions{max-width:560px;margin:0 auto;display:grid;grid-template-columns:1fr 1fr;gap:10px}
  .home-actions .hs-box,.home-actions .home-industry{margin:0;min-width:0;max-width:none}
  .home-industry{display:block;text-decoration:none;color:inherit;background:linear-gradient(135deg,#fffaf2,#f3e6d3);border:1px solid #e4d2b6}
  .home-industry:hover{transform:translateY(-1px);box-shadow:0 8px 22px rgba(91,63,39,.09)}
  .home-industry-head{display:flex;justify-content:space-between;align-items:center;gap:12px;margin-bottom:10px}
  .home-industry-head h2{margin:0}.home-industry-head>span{color:var(--mocha);font-weight:700;font-size:14px}
  .home-industry-list{display:flex;gap:8px;flex-wrap:wrap}
  .home-industry-list>span{width:100%;padding:7px 10px;border-radius:10px;background:rgba(255,255,255,.72);font-size:14px}
  html[data-theme="c"] .home-industry{background:#21343A;border-color:#466068}
  html[data-theme="c"] .home-industry-list>span{background:#17252B;color:#F5EAD7}
  .fed-policy-panel{max-width:none;margin:0;padding:20px 22px}.fed-policy-head{display:flex;align-items:flex-start;justify-content:space-between;gap:16px;margin-bottom:14px}.fed-policy-head h2{margin:0 0 4px;font-size:20px}.fed-policy-head p{margin:0;color:var(--mocha);font-size:12px;line-height:1.55}.fed-policy-status{display:flex;gap:6px;flex-wrap:wrap;justify-content:flex-end}.policy-status{white-space:nowrap;border:1px solid var(--grounds);border-radius:999px;padding:4px 8px;font-size:11px;color:var(--mocha);background:var(--foam)}.policy-status.ok{color:var(--up);border-color:color-mix(in srgb,var(--up) 45%,var(--grounds))}.policy-status.warn{color:var(--caramel-2)}.policy-status.danger{color:var(--down)}
  .fed-policy-grid{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:10px}.fed-policy-block{border:1px solid var(--grounds);border-radius:12px;padding:13px 14px;background:color-mix(in srgb,var(--foam) 88%,var(--grounds))}.fed-policy-block h3{font-size:15px;margin:0 0 9px}.policy-kpis{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:7px}.policy-kpi{min-width:0}.policy-kpi small{display:block;color:var(--mocha);font-size:11px;line-height:1.35}.policy-kpi b{display:block;margin-top:2px;font:700 17px var(--font-num);overflow-wrap:anywhere}.policy-note{margin:9px 0 0;color:var(--mocha);font-size:11px;line-height:1.55}.auction-list{margin:8px 0 0;padding:0;list-style:none;color:var(--mocha);font-size:11px;line-height:1.55}.auction-list b{color:var(--espresso)}.fomc-line{margin-top:10px;padding:10px 13px;border-left:4px solid var(--caramel);background:color-mix(in srgb,var(--foam) 82%,var(--caramel) 18%);font-size:12px}.fed-reading{margin-top:12px}.fed-source{margin-top:10px;color:var(--mocha);font-size:10.5px;line-height:1.5}.fed-source a{color:var(--caramel-2)}
  .policy-board{margin:0;padding:0;list-style:none;border-top:1px solid var(--grounds)}.policy-board li{display:grid;grid-template-columns:112px minmax(0,.9fr) minmax(0,1.3fr);align-items:center;gap:14px;padding:12px 2px;border-bottom:1px dashed var(--grounds)}.policy-board-label{font-weight:800;color:var(--espresso)}.policy-board-data{font:700 13px/1.55 var(--font-num);color:var(--espresso)}.policy-board-read{font-size:12px;line-height:1.6;color:var(--mocha)}.policy-board-read b{color:var(--caramel-2)}.policy-board-meta{display:flex;align-items:center;justify-content:space-between;gap:12px;flex-wrap:wrap;margin-top:11px}.policy-board-limit{margin:0;max-width:650px;color:var(--mocha);font-size:10.5px;line-height:1.55}
  @media(max-width:560px){.fed-policy-panel{padding:17px 16px}.fed-policy-head{display:block}.fed-policy-status{justify-content:flex-start;margin-top:10px}.fed-policy-grid{grid-template-columns:1fr}.policy-kpis{grid-template-columns:1fr 1fr}.policy-board li{grid-template-columns:1fr;gap:3px;padding:12px 0}.policy-board-label{color:var(--caramel-2)}.policy-board-data{font-size:13px}.policy-board-read{font-size:11.5px}}
  @media(max-width:560px){.home-actions,.home-action-panel .home-actions{grid-template-columns:1fr}.updnote{font-size:14px}.updnote small{font-size:12.5px}}
  @media(max-width:560px){.reading-row{grid-template-columns:54px 1fr}.ind-change-grid,.ind-stock-list{grid-template-columns:1fr}}
  @media(max-width:560px){.market-now-grid{grid-template-columns:1fr}.market-now-hero{padding:17px 18px}.market-now-title h1{font-size:27px}.market-now-badge{padding:6px 13px}.market-return-row{grid-template-columns:105px 1fr 88px}.market-return-row>span{padding:10px 8px}.market-return-main b,.market-return-med b{font-size:16px}.market-chart-head{align-items:flex-start;flex-direction:column}.market-periods{width:100%}.market-periods button{flex:1;padding:7px 5px}}
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
  .mk-stage { flex-shrink:0; border:1px solid var(--grounds); border-radius:999px;
             padding:3px 8px; font-family:var(--font-num); font-size:11px;
             font-weight:700; color:var(--caramel-2); background:var(--milk); }
  /* 本日推薦：沿用市場階段卡片的寬度與圓角，讓兩者看起來是同一組東西 */
  .hs-box { max-width:560px; margin:0 auto 16px; display:block;
           background:var(--foam); border:1.5px solid var(--grounds);
           border-radius:18px; padding:14px 18px; box-shadow:var(--shadow);
           text-decoration:none; color:var(--espresso);
           transition:border-color .15s, transform .15s; }
  .hs-box:hover { border-color:var(--caramel); transform:translateY(-1px); }
  .hs-head { display:flex; align-items:baseline; gap:8px; }
  .hs-head b { font-family:var(--font-head); font-size:15px; }
  .hs-n { font-family:var(--font-num); font-size:26px; color:var(--caramel-2);
           font-weight:700; margin-left:auto; }
  .hs-unit { font-size:13px; color:var(--mocha); }
  .hs-list { display:block; margin-top:8px; font-size:13px; color:var(--mocha);
           line-height:1.7; overflow:hidden; text-overflow:ellipsis;
           display:-webkit-box; -webkit-line-clamp:2; -webkit-box-orient:vertical; }
  .hs-sub { display:block; margin-top:8px; font-size:12px; color:var(--mocha); }
  .hs-go { display:block; margin-top:8px; font-size:13px; color:var(--caramel-2); }
  .mk-body { padding:2px 16px 14px; border-top:1px solid var(--grounds);
           font-size:14px; color:#555; line-height:1.9; }
  .mk-body b { color:var(--espresso); }
  .life-head { display:flex; align-items:baseline; justify-content:space-between;
              gap:10px; margin:14px 0 10px; }
  .life-head b { font-family:var(--font-head); color:var(--espresso); font-size:15px; }
  .life-head span { color:var(--mocha); font-size:12px; }
  .life-track { display:grid; grid-template-columns:repeat(3,minmax(0,1fr)); gap:8px; }
  .life-step { min-width:0; border:1.5px solid var(--grounds); border-radius:12px;
               padding:10px; background:rgba(255,255,255,.46); color:var(--mocha); }
  .life-step.on { border-color:var(--caramel); background:var(--milk);
                  box-shadow:0 0 0 2px rgba(166,103,65,.09); color:var(--espresso); }
  .life-top { display:flex; align-items:center; gap:7px; }
  .life-no { width:22px; height:22px; border-radius:50%; display:inline-flex;
             align-items:center; justify-content:center; flex-shrink:0;
             background:var(--grounds); color:var(--espresso); font:700 11px var(--font-num); }
  .life-step.on .life-no { background:var(--caramel); color:#fff; }
  .life-name { font-family:var(--font-head); font-size:13px; font-weight:700; }
  .life-hint { display:block; margin:6px 0 0 29px; font-size:11.5px; line-height:1.45; }
  .life-now { display:inline-block; margin:7px 0 0 29px; padding:2px 7px;
              border-radius:999px; background:var(--caramel); color:#fff;
              font-size:10.5px; font-weight:700; }
  .life-note { margin:11px 0 13px; color:var(--mocha); font-size:12px; line-height:1.7; }
  .life-intro { margin-top:12px; padding-top:12px; border-top:1px solid var(--grounds); }
  .mk-num { font-family:var(--font-num); font-size:12px; color:var(--mocha);
           flex-shrink:0; }
  @media(max-width:520px){
    .mk-main { flex-direction:column; align-items:flex-start; gap:2px; }
    .mk-stage { align-self:flex-start; }
    .mk-num { display:none; }
    .life-track { grid-template-columns:repeat(2,minmax(0,1fr)); }
    .life-step { padding:9px 8px; }
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
  .ind-tabs{display:flex;gap:7px;flex-wrap:wrap;margin:10px 0 14px}
  .ind-tabs button{border:1px solid var(--grounds);background:var(--milk);color:var(--mocha);border-radius:20px;padding:7px 13px;cursor:pointer;font-weight:700}
  .ind-tabs button.on{background:var(--espresso);color:var(--milk);border-color:var(--espresso)}
  .ind-rank{display:grid;gap:8px}.ind-row{border:1px solid var(--grounds);border-radius:12px;padding:11px 12px;background:rgba(255,255,255,.42)}
  .ind-row summary{display:grid;grid-template-columns:minmax(110px,1fr) repeat(4,minmax(68px,auto));gap:10px;align-items:center;cursor:pointer;list-style:none}
  .ind-row summary::-webkit-details-marker{display:none}.ind-name{font-weight:800;color:var(--espresso)}.ind-num{text-align:right;font-family:var(--font-num)}
  .ind-leaders{margin-top:10px;padding-top:9px;border-top:1px dashed var(--grounds)}.ind-leader{display:grid;grid-template-columns:1fr repeat(3,70px);gap:8px;padding:6px 0;font-size:12.5px}
  .ind-leader a{color:inherit;text-decoration:none}.ind-leader a:hover{color:var(--caramel-2)}
  .ind-quad{display:grid;grid-template-columns:1fr 1fr;gap:8px}.ind-q{min-height:120px;border-radius:12px;padding:12px;background:rgba(255,255,255,.48);border:1px solid var(--grounds)}
  .ind-q b{display:block;margin-bottom:7px}.ind-chip{display:inline-block;margin:3px 3px 0 0;padding:4px 8px;border-radius:14px;background:var(--milk);color:var(--mocha);font-size:12px}
  html[data-theme="c"] .ind-row,html[data-theme="c"] .ind-q{background:#21343A}html[data-theme="c"] .ind-tabs button.on{background:#D2A65F;color:#17252B}
  @media(max-width:600px){.ind-row summary{grid-template-columns:1fr 1fr}.ind-name{grid-column:1/-1}.ind-leader{grid-template-columns:1fr 64px}.ind-leader span:nth-child(n+3){text-align:right}.ind-quad{grid-template-columns:1fr}}

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
  #themeBtn{height:40px;padding:0 13px;border-radius:20px;border:1.5px solid var(--grounds);background:var(--foam);color:var(--caramel-2);cursor:pointer;font-size:13px;font-weight:700;box-shadow:var(--shadow);white-space:nowrap}
  #themePicker{position:fixed;z-index:120;top:64px;right:14px;width:238px;padding:12px;background:var(--foam);border:1.5px solid var(--grounds);border-radius:16px;box-shadow:var(--shadow);display:none}#themePicker.show{display:block}
  .theme-picker-title{font-weight:700;font-size:13px;margin:0 0 8px;color:var(--espresso)}.theme-choice{width:100%;display:grid;grid-template-columns:38px 1fr 20px;gap:9px;align-items:center;border:0;border-radius:11px;padding:9px;background:transparent;color:var(--espresso);text-align:left;cursor:pointer}.theme-choice:hover,.theme-choice.on{background:var(--milk)}.theme-choice b{display:block;font-size:13px}.theme-choice small{display:block;color:var(--mocha);font-size:10.5px}.theme-check{font-weight:700;color:var(--caramel-2)}.theme-swatches{display:grid;grid-template-columns:repeat(2,15px);gap:3px}.theme-swatches i{height:15px;border-radius:50%;border:1px solid rgba(0,0,0,.12)}
  html[data-theme="c"] .card,html[data-theme="c"] .market-data-card,html[data-theme="c"] .market-now-hero,html[data-theme="c"] .home-action-panel{color:var(--espresso)}
  html[data-theme="c"] .market-now-hero,html[data-theme="c"] .market-data-card{background:var(--foam)!important}
  html[data-theme="c"] .market-periods button.on{background:var(--caramel-2);color:#17252B}
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
  .site-footer { max-width:1180px; margin:0 auto; padding:0 18px calc(28px + env(safe-area-inset-bottom)); text-align:center;
                 color:var(--mocha); font-size:12px; line-height:1.8; }
  .site-footer a { color:var(--caramel-2); text-decoration:none; font-weight:700; }
  .site-footer a:hover { text-decoration:underline; }
  .site-version { margin-top:6px; font-size:11px; opacity:.68; letter-spacing:.02em; }
</style>
</head>
<body>

<button id="menuBtn" aria-label="選單" data-i18n-aria="ui.menu"><span></span><span></span><span></span></button>
<div id="topBtns">
  <a id="mktBtn" href="__TW_URL__" title="切換到台股咖啡館" aria-label="切換到台股咖啡館" data-i18n-aria="ui.mkt.aria">🇹🇼 <span data-i18n="ui.mkt">台股</span></a>
  <button id="themeBtn" type="button" aria-label="選擇咖啡館外觀" aria-expanded="false">☕ 外觀</button>
  <button id="langBtn" title="切換公司與產業的顯示語言">EN</button>
</div>
<div id="themePicker" role="dialog" aria-label="咖啡館外觀"><div class="theme-picker-title"><span class="q-zh">選擇咖啡館外觀</span><span class="q-en" style="display:none">Choose café theme</span></div>
<button class="theme-choice" data-theme-choice="b"><span class="theme-swatches"><i style="background:#F3EFE2"></i><i style="background:#42664C"></i><i style="background:#A45E2A"></i><i style="background:#FFFDF7"></i></span><span><b>B・京都喫茶</b><small>Kyoto Kissaten</small></span><span class="theme-check"></span></button>
<button class="theme-choice" data-theme-choice="c"><span class="theme-swatches"><i style="background:#17252B"></i><i style="background:#21343A"></i><i style="background:#D2A65F"></i><i style="background:#F5EAD7"></i></span><span><b>C・午夜爵士</b><small>Midnight Jazz</small></span><span class="theme-check"></span></button>
<button class="theme-choice" data-theme-choice="d"><span class="theme-swatches"><i style="background:#F5EAE5"></i><i style="background:#98574C"></i><i style="background:#7B6752"></i><i style="background:#FFF9F5"></i></span><span><b>D・玫瑰摩卡</b><small>Rose Mocha</small></span><span class="theme-check"></span></button></div>
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
  <a class="navitem active" data-page="home" href="/"><i>☕</i><b data-i18n="nav.home">菜單首頁</b><small data-i18n="nav.home.sub">今天適合出手嗎</small></a>
  <div class="nav-section"><span class="q-zh">研究市場</span><span class="q-en" style="display:none">Research</span></div>
  <details class="navgroup">
    <summary><i>📋</i><b><span class="q-zh">選股與產業</span><span class="q-en" style="display:none">Stocks & sectors</span></b><small><span class="q-zh">強勢股・產業輪動・拉回買點</span><span class="q-en" style="display:none">Momentum, rotation and pullbacks</span></small></summary>
    <a class="navitem sub" data-page="p1" href="/screener"><i>🔥</i><b data-i18n="p1.title">找強勢股</b><small data-i18n="nav.screen.sub">找出強勢主流題材股</small></a>
    <a class="navitem sub" data-page="pind" href="/industries"><i>🧱</i><b data-i18n="nav.industry">產業分析</b><small data-i18n="nav.industry.sub">動能擴散・產業領先股</small></a>
    <a class="navitem sub" data-page="p3" href="/pullback"><i>⭐</i><b data-i18n="p3.title">拉回找買點</b><small data-i18n="nav.pull.sub">收盤回到均線±3%</small></a>
    <a class="navitem sub" data-page="pgrow" href="/growth"><i>🌱</i><b data-i18n="grow.title">長期成長股列表</b><small data-i18n="nav.grow.sub">十年累計・年化報酬</small></a>
  </details>
  <details class="navgroup">
    <summary><i>🌤️</i><b><span class="q-zh">市場工具</span><span class="q-en" style="display:none">Market tools</span></b><small><span class="q-zh">總經・正2・均線位置</span><span class="q-en" style="display:none">Macro, leverage and moving averages</span></small></summary>
    <a class="navitem sub" data-page="pmac" href="/macro"><i>🏦</i><b data-i18n="pmac.title">利率與購買力</b><small data-i18n="nav.macro.sub">美債 2Y・10Y・CPI</small></a>
    <a class="navitem sub" data-page="p11" href="/consolidation"><i>🧭</i><b data-i18n="lev.title">正2 逐月績效</b><small data-i18n="nav.lev.sub">QLD・實際倍數</small></a>
    <a class="navitem sub" data-page="p10" href="/deduction"><i>📐</i><b data-i18n="nav.deduct">均線扣抵法</b><small data-i18n="nav.deduct.sub">50／100／150MA 何時追上</small></a>
  </details>
  <div class="nav-section"><span class="q-zh">我的工具</span><span class="q-en" style="display:none">My tools</span></div>
  <details class="navgroup">
    <summary><i>⭐</i><b data-i18n="nav.mine">我的自選股</b><small data-i18n="nav.mine.sub">績效・同期比較・風控・提醒</small></summary>
    <a class="navitem sub" data-page="p7" href="/twr"><i>📈</i><b data-i18n="p7.title">我的績效</b><small data-i18n="nav.twr.sub">TWR 報酬率試算</small></a>
    <a class="navitem sub" data-page="p12" href="/comparison"><i>⚖️</i><b data-i18n="p12.title">同期比較</b><small data-i18n="nav.compare.sub">如果當初買了別檔</small></a>
    <a class="navitem sub" data-page="p8" href="/risk"><i>🛡️</i><b data-i18n="p8.title">風控管理</b><small data-i18n="nav.risk.sub">ATR・波動率・趨勢・Beta</small></a>
    <a class="navitem sub" data-page="p4" href="/alerts"><i>🔔</i><b data-i18n="p4.title">推播通知</b><small data-i18n="nav.alert.sub">收盤到價提醒（測試中）</small></a>
  </details>
  <div class="nav-section"><span class="q-zh">學習與其他</span><span class="q-en" style="display:none">Learn & more</span></div>
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

  <!-- ============ 今日市場（版面照台股版）============
       結論秒開、細節手動：
         · __PHASE_BAR__ 只讀快取、零成本，一進來就看得到答案
         · 「大盤詳細數據」要展開才去打 /api/breadth，
           不讓每個訪客都觸發後端工作（台股版踩過，見台股 5.4） -->
  <div class="home-dashboard">
__HOME_MARKET_DASHBOARD__

__UPDATE_NOTE__

__FED_POLICY_PANEL__

  <section class="home-action-panel"><div class="qhead"><span class="q-zh">今日觀察 · ACTIONS</span><span class="q-en" style="display:none">WHAT TO EXPLORE</span></div>
  <div class="home-section-note"><span class="q-zh">先看近期選股結果，再查看強勢股與產業集中方向。以下都是過去資料的整理，不是未來預測。</span><span class="q-en" style="display:none">Start with realised selection results, then explore strong stocks and sector concentration. Nothing here predicts the future.</span></div>
  <div class="home-actions">
    __HOME_SCREEN__
    <a class="card home-industry" href="/industries">
      <div class="home-industry-head"><h2><span class="q-zh">產業速報</span><span class="q-en" style="display:none">Sector brief</span></h2><span><span class="q-zh">完整分析 →</span><span class="q-en" style="display:none">Full analysis →</span></span></div>
      <div id="homeIndustryBrief" class="home-industry-list">__HOME_INDUSTRY_BRIEF__</div>
    </a>
  </div>
  </section></div>

  <!-- ⚠️ 這裡原本是「找強勢股／拉回找買點」兩張 menu-item 卡。
       2026-08-07 移除 —— 左側選單已經有同樣的入口，首頁再放一次只是重複，
       換成名言卡（與台股版共用同一份 quotes/）。 -->
  <div class="qhead" data-i18n="home.qhead">今日供應 · QUOTES</div>
  __PHASE_BAR__
  <div id="qbox">
__QUOTES_HTML__
  </div>
  <div class="qmore-wrap">
    <button class="qmore" id="qmoreBtn" onclick="drawQuote()" data-i18n="home.more">再抽一張 ☕</button>
  </div>
  <div class="qsrc">__QUOTE_SRC__</div>
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
      <p>篩完如果檔數太多，上方的四個下拉可以繼續縮小範圍：<b>產業</b>、
      <b>季 EPS 年增</b>、<b>均線排列</b>與<b>創新高程度</b>，四個條件是 AND 關係。
      <b>產業分布本身就是訊息</b>——如果三十檔裡有十二檔是同一個產業，
      那多半就是當下的主流題材，而族群行情的持續性遠高於單一個股。</p>
      <p><b>三種常用的組合</b>：
      ①「站上 50 日線 ＋ 嚴格多頭」找的是趨勢已經確立、還在走的股票；
      ②「站上 10 日線 ＋ 近三日完全符合」找的是短線剛轉強、連續站穩的股票；
      ③「跌破 150 日線 ＋ 嚴格空頭」則是反過來找轉弱的標的，
      可以拿來檢查手上的持股該不該減碼。</p>
      <p>每一列還會顯示<b>創新高等級</b>（3 個月到 5 年）與<b>季報營收／EPS 年增率</b>。
      前者告訴你這檔股票在自己的歷史裡站在什麼位置，後者是基本面有沒有跟上的粗略檢查——
      ⚠️ 美股只公布季報，所以那個數字可能已經是兩三個月前的事。</p>
      <p><b>什麼時候不要用這頁</b>：大盤處在逆風階段時，這裡照樣會篩出幾十檔
      「相對強勢」的股票，但那不代表可以進場。先看首頁的市場階段再決定要不要出手。</p>
      <p><b>適合誰</b>：持有數個月的動量交易者。這裡是收盤資料，做不了當沖。
      想找的是「回檔後的進場點」而不是「現在誰最強」的話，請改用<b>拉回找買點</b>。</p>
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

  <div class="card"><h2><span class="stepno">06</span><span data-i18n="screen.advanced">基本面與進階資料</span></h2>
    <label class="opt"><input type="checkbox" id="epsHalves1"><span data-i18n="screen.eps">追加近兩年 H1／H2 EPS</span></label>
    <label class="opt"><input type="checkbox" id="valuation1"><span data-i18n="screen.valuation">顯示本益比與殖利率</span></label>
    <label class="opt"><input type="checkbox" id="structureHistory1"><span data-i18n="screen.structure">飆股前期結構回溯（1～5 年）</span></label>
    <div style="font-size:12px;color:var(--mocha);margin-top:7px;line-height:1.7" data-i18n="screen.epsNote">H1 是上半年兩季 EPS 合計，H2 是下半年兩季 EPS 合計；勾選後在公司名稱下方展開，不增加表格欄數。</div>
    <div style="font-size:12px;color:var(--mocha);margin-top:4px;line-height:1.7" data-i18n="screen.valuationNote">本益比與殖利率預設不顯示；勾選後才載入並增加兩欄。</div>
    <div style="font-size:12px;color:var(--mocha);margin-top:4px;line-height:1.7" data-i18n="screen.structureNote">回溯前高、最大回落、整理月數與突破時點，並顯示可拖曳平移的長期收盤價圖。美股使用既有五年收盤快取。</div>
  </div>

  <div class="screen-tools" id="screenTools1"></div>
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
      <p>結果依<b>乖離的絕對值</b>排序（乖離＝收盤價距離均線幾 %），
      最上面的就是貼得最近的。正乖離代表還在均線上方、負乖離代表已經跌破一點點——
      同樣是 ±3% 以內，這兩種的意義並不一樣。</p>
      <p><b>⚠️ 這頁用的是收盤價，不是盤中現價。</b>
      理由是定義必須穩定：用現價算，同一檔股票在早上十點與下午三點會給出不同答案，
      清單會整天跳動。盤中現價只出現在結果表格裡當參考，不參與篩選。</p>
      <p><b>怎麼分辨「健康的回檔」與「趨勢正在轉弱」</b>：
      回檔到均線時，均線排列若仍是多頭、而且成交沒有異常放大，多半只是休息；
      如果同一段期間裡短均線已經跌破長均線（排列變成空頭或糾結），
      那就不是回檔，是趨勢在換方向。這也是為什麼建議搭配排列條件一起篩。</p>
      <p><b>這頁不會告訴你的事</b>：它只回答「現在誰站在均線附近」，
      不回答「這檔股票值不值得買」。要先有標的，才輪到談進場點——
      標的請用<b>找強勢股</b>先篩出來。</p>
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

  <div class="card"><h2><span class="stepno">04</span><span data-i18n="screen.advanced">基本面與進階資料</span></h2>
    <label class="opt"><input type="checkbox" id="epsHalves3"><span data-i18n="screen.eps">追加近兩年 H1／H2 EPS</span></label>
    <label class="opt"><input type="checkbox" id="valuation3"><span data-i18n="screen.valuation">顯示本益比與殖利率</span></label>
    <label class="opt"><input type="checkbox" id="structureHistory3"><span data-i18n="screen.structure">飆股前期結構回溯（1～5 年）</span></label>
    <div style="font-size:12px;color:var(--mocha);margin-top:7px;line-height:1.7" data-i18n="screen.epsNote">H1 是上半年兩季 EPS 合計，H2 是下半年兩季 EPS 合計；勾選後在公司名稱下方展開，不增加表格欄數。</div>
    <div style="font-size:12px;color:var(--mocha);margin-top:4px;line-height:1.7" data-i18n="screen.valuationNote">本益比與殖利率預設不顯示；勾選後才載入並增加兩欄。</div>
    <div style="font-size:12px;color:var(--mocha);margin-top:4px;line-height:1.7" data-i18n="screen.structureNote">回溯前高、最大回落、整理月數與突破時點，並顯示可拖曳平移的長期收盤價圖。美股使用既有五年收盤快取。</div>
  </div>

  <div class="screen-tools" id="screenTools3"></div>
  <button class="gobtn" id="go3" data-i18n="btn.screen">開始篩選</button>
  <div class="status" id="status3"></div>
  <div id="result3"></div>
</div>

<!-- ============ 強勢股整理觀察 ============ -->
<div class="page" id="p11">
  <h2 class="ptitle" data-i18n="lev.title">正2 逐月績效</h2>
  <details class="pgintro" open>
    <summary data-i18n="lev.introT">槓桿的實際倍數，不會等於 2</summary>
    <div class="pgintro-b" data-i18n-html="lev.intro"><p>這裡列出 <b>QLD（ProShares Ultra QQQ，2 倍納斯達克100）</b>最近兩年的逐月報酬，對照納斯達克綜合指數，並算出每個月的<b>實際倍數</b>。</p><p><b>累積報酬的倍數不會剛好是 2。</b>槓桿 ETF 每日再平衡，趨勢順的時候大於 2、來回震盪的時候小於 2——這叫路徑依賴。連續兩個月 +10%／−10%，大盤累積 −1%，兩倍卻是 −4%。</p><p>⚠️ QLD 追蹤的是<b>納斯達克100</b>（非金融前 100 大）的單日正向兩倍，<b>不是綜合指數</b>（三千多檔）。所以「實際倍數」那一欄本來就不會乾淨；大盤月報酬接近 0 時分母太小，數字沒有意義，以「—」略過。</p></div>
  </details>
  <button class="gobtn" id="goLev" data-i18n="lev.run">查看逐月績效</button>
  <div class="status" id="statusLev"></div>
  <div id="resultLev"></div>
</div>

<!-- ============ 長期成長股列表 ============ -->
<div class="page" id="pgrow">
  <h2 class="ptitle" data-i18n="grow.title">長期成長股列表</h2>
  <details class="pgintro" open>
    <summary data-i18n="grow.introT">十年下來，誰真的漲上去了</summary>
    <div class="pgintro-b" data-i18n-html="grow.intro"><p>這裡列出<b>市值前 300 大</b>美股<b>固定回溯十年</b>的累計漲幅與年化報酬率，可以依兩者任一排序。所有個股用<b>同一個起跑點</b>，累計漲幅才能互相比較——若改用各自的上市日，期間長短不同，排名就沒有意義。</p><p><b>⚠️ 這份清單回答的是「現在的大公司過去十年漲了多少」，不是「十年前該買什麼」。</b>股票池是<b>今天</b>的前 300 大：十年前還很小、後來長大的公司被預先放進來，十年前很大、後來衰退掉出榜外的則完全看不到。這叫存活者偏誤加前視偏誤，會讓整份清單看起來比實際好很多。</p><p><b>⚠️ 未還原配息。</b>報價已還原拆股，但沒有還原股息，所以<b>高股息個股的報酬被系統性低估</b>——年配 6~7% 的十年下來可能少算五成以上。排名前段集中在科技股，有一部分是這個原因造成的。<b>台股站的同名頁面是含息的，兩邊的數字不能並排比較。</b></p><p><b>年數欄位要跟年化一起看。</b>上市不滿十年的個股會標示實際年數；短期間內一段暴漲會被年化放大成很誇張的數字。</p></div>
  </details>
  <div class="status" id="statusGrow"></div>
  <div id="resultGrow"></div>
</div>

<div class="page" id="pmac">
  <h2 class="ptitle" data-i18n="pmac.title">利率與購買力</h2>
  <details class="pgintro" open>
    <summary data-i18n="pmac.introT">投資報酬要先跨過利率與通膨</summary>
    <div class="pgintro-b" data-i18n-html="pmac.intro">
      <p>投資賺 10%，不代表購買力增加 10%。美國公債殖利率代表美元資金在低信用風險下可取得的報酬門檻；投資報酬減去相近期間的公債利率，才是承擔市場風險換來的粗略超額報酬。</p>
      <p><b>本年度累積 CPI</b>比較最新 CPI 與去年 12 月，回答今年以來物價漲了多少；<b>近五年</b>與<b>近十年累積 CPI</b>比較最新月份與五年／十年前同月。<b>兩個期間都要看</b>：五年窗口把 2021～2023 那波通膨算滿，十年窗口把它稀釋掉，兩者年化可以差快一個百分點——<b>用哪一個當基準會得到不同的實質報酬結論</b>，請挑跟你持有期間相近的那一個。</p>
      <p>實質報酬應用「(1＋名目報酬) ÷ (1＋同期通膨率) − 1」計算。公債利率是機會成本，CPI 才是購買力調整，兩者不能混為一談。</p>
    </div>
  </details>
  <div class="card" style="padding:14px 16px">
    <div style="font-size:13px;color:#555;line-height:1.8" data-i18n="pmac.disc">殖利率為年率；CPI 為期間累積漲幅，並非年化數字。資料是最近可用值、非即時報價，不構成投資建議。</div>
  </div>
  <div id="macroBox"></div>
  <div class="card">
    <h2>為什麼要關注公債利率？</h2>
    <div class="artbody" style="border-top:0;padding-top:0;margin-top:0">
      <p>公債殖利率是資金的機會成本，也是股票、房貸、公司融資與信用市場估值的共同底座。殖利率上升，未來現金流折回今天的價值通常下降；殖利率下降，金融條件通常較寬鬆，但也可能反映市場對景氣轉弱的擔心。</p>
      <h3>2Y：市場看 Fed 接下來要怎麼做</h3><p>2 年期對未來幾次升降息與通膨預期特別敏感。快速上升常代表市場把利率「更高、更久」重新計價；快速下降則常代表降息預期升溫或經濟風險增加。</p>
      <h3>10Y：全球金融市場的重要定價基準</h3><p>10 年期是全球重要的長期折現率。股票估值、公司融資、房貸與信用市場都會受到它影響，因此突破或跌破長期區間往往不只是債市事件。</p>
      <h3>30Y：美國長期信用、財政與無風險資產回報</h3><p>30 年期反映長期通膨、財政赤字、債券供給與期限風險。30Y 突然上升，可能表示市場要求更高的長期補償；快速下降，則可能反映避險需求或長期成長預期轉弱。應和 2Y、10Y 及整條殖利率曲線一起判讀。</p>
    </div>
  </div>
  <div class="card">
    <h2 data-i18n="pmac.src">資料來源與算法</h2>
    <div style="font-size:13px;color:#555;line-height:1.85" data-i18n-html="pmac.source">
      美國 2 年期、10 年期與 30 年期使用美國財政部 Daily Treasury Par Yield Curve Rates；三年圖關鍵區間以期間內第 20／80 百分位估算。CPI 使用美國勞工統計局經季節調整的全城市消費者物價指數 CUSR0000SA0。<br><br>
      本年度累積 CPI＝最新指數 ÷ 去年 12 月指數 − 1；近五年／近十年累積 CPI＝最新指數 ÷ 五年／十年前同月指數 − 1。皆為期間累積漲幅，不是年化值。<br><br>
      Source: U.S. Department of the Treasury and U.S. Bureau of Labor Statistics
      （<a href="https://home.treasury.gov/resource-center/data-chart-center/interest-rates" target="_blank" rel="noopener" style="color:var(--primary)">U.S. Treasury</a>；
      <a href="https://www.bls.gov/cpi/" target="_blank" rel="noopener" style="color:var(--primary)">BLS CPI</a>）。
    </div>
  </div>
</div>

<!-- ============ 產業分析 ============ -->
<div class="page" id="pind">
  <h2 class="ptitle" data-i18n="industry.title">產業分析</h2>
  <details class="pgintro" open>
    <summary data-i18n="industry.introT">資金集中在哪些產業，漲勢有沒有擴散？</summary>
    <div class="pgintro-b" data-i18n-html="industry.intro"><p>以目前市值前 300 大美股依 Nasdaq Sector 分組，比較<b>20／60 日報酬中位數</b>與前一期變化，再搭配上漲家數比例及前三檔正報酬集中度。重點是確認整個 Sector 是否轉強，而非只列漲幅前三名。</p><p>點擊產業即可展開完整股票清單。樣本少於 5 檔不參與排名；股票池是今日前 300 大，包含存活者偏誤，所有結論只回顧過去。</p></div>
  </details>
  <div class="card"><h2 data-i18n="industry.quad">產業四象限</h2><div id="indQuad" class="ind-quad"><div class="status" data-i18n="industry.loading">載入中…</div></div></div>
  <div class="card"><h2 data-i18n="industry.rank">產業強弱排名</h2>
    <div class="ind-tabs" id="indTabs">
      <button class="on" data-sort="median20" data-i18n="industry.m20">20日動能</button>
      <button data-sort="median60" data-i18n="industry.m60">60日趨勢</button>
      <button data-sort="win20_pct" data-i18n="industry.win">上漲比例</button>
      <button data-sort="above50_pct" data-i18n="industry.above">站上50日線</button>
      <button data-sort="newhigh_pct" data-i18n="industry.high">創新高</button>
    </div>
    <div class="status" id="indStatus"></div>
    <div id="indRank" class="ind-rank"></div>
  </div>
</div>

<!-- ============ 我的績效（TWR）============ -->
<div class="page" id="p7">
  <h2 class="ptitle" data-i18n="p7.title">我的績效</h2>

  <details class="pgintro">
    <summary data-i18n="p7.introT">你的報酬率，很可能算錯了</summary>
    <div class="pgintro-b" data-i18n-html="p7.intro">
      <p>多數人算報酬率的方式是「現在總資產 ÷ 投入本金 − 1」。
      只要中途沒有存錢或提錢，這樣算沒問題；<b>但只要有一次不定期的匯入，這個數字就會失真</b>。</p>
      <p>舉個極端的例子：年初 100 萬，上半年賠掉 20% 剩 80 萬；
      七月你又匯入 100 萬，下半年賺 10%，年底變成 198 萬。
      用「總資產 ÷ 總投入」算是 −1%，看起來只是小虧；
      但你真正的操作結果是「先賠 20%、再賺 10%」，也就是 <b>−12%</b>。
      差別來自於：<b>你在賠錢之後才把大部分的錢投進來</b>，那不是操作能力，是時機的巧合。</p>
      <p><b>時間加權報酬率（TWR）</b>就是為了拆掉這個影響：把每個月當成一段獨立的期間，
      各自算出當月報酬，再連乘起來。存入與提出多少完全不影響結果——
      這也是基金與代操績效的標準算法，因為經理人無法決定客戶什麼時候匯錢進來。</p>
      <p><b>跟 IRR（金額加權）差在哪</b>：IRR 會把「你投入多少、什麼時候投入」一起算進去，
      回答的是「我這筆錢賺了多少」；TWR 回答的是「我的選股與進出場做得好不好」。
      想評估自己的操作能力，要看 TWR；想知道實際口袋裡多了多少，看 IRR。</p>
      <p><b>怎麼填</b>：只需要兩欄——當月<b>淨存入</b>（存入減提出，提領填負數）與
      <b>月底總資產</b>（現金＋所有持股市值）。未到的月份留白即可，
      系統只計算有填的區間，並同時給你累積報酬率與年化報酬率。</p>
      <p><b>資料只存在這台裝置的瀏覽器</b>（localStorage），不會上傳、伺服器也沒有帳號系統。
      好處是不必註冊，代價是換裝置或清除瀏覽資料就會不見——這點先講清楚，不假裝有同步。</p>
    </div>
  </details>

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

  <div class="card" style="margin-top:16px">
    <h2 data-i18n="twr.vs">挑戰大盤</h2>
    <div style="font-size:12px;color:#888;line-height:1.7;margin-bottom:10px" data-i18n="twr.vsNote">查看納斯達克綜合指數最近兩年的每月漲跌幅、年度報酬率與當年度 CPI，和你的績效放在同一尺度比較。</div>
    <button class="gobtn" id="twMarket" data-i18n="twr.vsBtn">查看大盤近兩年表現</button>
    <div class="status" id="statusMkt"></div>
    <div id="mktResult"></div>
  </div>
</div>

<!-- ============ 我的自選股：同期比較 ============ -->
<div class="page" id="p12">
  <h2 class="ptitle" data-i18n="p12.title">同期比較</h2>
  <details class="pgintro">
    <summary data-i18n="cmp.introT">當初沒買的股票，後來漲了多少？</summary>
    <div class="pgintro-b" data-i18n-html="cmp.intro">
      <p>輸入你實際買進的 A 股票、日期、價格與股數，系統會算出當時投入的美元本金。</p>
      <p>再挑 B、C、D，假設在同一個交易日用<b>完全相同的本金買整股</b>，未用完的錢保留現金，
      比較到最新共同收盤日的總值與報酬率，直接看見選股造成的機會成本。</p>
      <p>資料只存在這台裝置。報酬採拆股一致的歷史收盤，但不含手續費、稅與現金股利；
      最長約可比較最近五年。</p>
    </div>
  </details>

  <div class="card">
    <h2><span class="stepno">01</span><span data-i18n="cmp.actual">輸入 A 股票的實際買進資料</span></h2>
    <div class="stockpick" style="position:relative;margin-bottom:12px">
      <input id="cmpASearch" type="text" autocomplete="off" data-i18n-ph="cmp.aPh"
             placeholder="搜尋 A 股票，例如 AAPL 或 Apple">
      <div id="cmpASuggest" class="suggest"></div>
      <div id="cmpAPicked" class="picked" style="display:none"></div>
    </div>
    <div class="cmp-form">
      <div class="cmp-field"><label data-i18n="cmp.date">買入日期</label>
        <input id="cmpDate" type="date"></div>
      <div class="cmp-field"><label data-i18n="cmp.price">A 實際買入價</label>
        <input id="cmpPrice" type="number" min="0.0001" step="0.01" inputmode="decimal" placeholder="例如 180.50"></div>
      <div class="cmp-field"><label data-i18n="cmp.shares">A 實際買入股數</label>
        <input id="cmpShares" type="number" min="0.0001" step="0.0001" inputmode="decimal" placeholder="例如 10"></div>
      <div class="cmp-field"><label data-i18n="cmp.principal">實際投入本金</label>
        <input id="cmpPrincipal" type="text" readonly value="—"></div>
    </div>
  </div>

  <div class="card">
    <h2><span class="stepno">02</span><span data-i18n="cmp.peers">選擇當初沒買的 B／C／D（最多 3 檔）</span></h2>
    <div class="stockpick" style="position:relative">
      <input id="cmpPeerSearch" type="text" autocomplete="off" data-i18n-ph="cmp.peerPh"
             placeholder="搜尋比較股票">
      <div id="cmpPeerSuggest" class="suggest"></div>
    </div>
    <div id="cmpPeers" class="cmp-peers"></div>
    <div class="rk-hint" data-i18n-html="cmp.local">資料與選擇<b>只存在這台裝置的瀏覽器</b>，不會上傳保存。</div>
  </div>

  <button class="gobtn" id="cmpBtn" data-i18n="cmp.run">開始同期比較</button>
  <div class="status" id="cmpStatus"></div>
  <div id="cmpResult"></div>
</div>

<!-- ============ 我的自選股：風控管理 ============ -->
<div class="page" id="p8">
  <h2 class="ptitle" data-i18n="p8.title">風控管理</h2>
  <details class="pgintro">
    <summary data-i18n="risk.introT">先想清楚會賠多少，再想能賺多少</summary>
    <div class="pgintro-b" data-i18n-html="risk.intro">
      <p>這頁把你持有的股票攤開來看四件事：<b>每天大概會動多少（ATR）</b>、
      <b>整體有多顛（波動率）</b>、<b>趨勢還在不在（均線排列）</b>、
      以及<b>跟大盤的連動程度（Beta）</b>。</p>
      <p>填進場價之後，會用 ATR 幫你算出<b>初始停損</b>與<b>移動停損</b>。
      重點不是那個數字有多精準，而是<b>逼你在買進之前就把出場條件寫下來</b>——
      套牢之後才想停損，通常就不會停了。</p>
      <p><b>為什麼用 ATR 而不是固定百分比</b>：同樣是 5%，對一檔日均波動 1% 的
      公用事業股來說是很遠的停損，對日均波動 6% 的高波動股卻是「今天就會被掃到」。
      ATR 是「這檔股票平常一天會動多少」，用它當單位，
      停損距離才會自動跟著標的的性格調整。</p>
      <p><b>資料只存在這台裝置的瀏覽器</b>，不會上傳、也沒有帳號系統。
      換裝置或清除瀏覽資料就會不見——這點先講清楚，不假裝有同步。</p>
    </div>
  </details>

  <div class="card">
    <h2><span class="stepno">01</span><span data-i18n="risk.pick">選擇持股（最多 3 檔）</span></h2>
    <div class="stockpick" style="position:relative">
      <input id="rkInput" type="text" autocomplete="off" data-i18n-ph="risk.ph"
             placeholder="輸入代號或公司名，例如 AAPL">
      <div id="rkSuggest" class="suggest"></div>
    </div>
    <div style="font-size:12px;color:#888;line-height:1.7;margin-top:8px"
         data-i18n="risk.pickNote">只提供市值前 300 大。選好後按下方按鈕計算。</div>
    <div id="rkChips" style="display:flex;gap:8px;flex-wrap:wrap;margin-top:10px"></div>
  </div>

  <div class="card">
    <h2><span class="stepno">02</span><span data-i18n="risk.mult">停損倍數</span></h2>
    <div style="display:flex;gap:8px;flex-wrap:wrap">
      <label class="opt" style="margin:0"><input type="radio" name="rkMult" value="1.5"><span data-i18n="risk.m15">1.5 × ATR（短線）</span></label>
      <label class="opt" style="margin:0"><input type="radio" name="rkMult" value="2" checked><span data-i18n="risk.m2">2 × ATR（波段）</span></label>
      <label class="opt" style="margin:0"><input type="radio" name="rkMult" value="3"><span data-i18n="risk.m3">3 × ATR（長抱）</span></label>
    </div>
    <div style="font-size:12px;color:#888;line-height:1.8;margin-top:10px"
         data-i18n-html="risk.multNote">
      倍數越大，停損越遠、越不容易被洗掉，但每次認錯的代價也越大。
      <b>⚠️ 停損最常見的錯誤是設太遠</b>——如果你發現自己一直往上調倍數，
      通常代表部位開太大，該調的是張數不是停損。
    </div>
  </div>

  <button class="gobtn" id="rkBtn" data-i18n="risk.btn">計算風控指標</button>
  <div class="status" id="rkStatus"></div>
  <div id="rkResult"></div>
</div>

<!-- ============ 我的自選股：均線扣抵法 ============ -->
<div class="page" id="p10">
  <h2 class="ptitle" data-i18n="p10.title">均線扣抵法</h2>

  <details class="pgintro">
    <summary data-i18n="ded.introT">還有多少時間可以整理？</summary>
    <div class="pgintro-b" data-i18n-html="ded.intro">
      <p><b>扣抵不是預測，是算術。</b>50 日線是最近 50 個交易日的平均，
      所以明天算的時候，會把 50 天前的那一筆丟掉、換成明天的收盤。
      那根「即將被丟掉的 K 棒」就叫<b>扣抵值</b>。</p>
      <p>由此可以直接推出一件事：<b>扣抵值比現在的價格低，50 日線就一定會往上</b>——
      跟明天漲不漲完全無關。反過來，扣抵值比現價高，均線就會往下。</p>
      <p>這頁回答的是：<b>照這樣走下去，50、100、150 日線要幾個交易日才會追上這個價位？</b>
      均線追上來之後，原本在下方的支撐就貼到價格附近，行情通常得選邊——
      所以這個天數可以當成「<b>還有多少時間可以慢慢整理</b>」的粗估。</p>
      <p>會同時算兩種假設：<b>盤整</b>（價格停在原地，均線追得最慢，算出來是上限）
      與<b>依近 20 日的實際斜率繼續走</b>。兩個數字之間就是合理的區間。</p>
      <p>⚠️ <b>這是算術外推，不是預測。</b>真實市場不會每天照同一個幅度走，
      天數只是「如果照這個節奏」的估計，不是保證還有幾天。</p>
    </div>
  </details>

  <div class="card">
    <h2><span class="stepno">01</span><span data-i18n="ded.pick">選擇標的</span></h2>
    <div style="display:flex;gap:8px;flex-wrap:wrap;margin-bottom:10px">
      <label class="opt" style="margin:0"><input type="radio" name="dedKind" value="index" checked><span data-i18n="ded.index">大盤（納斯達克綜合指數）</span></label>
      <label class="opt" style="margin:0"><input type="radio" name="dedKind" value="stock"><span data-i18n="ded.stock">個股（前 300 大）</span></label>
    </div>
    <div class="stockpick" id="dedPickBox" style="display:none;position:relative">
      <input id="dedSearch" type="text" autocomplete="off" data-i18n-ph="ded.ph"
             placeholder="輸入代號或公司名，例如 AAPL">
      <div id="dedSuggest" class="suggest"></div>
      <div id="dedPicked" class="picked" style="display:none"></div>
    </div>
  </div>

  <div class="card">
    <h2><span class="stepno">02</span><span data-i18n="ded.price">要追上的價位</span></h2>
    <input id="dedPrice" type="number" step="0.01"
           style="width:100%;padding:11px;font-size:15px;border:1.5px solid var(--grounds);
                  border-radius:10px;background:#fff;box-sizing:border-box;
                  font-family:var(--font-num)">
    <div style="font-size:12.5px;color:#888;line-height:1.75;margin-top:8px"
         data-i18n-html="ded.priceNote">留空就用<b>最新收盤價</b>。
      想估「如果撐在某個關卡要多久」，就把那個價位填進來。</div>
  </div>

  <button class="gobtn" id="dedBtn" data-i18n="ded.btn">試算</button>
  <div class="status" id="dedStatus"></div>
  <div id="dedResult"></div>
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
      從市值前 300 大美股中，找出最近指定期間任一天符合<b>3 個月、半年、1 年、2 年、3 年或 5 年新高</b>的股票。創新高採 2% 容差，避免只差一點就漏掉正在測試前高的股票。
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
  <div class="card rs-card">
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
    <div style="margin:0 0 14px">
      <label class="opt" style="margin:0"><input type="checkbox" id="structureHistoryRs"><span data-i18n="screen.structure">飆股前期結構回溯（1～5 年）</span></label>
      <div style="font-size:12px;color:var(--mocha);margin-top:4px;line-height:1.7" data-i18n="screen.structureNote">回溯前高、最大回落、整理月數與突破時點，並顯示可拖曳平移的長期收盤價圖。美股使用既有五年收盤快取。</div>
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

<footer class="site-footer">
  <div>本網站資料僅供投資研究與教育用途，不構成投資建議。</div>
  <div><a href="/privacy">隱私權政策 / Privacy Policy</a> ·
    <a href="mailto:seer51000@gmail.com?subject=US%20Stock%20Coffee%20Feedback">聯絡我們 / Contact</a></div>
  __BUILD_INFO__
</footer>

<script>
const $ = s => document.querySelector(s);
const APP_TOKEN = "__APP_TOKEN__";
const START_PAGE = "__START_PAGE__";
const CAFE_THEMES=['b','c','d'];
function applyCafeTheme(name){const theme=CAFE_THEMES.includes(name)?name:'b';document.documentElement.dataset.theme=theme;try{localStorage.setItem('us-cafe-theme',theme)}catch(e){}document.querySelectorAll('[data-theme-choice]').forEach(el=>{const on=el.dataset.themeChoice===theme;el.classList.toggle('on',on);const c=el.querySelector('.theme-check');if(c)c.textContent=on?'✓':''});const meta=document.querySelector('meta[name="theme-color"]');if(meta)meta.content=theme==='c'?'#17252B':theme==='d'?'#50302F':'#263A2D'}
function closeThemePicker(){const p=$("#themePicker"),b=$("#themeBtn");if(p)p.classList.remove('show');if(b)b.setAttribute('aria-expanded','false')}

/* ---- 顯示語言（機制與台股版相同）----
   data-i18n      → 換 textContent（中文原文自動備份在 data-zh，不會遺失）
   data-i18n-html → 換 innerHTML（保留 <b>/<p> 格式）
   JS 產生的字串   → 用 t(key, 中文預設)
   公司名稱與產業則由後端提供中英兩份，用 coName()/coSector() 挑。 */
/* ⚠️ 網址上的 ?lang=en 優先於 localStorage。
   伺服器是照 ?lang=en 決定 <title>／canonical 的，前端若還照舊值渲染，
   就會變成「head 說英文、內文是中文」—— 這種不一致 Google 看得到，使用者也看得到。
   分享出去的英文連結也必須真的開出英文畫面。 */
const _urlLang = new URLSearchParams(location.search).get("lang");
let LANG = (_urlLang === "en") ? "en"
         : (_urlLang === "zh") ? "zh"
         : (localStorage.getItem("us_lang") || "zh");
if (_urlLang === "en" || _urlLang === "zh") localStorage.setItem("us_lang", LANG);
/* 每頁的 title 由伺服器帶進來（兩種語言各一份），切語言時才不會被站名蓋掉。 */
const TITLE_ZH = "__TITLE_ZH__", TITLE_EN = "__TITLE_EN__";

const I18N = { en: {
  "ui.menu": "Menu",
  "brew.title": "Brewing, please wait", "brew.wait": "Getting ready…",
  "brand.name": "US Stock Coffee",
  "nav.home": "Menu", "nav.home.sub": "Is today a good day to act?",
  "nav.group": "Stock Screeners",
  "nav.group.sub": "Leaders · Pullbacks · Rates",
  "nav.screen.sub": "Find leading stocks",
  "nav.industry": "Sector Analysis", "nav.industry.sub": "Breadth · sector leaders",
  "nav.pull.sub": "Close back within ±3% of an MA",
  "nav.lev.sub": "QLD · realised multiple",
  "lev.title": "2x ETF Monthly Performance",
  "lev.introT": "The realised multiple is never exactly 2x",
  "lev.intro": "<p>Monthly returns for <b>QLD (ProShares Ultra QQQ, 2x Nasdaq-100)</b> over the past two years, against the Nasdaq Composite, with the <b>realised multiple</b> for each month.</p><p><b>Cumulative returns are never exactly 2x.</b> Leveraged ETFs rebalance daily: the multiple exceeds 2 in a smooth trend and falls below 2 in choppy markets. Two months of +10% then \u221210% leaves the index at \u22121% but the 2x fund at \u22124%.</p><p>\u26a0\ufe0f QLD tracks twice the <b>daily</b> move of the Nasdaq-100 (largest 100 non-financials), <b>not the Composite</b> (3,000+ names). Months where the index moved less than 0.2% show \u201c\u2014\u201d because the ratio is meaningless.</p>",
  "lev.run": "Show monthly performance",
  "nav.twr.sub": "TWR performance calculator",
  "nav.macro.sub": "US 2Y · 10Y · CPI",
  "nav.mine": "My Watchlist", "nav.mine.sub": "Performance · Comparison · Risk · Alerts",
  "p12.title": "Same-period Comparison", "nav.compare.sub": "What if you bought another stock?",
  "cmp.introT": "How much did the stocks you skipped gain?",
  "cmp.intro": "<p>Enter the stock you actually bought (A), its date, price and share count. The tool derives your real starting capital.</p><p>Then choose B, C and D. Each hypothetical position uses <b>the exact same capital to buy whole shares</b> on the same session, with unused money kept as cash. Results run through the latest common close, revealing the opportunity cost of the original choice.</p><p>Data stays on this device. Prices are split-consistent, but returns exclude fees, taxes and cash dividends. US comparisons cover roughly the latest five years.</p>",
  "cmp.actual": "Your actual A purchase", "cmp.aPh": "Search stock A, e.g. AAPL or Apple",
  "cmp.date": "Purchase date", "cmp.price": "Actual A purchase price",
  "cmp.shares": "Actual A shares", "cmp.principal": "Actual capital invested",
  "cmp.peers": "Stocks you skipped: B / C / D (up to 3)", "cmp.peerPh": "Search comparison stocks",
  "cmp.local": "Selections are stored <b>only in this browser</b> and are not saved on the server.",
  "cmp.run": "Compare Returns", "cmp.loading": "Calculating the same-period returns…",
  "cmp.needA": "Choose stock A first", "cmp.needPeer": "Choose at least one comparison stock",
  "cmp.needDate": "Enter a purchase date", "cmp.needTrade": "Enter a valid A price and share count",
  "cmp.max": "You can compare up to 3 stocks", "cmp.duplicate": "That stock is already selected",
  "cmp.nohit": "No match (top 300 by market cap only)", "cmp.fail": "Comparison failed — please try again",
  "cmp.actualTag": "Actually bought A", "cmp.hypTag": "Skipped stock",
  "cmp.best": "Best result", "cmp.return": "Return", "cmp.buyDate": "Comparison start",
  "cmp.buyPrice": "Starting price", "cmp.qty": "Shares", "cmp.cash": "Cash left",
  "cmp.split": "split-adjusted",
  "cmp.last": "Latest close", "cmp.value": "Current total", "cmp.vsA": "Difference vs A",
  "cmp.range": "Same period", "cmp.shift": "The requested date was not a common trading session; comparison starts on",
  "cmp.note": "Price return only: fees, taxes and cash dividends are excluded. B/C/D use whole shares and keep unused capital as cash.",
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
  "p7.introT": "Your return is probably wrong",
  "p7.intro": "<p>Most people compute return as \"current assets ÷ money put in − 1\". That is fine as long as you never added or withdrew funds midway — <b>but a single irregular transfer distorts it</b>.</p><p>An extreme example: you start the year with $1M and lose 20% in the first half, leaving $800k. In July you wire in another $1M and gain 10% in the second half, ending at $1.98M. Assets over contributions gives −1%, which looks like a small loss. But what you actually did was lose 20% and then gain 10% — that is <b>−12%</b>. The gap exists because <b>most of your money arrived after the loss</b>. That is timing, not skill.</p><p><b>Time-weighted return (TWR)</b> removes that effect: each month is treated as its own period, and the monthly returns are chained together. Deposits and withdrawals make no difference to the result. This is the standard for funds and managed accounts, precisely because a manager cannot control when clients wire money in.</p><p><b>How it differs from IRR (money-weighted)</b>: IRR accounts for how much you invested and when, answering \"how did this pot of money do?\" TWR answers \"how good were my picks and my timing of entries and exits?\" Use TWR to judge your process; use IRR to see what actually landed in your pocket.</p><p><b>What to enter</b>: just two columns per month — <b>net deposit</b> (deposits minus withdrawals; use a negative number for withdrawals) and <b>month-end total assets</b> (cash plus the market value of all holdings). Leave future months blank; only the months you fill are used, and you get both cumulative and annualised figures.</p><p><b>Everything stays in this browser</b> (localStorage). Nothing is uploaded and there is no account system. The upside is no sign-up; the cost is that changing device or clearing site data loses it — worth saying plainly rather than pretending there is sync.</p>",
  "p8.title": "Risk Dashboard", "p4.title": "Price Alerts",
  "home.qhead": "TODAY'S SERVING · QUOTES",
  "home.more": "Pour another ☕",
  "home.more.loading": "Brewing…",
  "home.more.done": "That's all for today ☕",
  /* --- 均線扣抵法 --- */
  "nav.deduct": "MA Deduction", "nav.deduct.sub": "When the 50/100/150MA catches up",
  "p10.title": "Moving-Average Deduction",
  "ded.introT": "How much time is left to consolidate?",
  "ded.intro": "<p><b>Deduction is arithmetic, not prediction.</b> The 50-day average is the mean of the last 50 closes, so tomorrow's calculation drops the close from 50 days ago and adds tomorrow's. That bar about to be dropped is the <b>deduction value</b>.</p><p>One thing follows directly: <b>if the deduction value is below the current price, the 50-day line must rise</b> — regardless of what happens tomorrow. If it is above, the average must fall.</p><p>This page answers: <b>at this pace, how many sessions until the 50-, 100- and 150-day averages reach this price?</b> Once the average catches up, support sits right at price and the market usually has to pick a side — so the number is a rough gauge of <b>how much room there is to keep consolidating</b>.</p><p>Two assumptions are shown: <b>flat</b> (price stays put — the slowest case, so an upper bound) and <b>continuing the last 20 sessions' slope</b>. The two numbers bracket a reasonable range.</p><p>⚠️ <b>This is arithmetic extrapolation, not a forecast.</b> Real markets do not move by the same amount every day.</p>",
  "ded.pick": "Choose a symbol", "ded.index": "Nasdaq Composite", "ded.stock": "Stock (top 300)",
  "ded.ph": "Ticker or company name, e.g. AAPL",
  "ded.price": "Price to reach",
  "ded.priceNote": "Leave blank to use the <b>latest close</b>. To estimate how long a specific level would take, enter it here.",
  "ded.btn": "Calculate", "ded.calc": "Calculating…",
  "ded.fail": "Calculation failed, please try again later",
  "ded.needStock": "Pick a stock first",
  "ded.last": "latest close", "ded.target": "target",
  "ded.useLast": " (blank — using latest close)",
  "ded.slope": "Last ", "ded.slope2": " sessions averaged ", "ded.maUnit": "-day MA",
  "ded.now": "Current MA", "ded.dv": "Tomorrow's deduction bar",
  "ded.rise": "Below target → the MA will rise", "ded.fall": "Above target → the MA will fall",
  "ded.up": "MA is below price, rising toward it",
  "ded.down": "MA is above price, easing toward it",
  "ded.gap": "Price vs MA", "ded.flat": "Flat (price stays at ",
  "ded.trend": "Continuing the 20-session slope",
  "ded.sessions": " sessions", "ded.over": "more than ", "ded.perDay": "day",
  "ded.done": "already deducted",
  "ded.noData": "Not enough history to compute this average",
  "ded.negNote": "\u26a0\ufe0f The recent slope is negative, so the shorter count in the trend row means price would fall to the average \u2014 not that the average is catching up. For \"how long can this keep consolidating\", read the flat row.",
  "grow.title": "Long-Term Growth List",
  "nav.grow.sub": "10-year total & annualised",
  "grow.introT": "Who actually went up over ten years",
  "grow.intro": "<p>This lists the <b>ten-year</b> cumulative and annualised returns for the <b>300 largest US stocks</b>, sortable by either. Every stock uses the <b>same starting date</b> so cumulative returns can be compared \u2014 using each stock's own listing date would make the periods different lengths and the ranking meaningless.</p><p><b>\u26a0\ufe0f This answers \"how much did today's large companies rise over the past ten years\", not \"what should you have bought ten years ago.\"</b> The universe is <b>today's</b> top 300: companies that were small then and grew are pre-loaded into the list, while companies that were large then and shrank out of the top 300 are invisible. That is survivorship plus look-ahead bias, and it makes the whole list look better than reality.</p><p><b>\u26a0\ufe0f Not dividend-adjusted.</b> Prices are split-adjusted but dividends are not added back, so <b>high-yield stocks are systematically understated</b> \u2014 a 6-7% yielder can be understated by more than half over ten years. The concentration of technology names at the top is partly caused by this.</p><p><b>Read the years column alongside the annualised figure.</b> Stocks listed for less than ten years are flagged; a single sharp run inside a short window gets magnified into an extreme annualised number.</p>",
  "grow.loading": "Loading long-term growth data\u2026",
  "grow.fail": "Failed to load",
  "grow.bench": "Nasdaq Composite, same period",
  "grow.benchNote": "Index and stocks both exclude dividends",
  "grow.total": "Total return",
  "grow.cagr": "Annualised",
  "grow.beat": "Beat the index (annualised)",
  "grow.neg": "Negative over ten years:",
  "grow.cnt": "",
  "grow.med": "median",
  "grow.rank": "Ranking",
  "grow.asof": "Data as of",
  "grow.byTotal": "By total return",
  "grow.byCagr": "By annualised",
  "grow.sym": "Symbol",
  "grow.name": "Name",
  "grow.years": "Years",
  "grow.yr": "y",
  "grow.shortT": "Listed less than ten years \u2014 annualised figure is unstable",
  "grow.spinT": "A spin-off occurred in this period \u2014 return is understated",
  "industry.title": "Sector Analysis",
  "industry.introT": "Where is capital concentrating, and is the advance broadening?",
  "industry.intro": "<p>This page groups the current top 300 US stocks by Nasdaq Sector. It compares <b>median 20- and 60-session returns</b> with their prior periods, then adds advancer share and top-three positive-return concentration. The goal is to test whether the whole sector strengthened, not merely list three winners.</p><p>Click a sector for its complete stock list. Sectors with fewer than five constituents are excluded. The universe is today’s top 300 and has survivorship bias; all readings are backward-looking.</p>",
  "industry.quad": "Sector Quadrants", "industry.rank": "Sector Strength Ranking",
  "industry.loading": "Loading…", "industry.m20": "20D Momentum",
  "industry.m60": "60D Trend", "industry.win": "Advancer Share",
  "industry.above": "Above 50MA", "industry.high": "60D Highs",
  "ded.warn": "\u26a0\ufe0f This is arithmetic extrapolation, not a forecast. It assumes the same daily move every session, which real markets do not do. Treat the session count as a rough \"if this pace holds\" estimate, not a guarantee.",
  "risk.introT": "Work out what you can lose before what you can make",
  "risk.intro": "<p>This page lays out four things about the stocks you hold: <b>how much it typically moves in a day (ATR)</b>, <b>how choppy it is overall (volatility)</b>, <b>whether the trend is still intact (MA alignment)</b>, and <b>how tightly it tracks the market (Beta)</b>.</p><p>Enter your entry price and it computes an <b>initial stop</b> and a <b>trailing stop</b> from ATR. The value isn't in the precision of that number — it's in <b>forcing you to write down the exit before you buy</b>. Decide a stop after you're underwater and you usually won't take it.</p><p><b>Why ATR instead of a fixed percentage</b>: 5% is a distant stop for a utility that moves 1% a day, and a same-day stop-out for a name that moves 6%. ATR is \"how much this stock normally moves in a day\", so using it as the unit makes the stop distance adapt to the character of the stock.</p><p><b>Everything stays in this browser</b> — nothing is uploaded and there is no account system. Changing device or clearing site data loses it, which is worth saying plainly rather than pretending there is sync.</p>",
  "risk.pick": "Pick your holdings (up to 3)",
  "risk.ph": "Ticker or company name, e.g. AAPL",
  "risk.pickNote": "Top 300 by market cap only. Choose them, then press the button below.",
  "risk.mult": "Stop multiple",
  "risk.m15": "1.5 × ATR (short term)", "risk.m2": "2 × ATR (swing)", "risk.m3": "3 × ATR (long hold)",
  "risk.multNote": "A larger multiple means a wider stop that is harder to get shaken out of — but every time you are wrong it costs more. <b>⚠️ The most common mistake with stops is setting them too far away.</b> If you find yourself steadily raising the multiple, the position is usually too large: adjust the size, not the stop.",
  "risk.btn": "Calculate Risk Metrics",
  "risk.calc": "Calculating… (the first run fetches data, ~15 seconds)",
  "risk.none": "Pick at least one stock first",
  "risk.max": "Up to 3 at a time — remove one first",
  "risk.fail": "Calculation failed, please try again later",
  "risk.needEntry": "Enter your entry price and the initial and trailing stops will appear here",
  "risk.initStop": "Initial stop", "risk.trailStop": "Trailing stop",
  "risk.peak": "Peak since set", "risk.dist": "Distance to stop",
  "risk.entry": "Entry price",
  "risk.nAtr": "Typical daily range — the unit for stop distance",
  "risk.kVol": "Volatility (6m, annualised)",
  "risk.nVol": "Overall choppiness — use it to size the position",
  "risk.kAlign": "MA trend", "risk.nAlign": "Whether the trend is still intact",
  "risk.nBeta": "Sensitivity to the Nasdaq Composite; above 1 moves more than the market",
  "alert.preparing": "US close-price alerts are being prepared",
  "alert.preparingNote": "Alerts will check official US closing prices against your targets and notify this device. The feature will open after push keys, subscription storage and the US close schedule are ready.",
  "p5.title": "Pro｜New Highs", "p9.title": "Pro｜RS Ranking",
  "pro.beta": "Beta", "pro.nhTitle": "New-high stock screener",
  "pro.nhBody": "Find top-300 US stocks that reached a <b>3-month, 6-month, 1-year, 2-year, 3-year or 5-year high</b> on any day in the selected window. A 2% tolerance avoids missing stocks that are effectively retesting a prior high.",
  "pro.nh1": "Last day", "pro.nh3": "Last 3 days", "pro.nh5": "Last 5 days",
  "pro.nhBtn": "Screen new highs",
  "rs.title": "RS relative-strength ranking",
  "rs.body": "<b>RS is not RSI.</b> It compares price gains among the top 300 US stocks over the selected period and converts them to a 1–99 market percentile. RS 90 means the stock outperformed roughly 90% of calculable peers. This is Stock Coffee's price percentile, not IBD's proprietary RS Rating.",
  "rs.period": "Comparison period", "rs.p20": "20 days (short term)",
  "rs.p60": "60 days (swing)", "rs.p120": "120 days (intermediate)",
  "rs.p250": "250 days (long term)", "rs.threshold": "Minimum RS",
  "rs.btn": "Show RS ranking",
  "p1.introT": "Find stocks that are moving right now — using moving averages",
  "p1.intro": "<p>A moving average is the average cost of a group of buyers. Above the 50-day line, the people who bought this quarter are in profit; below the 150-day line, most buyers of the past half-year are underwater. Moving averages don't predict — they tell you where market participants stand, and that shapes what they do next.</p><p>This screener filters the top 150 or 300 US companies by market cap: crossing above or below the 10, 20, 50 or 150-day moving average, or screening directly by <b>MA alignment</b> — strict bullish (10&gt;20&gt;50&gt;150) means later buyers paid more and still bought, which usually marks a trend in progress.</p><p>If the screen returns too many names, four dropdowns narrow it further and combine with AND: <b>sector</b>, <b>quarterly EPS growth</b>, <b>MA alignment</b> and <b>new-high tier</b>. <b>The sector distribution is itself a signal</b> — when twelve of thirty results share an industry, that is where money is going, and group moves persist far better than isolated ones.</p><p><b>Three common setups</b>: (1) above the 50-day plus strict bullish alignment finds trends already established and still running; (2) above the 10-day with \"all of the last 3 days\" finds names that have just turned up and held; (3) below the 150-day plus strict bearish alignment does the reverse — useful for checking whether something you already own should be trimmed.</p><p>Each row also shows the <b>new-high tier</b> (3 months to 5 years) and <b>quarterly revenue/EPS growth</b>. The first tells you where the stock sits within its own history; the second is a rough check on whether fundamentals are keeping up — note that US companies report quarterly, so that figure may already be two or three months old.</p><p><b>When not to use this page</b>: in a headwind market it will still return dozens of \"relatively strong\" names, and that does not make them tradable. Check the market stage on the home page first.</p><p><b>Who it's for</b>: momentum traders holding for several months. This is closing data — not built for day trading. If you want an entry after a pullback rather than a list of what is strongest right now, use <b>Pullback Buy Points</b> instead.</p>",
  "p3.introT": "Wait for a strong stock to come back, instead of chasing the high",
  "p3.intro": "<p>Leading stocks don't rise every day. After a run they consolidate, and that consolidation often stalls near a moving average — because that line is a group's average cost, which becomes psychological support.</p><p>This screen finds stocks whose <b>latest close has returned to within ±3% of the moving average you choose</b>. The point isn't to call the bottom; it's an entry with controlled risk — you're not buying the high, and if you're wrong the stop is obvious (a break of that line).</p><p>Which average to use depends on your holding period — the 20-day for shorter trades, the 50 or 150-day for swings. Combined with the <b>MA alignment</b> filter, you can look only for stocks whose trend is intact and merely resting.</p><p>Results are sorted by <b>absolute deviation</b> (how many percent the close sits from the line), so the top of the list pulled back the most precisely. A positive deviation means price is still above the line, negative means it has dipped slightly below — both can be within ±3%, but they do not mean the same thing.</p><p><b>This page uses closing prices, not intraday quotes.</b> The definition has to be stable: computed on live prices, the same stock would give different answers at 10am and 3pm and the list would churn all day. The intraday quote appears in the results table for reference only and never affects the screen.</p><p><b>Telling a healthy pullback from a failing trend</b>: if the MA alignment is still bullish when price reaches the line, it is usually just a rest. If the shorter average has already crossed below the longer one (alignment turned bearish or squeezed), that is not a pullback — the trend is changing direction. This is why pairing the alignment filter with this screen is worth the extra click.</p><p><b>What this page does not answer</b>: it tells you who is currently near a moving average, not whether a stock is worth owning. You need a candidate first and an entry second — find candidates with <b>Find Leading Stocks</b>.</p>",
  "twr.intro": "Time-weighted return (TWR) removes the effect of deposits and withdrawals, giving a clearer view of your investing performance. Enter each month's net cash flow and ending portfolio value. Data stays in this browser on this device.",
  "pmac.title": "Rates & Purchasing Power",
  "pmac.introT": "Returns must first clear interest rates and inflation",
  "pmac.intro": "<p>A 10% investment return does not mean 10% more purchasing power. US Treasury yields are the return hurdle available to dollar capital at low credit risk. Your return minus a similar-maturity Treasury yield is a rough estimate of the excess return earned for accepting market risk.</p><p><b>Year-to-date cumulative CPI</b> compares the latest CPI with last December; <b>10-year cumulative CPI</b> compares the latest month with the same month ten years earlier. They show how much prices have risen over each period.</p><p>Real return is calculated as “(1 + nominal return) ÷ (1 + inflation) − 1”. Treasury yields measure opportunity cost; CPI adjusts purchasing power. They are not interchangeable.</p>",
  "pmac.disc": "Yields are annualized; CPI figures are cumulative period changes, not annualized rates. Data is the latest available, not real-time, and is not investment advice.",
  "pmac.src": "Sources & Methodology",
  "pmac.loading": "Loading US rates and CPI…", "pmac.none": "Data is temporarily unavailable. Please try again later.",
  "pmac.bonds": "US Treasury Yields", "pmac.cpi": "Cumulative Price Increase",
  "pmac.source": "US 2-year and 10-year yields use the U.S. Treasury's Daily Treasury Par Yield Curve Rates. CPI uses the Bureau of Labor Statistics seasonally adjusted all-urban consumer price index, CUSR0000SA0.<br><br>YTD cumulative CPI = latest index ÷ prior December index − 1. Ten-year cumulative CPI = latest index ÷ the same month ten years earlier − 1.<br><br>Source: <a href=\"https://home.treasury.gov/resource-center/data-chart-center/interest-rates\" target=\"_blank\" rel=\"noopener\" style=\"color:var(--primary)\">U.S. Treasury</a> and <a href=\"https://www.bls.gov/cpi/\" target=\"_blank\" rel=\"noopener\" style=\"color:var(--primary)\">U.S. Bureau of Labor Statistics</a>.",
  "twr.basic": "Basic settings", "twr.year": "Year",
  "twr.start": "Starting portfolio value (cash + holdings)",
  "twr.monthly": "Monthly entries",
  "twr.note": "Net deposit = deposits minus withdrawals (enter withdrawals as negative). Ending value = cash plus all holdings. Leave future months blank.",
  "twr.col.m": "Month", "twr.col.in": "Net deposit", "twr.col.tot": "Ending value",
  "twr.col.ret": "Monthly return", "twr.col.cum": "Cumulative return",
  "twr.calc": "Calculate performance", "twr.clear": "Clear all data",
  "twr.vs": "Challenge the Market",
  "twr.vsNote": "Compare your performance with the Nasdaq Composite's monthly returns, annual return and CPI for each of the latest two years.",
  "twr.vsBtn": "View the market's latest two years",
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
  "th.ret20": "20D Cumulative Return", "th.ret60": "60D Cumulative Return",
  "th.strength": "Recent Strength",
  "th.per": "P/E", "th.yield": "Dividend Yield",
  "q.last": "Last", "q.regular": "market hours",
  "q.extended": "pre/after-hours", "q.close": "at close",
  "q.closed": "Market closed — showing last close",
  "th.eps": "Q EPS YoY", "th.rev": "Q Rev YoY", "th.nh": "New high",
  "th.align": "MA alignment", "th.hit": "Match date", "th.asof": "Data date",
  "screen.advanced": "Fundamentals & Advanced Data",
  "screen.eps": "Add the latest two years of H1/H2 EPS",
  "screen.epsNote": "H1 and H2 each combine two reported quarters. Results expand below the company name without adding four crowded columns.",
  "screen.valuation": "Show P/E and dividend yield",
  "screen.valuationNote": "P/E and dividend yield stay hidden by default; select this option to load and add both columns.",
  "screen.structure": "Trace pre-breakout structure (1–5 years)",
  "screen.structureNote": "Trace the prior high, maximum drawdown, consolidation length and breakout date, with a draggable long-term closing-price chart. US stocks reuse the existing five-year price cache.",
  "screen.saveName": "Custom strategy name", "screen.save": "Save", "screen.saved": "Saved presets",
  "screen.apply": "Apply", "screen.delete": "Delete", "screen.export": "Export CSV",
  "screen.savedOk": "Preset saved on this device", "screen.appliedOk": "Preset applied",
  "screen.deletedOk": "Preset deleted", "screen.noPreset": "Choose a saved preset first",
  "screen.noResult": "Run the screen before exporting", "screen.exported": "CSV exported",
  "flt.sector": "Sector", "flt.allSector": "All sectors",
  "flt.eps": "Q EPS YoY", "flt.align": "MA alignment", "flt.nh": "New high",
  "flt.any": "Any", "flt.hasNH": "Made a new high",
  "flt.momentum": "Recent return", "flt.sort": "Sort",
  "flt.bothPos": "20D & 60D both positive", "flt.ret20Pos": "20D above 0%",
  "flt.ret20Five": "20D above 5%", "flt.ret60Ten": "60D above 10%",
  "flt.recovery": "20D positive / 60D non-positive", "flt.consolidate": "60D positive / 20D non-positive",
  "flt.weak": "20D & 60D both non-positive", "flt.defaultSort": "Default order",
  "flt.ret20Desc": "20D: high to low", "flt.ret20Asc": "20D: low to high",
  "flt.ret60Desc": "60D: high to low", "flt.ret60Asc": "60D: low to high",
  "strength.strong": "Short & medium term strong", "strength.consolidate": "Medium-term strong · short-term consolidation",
  "strength.recovery": "Early recovery", "strength.weak": "Short & medium term weak",
  "yoy.neg": "Negative", "yoy.lo": "0–20%", "yoy.mid": "20–50%", "yoy.hi": "Over 50%",
  "nh.5y": "5-year high", "nh.3y": "3-year high", "nh.2y": "2-year high",
  "nh.1y": "1-year high", "nh.6m": "6-month high", "nh.3m": "3-month high",
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
  /* 伺服器端已同時渲染中英文的區塊（市場階段、本日推薦、生命週期）。
     這些沒有 data-i18n，必須在切換語言時直接切顯示，否則英文介面仍會混入中文。 */
  document.querySelectorAll(".q-zh").forEach(el => {
    el.style.display = (LANG === "zh") ? "" : "none";
  });
  document.querySelectorAll(".q-en").forEach(el => {
    el.style.display = (LANG === "en") ? "" : "none";
  });
  document.documentElement.lang = (LANG === "zh") ? "zh-Hant-TW" : "en";
  const themeLabel = $("#themeBtn");
  if (themeLabel) themeLabel.textContent = (LANG === "zh") ? "☕ 外觀" : "☕ Theme";
  document.title = (LANG === "zh") ? TITLE_ZH : TITLE_EN;
  /* canonical 跟著語言走，與伺服器端注入的規則一致（英文＝?lang=en）。 */
  const can = document.querySelector('link[rel="canonical"]');
  if (can){
    const base = location.origin + location.pathname;
    can.href = (LANG === "en") ? base + "?lang=en" : base;
  }
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
    /* 網址跟著語言改（不重新載入）。使用者複製網址分享時，對方才會看到同一種語言，
       也讓網址與 canonical／hreflang 說的是同一件事。 */
    try {
      const u = new URL(location.href);
      if (LANG === "en") u.searchParams.set("lang", "en");
      else u.searchParams.delete("lang");
      history.replaceState(null, "", u.pathname + u.search + u.hash);
    } catch(_){}
    applyLang();
    if (typeof setupScreenTool === "function"){ setupScreenTool("1"); setupScreenTool("3"); }
    document.querySelectorAll(".tw-month").forEach(el => {
      el.textContent = twMonth(parseInt(el.dataset.month, 10));
    });
    if (lastRows.length) render({rows:lastRows, as_of:lastMeta.as_of,
        ma_name_zh:lastMeta.ma_name_zh, ma_name:lastMeta.ma_name});
    if (lastRows3.length) render3({rows:lastRows3, as_of:lastMeta3.as_of, band:lastMeta3.band,
        ma_name_zh:lastMeta3.ma_name_zh, ma_name:lastMeta3.ma_name});
    if (lastProHigh) renderProHigh(lastProHigh);
    if (lastProRs) renderProRs(lastProRs);
    if (typeof IND_DATA !== "undefined" && IND_DATA) renderIndustries();
    if (typeof DATA_HEALTH !== "undefined" && DATA_HEALTH) renderDataQuality();
    if (typeof loadHomeIndustryBrief === "function") loadHomeIndustryBrief();
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

/* ---- 篩選條件儲存與目前結果 CSV ----
   只存在這台裝置；CSV 直接讀表格 DOM，因此會保留目前下拉篩選與排序。 */
const SCREEN_PRESET_KEY = 'us-screen-presets-v1';
const SCREEN_FIELDS = {
  '1': {names:['universe','days','mode','ma','direction','align'], checks:['epsHalves1','valuation1','structureHistory1']},
  '3': {names:['universe3','ma3','align3'], checks:['epsHalves3','valuation3','structureHistory3']}
};
function screenPresetsRead(){try{return JSON.parse(localStorage.getItem(SCREEN_PRESET_KEY)||'[]')||[]}catch(e){return []}}
function screenPresetsWrite(rows){try{localStorage.setItem(SCREEN_PRESET_KEY,JSON.stringify(rows.slice(-20)))}catch(e){}}
function screenEsc(s){return String(s||'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]))}
function screenToolStatus(slot,msg){const el=$('#screenToolStatus'+slot);if(el){el.textContent=msg;setTimeout(()=>{if(el.textContent===msg)el.textContent=''},2600)}}
function screenToolOptions(slot,selected){
  const rows=screenPresetsRead().filter(x=>String(x.slot)===String(slot));
  return '<option value="">'+t('screen.saved','已儲存條件')+'</option>'+rows.map(x=>'<option value="'+screenEsc(x.id)+'"'+(String(x.id)===String(selected)?' selected':'')+'>'+screenEsc(x.name)+'</option>').join('');
}
function refreshScreenTool(slot,selected){const sel=$('#screenSaved'+slot);if(sel)sel.innerHTML=screenToolOptions(slot,selected)}
function readScreenPreset(slot){
  const cfg=SCREEN_FIELDS[slot],values={},checks={};
  cfg.names.forEach(n=>values[n]=val(n));
  cfg.checks.forEach(id=>checks[id]=!!($('#'+id)&&$('#'+id).checked));
  return {values,checks};
}
function setScreenPreset(slot,preset){
  const cfg=SCREEN_FIELDS[slot];
  cfg.names.forEach(n=>{
    const wanted=String((preset.values||{})[n]||'');
    document.querySelectorAll('input[name="'+n+'"]').forEach(el=>{el.checked=el.value===wanted});
  });
  cfg.checks.forEach(id=>{if($('#'+id))$('#'+id).checked=!!(preset.checks||{})[id]});
  const changed=document.querySelector('#p'+slot+' input');
  if(changed)changed.dispatchEvent(new Event('change',{bubbles:true}));
  const mode=$('#modeCard');if(slot==='1'&&mode)mode.style.display=val('days')==='3'?'':'none';
  if(typeof screenSummary==='function'&&slot==='1')screenSummary();
}
function saveScreenPreset(slot){
  const input=$('#screenSaveName'+slot);
  let rows=screenPresetsRead(),name=(input.value||'').trim();
  if(!name)name=(LANG==='en'?'Preset ':'條件 ')+(rows.filter(x=>String(x.slot)===String(slot)).length+1);
  name=name.slice(0,40);
  const old=rows.find(x=>String(x.slot)===String(slot)&&x.name===name);
  const item=Object.assign({id:old?old.id:(Date.now().toString(36)+Math.random().toString(36).slice(2,6)),slot,name},readScreenPreset(slot));
  rows=rows.filter(x=>x.id!==item.id);rows.push(item);screenPresetsWrite(rows);
  input.value=name;refreshScreenTool(slot,item.id);screenToolStatus(slot,t('screen.savedOk','✓ 已儲存在本裝置'));
}
function applyScreenPreset(slot){
  const id=$('#screenSaved'+slot).value,p=screenPresetsRead().find(x=>String(x.id)===String(id));
  if(!p){screenToolStatus(slot,t('screen.noPreset','請先選擇已儲存條件'));return}
  setScreenPreset(slot,p);$('#screenSaveName'+slot).value=p.name;screenToolStatus(slot,t('screen.appliedOk','✓ 已套用條件'));
}
function deleteScreenPreset(slot){
  const id=$('#screenSaved'+slot).value;if(!id){screenToolStatus(slot,t('screen.noPreset','請先選擇已儲存條件'));return}
  screenPresetsWrite(screenPresetsRead().filter(x=>String(x.id)!==String(id)));refreshScreenTool(slot,'');screenToolStatus(slot,t('screen.deletedOk','已刪除條件'));
}
function csvCell(v){return '"'+String(v==null?'':v).replace(/"/g,'""')+'"'}
function exportScreenCsv(slot){
  const table=document.querySelector('#result'+slot+' .res-wide table');
  const rows=table&&table.tBodies[0]?Array.from(table.tBodies[0].rows).filter(r=>r.style.display!=='none'):[];
  if(!table||!rows.length){screenToolStatus(slot,t('screen.noResult','請先執行篩選，再匯出結果'));return}
  const clean=s=>String(s||'').replace(/↕/g,'').replace(/\s+/g,' ').trim();
  const lines=[Array.from(table.tHead.rows[0].cells).map(c=>csvCell(clean(c.innerText))).join(',')];
  rows.forEach(r=>lines.push(Array.from(r.cells).map(c=>csvCell(clean(c.innerText))).join(',')));
  const blob=new Blob(['\ufeff'+lines.join('\r\n')],{type:'text/csv;charset=utf-8'});
  const url=URL.createObjectURL(blob),a=document.createElement('a');
  a.href=url;a.download=(LANG==='en'?'us-stocks_':'美股_')+(slot==='1'?(LANG==='en'?'strong_':'強勢股_'):(LANG==='en'?'pullback_':'標股拉回_'))+new Date().toISOString().slice(0,10)+'.csv';
  document.body.appendChild(a);a.click();a.remove();setTimeout(()=>URL.revokeObjectURL(url),1000);
  screenToolStatus(slot,t('screen.exported','✓ 已匯出 CSV')+'（'+rows.length+'）');
}
function setupScreenTool(slot){
  const box=$('#screenTools'+slot);if(!box)return;
  box.innerHTML='<input id="screenSaveName'+slot+'" maxlength="40" placeholder="'+screenEsc(t('screen.saveName','自訂策略名'))+'">'
    +'<button type="button" id="screenSave'+slot+'">'+t('screen.save','儲存')+'</button>'
    +'<select id="screenSaved'+slot+'">'+screenToolOptions(slot,'')+'</select>'
    +'<button type="button" id="screenApply'+slot+'">'+t('screen.apply','套用')+'</button>'
    +'<button type="button" id="screenDelete'+slot+'">'+t('screen.delete','刪除')+'</button>'
    +'<button type="button" class="export" id="screenExport'+slot+'">'+t('screen.export','匯出 CSV')+'</button>'
    +'<span class="screen-tools-status" id="screenToolStatus'+slot+'"></span>';
  $('#screenSave'+slot).onclick=()=>saveScreenPreset(slot);$('#screenApply'+slot).onclick=()=>applyScreenPreset(slot);
  $('#screenDelete'+slot).onclick=()=>deleteScreenPreset(slot);$('#screenExport'+slot).onclick=()=>exportScreenCsv(slot);
}
setupScreenTool('1');setupScreenTool('3');
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
    align: val("align"),
    eps_halves: !!($("#epsHalves1") && $("#epsHalves1").checked),
    valuation: !!($("#valuation1") && $("#valuation1").checked),
    structure_history: !!($("#structureHistory1") && $("#structureHistory1").checked)
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
  const showHalves = !!($("#epsHalves1") && $("#epsHalves1").checked);
  const showValuation = !!($("#valuation1") && $("#valuation1").checked);
  const showStructure = !!($("#structureHistory1") && $("#structureHistory1").checked);
  const per = lastRows.find(r => r.period);
  $("#status1").innerHTML = t("st.asof","資料日期") + " " + (res.as_of || "—")
    + (per ? "｜" + t("st.quarter","財報季") + " " + per.period : "")
    + "｜" + (LANG === "zh" ? res.ma_name_zh : res.ma_name)
    + "（" + (val("direction") === "above" ? t("st.above","站上") : t("st.below","跌破")) + "）"
    + "｜" + t("st.match","符合") + " <span class=\"count\">" + lastRows.length + "</span> "
    + t("st.unit","檔") + quoteNote(res.quote);
  if (!lastRows.length){ $("#result1").innerHTML = "<div class='status'>" + t("st.none","沒有符合條件的股票。") + "</div>"; return; }

  let h = "";
  {
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
       + momentumControls("momentumFilter","sortFilter","applyFilter","tb1","cd1")
       + "</div>";
  }
  h += "<div class='tblwrap res-wide'><table><thead><tr>"
     + "<th>" + t("th.rank","市值排名") + "</th><th>" + t("th.sym","代號")
     + "</th><th>" + t("th.name","公司名稱") + "</th>" + (showStructure ? "<th>" + (LANG==="en"?"Pre-breakout structure":"前期結構") + "</th>" : "") + "<th>" + t("th.sector","產業") + "</th>"
     + "<th>" + t("th.close","收盤") + "</th>"
     + (showQ ? "<th>" + t("th.last","現價") + "</th><th>"
              + t("th.lastgap","與收盤差%") + "</th>" : "")
     + "<th>" + t("th.gap","均線乖離%") + "</th>"
     + "<th class='sort-th' onclick=\"toggleUsSort('tb1','cd1','ret20','sortFilter')\">" + t("th.ret20","20日累積漲幅") + " ↕</th><th class='sort-th' onclick=\"toggleUsSort('tb1','cd1','ret60','sortFilter')\">" + t("th.ret60","60日累積漲幅") + " ↕</th><th>" + t("th.strength","近期強弱") + "</th>"
     + (showValuation ? "<th>" + t("th.per","本益比") + "</th><th>" + t("th.yield","殖利率") + "</th>" : "")
     + "<th>" + t("th.eps","季EPS年增") + "</th><th>" + t("th.rev","季營收年增")
     + "</th><th>" + t("th.nh","創新高") + "</th>"
     + (showAlign ? "<th>" + t("th.align","均線排列") + "</th>" : "")
     + "<th>" + t("th.hit","符合日期") + "</th></tr></thead><tbody id='tb1'>" + rowsHtml(lastRows, showAlign, showQ, showHalves, showValuation, showStructure)
     + "</tbody></table></div>";
  h += "<div id='cd1'>" + cardsHtml(lastRows, showAlign, t("th.hit","符合日期"), showQ, showHalves, showValuation, showStructure) + "</div>";
  $("#result1").innerHTML = h;
  if(showStructure)setupStructureCharts($("#result1"));
}

/* ---- 創新高（與後端 NH_TIERS / NH_LABEL 對應）---- */
const NH_LABEL = {"5y": "5年新高", "3y": "3年新高", "2y": "2年新高", "1y": "1年新高",
                  "6m": "半年新高", "3m": "3個月新高"};
const NH_ORDER = ["5y", "3y", "2y", "1y", "6m", "3m"];
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
function momentumKey(ret20,ret60){
  if(ret20==null||ret60==null)return "";
  if(ret20>0&&ret60>0)return "strong";
  if(ret20<=0&&ret60>0)return "consolidate";
  if(ret20>0&&ret60<=0)return "recovery";
  return "weak";
}
function momentumName(key){
  const zh={strong:"短中期同步強勢",consolidate:"中期強勢・短線整理",recovery:"低檔開始復甦",weak:"短中期同步偏弱"};
  return t("strength."+key,zh[key]||"—");
}
function momentumBadge(ret20,ret60){const key=momentumKey(ret20,ret60);return key?`<span class="momentum-badge ${key}">${momentumName(key)}</span>`:"—";}
function momentumPass(mode,ret20,ret60){
  if(!mode)return true;if(ret20==null||ret60==null)return false;
  if(mode==="both_pos")return ret20>0&&ret60>0;
  if(mode==="ret20_pos")return ret20>0;
  if(mode==="ret20_5")return ret20>5;
  if(mode==="ret60_10")return ret60>10;
  return momentumKey(ret20,ret60)===mode;
}
function momentumControls(momentId,sortId,filterFn,tbId,cdId){
  return `<span class="rflabel">${t("flt.momentum","近期漲幅")}</span><select id="${momentId}" onchange="${filterFn}()"><option value="">${t("flt.any","不限")}</option><option value="both_pos">${t("flt.bothPos","20日、60日同步上漲")}</option><option value="ret20_pos">${t("flt.ret20Pos","20日漲幅大於 0%")}</option><option value="ret20_5">${t("flt.ret20Five","20日漲幅大於 5%")}</option><option value="ret60_10">${t("flt.ret60Ten","60日漲幅大於 10%")}</option><option value="recovery">${t("flt.recovery","20日轉強、60日仍偏弱")}</option><option value="consolidate">${t("flt.consolidate","60日偏強、20日整理")}</option><option value="weak">${t("flt.weak","20日、60日同步偏弱")}</option></select><span class="rflabel">${t("flt.sort","排序")}</span><select id="${sortId}" onchange="sortUsResult('${tbId}','${cdId}',this.value);${filterFn}()"><option value="default">${t("flt.defaultSort","預設排序")}</option><option value="ret20_desc">${t("flt.ret20Desc","20日：高至低")}</option><option value="ret20_asc">${t("flt.ret20Asc","20日：低至高")}</option><option value="ret60_desc">${t("flt.ret60Desc","60日：高至低")}</option><option value="ret60_asc">${t("flt.ret60Asc","60日：低至高")}</option></select>`;
}
function sortUsResult(tbId,cdId,value){
  const rows=tbId==="tb1"?lastRows:lastRows3,parts=(value||"default").split("_"),key=parts[0],dir=parts[1]||"asc";
  [["#"+tbId,"tr"],["#"+cdId+" .res-cards",".scard"]].forEach(pair=>{
    const parent=document.querySelector(pair[0]);if(!parent)return;
    const nodes=Array.from(parent.querySelectorAll(":scope > "+pair[1]));
    nodes.sort((a,b)=>{const ai=Number(a.dataset.i),bi=Number(b.dataset.i);if(key==="default")return ai-bi;const av=rows[ai]?.[key],bv=rows[bi]?.[key];return (dir==="desc"?bv-av:av-bv)||(ai-bi);});
    nodes.forEach(el=>parent.appendChild(el));
  });
}
function toggleUsSort(tbId,cdId,key,selectId){
  const sel=$("#"+selectId);if(!sel)return;sel.value=sel.value===key+"_desc"?key+"_asc":key+"_desc";sortUsResult(tbId,cdId,sel.value);(tbId==="tb1"?applyFilter:applyFilter3)();
}
function epsHalfPanel(s,show){
  if(!show || !s.eps_halves || !s.eps_halves.length) return "";
  const cells=s.eps_halves.slice(0,4).map(x=>`<span>${x.label}<b>${x.value==null?"—":Number(x.value).toFixed(2)}</b></span>`).join("");
  return `<details class="eps-half"><summary>${LANG==="en"?"2-year H1 / H2 EPS":"近兩年 H1／H2 EPS"}</summary><div class="eps-half-grid">${cells}</div></details>`;
}

const STRUCTURE_PATTERN_EN={"多重底":"Multiple bottom","VCP 波動收縮":"VCP contraction","U 型底":"U-shaped base","杯柄":"Cup with handle","長期橫盤":"Long base"};
function structurePatternName(v){return LANG==="en"?(STRUCTURE_PATTERN_EN[v]||v):v}
function structureNumber(v,prefix="",suffix=""){return v==null?"—":prefix+Number(v).toLocaleString(undefined,{maximumFractionDigits:1})+suffix}
function structurePanel(s){
  const d=s&&s.structure;if(!d)return "";
  const summary=!d.available?(LANG==="en"?"Unavailable":"無法回溯")
    :d.matched?(LANG==="en"?"✓ Structure match":"✓ 結構符合")
    :(d.prior_high!=null?(LANG==="en"?"Structure nearly complete":"結構接近完成"):(LANG==="en"?"Not formed":"未形成"));
  const summaryClass=!d.available?"":d.matched?"structure-hit":d.prior_high!=null?"structure-near":"structure-miss";
  const reasonText=!d.reason?"":LANG==="en"
    ?(!d.available?"Long-term prices are unavailable or contain a suspected split discontinuity.":d.prior_high==null?"The 20% drawdown, three-month base and recent return to the prior high were not all found.":"The earlier structure qualifies, but the best 1–3 month gain has not exceeded 30%.")
    :d.reason;
  const reason=reasonText?`<div class="structure-reason">${screenEsc(reasonText)}</div>`:"";
  if(!d.available)return `<details class="structure-details"><summary>${summary}</summary><div class="structure-panel">${reason}</div></details>`;
  const tags=(d.pattern_labels||[]).map(x=>`<span>${screenEsc(structurePatternName(x))}</span>`).join("");
  const gain=structureNumber(d.recent_gain_pct,d.recent_gain_pct>0?"+":"","%");
  const post=structureNumber(d.post_breakout_gain_pct,d.post_breakout_gain_pct>0?"+":"","%");
  const metrics=d.prior_high!=null?`<div class="structure-metrics">
    <div class="structure-metric"><small>${LANG==="en"?"Recent gain":"近期漲幅"} · ${d.recent_period_days}${LANG==="en"?"D":"日"}</small><b>${gain}</b></div>
    <div class="structure-metric"><small>${LANG==="en"?"Prior high":"前期高點"} · ${d.prior_high_date||""}</small><b>${structureNumber(d.prior_high,"$")}</b></div>
    <div class="structure-metric"><small>${LANG==="en"?"Max drawdown":"最大跌幅"} · ${d.trough_date||""}</small><b>${structureNumber(d.max_drawdown_pct,"","%")}</b></div>
    <div class="structure-metric"><small>${LANG==="en"?"Consolidation":"整理時間"}</small><b>${structureNumber(d.consolidation_months,"",LANG==="en"?" months":" 個月")}</b></div>
    <div class="structure-metric"><small>${LANG==="en"?"Breakout month":"突破時間"}</small><b>${d.breakout_date||(LANG==="en"?"Not yet":"尚未突破")}</b></div>
    <div class="structure-metric"><small>${LANG==="en"?"Vs prior high":"突破後漲幅"}</small><b>${post}</b></div>
  </div>`:`<div class="structure-metrics"><div class="structure-metric"><small>${LANG==="en"?"Best 1–3M gain":"近 1～3 月最大漲幅"}</small><b>${gain}</b></div><div class="structure-metric"><small>${LANG==="en"?"History available":"可回溯期間"}</small><b>${d.lookback_years||"—"} ${LANG==="en"?"years":"年"}</b></div></div>`;
  const encoded=encodeURIComponent(JSON.stringify(d.chart||[])),markers=encodeURIComponent(JSON.stringify(d.markers||{}));
  const chart=(d.chart||[]).length>1?`<div class="structure-chart-head"><span class="structure-chart-range"></span><span class="structure-chart-buttons"><button type="button" data-weeks="52">1Y</button><button type="button" data-weeks="156" class="on">3Y</button><button type="button" data-weeks="9999">5Y</button></span></div><div class="structure-chart" data-series="${encoded}" data-markers="${markers}" data-high="${d.prior_high==null?"":d.prior_high}"></div><div class="structure-chart-read"></div>`:"";
  const note=LANG==="en"?"Drag the line horizontally to pan; use the wheel or buttons to zoom. Weekly closing prices only. Pattern labels are heuristic outlines, not OHLCV confirmation.":"在折線圖上左右拖曳可平移；滾輪或 1Y／3Y／5Y 可縮放。圖為每週最後收盤價；型態標籤只是收盤輪廓候選，不是 OHLCV 確認。";
  return `<details class="structure-details"><summary class="${summaryClass}">${summary}</summary><div class="structure-panel"><div class="structure-title"><b>${LANG==="en"?"Pre-breakout structure":"飆股前期結構回溯"}</b><small>${LANG==="en"?"As of":"資料截至"} ${d.as_of||"—"} · ${d.lookback_years||"—"}${LANG==="en"?"Y":" 年"}</small></div>${tags?`<div class="structure-tags">${tags}</div>`:""}${reason}${metrics}${chart}<div class="structure-note">${note}</div></div></details>`;
}
function initStructureChart(box){
  if(!box||box.dataset.ready==="1")return;box.dataset.ready="1";
  let rows=[],markers={};try{rows=JSON.parse(decodeURIComponent(box.dataset.series||""));markers=JSON.parse(decodeURIComponent(box.dataset.markers||""))}catch(e){}
  if(rows.length<2)return;
  const panel=box.closest(".structure-panel"),range=panel.querySelector(".structure-chart-range"),read=panel.querySelector(".structure-chart-read"),buttons=panel.querySelectorAll(".structure-chart-buttons button");
  const W=680,H=238,L=44,R=12,T=20,B=27,high=Number(box.dataset.high),maxWindow=rows.length;
  let win=Math.min(156,maxWindow),start=Math.max(0,maxWindow-win),drag=null;
  const clamp=()=>{win=Math.max(Math.min(52,maxWindow),Math.min(maxWindow,win));start=Math.max(0,Math.min(maxWindow-win,start))};
  const nearestDate=(date,a,b)=>{if(!date)return -1;const ts=Date.parse(date);let best=-1,dist=Infinity;for(let i=a;i<b;i++){const q=Math.abs(Date.parse(rows[i][0])-ts);if(q<dist){dist=q;best=i}}return best};
  function draw(){
    clamp();const visible=rows.slice(start,start+win),vals=visible.map(r=>Number(r[1]));let lo=Math.min(...vals),hi=Math.max(...vals);if(Number.isFinite(high)&&high>=lo*.92&&high<=hi*1.08){lo=Math.min(lo,high);hi=Math.max(hi,high)}let pad=Math.max((hi-lo)*.08,hi*.01,.01);lo-=pad;hi+=pad;const span=Math.max(.01,hi-lo),x=i=>L+(i-start)/Math.max(1,win-1)*(W-L-R),y=v=>T+(hi-v)/span*(H-T-B);
    const grid=[hi,(hi+lo)/2,lo].map(v=>`<line x1="${L}" x2="${W-R}" y1="${y(v)}" y2="${y(v)}" stroke="var(--grounds)" stroke-dasharray="4 3"/><text x="${L-5}" y="${y(v)+3}" text-anchor="end" font-size="10" fill="var(--mocha)">${v.toFixed(v>=100?0:1)}</text>`).join("");
    const pts=visible.map((r,k)=>`${x(start+k).toFixed(1)},${y(Number(r[1])).toFixed(1)}`).join(" ");
    const highLine=Number.isFinite(high)&&high>=lo&&high<=hi?`<line x1="${L}" x2="${W-R}" y1="${y(high)}" y2="${y(high)}" stroke="#a66b45" stroke-width="1.2" stroke-dasharray="6 4"/><text x="${W-R-3}" y="${y(high)-4}" text-anchor="end" font-size="10" fill="#a66b45">${LANG==="en"?"Prior high":"前高"} ${high}</text>`:"";
    const markerSpec=[["peak","前高","#a66b45"],["trough","低點","#3d8b67"],["breakout","突破","#b93c32"]];let marks="";markerSpec.forEach(([key,zh,color])=>{const i=nearestDate(markers[key],start,start+win);if(i>=start&&i<start+win){const v=Number(rows[i][1]);marks+=`<circle cx="${x(i)}" cy="${y(v)}" r="4" fill="${color}" stroke="#fff" stroke-width="1.5"/><text x="${x(i)}" y="${Math.max(11,y(v)-7)}" text-anchor="middle" font-size="9.5" fill="${color}">${LANG==="en"?{peak:"High",trough:"Low",breakout:"Breakout"}[key]:zh}</text>`}});
    box.innerHTML=`<svg viewBox="0 0 ${W} ${H}" aria-label="${LANG==="en"?"Draggable pre-breakout closing-price chart":"可拖曳的飆股前期收盤價圖"}">${grid}${highLine}<polyline points="${pts}" fill="none" stroke="var(--caramel-2)" stroke-width="2.2" stroke-linejoin="round" stroke-linecap="round"/>${marks}<line class="structure-guide" y1="${T}" y2="${H-B}" stroke="var(--espresso)" opacity="0"/><circle class="structure-dot" r="4" fill="var(--caramel-2)" stroke="#fff" stroke-width="1.5" opacity="0"/><text x="${L}" y="${H-6}" font-size="10" fill="var(--mocha)">${visible[0][0].slice(0,7)}</text><text x="${W-R}" y="${H-6}" text-anchor="end" font-size="10" fill="var(--mocha)">${visible.at(-1)[0].slice(0,7)}</text></svg>`;
    range.textContent=`${visible[0][0].slice(0,7)} — ${visible.at(-1)[0].slice(0,7)}`;wire();
  }
  function wire(){const svg=box.querySelector("svg"),guide=svg.querySelector(".structure-guide"),dot=svg.querySelector(".structure-dot");
    const inspect=clientX=>{const r=svg.getBoundingClientRect(),px=(clientX-r.left)/r.width*W;let i=Math.round(start+(px-L)/(W-L-R)*(win-1));i=Math.max(start,Math.min(start+win-1,i));const xx=L+(i-start)/Math.max(1,win-1)*(W-L-R),visible=rows.slice(start,start+win),vals=visible.map(q=>Number(q[1]));let lo=Math.min(...vals),hi=Math.max(...vals);const pad=Math.max((hi-lo)*.08,hi*.01,.01);lo-=pad;hi+=pad;if(Number.isFinite(high)&&high>=lo*.92&&high<=hi*1.08){lo=Math.min(lo,high-pad*.2);hi=Math.max(hi,high+pad*.2)}const yy=T+(hi-Number(rows[i][1]))/Math.max(.01,hi-lo)*(H-T-B);guide.setAttribute("x1",xx);guide.setAttribute("x2",xx);guide.setAttribute("opacity",".4");dot.setAttribute("cx",xx);dot.setAttribute("cy",yy);dot.setAttribute("opacity","1");read.textContent=`${rows[i][0]}  $${Number(rows[i][1]).toLocaleString()}`};
    const panTo=clientX=>{const r=box.getBoundingClientRect(),shift=Math.round((clientX-drag.x)/r.width*win);start=drag.start-shift;draw()};
    box.onpointerdown=e=>{e.preventDefault();drag={x:e.clientX,start};box.setPointerCapture(e.pointerId);svg.classList.add("dragging");inspect(e.clientX)};
    box.onpointermove=e=>{if(drag&&box.hasPointerCapture(e.pointerId))panTo(e.clientX);else if(e.pointerType==="mouse")inspect(e.clientX)};
    const release=e=>{drag=null;const current=box.querySelector("svg");if(current)current.classList.remove("dragging");if(box.hasPointerCapture(e.pointerId))box.releasePointerCapture(e.pointerId)};box.onpointerup=release;box.onpointercancel=release;
    box.onmousedown=e=>{if(e.button===0&&!drag){drag={x:e.clientX,start};const current=box.querySelector("svg");if(current)current.classList.add("dragging")}};
    box.onmousemove=e=>{if(drag&&e.buttons===1)panTo(e.clientX)};box.onmouseup=()=>{drag=null;const current=box.querySelector("svg");if(current)current.classList.remove("dragging")};
    svg.addEventListener("wheel",e=>{e.preventDefault();const center=start+win/2;win=Math.round(win*(e.deltaY>0?1.22:.82));clamp();start=Math.round(center-win/2);draw()},{passive:false});
  }
  buttons.forEach(b=>b.onclick=e=>{e.preventDefault();win=Math.min(maxWindow,Number(b.dataset.weeks));start=maxWindow-win;buttons.forEach(q=>q.classList.toggle("on",q===b));draw()});draw();
}
function setupStructureCharts(root){if(!root)return;root.querySelectorAll(".structure-details").forEach(d=>d.addEventListener("toggle",()=>{if(d.open)d.querySelectorAll(".structure-chart").forEach(initStructureChart)}))}

/* 符合日期：檢查多天時一併顯示「符合幾天」，否則看不出「部分符合」的差別 */
function fmtHit(s){
  const d = (s.hit_date || "").slice(5);           /* MM-DD */
  if (!s.days || s.days <= 1) return d;
  return d + " <small style='color:var(--mocha)'>(" + s.hit_days + "/" + s.days + ")</small>";
}

function rowsHtml(rows, showAlign, showQ, showHalves, showValuation, showStructure=false){
  return rows.map((s,i) =>
    "<tr data-i='"+i+"' data-sector=\"" + sectorKey(s) + "\">"
    + "<td>" + s.rank + "</td><td><b>" + s.symbol + "</b></td>"
    + "<td class='coname' title=\"" + s.name + "\">" + coName(s) + epsHalfPanel(s,showHalves) + "</td>"
    + (showStructure ? "<td>" + structurePanel(s) + "</td>" : "")
    + "<td class='sector' title=\"" + s.sector + "\">" + coSector(s) + "</td>"
    + "<td>" + s.price.toFixed(2) + "</td>"
    + (showQ ? "<td>" + fmtLast(s) + "</td><td>" + fmtLastPct(s) + "</td>" : "")
    + "<td class='" + (s.gap >= 0 ? "pos" : "neg") + "'>" + (s.gap >= 0 ? "+" : "") + s.gap.toFixed(2) + "%</td>"
    + "<td class='" + yoyCls(s.ret20) + "'>" + fmtYoY(s.ret20) + "</td>"
    + "<td class='" + yoyCls(s.ret60) + "'>" + fmtYoY(s.ret60) + "</td>"
    + "<td>" + momentumBadge(s.ret20,s.ret60) + "</td>"
    + (showValuation ? "<td>" + (s.per == null ? "—" : s.per.toFixed(2)) + "</td><td>" + (s.yield == null ? "—" : s.yield.toFixed(2) + "%") + "</td>" : "")
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
function cardsHtml(rows, showAlign, lastLabel, showQ, showHalves, showValuation, showStructure=false){
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
    + "<div class='kv'><span>" + t("th.ret20","20日累積漲幅") + "</span><b class='" + yoyCls(s.ret20) + "'>" + fmtYoY(s.ret20) + "</b></div>"
    + "<div class='kv'><span>" + t("th.ret60","60日累積漲幅") + "</span><b class='" + yoyCls(s.ret60) + "'>" + fmtYoY(s.ret60) + "</b></div>"
    + "<div class='kv'><span>" + t("th.strength","近期強弱") + "</span><b>" + momentumBadge(s.ret20,s.ret60) + "</b></div>"
    + (showValuation ? "<div class='kv'><span>" + t("th.per","本益比") + "</span><b>" + (s.per == null ? "—" : s.per.toFixed(2)) + "</b></div><div class='kv'><span>" + t("th.yield","殖利率") + "</span><b>" + (s.yield == null ? "—" : s.yield.toFixed(2) + "%") + "</b></div>" : "")
    + "<div class='kv'><span>" + t("th.eps","季EPS年增") + "</span><b class='"
      + yoyCls(s.eps_yoy) + "'>" + fmtYoY(s.eps_yoy) + "</b></div>"
    + "<div class='kv'><span>" + t("th.rev","季營收年增") + "</span><b class='"
      + yoyCls(s.rev_yoy) + "'>" + fmtYoY(s.rev_yoy) + "</b></div>"
    + epsHalfPanel(s,showHalves)
    + "<div class='kv'><span>" + t("th.nh","創新高") + "</span><b>" + fmtNH(s.new_high) + "</b></div>"
    + (showAlign ? "<div class='kv'><span>" + t("th.align","均線排列")
                 + "</span><b>" + alignName(s.align) + "</b></div>" : "")
    + "<div class='kv'><span>" + lastLabel + "</span><b>" + fmtHit(s) + "</b></div>"
    + (showStructure ? structurePanel(s) : "")
    + "</div></details>").join("") + "</div>";
}

function applyFilter(){ applyAll("tb1", "cd1", lastRows, "secFilter", "epsFilter", "alignFilter", "nhFilter", "momentumFilter"); }

/* ---- 飆股拉回找買點 ---- */
let lastRows3 = [], lastMeta3 = {};
if ($("#go3")) $("#go3").onclick = () => {
  const params = {
    universe_n: parseInt(val("universe3"), 10),
    ma: parseInt(val("ma3"), 10),
    align: val("align3"),
    eps_halves: !!($("#epsHalves3") && $("#epsHalves3").checked),
    valuation: !!($("#valuation3") && $("#valuation3").checked),
    structure_history: !!($("#structureHistory3") && $("#structureHistory3").checked)
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
  const showHalves3 = !!($("#epsHalves3") && $("#epsHalves3").checked);
  const showValuation3 = !!($("#valuation3") && $("#valuation3").checked);
  const showStructure3 = !!($("#structureHistory3") && $("#structureHistory3").checked);
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
  {
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
       + momentumControls("momentumFilter3","sortFilter3","applyFilter3","tb3","cd3")
       + "</div>";
  }
  h += "<div class='tblwrap res-wide'><table><thead><tr>"
     + "<th>" + t("th.rank","市值排名") + "</th><th>" + t("th.sym","代號")
     + "</th><th>" + t("th.name","公司名稱") + "</th>" + (showStructure3 ? "<th>" + (LANG==="en"?"Pre-breakout structure":"前期結構") + "</th>" : "") + "<th>" + t("th.sector","產業") + "</th>"
     + "<th>" + t("th.close","收盤") + "</th>"
     + (showQ ? "<th>" + t("th.last","現價") + "</th><th>"
              + t("th.lastgap","與收盤差%") + "</th>" : "")
     + "<th>" + t("th.gap","均線乖離%") + "</th>"
     + "<th class='sort-th' onclick=\"toggleUsSort('tb3','cd3','ret20','sortFilter3')\">" + t("th.ret20","20日累積漲幅") + " ↕</th><th class='sort-th' onclick=\"toggleUsSort('tb3','cd3','ret60','sortFilter3')\">" + t("th.ret60","60日累積漲幅") + " ↕</th><th>" + t("th.strength","近期強弱") + "</th>"
     + (showValuation3 ? "<th>" + t("th.per","本益比") + "</th><th>" + t("th.yield","殖利率") + "</th>" : "")
     + "<th>" + t("th.eps","季EPS年增") + "</th><th>" + t("th.rev","季營收年增")
     + "</th><th>" + t("th.nh","創新高") + "</th>"
     + (showAlign ? "<th>" + t("th.align","均線排列") + "</th>" : "")
     + "<th>" + t("th.asof","資料日期") + "</th></tr></thead><tbody id='tb3'>"
     + rowsHtml(lastRows3, showAlign, showQ, showHalves3, showValuation3, showStructure3) + "</tbody></table></div>";
  h += "<div id='cd3'>" + cardsHtml(lastRows3, showAlign, t("th.asof","資料日期"), showQ, showHalves3, showValuation3, showStructure3) + "</div>";
  $("#result3").innerHTML = h;
  if(showStructure3)setupStructureCharts($("#result3"));
}

function applyFilter3(){ applyAll("tb3", "cd3", lastRows3, "secFilter3", "epsFilter3", "alignFilter3", "nhFilter3", "momentumFilter3"); }

/* ---- 強勢股整理觀察 ---- */
if ($("#goLev")) $("#goLev").onclick = async () => {
  const btn=$("#goLev"), st=$("#statusLev");
  btn.disabled=true; st.textContent = LANG==="en" ? "Loading…" : "讀取中…";
  try{
    const r = await fetch("/api/leverage",{method:"POST",
      headers:{"Content-Type":"application/json","X-App-Token":APP_TOKEN},body:"{}"});
    const j = await r.json();
    if(r.status===403){ if(retryOnStaleToken(j)) return; }
    /* ⚠️ 還沒好的時候要說「在準備」，不要說「沒有資料」——後者聽起來像壞掉。 */
    if(!j.rows || !j.rows.length){
      st.textContent = j.error || (LANG==="en"?"No data":"目前沒有資料"); return;
    }
    st.innerHTML = (LANG==="en"
      ? `Complete months: <span class="count">${j.months}</span> · data through ${j.data_date}`
      : `完整月份 <span class="count">${j.months}</span> 個 · 資料截至 ${j.data_date}`);
    const pct = v => (v>0?"+":"") + v.toFixed(2) + "%";
    // ⚠️ 美股慣例：漲綠跌紅（跟台股相反，不要照抄台股配色）
    const col = v => v>0 ? 'style="color:#1e8e4e"' : (v<0 ? 'style="color:#c0392b"' : "");
    const mult = r => (r===null||r===undefined) ? "—" : r.toFixed(2)+"x";
    // ⚠️ 按年度分組，月份收在 <details> 裡。最新年度預設展開 ——
    //    24 個月一次攤開會讓人找不到重點，年度層才是第一眼該看的。
    let html="";
    (j.years||[]).forEach((yr,i)=>{
      const ytag = yr.partial ? ` <span class="badge">${LANG==="en"?yr.n+" mo":"僅 "+yr.n+" 個月"}</span>` : "";
      let trs="";
      for(const s of yr.months){
        const tag = s.partial ? ` <span class="badge">${LANG==="en"?"partial":"未完月"}</span>` : "";
        trs += `<tr><td>${s.m.slice(5)}${LANG==="en"?"":"月"}${tag}</td><td ${col(s.etf)}>${pct(s.etf)}</td><td ${col(s.idx)}>${pct(s.idx)}</td><td>${mult(s.ratio)}</td></tr>`;
      }
      html += `<details class="scard"${i===0?" open":""}><summary><span class="sc-l"><b>${yr.y}</b>${ytag}</span>`+
        `<span class="sc-r" ${col(yr.etf)}>${pct(yr.etf)}</span></summary><div class="scard-body">`+
        `<div class="kv"><span>${LANG==="en"?"Nasdaq Composite":"納斯達克綜合"}</span><b>${pct(yr.idx)}</b></div>`+
        `<div class="kv"><span>${LANG==="en"?"Realised multiple":"實際倍數"}</span><b>${mult(yr.ratio)}</b></div>`+
        `<table style="margin-top:10px"><thead><tr><th>${LANG==="en"?"Month":"月份"}</th><th>${LANG==="en"?"2x":"正2"}</th>`+
        `<th>${LANG==="en"?"Index":"納斯達克"}</th><th>${LANG==="en"?"Mult.":"倍數"}</th></tr></thead><tbody>${trs}</tbody></table></div></details>`;
    });
    const sum = `<div class="card"><h2>${LANG==="en"?"Two-year summary":"兩年彙總"}</h2><div style="font-size:14px;line-height:2">`+
      `${LANG==="en"?"2x cumulative":"正2 累積"} <b>${pct(j.cum_etf)}</b> · ${LANG==="en"?"Nasdaq":"納斯達克"} <b>${pct(j.cum_idx)}</b> · `+
      `${LANG==="en"?"realised":"實際放大"} <b>${mult(j.cum_ratio)}</b><br>`+
      `${LANG==="en"?"Up":"上漲"} ${j.up} / ${LANG==="en"?"down":"下跌"} ${j.down} ${LANG==="en"?"months":"個月"} · `+
      `${LANG==="en"?"best":"最好"} ${pct(j.best)} · ${LANG==="en"?"worst":"最差"} ${pct(j.worst)}<br>`+
      `${LANG==="en"?"Monthly volatility":"月報酬標準差"}：${j.vol_etf.toFixed(2)}% vs ${j.vol_idx.toFixed(2)}% `+
      `(${(j.vol_etf/j.vol_idx).toFixed(2)}x)</div></div>`;
    /* ⚠️ 舊快取可能沒有 years（換欄位卻沒換快取檔名時會發生）。
       直接說出來，不要留一塊空白讓人以為壞掉。 */
    $("#resultLev").innerHTML = (html || '<div class="status">'+
      (LANG==="en" ? "Year grouping unavailable — cached data is in an older format."
                   : "年度分組尚未產生（快取為舊格式），請稍後再試。")+'</div>') + sum;
  }catch(e){ st.textContent=(LANG==="en"?"Failed: ":"讀取失敗：")+e; }
  finally{ btn.disabled=false; }
};

/* 三個條件同時成立才顯示（AND）。用列的索引對回原始資料，
   避免從 DOM 反推數值時被格式化字串（「—」「+12.3%」）搞混。

   ⚠️ **表格與卡片要一起篩**。只篩表格的話，手機上按下拉選單完全沒反應
   —— 因為手機看到的是卡片，表格早就被 CSS 隱藏了。 */
function applyAll(tbId, cdId, rows, secId, epsId, alignId, nhId, momentumId){
  const sec = $("#" + secId) ? $("#" + secId).value : "";
  const eps = $("#" + epsId) ? $("#" + epsId).value : "";
  const alg = (alignId && $("#" + alignId)) ? $("#" + alignId).value : "";
  const nh  = (nhId && $("#" + nhId)) ? $("#" + nhId).value : "";
  const momentum = (momentumId && $("#" + momentumId)) ? $("#" + momentumId).value : "";

  function pass(r){
    if (!r) return true;
    if (sec && r.sector !== sec) return false;
    if (eps && yoyBucket(r.eps_yoy) !== eps) return false;
    if (alg && r.align !== alg) return false;
    if (nh === "any" && !r.new_high) return false;
    if (nh && nh !== "any" && r.new_high !== nh) return false;
    if (!momentumPass(momentum,r.ret20,r.ret60)) return false;
    return true;
  }

  document.querySelectorAll("#" + tbId + " tr").forEach((tr) => {
    tr.style.display = pass(rows[Number(tr.dataset.i)]) ? "" : "none";
  });
  document.querySelectorAll("#" + cdId + " .scard").forEach((cd) => {
    cd.style.display = pass(rows[Number(cd.dataset.i)]) ? "" : "none";
  });
}

function drawHomeIndex(days=756){
  const box=$("#homeIndexChart");if(!box)return;let all=[];try{all=JSON.parse(box.dataset.series||"[]")}catch(e){}
  const rows=all.slice(-days);if(rows.length<2){box.innerHTML='<div class="status">No index data</div>';return}
  const prices=rows.map(r=>Number(r[1])).sort((a,b)=>a-b),n=prices.length,median=n%2?prices[(n-1)/2]:(prices[n/2-1]+prices[n/2])/2;
  const vals=rows.map(r=>(Number(r[1])/median-1)*100),W=900,H=190,L=45,R=72,T=12,B=25,lo=Math.min(0,...vals),hi=Math.max(0,...vals),span=Math.max(.01,hi-lo);
  const x=i=>L+i/(rows.length-1)*(W-L-R),y=v=>T+(hi-v)/span*(H-T-B),pct=v=>`${v>0?'+':''}${v.toFixed(0)}%`;
  const pts=vals.map((v,i)=>`${x(i).toFixed(1)},${y(v).toFixed(1)}`).join(' '),grid=[hi,0,lo].filter((v,i,a)=>i===0||Math.abs(v-a[i-1])>.5).map(v=>`<line x1="${L}" x2="${W-R}" y1="${y(v)}" y2="${y(v)}" stroke="var(--grounds)" stroke-dasharray="4 3"/><text x="${L-6}" y="${y(v)+3}" text-anchor="end" font-size="10" fill="var(--mocha)">${pct(v)}</text>`).join('');
  box.innerHTML=`<div class="home-chart-read"></div><svg viewBox="0 0 ${W} ${H}" aria-label="Nasdaq versus period median">${grid}<polyline points="${pts}" fill="none" stroke="var(--caramel-2)" stroke-width="2"/><line class="home-chart-guide" y1="${T}" y2="${H-B}" stroke="var(--mocha)" opacity="0"/><circle class="home-chart-dot" r="4" fill="var(--caramel-2)" stroke="var(--foam)" stroke-width="1.5" opacity="0"/><text x="${L}" y="${H-5}" font-size="10" fill="var(--mocha)">${rows[0][0].slice(0,7)}</text><text x="${W-R}" y="${H-5}" text-anchor="end" font-size="10" fill="var(--mocha)">${rows.at(-1)[0].slice(0,7)}</text><text x="${W-4}" y="${y(0)+3}" text-anchor="end" font-size="10" fill="var(--mocha)">${LANG==='en'?'Period median · 0%':'期間中位數 · 0%'}</text></svg>`;
  const svg=box.querySelector('svg'),read=box.querySelector('.home-chart-read'),guide=box.querySelector('.home-chart-guide'),dot=box.querySelector('.home-chart-dot');
  const show=clientX=>{const r=svg.getBoundingClientRect();let i=Math.round((((clientX-r.left)/r.width*W)-L)/(W-L-R)*(rows.length-1));i=Math.max(0,Math.min(rows.length-1,i));const gx=x(i),v=vals[i];read.textContent=LANG==='en'?`${rows[i][0]} · Nasdaq ${Number(rows[i][1]).toLocaleString()} · ${v>=0?'+':''}${v.toFixed(2)}% vs median`:`${rows[i][0]}　納斯達克 ${Number(rows[i][1]).toLocaleString()}　相對中位數 ${v>=0?'+':''}${v.toFixed(2)}%`;guide.setAttribute('x1',gx);guide.setAttribute('x2',gx);guide.setAttribute('opacity','.45');dot.setAttribute('cx',gx);dot.setAttribute('cy',y(v));dot.setAttribute('opacity','1')};
  svg.addEventListener('pointerdown',e=>{e.preventDefault();svg.classList.add('dragging');svg.setPointerCapture(e.pointerId);show(e.clientX)});svg.addEventListener('pointermove',e=>{if(e.pointerType==='mouse'||svg.hasPointerCapture(e.pointerId)){e.preventDefault();show(e.clientX)}});const release=e=>{svg.classList.remove('dragging');if(svg.hasPointerCapture(e.pointerId))svg.releasePointerCapture(e.pointerId)};svg.addEventListener('pointerup',release);svg.addEventListener('pointercancel',release);show(svg.getBoundingClientRect().right-(R/W)*svg.getBoundingClientRect().width);
}
document.querySelectorAll('.market-periods button').forEach(b=>b.onclick=()=>{document.querySelectorAll('.market-periods button').forEach(x=>x.classList.toggle('on',x===b));drawHomeIndex(Number(b.dataset.days))});drawHomeIndex();

/* ---- 大盤詳細數據：市場寬度的歷史折線圖 ----
   ⚠️ **展開才抓**，收合再展開不重複請求（照台股版 baro-box 的做法）。
      首頁每個訪客都會載入，不能一進來就打 API。
   ⚠️ 折線圖用**內嵌 SVG 自己畫**，不引外部圖表庫 ——
      這個專案刻意只有 flask/requests/gunicorn，前端也維持零依賴。 */
const brBox = $("#brBox");
brBox && brBox.addEventListener("toggle", () => {
  if (!brBox.open || brBox.dataset.loaded) return;
  brBox.dataset.loaded = "1";
  /* 新首頁已顯示市場寬度與指數中位數；收合區只保留市場階段，避免觀點二、三重複。 */
  $("#brStatus").textContent = "";
  return;
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

/* 大盤折線圖的游標互動：顯示日期、指數與相對三年中位數的位置。
   ⚠️ 用 pointer 事件（滑鼠與觸控共用一套），不要分別綁 mouse/touch。
   ⚠️ SVG 是 width:100% 縮放的，**client 座標不等於 viewBox 座標**，
      一定要用 getBoundingClientRect() 換算，否則在手機上會整個對不準。 */
function wireBreadthHover(j){
  const svg = $("#brSvg"), read = $("#brRead"),
        guide = $("#brGuide"), dot = $("#brDot");
  if (!svg || !read) return;
  const S = j.market_series || [];
  if (!S.length) return;
  const PAD_L = +svg.dataset.padl, PAD_R = +svg.dataset.padr,
        PAD_T = +svg.dataset.padt, PAD_B = +svg.dataset.padb,
        W = +svg.dataset.w, H = +svg.dataset.h;
  const iw = W - PAD_L - PAD_R, ih = H - PAD_T - PAD_B;
  const ymin = +svg.dataset.ymin, ymax = +svg.dataset.ymax;
  const xOf = i => PAD_L + (S.length < 2 ? 0 : i / (S.length - 1) * iw);
  const yOf = v => PAD_T + (ymax - v) / Math.max(.01, ymax - ymin) * ih;

  const fmt = (d, close, pct) => (LANG === "en")
    ? `${d} · ${Number(close).toLocaleString()} · ${pct >= 0 ? "+" : ""}${pct.toFixed(1)}% vs 3y median`
    : `${d} · ${Number(close).toLocaleString()} · 相對三年中位數 ${pct >= 0 ? "+" : ""}${pct.toFixed(1)}%`;
  /* 沒在指的時候顯示最新一天，不要留白 */
  const rest = () => {
    read.textContent = fmt(S[S.length - 1][0], S[S.length - 1][1], S[S.length - 1][2]);
    guide.setAttribute("opacity", "0");
    dot.setAttribute("opacity", "0");
  };
  rest();

  function at(clientX){
    const r = svg.getBoundingClientRect();
    const vx = (clientX - r.left) / r.width * W;          // client → viewBox
    let i = Math.round((vx - PAD_L) / iw * (S.length - 1));
    i = Math.max(0, Math.min(S.length - 1, i));
    const [d, close, pct] = S[i];
    read.textContent = fmt(d, close, pct);
    const gx = xOf(i).toFixed(1);
    guide.setAttribute("x1", gx); guide.setAttribute("x2", gx);
    guide.setAttribute("opacity", ".35");
    dot.setAttribute("cx", gx); dot.setAttribute("cy", yOf(pct).toFixed(1));
    dot.setAttribute("opacity", "1");
  }
  svg.addEventListener("pointermove", e => { e.preventDefault(); at(e.clientX); });
  svg.addEventListener("pointerdown", e => { e.preventDefault(); at(e.clientX); });
  svg.addEventListener("pointerleave", rest);
  svg.addEventListener("pointercancel", rest);
}

/* 今日快照：站上 50／150／200MA 的家數 ＋ 創 60 日新高家數。
   ⚠️⚠️ 用的是**美股的線**（50／150／200），不是台股的 60／120／240 ——
      50MA 相當於台股季線的地位、150MA 是趨勢模板線（與 breadth 折線圖同一條）、
      200MA 是美股最經典的長期線。**照搬台股的數字會跟站上其他頁面說不同語言。**
   📌 折線圖看的是「150MA 寬度的歷史走勢」，這裡看的是「今天各條線的橫斷面」——
      兩者互補：一個回答「現在算高還是低」，一個回答「現在是誰在撐」。 */
function maSnapshotHtml(j){
  const s = j.snapshot || {}, recent = recentReturnHtml(j.market_counts);
  if ((!s.rows || !s.rows.length) && !recent) return "";
  /* 美股慣例：漲綠跌紅（跟台股相反，不要照抄台股配色） */
  const col = (v, mid) => v >= mid ? "#1e8e4e" : "#c0392b";
  let h = `<div class="card"><h2>${LANG==="en"?"View 2 · Market breadth":"觀點二：市場寬度分析"}</h2>`;
  h += `<div style="font-size:13px;color:#666;margin-bottom:8px">
    ${t("br.snapIntro","指數會被少數權值股撐住。這裡看的是「有多少家個股真的站在趨勢上」——指數與寬度背離時，通常是寬度先說實話。")}</div>`;
  h += recent;
  if (!s.rows || !s.rows.length) {
    return h + `<div style="font-size:13px;color:#999">${t("br.nodata","市場寬度更新中…")}</div></div>`;
  }
  h += `<div style="margin-top:4px;font-size:14px;color:#666">${LANG==="en"?"Top 300 by market cap: stocks above each average":"市值前 300 大：站上均線的家數"}</div>`;
  for (const r of s.rows) {
    if (r.pct === null || r.pct === undefined) {
      h += `<div class="baro-row"><span>${t("br.above","站上")} ${r.label}</span>
            <span style="color:#999">${t("br.nodata","資料不足")}</span></div>`;
      continue;
    }
    h += `<div class="baro-row"><span>${t("br.above","站上")} ${r.label}</span>`+
         `<b style="color:${col(r.pct,50)}">${r.above} / ${r.base}　${r.pct}%</b></div>`;
  }
  const nh = s.newhigh;
  if (nh && nh.pct !== null && nh.pct !== undefined) {
    /* ⚠️ 創新高的門檻用 20% 不是 50% —— 它本來就不會過半，
       用 50% 當分界會永遠是紅的。 */
    h += `<div class="baro-row"><span>${t("br.nh","創 "+nh.window+" 日新高")}</span>`+
         `<b style="color:${col(nh.pct,20)}">${nh.above} / ${nh.base}　${nh.pct}%</b></div>`;
  }
  /* ⚠️⚠️ 分母不一樣一定要講。新上市的股票湊不滿 200 天，
     不列入 200MA 的分母；不說明的話讀者會以為三條線可以直接互比。 */
  h += `<div style="font-size:12px;color:#999;line-height:1.7;margin-top:6px">
    ${t("br.snapNote","分母是「有足夠交易日可以計算該均線」的家數，所以三條線的分母不同（新上市股票湊不滿 200 天）。創新高採 2% 容差（收盤達 60 日高點的 98% 即算）。均線家數看「還站在趨勢上」，創新高家數看「正在突破」——後者通常掉得更早，因為它需要新的買盤。")}
    ${s.date ? "<br>" + t("br.snapAsOf","資料日期") + " " + s.date : ""}</div></div>`;
  return h;
}

/* 市值前 300 大的三年家數趨勢。三張圖共用日期範圍與 0~300 刻度，
   才能直接比較不同條件的擴散／收縮，而不會被各圖自動縮放誤導。 */
function recentReturnHtml(m){
  const q=m&&m.recent_returns, rows=q&&q.rows||[];
  if(!rows.length)return "";
  const sign=v=>`${Number(v)>=0?"+":""}${Number(v).toFixed(2)}%`;
  const ease=p=>p>=65
    ?(LANG==="en"?"Most stocks rose; stock selection was relatively easy.":"多數個股上漲，這段期間選股相對容易。")
    :p>=55?(LANG==="en"?"More than half rose; stock selection leaned easier.":"上漲家數過半，這段期間選股偏容易。")
    :p>=45?(LANG==="en"?"Advancers and decliners were balanced; results were mixed.":"漲跌家數接近，這段期間選股結果分化。")
    :(LANG==="en"?"Most stocks fell; stock selection was difficult.":"多數個股下跌，這段期間選股較困難。");
  const strength=v=>v>=5
    ?(LANG==="en"?"The median gain was strong.":"個股中位漲幅明顯。")
    :v>0?(LANG==="en"?"The median stock posted a moderate gain.":"個股中位報酬溫和上漲。")
    :v>-5?(LANG==="en"?"The median stock declined moderately.":"個股中位報酬溫和下跌。")
    :(LANG==="en"?"The median decline was pronounced.":"個股中位跌幅明顯。");
  const body=rows.map(r=>`<div style="padding:9px 0;border-top:1px solid rgba(120,90,65,.12)">
    <div style="display:flex;justify-content:space-between;gap:12px;align-items:baseline">
      <b>${LANG==="en"?`Past ${r.days} sessions`:`過去 ${r.days} 個交易日`}</b>
      <span style="font-family:var(--font-num);color:var(--mocha)">${r.winners} / ${r.base} ${LANG==="en"?"stocks up":"檔上漲"} · ${r.win_pct}%</span>
    </div>
    <div style="font-size:13px;line-height:1.7;margin-top:3px">${ease(Number(r.win_pct))} ${strength(Number(r.median_return))}</div>
    <div style="font-size:12px;color:#888">${LANG==="en"?"Median stock return":"個股報酬中位數"} <b style="color:${Number(r.median_return)>=0?'#1e8e4e':'#c0392b'}">${sign(r.median_return)}</b></div>
  </div>`).join("");
  return `<div style="margin:12px 0 16px;padding:12px 14px;border-radius:12px;background:rgba(255,255,255,.48)">
    <b>${LANG==="en"?"Recent stock-selection environment (backward-looking)":"近期選股環境（回顧）"}</b>${body}
    <div style="font-size:11.5px;color:#999;line-height:1.6">${LANG==="en"?"Based on the current top 300 stocks. This summarizes realised returns and does not predict future performance.":`資料截至 ${q.as_of||"—"}，以目前市值前 300 大為樣本；只總結已實現的過去報酬，不預測未來。`}</div></div>`;
}

function marketCountHtml(j){
  const m = j.market_counts, series = m && m.series;
  if (!series) return "";
  const defs = [
    ["strict10", LANG === "en" ? "Strict bullish and above 10MA" : "嚴格多頭排列且站上 10 日線"],
    ["above100", LANG === "en" ? "Price above 100MA" : "股價站上 100 日線"],
    ["above150", LANG === "en" ? "Price above 150MA" : "股價站上 150 日線"]
  ];
  const W=560,H=132,L=30,R=8,T=8,B=18, max=Math.max(1,Number(m.universe)||300);
  const y=v=>T+(max-v)/max*(H-T-B);
  const chart=(key,title)=>{
    const S=series[key]||[];
    if(!S.length)return "";
    const x=i=>L+(S.length<2?0:i/(S.length-1)*(W-L-R));
    const pts=S.map((r,i)=>`${x(i).toFixed(1)},${y(r[1]).toFixed(1)}`).join(" ");
    const first=S[0][0],last=S[S.length-1][0],cur=S[S.length-1][1];
    return `<div style="margin:0 0 18px">
      <div style="display:flex;justify-content:space-between;gap:12px;font-size:13px;margin-bottom:3px">
        <b>${title}</b><span id="mcRead-${key}" style="font-family:var(--font-num);color:var(--mocha)">${last} · ${cur}</span>
      </div>
      <svg class="mcSvg" data-key="${key}" viewBox="0 0 ${W} ${H}" style="width:100%;height:auto;display:block;touch-action:none">
        <text x="${L-4}" y="${y(max)+3}" text-anchor="end" font-size="9" fill="#aaa">${max}</text>
        <text x="${L-4}" y="${y(0)+3}" text-anchor="end" font-size="9" fill="#aaa">0</text>
        <line x1="${L}" x2="${W-R}" y1="${y(0)}" y2="${y(0)}" stroke="#ddd"/>
        <polyline points="${pts}" fill="none" stroke="var(--caramel-2)" stroke-width="1.7" stroke-linejoin="round"/>
        <line class="mcGuide" y1="${T}" y2="${H-B}" stroke="var(--mocha)" opacity="0"/>
        <circle class="mcDot" r="3.2" fill="var(--espresso)" opacity="0"/>
        <text x="${L}" y="${H-4}" font-size="9" fill="#aaa">${first}</text>
        <text x="${W-R}" y="${H-4}" text-anchor="end" font-size="9" fill="#aaa">${last}</text>
      </svg></div>`;
  };
  return `<div class="card"><h2>${LANG==="en"?"Market stock counts · 3 years":"大盤家數走勢 · 三年"}</h2>`+
    recentReturnHtml(m)+
    defs.map(d=>chart(d[0],d[1])).join("")+
    `<div style="font-size:12px;color:#999">${LANG==="en"?"Same top-300 universe, date range and vertical scale across all three charts.":"三張圖統一使用市值前 300 大、三年日期範圍與相同縱軸刻度。"}</div></div>`;
}

function wireMarketCountHover(j){
  const m=j.market_counts, all=m&&m.series;
  if(!all)return;
  document.querySelectorAll(".mcSvg").forEach(svg=>{
    const key=svg.dataset.key,S=all[key]||[],read=$("#mcRead-"+key);
    if(!S.length||!read)return;
    const W=560,H=132,L=30,R=8,T=8,B=18,max=Math.max(1,Number(m.universe)||300);
    const x=i=>L+(S.length<2?0:i/(S.length-1)*(W-L-R));
    const y=v=>T+(max-v)/max*(H-T-B),guide=svg.querySelector(".mcGuide"),dot=svg.querySelector(".mcDot");
    const rest=()=>{const r=S[S.length-1];read.textContent=`${r[0]} · ${r[1]}`;guide.setAttribute("opacity","0");dot.setAttribute("opacity","0");};
    const at=clientX=>{const r=svg.getBoundingClientRect(),vx=(clientX-r.left)/r.width*W;
      let i=Math.round((vx-L)/(W-L-R)*(S.length-1));i=Math.max(0,Math.min(S.length-1,i));
      const row=S[i],gx=x(i).toFixed(1);read.textContent=`${row[0]} · ${row[1]}`;
      guide.setAttribute("x1",gx);guide.setAttribute("x2",gx);guide.setAttribute("opacity",".35");
      dot.setAttribute("cx",gx);dot.setAttribute("cy",y(row[1]).toFixed(1));dot.setAttribute("opacity","1");};
    svg.addEventListener("pointermove",e=>{e.preventDefault();at(e.clientX)});
    svg.addEventListener("pointerdown",e=>{e.preventDefault();at(e.clientX)});
    svg.addEventListener("pointerleave",rest);svg.addEventListener("pointercancel",rest);rest();
  });
}

function breadthHtmlLegacy(j){
  const S = j.series || [];
  if (!S.length) return maSnapshotHtml(j);   /* 折線圖沒資料時，至少把快照顯示出來 */
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
       <b>washout threshold (${j.wash}%)</b>. This breadth chart is independent of the
       five-stage label; the label uses the index's 5/10/20/60/120-day MA alignment and distance.<br>
       Percentiles above cover the ${j.span_years} years shown here; the
       ${j.top}%/${j.wash}% thresholds were set from a 10-year backtest.<br>
       Historical breadth is recalculated using today's constituents, so earlier
       values may be biased upward (survivorship bias).</p>`
    : `<p style="font-size:12px;color:var(--mocha);line-height:1.8;margin:10px 0 0">
       紅線是<b>頂部門檻 ${j.top}%</b>，綠線是<b>洗盤門檻 ${j.wash}%</b>。
       這張寬度圖與四階段標籤分開判讀；四階段改用大盤 5／10／20／60／120 日均線排列與乖離。
       150MA 寬度只描述有多少成分股仍站在中長期趨勢上。<br>
       ⚠️ 上面的分位數只涵蓋圖上這 ${j.span_years} 年；
       ${j.top}%／${j.wash}% 的門檻是用 10 年回測訂的，兩者母體不同。<br>
       歷史寬度以今日成分股回算，較早數值可能因存活者偏誤而偏高。</p>`;

  /* 今日快照放在折線圖之後：先看「歷史上算高還是低」，再看「今天是誰在撐」。 */
  return idxHtml
       + marketCountHtml(j)
       + `<div style="font-size:12.5px;color:var(--mocha);margin:2px 0 6px">${head}</div>`
       + svg + `<div style="margin-top:10px">${stats}</div>` + note
       + maSnapshotHtml(j);
}

/* 近三年納斯達克綜合指數。縱軸不是一般報酬率：三年價格中位數固定為 0%，
   每一天顯示相對該中位數的位置；圖頂就是三年最高點。 */
function breadthHtml(j){
  const S = j.market_series || [];
  let idxHtml = "";
  if (j.idx){
    const q=j.idx, col=q.close>q.ma100?"#CB4B3A":"#4A7C64";
    idxHtml=`<div style="font-size:12.5px;color:var(--mocha);margin:2px 0 6px">${LANG==="en"?"Nasdaq Composite":"納斯達克綜合指數"} <span style="font-family:var(--font-num)">${q.date}</span></div>
      <div style="display:flex;align-items:baseline;gap:10px;margin-bottom:12px;flex-wrap:wrap">
      <b style="font-family:var(--font-num);font-size:24px;color:var(--espresso)">${q.close.toLocaleString()}</b>
      <span style="font-size:12.5px;color:${col}">50MA ${q.ma50.toLocaleString()} (${q.gap50>0?"+":""}${q.gap50}%) · 100MA ${q.ma100.toLocaleString()} (${q.gap100>0?"+":""}${q.gap100}%)</span></div>`;
  }
  if (!S.length) return maSnapshotHtml(j);

  const W=560,H=178,L=46,R=10,T=14,B=22,iw=W-L-R,ih=H-T-B;
  const pcts=S.map(r=>Number(r[2]));
  const ymin=Math.min(0,...pcts), ymax=Math.max(0,...pcts);
  const span=Math.max(.01,ymax-ymin);
  const x=i=>L+(S.length<2?0:i/(S.length-1)*iw);
  const y=v=>T+(ymax-v)/span*ih;
  const pts=S.map((r,i)=>`${x(i).toFixed(1)},${y(r[2]).toFixed(1)}`).join(" ");
  const pct=v=>`${v>0?"+":""}${Number(v).toFixed(1)}%`;
  const first=S[0][0], last=S[S.length-1][0], cur=S[S.length-1];
  const axis=(v,label)=>`<text x="${L-5}" y="${(y(v)+3).toFixed(1)}" text-anchor="end" font-size="9" fill="#888" font-family="var(--font-num)">${label}</text>`;
  const chart=`<div class="card"><h2>${LANG==="en"?"View 3 · Nasdaq position over 3 years":"觀點三：大盤近三年位置"}</h2>
    ${idxHtml}
    <div id="brRead" style="font-family:var(--font-num);font-size:12px;color:var(--mocha);height:18px;margin-bottom:3px"></div>
    <svg id="brSvg" viewBox="0 0 ${W} ${H}" style="width:100%;height:auto;display:block;touch-action:none"
      data-padl="${L}" data-padr="${R}" data-padt="${T}" data-padb="${B}" data-w="${W}" data-h="${H}" data-ymin="${ymin}" data-ymax="${ymax}">
      ${axis(ymax,pct(ymax))}${axis(0,"0%")}${ymin<0?axis(ymin,pct(ymin)):""}
      <line x1="${L}" x2="${W-R}" y1="${y(0)}" y2="${y(0)}" stroke="var(--mocha)" stroke-width="1.2" opacity=".55"/>
      <polyline points="${pts}" fill="none" stroke="var(--caramel-2)" stroke-width="1.8" stroke-linejoin="round"/>
      <circle cx="${x(S.length-1).toFixed(1)}" cy="${y(cur[2]).toFixed(1)}" r="2.8" fill="var(--caramel-2)"/>
      <line id="brGuide" y1="${T}" y2="${H-B}" stroke="var(--mocha)" stroke-width="1" opacity="0"/>
      <circle id="brDot" r="3.2" fill="var(--espresso)" opacity="0"/>
      <text x="${L}" y="${H-4}" font-size="9" fill="#aaa">${first}</text>
      <text x="${W-R}" y="${H-4}" text-anchor="end" font-size="9" fill="#aaa">${last}</text>
    </svg>
    <div style="display:grid;grid-template-columns:repeat(3,1fr);gap:8px;margin-top:10px;font-size:12px;text-align:center">
      <div><span style="color:var(--mocha)">${LANG==="en"?"3y median · 0%":"三年中位數 · 0%"}</span><br><b>${Number(j.market_median).toLocaleString()}</b></div>
      <div><span style="color:var(--mocha)">${LANG==="en"?"3y high":"三年最高點"}</span><br><b>${Number(j.market_high).toLocaleString()} · ${pct(ymax)}</b></div>
      <div><span style="color:var(--mocha)">${LANG==="en"?"Latest":"最新"}</span><br><b>${Number(cur[1]).toLocaleString()} · ${pct(cur[2])}</b></div>
    </div>
    <p style="font-size:12px;color:var(--mocha);line-height:1.8;margin:10px 0 0">${LANG==="en"
      ?"The vertical-axis 0% is the median Nasdaq Composite close over the displayed three years. Values above or below show distance from that median; this is not a return from the first date."
      :"縱軸 0% 是圖中近三年納斯達克綜合指數收盤中位數；向上最高點就是三年最高點，向下則是低於中位數的位置。這不是從起始日計算的報酬率。"}</p></div>`;
  return maSnapshotHtml(j) + chart;
}

/* ---- 升級專業版：創新高／RS ---- */
let lastProHigh = null, lastProRs = null;
const proPct = v => `<span class="${Number(v) >= 0 ? 'pos' : 'neg'}">${Number(v) >= 0 ? '+' : ''}${Number(v).toFixed(2)}%</span>`;
const proKv = (k, v) => `<div class="kv"><span>${k}</span><b>${v}</b></div>`;

/* ⚠️⚠️ **不要直接 `r.json()`。**
   伺服器回 500／502 時給的是 HTML 錯誤頁，`r.json()` 會丟
   「SyntaxError: Unexpected token '<'」—— 那個訊息**把真正的原因整個蓋掉了**，
   使用者只看得到「連線失敗」，看不到是幾號錯誤、也看不到錯誤內容。
   2026-08-13 實際踩到：RS 篩選失敗時完全查不出原因。
   📌 通則：**解析回應之前先看 `r.status` 與 Content-Type。** */
async function readJson(r){
  const ct = r.headers.get("content-type") || "";
  if (!ct.includes("json")) {
    const body = (await r.text()).replace(/<[^>]*>/g, " ").trim().slice(0, 160);
    throw new Error("HTTP " + r.status + (body ? "：" + body : "（伺服器回了非 JSON 內容）"));
  }
  return r.json();
}

function runProJob(url, params, button, status, done){
  button.disabled = true; status.textContent = "";
  brewOpen(t("st.send","送出篩選條件…"));
  fetch(url, {method:"POST", headers:{"Content-Type":"application/json","X-App-Token":APP_TOKEN},
    body:JSON.stringify(params)}).then(readJson).then(j => {
      if (!j.job){ brewClose(); button.disabled=false; if (retryOnStaleToken(j)) return;
        status.textContent=j.error||t("st.nojob","無法建立工作"); return; }
      const pollPro = () => fetch("/api/job/"+j.job).then(readJson).then(x => {
        if (!x.done){ brewProgress(x.progress,x.status); setTimeout(pollPro,500); return; }
        brewClose(); button.disabled=false;
        if (x.error){ status.textContent=t("st.failed","篩選失敗：")+x.error; return; }
        done(x.result);
      }).catch(e=>{ brewClose(); button.disabled=false; status.textContent=t("st.conn","連線失敗：")+e.message; });
      pollPro();
  }).catch(e=>{ brewClose(); button.disabled=false; status.textContent=t("st.conn","連線失敗：")+e.message; });
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
  NH_ORDER.filter(k=>highs[k]).forEach(k=>ho+=`<option value="${k}">${nhName(k)}（${highs[k]}）</option>`);
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
  const showStructureRs=!!($("#structureHistoryRs")&&$("#structureHistoryRs").checked);
  $("#proRsStatus").innerHTML=(LANG==="en"?`Compared ${j.scanned} stocks over ${j.period} days: `:`比較 ${j.scanned} 檔股票近 ${j.period} 日：`)+`<span class="count">${rows.length}</span> ${LANG==="en"?`scored RS ${j.threshold}+`:`檔 RS ≥ ${j.threshold}`} · ${j.as_of||"—"}`;
  if(!rows.length){$("#proRsResult").innerHTML=`<div class="concl gray">${LANG==="en"?"No stocks match.":"目前沒有股票符合這個 RS 門檻。"}</div>`;return;}
  const sectors={};rows.forEach(s=>sectors[s.sector]=(sectors[s.sector]||0)+1);
  let opts=`<option value="">${LANG==="en"?"All sectors":"全部產業"}（${rows.length}）</option>`;
  Object.keys(sectors).sort((a,b)=>sectors[b]-sectors[a]).forEach(k=>opts+=`<option value="${k}">${LANG==="en"?k:zhSectorFromRows(rows,k)}（${sectors[k]}）</option>`);
  let trs="",structureRows="",cards="";rows.forEach((s,i)=>{const name=coName(s),sector=coSector(s),gain=proPct(s.gain);
    const match=s.structure&&s.structure.available?(s.structure.matched?2:s.structure.prior_high!=null?1:0):-1;
    const near=s.structure&&s.structure.available?(s.structure.matched?1:s.structure.prior_high!=null?2:0):-1;
    trs+=`<tr data-rs-row data-rs-i="${i}" data-sector="${s.sector}"><td>${s.rank}</td><td><b>${s.symbol}</b></td><td>${name}</td><td>${sector}</td><td>${s.close}</td><td>${gain}</td><td><span class="rs-score">${s.rs}</span></td></tr>`;
    if(showStructureRs)structureRows+=`<article class="rs-structure-item" data-rs-row data-rs-i="${i}" data-structurematch="${match}" data-structurenear="${near}" data-sector="${s.sector}"><div class="rs-structure-head">`
      +`<div class="rs-structure-cell"><small>${t("th.rank","市值排名")}</small><b>#${s.rank}</b></div>`
      +`<div class="rs-structure-cell rs-structure-company"><small>${t("th.name","公司名稱")}</small><b><span>${s.symbol}</span>${name}</b></div>`
      +`<div class="rs-structure-cell rs-structure-industry"><small>${t("th.sector","產業")}</small><b>${sector}</b></div>`
      +`<div class="rs-structure-cell rs-structure-close"><small>${t("th.close","收盤")}</small><b>${s.close}</b></div>`
      +`<div class="rs-structure-cell"><small>${j.period}${LANG==="en"?"-day gain":" 日漲幅"}</small><b>${gain}</b></div>`
      +`<div class="rs-structure-cell"><small>RS</small><b><span class="rs-score">${s.rs}</span></b></div></div>${structurePanel(s)}</article>`;
    cards+=`<details class="scard" data-rs-row data-rs-i="${i}" data-structurematch="${match}" data-structurenear="${near}" data-sector="${s.sector}"><summary><span class="sc-l"><b>${s.symbol}</b> ${name}</span><span class="sc-r"><span class="rs-score">${s.rs}</span></span></summary><div class="scard-body">${proKv(t("th.rank","市值排名"),s.rank)}${proKv(t("th.sector","產業"),sector)}${proKv(t("th.close","收盤"),s.close)}${proKv(`${j.period}${LANG==="en"?"-day gain":" 日漲幅"}`,gain)}${proKv("RS",s.rs)}${showStructureRs?structurePanel(s):""}</div></details>`;
  });
  const sorting=showStructureRs?`<span class="rflabel">${LANG==="en"?"Sort":"排序"}</span><select data-rs-sort onchange="sortProRs(this.value)"><option value="default">${LANG==="en"?"Default":"預設排序"}</option><option value="structurematch_desc">${LANG==="en"?"Structure match first":"結構符合優先"}</option><option value="structurenear_desc">${LANG==="en"?"Nearly complete first":"結構接近完成優先"}</option></select>`:"";
  const filters=`<div class="resfilter"><span class="rflabel">${t("flt.sector","產業")}</span><select data-rs-sector onchange="filterProRs(this.value)">${opts}</select>${sorting}</div>`;
  const desktop=showStructureRs?`<div class="res-wide rs-structure-list">${structureRows}</div>`:`<div class="res-wide"><table><thead><tr><th>${t("th.rank","排名")}</th><th>${t("th.sym","代號")}</th><th>${t("th.name","公司")}</th><th>${t("th.sector","產業")}</th><th>${t("th.close","收盤")}</th><th>${j.period}${LANG==="en"?"-day gain":" 日漲幅"}</th><th>RS</th></tr></thead><tbody>${trs}</tbody></table></div>`;
  $("#proRsResult").innerHTML=filters+desktop+`<div class="res-cards">${cards}</div>`;
  if(showStructureRs)setupStructureCharts($("#proRsResult"));
}
function filterProRs(sector){$("#proRsResult").querySelectorAll("[data-rs-row]").forEach(el=>el.style.display=(!sector||el.dataset.sector===sector)?"":"none");}
function sortProRs(value){
  const parts=(value||"default").split("_"),key=parts[0],dir=parts[1]||"asc";
  [".rs-structure-list",".res-cards"].forEach(sel=>{const parent=$("#proRsResult "+sel);if(!parent)return;const nodes=Array.from(parent.children).filter(el=>el.hasAttribute("data-rs-i"));nodes.sort((a,b)=>{const ai=Number(a.dataset.rsI),bi=Number(b.dataset.rsI);if(key==="default")return ai-bi;const av=Number(a.dataset[key]),bv=Number(b.dataset[key]);return (dir==="desc"?bv-av:av-bv)||(ai-bi)});nodes.forEach(el=>parent.appendChild(el))});
  filterProRs($("#proRsResult [data-rs-sector]")?.value||"");
}
if($("#proHighBtn")) $("#proHighBtn").onclick=()=>{ $("#proHighResult").innerHTML=""; runProJob("/api/pro/new-high",{days:Number(val("proHighDays")||1)},$("#proHighBtn"),$("#proHighStatus"),renderProHigh); };
if($("#proRsBtn")) $("#proRsBtn").onclick=()=>{ $("#proRsResult").innerHTML=""; runProJob("/api/pro/rs",{period:Number(val("proRsPeriod")||60),threshold:Number(val("proRsThreshold")||90),structure_history:!!($("#structureHistoryRs")&&$("#structureHistoryRs").checked)},$("#proRsBtn"),$("#proRsStatus"),renderProRs); };

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

if ($("#twMarket")) $("#twMarket").onclick = async () => {
  const status = $("#statusMkt"), out = $("#mktResult");
  status.textContent = LANG === "en" ? "Loading…" : "讀取大盤與 CPI 資料中…";
  out.innerHTML = "";
  try {
    const r = await fetch("/api/market-years");
    const data = await r.json();
    if (!r.ok) throw new Error(data.error || "request failed");
    out.innerHTML = (data.years || []).map(y => {
      const cpiPeriod = y.cpi_period || "";
      const cpiNote = y.cpi_full_year ? "" : (LANG === "en"
        ? ` (through ${cpiPeriod})` : `（截至 ${parseInt(cpiPeriod.slice(5), 10)} 月）`);
      const months = (y.monthly || []).map(m =>
        `<tr><td>${twMonth(m.month-1)}</td><td>${twPct(m.return)}</td></tr>`).join("");
      return `<div class="card" style="margin-top:12px">
        <h2>${y.year}</h2>
        <div class="baro-row"><span>${LANG === "en" ? "Nasdaq Composite annual return" : "納斯達克綜合指數年度報酬"}</span><b>${twPct(y.annual_return)}</b></div>
        <div class="baro-row"><span>${LANG === "en" ? "Annual CPI" : "當年度 CPI"}${cpiNote}</span><b>${y.cpi == null ? "—" : twPct(y.cpi)}</b></div>
        <div style="overflow-x:auto;margin-top:8px"><table style="font-size:13px"><tr><th>${LANG === "en" ? "Month" : "月份"}</th><th>${LANG === "en" ? "Nasdaq return" : "大盤漲跌幅"}</th></tr>${months}</table></div>
      </div>`;
    }).join("");
    status.textContent = LANG === "en" ? "Official Nasdaq and BLS data" : "納斯達克綜合指數與 BLS 官方 CPI";
  } catch (e) {
    status.textContent = (LANG === "en" ? "Unable to load: " : "讀取失敗：") + e.message;
  }
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
    try {
      const c = await caches.open("us-push-state");
      await c.delete("/api/__us_badge");
      await c.delete("/__us_badge");        // 舊鍵（2026-08-07 前）順手清掉
    }
    catch(_){}
  }
}
clearUsPushBadge();

/* ---- 名言卡：再抽一張 ---- */
async function drawQuote(){
  const btn = $('#qmoreBtn'), box = $('#qbox');
  if (!btn || !box) return;
  /* ⚠️ 中英兩份卡都在 HTML 裡，要插進**目前顯示的那一份**，
        否則切語言之後抽出來的卡會看不到。 */
  const wrap = box.querySelector(LANG === 'en' ? '.q-en' : '.q-zh') || box;
  const seen = [...wrap.querySelectorAll('.qcard')]
    .map(c => c.getAttribute('data-no')).filter(Boolean).join(',');
  btn.disabled = true;
  const old = btn.textContent;
  btn.textContent = t('home.more.loading', '沖泡中…');
  try {
    const r = await fetch('/api/quote-more?lang=' + LANG + '&seen=' + seen,
                          {headers: {'X-App-Token': APP_TOKEN}});
    if (r.status === 403){ retryOnStaleToken(); return; }
    const j = await r.json();
    if (j.done){ btn.textContent = t('home.more.done', '今天的都喝完了 ☕'); return; }
    wrap.insertAdjacentHTML('beforeend', j.html);
    btn.textContent = old;
    btn.disabled = false;
    if (j.remain === 0){
      btn.textContent = t('home.more.done', '今天的都喝完了 ☕');
      btn.disabled = true;
    }
  } catch(e){
    btn.textContent = old;
    btn.disabled = false;
  }
}

/* ================= 均線扣抵法（/deduction）=================
   ⚠️ 與台股版同一套版面與說法（結論先行、三種結果三種說法、負斜率要另外解釋）。
      兩邊要改就一起改。 */
let dedCode = '', dedName = '', dedLoaded = false, dedStocks = [];
function dedKind(){
  const el = document.querySelector('input[name=dedKind]:checked');
  return el ? el.value : 'index';
}
function dedToggle(){
  const stock = dedKind() === 'stock';
  $('#dedPickBox').style.display = stock ? '' : 'none';
  if (!stock){ dedCode = ''; dedName = ''; $('#dedPicked').style.display = 'none'; }
}
async function dedLoadStocks(){
  if (dedLoaded) return;
  try {
    const r = await fetch('/api/stocklist', {headers: {'X-App-Token': APP_TOKEN}});
    if (!r.ok) throw new Error('stock list ' + r.status);
    dedStocks = await r.json(); dedLoaded = true;
  } catch(e){
    $('#dedSearch').placeholder = t('alert.loadFail', '股票清單載入失敗，請重新整理');
  }
}
async function dedSearch(){
  /* ⚠️ 這裡呼叫的每個函式都必須真的存在 —— 名字打錯只有在**使用者實際打字時**
        才會丟 ReferenceError，語法檢查與載入期執行都抓不到。
        台股版 2026-08-07 就是這樣讓「輸入代號沒反應」上線的。 */
  await dedLoadStocks();
  const raw = ($('#dedSearch').value || '').trim(), kw = raw.toUpperCase();
  const box = $('#dedSuggest');
  if (!raw){ box.classList.remove('show'); return; }
  const hit = dedStocks.filter(x => x.code.indexOf(kw) === 0
    || (x.name || '').toUpperCase().indexOf(kw) >= 0
    || (x.name_zh || '').indexOf(raw) >= 0).slice(0, 20);
  if (!hit.length){
    box.innerHTML = '<div class="empty">'
      + t('alert.notFound', '找不到符合的股票（僅限市值前 300 大）') + '</div>';
    box.classList.add('show'); return;
  }
  box.innerHTML = hit.map(x => {
    const nm = (LANG === 'en') ? x.name : (x.name_zh || x.name);
    return '<div onclick="dedPick(\'' + x.code + "','"
      + String(nm).replace(/'/g, '') + '\')"><b>' + x.code + '</b>' + nm + '</div>';
  }).join('');
  box.classList.add('show');
}
function dedPick(code, name){
  dedCode = code; dedName = name;
  $('#dedSearch').value = '';
  $('#dedSuggest').classList.remove('show');
  const p = $('#dedPicked');
  p.innerHTML = '<span>' + t('alert.picked', '已選擇') + '：<b>' + code + ' ' + name
    + '</b></span><span class="clr" onclick="dedClear()">'
    + t('alert.repick', '重新選擇 ✕') + '</span>';
  p.style.display = 'flex';
}
function dedClear(){
  dedCode = ''; dedName = '';
  $('#dedPicked').style.display = 'none';
  $('#dedSearch').value = '';
}
function dedDays(o, maxDays){
  /* ⚠️ 三種結果要用三種說法：追不上→「超過 N 個交易日」、已到位→「已扣抵」、其餘→天數。
        顯示 0 會讓人以為還有一天可以整理；空白看起來像壞掉。 */
  if (o.days == null) return '<span class="ded-over">' + t('ded.over', '超過 ')
    + maxDays + t('ded.sessions', ' 個交易日') + '</span>';
  if (o.days === 0) return '<b class="ded-done">' + t('ded.done', '已扣抵') + '</b>';
  return '<b>' + o.days + '</b>' + t('ded.sessions', ' 個交易日');
}
function dedCard(name, flat, trend, maxDays, target, slope){
  /* ⚠️ 閱讀順序＝結論先行：天數放最上面，「目前均線／明日扣抵 K 棒」是解釋，放後面。 */
  const dir = (flat.side === 'below')
    ? t('ded.up', '均線在價格下方，往上追')
    : t('ded.down', '均線在價格上方，往下貼近');
  const slopeCls = slope > 0 ? 'ded-pos' : (slope < 0 ? 'ded-neg-v' : '');
  const slopeTxt = (slope > 0 ? '+' : '') + slope + '%/' + t('ded.perDay', '日');
  return '<div class="card"><h2>' + name + '</h2>'
    + '<div class="ded-rows">'
    + '<div><span>' + t('ded.flat', '盤整（價格停在 ') + target.toLocaleString() + '）</span><span>'
    + dedDays(flat, maxDays) + '</span></div>'
    + '<div><span>' + t('ded.trend', '延續近 20 日斜率')
    + ' <small class="' + slopeCls + '">(' + slopeTxt + ')</small></span><span>'
    + dedDays(trend, maxDays) + '</span></div>'
    + '</div>'
    /* ⚠️⚠️ 斜率為負時「天數變少」是價格跌下去碰到均線，不是均線追上來 —— 意義相反。 */
    + (slope < 0 ? '<div class="ded-neg">' + t('ded.negNote',
        '⚠️ 近期斜率是向下的，所以「趨勢」那一列的天數變少，是因為價格跌下去碰到均線，'
        + '不是均線追上來。想估的若是多頭整理可以等多久，請看「盤整」那一列。') + '</div>' : '')
    + '<div class="ded-note">' + dir + '　·　'
    + t('ded.gap', '目前價位距離均線') + ' <b>'
    + (flat.gap_pct == null ? '—' : (flat.gap_pct > 0 ? '+' : '') + flat.gap_pct + '%') + '</b></div>'
    + '<div class="ded-grid">'
    + '<div class="ded-i"><div class="k">' + t('ded.now', '目前均線') + '</div><div class="v">'
    + flat.ma.toLocaleString() + '</div></div>'
    + '<div class="ded-i"><div class="k">' + t('ded.dv', '明日扣抵 K 棒') + '</div><div class="v">'
    + flat.deduct_next.toLocaleString() + '</div><div class="n">'
    + (flat.rising ? t('ded.rise', '低於目標價 → 均線會往上')
                   : t('ded.fall', '高於目標價 → 均線會往下')) + '</div></div>'
    + '</div></div>';
}
async function runDeduct(){
  const btn = $('#dedBtn');
  if (dedKind() === 'stock' && !dedCode){
    $('#dedStatus').textContent = t('ded.needStock', '請先選擇一檔股票');
    return;
  }
  btn.disabled = true;
  $('#dedStatus').textContent = t('ded.calc', '試算中…');
  try {
    const body = {code: dedKind() === 'stock' ? dedCode : 'COMP'};
    const pv = parseFloat($('#dedPrice').value);
    if (pv > 0) body.price = pv;
    const r = await fetch('/api/deduct', {
      method: 'POST',
      headers: {'Content-Type': 'application/json', 'X-App-Token': APP_TOKEN},
      body: JSON.stringify(body)});
    if (r.status === 403){ retryOnStaleToken(); return; }
    const j = await r.json();
    if (j.error){ $('#dedStatus').textContent = j.error; $('#dedResult').innerHTML = ''; return; }
    $('#dedStatus').textContent = '';
    const label = (LANG === 'en') ? (j.name || j.code) : (j.name_zh || j.name || j.code);
    let h = '<div class="concl blue">' + label + '　'
      + t('ded.last', '最新收盤') + ' <b>' + j.last.toLocaleString() + '</b>　'
      + t('ded.target', '目標價') + ' <b>' + j.target.toLocaleString() + '</b>'
      + (j.custom_price ? '' : t('ded.useLast', '（未填，用最新收盤）'))
      + '<div style="font-size:12.5px;font-weight:normal;color:#777;margin-top:6px">'
      + t('ded.slope', '近 ') + j.slope_lookback + t('ded.slope2', ' 日平均每日 ')
      + (j.slope_pct > 0 ? '+' : '') + j.slope_pct + '%</div></div>';
    for (const n of (j.mas || [50, 100, 150])){
      const key = String(n), f = j.flat[key], tr = j.trend[key];
      if (!f || f.ma == null){
        h += '<div class="card"><h2>' + n + 'MA</h2><div style="color:#999">'
          + t('ded.noData', '歷史收盤不足，算不出這條均線') + '</div></div>';
        continue;
      }
      h += dedCard(n + t('ded.maUnit', ' 日線'), f, tr, j.max_days, j.target, j.slope_pct);
    }
    h += '<div class="ded-warn">' + t('ded.warn',
      '⚠️ 這是算術外推，不是預測。它假設未來每天都照同一個幅度走，真實市場不會這樣。天數請當成「如果照這個節奏」的粗估，不是保證還有幾天。') + '</div>';
    $('#dedResult').innerHTML = h;
  } catch(e){
    $('#dedStatus').textContent = t('ded.fail', '試算失敗，請稍後再試');
  } finally { btn.disabled = false; }
}
if ($('#dedBtn')){
  $('#dedBtn').onclick = runDeduct;
  $('#dedSearch').oninput = dedSearch;
  document.querySelectorAll('input[name=dedKind]').forEach(el => { el.onchange = dedToggle; });
  document.addEventListener('click', e => {
    const p = $('#dedSearch') && $('#dedSearch').parentElement;
    if (p && !p.contains(e.target) && $('#dedSuggest')) $('#dedSuggest').classList.remove('show');
  });
}

/* ================= 風控管理（/risk）=================
   ⚠️ 進場價、追蹤最高價與停損只存在 localStorage（us_risk_positions），
      跟到價提醒的 us_push_cid 一樣不上傳。沒有帳號系統是刻意的取捨。 */
const RK_KEY = "us_risk_positions";
let rkList = [], rkStocks = [], rkLoaded = false, rkSugIdx = -1, rkLast = null;

function rkLoad(){
  try { return JSON.parse(localStorage.getItem(RK_KEY) || "{}") || {}; }
  catch(_){ return {}; }
}
function rkSave(o){ try { localStorage.setItem(RK_KEY, JSON.stringify(o)); } catch(_){} }
function rkMult(){ return parseFloat((document.querySelector("input[name=rkMult]:checked") || {}).value || "2"); }

async function rkLoadStocks(){
  if (rkLoaded) return;
  try {
    const r = await fetch("/api/stocklist", {headers: {"X-App-Token": APP_TOKEN}});
    if (!r.ok) throw new Error("stock list " + r.status);
    rkStocks = await r.json(); rkLoaded = true;
  } catch(e){
    $("#rkInput").placeholder = t("alert.loadFail", "股票清單載入失敗，請重新整理");
  }
}
async function rkSearch(){
  await rkLoadStocks();
  const raw = ($("#rkInput").value || "").trim(), kw = raw.toUpperCase();
  const box = $("#rkSuggest");
  if (!raw){ box.classList.remove("show"); return; }
  const hit = rkStocks.filter(s => s.code.indexOf(kw) === 0
    || (s.name || "").toUpperCase().indexOf(kw) >= 0
    || (s.name_zh || "").indexOf(raw) >= 0).slice(0, 20);
  rkSugIdx = -1;
  if (!hit.length){
    box.innerHTML = '<div class="empty">'
      + t("alert.notFound", "找不到符合的股票（僅限市值前 300 大）") + "</div>";
    box.classList.add("show"); return;
  }
  box.innerHTML = hit.map(s => {
    const nm = (LANG === "en") ? s.name : (s.name_zh || s.name);
    return '<div onclick="rkAdd(\'' + s.code + '\')"><b>' + s.code + "</b>" + nm + "</div>";
  }).join("");
  box.classList.add("show");
}
function rkAdd(code){
  $("#rkInput").value = "";
  $("#rkSuggest").classList.remove("show");
  if (rkList.indexOf(code) >= 0) return;
  if (rkList.length >= 3){
    $("#rkStatus").textContent = t("risk.max", "最多同時看 3 檔，請先移除一檔");
    return;
  }
  rkList.push(code); rkChips(); $("#rkStatus").textContent = "";
}
function rkDel(code){
  rkList = rkList.filter(x => x !== code);
  rkChips();
  if (rkLast) rkRender(rkLast);
}
function rkChips(){
  $("#rkChips").innerHTML = rkList.map(c =>
    '<span class="chip">' + c + '<i onclick="rkDel(\'' + c + '\')">✕</i></span>').join("");
}

/* ⚠️⚠️ 移動停損：**只上移、不下調**。
   前次停損當下限，避免 ATR 變大時停損反而往下跑（那等於自己放寬認錯的標準）。
   ⚠️ 但**使用者手動改倍數時要重算**，不受前次下限限制 ——
      下限的用意是擋住「指標波動造成的放寬」，不是把使用者的決定鎖死。 */
function rkStops(sym, price, atr, mult){
  const all = rkLoad(), p = all[sym] || {};
  const entry = parseFloat(p.entry || "");
  if (!(entry > 0) || !(atr > 0)) return null;
  const peak = Math.max(parseFloat(p.peak || 0) || 0, price || 0, entry);
  const initial = entry - mult * atr;
  let trail = peak - mult * atr;
  const sameMult = String(p.mult || "") === String(mult);
  if (sameMult && p.stop != null) trail = Math.max(trail, parseFloat(p.stop));
  if (trail < initial) trail = initial;
  all[sym] = {entry: entry, peak: peak, stop: trail, mult: mult};
  rkSave(all);
  return {entry: entry, peak: peak, initial: initial, trail: trail};
}
function rkSetEntry(sym, v){
  const all = rkLoad(), p = all[sym] || {};
  const n = parseFloat(v);
  if (!(n > 0)){ delete all[sym]; rkSave(all); if (rkLast) rkRender(rkLast); return; }
  /* 改進場價等於重新開始一個部位：追蹤最高價與停損都要歸零重算。 */
  all[sym] = {entry: n, peak: n, stop: null, mult: null};
  rkSave(all); if (rkLast) rkRender(rkLast);
}

function rkFmt(v, d){ return (v == null) ? "—" : Number(v).toFixed(d == null ? 2 : d); }
function rkRender(data){
  rkLast = data;
  const mult = rkMult();
  const rows = (data.rows || []).filter(r => rkList.indexOf(r.symbol) >= 0);
  if (!rows.length){ $("#rkResult").innerHTML = ""; return; }
  $("#rkResult").innerHTML = rows.map(r => {
    const nm = (LANG === "en") ? r.name : (r.name_zh || r.name);
    const s = rkStops(r.symbol, r.close, r.atr, mult);
    let stopHtml = '<div class="rk-hint">'
      + t("risk.needEntry", "填入進場價後，這裡會算出初始停損與移動停損") + "</div>";
    if (s){
      const dist = (r.close && s.trail) ? (r.close - s.trail) / r.close * 100 : null;
      const lamp = (dist == null) ? "" : (dist < 0 ? "🔴" : (dist <= 5 ? "🟡" : "🟢"));
      stopHtml = '<div class="rk-stops">'
        + '<div><span>' + t("risk.initStop", "初始停損") + "</span><b>"
        + rkFmt(s.initial) + "</b></div>"
        + '<div><span>' + t("risk.trailStop", "移動停損") + "</span><b>"
        + rkFmt(s.trail) + "</b></div>"
        + '<div><span>' + t("risk.peak", "設定後最高") + "</span><b>"
        + rkFmt(s.peak) + "</b></div>"
        + '<div><span>' + t("risk.dist", "距離停損") + "</span><b>" + lamp + " "
        + (dist == null ? "—" : (dist.toFixed(1) + "%")) + "</b></div></div>";
    }
    return '<div class="card rk-card">'
      + '<div class="rk-h"><b>' + r.symbol + "</b><span>" + nm + "</span>"
      + '<i onclick="rkDel(\'' + r.symbol + '\')">✕</i></div>'
      + '<div class="rk-sub">' + t("th.last", "收盤") + " " + rkFmt(r.close)
      + (r.as_of ? ("　" + r.as_of) : "") + "</div>"
      + '<div class="rk-grid">'
      + '<div class="rk-i"><div class="k">ATR（' + (data.atr_period || 14) + '）</div><div class="v">'
      + rkFmt(r.atr) + (r.atr_pct ? ('　<small>' + r.atr_pct + "%</small>") : "")
      + '</div><div class="n">' + t("risk.nAtr", "每日典型波動，停損距離的單位") + "</div></div>"
      + '<div class="rk-i"><div class="k">' + t("risk.kVol", "半年年化波動率") + '</div><div class="v">'
      + (r.vol == null ? "—" : (r.vol + "%"))
      + '</div><div class="n">' + t("risk.nVol", "整體顛簸程度，用來決定部位大小") + "</div></div>"
      + '<div class="rk-i"><div class="k">' + t("risk.kAlign", "均線趨勢") + '</div><div class="v">'
      + alignName(r.align)
      + '</div><div class="n">' + t("risk.nAlign", "趨勢還在不在") + "</div></div>"
      + '<div class="rk-i"><div class="k">Beta</div><div class="v">' + rkFmt(r.beta)
      + '</div><div class="n">' + t("risk.nBeta", "對納斯達克綜合指數的連動；>1 比大盤敏感") + "</div></div>"
      + "</div>"
      + '<div class="rk-entry"><span>' + t("risk.entry", "進場價") + "</span>"
      + '<input type="number" step="0.01" value="' + ((rkLoad()[r.symbol] || {}).entry || "")
      + '" onchange="rkSetEntry(\'' + r.symbol + '\', this.value)"></div>'
      + stopHtml + "</div>";
  }).join("");
}

async function runRisk(){
  if (!rkList.length){
    $("#rkStatus").textContent = t("risk.none", "請先選擇至少一檔股票");
    return;
  }
  const btn = $("#rkBtn");
  btn.disabled = true;
  $("#rkStatus").textContent = t("risk.calc", "計算中…（第一次會抓資料，約十幾秒）");
  try {
    const r = await fetch("/api/risk", {
      method: "POST",
      headers: {"Content-Type": "application/json", "X-App-Token": APP_TOKEN},
      body: JSON.stringify({symbols: rkList})
    });
    if (r.status === 403){ retryOnStaleToken(); return; }
    const j = await r.json();
    if (j.error){ $("#rkStatus").textContent = j.error; return; }
    $("#rkStatus").textContent = "";
    rkRender(j);
  } catch(e){
    $("#rkStatus").textContent = t("risk.fail", "計算失敗，請稍後再試");
  } finally { btn.disabled = false; }
}

if ($("#rkBtn")){
  $("#rkBtn").onclick = runRisk;
  $("#rkInput").oninput = rkSearch;
  document.querySelectorAll("input[name=rkMult]").forEach(el => {
    el.onchange = () => { if (rkLast) rkRender(rkLast); };
  });
}

/* ================= 我的自選股：同期比較（/comparison）================= */
const CMP_KEY = "us_same_period_v1";
let cmpStocks = [], cmpA = null, cmpPeers = [];
function cmpStock(code){ return cmpStocks.find(s => s.code === code); }
function cmpName(s){ return !s ? "" : (LANG === "en" ? s.name : (s.name_zh || s.name)); }
function cmpEsc(v){ const d=document.createElement("div"); d.textContent=String(v||""); return d.innerHTML; }
function cmpSave(){
  if (!$("#cmpDate")) return;
  localStorage.setItem(CMP_KEY,JSON.stringify({a:cmpA?cmpA.code:"",peers:cmpPeers,
    date:$("#cmpDate").value,price:$("#cmpPrice").value,shares:$("#cmpShares").value}));
}
function cmpPrincipal(){
  const price=Number($("#cmpPrice")&&$("#cmpPrice").value), shares=Number($("#cmpShares")&&$("#cmpShares").value);
  const value=(price>0&&shares>0)?price*shares:0;
  if ($("#cmpPrincipal")) $("#cmpPrincipal").value=value?"$"+value.toLocaleString(undefined,{maximumFractionDigits:2}):"—";
  return value;
}
function cmpRenderPicks(){
  const aBox=$("#cmpAPicked");
  if (aBox){
    if (cmpA){ aBox.innerHTML="<span>"+t("alert.picked","已選擇")+"：<b>"+cmpEsc(cmpA.code+" "+cmpName(cmpA))
      +"</b></span><span class=\"clr\" onclick=\"cmpClearA()\">"+t("alert.repick","重新選擇 ✕")+"</span>"; aBox.style.display="flex"; }
    else { aBox.style.display="none"; aBox.innerHTML=""; }
  }
  const box=$("#cmpPeers");
  if (box) box.innerHTML=cmpPeers.map((code,i)=>{ const s=cmpStock(code)||{code:code,name:""};
    return "<span class=\"cmp-chip\"><b>"+"BCD"[i]+"・"+cmpEsc(s.code)+"</b>"+cmpEsc(cmpName(s))
      +"<span class=\"x\" onclick=\"cmpRemovePeer('"+s.code+"')\">✕</span></span>"; }).join("");
}
function cmpClearA(){ cmpA=null; cmpSave(); cmpRenderPicks(); }
function cmpRemovePeer(code){ cmpPeers=cmpPeers.filter(x=>x!==code); cmpSave(); cmpRenderPicks(); }
function cmpChoose(code,kind){
  const s=cmpStock(code); if (!s) return;
  if (kind==="a"){
    cmpA=s; cmpPeers=cmpPeers.filter(x=>x!==code); $("#cmpASearch").value=""; $("#cmpASuggest").classList.remove("show");
  } else {
    if ((cmpA&&cmpA.code===code)||cmpPeers.includes(code)){ alert(t("cmp.duplicate","這檔已經選過了")); return; }
    if (cmpPeers.length>=3){ alert(t("cmp.max","最多比較 3 檔")); return; }
    cmpPeers.push(code); $("#cmpPeerSearch").value=""; $("#cmpPeerSuggest").classList.remove("show");
  }
  cmpSave(); cmpRenderPicks();
}
function cmpSuggest(kind){
  const inp=$(kind==="a"?"#cmpASearch":"#cmpPeerSearch"), box=$(kind==="a"?"#cmpASuggest":"#cmpPeerSuggest");
  if (!inp||!box) return;
  const kw=inp.value.trim().toLowerCase(); if (!kw){ box.classList.remove("show"); return; }
  const hit=cmpStocks.filter(s=>s.code.toLowerCase().indexOf(kw)===0 || s.name.toLowerCase().indexOf(kw)>=0
    || (s.name_zh||"").toLowerCase().indexOf(kw)>=0).slice(0,30);
  box.innerHTML=hit.length?hit.map(s=>"<div onclick=\"cmpChoose('"+s.code+"','"+kind+"')\"><b>"
    +cmpEsc(s.code)+"</b>"+cmpEsc(cmpName(s))+"</div>").join("")
    :"<div class=\"empty\">"+t("cmp.nohit","找不到符合的股票（僅限市值前300大）")+"</div>";
  box.classList.add("show");
}
async function cmpInit(){
  if (!$("#cmpDate")) return;
  $("#cmpDate").max=new Date().toISOString().slice(0,10);
  if (!cmpStocks.length){
    try {
      const r=await fetch("/api/stocklist",{headers:{"X-App-Token":APP_TOKEN}});
      if (r.status===403){ retryOnStaleToken(); return; }
      cmpStocks=await r.json();
    } catch(e){ cmpStocks=[]; }
  }
  try {
    const x=JSON.parse(localStorage.getItem(CMP_KEY)||"{}"); cmpA=cmpStock(x.a)||null;
    cmpPeers=(x.peers||[]).filter(c=>cmpStock(c)&&(!cmpA||c!==cmpA.code)).slice(0,3);
    $("#cmpDate").value=x.date||""; $("#cmpPrice").value=x.price||""; $("#cmpShares").value=x.shares||"";
  } catch(e){ cmpA=null; cmpPeers=[]; }
  cmpPrincipal(); cmpRenderPicks();
}
function cmpMoney(v){ return Number(v).toLocaleString(LANG==="en"?"en-US":"zh-TW",{minimumFractionDigits:0,maximumFractionDigits:2}); }
function cmpRenderResult(j){
  const best=Math.max.apply(null,(j.rows||[]).map(r=>r.return_pct));
  let head="<div class=\"concl blue\">"+t("cmp.range","同期區間")+"：<b>"+j.entry_date+" → "+j.as_of+"</b>"
    +"　·　"+t("cmp.principal","實際投入本金")+" <b>$"+cmpMoney(j.principal)+"</b></div>";
  if (j.entry_date!==j.requested_date) head+="<div class=\"status\">"+t("cmp.shift","指定日期不是共同交易日，比較改從")+" "+j.entry_date+"</div>";
  const cards=(j.rows||[]).map(r=>{
    const up=r.return_pct>=0,isBest=Math.abs(r.return_pct-best)<0.000001;
    const role=r.role==="A"?t("cmp.actualTag","實際買入 A"):t("cmp.hypTag","當初沒買")+" "+r.role;
    const name=LANG==="en"?r.name:(r.name_zh||r.name);
    const diff=r.role==="A"?"—":((r.difference_vs_a>=0?"+":"")+"$"+cmpMoney(r.difference_vs_a));
    const qty=(r.role==="A"&&Math.abs(r.split_factor-1)>0.000001)
      ? cmpMoney(r.original_shares)+" → "+cmpMoney(r.shares)+"（"+t("cmp.split","拆股調整")+"）"
      : cmpMoney(r.shares);
    return "<div class=\"cmp-card "+(r.role==="A"?"actual ":"")+(isBest?"best":"")+"\"><div class=\"cmp-head\">"
      +"<span class=\"cmp-role\">"+role+"</span><div style=\"min-width:0\"><div class=\"cmp-code\">"+cmpEsc(r.code)
      +(isBest?"　<small>🏆 "+t("cmp.best","同期最佳")+"</small>":"")+"</div><div class=\"cmp-name\">"+cmpEsc(name)+"</div></div></div>"
      +"<div class=\"cmp-ret "+(up?"up":"down")+"\">"+(up?"+":"")+r.return_pct.toFixed(2)+"%</div>"
      +"<div class=\"cmp-kv\"><span>"+t("cmp.buyPrice","起始價格")+"</span><span>$"+cmpMoney(r.entry_price)+"</span>"
      +"<span>"+t("cmp.qty","可買股數")+"</span><span>"+qty+"</span>"
      +"<span>"+t("cmp.cash","剩餘現金")+"</span><span>$"+cmpMoney(r.cash)+"</span>"
      +"<span>"+t("cmp.last","最新收盤")+"</span><span>$"+cmpMoney(r.last_price)+"（"+r.last_date+"）</span>"
      +"<span>"+t("cmp.value","目前總值")+"</span><span>$"+cmpMoney(r.current_value)+"</span>"
      +"<span>"+t("cmp.vsA","相較 A 多／少")+"</span><span>"+diff+"</span></div></div>";
  }).join("");
  $("#cmpResult").innerHTML=head+"<div class=\"cmp-grid\">"+cards+"</div><div class=\"rk-hint\">⚠️ "
    +t("cmp.note","僅比較價格報酬：未計手續費、稅與現金股利；B/C/D 以整股買入，剩餘本金保留現金。")+"</div>";
}
async function cmpRun(){
  if (!cmpA){ $("#cmpStatus").textContent=t("cmp.needA","請先選擇 A 股票"); return; }
  if (!cmpPeers.length){ $("#cmpStatus").textContent=t("cmp.needPeer","至少選擇一檔比較股票"); return; }
  if (!$("#cmpDate").value){ $("#cmpStatus").textContent=t("cmp.needDate","請輸入買入日期"); return; }
  const price=Number($("#cmpPrice").value),shares=Number($("#cmpShares").value);
  if (!(price>0)||!(shares>0)){ $("#cmpStatus").textContent=t("cmp.needTrade","請輸入正確的 A 買入價與股數"); return; }
  cmpSave(); $("#cmpBtn").disabled=true; $("#cmpStatus").textContent=t("cmp.loading","正在計算同期報酬…"); $("#cmpResult").innerHTML="";
  try {
    const r=await fetch("/api/comparison",{method:"POST",headers:{"Content-Type":"application/json","X-App-Token":APP_TOKEN},
      body:JSON.stringify({anchor:cmpA.code,peers:cmpPeers,date:$("#cmpDate").value,buy_price:price,shares:shares,lang:LANG})});
    if (r.status===403){ retryOnStaleToken(); return; }
    const j=await r.json(); if (!r.ok||j.error){ $("#cmpStatus").textContent=j.error||t("cmp.fail","比較失敗，請稍後再試"); return; }
    $("#cmpStatus").textContent=""; cmpRenderResult(j);
  } catch(e){ $("#cmpStatus").textContent=t("cmp.fail","比較失敗，請稍後再試"); }
  finally { $("#cmpBtn").disabled=false; }
}
if ($("#cmpASearch")) $("#cmpASearch").addEventListener("input",()=>cmpSuggest("a"));
if ($("#cmpPeerSearch")) $("#cmpPeerSearch").addEventListener("input",()=>cmpSuggest("peer"));
["cmpDate","cmpPrice","cmpShares"].forEach(id=>{if($("#"+id))$("#"+id).addEventListener("input",()=>{cmpPrincipal();cmpSave();});});
if ($("#cmpBtn")) $("#cmpBtn").onclick=cmpRun;
document.addEventListener("click",e=>{
  [["cmpASearch","cmpASuggest"],["cmpPeerSearch","cmpPeerSuggest"]].forEach(x=>{
    const inp=$("#"+x[0]),box=$("#"+x[1]); if(inp&&box&&!inp.parentElement.contains(e.target))box.classList.remove("show");
  });
});

/* ---- 美國利率與購買力 ---- */
const MACRO_EN = {
  us2y:"US 2Y Treasury", us10y:"US 10Y Treasury", us30y:"US 30Y Treasury",
  jp2y:"Japan 2Y Government Bond", jp10y:"Japan 10Y Government Bond", jp30y:"Japan 30Y Government Bond",
  "br.snapTitle":"Today's Market Breadth",
  "br.snapIntro":"An index can be held up by a few heavyweights. This shows how many individual stocks are actually in trend — when the index and breadth diverge, breadth usually tells the truth first.",
  "br.above":"Above",
  "br.nh":"60-day new highs",
  "br.nodata":"insufficient data",
  "br.snapAsOf":"As of",
  "br.snapNote":"Denominators count only stocks with enough trading days for that average, so the three lines differ (newly listed names cannot fill 200 days). New highs use a 2% tolerance. Moving-average counts show how many remain in trend; new-high counts show how many are breaking out — the latter usually falls first, because it needs fresh buying.",
  cpi_ytd:"YTD Cumulative CPI", cpi_5y:"5-Year Cumulative CPI",
  cpi_10y:"10-Year Cumulative CPI"
};
function macroTile(it){
  const name = (LANG === "en" && MACRO_EN[it.key]) ? MACRO_EN[it.key] : it.label;
  const unit = it.unit ? `<small>${it.unit}</small>` : "";
  let sub = it.date || "";
  if (it.base_date){
    sub += (LANG === "en" ? " · base " : " · 基期 ") + it.base_date;
  } else if (it.chg !== undefined){
    const arrow = it.chg > 0 ? "▲ +" : (it.chg < 0 ? "▼ " : "・");
    sub += ` · ${arrow}${Math.abs(it.chg)}`;
  }
  return `<div class="mstat"><div class="ml">${name}</div><div class="mv">${it.value}${unit}</div><div class="msub">${sub}</div></div>`;
}
function yieldChart(rows,market="us"){
  if (!rows || rows.length < 2) return "";
  const W=900,H=330,L=52,R=18,T=18,B=38,keys=[market+"2y",market+"10y",market+"30y"];
  const colors={[keys[0]]:"#c87533",[keys[1]]:"#3f718c",[keys[2]]:"#7a5b9e"};
  const vals=rows.flatMap(r=>keys.map(k=>Number(r[k])).filter(Number.isFinite));
  let min=Math.floor((Math.min(...vals)-.15)*2)/2,max=Math.ceil((Math.max(...vals)+.15)*2)/2;if(max<=min)max=min+1;
  const x=i=>L+i*(W-L-R)/(rows.length-1),y=v=>T+(max-v)*(H-T-B)/(max-min);
  let grid="";for(let i=0;i<=4;i++){const v=min+(max-min)*i/4,yy=y(v);grid+=`<line x1="${L}" y1="${yy}" x2="${W-R}" y2="${yy}" stroke="var(--grounds)"/><text x="${L-8}" y="${yy+4}" text-anchor="end" fill="var(--mocha)" font-size="11">${v.toFixed(1)}%</text>`;}
  const paths=keys.map(k=>{let d="";rows.forEach((r,i)=>{if(Number.isFinite(Number(r[k])))d+=(d?"L":"M")+x(i).toFixed(1)+" "+y(Number(r[k])).toFixed(1)+" ";});return `<path d="${d}" fill="none" stroke="${colors[k]}" stroke-width="2.2"/>`;}).join("");
  const ticks=[0,Math.floor((rows.length-1)/2),rows.length-1].map(i=>`<text x="${x(i)}" y="${H-10}" text-anchor="middle" fill="var(--mocha)" font-size="11">${rows[i].date.slice(0,7)}</text>`).join("");
  const title=market==="jp"?(LANG==="en"?"Japan government bond yields — 3 years":"日圓利率｜日債 2Y／10Y／30Y 三年走勢"):(LANG==="en"?"US Treasury yields — 3 years":"美債 2Y／10Y／30Y 三年走勢");
  return `<div class="card"><h2>${title}</h2><div class="yield-legend"><span><i style="background:${colors[keys[0]]}"></i>2Y</span><span><i style="background:${colors[keys[1]]}"></i>10Y</span><span><i style="background:${colors[keys[2]]}"></i>30Y</span></div><svg class="yield-chart" viewBox="0 0 ${W} ${H}" role="img" aria-label="${market==='jp'?'Japan government bond':'US Treasury'} yield chart" data-market="${market}" data-min="${min}" data-max="${max}">${grid}${paths}${ticks}<g class="yield-hover" visibility="hidden" pointer-events="none"><line class="yield-cross" y1="${T}" y2="${H-B}" stroke="var(--espresso)" stroke-width="1" stroke-dasharray="4 3" opacity=".55"/>${keys.map(k=>`<circle data-key="${k}" r="5" fill="${colors[k]}" stroke="white" stroke-width="2"/>`).join("")}<g class="yield-tip"><rect width="240" height="136" rx="12" fill="var(--espresso)" stroke="var(--grounds)" stroke-width="2" opacity=".96"/><text x="16" y="29" fill="white" font-size="20" font-weight="700"></text><text data-key="${keys[0]}" x="16" y="60" fill="white" font-size="20"></text><text data-key="${keys[1]}" x="16" y="90" fill="white" font-size="20"></text><text data-key="${keys[2]}" x="16" y="120" fill="white" font-size="20"></text></g></g><rect class="yield-hit" x="${L}" y="${T}" width="${W-L-R}" height="${H-T-B}" fill="transparent" style="cursor:crosshair;touch-action:none"/></svg><div class="status">${LANG==="en"?"Hover or drag to inspect daily yields.":"將滑鼠移到圖上，或用手指拖曳，可查看每日利率。"}</div></div>`;
}
function setupYieldHover(svg,rows){
  if(!svg||!rows||rows.length<2)return;
  const W=900,H=330,L=52,R=18,T=18,B=38,min=Number(svg.dataset.min),max=Number(svg.dataset.max);
  const market=svg.dataset.market||"us",keys=[market+"2y",market+"10y",market+"30y"];
  const hover=svg.querySelector(".yield-hover"),cross=svg.querySelector(".yield-cross"),tip=svg.querySelector(".yield-tip");
  const x=i=>L+i*(W-L-R)/(rows.length-1),y=v=>T+(max-v)*(H-T-B)/(max-min);
  function show(ev){
    const rect=svg.getBoundingClientRect(),px=(ev.clientX-rect.left)*W/rect.width;
    const i=Math.max(0,Math.min(rows.length-1,Math.round((px-L)*(rows.length-1)/(W-L-R)))),row=rows[i],xx=x(i);
    hover.setAttribute("visibility","visible");cross.setAttribute("x1",xx);cross.setAttribute("x2",xx);
    keys.forEach(k=>{const c=hover.querySelector(`circle[data-key="${k}"]`);c.setAttribute("cx",xx);c.setAttribute("cy",y(Number(row[k])));hover.querySelector(`text[data-key="${k}"]`).textContent=`${k.slice(2).toUpperCase()}: ${Number(row[k]).toFixed(2)}%`;});
    hover.querySelector("text:not([data-key])").textContent=row.date;
    tip.setAttribute("transform",`translate(${xx>W-265?xx-250:xx+10} ${T+8})`);
  }
  svg.addEventListener("pointermove",show);svg.addEventListener("pointerdown",show);
  svg.addEventListener("pointerleave",()=>hover.setAttribute("visibility","hidden"));
}
async function loadMacro(){
  const box = $("#macroBox");
  if (!box) return;
  box.innerHTML = `<div class="status">${t("pmac.loading", "讀取美國利率與 CPI…")}</div>`;
  try {
    const data = await (await fetch("/api/macro")).json();
    const byKey = {};
    (data.items || []).forEach(it => byKey[it.key] = it);
    const groups = [
      [t("pmac.bonds", "美國公債殖利率"), ["us2y", "us10y", "us30y"]],
      [LANG==="en"?"Japan government bonds":"日本公債（日圓利率）", ["jp2y", "jp10y", "jp30y"]],
      [t("pmac.cpi", "累積物價漲幅"), ["cpi_ytd", "cpi_5y", "cpi_10y"]]
    ];
    let html = "";
    groups.forEach(group => {
      const tiles = group[1].filter(k => byKey[k]).map(k => macroTile(byKey[k])).join("");
      if (tiles) html += `<div class="card"><h2>${group[0]}</h2><div class="macro-grid">${tiles}</div></div>`;
    });
    html += yieldChart(data.yield_history);
    html += yieldChart(data.jp_yield_history,"jp");
    if (data.yield_conclusions && data.yield_conclusions.length){
      html += `<div class="card"><h2>${LANG==="en"?"Yield curve reading":"殖利率判讀卡"}</h2><div class="reading-card"><div class="reading-row"><b>${LANG==="en"?"Data":"數據"}</b><span>${LANG==="en"?`Checked ${data.updated||"—"}; latest available closing yields.`:`資料檢查日 ${data.updated||"—"}；顯示最近可用收盤殖利率。`}</span></div><div class="reading-row"><b>${LANG==="en"?"Reading":"解讀"}</b><ul class="yield-findings">${data.yield_conclusions.map(c=>`<li class="${c.level||""}">${c.text}</li>`).join("")}</ul></div><div class="reading-row"><b>${LANG==="en"?"Limit":"限制"}</b><span>${LANG==="en"?"Rule-based review of past reversals, percentiles and curve spreads; it cannot predict the next rate move.":"依過去反轉、百分位與曲線利差整理，不能據此預測下一次利率方向。"}</span></div></div></div>`;
    }
    if (!html) html = `<div class="status">${t("pmac.none", "暫時無法取得資料，請稍後再試。")}</div>`;
    else html += `<div class="status">${LANG === "en" ? "Checked" : "資料檢查日"}：${data.updated || "—"}</div>`;
    box.innerHTML = html;
    setupYieldHover(box.querySelector('.yield-chart[data-market="us"]'),data.yield_history);
    setupYieldHover(box.querySelector('.yield-chart[data-market="jp"]'),data.jp_yield_history);
  } catch(e){
    box.innerHTML = `<div class="status">${t("pmac.none", "暫時無法取得資料，請稍後再試。")}</div>`;
  }
}

/* ---- 全站資料品質提示：外觀切換不改變這個固定資訊層級。 ---- */
let DATA_HEALTH=null;
const PAGE_DATA_SOURCES={home:['market_returns','market_breadth','nasdaq_index','fed_policy','treasury_actions'],pind:['market_breadth'],pmac:['us_yields','jp_yields'],p1:['market_returns'],p3:['market_returns'],pgrow:['market_returns'],p11:['nasdaq_index'],p7:['nasdaq_index'],p8:['market_returns'],p12:['market_returns'],p10:['nasdaq_index'],p4:['market_returns'],p5:['market_returns'],p9:['market_returns']};
function qualityChip(item){const cls={ok:'dq-ok',pending:'dq-pending',warn:'dq-warn',danger:'dq-danger'}[item.severity]||'dq-danger';const zh=`${item.label_zh||'資料'}：${item.status_zh||'更新失敗，沿用舊資料'}`;const en=`${item.label_en||'Data'}: ${item.status_en||'Update failed; using older data'}`;return `<span class="data-quality-chip ${cls}" title="${item.actual||''}"><span class="q-zh"${LANG==='zh'?'':' style="display:none"'}>${zh}</span><span class="q-en"${LANG==='en'?'':' style="display:none"'}>${en}</span></span>`}
function renderDataQuality(){if(!DATA_HEALTH)return;Object.entries(PAGE_DATA_SOURCES).forEach(([pid,keys])=>{const page=document.getElementById(pid);if(!page)return;let strip=page.querySelector(':scope > .data-quality-strip');if(!strip){strip=document.createElement('div');strip.className='data-quality-strip';const title=page.querySelector(':scope > .ptitle');title?title.insertAdjacentElement('afterend',strip):page.prepend(strip)}strip.innerHTML=keys.map(k=>qualityChip(DATA_HEALTH.items[k]||{})).join('')})}
async function loadDataQuality(){try{DATA_HEALTH=await readJson(await fetch('/api/data-health'));renderDataQuality()}catch(e){DATA_HEALTH={items:{market_returns:{severity:'danger',status_zh:'更新失敗，沿用舊資料',status_en:'Update failed; using older data',label_zh:'資料',label_en:'Data'}}};Object.keys(PAGE_DATA_SOURCES).forEach(k=>PAGE_DATA_SOURCES[k]=['market_returns']);renderDataQuality()}}
loadDataQuality();

/* ---- 產業分析 ---- */
let IND_DATA=null,IND_SORT="median20";
const indPct=v=>`<span style="color:${Number(v)>=0?'#278153':'#c84335'}">${Number(v)>=0?'+':''}${Number(v).toFixed(2)}%</span>`;
const indDelta=v=>v==null?'—':`${Number(v)>=0?'▲':'▼'} ${Math.abs(Number(v)).toFixed(2)} ${LANG==='en'?'pp':'個百分點'}`;
function staleNote(date){const d=new Date(String(date).slice(0,10)+'T12:00:00'),today=new Date();if(!Number.isFinite(d.getTime()))return LANG==="en"?' · ⚠️ Data date unavailable':' · ⚠️ 缺少資料日期';d.setHours(12,0,0,0);today.setHours(12,0,0,0);let n=0;while(d<today){d.setDate(d.getDate()+1);if(d.getDay()>0&&d.getDay()<6)n++;}return n>1?(LANG==="en"?` · ⚠️ ${n} weekdays behind; updating`:` · ⚠️ 落後 ${n} 個平日，正在更新`):'';}
function indName(row){return LANG==="zh"?(row.name_zh||row.name):row.name}
function renderIndustries(){
  if(!IND_DATA||!$("#indRank"))return;
  const rows=[...(IND_DATA.industries||[])].sort((a,b)=>Number(b[IND_SORT])-Number(a[IND_SORT]));
  const labels=LANG==="en"
    ?{median20:"20D median",median60:"60D median",win20_pct:"20D advancers",above50_pct:"Above 50MA",newhigh_pct:"60D highs"}
    :{median20:"20日中位",median60:"60日中位",win20_pct:"20日上漲",above50_pct:"站上50日線",newhigh_pct:"創60日新高"};
  $("#indStatus").textContent=LANG==="en"
    ?`As of ${IND_DATA.as_of} · ${IND_DATA.sample} calculable stocks in the top ${IND_DATA.universe}${staleNote(IND_DATA.as_of)}`
    :`資料截至 ${IND_DATA.as_of} · 前 ${IND_DATA.universe} 大中 ${IND_DATA.sample} 檔可計算${staleNote(IND_DATA.as_of)}`;
  $("#indRank").innerHTML=rows.map((r,i)=>{const concentration=Number(r.leader_concentration_pct||0);const concentrated=concentration>=60;const allStocks=(r.stocks||r.leaders||[]);const reading=r.quadrant==="recovery"?(LANG==="en"?"The 60-day trend is still weak, but the latest 20 days have turned positive: an early recovery, not a confirmed uptrend.":"60 日仍弱、最近 20 日已轉正，屬於復甦初期，還不是已確認的上升趨勢。"):r.win20_pct>=60&&!concentrated?(LANG==="en"?"Strength is supported by broad participation rather than only a few leaders.":"上漲家數過半且領先股不過度集中，產業整體轉強的可信度較高。"):concentrated?(LANG==="en"?"Most positive performance is concentrated in the top three stocks; the sector has not strengthened broadly.":"正報酬多集中在前三檔，產業尚未全面轉強。"):LANG==="en"?"Read returns together with participation; a positive median alone is not enough.":"報酬需搭配上漲家數判讀；只有中位數為正，仍不足以代表全面轉強。";return `<details class="ind-row"><summary>
    <span class="ind-name">${i+1}. ${cmpEsc(indName(r))}<small style="display:block;color:var(--mocha);font-weight:400">${r.count} ${LANG==="en"?"stocks · click for full list":"檔・點擊查看完整清單"}</small></span>
    <span class="ind-num"><small>${labels[IND_SORT]}</small><br><b>${IND_SORT.startsWith("median")?indPct(r[IND_SORT]):Number(r[IND_SORT]).toFixed(1)+"%"}</b></span>
    <span class="ind-num"><small>${LANG==="en"?"20D":"20日"}</small><br>${indPct(r.median20)}</span>
    <span class="ind-num"><small>${LANG==="en"?"60D":"60日"}</small><br>${indPct(r.median60)}</span>
    <span class="ind-num"><small>50MA</small><br>${r.above50_pct}%</span></summary>
    <div class="ind-change-grid"><div class="ind-change">${LANG==="en"?"20D vs prior 20D":"20 日較前 20 日"}<b>${indDelta(r.change20)}</b></div><div class="ind-change">${LANG==="en"?"60D vs prior 60D":"60 日較前 60 日"}<b>${indDelta(r.change60)}</b></div><div class="ind-change">${LANG==="en"?"Top-3 concentration":"前三檔正報酬集中度"}<b>${concentration.toFixed(1)}% · ${concentrated?(LANG==="en"?"concentrated":"偏集中"):(LANG==="en"?"broad":"較分散")}</b></div></div>
    <div class="reading-card"><div class="reading-row"><b>${LANG==="en"?"Data":"數據"}</b><span>${LANG==="en"?`20D median ${r.median20}%, 60D median ${r.median60}%, ${r.win20_pct}% advanced.`:`20 日中位報酬 ${r.median20}%，60 日中位報酬 ${r.median60}%，上漲家數比例 ${r.win20_pct}%。`}</span></div><div class="reading-row"><b>${LANG==="en"?"Reading":"解讀"}</b><span>${reading}</span></div><div class="reading-row"><b>${LANG==="en"?"Limit":"限制"}</b><span>${LANG==="en"?"This is a current top-300, backward-looking sample and cannot predict whether sector strength will continue.":"這是目前前 300 大的回顧樣本，不能據此預測產業強勢是否延續。"}</span></div></div>
    <div class="ind-leaders"><b>${LANG==="en"?"Sector stock list":"產業股票清單"}</b><div class="ind-stock-list">${allStocks.map(s=>`<div class="ind-stock"><span><b>${cmpEsc(s.symbol)}</b> ${cmpEsc(LANG==="zh"?(s.name_zh||s.name):s.name)}</span><span>${indPct(s.ret20)}</span></div>`).join("")}</div></div></details>`}).join("");
  const qs=LANG==="en"
    ?{strong:["Persistently Strong","Both 20D and 60D median returns are positive"],recovery:["Early Recovery","60D remains weak; 20D has turned positive"],cooling:["Cooling From Strength","60D remains positive; 20D has turned negative"],weak:["Persistently Weak","Both 20D and 60D median returns are negative"]}
    :{strong:["持續強勢","20日、60日中位報酬皆為正"],recovery:["低檔轉強","60日仍弱，20日已轉正"],cooling:["高檔降溫","60日仍強，20日轉負"],weak:["持續偏弱","20日、60日中位報酬皆為負"]};
  $("#indQuad").innerHTML=Object.entries(qs).map(([key,value])=>`<div class="ind-q"><b>${value[0]}</b><small style="color:var(--mocha)">${value[1]}</small><div>${rows.filter(r=>r.quadrant===key).map(r=>`<span class="ind-chip">${cmpEsc(indName(r))} ${r.median20>=0?"+":""}${r.median20}%</span>`).join("")||`<span class="ind-chip">${LANG==="en"?"None":"目前無"}</span>`}</div></div>`).join("");
}
async function loadIndustries(){
  if(IND_DATA||!$("#indRank"))return;
  $("#indStatus").textContent=LANG==="en"?"Loading sector data…":"讀取產業資料…";
  try{
    const data=await readJson(await fetch("/api/industries"));
    if(!data.ok)throw Error(data.error||(LANG==="en"?"No data":"無資料"));
    IND_DATA=data;renderIndustries();
  }catch(e){
    $("#indStatus").textContent=LANG==="en"
      ?"Sector analysis is being prepared. Please try again shortly."
      :"產業分析正在背景建立中，請稍後再試。";
  }
}
async function loadHomeIndustryBrief(){
  const box=$("#homeIndustryBrief");if(!box)return;
  try{
    const data=await readJson(await fetch("/api/industries"));
    if(!data.ok)throw Error();
    const top=[...(data.industries||[])].sort((a,b)=>Number(b.median20)-Number(a.median20)).slice(0,3);
    box.innerHTML=top.map((r,i)=>`<span>${i===0?(LANG==="en"?"Strongest recently":"近期最強"):(LANG==="en"?"Strong "+(i+1):"強勢 "+(i+1))}・<b>${cmpEsc(indName(r))}</b> ${indPct(r.median20)}</span>`).join("")
      +`<span>${LANG==="en"?"As of":"資料截至"} ${data.as_of}</span>`;
  }catch(e){
    box.innerHTML=`<span>${LANG==="en"?"Sector data is updating; check again shortly":"產業資料正在更新，稍後再查看"}</span>`;
  }
}
document.querySelectorAll("#indTabs button").forEach(button=>button.onclick=()=>{
  IND_SORT=button.dataset.sort;
  document.querySelectorAll("#indTabs button").forEach(x=>x.classList.toggle("on",x===button));
  renderIndustries();
});


/* ---- 長期成長股列表 ---- */
let GROW = null, GROW_SORT = "total";
function growNum(v, dp){
  return (v >= 0 ? "+" : "") + v.toLocaleString(undefined,
    {minimumFractionDigits: dp, maximumFractionDigits: dp}) + "%";
}
function growTable(){
  const rows = GROW.rows.slice().sort((a, b) =>
    GROW_SORT === "total" ? b.total_pct - a.total_pct : b.cagr_pct - a.cagr_pct);
  /* ⚠️ 分拆過的個股報酬被嚴重低估（Nasdaq 報價不還原分拆），要標出來 */
  const spun = new Set((GROW.jumps || []).filter(j => j.pct < -35).map(j => j.symbol));
  /* 主數字＝目前排序的那一個，副數字放另一個 —— 排序切換時兩者對調，
     使用者眼睛不用在欄位間找。 */
  const byTotal = GROW_SORT === "total";
  let h = `<div class="growlist">`;
  rows.forEach((r, i) => {
    const shortMark = r.full_period ? "" :
      ` <span title="${t("grow.shortT", "上市未滿十年，年化不穩")}">⚠️</span>`;
    const spinMark = spun.has(r.symbol) ?
      ` <span title="${t("grow.spinT", "期間有分拆，報酬被低估")}">✂️</span>` : "";
    const main = byTotal ? growNum(r.total_pct, 1) : growNum(r.cagr_pct, 2);
    const sub = byTotal
      ? `${t("grow.cagr", "年化")} ${growNum(r.cagr_pct, 2)}`
      : `${t("grow.total", "累計")} ${growNum(r.total_pct, 1)}`;
    h += `<div class="growrow${i < 3 ? " top" : ""}">`
       + `<div class="growrk">${i + 1}</div>`
       + `<div class="growmid"><div class="growsym">${r.symbol}${spinMark}</div>`
       + `<div class="growname">${r.name || ""}</div></div>`
       + `<div class="growval"><div class="growtot">${main}</div>`
       + `<div class="growsub">${sub} · ${r.years.toFixed(1)}${t("grow.yr", "年")}${shortMark}</div>`
       + `</div></div>`;
  });
  return h + "</div>";
}
function growRender(){
  const box = $("#resultGrow");
  if (!box || !GROW) return;
  const b = GROW.benchmark || {};
  const nBeat = GROW.rows.filter(r => r.cagr_pct > (b.cagr_pct || 0)).length;
  const nNeg = GROW.rows.filter(r => r.total_pct < 0).length;
  const sorted = GROW.rows.map(r => r.total_pct).sort((x, y) => x - y);
  const med = sorted[Math.floor(sorted.length / 2)];
  const on = s => GROW_SORT === s ? " active" : "";
  box.innerHTML =
    `<div class="card"><h2>${t("grow.bench", "同期納斯達克綜合指數")}</h2>`
    + `<div class="macro-grid">`
    + `<div class="mstat"><div class="ml">${t("grow.total", "累計漲幅")}</div>`
    + `<div class="mv">${growNum(b.total_pct || 0, 1)}</div>`
    + `<div class="msub">${b.start_date || ""} ~ ${b.end_date || ""}</div></div>`
    + `<div class="mstat"><div class="ml">${t("grow.cagr", "年化")}</div>`
    + `<div class="mv">${growNum(b.cagr_pct || 0, 2)}</div>`
    + `<div class="msub">${t("grow.benchNote", "指數與個股同為不含息口徑")}</div></div>`
    + `<div class="mstat"><div class="ml">${t("grow.beat", "年化贏過指數")}</div>`
    + `<div class="mv">${nBeat} / ${GROW.rows.length}</div>`
    + `<div class="msub">${t("grow.neg", "十年負報酬")} ${nNeg} ${t("grow.cnt", "檔")}`
    + ` · ${t("grow.med", "中位數")} ${growNum(med, 1)}</div></div>`
    + `</div></div>`
    + `<div class="card"><h2>${t("grow.rank", "排名")}`
    + ` <small style="font-weight:400;opacity:.7">${t("grow.asof", "資料截至")} ${GROW.as_of || "—"}</small></h2>`
    + `<div class="segbar">`
    + `<button class="segbtn${on("total")}" data-sort="total">${t("grow.byTotal", "依累計漲幅")}</button>`
    + `<button class="segbtn${on("cagr")}" data-sort="cagr">${t("grow.byCagr", "依年化報酬")}</button>`
    + `</div>`
    + growTable() + `</div>`;
  box.querySelectorAll(".segbtn").forEach(btn => btn.onclick = () => {
    GROW_SORT = btn.dataset.sort; growRender();
  });
}
async function loadGrowth(){
  const st = $("#statusGrow");
  if (!st) return;
  st.textContent = t("grow.loading", "讀取長期成長股資料…");
  try {
    /* ⚠️ 用 readJson：伺服器出錯時回的是 HTML，直接 .json() 只會看到
       「Unexpected token '<'」，查不出真正原因（2026-08-14 的教訓）。 */
    GROW = await readJson(await fetch("/api/growth"));
    st.textContent = "";
    growRender();
  } catch(e){
    st.textContent = t("grow.fail", "讀取失敗") + "：" + e.message;
  }
}

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
if (START_PAGE === "p12") cmpInit();
if (START_PAGE === "pmac") loadMacro();
if (START_PAGE === "pgrow") loadGrowth();
if (START_PAGE === "pind") loadIndustries();
loadHomeIndustryBrief();
applyCafeTheme(document.documentElement.dataset.theme||'b');
const themeBtn=$("#themeBtn"),themePicker=$("#themePicker");if(themeBtn&&themePicker){themeBtn.onclick=e=>{e.stopPropagation();const open=themePicker.classList.toggle('show');themeBtn.setAttribute('aria-expanded',open?'true':'false')};themePicker.onclick=e=>e.stopPropagation();document.querySelectorAll('[data-theme-choice]').forEach(el=>el.onclick=()=>{applyCafeTheme(el.dataset.themeChoice);closeThemePicker()});document.addEventListener('click',closeThemePicker);document.addEventListener('keydown',e=>{if(e.key==='Escape')closeThemePicker()})}
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

# 網址 → 分頁 id ＋ 每頁專屬的 SEO 中繼資料（與台股版同一套結構）。
#
# ⚠️ `index: False` 的頁面**不會**進 sitemap，而且會送 noindex。
#    試作頁（/pro、/pro/rs）與準備頁（/risk、/alerts）內容太薄，
#    被收錄只會拉低整站的品質評價 —— 但網址仍然存在、可以直接連、可以分享。
#    功能做完之後把 index 改成 True 即可，不必改別的地方。
PAGE_ROUTES = {
    "industries": {
        "page": "pind", "index": True,
        "zh": ("美股產業強弱分析｜20／60日動能、50MA寬度與領先股",
               "以市值前 300 大美股的 Sector 報酬中位數、上漲家數、站上 50 日線與創新高比例，"
               "觀察產業輪動、漲勢擴散與 RS60 領先股。"),
        "en": ("US Sector Strength｜20/60-Day Momentum, 50MA Breadth and Leaders",
               "Compare sectors within the top 300 US stocks using median returns, participation, "
               "50-day moving-average breadth, 60-day highs and RS60 leaders."),
    },
    "screener": {
        "page": "p1", "index": True,
        "zh": ("找強勢股｜美股均線篩選與均線排列",
               "從市值前 150／300 大美股中，篩出站上或跌破 10／20／50／150 日均線、"
               "並符合指定均線排列的股票，附季報營收與 EPS 年增率、創新高分級。免註冊。"),
        "en": ("Find Leading Stocks｜US Moving-Average Screener",
               "Screen the top 150/300 US stocks for those above or below the 10/20/50/150-day "
               "moving averages with a given MA alignment, plus quarterly revenue/EPS growth "
               "and new-high tiers. No sign-up."),
    },
    "pullback": {
        "page": "p3", "index": True,
        "zh": ("拉回找買點｜美股收盤回到均線 ±3%",
               "找出收盤價回到 10／20／50／150 日均線 ±3% 範圍內的美股，依乖離絕對值排序，"
               "用來等強勢股的回檔進場點。免註冊。"),
        "en": ("Pullback Buy Points｜US Stocks Back Within ±3% of an MA",
               "Find US stocks whose close has returned to within ±3% of the 10/20/50/150-day "
               "moving average, sorted by absolute deviation — for timing entries on pullbacks."),
    },
    "consolidation": {
        "page": "p11", "index": True,
        "zh": ("正2 逐月績效｜QLD 對納斯達克的實際倍數",
               "ProShares Ultra QQQ（QLD）最近兩年的逐月報酬與納斯達克綜合指數對照，"
               "並算出每個月的實際倍數。槓桿每日再平衡，累積倍數不會等於 2。"),
        "en": ("2x ETF Monthly Performance｜QLD vs Nasdaq Realised Multiple",
               "Monthly returns for ProShares Ultra QQQ (QLD) against the Nasdaq Composite "
               "over two years, with the realised multiple. Daily rebalancing means "
               "cumulative leverage is never exactly 2x."),
    },
    "growth": {
        "page": "pgrow", "index": True,
        "zh": ("長期成長股列表｜美股市值前 300 大的十年報酬",
               "市值前 300 大美股近十年的累計漲幅與年化報酬率，可依兩者排序。"
               "⚠️ 未還原配息，且股票池是今天的前 300 大，含存活者偏誤。"),
        "en": ("Long-Term Growth List｜10-Year Returns of the Top 300 US Stocks",
               "Ten-year cumulative and annualised returns for the 300 largest US "
               "stocks, sortable by either. Note: not dividend-adjusted, and the "
               "universe is today's top 300 (survivorship bias)."),
    },
    "twr": {
        "page": "p7", "index": True,
        "zh": ("我的績效｜時間加權報酬率（TWR）計算機",
               "逐月輸入淨存入與月底資產，算出不受存提款干擾的累積與年化報酬率。"
               "資料只存在你的瀏覽器，免註冊。"),
        "en": ("My Performance｜Time-Weighted Return (TWR) Calculator",
               "Enter monthly net deposits and month-end balances to get cumulative and annualised "
               "returns unaffected by deposits and withdrawals. Stored only in your browser."),
    },
    "macro": {
        "page": "pmac", "index": True,
        "zh": ("美國利率與購買力｜2 年期、10 年期公債與累積 CPI",
               "查看美國 2 年期、10 年期公債殖利率，以及本年度、近五年與近十年累積 CPI 漲幅，"
               "比較投資報酬門檻、超額報酬與美元實質購買力。"),
        "en": ("US Rates & Purchasing Power｜2Y, 10Y Treasuries and Cumulative CPI",
               "View US 2-year and 10-year Treasury yields plus year-to-date and 10-year "
               "cumulative CPI changes to compare return hurdles and real purchasing power."),
    },
    "articles": {
        "page": "pm", "index": True,
        "zh": ("文章區｜美股大盤判讀與動量交易教學",
               "美股大盤怎麼看、均線與市場寬度怎麼用、美股與台股有什麼不同 —— "
               "美股咖啡館的教學文章索引。"),
        "en": ("Articles｜Reading the US Market and Momentum Trading",
               "How to read the US market, how to use moving averages and market breadth, and how "
               "US and Taiwan markets differ — the US Stock Coffee article index."),
    },
    "comparison": {
        "page": "p12", "index": False,
        "zh": ("同期比較｜同樣本金比較 A、B、C、D 美股報酬",
               "輸入實際買進的 A 股票，再以相同美元本金計算當初若買 B、C、D，"
               "可買股數、目前總值、報酬率與相較 A 的機會成本。資料只存在瀏覽器。"),
        "en": ("Same-period Comparison｜Compare A, B, C and D with Equal Capital",
               "Enter the US stock you actually bought, then compare what the same capital would "
               "be worth in up to three alternatives, including whole-share counts and opportunity cost."),
    },
    # ⚠️ `risk` 在 2026-08-07 功能完成後改成 index=True。
    #    comparison 是個人操作頁；alerts 測試中；pro 兩頁仍是功能試作，全部 noindex。
    "risk": {
        "page": "p8", "index": True,
        "zh": ("風控管理｜自選股 ATR、波動率、均線趨勢與 Beta",
               "選最多 3 檔持股，一次看清 14 日 ATR、半年年化波動率、均線趨勢與對納斯達克的 Beta，"
               "並用進場價算出初始停損與移動停損。資料只存在你的瀏覽器，免註冊。"),
        "en": ("Risk Dashboard｜ATR, Volatility, MA Trend and Beta",
               "Pick up to 3 holdings and see 14-day ATR, six-month annualised volatility, "
               "moving-average trend and beta to the Nasdaq Composite, plus initial and trailing "
               "stops from your entry price. Stored only in your browser, no sign-up."),
    },
    "deduction": {
        "page": "p10", "index": True,
        "zh": ("均線扣抵法｜50／100／150 日線何時追上目前價位",
               "用扣抵值推算納斯達克綜合指數或個股的 50、100、150 日線，"
               "在盤整或延續目前斜率兩種假設下，還要幾個交易日才會追上指定價位。免註冊。"),
        "en": ("Moving-Average Deduction｜When Will the 50, 100 and 150MA Catch Up",
               "Project the 50-, 100- and 150-day moving averages for the Nasdaq Composite or any "
               "top-300 US stock using the deduction value, and see how many sessions they need "
               "to reach a given price under a flat or trend-continuation assumption."),
    },
    "alerts": {
        "page": "p4", "index": False,
        "zh": ("推播通知｜收盤到價提醒", "設定目標價，收盤價落在 ±2% 時通知你。測試中。"),
        "en": ("Price Alerts｜Close-Price Notifications",
               "Set a target price and get notified when the close lands within ±2%. In testing."),
    },
    "pro": {
        "page": "p5", "index": False,
        "zh": ("專業版創新高股票篩選", "從市值前 300 大美股找出近期創 3 個月至 5 年新高的股票。功能試作中。"),
        "en": ("Pro New-high Stock Screener",
               "Find recent 3-month through 5-year highs among the top 300 US stocks. Prototype."),
    },
    "pro/rs": {
        "page": "p9", "index": False,
        "zh": ("RS 相對強弱排名｜美股市場百分位",
               "比較市值前 300 大美股 20／60／120／250 日的價格表現，篩出 RS 領先股。功能試作中。"),
        "en": ("RS Relative-Strength Ranking｜US Market Percentile",
               "Rank the top 300 US stocks by 20-, 60-, 120- or 250-day price strength. Prototype."),
    },
}

# 首頁沒有 slug，另外放一份。
HOME_SEO = {
    "zh": ("美股咖啡館 US Stock Coffee｜美股選股工具・均線篩選",
           "免費美股選股工具。用 10/20/50/150 日均線與均線排列篩選市值前 300 大美股，"
           "找出強勢股與拉回買點，附大盤生命週期、市場寬度與 TWR 報酬率計算機。免註冊、開啟即用。"),
    "en": ("US Stock Coffee｜US Stock Screener · Moving-Average Filter",
           "Free US stock screener. Filter the top 300 US stocks by 10/20/50/150-day moving "
           "averages and MA alignment to find leaders and pullback entries, with a market "
           "lifecycle view, market breadth and a TWR calculator. No sign-up."),
}

# 分頁 id → 網址路徑（反查用）
PAGE_PATHS = {v["page"]: k for k, v in PAGE_ROUTES.items()}

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

    def _link(m):
        text, url = m.group(1), m.group(2)
        if url.startswith("/"):
            return '<a href="%s">%s</a>' % (url, text)      # 站內：同一個分頁
        return '<a href="%s" target="_blank" rel="noopener">%s</a>' % (url, text)

    def inline(s):
        s = _h.escape(s)
        s = re.sub(r"\*\*(.+?)\*\*", r"<strong>\1</strong>", s)
        # ⚠️⚠️ **站內與外部連結必須用同一條規則一次處理，而且標題不能含中括號。**
        #    2026-08-07 修：原本拆成兩條 re.sub，外部連結那條先跑。
        #    同一行裡「先站內、後外部」時（例：`[A](/)是[B](https://…)`），
        #    `\[(.+?)\]` 會回溯吃掉中間整段，把 `A](/)是[B` 當成連結文字 ——
        #    畫面上就會看到多出來的 `](/)是[` 符號。
        #    `[^\[\]]+` 讓標題不能跨過任何一組中括號，回溯就發生不了。
        s = re.sub(r"\[([^\[\]]+)\]\((https?://[^\s)]+|/[^\s)]*)\)", _link, s)
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


def _load_articles(lang="zh"):
    """讀文章並解析 front-matter。

    lang="zh" → `articles/*.md`；lang="en" → `articles/en/*.md`（**同檔名對應同一篇**）。

    ⚠️⚠️ **英文版缺檔時整批退回中文**，不會空白也不會半中半英。
    因為文章是靠「檔名」配對的，只補一半會讓兩種語言的清單長度不同 ——
    而 sitemap 的 hreflang 要求兩邊互指，數量對不上 Search Console 會整組忽略。
    📌 所以要嘛整批補齊，要嘛整批沒有，**不要只補幾篇**。
    """
    base = ARTICLES_DIR if lang == "zh" else os.path.join(ARTICLES_DIR, "en")
    if lang == "en" and not os.path.isdir(base):
        return _load_articles("zh")
    items = []
    if not os.path.isdir(base):
        return items
    for fn in sorted(os.listdir(base)):
        if not fn.endswith(".md"):
            continue
        try:
            with open(os.path.join(base, fn), "r", encoding="utf-8") as f:
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


def _art_links_html(lang="zh"):
    """⚠️ 這段會被塞進 `<ul class="alinks">` 裡，**只能產生 `<li>`**。

    語言切換的 class 必須掛在 `<li>` 自己身上，不可以在外面包一層 `<span>` ——
    `<ul>` 的合法子元素只有 `<li>`，包 span 會被瀏覽器搬出清單，版面直接垮掉，
    而且 Python 與 JS 的語法檢查都抓不到（見 5.5 的同類教訓）。
    """
    import html as _h
    pre = "/en" if lang == "en" else ""
    cls = 'q-en" style="display:none' if lang == "en" else "q-zh"
    rows = []
    for a in _load_articles(lang):
        rows.append(
            '<li class="%s"><a href="%s/article/%s"><span class="atag">%s</span>'
            '<div class="atitle">%s</div><p class="asum">%s</p>'
            '<span class="adate">%s</span></a></li>' %
            (cls, pre, quote(a["slug"]), _h.escape(a["tag"]), _h.escape(a["title"]),
             _h.escape(a["summary"]), _h.escape(a["date"])))
    return "".join(rows)


def _find_article(aid, lang="zh"):
    items = _load_articles(lang)
    for a in items:
        if aid in (a["id"], a["slug"]):
            return a, [x for x in items if x["id"] != a["id"]][:5]
    return None, items[:5]


ARTICLE_PAGE = r"""<!doctype html><html lang="__HTMLLANG__"><head>
<meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<title>__TITLE__｜美股咖啡館 US Stock Coffee</title>
<meta name="description" content="__DESC__"><link rel="canonical" href="__URL__">
<meta name="google-adsense-account" content="ca-pub-4558422800482658">
__ALTS__
<meta name="robots" content="index,follow,max-image-preview:large">
<meta property="og:type" content="article"><meta property="og:site_name" content="美股咖啡館 US Stock Coffee">
<meta property="og:title" content="__TITLE__"><meta property="og:description" content="__DESC__">
<meta property="og:url" content="__URL__"><meta property="og:image" content="__SITE__/icon.png">
<script type="application/ld+json">__JSONLD__</script>
<style>
:root{--milk:#f1ead9;--foam:#fbf6ec;--grounds:#e4d7c1;--espresso:#33241a;--mocha:#6b5540;--caramel:#c68a3e;--caramel2:#a56c24}
*{box-sizing:border-box}html{min-height:100%;background:var(--milk);overscroll-behavior-y:none}body{margin:0;min-height:100vh;min-height:100dvh;background:var(--milk);color:var(--espresso);font-family:-apple-system,BlinkMacSystemFont,"PingFang TC","Noto Sans TC",sans-serif;line-height:1.95;overflow-x:clip;overscroll-behavior-y:none}
.top{background:var(--espresso);padding:12px 18px;display:flex;justify-content:space-between}.top a{color:var(--foam);text-decoration:none;font-weight:800}.top .go{color:#f0c88a}
main{max-width:760px;margin:auto;padding:24px 18px calc(60px + env(safe-area-inset-bottom))}.crumb{font-size:13px;color:var(--mocha)}.crumb a{color:var(--caramel2);text-decoration:none}.tag{display:inline-block;margin-top:18px;background:var(--caramel);color:white;border-radius:999px;padding:2px 11px;font-size:12px;font-weight:700}
h1{font-size:28px;line-height:1.45;margin:12px 0 5px}.meta{font-size:12px;color:var(--mocha)}.summary{margin:18px 0 28px;background:var(--foam);border:1px solid var(--grounds);border-left:4px solid var(--caramel);border-radius:0 12px 12px 0;padding:12px 16px;color:var(--mocha)}
article{font-size:16.5px}article h2{font-size:20px;margin:34px 0 10px;border-left:4px solid var(--caramel);padding-left:10px}article h3{font-size:17px;color:var(--caramel2);margin:26px 0 8px}article p{margin:12px 0}article li{margin:7px 0}article strong{color:var(--espresso)}
.cta{display:block;margin-top:36px;padding:13px;text-align:center;background:var(--caramel);color:white;border-radius:999px;text-decoration:none;font-weight:800}.more{margin-top:35px;border-top:1px solid var(--grounds);padding-top:18px}.more a{color:var(--caramel2);text-decoration:none}
</style></head><body><div class="top"><a href="__HOME__">☕ 美股咖啡館</a><a class="go" href="__HOME__">__CTA_TOP__</a></div>
<main><nav class="crumb"><a href="__HOME__">__S_HOME__</a> › <a href="__PRE__/articles">__S_ARTS__</a> › __TITLE__</nav>
<span class="tag">__TAG__</span><h1>__TITLE__</h1><div class="meta">__DATE__</div>
<div class="summary">__DESC__</div><article>__BODY__</article>
<a class="cta" href="__HOME__">__CTA__</a><div class="more"><b>__S_MORE__</b><ul>__MORE__</ul></div></main></body></html>"""

ARTICLE_STRINGS = {
    "zh": {"home": "首頁", "arts": "文章區", "more": "其他文章",
           "cta_top": "開啟選股工具", "cta": "免費使用美股選股工具，免註冊 →",
           "htmllang": "zh-Hant-TW"},
    "en": {"home": "Home", "arts": "Articles", "more": "More articles",
           "cta_top": "Open the screener", "cta": "Use the free US stock screener — no sign-up →",
           "htmllang": "en"},
}


def _render_article(a, lang, others):
    """單篇文章頁。中英各有自己的網址：`/article/<slug>` 與 `/en/article/<slug>`。

    ⚠️⚠️ **canonical 與 hreflang 必須互相對應**：中文頁要指到英文頁、英文頁也要指回
    中文頁，兩邊都要列出自己。少一邊 Search Console 會報「沒有回傳連結」，
    然後**整組忽略**（不是只忽略缺的那一邊）。
    """
    import html as _h
    S = ARTICLE_STRINGS[lang]
    pre = "/en" if lang == "en" else ""
    zh_url = SITE_URL + "/article/" + quote(a["slug"])
    en_url = SITE_URL + "/en/article/" + quote(a["slug"])
    url = en_url if lang == "en" else zh_url
    alts = ('<link rel="alternate" hreflang="zh-Hant" href="' + zh_url + '">\n'
            '<link rel="alternate" hreflang="en" href="' + en_url + '">\n'
            '<link rel="alternate" hreflang="x-default" href="' + zh_url + '">')
    ld = {"@context": "https://schema.org", "@type": "Article",
          "headline": a["title"], "description": a["summary"], "url": url,
          "datePublished": a["date"], "dateModified": a["date"],
          "inLanguage": S["htmllang"], "isAccessibleForFree": True,
          "author": {"@type": "Organization", "name": "美股咖啡館 US Stock Coffee"}}
    more = "".join('<li><a href="%s/article/%s">%s</a></li>' %
                   (pre, quote(x["slug"]), _h.escape(x["title"])) for x in others)
    out = ARTICLE_PAGE
    vals = {"__TITLE__": _h.escape(a["title"]), "__DESC__": _h.escape(a["summary"]),
            "__TAG__": _h.escape(a["tag"]), "__DATE__": _h.escape(a["date"]),
            "__BODY__": a["html"], "__MORE__": more, "__URL__": url,
            "__ALTS__": alts, "__HTMLLANG__": S["htmllang"], "__PRE__": pre,
            "__HOME__": "/?lang=en" if lang == "en" else "/",
            "__S_HOME__": S["home"], "__S_ARTS__": S["arts"], "__S_MORE__": S["more"],
            "__CTA_TOP__": S["cta_top"], "__CTA__": S["cta"],
            "__SITE__": SITE_URL, "__JSONLD__": json.dumps(ld, ensure_ascii=False)}
    for k, v in vals.items():
        out = out.replace(k, v)
    return out


def _article_slug_redirect(a, aid, pre):
    """用舊的檔名網址進來 → **301 導到 slug 版本**（正式網址只有一個）。

    ⚠️ 舊網址永遠保持有效（分享出去的連結不能變 404），只是會被導過去。
    ⚠️ 一定要 301 不能 302 —— 302 對搜尋引擎的意思是「原網址才是正式的」，正好相反。
    """
    if a["slug"] != aid:
        from flask import redirect
        return redirect(pre + "/article/" + quote(a["slug"]), code=301)
    return None


@app.route("/article/<path:aid>")
def article_page(aid):
    a, others = _find_article(aid, "zh")
    if not a:
        return _render("articles"), 404
    r = _article_slug_redirect(a, aid, "")
    return r if r else _render_article(a, "zh", others)


@app.route("/en/article/<path:aid>")
def article_page_en(aid):
    a, others = _find_article(aid, "en")
    if not a:
        return _render("articles"), 404
    r = _article_slug_redirect(a, aid, "/en")
    return r if r else _render_article(a, "en", others)


@app.route("/en/articles")
def articles_index_en():
    """`/en/articles` → 301 到 `/articles?lang=en`。

    ⚠️ **文章索引與單篇文章刻意用不同的網址形式**，這不是不一致，是遷就既有架構：
      ・索引頁是主站 PAGE 的一個分頁 → 沿用全站的 `?lang=en` 參數式（見 sitemap 的 `pair()`）
      ・單篇文章是獨立的 HTML 模板 → 用路徑式 `/en/article/<slug>`
    這裡只是給猜網址的人一個入口，並用 301 明確指向正式版本。
    """
    from flask import redirect
    return redirect("/articles?lang=en", code=301)


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



def _quote_card_html(q, extra=False):
    """單張名言卡。extra=True 是「再抽一張」抽出來的，加淡入動畫。"""
    import html as _h
    if len(q["lines"]) > 1:            # 主題卡：多行條列
        body = ('<ul class="qlist">'
                + "".join("<li>" + _h.escape(x) + "</li>" for x in q["lines"])
                + '</ul>')
    else:                              # 單句卡
        body = '<div class="qtext">' + _h.escape(q["lines"][0]) + '</div>'
    return ('<div class="' + ("qcard qnew" if extra else "qcard")
            + '" data-no="' + str(q["no"]) + '">'
            '<span class="qtag">' + _h.escape(q["tag"]) + '</span>' + body
            + '<div class="qfoot"><span>' + _h.escape(q["author"]) + '</span>'
            '<span class="qnum">' + str(q["no"]) + ' / ' + str(q["total"]) + '</span>'
            '</div></div>')


def _quotes_html():
    """首頁名言卡（伺服器端渲染，開啟即顯示、不必等 API）。

    ⚠️ 中英兩份都輸出、用 `.q-zh` / `.q-en` 切換 —— 與市場階段、本日推薦同一套機制，
       切語言不必重新請求。
    ⚠️ **只讀市場階段的快取**（`market_phase_cached` 本來就不連網）。
    """
    try:
        phase, _s, _d, _b = market_phase_cached()
    except Exception:
        phase = ""
    zh = "\n".join("  " + _quote_card_html(q) for q in home_quotes("zh", phase))
    en = "\n".join("  " + _quote_card_html(q) for q in home_quotes("en", phase))
    return ('<div class="q-zh">\n' + zh + '\n</div>\n'
            '<div class="q-en" style="display:none">\n' + en + '\n</div>')


def _data_health_snapshot():
    """首頁與診斷端點共用的資料健康快照；允許一個平日的來源延遲。"""
    counts = _load_cache(MARKET_COUNT_CACHE, None) or {}
    breadth = _load_cache("breadth.json", None) or {}
    index_data = _load_cache("nasdaq_index.json", None) or {}
    actuals = {
        "market_returns": str((counts.get("recent_returns") or {}).get("as_of") or counts.get("as_of") or ""),
        "market_breadth": max(breadth) if breadth else "",
        "nasdaq_index": max(index_data) if index_data else "",
    }
    labels = {"market_returns": ("近期選股統計", "selection statistics"),
              "market_breadth": ("市場寬度", "market breadth"),
              "nasdaq_index": ("納斯達克指數", "Nasdaq index")}
    items, warnings_zh, warnings_en = {}, [], []
    et_now = _utcnow() - timedelta(hours=_et_offset_hours(_utcnow()))
    failed_hint = "%s %s" % (SCHED_STATE.get("last_result") or "", SCHED_STATE.get("loop_error") or "")

    def quality(lag, failed=False, market=None):
        if failed and lag > 0:
            return "failed", QUALITY_STATUS_ZH["failed"], "Update failed; using older data", "danger"
        if lag <= 0:
            return "fresh", QUALITY_STATUS_ZH["fresh"], "Data current", "ok"
        if lag == 1:
            market_now = (_utcnow() + timedelta(hours=9)) if market == "jp" else et_now
            publish_hour = 10 if market == "jp" else UPDATE_HOUR_ET
            if market_now.weekday() < 5 and market_now.hour < publish_hour:
                return "pending", QUALITY_STATUS_ZH["pending"], "Awaiting today’s release", "pending"
        if lag == 1:
            return "lag1", QUALITY_STATUS_ZH["lag1"], "One session behind", "warn"
        return "overdue", QUALITY_STATUS_ZH["overdue"], "Data exceeds allowed delay", "danger"

    for key, actual in actuals.items():
        lag = _business_days_behind(actual)
        status, zh_text, en_text, severity = quality(
            lag, "失敗" in failed_hint or "failed" in failed_hint.lower())
        items[key] = {"actual": actual, "business_days_behind": lag, "status": status,
                      "status_zh": zh_text, "status_en": en_text, "severity": severity,
                      "label_zh": labels[key][0], "label_en": labels[key][1]}
        if status in ("failed", "overdue"):
            zh, en = labels[key]
            warnings_zh.append("%s：%s（目前 %s）" % (zh, zh_text, actual or "無資料"))
            warnings_en.append("%s: %s (current %s)" % (en, en_text, actual or "missing"))
    macro = _load_cache(MACRO_CACHE_FILE, None) or {}
    macro_items = {x.get("key"): x for x in (macro.get("items") or [])}
    for health_key, keys, zh_label, en_label in (
            ("us_yields", ("us2y", "us10y", "us30y"), "美國公債利率", "US Treasury yields"),
            ("jp_yields", ("jp2y", "jp10y", "jp30y"), "日本公債利率", "Japan government-bond yields")):
        dates = [str((macro_items.get(key) or {}).get("date") or "") for key in keys]
        actual = min(dates) if all(dates) else ""
        market = "us" if health_key == "us_yields" else "jp"
        lag = _business_days_behind(actual, market=market)
        y_status, y_zh, y_en, y_severity = quality(
            lag, "失敗" in failed_hint or "failed" in failed_hint.lower(), market)
        items[health_key] = {"actual": actual, "business_days_behind": lag,
                             "status": y_status, "status_zh": y_zh, "status_en": y_en,
                             "severity": y_severity, "label_zh": zh_label, "label_en": en_label}
        if y_status in ("failed", "overdue"):
            warnings_zh.append(zh_label + "：" + y_zh)
            warnings_en.append(en_label + ": " + y_en)
    fed_data = _load_cache(FED_POLICY_CACHE_FILE, None) or {}
    fed_policy = fed_data.get("policy") or {}
    treasury_actions = fed_data.get("treasury") or {}
    for health_key, actual, zh_label, en_label in (
            ("fed_policy", str((fed_policy.get("dff") or {}).get("date") or ""),
             "聯準會政策資料", "Federal Reserve policy data"),
            ("treasury_actions", str((treasury_actions.get("tga") or {}).get("date") or ""),
             "美國財政部行動", "U.S. Treasury actions")):
        lag = _business_days_behind(actual, market="us")
        # EFFR 與 Daily Treasury Statement 都是下一營業日發布；這一日是正常發布差，
        # 不應標成資料落後。超過它才進入「待公布／落後」判斷。
        quality_lag = max(0, lag - 1)
        p_status, p_zh, p_en, p_severity = quality(
            quality_lag, bool(fed_data.get("errors")), "us")
        items[health_key] = {"actual": actual, "business_days_behind": lag,
                             "status": p_status, "status_zh": p_zh, "status_en": p_en,
                             "severity": p_severity, "label_zh": zh_label, "label_en": en_label}
        if p_status in ("failed", "overdue"):
            warnings_zh.append(zh_label + "：" + p_zh)
            warnings_en.append(en_label + ": " + p_en)
    heartbeat = SCHED_STATE.get("heartbeat_ts") or 0
    schedule_status = "running" if heartbeat and time.time() - heartbeat <= 360 else ("starting" if SCHED_STATE.get("thread_started") else "stopped")
    if schedule_status == "stopped":
        warnings_zh.append("背景排程未啟動")
        warnings_en.append("background scheduler is not running")
    return {"status": "ok" if not warnings_zh else "stale", "items": items,
            "schedule": {"status": schedule_status, "heartbeat_age_sec": round(time.time() - heartbeat) if heartbeat else None,
                         "last_result": SCHED_STATE.get("last_result"), "completed_session": SCHED_STATE.get("completed_session")},
            "warnings_zh": warnings_zh, "warnings_en": warnings_en,
            "checked_at": _fmt_et(_utcnow())}


def _fed_policy_panel_html():
    """首頁聯準會與財政部快照；只讀背景排程快取，不在頁面請求中連外。"""
    import html as _h
    data = _load_cache(FED_POLICY_CACHE_FILE, None) or {}
    if not data:
        return ('<section class="card fed-policy-panel"><div class="fed-policy-head"><div>'
                '<h2><span class="q-zh">聯準會與財政部動向</span><span class="q-en" style="display:none">Fed &amp; Treasury watch</span></h2>'
                '<p><span class="q-zh">官方資料正在首次整理，完成後會自動顯示。</span><span class="q-en" style="display:none">Official data are being prepared for the first time.</span></p>'
                '</div><span class="policy-status warn"><span class="q-zh">資料整理中</span><span class="q-en" style="display:none">Updating</span></span></div></section>')

    policy = data.get("policy") or {}; liquid = data.get("liquidity") or {}
    balance = data.get("balance_sheet") or {}; treasury = data.get("treasury") or {}
    dff, lower, upper, iorb = (policy.get(k) or {} for k in ("dff", "dfedtarl", "dfedtaru", "iorb"))
    rrp, repo = liquid.get("on_rrp") or {}, liquid.get("repo") or {}
    assets = balance.get("total_assets") or {}; treas = balance.get("treasury_holdings") or {}
    mbs = balance.get("mbs_holdings") or {}; tga = treasury.get("tga") or {}

    def number(item, scale=1, suffix=""):
        try:
            return ("{:,.2f}".format(float(item.get("value")) / scale).rstrip("0").rstrip(".") + suffix)
        except (TypeError, ValueError):
            return "—"

    def signed(value, scale=1, suffix=""):
        try:
            return "%+.1f%s" % (float(value) / scale, suffix)
        except (TypeError, ValueError):
            return "—"

    def status(label_zh, label_en, date_text, weekly=False, expected_lag=0, publish_hour=17):
        if not date_text:
            return '<span class="policy-status danger"><span class="q-zh">%s：更新失敗</span><span class="q-en" style="display:none">%s: failed</span></span>' % (label_zh, label_en)
        if weekly:
            try:
                age = ((_utcnow() - timedelta(hours=_et_offset_hours(_utcnow()))).date()
                       - datetime.strptime(date_text[:10], "%Y-%m-%d").date()).days
            except ValueError:
                age = 99
            level, zh_state, en_state = (("ok", "資料最新", "current") if age <= 8 else
                                         ("danger", "資料落後", "delayed"))
        else:
            lag = _business_days_behind(date_text, market="us")
            adjusted = max(0, lag - expected_lag)
            et_now = _utcnow() - timedelta(hours=_et_offset_hours(_utcnow()))
            level, zh_state, en_state = (("ok", "資料最新", "current") if adjusted <= 0 else
                                         ("warn", "尚待今日公布", "awaiting today's release") if adjusted == 1 and et_now.hour < publish_hour else
                                         ("warn", "落後一個交易日", "one session behind") if adjusted == 1 else
                                         ("danger", "資料落後", "delayed"))
        return '<span class="policy-status %s"><span class="q-zh">%s：%s</span><span class="q-en" style="display:none">%s: %s</span></span>' % (level, label_zh, zh_state, label_en, en_state)

    within = False
    try:
        within = float(lower["value"]) <= float(dff["value"]) <= float(upper["value"])
    except (KeyError, TypeError, ValueError):
        pass
    policy_read_zh = ("有效聯邦基金利率仍在目標區間內。" if within else "有效聯邦基金利率與目標區間需要留意。")
    policy_read_en = ("The effective fed funds rate remains inside the target range." if within else
                      "The effective fed funds rate versus the target range needs attention.")
    rrp_change = rrp.get("change_20")
    liquid_zh = ("ON RRP近20期下降，聯準會吸收的隔夜閒置現金減少。" if isinstance(rrp_change, (int, float)) and rrp_change < 0 else
                 "ON RRP近20期增加，停放在聯準會的隔夜現金增加。" if isinstance(rrp_change, (int, float)) and rrp_change > 0 else
                 "ON RRP近20期變化有限。")
    liquid_en = ("ON RRP has declined over 20 observations, so less overnight cash is being absorbed." if isinstance(rrp_change, (int, float)) and rrp_change < 0 else
                 "ON RRP has risen over 20 observations, so more overnight cash is parked at the Fed." if isinstance(rrp_change, (int, float)) and rrp_change > 0 else
                 "ON RRP has changed little over 20 observations.")
    holdings_4w = sum(x for x in (treas.get("change_4w"), mbs.get("change_4w")) if isinstance(x, (int, float)))
    if holdings_4w < -5000:
        balance_zh, balance_en = "公債與MBS持有量近4週縮減，資產負債表仍在收縮。", "Treasury and MBS holdings fell over four weeks; the balance sheet is still contracting."
    elif holdings_4w > 5000:
        balance_zh, balance_en = "公債與MBS持有量近4週增加；這不自動等同QE。", "Treasury and MBS holdings rose over four weeks; this alone is not QE."
    else:
        balance_zh, balance_en = "公債與MBS持有量近4週大致持平。", "Treasury and MBS holdings were broadly stable over four weeks."
    tga_change = tga.get("change_20")
    tga_zh = ("TGA近20期回補，通常會暫時吸收金融體系現金。" if isinstance(tga_change, (int, float)) and tga_change > 0 else
              "TGA近20期下降，財政支出通常會把現金釋回金融體系。" if isinstance(tga_change, (int, float)) and tga_change < 0 else
              "TGA近20期變化有限。")
    tga_en = ("TGA rose over 20 observations, which usually absorbs cash from the financial system." if isinstance(tga_change, (int, float)) and tga_change > 0 else
              "TGA fell over 20 observations; Treasury outlays usually return cash to the financial system." if isinstance(tga_change, (int, float)) and tga_change < 0 else
              "TGA changed little over 20 observations.")

    auctions = treasury.get("auctions") or []
    auction_zh = "、".join('%s %s $%.1fB' %
                          (_h.escape(str(x.get("auction_date") or "—")),
                           _h.escape(str(x.get("term") or x.get("type") or "")),
                           float(x.get("offering_bn") or 0)) for x in auctions[:3]) or "尚無已公告標售"
    auction_en = " · ".join('%s %s $%.1fB' %
                            (_h.escape(str(x.get("auction_date") or "—")),
                             _h.escape(str(x.get("term") or x.get("type") or "")),
                             float(x.get("offering_bn") or 0)) for x in auctions[:3]) or "No announced auctions"
    fomc = data.get("next_fomc") or {}
    fomc_date = _h.escape(str(fomc.get("decision_date") or "—"))
    auction_total = float(treasury.get("next_7d_offering_bn") or 0)
    as_of = _h.escape(str(data.get("as_of") or "—"))
    return (
        '<section class="card fed-policy-panel"><div class="fed-policy-head"><div><h2><span class="q-zh">聯準會與財政部動向</span><span class="q-en" style="display:none">Fed &amp; Treasury watch</span></h2>'
        '<p><span class="q-zh">政策留言板・只列關鍵數字與已發生的變化</span><span class="q-en" style="display:none">Policy board · key figures and observed changes only</span></p></div><div class="fed-policy-status">'
        + status("利率", "Rates", str(dff.get("date") or ""), expected_lag=1, publish_hour=10)
        + status("資產負債表", "Balance sheet", str(assets.get("date") or ""), True)
        + status("財政部", "Treasury", str(tga.get("date") or ""), expected_lag=1, publish_hour=16) + '</div></div>'
        '<ul class="policy-board">'
        '<li><span class="policy-board-label"><span class="q-zh">政策利率</span><span class="q-en" style="display:none">Policy rate</span></span><span class="policy-board-data"><span class="q-zh">目標 ' + number(lower, 1, "%") + '–' + number(upper, 1, "%") + '　EFFR ' + number(dff, 1, "%") + '　IORB ' + number(iorb, 1, "%") + '</span><span class="q-en" style="display:none">Target ' + number(lower, 1, "%") + '–' + number(upper, 1, "%") + ' · EFFR ' + number(dff, 1, "%") + ' · IORB ' + number(iorb, 1, "%") + '</span></span><span class="policy-board-read"><span class="q-zh">' + policy_read_zh + ' 下次FOMC決議 <b>' + fomc_date + '</b>。</span><span class="q-en" style="display:none">' + policy_read_en + ' Next FOMC decision: <b>' + fomc_date + '</b>.</span></span></li>'
        '<li><span class="policy-board-label"><span class="q-zh">隔夜流動性</span><span class="q-en" style="display:none">Overnight liquidity</span></span><span class="policy-board-data"><span class="q-zh">ON RRP $' + number(rrp, 1, "B") + '　20期 ' + signed(rrp_change, 1, "B") + '　Repo $' + number(repo, 1, "B") + '</span><span class="q-en" style="display:none">ON RRP $' + number(rrp, 1, "B") + ' · 20 obs ' + signed(rrp_change, 1, "B") + ' · Repo $' + number(repo, 1, "B") + '</span></span><span class="policy-board-read"><span class="q-zh">' + liquid_zh + '</span><span class="q-en" style="display:none">' + liquid_en + '</span></span></li>'
        '<li><span class="policy-board-label"><span class="q-zh">聯準會持有</span><span class="q-en" style="display:none">Fed holdings</span></span><span class="policy-board-data"><span class="q-zh">總資產 $' + number(assets, 1000000, "T") + '　美債 $' + number(treas, 1000000, "T") + '　MBS $' + number(mbs, 1000000, "T") + '　4週 ' + signed(holdings_4w, 1000, "B") + '</span><span class="q-en" style="display:none">Assets $' + number(assets, 1000000, "T") + ' · Treasuries $' + number(treas, 1000000, "T") + ' · MBS $' + number(mbs, 1000000, "T") + ' · 4w ' + signed(holdings_4w, 1000, "B") + '</span></span><span class="policy-board-read"><span class="q-zh">' + balance_zh + '</span><span class="q-en" style="display:none">' + balance_en + '</span></span></li>'
        '<li><span class="policy-board-label"><span class="q-zh">財政部現金</span><span class="q-en" style="display:none">Treasury cash</span></span><span class="policy-board-data"><span class="q-zh">TGA $' + number(tga, 1000, "B") + '　20期 ' + signed(tga_change, 1000, "B") + '</span><span class="q-en" style="display:none">TGA $' + number(tga, 1000, "B") + ' · 20 obs ' + signed(tga_change, 1000, "B") + '</span></span><span class="policy-board-read"><span class="q-zh">' + tga_zh + '</span><span class="q-en" style="display:none">' + tga_en + '</span></span></li>'
        '<li><span class="policy-board-label"><span class="q-zh">國債標售</span><span class="q-en" style="display:none">Treasury auctions</span></span><span class="policy-board-data"><span class="q-zh">未來7日合計 $' + ('%.1fB' % auction_total) + '</span><span class="q-en" style="display:none">Next 7 days $' + ('%.1fB' % auction_total) + '</span></span><span class="policy-board-read"><span class="q-zh">' + auction_zh + '</span><span class="q-en" style="display:none">' + auction_en + '</span></span></li></ul>'
        '<div class="policy-board-meta"><p class="policy-board-limit"><span class="q-zh">資料截至 ' + as_of + '。逆回購、TGA與標售只描述美元流動性，不能單獨預測股市；只有官方明確啟動淨資產購買計畫才標示為QE。</span><span class="q-en" style="display:none">Data as of ' + as_of + '. ON RRP, TGA and auctions describe dollar liquidity but cannot forecast stocks alone. QE is shown only for an officially announced net asset-purchase programme.</span></p><div class="fed-source"><a href="https://fred.stlouisfed.org/" target="_blank" rel="noopener">Fed / FRED</a> · <a href="https://fiscaldata.treasury.gov/" target="_blank" rel="noopener">Treasury</a> · <a href="https://www.federalreserve.gov/monetarypolicy/fomccalendars.htm" target="_blank" rel="noopener">FOMC</a></div></div></section>')


def _update_note_html():
    """首頁的資料日期、實際完成時間與下次排程。只讀快取，不連網。

    排程從 17:00 ET 開始，來源還沒有當日 K 線就每 20 分鐘重試，因此不預告
    一個假的「完成區間」；改為顯示上次真正完成的美東時間。
    """
    try:
        nxt = _next_update_utc()
    except Exception:
        return ""
    as_of = _home_screen_target_date() or ""
    completed_session = str(SCHED_STATE.get("completed_session") or "")
    completed_at = str(SCHED_STATE.get("completed_at_et") or "")
    completed_zh = ("　·　當日更新完成 <b>%s</b>（美東時間）" % completed_at
                    if completed_at and completed_session == as_of else "")
    completed_en = ("　·　daily update completed <b>%s</b>" % completed_at
                    if completed_at and completed_session == as_of else "")
    et_start = nxt - timedelta(hours=_et_offset_hours(nxt))
    zh = ("資料日期 <b>%s</b>%s　·　下次於美東 <b>%s</b> 開始檢查"
          % (as_of.replace("-", "/") or "—", completed_zh,
             et_start.strftime("%m/%d %H:%M")))
    en = ("Data as of <b>%s</b>%s　·　next check starts <b>%s ET</b>"
          % (as_of or "—", completed_en, et_start.strftime("%m/%d %H:%M")))
    tip_zh = "美股 16:00 收盤後，自 17:00 ET 起每 %d 分鐘檢查，直到成功更新當日收盤價。" % UPDATE_RETRY_MINUTES
    tip_en = ("After the 16:00 ET close, we check every %d minutes from 17:00 ET "
              "until that session's closing prices are updated." % UPDATE_RETRY_MINUTES)
    health = _data_health_snapshot()
    health_zh = ("✓ 核心資料與排程正常" if health["status"] == "ok" else
                 "⚠ 資料更新中／落後：" + "、".join(health["warnings_zh"]))
    health_en = ("✓ Core data and schedules are healthy" if health["status"] == "ok" else
                 "⚠ Updating or delayed: " + ", ".join(health["warnings_en"]))
    health_cls = "health-ok" if health["status"] == "ok" else "health-stale"
    return ('<div class="updnote">'
            '<span class="q-zh">' + zh + '<small>' + tip_zh + '</small><span class="data-health-line ' + health_cls + '">' + health_zh + '</span></span>'
            '<span class="q-en" style="display:none">' + en
            + '<small>' + tip_en + '</small><span class="data-health-line ' + health_cls + '">' + health_en + '</span></span></div>')


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
    stage = LIFECYCLE_STAGE.get(phase)
    stage_html = ""
    if stage:
        stage_html = (
            '<span class="mk-stage q-zh">第 ' + str(stage) + ' / 4 階段</span>'
            '<span class="mk-stage q-en" style="display:none">Stage ' + str(stage) + ' of 4</span>')
    zh_rule = {
        "tailwind": "5日線與10日線可互換，但兩者都高於20日線，且20日線高於60日線、60日線高於120日線",
        "transition": "均線非多頭排列，至少兩條短期均線與60日線乖離小於5%並持續三日，且60日線高於120日線",
        "riskoff": "收盤價連續三日低於120日線3%以上",
        "recovery_confirmed": "120日線高於20日線或60日線後啟動觀察，接著收盤價連續三日站上120日線4%以上",
    }.get(phase, "")
    en_rule = {
        "tailwind": "the 5-day and 10-day MAs may swap order, but both stay above 20MA, with 20MA above 60MA and 60MA above 120MA",
        "transition": "MAs are not bullish, at least two short MAs stay within 5% of the 60-day MA for three sessions, and the 60-day MA remains above the 120-day MA",
        "riskoff": "the close stays more than 3% below the 120-day MA for three sessions",
        "recovery_confirmed": "observation starts after 120MA rises above 20MA or 60MA, followed by three closes more than 4% above 120MA",
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
        + _h.escape(ui["en_do"] +
        (" (No condition matched; keeping the prior state.)" if "不合條件" in do else "")) + '</span>'
        '</span>'
        + stage_html +
        '<span class="mk-num">' + _h.escape(date) + '</span>'
        '</summary>'
        '<div class="mk-body">'
        + _lifecycle_html(phase) +
        '<div class="life-intro">'
        '<span class="q-zh"><b>怎麼閱讀：</b>大盤階段依收盤價、5／10／20／60／120日均線排列與乖離整理成五個位置。'
        '它不是下一站預測；階段可能跳過、退回，沒有新條件成立時會延續最近已確認階段。<br><br>'
        '目前屬於<b>' + _h.escape(ui["zh"])
        + '</b>；判定條件是：' + _h.escape(zh_rule) + '。<br><br>'
        '均線排列描述已發生的趨勢，乖離只表示收盤價離均線多遠，不能據此預測下一日漲跌。</span>'
        '<span class="q-en" style="display:none"><b>How to read it:</b> The market lifecycle '
        'uses the close and the 5/10/20/60/120-day MA alignment and distance to organize the market into five positions. '
        'It is not a forecast; stages can be skipped or reversed, and the latest confirmed stage remains until another condition is met.<br><br>The market is in '
        '<b>' + _h.escape(ui["en"]) + '</b>; this state is defined when '
        + _h.escape(en_rule) + '.<br><br>MA alignment describes an observed trend, while distance only shows how far the close sits from an MA; neither predicts the next session.</span>'
        '</div></div></details>')


def _home_market_dashboard_html():
    """首頁首屏：近期選股結果、今日市場寬度與納斯達克相對期間中位數。"""
    import html as _h
    counts = _load_cache(MARKET_COUNT_CACHE, None) or {}
    recent = (counts.get("recent_returns") or {}).get("rows") or []
    by_day = {int(r.get("days", 0)): r for r in recent}
    r20, r60 = by_day.get(20, {}), by_day.get(60, {})
    win20 = float(r20.get("win_pct") or 0)
    med20 = float(r20.get("median_return") or 0)
    med60 = float(r60.get("median_return") or 0)
    snap = get_ma_breadth_snapshot() or {}
    long_rows = [r for r in snap.get("rows", []) if int(r.get("period") or 0) in (150, 200)]
    long_breadth = (sum(float(r.get("pct") or 0) for r in long_rows) / len(long_rows)
                    if long_rows else None)
    if not r20:
        zh_badge, en_badge = "資料整理中", "Updating"
        zh, en = "近期選股資料正在更新。", "Recent stock-selection data is updating."
    elif med20 >= 7 and win20 >= 65 and med60 >= 5:
        zh_badge, en_badge = "明顯偏強", "Clearly strong"
        zh, en = "多數個股參與上漲，20日漲幅明顯，60日趨勢也維持正向。", "Participation is broad, the 20-session gain is meaningful and the 60-session trend remains positive."
    elif med20 >= 3 and win20 >= 55 and med60 >= 0:
        zh_badge, en_badge = "溫和偏強", "Moderately strong"
        zh, en = "上漲家數過半，個股中位漲幅已有強度，近期選股環境偏有利。", "More than half advanced and the median gain has meaningful strength."
    elif med20 <= -3 and win20 < 45:
        zh_badge, en_badge = "明顯偏弱", "Clearly weak"
        zh, en = "多數個股下跌且中位報酬明顯為負，近期選股難度高。", "Most stocks fell and the median return is clearly negative."
    elif -3 < med20 < 3:
        zh_badge, en_badge = "盤整偏弱", "Weak consolidation"
        zh, en = "個股20日中位報酬不足3%，整體漲幅有限，行情以區間整理為主。", "The 20-session median return is below 3%, so gains are limited and the market is range-bound."
    else:
        zh_badge, en_badge = "盤勢整理", "Consolidating"
        zh, en = "報酬強弱與上漲家數沒有同步，類股表現分化。", "Return strength and participation disagree, indicating a divided market."
    if r20 and long_breadth is not None:
        if long_breadth >= 60:
            zh += " 150／200日線寬度偏高，市場位階較高。"; en += " 150/200-day breadth indicates a higher market position."
        elif long_breadth <= 40:
            zh += " 150／200日線寬度偏低，市場仍處低位階。"; en += " 150/200-day breadth remains at a lower market position."

    def ret_row(days):
        r = by_day.get(days)
        if not r: return ""
        med = float(r.get("median_return") or 0); sign = "+" if med >= 0 else ""
        color = "#278153" if med >= 0 else "#c84335"
        return ('<div class="market-return-row"><span><span class="q-zh">過去 %d 個交易日</span><span class="q-en" style="display:none">Past %d sessions</span></span>' % (days, days)
                + '<span class="market-return-main"><b>%s</b> / %s <span class="q-zh">檔上漲</span><span class="q-en" style="display:none">advanced</span> · <b>%.1f%%</b></span>' % (r.get("winners",0),r.get("base",0),float(r.get("win_pct") or 0))
                + '<span class="market-return-med"><span class="q-zh">中位報酬</span><span class="q-en" style="display:none">Median return</span><b style="color:%s">%s%.2f%%</b></span></div>' % (color,sign,med))
    breadth_rows = ""
    labels = {50:("季線","50MA"),150:("中長期","150MA"),200:("年線","200MA")}
    for r in snap.get("rows", []):
        p=int(r.get("period") or 0)
        if p not in labels or r.get("pct") is None: continue
        above=float(r["pct"]); below=max(0,100-above); zh_l,en_l=labels[p]
        breadth_rows += ('<div class="breadth-row"><b><span class="q-zh">%s</span><span class="q-en" style="display:none">%s</span></b>' % (zh_l,en_l)
                         + '<div class="breadth-bar"><span class="breadth-above" style="width:%.1f%%"></span><span class="breadth-below" style="width:%.1f%%"></span></div><span class="breadth-num"><span class="up">%.1f%%</span> ｜ <span class="down">%.1f%%</span></span></div>' % (above,below,above,below))
    idx = _load_cache("nasdaq_index.json", None) or {}
    series = [[str(k),round(float(v),2)] for k,v in sorted(idx.items()) if v is not None][-MARKET_INDEX_KEEP:]
    encoded = _h.escape(json.dumps(series,separators=(",",":")),quote=True)
    as_of = (counts.get("recent_returns") or {}).get("as_of") or snap.get("date") or "—"
    return ('<section class="market-now"><div class="market-now-hero"><div class="market-now-title"><h1><span class="q-zh">今日市場</span><span class="q-en" style="display:none">Today’s Market</span></h1>'
            '<span class="market-now-badge"><span class="q-zh">'+zh_badge+'</span><span class="q-en" style="display:none">'+en_badge+'</span></span></div>'
            '<div class="reading-card"><div class="reading-row"><b><span class="q-zh">數據</span><span class="q-en" style="display:none">Data</span></b><span><span class="q-zh">過去 20 日中位報酬 '+('%+.2f%%' % med20)+'、上漲家數 '+('%.1f%%' % win20)+'；60 日中位報酬 '+('%+.2f%%' % med60)+'。資料截至 '+_h.escape(str(as_of))+'。</span><span class="q-en" style="display:none">20-session median '+('%+.2f%%' % med20)+', advancers '+('%.1f%%' % win20)+'; 60-session median '+('%+.2f%%' % med60)+'. Data as of '+_h.escape(str(as_of))+'.</span></span></div>'
            '<div class="reading-row"><b><span class="q-zh">解讀</span><span class="q-en" style="display:none">Reading</span></b><span><span class="q-zh">'+zh+'</span><span class="q-en" style="display:none">'+en+'</span></span></div>'
            '<div class="reading-row"><b><span class="q-zh">限制</span><span class="q-en" style="display:none">Limit</span></b><span><span class="q-zh">目前市值前 300 大的已實現收盤報酬，只描述過去選股環境，不能據此預測下一段行情。</span><span class="q-en" style="display:none">Current top 300 and realised closing returns only. This describes the past selection environment and cannot forecast the next market move.</span></span></div></div></div>'
            '<div class="market-now-grid"><div class="market-data-card"><h2><span class="q-zh">近期選股環境（回顧）</span><span class="q-en" style="display:none">Recent selection environment</span></h2>'+ret_row(20)+ret_row(60)+'</div>'
            '<div class="market-data-card"><h2><span class="q-zh">市場寬度</span><span class="q-en" style="display:none">Market breadth</span></h2>'+breadth_rows+'<div class="breadth-legend"><span><i style="background:#278153"></i><span class="q-zh">站上均線</span><span class="q-en" style="display:none">Above MA</span></span><span><i style="background:#c84335"></i><span class="q-zh">跌破均線</span><span class="q-en" style="display:none">Below MA</span></span></div></div></div>'
            '<div class="market-data-card market-chart-card"><div class="market-chart-head"><h2><span class="q-zh">納斯達克・相對期間中位數</span><span class="q-en" style="display:none">Nasdaq vs period median</span></h2><div class="market-periods"><button class="on" data-days="756">3Y</button><button data-days="252">1Y</button><button data-days="126">6M</button><button data-days="63">3M</button></div></div><div id="homeIndexChart" data-series="'+encoded+'"></div><div class="market-chart-note"><span class="q-zh">縱軸0%＝所選期間收盤中位數；只描述相對位置，不預測未來。</span><span class="q-en" style="display:none">0% is the selected period’s median close; this describes position, not the future.</span></div></div></section>')


def _lifecycle_html(phase):
    """首頁四階段市場地圖；中英文同時渲染，交由既有語言切換顯示。"""
    import html as _h

    def one(lang):
        rows = []
        for no, (key, zh, zh_hint, en, en_hint) in enumerate(MARKET_LIFECYCLE, 1):
            name, hint = (zh, zh_hint) if lang == "zh" else (en, en_hint)
            active = key == phase
            rows.append(
                '<div class="life-step' + (' on' if active else '') + '"'
                + (' aria-current="step"' if active else '') + '>'
                '<div class="life-top"><span class="life-no">' + str(no) + '</span>'
                '<span class="life-name">' + _h.escape(name) + '</span></div>'
                '<span class="life-hint">' + _h.escape(hint) + '</span>'
                + (('<span class="life-now">' + ('目前位置' if lang == "zh" else 'Current') + '</span>')
                   if active else '')
                + '</div>')
        title = "大盤生命週期" if lang == "zh" else "Market Lifecycle"
        sub = "目前位置，不是未來預測" if lang == "zh" else "Current position, not a forecast"
        note = ("階段不一定依序前進，也可能跳階或退回；請把它當作市場地圖，而不是買賣訊號。"
                if lang == "zh" else
                "Stages may be skipped or reversed. Treat this as a market map, not a trading signal.")
        return ('<div class="life-head"><b>' + title + '</b><span>' + sub + '</span></div>'
                '<div class="life-track">' + ''.join(rows) + '</div>'
                '<p class="life-note">' + note + '</p>')

    return ('<div class="q-zh">' + one("zh") + '</div>'
            '<div class="q-en" style="display:none">' + one("en") + '</div>')


def _only_page(html, keep):
    """只保留目標分頁的 `<div class="page" id="…">`，其餘整段移除。

    ⚠️⚠️ **這是這個站最重要的一項 SEO 設定。**
    九個網址如果都送出全部分頁的 HTML，Google 會看到九個內文幾乎一樣的頁面，
    判定為重複內容、只挑一個當代表，其餘八個等於白做。

    以 `<div>` 配對計數切割，不用正則硬拆巢狀結構（正則處理不了巢狀）。
    寫法與台股版完全相同 —— 兩邊要改就一起改。
    """
    out, i = [], 0
    while True:
        j = html.find('<div class="page', i)
        if j < 0:
            out.append(html[i:])
            break
        out.append(html[i:j])
        head_end = html.find(">", j)
        head = html[j:head_end + 1]
        m = re.search(r'id="(\w+)"', head)
        pid = m.group(1) if m else ""
        depth, k = 0, j
        while k < len(html):
            nd = html.find("<div", k)
            cd = html.find("</div>", k)
            if cd < 0:
                k = len(html)
                break
            if 0 <= nd < cd:
                depth += 1
                k = nd + 4
            else:
                depth -= 1
                k = cd + 6
                if depth == 0:
                    break
        if pid == keep:
            block = html[j:k]
            if 'class="page"' in head:      # 確保目標頁是顯示狀態
                block = block.replace('<div class="page"', '<div class="page show"', 1)
            out.append(block)
        i = k
    return "".join(out)


def _page_seo(slug, lang):
    """回傳 (title, description)。slug 為 None 代表首頁。"""
    cfg = PAGE_ROUTES.get(slug) if slug else None
    if cfg:
        t, d = cfg[lang]
        suffix = "｜美股咖啡館" if lang == "zh" else " | US Stock Coffee"
        return t + suffix, d
    return HOME_SEO[lang]


def _seo_head(slug, lang):
    """整個 <head> 的 SEO 區塊：title、description、canonical、hreflang、OG、JSON-LD。

    ⚠️ **canonical 與 hreflang 必須互相對應**：中文頁指到英文頁、英文頁也要指回中文頁，
       否則 Search Console 會報「沒有回傳連結」而整組忽略。
    ⚠️ 英文版是**參數**（`?lang=en`）不是路徑，沒有 `/en/screener` 這種網址。
    """
    import html as _h
    title, desc = _page_seo(slug, lang)
    path = "/" + slug if slug else "/"
    zh_url, en_url = SITE_URL + path, SITE_URL + path + "?lang=en"
    canon = en_url if lang == "en" else zh_url
    noindex = bool(slug) and not PAGE_ROUTES[slug]["index"]

    ld = {"@context": "https://schema.org", "@type": "WebApplication",
          "name": "US Stock Coffee", "url": SITE_URL,
          "applicationCategory": "FinanceApplication",
          "operatingSystem": "Any", "inLanguage": ["zh-Hant-TW", "en"],
          "isAccessibleForFree": True,
          "description": _page_seo(None, "zh")[1],
          "offers": {"@type": "Offer", "price": "0", "priceCurrency": "USD"},
          "publisher": {"@type": "Organization", "name": "美股咖啡館 US Stock Coffee",
                        "url": SITE_URL, "logo": SITE_URL + "/icon.png"}}

    e = _h.escape
    lines = [
        "<title>" + e(title) + "</title>",
        '<meta name="description" content="' + e(desc) + '">',
        '<meta name="google-adsense-account" content="ca-pub-4558422800482658">',
        '<link rel="canonical" href="' + e(canon) + '">',
        '<link rel="alternate" hreflang="zh-Hant" href="' + e(zh_url) + '">',
        '<link rel="alternate" hreflang="en" href="' + e(en_url) + '">',
        '<link rel="alternate" hreflang="x-default" href="' + e(zh_url) + '">',
        '<meta name="robots" content="' +
        ("noindex,follow" if noindex else "index,follow,max-image-preview:large") + '">',
        '<meta property="og:type" content="website">',
        '<meta property="og:site_name" content="美股咖啡館 US Stock Coffee">',
        '<meta property="og:title" content="' + e(title) + '">',
        '<meta property="og:description" content="' + e(desc) + '">',
        '<meta property="og:url" content="' + e(canon) + '">',
        '<meta property="og:image" content="' + SITE_URL + '/icon.png">',
        '<meta property="og:locale" content="' +
        ("zh_TW" if lang == "zh" else "en_US") + '">',
        '<meta name="twitter:card" content="summary">',
        '<meta name="twitter:title" content="' + e(title) + '">',
        '<meta name="twitter:description" content="' + e(desc) + '">',
        '<script type="application/ld+json">'
        + json.dumps(ld, ensure_ascii=False) + '</script>',
    ]
    return "\n".join(lines)


def _render(slug=None):
    """送出頁面。slug 為 None 代表首頁。

    ⚠️ **每個網址只送自己那一頁**（`_only_page`），而且 head 是伺服器端注入的 ——
       爬蟲不執行 JS 也讀得到正確的 title 與 canonical。
    """
    start_page = PAGE_ROUTES[slug]["page"] if slug else "home"
    lang = "en" if request.args.get("lang") == "en" else "zh"
    title_zh, _ = _page_seo(slug, "zh")
    title_en, _ = _page_seo(slug, "en")

    html = PAGE.replace("__APP_TOKEN__", make_app_token())
    html = html.replace("__START_PAGE__", start_page, 1)
    html = html.replace("__TW_URL__", TW_URL)
    html = html.replace("__HOME_MARKET_DASHBOARD__", _home_market_dashboard_html())
    html = html.replace("__PHASE_BAR__", _phase_banner_html())
    html = html.replace("__UPDATE_NOTE__", _update_note_html())
    html = html.replace("__FED_POLICY_PANEL__", _fed_policy_panel_html())
    html = html.replace("__HOME_SCREEN__", _home_screen_html())
    html = html.replace("__HOME_INDUSTRY_BRIEF__", _home_industry_brief_html())
    html = html.replace("__BUILD_INFO__", _build_badge_html())
    # ⚠️ 只放**公開**金鑰。VAPID_PRIVATE 絕對不能出現在頁面上。
    html = html.replace("__VAPID_PUBLIC__", VAPID_PUBLIC)
    # ⚠️ 中英兩份都送出，用 q-zh／q-en 包起來讓 applyLang() 能即時切換。
    #    只送當前語言的話，使用者在頁面上按語言鈕時文章清單不會跟著換
    #    （applyLang 是純前端，不會回頭跟伺服器要資料）。
    html = html.replace("__ART_LINKS__",
                        _art_links_html("zh") + _art_links_html("en"))
    html = html.replace("__QUOTES_HTML__", _quotes_html())
    import html as _hq
    _src = "<br>".join(_hq.escape(x) for x in QUOTE_SOURCES)
    _src_en = "<br>".join(_hq.escape(x) for x in (QUOTE_SOURCES_EN or QUOTE_SOURCES))
    html = html.replace(
        "__QUOTE_SRC__",
        '<span class="q-zh">' + (_src + "<br>" if _src else "") + '每日更新兩則輪替</span>'
        '<span class="q-en" style="display:none">'
        + (_src_en + "<br>" if _src_en else "") + 'Two quotes daily, on rotation</span>')
    html = html.replace("__SEO_HEAD__", _seo_head(slug, lang), 1)
    # ⚠️ 這兩個是 JS 字串常值，必須跳脫雙引號，否則標題含 " 就會把 <script> 打斷。
    html = html.replace("__TITLE_ZH__", title_zh.replace('"', '\\"'), 1)
    html = html.replace("__TITLE_EN__", title_en.replace('"', '\\"'), 1)
    if lang == "en":
        html = html.replace('<html lang="zh-Hant-TW">', '<html lang="en">', 1)
    html = _only_page(html, start_page)     # ⭐ 每個網址只送出自己那一頁
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
    idx_series = []
    idx_median = None
    idx_high = None
    idx_low = None
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

        # 近三年大盤走勢以「這段期間的指數中位數」為 0%。這不是報酬率，
        # 而是讓使用者直接看每一天位於三年價格分布的上方或下方多少。
        chart_days = ids[-MARKET_INDEX_KEEP:]
        chart_vals = [float(idx[d]) for d in chart_days]
        if chart_vals:
            ordered = sorted(chart_vals)
            n = len(ordered)
            idx_median = (ordered[n // 2] if n % 2 else
                          (ordered[n // 2 - 1] + ordered[n // 2]) / 2.0)
            idx_high = max(chart_vals)
            idx_low = min(chart_vals)
            idx_series = [[d, round(float(idx[d]), 2),
                           round((float(idx[d]) / idx_median - 1) * 100, 2)]
                          for d in chart_days]
    except Exception:
        idx_out = None            # ⚠️ 指數讀不到不能影響寬度那半邊
        idx_series = []

    return jsonify(
        idx=idx_out,
        market_series=idx_series,
        market_median=round(idx_median, 2) if idx_median is not None else None,
        market_high=round(idx_high, 2) if idx_high is not None else None,
        market_low=round(idx_low, 2) if idx_low is not None else None,
        market_span_years=3,
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
        # 今日快照：站上 50／150／200MA 的家數 ＋ 創 60 日新高家數
        # ⚠️ 一樣只讀快取，不重算（見上面的原則）。
        snapshot=get_ma_breadth_snapshot(),
        market_counts=_load_cache(MARKET_COUNT_CACHE, 24 * 365) or {},
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


def _same_period_comparison(anchor, peers, requested_date, buy_price, shares, lang="zh"):
    """同本金同期比較。歷史快取為拆股一致口徑，個人輸入不保存到伺服器。"""
    def msg(zh, en):
        return en if lang == "en" else zh

    universe = _load_cache("universe.json", None) or []
    info = {str(u.get("symbol") or "").upper(): u for u in universe[:300]
            if u.get("symbol")}
    codes = [anchor] + peers
    missing = [c for c in codes if c not in info]
    if missing:
        raise ValueError(msg("僅限目前市值前 300 大股票：", "Limited to the current top 300: ")
                         + ", ".join(missing))

    histories = {}
    for c in codes:
        rows = get_history(c) or []
        histories[c] = {str(d): float(v) for d, v in rows if d and v is not None}
    missing = [c for c in codes if len(histories[c]) < 2]
    if missing:
        raise ValueError(msg("這些股票的歷史收盤不足：", "Insufficient history for: ")
                         + ", ".join(missing))

    common = None
    for c in codes:
        dates = set(histories[c])
        common = dates if common is None else common.intersection(dates)
    common = sorted(common or [])
    usable = [d for d in common if d >= requested_date]
    if len(usable) < 2:
        earliest = max(min(histories[c]) for c in codes)
        latest = min(max(histories[c]) for c in codes)
        raise ValueError(msg("買入日超出可比較範圍（目前共同資料 %s～%s）",
                             "Purchase date is outside the common range (%s to %s)")
                         % (earliest, latest))
    entry_date, as_of = usable[0], usable[-1]
    if entry_date >= as_of:
        raise ValueError(msg("買入日後尚無足夠收盤資料可比較",
                             "Not enough closes after the purchase date"))

    principal = float(buy_price) * float(shares)
    # Nasdaq 歷史序列會回頭調整拆股前價格。使用者輸入的卻是當時實際成交價與原股數，
    # 所以當「實際價 / 還原收盤」接近常見拆股倍數時，要同步放大目前股數。
    adjusted_close = histories[anchor][entry_date]
    observed = float(buy_price) / adjusted_close if adjusted_close > 0 else 1.0
    split_factor = 1.0
    split_factors = list(SPLIT_RATIOS) + [1.0 / float(r) for r in SPLIT_RATIOS]
    for factor in split_factors:
        if abs(observed / factor - 1) <= 0.18:
            split_factor = float(factor)
            break
    current_shares = float(shares) * split_factor
    a_last = histories[anchor][as_of]
    a_value = current_shares * a_last
    a_return = (a_value / principal - 1) * 100

    def names(c):
        u = info[c]
        raw = u.get("name") or c
        return raw, zh_company(c, raw)

    name, name_zh = names(anchor)
    rows = [{
        "role": "A", "code": anchor, "name": name, "name_zh": name_zh,
        "entry_price": round(float(buy_price), 4), "shares": round(current_shares, 6),
        "original_shares": round(float(shares), 6), "split_factor": split_factor,
        "cash": 0.0, "last_price": round(a_last, 4), "last_date": as_of,
        "current_value": round(a_value, 2), "return_pct": round(a_return, 4),
        "difference_vs_a": 0.0,
    }]
    for i, c in enumerate(peers):
        start, last = histories[c][entry_date], histories[c][as_of]
        qty = math.floor(principal / start)
        cash = principal - qty * start
        value = qty * last + cash
        name, name_zh = names(c)
        rows.append({
            "role": "BCD"[i], "code": c, "name": name, "name_zh": name_zh,
            "entry_price": round(start, 4), "shares": int(qty),
            "original_shares": int(qty), "split_factor": 1.0,
            "cash": round(cash, 2), "last_price": round(last, 4), "last_date": as_of,
            "current_value": round(value, 2),
            "return_pct": round((value / principal - 1) * 100, 4),
            "difference_vs_a": round(value - a_value, 2),
        })
    return {"requested_date": requested_date, "entry_date": entry_date, "as_of": as_of,
            "currency": "USD", "principal": round(principal, 2), "rows": rows,
            "price_return_only": True, "whole_share_peers": True}


@app.route("/api/comparison", methods=["POST"])
def api_comparison():
    if not _valid_app_token(request.headers.get("X-App-Token")):
        return jsonify(error="連線憑證已過期，請重新整理頁面"), 403
    p = request.get_json(silent=True) or {}
    lang = "en" if p.get("lang") == "en" else "zh"
    msg = (lambda zh, en: en if lang == "en" else zh)
    anchor = str(p.get("anchor") or "").strip().upper()
    peers = [str(x).strip().upper() for x in (p.get("peers") or []) if str(x).strip()]
    peers = list(dict.fromkeys(peers))
    try:
        buy_price, shares = float(p.get("buy_price")), float(p.get("shares"))
        requested = datetime.strptime(str(p.get("date") or ""), "%Y-%m-%d").date()
    except (TypeError, ValueError):
        return jsonify(error=msg("請輸入正確的買入日期、價格與股數",
                                 "Enter a valid purchase date, price and share count")), 400
    if not anchor or not peers:
        return jsonify(error=msg("請選擇 A 股票與至少一檔比較股票",
                                 "Choose stock A and at least one comparison stock")), 400
    if len(peers) > 3 or anchor in peers:
        return jsonify(error=msg("B／C／D 最多 3 檔，且不可與 A 重複",
                                 "B/C/D allow up to 3 unique stocks and cannot repeat A")), 400
    if buy_price <= 0 or shares <= 0:
        return jsonify(error=msg("買入價與股數必須大於 0",
                                 "Purchase price and shares must be greater than zero")), 400
    if requested > _utcnow().date():
        return jsonify(error=msg("買入日期不能晚於今天", "Purchase date cannot be in the future")), 400
    try:
        return jsonify(_same_period_comparison(anchor, peers, requested.isoformat(),
                                               buy_price, shares, lang))
    except ValueError as e:
        return jsonify(error=str(e)), 400
    except Exception as e:
        return jsonify(error=msg("同期比較計算失敗：", "Comparison failed: ") + str(e)[:80]), 500


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


@app.route("/api/quote-more")
def api_quote_more():
    """再抽一張：從尚未出現過的名言中隨機挑一張，回傳渲染好的卡片 HTML。

    ⚠️⚠️ **抽卡範圍要跟著今天的市場階段**，只限「當前階段 ＋ 通用」。
       全庫隨機的話，逆風盤可能抽到「順勢而為」「持有贏家」，
       跟上方的市場階段直接打架 —— 首頁好不容易建立的一致性會破功。
    ⚠️ 池子一律用**中文**名言算索引（英文檔的主題是英文），否則中英會抽到不同卡。
    """
    if not _valid_app_token(request.headers.get("X-App-Token")):
        return jsonify(error="連線憑證已過期，請重新整理頁面"), 403
    import random
    seen = set()
    for x in (request.args.get("seen", "") or "").split(","):
        x = x.strip()
        if x.isdigit():
            seen.add(int(x))
    lang = "en" if request.args.get("lang") == "en" else "zh"
    cards, _ = _quote_set(lang)
    try:
        phase, _s, _d, _b = market_phase_cached()
    except Exception:
        phase = ""
    tags = list(REGIME_TAGS.get(phase or "", [])) + list(GENERIC_TAGS)
    pool = [i for i, c in enumerate(QUOTES)
            if c[1] in tags and i < len(cards) and (i + 1) not in seen]
    if not pool:                       # 這個階段抽完了，不再往全庫擴散
        return jsonify(done=True)
    idx = random.choice(pool)
    author, tag, lines = cards[idx]
    q = {"author": author, "tag": tag, "lines": lines,
         "no": idx + 1, "total": len(cards)}
    return jsonify(html=_quote_card_html(q, extra=True), no=q["no"],
                   remain=len(pool) - 1)


@app.route("/api/deduct", methods=["POST"])
def api_deduct():
    """均線扣抵法：50MA／150MA 要幾個交易日才追得上指定價位。

    ⚠️ **只讀既有快取，不連網。** 指數讀 `nasdaq_index.json`、
       個股讀既有的 `hist_` —— 這頁是使用者一按就跑的，不能觸發外部請求。
    ⚠️ 盤整與延續趨勢**兩種假設一起回**：單一數字會被當成預測。
    """
    if not _valid_app_token(request.headers.get("X-App-Token")):
        return jsonify(error="連線憑證已過期，請重新整理頁面"), 403
    p = request.get_json(silent=True) or {}
    sym = str(p.get("code") or "").strip().upper()
    try:
        price = float(p.get("price")) if p.get("price") not in (None, "") else None
    except (TypeError, ValueError):
        return jsonify(error="價格格式錯誤"), 400
    if price is not None and price <= 0:
        return jsonify(error="價格要大於 0"), 400

    name, closes = "", []
    if not sym or sym in ("COMP", "IXIC", "INDEX", "NASDAQ"):
        sym, name = "COMP", "納斯達克綜合指數"
        idx = _load_cache("nasdaq_index.json", 24 * 365) or {}
        closes = [idx[d] for d in sorted(idx)][-400:]
    else:
        closes = [c for _d, c in (get_history(sym) or [])]
        for u in (_load_cache("universe.json", None) or []):
            if u.get("symbol") == sym:
                name = u.get("name") or sym
                break
    if len(closes) < max(DEDUCT_MAS):
        return jsonify(error="這檔的歷史收盤不足 %d 個交易日，算不出 %dMA 扣抵"
                             % (max(DEDUCT_MAS), max(DEDUCT_MAS))), 400

    last = float(closes[-1])
    target = price if price is not None else last
    slope = _recent_slope(closes)
    return jsonify(
        code=sym, name=name or sym, name_zh=(name if sym == "COMP"
                                             else zh_company(sym, name or sym)),
        last=round(last, 2), target=round(target, 2), custom_price=price is not None,
        slope_pct=round(slope * 100, 3), slope_lookback=DEDUCT_SLOPE_LOOKBACK,
        flat=_ma_deduction(closes, target, daily_change=0.0),
        trend=_ma_deduction(closes, target, daily_change=slope),
        mas=list(DEDUCT_MAS), max_days=DEDUCT_MAX_DAYS)


@app.route("/api/risk", methods=["POST"])
def api_risk():
    """風控頁：一次算最多 3 檔的 ATR／波動率／均線趨勢／Beta。

    ⚠️ 會連網抓 OHLC（每檔 12 小時快取一次），所以**必須限制檔數**。
       上限 3 檔與台股版一致 —— 這不是效能考量而已，
       風控本來就該只放在你真的持有的部位上。
    """
    if not _valid_app_token(request.headers.get("X-App-Token")):
        return jsonify(error="連線憑證已過期，請重新整理頁面"), 403
    p = request.get_json(silent=True) or {}
    syms = [str(x).upper().strip() for x in (p.get("symbols") or []) if str(x).strip()]
    syms = list(dict.fromkeys(syms))            # 去重、保順序
    if not syms:
        return jsonify(rows=[])
    if len(syms) > RISK_MAX:
        return jsonify(error="最多只能同時看 %d 檔" % RISK_MAX), 400
    try:
        return jsonify(rows=risk_metrics(syms), atr_period=RISK_ATR_PERIOD,
                       vol_sessions=RISK_VOL_SESSIONS,
                       beta_sessions=RISK_BETA_SESSIONS)
    except Exception as e:
        return jsonify(error="風控資料計算失敗：%s" % str(e)[:80]), 500


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
    /* ⚠️⚠️ 這是 Cache API 的**鍵**，不是網頁。
       但 Googlebot 執行 JS 時會把字串當成網址去抓 ——
       台股版 2026-08-07 就被 Search Console 報了 `/__unread` 404。
       移到 `/api/` 底下，robots.txt 的 `Disallow: /api/` 就會擋住。
       📌 404 本身不影響排名，這純粹是把報表清乾淨。 */
    const prev = await cache.match('/api/__us_badge');
    let count = prev ? parseInt(await prev.text(), 10) || 0 : 0;
    count += 1;
    await cache.put('/api/__us_badge', new Response(String(count)));
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
    return _render(None)


# ⚠️ 路由名要把 "/" 換掉（"pro/rs"），Flask 的 endpoint 名不能含斜線。
for _slug in PAGE_ROUTES:
    app.add_url_rule("/" + _slug, "page_" + _slug.replace("/", "_"),
                     (lambda s=_slug: (lambda: _render(s)))())


@app.route("/robots.txt")
def robots_txt():
    """檢索規則。API、Service Worker 與診斷端點不需要被收錄。

    ⚠️ 不要擋 AI 爬蟲 —— 這個站的流量有一部分會從那裡來（台股版同一個決定）。
    """
    body = ("User-agent: *\n"
            "Allow: /\n"
            "Disallow: /api/\n"
            "Disallow: /sw.js\n"
            "\n"
            "Sitemap: " + SITE_URL + "/sitemap.xml\n")
    return app.response_class(body, mimetype="text/plain")


@app.route("/ads.txt")
def ads_txt():
    """AdSense 授權賣方宣告；由網站根目錄直接回傳純文字。"""
    return app.response_class(
        "google.com, pub-4558422800482658, DIRECT, f08c47fec0942fa0\\n",
        mimetype="text/plain")


@app.route("/sitemap.xml")
def sitemap_xml():
    """動態產生 sitemap：首頁、可索引功能頁、文章與隱私權政策。

    ⚠️ `index: False` 的頁面不放進來 —— 送 noindex 又列進 sitemap 是自相矛盾的訊號。
    ⚠️ hreflang 必須**互相對應**（每個網址都列出全部語言版本，含自己），
       否則 Search Console 會報「沒有回傳連結」而整組忽略。
    """
    import html as _h
    today = _utcnow().strftime("%Y-%m-%d")

    def url(loc, lastmod, prio, changefreq, alts=()):
        x = ["  <url>", "    <loc>" + _h.escape(loc) + "</loc>"]
        for hl, href in alts:
            x.append('    <xhtml:link rel="alternate" hreflang="' + hl
                     + '" href="' + _h.escape(href) + '"/>')
        x.append("    <lastmod>" + lastmod + "</lastmod>")
        x.append("    <changefreq>" + changefreq + "</changefreq>")
        x.append("    <priority>" + prio + "</priority>")
        x.append("  </url>")
        return "\n".join(x)

    def pair(loc):
        return [("zh-Hant", loc), ("en", loc + "?lang=en"), ("x-default", loc)]

    parts = ['<?xml version="1.0" encoding="UTF-8"?>',
             '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9"'
             ' xmlns:xhtml="http://www.w3.org/1999/xhtml">']
    parts.append(url(SITE_URL + "/", today, "1.0", "daily", pair(SITE_URL + "/")))
    # 隱私權政策為獨立公開頁；目前沒有真正的英文版，不列 hreflang 以免送出重複內容。
    parts.append(url(SITE_URL + "/privacy", today, "0.3", "yearly"))
    for slug, cfg in PAGE_ROUTES.items():
        if not cfg["index"] or slug == "articles":
            continue
        loc = SITE_URL + "/" + slug
        parts.append(url(loc, today, "0.9", "weekly", pair(loc)))
    arts = _load_articles()
    en_dir = os.path.join(ARTICLES_DIR, "en")
    # 英文版必須每篇都實際存在才建立整組 hreflang；半套翻譯不能送進 sitemap。
    has_en = bool(arts) and os.path.isdir(en_dir) and all(
        os.path.isfile(os.path.join(en_dir, a["id"] + ".md")) for a in arts)
    if arts:
        loc = SITE_URL + "/articles"
        # 英文文章索引沿用 App 的參數網址；`/en/articles` 會 301 到這個正式網址。
        eloc_list = SITE_URL + "/articles?lang=en"
        list_alts = [("zh-Hant", loc), ("x-default", loc)]
        if has_en:
            list_alts.insert(1, ("en", eloc_list))
        parts.append(url(loc, today, "0.8", "weekly", list_alts))
        if has_en:
            parts.append(url(eloc_list, today, "0.6", "weekly", list_alts))
        for a in arts:
            aloc = SITE_URL + "/article/" + quote(a["slug"])
            if has_en:
                eloc = SITE_URL + "/en/article/" + quote(a["slug"])
                alts = [("zh-Hant", aloc), ("en", eloc), ("x-default", aloc)]
                parts.append(url(aloc, a.get("date") or today, "0.7", "monthly", alts))
                parts.append(url(eloc, a.get("date") or today, "0.6", "monthly", alts))
            else:
                parts.append(url(aloc, a.get("date") or today, "0.7", "monthly",
                                 [("zh-Hant", aloc), ("x-default", aloc)]))
    parts.append("</urlset>")
    return app.response_class("\n".join(parts), mimetype="application/xml")


@app.route("/privacy")
def privacy():
    """公開的隱私權政策，讓使用者與 AdSense 審查都能直接查閱。"""
    return render_template_string(PRIVACY_PAGE)


PRIVACY_PAGE = r"""<!doctype html><html lang="zh-Hant-TW"><head>
<meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<title>隱私權政策｜美股咖啡館 US Stock Coffee</title>
<meta name="description" content="美股咖啡館的隱私權、Cookie、推播資料與投資免責聲明。">
<link rel="canonical" href="https://us.stock-coffee.com/privacy"><meta name="robots" content="index,follow">
<meta name="google-adsense-account" content="ca-pub-4558422800482658">
<style>:root{--milk:#f1ead9;--foam:#fbf6ec;--grounds:#e4d7c1;--espresso:#33241a;--caramel:#a56c24}*{box-sizing:border-box}html{min-height:100%;background:var(--milk);overscroll-behavior-y:none}body{margin:0;min-height:100vh;min-height:100dvh;background:var(--milk);color:var(--espresso);font-family:-apple-system,BlinkMacSystemFont,"PingFang TC","Noto Sans TC",sans-serif;line-height:1.9;overflow-x:clip;overscroll-behavior-y:none}main{max-width:760px;margin:auto;padding:28px 20px calc(56px + env(safe-area-inset-bottom))}.top{background:var(--espresso);padding:13px 20px}.top a{color:var(--foam);text-decoration:none;font-weight:800}h1{font-size:29px;line-height:1.45}h2{font-size:19px;margin:30px 0 8px;color:var(--caramel)}p,li{font-size:16px}a{color:var(--caramel);font-weight:700}.note{padding:12px 15px;border-radius:10px;background:var(--foam);border:1px solid var(--grounds)}.updated{color:#6b5540;font-size:13px}</style>
</head><body><div class="top"><a href="/">☕ 美股咖啡館 US Stock Coffee</a></div><main>
<h1>隱私權政策 / Privacy Policy</h1><p class="updated">最後更新：2026 年 8 月 20 日</p>
<p class="note">美股咖啡館提供公開市場資料整理、選股與試算工具。本站不要求建立帳號，並以最少必要資料為原則。</p>
<h2>一、我們處理的資料</h2><p>你在績效試算、觀察清單等工具輸入的內容，原則上儲存在你的瀏覽器裝置中（例如 localStorage），不會因使用這些工具自動傳送給本站。若你主動啟用到價推播，推播訂閱識別碼、股票代號與目標價格會儲存於伺服器，僅用來發送你要求的通知；你可隨時在網站中刪除提醒。</p>
<h2>二、Cookie、廣告與第三方服務</h2><p>本站可能使用 Google AdSense 顯示廣告。Google 與其他第三方廣告供應商可能使用 Cookie 或類似技術，依你造訪本站或其他網站的紀錄提供及衡量廣告。你可在 <a href="https://adssettings.google.com/" rel="noopener noreferrer">Google 廣告設定</a> 管理個人化廣告，並可參閱 <a href="https://policies.google.com/technologies/partner-sites" rel="noopener noreferrer">Google 如何使用合作夥伴網站資料</a>。</p><p>依法需要取得同意的地區，本站將透過適用的同意管理機制提供 Cookie 與個人化廣告選擇。</p>
<h2>三、資料來源與用途</h2><p>股價、公司基本面與總體資料取自公開市場資料與第三方資料服務，僅用於呈現網站功能與維護服務。我們不販售你的個人資料，也不會將推播資料用於行銷目的。</p>
<h2>四、投資免責聲明</h2><p>本站的篩選條件、技術指標、財務數字與文章均為資料整理及教育用途，<strong>不構成投資建議、招攬或保證報酬</strong>。市場投資有風險，請依自己的判斷、投資經驗與風險承受度作出決定。</p>
<h2>五、聯絡與資料刪除</h2><p>如需協助刪除推播提醒，或對本政策有問題，請來信：<a href="mailto:seer51000@gmail.com">seer51000@gmail.com</a>。</p>
<p><a href="/">← 回到美股咖啡館</a></p></main></body></html>"""


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
    w("  程式版本       : %s" % APP_VERSION)
    w("  commit / branch: %s / %s" % (BUILD_COMMIT, BUILD_BRANCH))
    w("  本次服務啟動    : %s" % BUILD_STARTED_AT)
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

    w("\n【最近 30 次資料更新】—— 由新到舊，跨部署保留")
    _history = _load_cache(UPDATE_HISTORY_FILE, None) or []
    if not _history:
        w("  尚無紀錄（新版本部署後第一次實際抓取才會寫入）")
    for _row in reversed(_history[-UPDATE_HISTORY_LIMIT:]):
        w("  %(executed_at)s | %(source)s | 最新 %(latest_date)s | %(result)s | %(duration_sec)s 秒" % _row)
        if _row.get("detail"):
            w("    ↳ %s" % _row["detail"])

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
        w("  規則            : 5／10／20／60／120MA 排列；乖離條件連續 %d 日確認"
          % PHASE_CONFIRM_DAYS)
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
    w("  開始嘗試時間     : 每個美東交易日 %02d:00 ET（收盤後 %d 小時）"
      % (UPDATE_HOUR_ET, UPDATE_HOUR_ET - 16))
    w("  探測策略        : 每 %d 分鐘用 %s 探一次，直到當日收盤出現並完成全量更新"
      % (UPDATE_RETRY_MINUTES, PROBE_SYMBOL))
    w("  下次更新        : %s" % SCHED_STATE["next_run"])
    w("  上次探測        : %s" % SCHED_STATE.get("probe", "—"))
    if SCHED_STATE.get("probe_error"):
        w("  ⚠️ 探測錯誤     : %s" % SCHED_STATE["probe_error"])
    w("  上次更新        : %s" % SCHED_STATE["last_run"])
    w("  上次結果        : %s" % SCHED_STATE["last_result"])
    w("  完成資料日     : %s" % (SCHED_STATE.get("completed_session") or "—"))
    w("  完成美東時間   : %s" % (SCHED_STATE.get("completed_at_et") or "—"))
    # 「成功」現在同時要求探測來源已到目標日；未到會明確顯示「來源延遲」。
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
        # ⚠️ 拆股護欄：只印「觀察到的事實」，不要替讀的人斷定是拆股還是崩盤（見 5.13）。
        if SPLIT_NOTES:
            w("  價格斷層        : %d 檔" % len(SPLIT_NOTES))
            for _k, _v in sorted(SPLIT_NOTES.items())[:8]:
                w("      %-18s %s" % (_k.replace("hist_", "").replace(".json", ""), _v))
        else:
            w("  價格斷層        : 無（沒有偵測到疑似拆股的價格跳動）")
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
        "eps_halves": bool(p.get("eps_halves")),
        "valuation": bool(p.get("valuation")),
        "structure_history": bool(p.get("structure_history")),
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
        "eps_halves": bool(p.get("eps_halves")),
        "valuation": bool(p.get("valuation")),
        "structure_history": bool(p.get("structure_history")),
    }
    if params["universe_n"] not in (150, 300):
        return jsonify(error="股票範圍不支援"), 400
    if params["ma"] not in MA_SET:
        return jsonify(error="均線週期不支援"), 400
    if params["align"] not in ALIGN_NAMES:
        return jsonify(error="均線排列條件不支援"), 400
    return jsonify(job=start_job(screen_pullback, params))


@app.route("/api/leverage", methods=["POST"])
def api_leverage():
    """QLD 逐月績效。⚠️ 只抓月資料、不跑篩選，所以直接回結果、不用背景工作。"""
    if not _valid_app_token(request.headers.get("X-App-Token")):
        return jsonify(error="連線憑證已過期，請重新整理頁面"), 403
    try:
        data = get_leverage_monthly()
    except Exception as e:
        return jsonify(error=str(e)), 500
    if not data.get("rows"):
        # ⚠️ 沒資料時說「在準備」並回 200，不要回 500 —— 後者看起來像壞掉。
        #    （雖然這裡只打 1 次 Nasdaq，風險比台股的 28 次低很多，
        #      但回應語意要一致，見 PROJECT_CONTEXT「外部 API 不能掛在請求上」。）
        return jsonify(pending=True, error="資料準備中，請稍後重新整理")
    return jsonify(data)


# ⚠️ 舊路由保留回 410，讓還開著舊頁面的瀏覽器拿到明確答案，而不是 404 或靜默失敗。
@app.route("/api/consolidation", methods=["POST"])
def api_consolidation_gone():
    return jsonify(error="此功能已由『正2 逐月績效』取代"), 410


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
    return jsonify(job=start_job(screen_pro_rs, {
        "period": period, "threshold": threshold,
        "structure_history": bool(p.get("structure_history"))}))


@app.route("/api/growth")
def api_growth():
    """長期成長股列表。公開唯讀，資料隨程式部署（見 `get_growth`）。"""
    d = get_growth()
    if d.get("error"):
        return jsonify(error=d["error"]), 503
    return jsonify(d)


@app.route("/api/industries")
def api_industries():
    """產業強弱排名、四象限與 Sector 領先股；只讀背景快取。"""
    data = get_industry_analysis()
    if not data.get("industries"):
        return jsonify(ok=False, error="產業分析正在背景建立中"), 503
    return jsonify(ok=True, **data)


@app.route("/api/macro")
def api_macro():
    """美國公債殖利率與累積 CPI；落後超過一個平日時每小時重試。"""
    try:
        return jsonify(_us_rate_inflation_data())
    except Exception as exc:
        return jsonify(error=str(exc), items=[]), 503


@app.route("/api/fed-policy")
def api_fed_policy():
    """聯準會與財政部官方資料快照；公開唯讀且不在請求中連外。"""
    data = _load_cache(FED_POLICY_CACHE_FILE, None) or {}
    if not data:
        return jsonify(pending=True, error="官方政策資料正在背景整理"), 202
    return jsonify(data)


@app.route("/api/market-years")
def api_market_years():
    """我的績效：納斯達克綜合指數最近兩年報酬與同期 CPI。"""
    try:
        daily = get_nasdaq_index()
        points = sorted((date, float(value)) for date, value in daily.items())
        if not points:
            raise ValueError("查無納斯達克綜合指數資料")
        latest_year = int(points[-1][0][:4])
        years = [latest_year - 1, latest_year]
        month_end = {}
        for date, value in points:
            month_end[date[:7]] = (date, value)
        cpi = _us_cpi_for_years(years)
        output = []
        for year in years:
            prev = month_end.get("%04d-12" % (year - 1))
            monthly, prior = [], prev
            for month in range(1, 13):
                current = month_end.get("%04d-%02d" % (year, month))
                if current and prior:
                    monthly.append({"month": month,
                                    "return": round((current[1] / prior[1] - 1) * 100, 2)})
                if current:
                    prior = current
            year_points = [point for key, point in month_end.items()
                           if key.startswith("%04d-" % year)]
            if not prev or not year_points:
                continue
            last = year_points[-1]
            c = cpi.get(str(year), {})
            output.append({"year": year, "monthly": monthly,
                           "annual_return": round((last[1] / prev[1] - 1) * 100, 2),
                           "cpi": c.get("value"), "cpi_period": c.get("period"),
                           "cpi_full_year": c.get("full_year", False)})
        return jsonify(years=output, index="Nasdaq Composite")
    except Exception as exc:
        return jsonify(error=str(exc), years=[]), 503


@app.route("/api/job/<job_id>")
def api_job(job_id):
    j = JOBS.get(job_id)
    if not j:
        return jsonify(error="查無此工作"), 404
    return jsonify(j)


@app.route("/api/data-health")
def api_data_health():
    """前端與維運共用的唯讀資料健康端點。"""
    return jsonify(_data_health_snapshot())


@app.route("/healthz")
def healthz():
    """Render 與 CI 使用的輕量存活檢查；不連外、不啟動資料抓取。"""
    return jsonify(status="ok", build=_build_info())


@app.route("/api/version")
def api_version():
    return jsonify(_build_info())


@app.route("/api/prefetch-status")
def api_prefetch_status():
    st = dict(PREFETCH_STATE)
    st["build"] = _build_info()
    st["health"] = _data_health_snapshot()
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
    st["macro_schedule"] = dict(MACRO_STATE)
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
            try:
                t3 = threading.Thread(target=_macro_updater, name="macro-updater", daemon=True)
                t3.start()
                MACRO_STATE["thread_started"] = True
            except Exception as e:
                MACRO_STATE["last_result"] = "排程啟動失敗：%s" % str(e)[:100]


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
