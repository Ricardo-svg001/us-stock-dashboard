import inspect
import json
import os
import pathlib
import time
import unittest
from datetime import date

os.environ.setdefault("CACHE_DIR", "/tmp/stock-coffee-contract-test")
os.environ.setdefault("ENABLE_PREFETCH", "0")
os.environ.setdefault("ENABLE_DAILY_UPDATE", "0")

import app


class SharedDataContractTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        contract_path = pathlib.Path(__file__).resolve().parents[1] / "data_contract.json"
        cls.contract = json.loads(contract_path.read_text(encoding="utf-8"))

    def test_sources_match_shared_contract(self):
        sources = self.contract["sources"]
        self.assertEqual(app.TREASURY_XML, sources["us_treasury"]["url"])
        self.assertEqual(app.JGB_DAILY_CSV, sources["jgb_daily"]["url"])
        self.assertEqual(app.JGB_HISTORY_CSV, sources["jgb_history"]["url"])
        fn = getattr(app, "_jgb_yield_series_raw", None) or app._jgb_yields_raw
        source = inspect.getsource(fn)
        self.assertIn("JGB_DAILY_CSV", source)
        self.assertIn("JGB_HISTORY_CSV", source)
        self.assertLess(source.index("JGB_HISTORY_CSV"), source.index("JGB_DAILY_CSV"))

    def test_lag_calendar_and_status_contract(self):
        self.assertEqual(app.MAX_BOND_LAG_DAYS, 1)
        self.assertEqual(self.contract["allowed_lag_business_days"],
                         {"us_yields": app.MAX_BOND_LAG_DAYS,
                          "jp_yields": app.MAX_BOND_LAG_DAYS})
        self.assertEqual(app.HOLIDAY_CALENDAR_SPEC, self.contract["holiday_calendars"])
        self.assertEqual(app.QUALITY_STATUS_ZH, self.contract["quality_statuses_zh"])
        self.assertIn(date(2026, 4, 3), app._market_holidays("us", [2026]))
        self.assertIn(date(2026, 2, 11), app._market_holidays("jp", [2026]))

    def test_update_history_keeps_last_thirty(self):
        app._clear_cache(app.UPDATE_HISTORY_FILE)
        for index in range(35):
            app._record_update(f"source-{index}", "2026-08-25", "success",
                               time.perf_counter())
        history = app._load_cache(app.UPDATE_HISTORY_FILE, None)
        self.assertEqual(len(history), 30)
        self.assertEqual(history[0]["source"], "source-5")
        self.assertEqual(history[-1]["source"], "source-34")
        self.assertTrue({"executed_at", "source", "latest_date", "result",
                         "duration_sec"} <= set(history[-1]))


if __name__ == "__main__":
    unittest.main()

