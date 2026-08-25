import inspect
import json
import os
import pathlib
import time
import unittest
from datetime import date, timedelta

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

    def test_five_stage_market_contract(self):
        spec = self.contract["market_phase"]
        self.assertEqual(tuple(spec["moving_averages"]), app.MARKET_PHASE_MAS)
        self.assertEqual(spec["stage_count"], len(app.MARKET_LIFECYCLE))
        self.assertEqual(spec["stage_keys"], [row[0] for row in app.MARKET_LIFECYCLE])
        self.assertEqual(app.PHASE_GAP_PCT, 5.0)
        self.assertEqual(app.PHASE_RISKOFF_PCT, 3.0)
        self.assertEqual(app.PHASE_RECOVERY_PCT, 4.0)
        self.assertEqual(app.PHASE_CONFIRM_DAYS, 3)
        self.assertTrue(spec["carry_forward_when_unmatched"])
        self.assertEqual(spec["recovery_watch_trigger_any"],
                         ["120ma_gt_20ma", "120ma_gt_60ma"])
        self.assertTrue(spec["recovery_watch_reset_on_tailwind"])

        def series(values):
            start = date(2025, 1, 1)
            return {str(start + timedelta(days=i)): value for i, value in enumerate(values)}

        rising = [100 * (1.01 ** i) for i in range(145)]
        tailwind = rising + [rising[-1] * .98] * 5  # 最後形成 5MA < 10MA，仍屬多頭
        self.assertEqual(app._five_stage_from_index(series(tailwind))[0], "tailwind")
        base = [100 * (1.002 ** i) for i in range(140)]
        consolidation = base + [base[-1] * .98] * 10
        self.assertEqual(app._five_stage_from_index(series(consolidation))[0], "transition")
        self.assertEqual(app._five_stage_from_index(
            series([200 * (.995 ** i) for i in range(150)]))[0], "riskoff")
        early = [200 * (.995 ** i) for i in range(140)] + [100] * 5 + [50] * 2 + [115] * 3
        self.assertEqual(app._five_stage_from_index(series(early))[0], "recovery_early")
        confirmed = [200 * (.995 ** i) for i in range(147)] + [140] * 3
        confirmed_result = app._five_stage_from_index(series(confirmed))
        self.assertEqual(confirmed_result[0], "recovery_confirmed")
        self.assertTrue(confirmed_result[2]["recovery_watch"])
        self.assertTrue(confirmed_result[2]["broad_bear"])
        unmatched = consolidation + [126.8973, 127.2110, 113.1703, 138.3940, 111.2081,
                                     111.4505, 118.1711, 115.9632, 124.4106, 110.7484]
        carried = app._five_stage_from_index(series(unmatched))
        self.assertEqual(carried[0], "transition")
        self.assertTrue(carried[2]["carried"])


if __name__ == "__main__":
    unittest.main()
