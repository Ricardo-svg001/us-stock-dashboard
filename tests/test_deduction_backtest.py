import json
import os
import sys
import types
import unittest
from pathlib import Path

os.environ.setdefault("ENABLE_PREFETCH", "0")
os.environ.setdefault("ENABLE_DAILY_UPDATE", "0")
sys.modules.setdefault(
    "holidays", types.SimpleNamespace(country_holidays=lambda *args, **kwargs: {}))
import app


ROOT = Path(__file__).resolve().parents[1]


class DeductionBacktestTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.history = json.loads(
            (ROOT / "deduction_index_10y_seed.json").read_text(encoding="utf-8"))
        cls.result = app._deduction_index_backtest(sorted(cls.history.items()))

    def test_flat_deduction_has_only_period_results(self):
        result = app._ma_deduction(list(range(100, 280)), 279)
        self.assertEqual(set(result), {"50", "100", "150"})
        self.assertTrue(all("days" in row and "ma" in row for row in result.values()))

    def test_seed_backtest_is_stable_and_has_complete_horizon_denominators(self):
        self.assertEqual(self.result["event_count"], 8)
        self.assertEqual(set(self.result["horizons"]),
                         {str(month) for month in range(3, 10)})
        for month in range(3, 10):
            months = str(month)
            sessions = month * 21
            expected = sum(
                event["followup_sessions"] >= sessions
                or (event["half_break"]["sessions"] is not None
                    and event["half_break"]["sessions"] <= sessions)
                for event in self.result["events"])
            self.assertEqual(self.result["horizons"][months]["eligible"], expected)
            self.assertNotIn("short_breaks", self.result["horizons"][months])

    def test_backtest_contract_contains_only_150ma_breaks(self):
        self.assertNotIn("short_median_months", self.result)
        for event in self.result["events"]:
            self.assertNotIn("short_break", event)

    def test_every_reported_150ma_break_meets_three_day_five_percent_rule(self):
        ordered = sorted((date, float(close)) for date, close in self.history.items())
        dates = [row[0] for row in ordered]
        closes = [row[1] for row in ordered]
        period = 150
        moving = {}
        total = sum(closes[:period])
        moving[dates[period - 1]] = total / period
        for index in range(period, len(closes)):
            total += closes[index] - closes[index - period]
            moving[dates[index]] = total / period
        for event in self.result["events"]:
            end_date = event["half_break"]["date"]
            if not end_date:
                continue
            end = dates.index(end_date)
            for index in range(end - 2, end + 1):
                self.assertLessEqual(closes[index], moving[dates[index]] * 0.95)


if __name__ == "__main__":
    unittest.main()
