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
        self.assertEqual(self.result["event_count"], 19)
        self.assertEqual(set(self.result["horizons"]),
                         {str(month) for month in range(3, 13)})
        for month in range(3, 13):
            months = str(month)
            sessions = month * 21
            expected = sum(
                event["followup_sessions"] >= sessions
                or (event["half_break"]["sessions"] is not None
                    and event["half_break"]["sessions"] <= sessions)
                for event in self.result["events"])
            self.assertEqual(self.result["horizons"][months]["eligible"], expected)
            self.assertNotIn("mid_eligible", self.result["horizons"][months])
            self.assertNotIn("short_breaks", self.result["horizons"][months])

    def test_backtest_contract_contains_only_150ma_breaks_and_drawdown(self):
        self.assertNotIn("short_median_months", self.result)
        self.assertNotIn("mid_median_months", self.result)
        for event in self.result["events"]:
            self.assertNotIn("short_break", event)
            self.assertNotIn("mid_break", event)
            self.assertIn("half_break", event)
            self.assertIn("max_drawdown_pct", event)

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

    def test_renewed_bull_confirmation_can_start_another_event(self):
        signals = {event["signal_date"] for event in self.result["events"]}
        self.assertIn("2021-05-11", signals)
        self.assertIn("2021-09-28", signals)

    def test_ten_to_twelve_month_breaks_are_included(self):
        event = next(row for row in self.result["events"]
                     if row["signal_date"] == "2021-03-08")
        self.assertEqual(event["half_break"]["date"], "2022-01-24")
        self.assertEqual(self.result["horizons"]["12"]["half_pct"], 83.3)

    def test_drawdown_runs_from_break_until_three_day_150ma_reclaim(self):
        event = next(row for row in self.result["events"]
                     if row["signal_date"] == "2021-03-08")
        self.assertEqual(event["half_recovery"]["date"], "2022-08-16")
        self.assertEqual(event["half_recovery"]["sessions"], 141)
        self.assertEqual(event["max_drawdown_pct"], -23.2)
        self.assertEqual(event["low_date"], "2022-06-16")
        self.assertEqual(self.result["max_drawdown_median_pct"], -13.5)

    def test_interface_explains_method_before_event_and_probability_tables(self):
        with app.app.test_client() as client:
            body = client.get("/deduction").get_data(as_text=True)
        conditions = body.index("回測條件")
        events = body.index("首次回檔與首次跌破時間")
        probabilities = body.index("時間推移與累積跌破機率")
        self.assertLess(conditions, events)
        self.assertLess(events, probabilities)
        self.assertIn("超過 12 個月後，與原始回檔的因果關聯已不足", body)
        self.assertNotIn("已跌破 100MA", body)
        self.assertIn("跌破後最大跌幅", body)


if __name__ == "__main__":
    unittest.main()
