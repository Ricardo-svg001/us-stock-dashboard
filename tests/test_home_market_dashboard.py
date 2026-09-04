import os
import sys
import tempfile
import types
import unittest
from unittest import mock

os.environ.setdefault("ENABLE_PREFETCH", "0")
os.environ.setdefault("ENABLE_DAILY_UPDATE", "0")
try:
    import holidays  # noqa: F401
except ModuleNotFoundError:
    sys.modules["holidays"] = types.SimpleNamespace(
        country_holidays=lambda *args, **kwargs: {})

import app


class HomeMarketDashboardTest(unittest.TestCase):
    def setUp(self):
        self.old_cache_dir = app.CACHE_DIR
        self.tmp = tempfile.TemporaryDirectory()
        app.CACHE_DIR = self.tmp.name

    def tearDown(self):
        app.CACHE_DIR = self.old_cache_dir
        self.tmp.cleanup()

    def test_quartiles_use_linear_interpolation(self):
        self.assertEqual(app._return_quartiles([1, 2, 3, 4]), (1.75, 3.25))
        self.assertEqual(app._return_quartiles([]), (None, None))

    def test_dashboard_shows_quartiles_only_when_cached(self):
        app._save_cache(app.MARKET_COUNT_CACHE, {
            "recent_returns": {"as_of": "2026-09-01", "rows": [
                {"days": 20, "base": 4, "winners": 2, "win_pct": 50,
                 "median_return": 2.5, "q1_return": -1.25, "q3_return": 6.75},
                {"days": 60, "base": 4, "winners": 3, "win_pct": 75,
                 "median_return": 8.5},
            ]},
        })
        breadth = {"date": "2026-09-01", "rows": [
            {"period": 50, "pct": 55},
            {"period": 100, "pct": 60},
            {"period": 150, "pct": 65},
        ]}
        with mock.patch.object(app, "get_ma_breadth_snapshot", return_value=breadth):
            html = app._home_market_dashboard_html()
        self.assertIn("報酬四分位區間", html)
        for quartile in ("Q1", "Q2", "Q3", "Q4"):
            self.assertIn(quartile, html)
        for boundary in ("≤ -1.25%", "-1.25%～+2.50%", "+2.50%～+6.75%", "≥ +6.75%"):
            self.assertIn(boundary, html)
        self.assertEqual(html.count("market-return-quartiles"), 1)
        self.assertIn("market-return-grid", html)
        self.assertIn("market-breadth-card", html)
        self.assertIn("半年線", html)
        self.assertNotIn("中長期", html)
        for label in ("季線（50MA）", "半年線（100MA）", "年線（150MA）"):
            self.assertIn(label, html)

    def test_home_breadth_uses_50_100_150_moving_averages(self):
        self.assertEqual(app.SNAP_MAS, ((50, "50MA"), (100, "100MA"), (150, "150MA")))
        history = [["2026-%03d" % day, float(day)] for day in range(1, 151)]
        result = app.build_ma_breadth_snapshot(
            universe=[{"symbol": "TEST"}], histories={"TEST": history})
        self.assertEqual([row["period"] for row in result["rows"]], [50, 100, 150])
        self.assertEqual([row["base"] for row in result["rows"]], [1, 1, 1])

    def test_liquidity_chart_has_four_period_buttons(self):
        app._save_cache(app.FED_POLICY_CACHE_FILE, {"liquidity_history": {}})
        html = app._fed_policy_panel_html()
        for days in (92, 183, 365, 1096):
            self.assertIn('data-liquidity-days="%d"' % days, html)
        self.assertIn("3個月", html)
        self.assertIn("6個月", html)
        self.assertIn("1年", html)
        self.assertIn("3年", html)

    def test_liquidity_chart_preserves_ratio_and_removes_mobile_blank_space(self):
        with open(app.__file__, encoding="utf-8") as source_file:
            source = source_file.read()
        self.assertIn("W=900,H=220,L=72,R=22", source)
        self.assertNotIn("H=compact?180:220", source)
        self.assertIn("#liquidityChart{min-height:0}", source)
        self.assertNotIn("data-liquidity-key", source)

    def test_home_islands_keep_full_menu_and_liquidity_fold(self):
        html = app.PAGE
        self.assertIn('id="topBrand"', html)
        self.assertIn("home-shortcuts", html)
        self.assertIn("island-shortcut", html)
        self.assertIn("bpromise", html)
        self.assertIn('href="/pro/rs"', html)
        self.assertIn('data-page="p7"', html)


if __name__ == "__main__":
    unittest.main()
