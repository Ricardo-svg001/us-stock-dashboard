import os
import sys
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


class DailyMenuShareTests(unittest.TestCase):
    def _render_share(self):
        market_counts = {
            "as_of": "2026-09-03",
            "recent_returns": {
                "as_of": "2026-09-03",
                "rows": [
                    {"days": 20, "base": 298, "winners": 169,
                     "win_pct": 56.7, "median_return": 1.15},
                    {"days": 60, "base": 298, "winners": 202,
                     "win_pct": 67.8, "median_return": 6.40},
                ],
            },
        }
        screen = {
            "as_of": "2026-09-03", "n": 54,
            "top": [{"symbol": "NVDA"}, {"symbol": "MSFT"}, {"symbol": "META"}],
            "sectors": [
                {"name": "Finance", "name_zh": "金融", "n": 14},
                {"name": "Energy", "name_zh": "能源", "n": 12},
            ],
        }
        breadth = {
            "date": "2026-09-03",
            "rows": [
                {"period": 50, "pct": 60.7},
                {"period": 100, "pct": 68.8},
                {"period": 150, "pct": 73.5},
            ],
        }

        def fake_cache(name, _max_age):
            return market_counts if name == app.MARKET_COUNT_CACHE else screen

        with mock.patch.object(app, "_load_cache", side_effect=fake_cache), \
                mock.patch.object(app, "get_ma_breadth_snapshot",
                                  return_value=breadth), \
                mock.patch.object(app, "_home_screen_target_date",
                                  return_value="2026-09-03"):
            return app._home_daily_menu_share_html()

    def test_homepage_button_and_both_templates_are_rendered(self):
        html = self._render_share()
        self.assertIn('id="homeDailyShareBtn"', html)
        self.assertIn("每日「今日菜單」文案", html)
        self.assertIn("☕ 美股咖啡館・今日菜單（9/3）", html)
        self.assertIn("20日：上漲 56.7%、中位報酬 +1.15%", html)
        self.assertIn("結果：54檔", html)
        self.assertIn("前幾名：NVDA、MSFT、META", html)
        self.assertIn("產業較集中：金融", html)

    def test_javascript_reads_numbered_attributes_without_blank_output(self):
        html = self._render_share()
        self.assertIn("root.getAttribute('data-template-1')", html)
        self.assertIn("root.getAttribute('data-template-2')", html)
        self.assertNotIn("root.dataset.template1", html)
        self.assertNotIn("root.dataset.template2", html)


if __name__ == "__main__":
    unittest.main()
