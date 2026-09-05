"""手機下方快捷列：對應美股四個入口。"""
import os
import re
import sys
import types
import unittest

os.environ.setdefault("ENABLE_PREFETCH", "0")
os.environ.setdefault("ENABLE_DAILY_UPDATE", "0")
try:
    import holidays  # noqa: F401
except ModuleNotFoundError:
    sys.modules["holidays"] = types.SimpleNamespace(
        country_holidays=lambda *args, **kwargs: {})

import app


class MobileBottomNavTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.client = app.app.test_client()

    def test_home_has_four_app_tabs_mapped_to_us_routes(self):
        html = self.client.get("/").get_data(as_text=True)
        self.assertIn('class="app-tabs"', html)
        self.assertIn('data-tab="market" href="/"', html)
        self.assertIn('data-tab="screen" href="/screener"', html)
        self.assertIn('data-tab="structure" href="/breakout-structure"', html)
        self.assertIn('id="appMoreBtn"', html)
        self.assertIn("主頁面", html)
        self.assertIn("找強勢股", html)
        self.assertIn("飆股結構", html)
        self.assertIn("更多", html)
        self.assertRegex(
            html,
            r"@media\(max-width:760px\)\{[^}]*\.app-tabs \{[^}]*display:grid",
        )
        self.assertNotIn("#menuBtn { display:none; }", html)
        self.assertIn("#menuBtn{\n      display:flex!important", html)
        self.assertIn('el.dataset.tab === activeTab', html)

    def test_screener_marks_screen_tab_active(self):
        html = self.client.get("/screener").get_data(as_text=True)
        self.assertIn('const START_PAGE = "p1"', html)
        self.assertIn('START_PAGE === "p1" ? "screen"', html)

    def test_structure_page_marks_structure_tab_active(self):
        html = self.client.get("/breakout-structure").get_data(as_text=True)
        self.assertIn('const START_PAGE = "pstructure"', html)
        self.assertIn('START_PAGE === "pstructure" ? "structure"', html)


if __name__ == "__main__":
    unittest.main()
