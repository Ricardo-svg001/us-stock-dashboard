"""手機與桌機品牌列獨立區塊＋桌機 120% 基準縮放。"""
import re
import unittest

import app


class BrandBarAndDesktopZoomTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.client = app.app.test_client()
        cls.html = cls.client.get("/").get_data(as_text=True)

    def test_brand_bar_wraps_logo_and_top_controls(self):
        self.assertIn('id="brandBar"', self.html)
        start = self.html.find('<header id="brandBar"')
        end = self.html.find("</header>", start)
        self.assertGreaterEqual(start, 0)
        self.assertGreater(end, start)
        block = self.html[start:end]
        self.assertIn('id="menuBtn"', block)
        self.assertIn('id="topBrand"', block)
        self.assertIn('id="topBtns"', block)
        self.assertLess(block.find('id="menuBtn"'), block.find('id="topBrand"'))
        self.assertLess(block.find('id="topBrand"'), block.find('id="topBtns"'))

    def test_mobile_brand_bar_is_independent_fixed_block(self):
        mobile = re.search(
            r"@media\(max-width:760px\)\{(.*?)\}"
            r"\s*@media\(max-width:560px\)\{\.reading-row",
            self.html,
            re.S,
        )
        self.assertIsNotNone(mobile, "missing mobile brand-bar media query")
        block = mobile.group(1)
        self.assertIn("#brandBar{", block)
        self.assertIn("position:fixed", block)
        self.assertIn("background:var(--milk)", block)
        self.assertIn("--brand-bar-h:52px", block)
        self.assertIn(
            ".wrap{padding-top:calc(var(--brand-bar-h) + env(safe-area-inset-top) + 12px)}",
            block,
        )
        self.assertIn("#menuBtn,#topBrand,#topBtns{position:static", block)
        self.assertIn("#topBrand small{display:none}", block)

    def test_desktop_sets_120_percent_zoom_baseline(self):
        desktop = re.search(
            r"@media\(min-width:1024px\)\{(.*?)\}"
            r"\s*@media\(min-width:761px\)",
            self.html,
            re.S,
        )
        self.assertIsNotNone(desktop, "missing desktop zoom media query")
        block = desktop.group(1)
        self.assertIn("body{zoom:1.2}", block)
        self.assertIn("基準值", self.html)

    def test_desktop_brand_bar_is_independent_fixed_block(self):
        desktop_layout = re.search(
            r"@media\(min-width:761px\)\{(.*?)\}"
            r"\s*@media\(max-width:760px\)\{",
            self.html,
            re.S,
        )
        self.assertIsNotNone(desktop_layout, "missing desktop layout media query")
        block = desktop_layout.group(1)
        self.assertIn("--desktop-brand-bar-h:64px", block)
        self.assertIn("#brandBar{", block)
        self.assertIn("position:fixed", block)
        self.assertIn("display:flex", block)
        self.assertIn("background:var(--milk)", block)
        self.assertIn("#brandBar #menuBtn,#brandBar #topBrand,#brandBar #topBtns{position:static", block)
        self.assertIn(".wrap{padding-top:calc(var(--desktop-brand-bar-h) + 14px)}", block)

    def test_topbar_has_one_article_link_and_round_menu_button(self):
        start = self.html.find('<header id="brandBar"')
        end = self.html.find("</header>", start)
        topbar = self.html[start:end]
        self.assertIn('id="topArticlesLink" href="/articles"', topbar)
        self.assertNotIn('id="mktBtn"', topbar)
        self.assertNotIn('id="themeBtn"', topbar)
        self.assertNotIn('id="langBtn"', topbar)
        self.assertIn(
            "#brandBar #menuBtn{order:0;flex:0 0 46px;width:46px;min-width:46px;height:46px;aspect-ratio:1}",
            self.html,
        )

    def test_sidebar_theme_and_language_do_not_depend_on_removed_topbar_buttons(self):
        self.assertIn("function openThemePicker()", self.html)
        self.assertIn("function toggleLang()", self.html)
        self.assertNotIn('class="top-control-proxy"', self.html)
        self.assertIn("openThemePicker();", self.html)
        self.assertIn("toggleLang();", self.html)


if __name__ == "__main__":
    unittest.main()
