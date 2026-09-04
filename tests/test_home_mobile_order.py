"""首頁手機排版：區塊順序與標題字級。"""
import re
import unittest

import app


class HomeMobileOrderTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.client = app.app.test_client()
        cls.html = cls.client.get("/").get_data(as_text=True)

    def test_mobile_css_orders_five_home_sections(self):
        """手機寬度必須固定：大盤 → 篩選／產業 → 選股環境 → 聯準會。"""
        mobile = re.search(
            r"@media\(max-width:760px\)\{(.*?)\}\s*@media\(max-width:560px\)",
            self.html,
            re.S,
        )
        self.assertIsNotNone(mobile, "missing mobile home media query")
        block = mobile.group(1)
        self.assertIn("display:flex", block)
        self.assertIn("flex-direction:column", block)
        for selector, order in (
            (".home-dashboard .market-chart-card", "1"),
            (".home-dashboard .home-action-panel", "2"),
            (".home-dashboard .market-returns-card", "3"),
            (".home-dashboard .fed-policy-panel", "5"),
        ):
            self.assertRegex(
                block,
                re.escape(selector) + r"\{[^}]*order:" + order,
                msg=f"{selector} should be order:{order}",
            )

    def test_home_section_titles_are_bold_and_larger(self):
        self.assertIn("納斯達克大盤", self.html)
        self.assertIn("產業速報", self.html)
        self.assertIn("近期選股環境", self.html)
        self.assertRegex(self.html, r"\.island-shortcut>b\{display:block;font:800 22px")
        self.assertRegex(self.html, r"\.hs-head b \{[^}]*font-size:22px[^}]*font-weight:800")
        self.assertRegex(self.html, r"\.market-data-card h2\{[^}]*font:800 22px")
        self.assertRegex(self.html, r"\.home-industry-head h2\{[^}]*font:800 22px")
        self.assertRegex(self.html, r"\.fed-policy-head h2\{[^}]*font:800 22px")
        self.assertIn(".island-shortcut>span{", self.html)
        self.assertIn("hs-meta", self.html)
        self.assertNotIn("強勢股篩選：今天沒有符合條件", self.html)


if __name__ == "__main__":
    unittest.main()
