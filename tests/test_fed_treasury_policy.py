import os
import unittest
from unittest import mock

os.environ.setdefault("CACHE_DIR", "/tmp/stock-coffee-policy-test")
os.environ.setdefault("ENABLE_PREFETCH", "0")
os.environ.setdefault("ENABLE_DAILY_UPDATE", "0")

import app


class FedTreasuryPolicyTest(unittest.TestCase):
    def tearDown(self):
        app._clear_cache(app.FED_POLICY_CACHE_FILE)

    def test_home_board_reads_cache_without_network(self):
        app._save_cache(app.FED_POLICY_CACHE_FILE, {
            "as_of": "2026-08-25",
            "policy": {
                "dff": {"date": "2026-08-25", "value": 3.63},
                "dfedtarl": {"date": "2026-08-25", "value": 3.5},
                "dfedtaru": {"date": "2026-08-25", "value": 3.75},
                "iorb": {"date": "2026-08-25", "value": 3.65},
            },
            "liquidity": {
                "on_rrp": {"date": "2026-08-25", "value": .4, "change_20": -.7},
                "repo": {"date": "2026-08-25", "value": 0, "change_20": 0},
            },
            "balance_sheet": {
                "total_assets": {"date": "2026-08-19", "value": 6745699},
                "treasury_holdings": {"date": "2026-08-19", "value": 4542228,
                                      "change_4w": 26567},
                "mbs_holdings": {"date": "2026-08-19", "value": 1930728,
                                 "change_4w": -14060},
            },
            "treasury": {
                "tga": {"date": "2026-08-25", "value": 966849, "change_20": 64098},
                "next_7d_offering_bn": 44,
                "auctions": [{"auction_date": "2026-08-27", "term": "7-Year",
                              "type": "Note", "offering_bn": 44}],
            },
            "next_fomc": {"decision_date": "2026-09-16"},
        })
        with mock.patch.object(app.requests, "get", side_effect=AssertionError("network called")):
            html = app._fed_policy_panel_html()
        self.assertIn("policy-board", html)
        self.assertEqual(html.count("policy-board-label"), 5)
        self.assertIn("聯準會與財政部動向", html)
        self.assertIn("Fed &amp; Treasury watch", html)
        self.assertIn("只有官方明確啟動淨資產購買計畫才標示為QE", html)

    def test_series_change(self):
        rows = [("2026-08-%02d" % (index + 1), float(index)) for index in range(21)]
        self.assertEqual(app._series_change(rows, 20), 20.0)
        self.assertIsNone(app._series_change(rows, 21))


if __name__ == "__main__":
    unittest.main()
