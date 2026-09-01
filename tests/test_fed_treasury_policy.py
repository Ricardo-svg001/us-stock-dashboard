import os
import unittest
from unittest import mock

os.environ.setdefault("CACHE_DIR", "/tmp/stock-coffee-policy-test")
os.environ.setdefault("ENABLE_PREFETCH", "0")
os.environ.setdefault("ENABLE_DAILY_UPDATE", "0")

import app


class _Response:
    def __init__(self, row):
        self.row = row

    def raise_for_status(self):
        return None

    def json(self):
        return {"data": [self.row]}


class FedTreasuryPolicyTest(unittest.TestCase):
    def tearDown(self):
        app._clear_cache(app.FED_POLICY_CACHE_FILE)

    def test_home_board_explains_four_layers_without_network(self):
        app._save_cache(app.FED_POLICY_CACHE_FILE, {
            "as_of": "2026-08-28",
            "policy": {
                "dff": {"date": "2026-08-28", "value": 3.63},
                "dfedtarl": {"date": "2026-08-28", "value": 3.5},
                "dfedtaru": {"date": "2026-08-28", "value": 3.75},
                "iorb": {"date": "2026-08-28", "value": 3.65},
            },
            "liquidity": {
                "on_rrp": {"date": "2026-08-28", "value": .4, "change_20": -.7},
                "repo": {"date": "2026-08-28", "value": 0, "change_20": 0},
            },
            "balance_sheet": {
                "total_assets": {"date": "2026-08-26", "value": 6745699},
                "treasury_holdings": {"date": "2026-08-26", "value": 4542228,
                                      "change_4w": 26567},
                "mbs_holdings": {"date": "2026-08-26", "value": 1930728,
                                 "change_4w": -14060},
            },
            "treasury": {
                "tga": {"date": "2026-08-28", "value": 966849,
                        "change_20": 64098},
                "next_7d_offering_bn": 44,
                "auctions": [{"auction_date": "2026-09-02", "term": "7-Year",
                              "type": "Note", "offering_bn": 44}],
            },
            "fiscal_health": {
                "debt": {"date": "2026-08-28", "total": 40104097482666.58,
                         "held_public": 32340688588401.83,
                         "intragov": 7763408894264.75},
                "debt_to_gdp": {"date": "2026-04-01", "value": 122.6,
                                "change_4q": 2.1},
                "interest": {"date": "2026-07-31", "fiscal_year": "2026",
                             "gross_fytd": 1169592962086.09,
                             "revenue_fytd": 4485419503881.15,
                             "revenue_share_pct": 26.1, "avg_rate_pct": 3.447,
                             "annualized_cost_estimate": 1382380000000},
                "qt_model": {"soma_pct_gdp": 1,
                             "ten_year_term_premium_bp": 10},
            },
            "next_fomc": {"decision_date": "2026-09-16"},
        })
        with mock.patch.object(app.requests, "get",
                               side_effect=AssertionError("network called")):
            html = app._fed_policy_panel_html()
        self.assertEqual(html.count("policy-board-label"), 10)
        for text in ("一、資金價格", "二、短期美元流動性",
                     "三、國債供給與聯準會資產負債表", "四、財政承受力",
                     "美債總額", "美債／GDP", "國債利息／國庫收入", "縮表模型",
                     "不能用Fed利率直接乘總債務"):
            self.assertIn(text, html)
        self.assertIn("$40.1T", html)
        self.assertIn("26.1%", html)
        self.assertIn("一年 +2.1%", html)
        self.assertNotIn("一年 +2.1pp", html)
        self.assertIn("只有官方明確啟動淨資產購買計畫才標示為QE", html)

    def test_fiscal_debt_burden_uses_same_period_receipts_and_interest(self):
        responses = [
            _Response({"record_date": "2026-08-28",
                       "tot_pub_debt_out_amt": "40104097482666.58",
                       "debt_held_public_amt": "32340688588401.83",
                       "intragov_hold_amt": "7763408894264.75"}),
            _Response({"record_date": "2026-07-31",
                       "avg_interest_rate_amt": "3.447"}),
            _Response({"record_date": "2026-07-31", "record_fiscal_year": "2026",
                       "current_fytd_rcpt_outly_amt": "4485419503881.15"}),
            _Response({"record_date": "2026-07-31", "record_fiscal_year": "2026",
                       "current_fytd_rcpt_outly_amt": "1169592962086.09"}),
        ]
        with mock.patch.object(app.requests, "get", side_effect=responses) as get:
            result = app._fiscal_debt_burden_raw()
        self.assertEqual(get.call_count, 4)
        self.assertAlmostEqual(result["debt"]["total"], 40104097482666.58)
        self.assertEqual(result["interest"]["revenue_share_pct"], 26.1)
        self.assertEqual(result["interest"]["avg_rate_pct"], 3.447)
        self.assertAlmostEqual(result["interest"]["annualized_cost_estimate"],
                               40104097482666.58 * .03447)

    def test_article_has_matching_zh_and_en_versions(self):
        slug = "how-fed-liquidity-debt-and-rates-affect-us-stocks"
        zh = next(item for item in app._load_articles("zh") if item["slug"] == slug)
        en = next(item for item in app._load_articles("en") if item["slug"] == slug)
        self.assertEqual(zh["tag"], "利率與整體")
        self.assertEqual(en["tag"], "Rates & Macro")
        self.assertIn("四層", zh["summary"])
        self.assertIn("four layers", en["html"])

    def test_series_change(self):
        rows = [("2026-08-%02d" % (index + 1), float(index)) for index in range(21)]
        self.assertEqual(app._series_change(rows, 20), 20.0)
        self.assertIsNone(app._series_change(rows, 21))


if __name__ == "__main__":
    unittest.main()
