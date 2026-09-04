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
        return {"data": self.row if isinstance(self.row, list) else [self.row]}


class FedTreasuryPolicyTest(unittest.TestCase):
    def tearDown(self):
        app._clear_cache(app.FED_POLICY_CACHE_FILE)

    def test_home_board_uses_responsive_indicator_cards_without_network(self):
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
                "net_liquidity": {"date": "2026-08-26", "value": 5775880,
                                  "change_4w": -44200},
            },
            "balance_sheet": {
                "total_assets": {"date": "2026-08-26", "value": 6745699},
                "securities": {"date": "2026-08-26", "value": 6475303,
                               "change_4w": -12000},
                "treasury_holdings": {"date": "2026-08-26", "value": 4542228,
                                      "change_4w": 26567},
                "mbs_holdings": {"date": "2026-08-26", "value": 1930728,
                                 "change_4w": -14060},
                "bank_reserves": {"date": "2026-08-26", "value": 3062149,
                                  "change_4w": -80000},
            },
            "treasury": {
                "tga": {"date": "2026-08-28", "value": 966849,
                        "change_4w": 64098},
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
            "liquidity_history": {
                "net_liquidity": [["2026-08-19", 5780000], ["2026-08-26", 5775880]],
                "securities": [["2026-08-19", 6469000], ["2026-08-26", 6475303]],
                "total_assets": [["2026-08-19", 6750000], ["2026-08-26", 6745699]],
                "tga": [["2026-08-19", 970000], ["2026-08-26", 966849]],
                "on_rrp": [["2026-08-19", 500], ["2026-08-26", 400]],
                "bank_reserves": [["2026-08-19", 3100000], ["2026-08-26", 3062149]],
            },
        })
        with mock.patch.object(app.requests, "get",
                               side_effect=AssertionError("network called")):
            html = app._fed_policy_panel_html()
        self.assertEqual(html.count('<article class="indicator-card'), 11)
        self.assertEqual(html.count('class="indicator-section"'), 4)
        self.assertNotIn('class="policy-board"', html)
        for text in ("資金價格", "短期美元流動性",
                     "國債供給與聯準會資產負債表", "財政承受力",
                     "美國聯邦債務", "聯邦債務／GDP", "國債利息／聯邦收入", "縮表模型",
                     "不能用Fed利率直接乘總債務"):
            self.assertIn(text, html)
        for text in ("WSHOSHO", "WALCL", "WDTGAL", "RRPONTSYD", "WRESBAL",
                     "6.48兆美元", "40.1兆美元",
                     "3.50%～3.75%", "情境試算", "資料尚未取得"):
            self.assertIn(text, html)
        self.assertIn("淨流動性＝Fed 總資產（WALCL）− TGA（WDTGAL）− ON RRP（RRPONTSYD）", html)
        self.assertIn('class="fed-policy-fold liquidity-fold"', html)
        self.assertIn('class="fed-policy-fold policy-detail-fold"', html)
        self.assertIn('class="indicator-direction positive"', html)
        self.assertIn('class="indicator-direction negative"', html)
        self.assertIn('class="indicator-direction neutral"', html)
        self.assertIn("QT／抽走流動性", html)
        self.assertIn("TGA 金額上升，從市場吸收流動性", html)
        self.assertIn("資金回流市場", html)
        self.assertIn("26.1%", html)
        self.assertIn("近1年 +2.1%", html)
        self.assertIn("FY2026累計 1.17兆美元", html)
        self.assertNotIn("FY2026預估毛利息", html)
        self.assertIn("debt_to_penny", html)
        self.assertIn("只有官方明確啟動淨資產購買計畫才標示為QE", html)

    def test_missing_comparisons_are_disclosed_not_invented(self):
        app._save_cache(app.FED_POLICY_CACHE_FILE, {
            "policy": {"dff": {"date": "2026-08-28", "value": 3.63},
                       "dfedtarl": {"date": "2026-08-28", "value": 3.5},
                       "dfedtaru": {"date": "2026-08-28", "value": 3.75}},
            "treasury": {"tga": {}}, "liquidity": {}, "balance_sheet": {},
            "fiscal_health": {}, "liquidity_history": {},
        })
        html = app._fed_policy_panel_html()
        self.assertIn("最近變動：現有快取未提供前次比較值", html)
        self.assertIn("目前僅能確認發行規模，尚無法判斷相對壓力", html)
        self.assertIn("FRED／BEA A191RL1Q225SBEA", html)
        self.assertNotIn("FY—預估", html)

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

    def test_fiscal_debt_burden_builds_current_fiscal_year_history(self):
        responses = [
            _Response([
                {"record_date": "2026-07-31", "tot_pub_debt_out_amt": "40100000000000"},
                {"record_date": "2026-06-30", "tot_pub_debt_out_amt": "40000000000000"},
            ]),
            _Response([
                {"record_date": "2026-07-31", "avg_interest_rate_amt": "3.45"},
                {"record_date": "2026-06-30", "avg_interest_rate_amt": "3.40"},
            ]),
            _Response([
                {"record_date": "2026-07-31", "record_fiscal_year": "2026", "current_fytd_rcpt_outly_amt": "4500000000000"},
                {"record_date": "2026-06-30", "record_fiscal_year": "2026", "current_fytd_rcpt_outly_amt": "3900000000000"},
            ]),
            _Response([
                {"record_date": "2026-07-31", "record_fiscal_year": "2026", "current_fytd_rcpt_outly_amt": "1170000000000"},
                {"record_date": "2026-06-30", "record_fiscal_year": "2026", "current_fytd_rcpt_outly_amt": "1000000000000"},
            ]),
        ]
        with mock.patch.object(app.requests, "get", side_effect=responses):
            result = app._fiscal_debt_burden_raw()
        history = result["history"]
        self.assertEqual(len(history["avg_rate"]), 2)
        self.assertEqual(len(history["annualized_cost"]), 2)
        self.assertEqual(len(history["gross_interest"]), 2)
        self.assertEqual(len(history["revenue"]), 2)
        self.assertEqual(len(history["interest_share"]), 2)
        self.assertAlmostEqual(history["interest_share"][-1][1], 26.0)

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

    def test_tga_decline_label_names_the_indicator_and_liquidity_effect(self):
        cached = {"treasury": {"tga": {"date": "2026-08-28", "value": 959440,
                                         "change_4w": -11010}}}
        with mock.patch.object(app, "_load_cache", return_value=cached):
            html = app._fed_policy_panel_html()
        self.assertIn("TGA 金額下降，向市場釋放流動性", html)
        self.assertIn('class="indicator-direction positive"><b>↓</b>', html)

    def test_liquidity_history_normalizes_rrp_and_uses_past_observation(self):
        history = app._liquidity_history({
            "WALCL": [("2026-08-20", 7000000), ("2026-08-27", 6900000)],
            "WSHOSHO": [("2026-08-20", 6500000)],
            "WDTGAL": [("2026-08-19", 900000), ("2026-08-26", 950000)],
            "RRPONTSYD": [("2026-08-18", 10), ("2026-08-25", 20)],
            "WRESBAL": [("2026-08-20", 3000000)],
        })
        self.assertEqual(history["on_rrp"], [("2026-08-18", 10000.0),
                                              ("2026-08-25", 20000.0)])
        self.assertEqual(history["net_liquidity"], [("2026-08-20", 6090000.0),
                                                     ("2026-08-27", 5930000.0)])


if __name__ == "__main__":
    unittest.main()
