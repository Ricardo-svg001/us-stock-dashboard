import unittest

import app


def _row(symbol, sector, industry, ret20, ret60, rank):
    return {"rank": rank, "symbol": symbol, "name": symbol,
            "name_zh": symbol, "sector": sector, "sector_zh": sector,
            "industry": industry, "ret20": ret20, "ret60": ret60,
            "prev20": ret20 - 1, "prev60": ret60 - 1,
            "above50": ret60 >= 0, "newhigh": ret20 >= 5,
            "rs60": 80 - rank, "structure_status": "none"}


class IndustryTaxonomyTest(unittest.TestCase):
    def test_nvidia_has_reviewed_ai_reason(self):
        taxonomy = app._load_industry_taxonomy()
        ai = next(x for x in taxonomy["by_symbol"]["NVDA"]
                  if x["name"] == "AI Compute")
        self.assertEqual(ai["relevance"], "core")
        self.assertIn("generative-AI", ai["reason_en"])
        self.assertIn("生成式 AI", ai["reason_zh"])

    def test_official_sector_is_not_replaced_by_subindustry(self):
        rows = [_row("A%d" % i, "Technology", "Semiconductors", i, i, i)
                for i in range(1, 6)]
        groups = app._build_industry_groups(
            rows, lambda row: [{"name": row["sector"]}], 5, "official")
        self.assertEqual(groups[0]["name"], "Technology")
        self.assertEqual(groups[0]["kind"], "official")
        self.assertEqual(rows[0]["industry"], "Semiconductors")

    def test_reason_and_multi_label_survive_group_build(self):
        rows = [_row("A", "Tech", "Software", 10, 20, 1),
                _row("B", "Tech", "Software", 0, 5, 2),
                _row("C", "Tech", "Software", -2, -3, 3)]
        labels = {"A": [{"name": "AI", "name_zh": "人工智慧",
                           "relevance": "core", "reason_en": "Approved reason."}],
                  "B": [{"name": "AI", "name_zh": "人工智慧",
                           "relevance": "important"}],
                  "C": [{"name": "AI", "name_zh": "人工智慧",
                           "relevance": "secondary"}]}
        groups = app._build_industry_groups(
            rows, lambda row: labels[row["symbol"]], 3, "theme")
        self.assertEqual(groups[0]["name_zh"], "人工智慧")
        self.assertEqual(groups[0]["stocks"][0]["reason_en"], "Approved reason.")
        self.assertEqual([x["relevance"] for x in groups[0]["stocks"]],
                         ["core", "important", "secondary"])

    def test_theme_overlap_is_directional(self):
        def group(name, symbols):
            return {"name": name, "name_zh": name,
                    "stocks": [{"symbol": symbol} for symbol in symbols]}
        groups = [group("A", ["1", "2", "3", "4"]),
                  group("B", ["1", "2", "3"]),
                  group("C", ["1", "2", "5"])]
        result = app._attach_theme_overlaps(groups)
        self.assertEqual(result[0]["overlaps"][0]["count"], 3)
        self.assertEqual(result[0]["overlaps"][0]["pct"], 75.0)
        self.assertEqual(result[1]["overlaps"][0]["pct"], 100.0)


if __name__ == "__main__":
    unittest.main()
