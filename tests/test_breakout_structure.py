import os
import json
from pathlib import Path
import sys
import types
import unittest
from datetime import date, timedelta

os.environ["ENABLE_PREFETCH"] = "0"
os.environ["ENABLE_DAILY_UPDATE"] = "0"
try:
    import holidays  # noqa: F401
except ModuleNotFoundError:
    sys.modules["holidays"] = types.SimpleNamespace(
        country_holidays=lambda country, **kwargs: (
            {date(2026, 2, 11): "National Foundation Day"}
            if country == "JP" else {}))

sys.path.insert(0, os.path.dirname(os.path.dirname(__file__)))
import app


def linear(a, b, n):
    return [a + (b - a) * i / max(1, n - 1) for i in range(n)]


def rounded_base(final_price=153):
    values = (linear(82, 100, 80) + linear(100, 64, 170)
              + linear(64, 72, 280) + linear(72, 89, 310)
              + linear(89, final_price, 60))
    out, d = [], date(2021, 8, 2)
    for value in values:
        while d.weekday() >= 5:
            d += timedelta(days=1)
        out.append([d.isoformat(), value])
        d += timedelta(days=1)
    return out


class BreakoutStructureTest(unittest.TestCase):
    def test_deployed_seed_covers_top_300_and_four_periods(self):
        payload = json.loads(Path(app.BREAKOUT_STRUCTURE_FILE).read_text(encoding="utf-8"))
        self.assertEqual(payload["version"], app.STRUCTURE_VERSION)
        self.assertEqual(payload["universe"], 300)
        self.assertEqual(set(payload["period_sessions"]), {"6m", "1y", "2y", "5y"})
        self.assertEqual(len(payload["rows"]), 300)
        self.assertTrue(all(set(row["periods"]) == {"6m", "1y", "2y", "5y"}
                            for row in payload["rows"].values()))

    def test_long_base_with_recent_acceleration_matches(self):
        result = app.analyze_breakout_structure(rounded_base())
        self.assertTrue(result["available"])
        self.assertTrue(result["matched"])
        self.assertLessEqual(result["max_drawdown_pct"], -20)
        self.assertGreaterEqual(result["consolidation_months"], 3)
        self.assertGreater(result["recent_gain_pct"], 30)
        self.assertGreater(len(result["chart"]), 100)

    def test_structure_without_thirty_percent_gain_is_nearly_complete(self):
        result = app.analyze_breakout_structure(rounded_base(final_price=100))
        self.assertTrue(result["available"])
        self.assertFalse(result["matched"])
        self.assertIsNotNone(result.get("prior_high"))
        self.assertIn("30%", result["reason"])

    def test_suspected_split_discontinuity_is_rejected(self):
        rows = rounded_base()
        for row in rows[400:]:
            row[1] *= .5
        result = app.analyze_breakout_structure(rows)
        self.assertFalse(result["available"])
        self.assertIn("拆股", result["reason"])

    def test_watchlist_only_traces_rows_that_pass_original_screen(self):
        originals = (app.get_universe, app.load_histories, app.load_fundamentals,
                     app.attach_quotes, app.get_breakout_structures)
        seen = []
        try:
            histories = {
                "AAA": rounded_base(),
                "BBB": [[row[0], 300 - i * .2]
                        for i, row in enumerate(rounded_base())],
            }
            app.get_universe = lambda n=150: [
                {"symbol": "AAA", "name": "Alpha", "sector": "Technology"},
                {"symbol": "BBB", "name": "Beta", "sector": "Finance"},
            ]
            app.load_histories = lambda symbols, status_cb=None: histories
            app.load_fundamentals = lambda symbols, status_cb=None: {}
            app.attach_quotes = lambda rows: (rows, {"open": False})

            def fake_structures(symbols, histories=None, status_cb=None):
                seen.extend(symbols)
                return {s: {"available": True, "matched": True} for s in symbols}

            app.get_breakout_structures = fake_structures
            result = app.screen_watchlist(
                150, ma=50, direction="above", days=1, align="none",
                structure_history=True)
            self.assertEqual(seen, ["AAA"])
            self.assertTrue(result["rows"][0]["structure"]["matched"])
        finally:
            (app.get_universe, app.load_histories, app.load_fundamentals,
             app.attach_quotes, app.get_breakout_structures) = originals

    def test_independent_structure_screen_filters_status_and_pattern(self):
        result = app.get_breakout_structure_screen("5y", "qualified", "u_or_cup")
        self.assertEqual(result["universe"], 300)
        self.assertTrue(result["results"])
        self.assertTrue(all(r["structure_status"] in ("matched", "near")
                            for r in result["results"]))
        self.assertTrue(all(set(r["structure"].get("pattern_labels") or [])
                            .intersection(("U 型底", "杯柄"))
                            for r in result["results"]))

    def test_risk_is_capped_at_five_and_rs_uses_full_universe(self):
        self.assertEqual(app.RISK_MAX, 5)
        original = app._load_cache
        dates = [(date(2026, 1, 1) + timedelta(days=i)).isoformat()
                 for i in range(130)]
        histories = {
            "AAA": [[d, 100 + i * 3] for i, d in enumerate(dates)],
            "BBB": [[d, 100 + i] for i, d in enumerate(dates)],
            "CCC": [[d, 100 - i * .2] for i, d in enumerate(dates)],
        }
        try:
            def fake(name, _ttl):
                if name == "universe.json":
                    return [{"symbol": s} for s in histories]
                if name.startswith("hist_"):
                    return histories.get(name[5:-5], [])
                return original(name, _ttl)
            app._load_cache = fake
            scores = app._relative_strength_scores()
        finally:
            app._load_cache = original
        self.assertGreater(scores["AAA"]["rs20"], scores["BBB"]["rs20"])
        self.assertGreater(scores["BBB"]["rs120"], scores["CCC"]["rs120"])

    def test_route_and_navigation_exist(self):
        client = app.app.test_client()
        page = client.get("/breakout-structure")
        self.assertEqual(page.status_code, 200)
        html = page.get_data(as_text=True)
        self.assertIn('id="pstructure"', html)
        self.assertIn('href="/breakout-structure"', html)
        api = client.get("/api/breakout-structure?period=1y&status=qualified&pattern=u_or_cup")
        self.assertEqual(api.status_code, 200)
        self.assertTrue(api.get_json()["ok"])


if __name__ == "__main__":
    unittest.main()
