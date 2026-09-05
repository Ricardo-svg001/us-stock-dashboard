import importlib.util
import pathlib
import unittest


def _load():
    path = pathlib.Path(__file__).resolve().parents[1] / "研究" / "腳本" / "抓取十年歷史.py"
    spec = importlib.util.spec_from_file_location("fetch_hist10", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


class YahooExtendTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.m = _load()

    def test_overlap_accepts_identical_closes(self):
        nasdaq = [[f"2023-03-{i:02d}", 100.0 + i] for i in range(1, 25)]
        yahoo = [["2022-01-03", 80.0]] + nasdaq
        ok, med = self.m.yahoo_extends(nasdaq, yahoo)
        self.assertTrue(ok)
        self.assertEqual(med, 0.0)

    def test_rejects_mismatched_scale(self):
        nasdaq = [[f"2023-03-{i:02d}", 100.0] for i in range(1, 25)]
        yahoo = [["2022-01-03", 80.0]] + [[d, c * 2] for d, c in nasdaq]
        ok, med = self.m.yahoo_extends(nasdaq, yahoo)
        self.assertFalse(ok)
        self.assertGreater(med, 1)

    def test_does_not_extend_when_yahoo_not_older(self):
        nasdaq = [[f"2023-03-{i:02d}", 100.0] for i in range(1, 25)]
        ok, med = self.m.yahoo_extends(nasdaq, nasdaq)
        self.assertFalse(ok)
        self.assertIsNone(med)


if __name__ == "__main__":
    unittest.main()
