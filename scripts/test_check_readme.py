#!/usr/bin/env python3
"""Unit tests of check_readme.py.

    python3 -m unittest discover -s scripts -p 'test_*.py'
"""

import io
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import check_readme as cr  # noqa: E402

Y, N, D = "✅", "❌", "—"

EN = f"""# title

Some text. The tables may move; headings may change.

```
| notation | expansion defined | well-foundedness | well-foundedness (non-standard) |
|---|:-:|:-:|:-:|
| inside a fence | {Y} | {Y} | {Y} |
```

| notation | expansion defined | well-foundedness | well-foundedness (non-standard) |
|---|:-:|:-:|:-:|
| BMS | {Y} | {Y} | {Y} |
| extended Buchholz's ψ | {Y} | {Y} |  |

Text between tables.

| notation | defined | injective | surjective | decreases on expansion | equals the rank | order-preserving |
|---|:-:|:-:|:-:|:-:|:-:|:-:|
| one-row DBMS | {Y} |  | {Y} | {Y} | {Y} | {Y} |
| Y sequence |  |  |  |  |  |  |

| from \\\\ to | primitive sequences | BMS, `r` rows | one-row DBMS |
|---|:-:|:-:|:-:|
| primitive sequences | {D} |  |  |
| BMS, `r` rows |  | {D} |  |
| one-row DBMS | {Y}{Y}{Y}{N}{N}{Y} |  | {D} |

| name | statement |
|---|---|
| `x` | an unrelated table |
"""

JA = f"""# 題

| 表記 | 展開の定義 | 整礎性 | 整礎性(非標準) |
|---|:-:|:-:|:-:|
| BMS | {Y} | {Y} | {Y} |
| 拡張ブーフホルツ ψ | {Y} | {Y} |  |

| 表記 | 定義 | 単射性 | 全射性 | 展開で値が下がる | 階数と一致 | 順序を保つ |
|---|:-:|:-:|:-:|:-:|:-:|:-:|
| 1 行の DBMS | {Y} |  | {Y} | {Y} | {Y} | {Y} |
| Y 数列 |  |  |  |  |  |  |

| 翻訳元＼翻訳先 | 原始数列 | BMS `r` 行 | 1 行の DBMS |
|---|:-:|:-:|:-:|
| 原始数列 | {D} |  |  |
| BMS `r` 行 |  | {D} |  |
| 1 行の DBMS | {Y}{Y}{Y}{N}{N}{Y} |  | {D} |
"""


def goal(table, record, row_en, row_ja, tgt_en, tgt_ja, column, status):
    return "\t".join(["GOAL", table, record, row_en, row_ja, tgt_en, tgt_ja,
                      column, status])


def notation(record, en, ja, expansion, wf):
    return [goal("notation", record, en, ja, "", "", "expansion", expansion),
            goal("notation", record, en, ja, "", "", "wf", wf)]


def nonstd(record, en, ja, wf):
    return [goal("notation", record, en, ja, "", "", "wf-nonstd", wf)]


def ordinal(record, en, ja, statuses):
    return [goal("ordinal", record, en, ja, "", "", c, s)
            for c, s in zip(cr.COLUMNS["ordinal"], statuses)]


def between(record, src, tgt, statuses):
    return [goal("between", record, src[0], src[1], tgt[0], tgt[1], c, s)
            for c, s in zip(cr.COLUMNS["between"], statuses)]


P, R, O = "proved", "refuted", "open"

GOALS = (
    notation("G.bmsNotation", "BMS", "BMS", P, P)
    + nonstd("G.bmsNonStd", "BMS", "BMS", P)
    + notation("G.exbNotation", "extended Buchholz's ψ", "拡張ブーフホルツ ψ", P, P)
    + ordinal("G.dbms1Ord", "one-row DBMS", "1 行の DBMS", [P, R, P, P, P, P])
    + between("G.dbms1ToPrss", ("one-row DBMS", "1 行の DBMS"),
              ("primitive sequences", "原始数列"), [P, P, P, R, O, P])
)


def audit(goals=GOALS, axioms="propext,Classical.choice,Quot.sound",
          begin="GOALS-BEGIN\t1", count=None, noise=True):
    lines = []
    if noise:
        lines.append("leanman: check started")
    lines.append(begin)
    lines.extend(goals)
    lines.append(f"GOALS-END\t{len(goals) if count is None else count}")
    if noise:
        lines.append("some other message")
    lines.append(f"GOALS-AXIOMS\t{axioms}")
    return "\n".join(lines) + "\n"


class SplitAndFind(unittest.TestCase):
    def test_split_cells(self):
        self.assertEqual(cr.split_cells("| a | b |  |"), ["a", "b", ""])
        self.assertEqual(cr.split_cells("| a | b"), ["a", "b"])
        self.assertEqual(cr.split_cells("| from \\\\ to | x |"), ["from \\\\ to", "x"])
        self.assertEqual(cr.split_cells("| BMS, `r` rows |"), ["BMS, `r` rows"])

    def test_find_tables_skips_fences_and_needs_delimiter(self):
        tables = cr.find_tables(EN)
        self.assertEqual([t.header.cells[0] for t in tables],
                         ["notation", "notation", "from \\\\ to", "name"])
        first = tables[0]
        self.assertEqual(first.header.line, 11)
        self.assertEqual([r.cells[0] for r in first.rows],
                         ["BMS", "extended Buchholz's ψ"])
        self.assertEqual(first.rows[0].line, 13)
        # A line starting with | but no delimiter line is not a table.
        self.assertEqual(cr.find_tables("| a | b |\n| c | d |\n"), [])

    def test_table_ends_at_first_other_line(self):
        text = "| a | b |\n|---|---|\n| 1 | 2 |\n\n| 3 | 4 |\n"
        tables = cr.find_tables(text)
        self.assertEqual(len(tables), 1)
        self.assertEqual(len(tables[0].rows), 1)

    def test_locate_tables(self):
        en = cr.locate_tables(EN, "en", "README.md")
        ja = cr.locate_tables(JA, "ja", "README-ja.md")
        self.assertEqual(en["between"].header.cells[1:],
                         ["primitive sequences", "BMS, `r` rows", "one-row DBMS"])
        self.assertEqual(ja["between"].header.cells[1:],
                         ["原始数列", "BMS `r` 行", "1 行の DBMS"])
        self.assertEqual(len(en["ordinal"].rows), 2)

    def test_normalize_and_allowed(self):
        self.assertEqual(cr.normalize(" ✅️ "), Y)
        self.assertEqual(cr.normalize(f"{Y} {N}"), Y + N)
        self.assertEqual(cr.normalize(f"{Y}(*1)"), Y)
        self.assertEqual(cr.normalize(f"{Y}{N}(*12)"), Y + N)
        self.assertTrue(cr.allowed("notation", ""))
        self.assertTrue(cr.allowed("ordinal", Y))
        self.assertFalse(cr.allowed("ordinal", N))
        self.assertFalse(cr.allowed("notation", D))
        self.assertTrue(cr.allowed("between", D))
        self.assertTrue(cr.allowed("between", ""))
        self.assertTrue(cr.allowed("between", Y * 3 + N * 3))
        self.assertFalse(cr.allowed("between", Y * 5))
        self.assertFalse(cr.allowed("between", Y * 7))
        self.assertFalse(cr.allowed("between", Y * 5 + "x"))


class Marks(unittest.TestCase):
    def test_marks(self):
        a = cr.parse_audit(audit())
        n = a.tables["en"]["notation"]
        self.assertEqual(cr.expected_mark(n, "notation", "BMS", "wf-nonstd"), Y)
        self.assertEqual(cr.expected_mark(n, "notation", "extended Buchholz's ψ",
                                          "wf-nonstd"), "")
        self.assertEqual(cr.expected_mark(n, "notation", "nobody", "wf"), "")
        o = a.tables["ja"]["ordinal"]
        self.assertEqual(cr.expected_mark(o, "ordinal", "1 行の DBMS", "injective"), "")
        self.assertEqual(cr.expected_mark(o, "ordinal", "1 行の DBMS", "rank"), Y)
        b = a.tables["en"]["between"]
        self.assertEqual(cr.expected_mark(b, "between", "one-row DBMS",
                                          "primitive sequences"), Y * 3 + N * 2 + Y)
        self.assertEqual(cr.expected_mark(b, "between", "BMS, `r` rows",
                                          "one-row DBMS"), "")
        self.assertEqual(cr.expected_mark(b, "between", "one-row DBMS",
                                          "one-row DBMS"), D)

    def test_several_records_one_row(self):
        goals = GOALS + notation("G.bmsNotation2", "BMS", "BMS", P, O)
        a = cr.parse_audit(audit(goals))
        n = a.tables["en"]["notation"]
        self.assertEqual(cr.expected_mark(n, "notation", "BMS", "expansion"), Y)
        self.assertEqual(cr.expected_mark(n, "notation", "BMS", "wf"), "")


class Compare(unittest.TestCase):
    def run_check(self, a=None, en=EN, ja=JA):
        return cr.check(audit() if a is None else a, en, ja)

    def test_agree(self):
        self.assertEqual(self.run_check(), [])

    def test_variation_selector_and_spaces_are_ignored(self):
        en = EN.replace(f"| one-row DBMS | {Y}{Y}{Y}{N}{N}{Y} |",
                        f"| one-row DBMS | {Y}️ {Y}{Y} {N}{N}{Y} |")
        self.assertEqual(self.run_check(en=en), [])

    def test_wrong_mark_first_table(self):
        en = EN.replace(f"| extended Buchholz's ψ | {Y} | {Y} |  |",
                        f"| extended Buchholz's ψ | {Y} | {Y} | {Y} |")
        out = self.run_check(en=en)
        self.assertEqual(out, [
            f'README.md:14: notation: row "extended Buchholz\'s ψ": column '
            f'wf-nonstd: expected "", found "{Y}"'])

    def test_wrong_mark_second_table_ja(self):
        ja = JA.replace(f"| 1 行の DBMS | {Y} |  |", f"| 1 行の DBMS | {Y} | {Y} |")
        out = self.run_check(ja=ja)
        self.assertEqual(out, [
            f'README-ja.md:10: ordinal: row "1 行の DBMS": column injective: '
            f'expected "", found "{Y}"'])

    def test_six_marks_per_column(self):
        en = EN.replace(f"{Y}{Y}{Y}{N}{N}{Y}", f"{Y}{Y}{Y}{Y}{N}{N}")
        out = self.run_check(en=en)
        self.assertEqual(out, [
            f'README.md:27: between: row "one-row DBMS": target "primitive '
            f'sequences": column injective: expected "{N}", found "{Y}"',
            f'README.md:27: between: row "one-row DBMS": target "primitive '
            f'sequences": column rank: expected "{Y}", found "{N}"'])

    def test_blank_cell_where_marks_expected(self):
        en = EN.replace(f"| one-row DBMS | {Y}{Y}{Y}{N}{N}{Y} |  | {D} |",
                        f"| one-row DBMS |  |  | {D} |")
        out = self.run_check(en=en)
        self.assertEqual(len(out), 1)
        self.assertIn('cell: expected "' + Y * 3 + N * 2 + Y + '", found ""', out[0])

    def test_marks_where_no_record(self):
        ja = JA.replace(f"| BMS `r` 行 |  | {D} |  |",
                        f"| BMS `r` 行 |  | {D} | {Y * 6} |")
        out = self.run_check(ja=ja)
        self.assertEqual(len(out), 1)
        self.assertIn('target "1 行の DBMS": cell: expected "", found "' + Y * 6 + '"',
                      out[0])

    def test_diagonal(self):
        en = EN.replace(f"| BMS, `r` rows |  | {D} |  |", "| BMS, `r` rows |  |  |  |")
        out = self.run_check(en=en)
        self.assertEqual(out, [
            'README.md:26: between: row "BMS, `r` rows": target "BMS, `r` rows": '
            f'cell: expected "{D}", found ""'])

    def test_not_allowed_form(self):
        en = EN.replace(f"| BMS | {Y} | {Y} | {Y} |", f"| BMS | {Y} | yes | {Y} |")
        out = self.run_check(en=en)
        self.assertEqual(out, [
            'README.md:13: notation: row "BMS": column wf: not an allowed form: '
            'found "yes"'])
        en = EN.replace(f"{Y}{Y}{Y}{N}{N}{Y}", f"{Y}{Y}{Y}{N}{N}")
        out = self.run_check(en=en)
        self.assertEqual(len(out), 1)
        self.assertIn("not an allowed form", out[0])

    def test_row_missing(self):
        goals = GOALS + ordinal("G.x", "ω-Y", "ω-Y", [P] * 6)
        out = self.run_check(a=audit(goals))
        self.assertEqual(out, [
            'README.md:18: ordinal: row "ω-Y": not in the table',
            'README-ja.md:8: ordinal: row "ω-Y": not in the table'])

    def test_target_missing(self):
        goals = GOALS + between("G.x", ("primitive sequences", "原始数列"),
                                ("pair sequences", "ペア数列"), [P] * 6)
        out = self.run_check(a=audit(goals))
        self.assertIn('README.md:23: between: target "pair sequences": '
                      'not a column header', out)
        self.assertIn('README-ja.md:13: between: target "ペア数列": '
                      'not a column header', out)
        self.assertEqual(len(out), 2)

    def test_header_order(self):
        en = EN.replace("| from \\\\ to | primitive sequences | BMS, `r` rows |",
                        "| from \\\\ to | BMS, `r` rows | primitive sequences |")
        out = self.run_check(en=en)
        self.assertTrue(any("the column headers are not the row labels" in m
                            for m in out))

    def test_row_count_differs(self):
        ja = JA.replace("| Y 数列 |  |  |  |  |  |  |\n", "")
        out = self.run_check(ja=ja)
        self.assertEqual(out, [
            "README-ja.md:8: ordinal: 1 rows, but README.md has 2 rows (line 18)"])

    def test_pairing(self):
        # Swap two rows of the Japanese first table: each row still has the
        # right marks, but the n-th rows no longer pair as the audit says.
        ja = JA.replace(
            f"| BMS | {Y} | {Y} | {Y} |\n| 拡張ブーフホルツ ψ | {Y} | {Y} |  |",
            f"| 拡張ブーフホルツ ψ | {Y} | {Y} |  |\n| BMS | {Y} | {Y} | {Y} |")
        out = self.run_check(ja=ja)
        self.assertEqual(len(out), 2)
        self.assertTrue(all("the audit pairs" in m for m in out))
        self.assertIn('README-ja.md:5: notation: row 1: README.md has "BMS" and '
                      'README-ja.md has "拡張ブーフホルツ ψ", but the audit pairs '
                      '"BMS" with "BMS"', out)

    def test_pairing_unnamed_rows_are_free(self):
        # Rows that the audit does not name may pair freely.
        ja = JA.replace("| Y 数列 |", "| なにか |")
        self.assertEqual(self.run_check(ja=ja), [])


class AuditValidity(unittest.TestCase):
    def assertFatal(self, text, fragment):
        with self.assertRaises(cr.Fatal) as ctx:
            cr.parse_audit(text)
        self.assertIn(fragment, str(ctx.exception))

    def test_valid_with_noise(self):
        a = cr.parse_audit(audit())
        self.assertEqual(a.count, len(GOALS))
        self.assertEqual(a.axioms, ["propext", "Classical.choice", "Quot.sound"])

    def test_empty_axioms(self):
        self.assertEqual(cr.parse_audit(audit(axioms="")).axioms, [])
        text = audit().replace("GOALS-AXIOMS\tpropext,Classical.choice,Quot.sound",
                               "GOALS-AXIOMS")
        self.assertEqual(cr.parse_audit(text).axioms, [])

    def test_sorry(self):
        self.assertFatal(audit(axioms="propext,sorryAx"), "sorryAx")

    def test_begin(self):
        self.assertFatal(audit(begin="GOALS-BEGIN\t2"), "version")
        self.assertFatal(audit(begin="nothing"), "GOALS-BEGIN appears 0")
        self.assertFatal(audit() + "GOALS-BEGIN\t1\n", "GOALS-BEGIN appears 2")

    def test_end_and_count(self):
        self.assertFatal(audit(count=3), "GOALS-END says 3")
        self.assertFatal(audit() + "GOALS-END\t0\n", "GOALS-END appears 2")
        self.assertFatal(audit().replace("GOALS-AXIOMS", "X"), "GOALS-AXIOMS appears 0")

    def test_fields(self):
        self.assertFatal(audit(GOALS + ["GOAL\tnotation\tx"]), "not 9")
        self.assertFatal(audit([goal("table", "r", "a", "b", "", "", "wf", P)]),
                         "unknown table")
        self.assertFatal(audit([goal("notation", "r", "a", "b", "", "", "rank", P)]),
                         "not a column id")
        self.assertFatal(audit([goal("notation", "r", "a", "b", "", "", "wf", "sorry")]),
                         "unknown status")
        self.assertFatal(audit([goal("notation", "r", "a", "", "", "", "wf", P)]),
                         "row label is empty")
        self.assertFatal(audit([goal("ordinal", "r", "a", "b", "c", "d", "rank", P)]),
                         "target label is given")
        self.assertFatal(audit([goal("between", "r", "a", "b", "", "d", "rank", P)]),
                         "target label is empty")
        self.assertFatal(audit([goal("between", "r", "a", "b", "a", "d", "rank", P)]),
                         "is the source")

    def test_one_to_one_labels(self):
        self.assertFatal(audit(notation("r", "BMS", "BMS", P, P)
                               + notation("s", "BMS", "バシク", P, P)),
                         "more than one ja label")
        self.assertFatal(audit(notation("r", "BMS", "BMS", P, P)
                               + notation("s", "Bashicu", "BMS", P, P)),
                         "more than one en label")
        # In the table between, sources and targets are one set of labels.
        self.assertFatal(audit(between("r", ("a", "A"), ("b", "B"), [P] * 6)
                               + between("s", ("b", "X"), ("a", "A"), [P] * 6)),
                         "more than one ja label")
        # The same label in two different tables may be paired differently.
        cr.parse_audit(audit(notation("r", "Y", "Y 数列", P, P)
                             + ordinal("s", "Y", "Y", [P] * 6)))


class ReadmeValidity(unittest.TestCase):
    def assertFatal(self, en, ja, fragment):
        with self.assertRaises(cr.Fatal) as ctx:
            cr.check(audit(), en, ja)
        self.assertIn(fragment, str(ctx.exception))

    def test_missing_table(self):
        en = EN.replace("| from \\\\ to |", "| from / to |")
        self.assertFatal(en, JA, "README.md: the table between is missing")

    def test_table_twice(self):
        ja = JA + "\n| 表記 | 展開の定義 | 整礎性 | 整礎性(非標準) |\n|---|---|---|---|\n"
        self.assertFatal(EN, ja, "the table notation appears 2 times")

    def test_wrong_cell_count(self):
        en = EN.replace(f"| BMS | {Y} | {Y} | {Y} |", f"| BMS | {Y} | {Y} |")
        self.assertFatal(en, JA, "README.md:13: notation: the row has 3 cells")

    def test_label_twice(self):
        ja = JA.replace("| Y 数列 |", "| 1 行の DBMS |")
        self.assertFatal(EN, ja, "appears twice")


class CommandLine(unittest.TestCase):
    def run_main(self, a, en=EN, ja=JA):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "README.md").write_text(en, encoding="utf-8")
            (root / "README-ja.md").write_text(ja, encoding="utf-8")
            (root / "audit.txt").write_text(a, encoding="utf-8")
            out, err = io.StringIO(), io.StringIO()
            with redirect_stdout(out), redirect_stderr(err):
                code = cr.main(["--audit", str(root / "audit.txt"), "--root", d])
            # The script never writes the README files.
            self.assertEqual((root / "README.md").read_text(encoding="utf-8"), en)
            self.assertEqual((root / "README-ja.md").read_text(encoding="utf-8"), ja)
            return code, out.getvalue(), err.getvalue()

    def test_exit_0(self):
        code, out, err = self.run_main(audit())
        self.assertEqual((code, out, err), (0, "", ""))

    def test_exit_1_prints_every_mismatch(self):
        en = EN.replace(f"| BMS | {Y} | {Y} | {Y} |", "| BMS |  |  |  |")
        code, out, err = self.run_main(audit(), en=en)
        self.assertEqual(code, 1)
        self.assertEqual(len(out.splitlines()), 3)
        self.assertEqual(err, "")

    def test_exit_2(self):
        code, out, err = self.run_main(audit(axioms="sorryAx"))
        self.assertEqual(code, 2)
        self.assertEqual(out, "")
        self.assertIn("sorryAx", err)

    def test_exit_2_missing_file(self):
        with tempfile.TemporaryDirectory() as d:
            err = io.StringIO()
            with redirect_stderr(err):
                code = cr.main(["--audit", str(Path(d) / "none.txt"), "--root", d])
            self.assertEqual(code, 2)
            self.assertIn("cannot read", err.getvalue())


def synthesize_audit(en_text, ja_text):
    """An audit that reproduces the marks of two README files, pairing the
    n-th rows. Used to test the parser on the real README files."""
    en = cr.locate_tables(en_text, "en", "README.md")
    ja = cr.locate_tables(ja_text, "ja", "README-ja.md")
    goals = []
    for t in ("notation", "ordinal"):
        for er, jr in zip(en[t].rows, ja[t].rows):
            for c, cell in zip(cr.COLUMNS[t], er.cells[1:]):
                if cr.normalize(cell) == Y:
                    goals.append(goal(t, "R", er.cells[0], jr.cells[0], "", "", c, P))
    en_b, ja_b = en["between"], ja["between"]
    targets = list(zip(en_b.header.cells[1:], ja_b.header.cells[1:]))
    for er, jr in zip(en_b.rows, ja_b.rows):
        for (te, tj), cell in zip(targets, er.cells[1:]):
            cell = cr.normalize(cell)
            if len(cell) == 6:
                goals += between("R", (er.cells[0], jr.cells[0]), (te, tj),
                                 [P if ch == Y else R for ch in cell])
    return audit(goals)


class RealReadme(unittest.TestCase):
    def test_real_readme_parses(self):
        root = Path(__file__).resolve().parent.parent
        try:
            en = (root / "README.md").read_text(encoding="utf-8")
            ja = (root / "README-ja.md").read_text(encoding="utf-8")
        except OSError:
            self.skipTest("README files not found")
        self.assertEqual(cr.check(synthesize_audit(en, ja), en, ja), [])
        self.assertEqual(cr.check(synthesize_audit(EN, JA), EN, JA), [])


if __name__ == "__main__":
    unittest.main()
