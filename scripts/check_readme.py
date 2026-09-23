#!/usr/bin/env python3
"""Check that the tables of README.md and README-ja.md agree with the audit.

This is the script of spec.md, section 7.8.

    python3 scripts/check_readme.py --audit audit.txt [--root DIR]

The audit is the standard output of test/GoalsAudit.lean (spec.md 7.7). The
script reads the audit and the two README files and writes none. It never
changes a README. It does not run Lean.

Exit codes:
  0  the audit is valid and both files agree with it
  1  at least one mismatch (printed on standard output, one per line)
  2  the files cannot be compared (the reason goes to standard error)

Python 3 standard library only.
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

# ---------------------------------------------------------------------------
# Constants of spec.md 7.4, 7.7 and 7.8

AUDIT_VERSION = "1"

TABLES = ("notation", "ordinal", "between")

# The column ids of each table, in the order of the README columns (for
# `between`: the order of the six marks of a cell).
COLUMNS = {
    "notation": ("expansion", "wf", "wf-nonstd"),
    "ordinal": ("defined", "injective", "surjective", "decreasing", "rank", "order"),
    "between": ("defined", "preserves", "commutes", "injective", "surjective", "rank"),
}

STATUSES = ("proved", "refuted", "open")

ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})

LANGS = ("en", "ja")

FILES = {"en": "README.md", "ja": "README-ja.md"}

# The header rows by which the tables are found, as in the Markdown source.
# For `notation` and `ordinal`: the whole header row.
# For `between`: the first header cell only.
HEADERS = {
    "en": {
        "notation": ("notation", "expansion defined", "well-foundedness",
                     "well-foundedness (non-standard)"),
        "ordinal": ("notation", "defined", "injective", "surjective",
                    "decreases on expansion", "equals the rank", "order-preserving"),
        "between": "from \\\\ to",  # two backslashes, as in the source
    },
    "ja": {
        "notation": ("表記", "展開の定義", "整礎性", "整礎性(非標準)"),
        "ordinal": ("表記", "定義", "単射性", "全射性", "展開で値が下がる",
                    "階数と一致", "順序を保つ"),
        "between": "翻訳元＼翻訳先",  # U+FF3C
    },
}

PROVED_MARK = "✅"   # ✅
REFUTED_MARK = "❌"  # ❌
DIAGONAL = "—"      # —
VS16 = "️"          # emoji variation selector

DELIMITER_CELL = re.compile(r":?-+:?")


class Fatal(Exception):
    """The files cannot be compared (exit 2)."""


# ---------------------------------------------------------------------------
# The audit

@dataclass
class AuditTable:
    """What the audit says about one table, for one language."""
    # notation, ordinal: row label -> column id -> statuses
    # between: source label -> target label -> column id -> statuses
    marks: dict = field(default_factory=dict)
    # between only: the target labels
    targets: set = field(default_factory=set)
    # the label of this language -> the label of the other language
    pair: dict = field(default_factory=dict)


@dataclass
class Audit:
    # lang -> table -> AuditTable
    tables: dict
    axioms: list
    count: int


def parse_audit(text: str) -> Audit:
    """Read the audit output of spec.md 7.7. Raise Fatal if it is not valid."""
    begins, ends, axioms_lines, goals = [], [], [], []
    for number, raw in enumerate(text.splitlines(), 1):
        line = raw.rstrip("\r\n")
        fields = line.split("\t")
        kind = fields[0]
        if kind == "GOALS-BEGIN":
            begins.append((number, fields))
        elif kind == "GOALS-END":
            ends.append((number, fields))
        elif kind == "GOALS-AXIOMS":
            axioms_lines.append((number, fields))
        elif kind == "GOAL":
            goals.append((number, fields))

    if len(begins) != 1:
        raise Fatal(f"audit: GOALS-BEGIN appears {len(begins)} times, not once")
    number, fields = begins[0]
    if len(fields) != 2 or fields[1] != AUDIT_VERSION:
        raise Fatal(f"audit line {number}: GOALS-BEGIN must have version "
                    f"{AUDIT_VERSION}, found {line_repr(fields[1:])}")
    if len(ends) != 1:
        raise Fatal(f"audit: GOALS-END appears {len(ends)} times, not once")
    number, fields = ends[0]
    if len(fields) != 2 or not re.fullmatch(r"[0-9]+", fields[1]):
        raise Fatal(f"audit line {number}: GOALS-END must have one number, "
                    f"found {line_repr(fields[1:])}")
    if int(fields[1]) != len(goals):
        raise Fatal(f"audit line {number}: GOALS-END says {int(fields[1])} "
                    f"GOAL lines, but there are {len(goals)}")
    if len(axioms_lines) != 1:
        raise Fatal(f"audit: GOALS-AXIOMS appears {len(axioms_lines)} times, not once")
    number, fields = axioms_lines[0]
    if len(fields) > 2:
        raise Fatal(f"audit line {number}: GOALS-AXIOMS must have one field "
                    f"after the keyword, found {len(fields) - 1}")
    axioms = fields[1].split(",") if len(fields) == 2 and fields[1] != "" else []
    bad = [a for a in axioms if a not in ALLOWED_AXIOMS]
    if bad:
        raise Fatal(f"audit line {number}: the records use axioms outside "
                    f"propext, Classical.choice, Quot.sound: {', '.join(bad)}")

    tables = {lang: {t: AuditTable() for t in TABLES} for lang in LANGS}
    # table -> lang -> label -> the set of labels of the other language
    pairs = {t: {lang: {} for lang in LANGS} for t in TABLES}

    for number, fields in goals:
        where = f"audit line {number}"
        if len(fields) != 9:
            raise Fatal(f"{where}: a GOAL line has {len(fields)} fields, not 9")
        _, table, _record, row_en, row_ja, tgt_en, tgt_ja, column, status = fields
        if table not in TABLES:
            raise Fatal(f"{where}: unknown table {line_repr([table])}")
        if column not in COLUMNS[table]:
            raise Fatal(f"{where}: {line_repr([column])} is not a column id "
                        f"of the table {table}")
        if status not in STATUSES:
            raise Fatal(f"{where}: unknown status {line_repr([status])}")
        if row_en == "" or row_ja == "":
            raise Fatal(f"{where}: a row label is empty")
        if table == "between":
            if tgt_en == "" or tgt_ja == "":
                raise Fatal(f"{where}: a target label is empty in the table between")
            if tgt_en == row_en:
                raise Fatal(f"{where}: the target {line_repr([tgt_en])} is the source")
        elif tgt_en != "" or tgt_ja != "":
            raise Fatal(f"{where}: a target label is given in the table {table}")

        labels = [(row_en, row_ja)]
        if table == "between":
            labels.append((tgt_en, tgt_ja))
        for en, ja in labels:
            pairs[table]["en"].setdefault(en, set()).add(ja)
            pairs[table]["ja"].setdefault(ja, set()).add(en)

        for lang, row, tgt in (("en", row_en, tgt_en), ("ja", row_ja, tgt_ja)):
            at = tables[lang][table]
            if table == "between":
                at.targets.add(tgt)
                cell = at.marks.setdefault(row, {}).setdefault(tgt, {})
            else:
                cell = at.marks.setdefault(row, {})
            cell.setdefault(column, []).append(status)

    for table in TABLES:
        for lang in LANGS:
            other = "ja" if lang == "en" else "en"
            for label, others in pairs[table][lang].items():
                if len(others) > 1:
                    names = ", ".join(line_repr([o]) for o in sorted(others))
                    raise Fatal(f"audit: in the table {table}, the {lang} label "
                                f"{line_repr([label])} goes with more than one "
                                f"{other} label: {names}")
                tables[lang][table].pair[label] = next(iter(others))

    return Audit(tables=tables, axioms=axioms, count=len(goals))


def expected_mark(at: AuditTable, table: str, row: str, target: str | None = None) -> str:
    """The mark of spec.md 7.5, in normalized form."""
    if table == "between":
        if row == target:
            return DIAGONAL
        cell = at.marks.get(row, {}).get(target)
        if cell is None:
            return ""
        return "".join(
            PROVED_MARK if all_proved(cell.get(c, [])) else REFUTED_MARK
            for c in COLUMNS["between"])
    cell = at.marks.get(row, {})
    return PROVED_MARK if all_proved(cell.get(target, [])) else ""


def all_proved(statuses: list) -> bool:
    return bool(statuses) and all(s == "proved" for s in statuses)


# ---------------------------------------------------------------------------
# The README

@dataclass
class Row:
    line: int      # 1-based line number in the file
    cells: list    # cells, spaces at both ends removed


@dataclass
class Table:
    header: Row
    rows: list     # of Row, without the delimiter line


def split_cells(line: str) -> list:
    """Split a table line into cells as spec.md 7.8 says."""
    body = line[1:] if line.startswith("|") else line
    if body.endswith("|"):
        body = body[:-1]
    return [c.strip(" \t") for c in body.split("|")]


def find_tables(text: str) -> list:
    """All tables of a Markdown text, outside fenced code blocks."""
    lines = []  # (line number, text) outside fenced code blocks
    fenced = False
    for number, raw in enumerate(text.splitlines(), 1):
        line = raw.rstrip("\r\n")
        if line.startswith("```"):
            fenced = not fenced
            lines.append((number, None))  # a fence line ends a table
            continue
        lines.append((number, None if fenced else line))

    tables = []
    i = 0
    while i < len(lines):
        number, line = lines[i]
        if line is not None and line.startswith("|") and i + 1 < len(lines):
            _, delim = lines[i + 1]
            if (delim is not None and delim.startswith("|")
                    and all(DELIMITER_CELL.fullmatch(c) for c in split_cells(delim))):
                table = Table(header=Row(number, split_cells(line)), rows=[])
                j = i + 2
                while j < len(lines):
                    n, l = lines[j]
                    if l is None or not l.startswith("|"):
                        break
                    table.rows.append(Row(n, split_cells(l)))
                    j += 1
                tables.append(table)
                i = j
                continue
        i += 1
    return tables


def locate_tables(text: str, lang: str, name: str) -> dict:
    """The three tables of one README, by their header rows. Raise Fatal if a
    table is missing, appears twice, has a row of the wrong length, or has a
    label twice."""
    found = {t: [] for t in TABLES}
    for table in find_tables(text):
        cells = tuple(table.header.cells)
        for t in ("notation", "ordinal"):
            if cells == HEADERS[lang][t]:
                found[t].append(table)
        if cells and cells[0] == HEADERS[lang]["between"]:
            found["between"].append(table)

    result = {}
    for t in TABLES:
        if not found[t]:
            raise Fatal(f"{name}: the table {t} is missing")
        if len(found[t]) > 1:
            lines = ", ".join(str(x.header.line) for x in found[t])
            raise Fatal(f"{name}: the table {t} appears {len(found[t])} times "
                        f"(lines {lines})")
        table = found[t][0]
        width = len(table.header.cells)
        seen = {}
        for row in table.rows:
            if len(row.cells) != width:
                raise Fatal(f"{name}:{row.line}: {t}: the row has "
                            f"{len(row.cells)} cells, the header has {width}")
            label = row.cells[0]
            if label in seen:
                raise Fatal(f"{name}:{row.line}: {t}: the label "
                            f"{line_repr([label])} appears twice (also line "
                            f"{seen[label]})")
            seen[label] = row.line
        result[t] = table
    return result


def normalize(cell: str) -> str:
    return cell.replace(" ", "").replace(VS16, "")


def allowed(table: str, cell: str) -> bool:
    if table == "between":
        return (cell in ("", DIAGONAL)
                or (len(cell) == 6 and all(ch in (PROVED_MARK, REFUTED_MARK) for ch in cell)))
    return cell in ("", PROVED_MARK)


# ---------------------------------------------------------------------------
# The comparison

def line_repr(values: list) -> str:
    return ", ".join('"' + v + '"' for v in values)


def check_file(tables: dict, audit: Audit, lang: str, name: str) -> list:
    """Mismatches 1 to 4 of spec.md 7.8, for one file."""
    out = []
    for t in TABLES:
        table = tables[t]
        at = audit.tables[lang][t]
        labels = [row.cells[0] for row in table.rows]
        head = table.header.line

        # 3. rows (and targets) that the audit names but the table lacks
        for label in sorted(set(at.marks) - set(labels)):
            out.append(f'{name}:{head}: {t}: row "{label}": not in the table')
        if t == "between":
            targets = table.header.cells[1:]
            for label in sorted(at.targets - set(targets)):
                out.append(f'{name}:{head}: {t}: target "{label}": not a column header')
            # 4. the column headers are the row labels in the same order
            if targets != labels:
                out.append(f"{name}:{head}: {t}: the column headers are not the "
                           f"row labels in the same order: headers "
                           f"[{line_repr(targets)}], rows [{line_repr(labels)}]")

        for row in table.rows:
            label = row.cells[0]
            if t == "between":
                columns = [(tgt, None) for tgt in table.header.cells[1:]]
            else:
                columns = [(None, c) for c in COLUMNS[t]]
            for (tgt, column), raw in zip(columns, row.cells[1:]):
                found = normalize(raw)
                where = f'{name}:{row.line}: {t}: row "{label}"'
                if tgt is not None:
                    where += f': target "{tgt}"'
                # 1. allowed forms
                if not allowed(t, found):
                    col = f": column {column}" if column else ""
                    out.append(f'{where}{col}: not an allowed form: found "{raw}"')
                    continue
                # 2. and 4. (diagonal): the mark of 7.5
                if t == "between":
                    expected = expected_mark(at, t, label, tgt)
                    if expected == found:
                        continue
                    if len(expected) == 6 and len(found) == 6:
                        for c, e, f in zip(COLUMNS["between"], expected, found):
                            if e != f:
                                out.append(f'{where}: column {c}: expected "{e}", found "{f}"')
                    else:
                        out.append(f'{where}: cell: expected "{expected}", found "{found}"')
                else:
                    expected = expected_mark(at, t, label, column)
                    if expected != found:
                        out.append(f'{where}: column {column}: expected '
                                   f'"{expected}", found "{found}"')
    return out


def check_pair(en_tables: dict, ja_tables: dict, audit: Audit) -> list:
    """Mismatches 5 and 6 of spec.md 7.8, between the two files."""
    out = []
    en_name, ja_name = FILES["en"], FILES["ja"]
    for t in TABLES:
        en_rows, ja_rows = en_tables[t].rows, ja_tables[t].rows
        # 5. the same number of rows
        if len(en_rows) != len(ja_rows):
            out.append(f"{ja_name}:{ja_tables[t].header.line}: {t}: "
                       f"{len(ja_rows)} rows, but {en_name} has {len(en_rows)} "
                       f"rows (line {en_tables[t].header.line})")
            continue
        # 6. the n-th rows are one row
        en2ja = audit.tables["en"][t].pair
        ja2en = audit.tables["ja"][t].pair
        for n, (er, jr) in enumerate(zip(en_rows, ja_rows), 1):
            le, lj = er.cells[0], jr.cells[0]
            if le in en2ja and en2ja[le] != lj:
                out.append(f'{ja_name}:{jr.line}: {t}: row {n}: {en_name} has '
                           f'"{le}" and {ja_name} has "{lj}", but the audit '
                           f'pairs "{le}" with "{en2ja[le]}"')
            elif lj in ja2en and ja2en[lj] != le:
                out.append(f'{ja_name}:{jr.line}: {t}: row {n}: {en_name} has '
                           f'"{le}" and {ja_name} has "{lj}", but the audit '
                           f'pairs "{lj}" with "{ja2en[lj]}"')
    return out


def check(audit_text: str, en_text: str, ja_text: str) -> list:
    """All mismatches. Raise Fatal if the files cannot be compared."""
    audit = parse_audit(audit_text)
    en_tables = locate_tables(en_text, "en", FILES["en"])
    ja_tables = locate_tables(ja_text, "ja", FILES["ja"])
    return (check_file(en_tables, audit, "en", FILES["en"])
            + check_file(ja_tables, audit, "ja", FILES["ja"])
            + check_pair(en_tables, ja_tables, audit))


# ---------------------------------------------------------------------------
# Command line

def read_text(path: str) -> str:
    try:
        if path == "-":
            return sys.stdin.buffer.read().decode("utf-8")
        return Path(path).read_bytes().decode("utf-8")
    except (OSError, UnicodeDecodeError) as e:
        raise Fatal(f"cannot read {path}: {e}") from e


def main(argv: list | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Check that the tables of README.md and README-ja.md "
                    "agree with the audit of test/GoalsAudit.lean (spec.md 7.8).")
    parser.add_argument("--audit", required=True, metavar="FILE",
                        help="a file holding the audit output; - reads standard input")
    parser.add_argument("--root", metavar="DIR",
                        default=str(Path(__file__).resolve().parent.parent),
                        help="the directory holding README.md and README-ja.md "
                             "(default: the parent of the directory of this script)")
    args = parser.parse_args(argv)

    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(encoding="utf-8")
        except (AttributeError, ValueError):
            pass

    try:
        audit_text = read_text(args.audit)
        root = Path(args.root)
        en_text = read_text(str(root / FILES["en"]))
        ja_text = read_text(str(root / FILES["ja"]))
        mismatches = check(audit_text, en_text, ja_text)
    except Fatal as e:
        print(f"check_readme: {e}", file=sys.stderr)
        return 2

    for m in mismatches:
        print(m)
    return 1 if mismatches else 0


if __name__ == "__main__":
    sys.exit(main())
