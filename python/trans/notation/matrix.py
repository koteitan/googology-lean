"""Matrices: bmsN and dbmsN (notations.md, section 1).

A matrix is a tuple of columns; a column is a tuple of N naturals, from the
top row (row 0) down. This is the Lean list state `List (List Nat)`.
"""

import json
import re

from .common import ParseError, strip_spaces

_COLS = re.compile(r'(\([0-9]+(,[0-9]+)*\))*')
_BARE = re.compile(r'[0-9]+(,[0-9]+)*')


def parse(s, rows):
    """Read a matrix with `rows` rows."""
    t = strip_spaces(s)
    what = 'matrix with %d row%s' % (rows, '' if rows == 1 else 's')
    if t in ('', '()'):
        return ()
    if t.startswith('['):
        cols = _parse_lean(t, rows, what)
    elif t.startswith('('):
        if not _COLS.fullmatch(t):
            raise ParseError('%s: not a list of columns: %r' % (what, s))
        cols = [tuple(int(v) for v in c.split(','))
                for c in re.findall(r'\(([^()]*)\)', t)]
    elif _BARE.fullmatch(t):
        if rows != 1:
            raise ParseError('%s: every column must be in parentheses: %r' % (what, s))
        cols = [(int(v),) for v in t.split(',')]
    else:
        raise ParseError('%s: cannot read %r' % (what, s))
    for c in cols:
        if len(c) != rows:
            raise ParseError('%s: the column %s has %d entries' % (what, show_col(c), len(c)))
    return tuple(cols)


def _parse_lean(t, rows, what):
    try:
        v = json.loads(t)
    except ValueError:
        raise ParseError('%s: not a Lean list: %r' % (what, t)) from None
    if not isinstance(v, list):
        raise ParseError('%s: not a Lean list: %r' % (what, t))
    if rows == 1 and all(isinstance(x, int) for x in v):
        v = [[x] for x in v]
    cols = []
    for c in v:
        if not (isinstance(c, list) and all(isinstance(x, int) and x >= 0 for x in c)):
            raise ParseError('%s: not a list of columns of naturals: %r' % (what, t))
        cols.append(tuple(c))
    return cols


def show_col(c):
    return '(' + ','.join(str(v) for v in c) + ')'


def show(m):
    """The canonical form: `(0,0)(1,1)`, and `()` for the empty matrix."""
    return ''.join(show_col(c) for c in m) if m else '()'
