"""The notations of `trans` and their system names (notations.md, section 0)."""

import re

from . import exb, inacc, label, matrix, seq, ssoss
from .common import ParseError

ALIASES = {'prim': 'bms1', 'pss': 'bms2', 'trio': 'bms3'}


class System:
    """A notation: its name, how to read a term and how to print one.

    `parse` or `show` is None for a notation that is output-only or input-only.
    """

    def __init__(self, name, title, parse=None, show=None, lean=None):
        self.name = name
        self.title = title
        self.parse = parse
        self.show = show
        self.lean = lean


FIXED = {
    'exb': System('exb', 'extended Buchholz psi', exb.parse, exb.show, exb.lean),
    'ord': System('ord', 'ordinals as the trio sheet labels', label.parse, None, label.lean),
    'inacc': System('inacc', 'psi over w weakly inaccessibles', inacc.parse, inacc.show,
                    inacc.lean),
    'y': System('y', 'Y sequence', seq.parse, seq.show),
    'omegay': System('omegay', 'w-Y sequence', seq.parse, seq.show),
    'ssoss': System('ssoss', 'strong second-order searching sequence, below (0,0,2)',
                    ssoss.parse, ssoss.show, ssoss.lean),
    'por1': System('por1', 'pattern of resemblance of order 1 (R1+)', None, str),
    'por2': System('por2', 'pattern of resemblance of order 2', None, str),
    'wilken1': System('wilken1', "Wilken's theta terms T^1", None, str),
    'wilken2': System('wilken2', "Wilken's R2 terms", None, str),
}

_MATRIX = re.compile(r'(d?bms)([1-9][0-9]*)')


def _show_lean_matrix(m):
    return '[' + ', '.join('[' + ', '.join(str(v) for v in c) + ']' for c in m) + ']'


FAMILIES = ('bms', 'dbms')


def get(name):
    """The system of a name; matrix systems bmsN, dbmsN are made on demand.

    `bms` and `dbms` without N read N from the term (the longest column);
    see `concrete` and `targets`.
    """
    name = ALIASES.get(name, name)
    if name in FIXED:
        return FIXED[name]
    if name in FAMILIES:
        return System(name, '%s, N read from the term' % name.upper(),
                      lambda s: matrix.parse(s, None), matrix.show, _show_lean_matrix)
    m = _MATRIX.fullmatch(name)
    if m:
        rows = int(m.group(2))
        title = '%s with %d row%s' % (m.group(1).upper(), rows, '' if rows == 1 else 's')
        return System(name, title, lambda s: matrix.parse(s, rows), matrix.show,
                      _show_lean_matrix)
    raise KeyError('unknown system %r' % name)


def concrete(name, value):
    """The system name of a parsed term: `bms` and `dbms` get the N of the term."""
    return name + str(matrix.rows_of(value)) if name in FAMILIES else name


def targets(name, src):
    """The output systems to try for `--to name`, in order.

    For `bms` / `dbms` without N: the N of the input first when the input is a
    matrix, then N = 1, 2, 3, ... up to the larger of 3 and that N.
    """
    if name not in FAMILIES:
        return [name]
    m = _MATRIX.fullmatch(src)
    first = int(m.group(2)) if m else None
    out = [name + str(first)] if first else []
    for n in range(1, max(3, first or 0) + 1):
        if name + str(n) not in out:
            out.append(name + str(n))
    return out


def listing():
    """The system names, for `trans --list`."""
    rows = [('bmsN', 'BMS with N rows (bms1 = prim, bms2 = pss, bms3 = trio)', 'in, out'),
            ('dbmsN', 'DBMS with N rows', 'in, out'),
            ('bms', 'BMS, N read from the term (the longest column)', 'in, out'),
            ('dbms', 'DBMS, N read from the term (the longest column)', 'in, out')]
    for s in FIXED.values():
        io = ', '.join(x for x, f in (('in', s.parse), ('out', s.show)) if f)
        rows.append((s.name, s.title, io))
    return rows


__all__ = ['ParseError', 'System', 'concrete', 'get', 'listing', 'targets']
