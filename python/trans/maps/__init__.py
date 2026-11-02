"""The maps of `trans`, as edges of a graph between the systems.

A conversion from A to B follows a path of edges. The paths are tried from the
shortest; the first one whose every edge accepts its input gives the result.
An edge refuses an input outside its domain by raising DomainError.
"""

import re

from . import bms, por, pss, ssoss, trio, trio_rules
from notation import exb
from notation.exb_std import is_ot, lt
from .errors import DomainError


def psi0_omega_index(x):
    """alpha if x is p0(W_alpha) = psi_0(psi_alpha(0)) with alpha != 0, else DomainError."""
    if len(x) == 1 and x[0][0] == () and len(x[0][1]) == 1:
        alpha, inner = x[0][1][0]
        if inner == () and alpha != ():
            return alpha
    raise DomainError('trioE2: the term is not of the form p0(W_a)')


def exb_to_bms3(x):
    """The trio matrix of x = p0(W_alpha): trioE2 alpha, on the proved domain of trioE2."""
    return trio.exb_to_bms3(psi0_omega_index(x))


PSI0_OMEGA_OMEGA = exb.psi((), exb.omega_sub(exb.OMEGA))   # p0(W_w)


def bms2_to_exb(m):
    """pairOrdTerm, the value of a pair sequence.

    Its proved domain is the standard pair sequences (CTPS). There is no
    computable test of CTPS in Lean, so only the necessary conditions are
    checked: the first column is (0,0), and the value is a standard form below
    p0(W_w) (Googology/Trans/BMS/ExBuchholz/PSS/Rank.lean, `pairTerm_mem`).
    """
    if not m:
        return exb.ZERO
    if m[0] != (0, 0):
        raise DomainError('pairOrdTerm: the first column is not (0,0)')
    t = pss.pair_ord_term(m)
    if not (is_ot(t) and lt(t, PSI0_OMEGA_OMEGA)):
        raise DomainError('pairOrdTerm: not a standard pair sequence (the value is not a '
                          'standard form below p0(W_w))')
    return t


class Edge:
    def __init__(self, src, dst, fn, name, lean, wide=False):
        self.src = src
        self.dst = dst
        self.fn = fn
        self.name = name      # the name of the Lean map (or the program)
        self.lean = lean      # where it is defined
        self.wide = wide      # calibrated by #guard only, not proved; used with --wide

    def __repr__(self):
        return '%s -> %s (%s)' % (self.src, self.dst, self.name)


FIXED = [
    Edge('dbms1', 'bms1', lambda m: m, 'l1ToPrim',
         'Googology/Trans/DBMS/BMS/OneRowL.lean:113'),
    Edge('bms1', 'dbms1', lambda m: m, 'primToL1',
         'Googology/Trans/DBMS/BMS/OneRowL.lean:116'),
    Edge('bms1', 'exb', bms.bms1_to_exb, 'read 0',
         'Googology/Trans/BMS/ExBuchholz/Basic.lean:49'),
    Edge('exb', 'bms1', bms.exb_to_bms1, 'unread 0',
         'Googology/Trans/BMS/ExBuchholz/Basic.lean:197'),
    Edge('bms2', 'exb', bms2_to_exb, 'pairOrdTerm',
         'Googology/Trans/BMS/ExBuchholz/PSS/Rank.lean:344'),
    Edge('exb', 'bms3', exb_to_bms3, 'trioE2',
         'Googology/Trans/ExBuchholz/BMS/Trio/TrioFixStripTree.lean:113'),
    Edge('ssoss', 'exb', ssoss.ssoss_to_exb, 'o',
         'Googology/Notation/SSOSS/SequenceOrdinal.lean:17'),
    Edge('bms2', 'por1', por.bms2_to_por1, 'phi.py',
         'Googology/Trans/BMS/PoR/PSS/por/phi.py'),
    Edge('bms2', 'wilken1', por.bms2_to_wilken1, 'tr.py (= trNode)',
         'Googology/Trans/BMS/PoR/PSS/por/tr.py'),
    Edge('bms3', 'por2', por.bms3_to_por2, 'phi3def2.py',
         'Googology/Trans/BMS/PoR/Trio/por/phi3def2.py'),
    Edge('bms3', 'wilken2', por.bms3_to_wilken2, 'tr3.py',
         'Googology/Trans/BMS/PoR/Trio/por/tr3.py'),
]

def exb_to_bms3_wide(x):
    """The rule program trioMatrixLSt on x = p0(W_alpha), alpha standard.

    Calibrated by #guard only: it equals trioE2 where trioE2 is proved, but its
    agreement with trioE2 in general (CalibSt) is open, and it fails beyond
    reading depth 200 (the towers T_202 and T_203 get the same matrix).
    """
    alpha = psi0_omega_index(x)
    if not is_ot(alpha):
        raise DomainError('trioMatrixLSt: the index is not standard (isOT)')
    return trio_rules.trio_matrix_l_st(alpha)


def ord_to_bms3(od):
    """The rule program trioRuleMatrixSt on a sheet label a, read as p0(W_a)."""
    if not od:
        raise DomainError('trioRuleMatrixSt: the label names 0')
    return trio_rules.trio_rule_matrix_st(od)


WIDE = [
    Edge('exb', 'bms3', exb_to_bms3_wide, 'trioMatrixLSt',
         'Googology/Trans/ExBuchholz/BMS/Trio/TrioFixStrip.lean:422', wide=True),
    Edge('ord', 'bms3', ord_to_bms3, 'trioRuleMatrixSt',
         'Googology/Trans/ExBuchholz/BMS/Trio/TrioFixStrip.lean:410', wide=True),
]

_ROWS = re.compile(r'd?bms([1-9][0-9]*)')


def edges(max_rows, wide=False):
    """Every edge, with the matrix families cut at `max_rows` rows.

    The zeroRow edges come first, so that among paths of the same length the
    one through matrices only is tried first.
    """
    out = []
    for r in range(1, max_rows):
        out.append(Edge('bms%d' % r, 'bms%d' % (r + 1), bms.zero_row,
                        'toPairS' if r == 1 else 'zeroRow',
                        'Googology/Trans/BMS/BMS/ZeroRow.lean:38'))
        out.append(Edge('dbms%d' % r, 'dbms%d' % (r + 1), bms.zero_row, 'zeroRow',
                        'Googology/Trans/DBMS/DBMS/ZeroRow.lean:168'))
    out += FIXED
    if wide:
        out += WIDE
    return out


def _rows(name):
    m = _ROWS.fullmatch(name)
    return int(m.group(1)) if m else 0


def paths(src, dst, limit=8, wide=False):
    """The simple paths from src to dst, shortest first; among paths of one
    length, those without wide edges first."""
    es = edges(max(3, _rows(src), _rows(dst)), wide)
    out = []
    frontier = [(src, [])]
    for _ in range(limit + 1):
        nxt = []
        for node, path in frontier:
            if node == dst:
                out.append(path)
                continue
            seen = {src} | {e.dst for e in path}
            for e in es:
                if e.src == node and e.dst not in seen:
                    nxt.append((e.dst, path + [e]))
        frontier = nxt
    return sorted(out, key=lambda p: (len(p), sum(e.wide for e in p)))


def convert(src, dst, term, wide=False):
    """Convert `term` of system src to system dst. Returns (value, path)."""
    ps = paths(src, dst, wide=wide)
    if not ps:
        if not wide and paths(src, dst, wide=True):
            raise DomainError('no map from %s to %s without --wide' % (src, dst))
        raise DomainError('no map from %s to %s' % (src, dst))
    errors = []
    for path in ps:
        x = term
        try:
            for e in path:
                x = e.fn(x)
        except DomainError as err:
            errors.append('%s: %s' % (' -> '.join([src] + [e.dst for e in path]), err))
            continue
        return x, path
    raise DomainError('every path failed:\n  ' + '\n  '.join(errors))


__all__ = ['DomainError', 'Edge', 'convert', 'edges', 'paths']
