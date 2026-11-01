#!/usr/bin/env python3
"""Write a Lean file whose `#guard`s say that the Python parsers agree with Lean.

    python3 tests/gen_lean_check.py > Check.lean
    leanman check -C <the Lean project> Check.lean

- ord: every label string in Googology/Trans/ExBuchholz/BMS/Trio/ is read by the
  Lean `TrioRules.parse` and by `notation.label.parse`; the two values must be
  equal (`none` on both sides when the label does not parse).
- exb: the shorthands are compared with the named Lean terms (te0, tzeta0, ...).
- inacc: the printed Lean values must elaborate as `InaccPsi.Term`.
- read / unread / zeroRow (maps/bms.py): on every list with `Col 0` up to
  length 7, Lean `read 0`, `unread 0 (read 0 l)` and `zeroRow` agree with Python.
"""

import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)

from notation import ParseError, exb, inacc, label  # noqa: E402
from maps import bms  # noqa: E402

REPO = os.path.dirname(os.path.dirname(ROOT))
TRIO = os.path.join(REPO, 'Googology', 'Trans', 'ExBuchholz', 'BMS', 'Trio')

# exb input, and the Lean term it must be. Names from Notation/ExBuchholz/Order.lean,
# Trans/BMS/ExBuchholz/{Basic,Eps0,Zeta}.lean and PSS/{Terms,Rank}.lean.
EXB = [
    ('0', 'Term.nil'),
    ('1', 't1'),
    ('3', 'Term.numeral 3'),
    ('W', 'tW'),
    ('w', 'Googology.Trans.BMS.tw'),
    ('e0', 'Googology.Trans.BMS.te0'),
    ('p0(W)', 'Googology.Trans.BMS.te0'),
    ('e1', 'Googology.Trans.BMS.te1'),
    ('z0', 'Googology.Trans.BMS.tzeta0'),
    ('W_w', 'Googology.Trans.PSS.tOmegaW'),
    ('p0(W_w)', 'Googology.Trans.PSS.psiOmegaOmega'),
]

INACC = ['0', '2', 'w', 'W_w', 'I_w+I_3', 'phi(1,W)', 'pS_(w+1)(I_2)', 'pI_0(W_2+1)',
         '(1+1)+w']


def labels():
    seen = set()
    pat = re.compile(r'(?:parse|ruleOf|parseM)\s+"([^"\\]*)"')
    for name in sorted(os.listdir(TRIO)):
        if name.endswith('.lean'):
            with open(os.path.join(TRIO, name)) as f:
                for s in pat.findall(f.read()):
                    if s not in seen:
                        seen.add(s)
                        yield s


def col_lists(n):
    """Every list with Col 0 (start 0, never below 0, rise <= 1) of length <= n."""
    out = [()]
    level = [(0,)]
    for _ in range(n):
        out += level
        level = [l + (y,) for l in level for y in range(0, l[-1] + 2)]
    return out


def main():
    out = ['import Googology.Trans.ExBuchholz.BMS.Trio.TrioRules',
           'import Googology.Trans.BMS.ExBuchholz.Zeta',
           'import Googology.Trans.BMS.ExBuchholz.PSS.Rank',
           'import Googology.Notation.InaccPsi.Term',
           'import Googology.Trans.BMS.BMS.ZeroRow',
           '',
           'open Googology.Trans.BMS.TrioRules',
           'open Googology.Notation.ExBuchholz Googology.Notation.ExBuchholz.Term',
           '',
           '-- ord: Python label.parse = Lean TrioRules.parse']
    n = 0
    for s in labels():
        try:
            v = 'some %s' % label.lean(label.parse(s))
        except ParseError:
            v = 'none'
        out.append('#guard Googology.Trans.BMS.TrioRules.parse "%s" == (%s : Option Od)' % (s, v))
        n += 1
    out += ['', '-- exb: Python exb.parse = the named Lean terms']
    for s, t in EXB:
        out.append('#guard (%s : Term) = %s  -- %s' % (exb.lean(exb.parse(s)), t, s))
    out += ['', '-- inacc: the Python values elaborate']
    for s in INACC:
        out.append('#check (%s : Googology.Notation.InaccPsi.Term)  -- %s'
                   % (inacc.lean(inacc.parse(s)), s))
    out += ['', '-- read / unread / zeroRow']
    k = 0
    for l in col_lists(7):
        ll = '[' + ','.join(map(str, l)) + ']'
        out.append('#guard Googology.Trans.BMS.read 0 %s = (%s : Term)'
                   % (ll, exb.lean(bms.read(0, l))))
        out.append('#guard Googology.Trans.BMS.unread 0 (Googology.Trans.BMS.read 0 %s) = %s'
                   % (ll, '[' + ','.join(map(str, bms.unread(0, bms.read(0, l)))) + ']'))
        m = tuple((a, a % 2) for a in l)
        out.append('#guard Googology.Trans.BMS.zeroRow %s = %s'
                   % ('[' + ','.join('[%d,%d]' % c for c in m) + ']',
                      '[' + ','.join('[%d,%d,0]' % c for c in m) + ']'))
        assert bms.zero_row(m) == tuple(c + (0,) for c in m)
        k += 1
    print('\n'.join(out))
    print('-- %d lists' % k, file=sys.stderr)
    print('-- %d labels' % n, file=sys.stderr)


if __name__ == '__main__':
    main()
