"""Unit tests of maps/trio_rules.py against values fixed in the Lean files.

Trio/ is Googology/Trans/ExBuchholz/BMS/Trio/. The full comparison with Lean is
tests/gen_lean_trio_rules.py.
"""

import os
import re
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)

from maps import trio, trio_rules as R  # noqa: E402
from notation import exb  # noqa: E402

TRIO = os.path.join(os.path.dirname(os.path.dirname(ROOT)),
                    'Googology', 'Trans', 'ExBuchholz', 'BMS', 'Trio')

T1 = exb.ONE
TW = exb.BIG_OMEGA
TE0 = exb.eps(0)
W1 = ('W', R.ONE)                     # the exponent .W one


def cons(a, b, t):
    return ((a, b),) + t


def psi(a, b):
    return ((a, b),)


def tower(k):
    """TrioTree.lean:637  towerP."""
    t = ()
    for _ in range(k):
        t = psi((), t)
    return t


def mat(rows):
    return tuple(tuple(c) for c in rows)


class FixedValues(unittest.TestCase):
    def test_t_alpha_beta(self):
        # Trio/TrioFixStrip.lean:457 trioMatrixLSt_tβ, :462 trioMatrixLSt_tα
        ta = psi((), psi(T1, TE0))
        tb = psi((), psi(T1, psi((), cons(T1, (), psi((), cons(T1, (), T1))))))
        self.assertEqual(R.trio_matrix_l_st(tb), mat(
            [[0, 0, 0], [1, 1, 1], [2, 1, 1], [3, 0, 0], [4, 1, 0], [5, 0, 0], [6, 1, 0],
             [6, 0, 0], [7, 1, 0], [7, 0, 0]]))
        self.assertEqual(R.trio_matrix_l_st(ta), mat(
            [[0, 0, 0], [1, 1, 1], [2, 1, 1], [3, 0, 0], [4, 1, 0], [5, 0, 0], [6, 1, 0]]))
        self.assertLess(R.trio_matrix_l_st(ta), R.trio_matrix_l_st(tb))

    def test_strip_e0w(self):
        # Trio/TrioFixStrip.lean:446 e0w, :452 stripSt_e0w
        e0w = ('o', ((('psi', (), ((W1, 1),)), 1), (R.O0, 1)))
        self.assertEqual(R.strip_st(('o', ((e0w, 1),))), ((W1, 1), (e0w, 1)))

    def test_of_term_fix_psi_omega_one(self):
        # Trio/TrioFixOfTerm.lean:237 ofTermFix_psi_Omega_one
        self.assertEqual(R.of_term_fix(psi((), cons(T1, (), T1))),
                         R.wpow(((('psi', (), ((W1, 1),)), 1), (R.O0, 1))))

    def test_p_om_one(self):
        # Trio/TrioFixStripSheet9.lean:107  trioMatrixLSt (pOm t1)
        self.assertEqual(R.trio_matrix_l_st(psi((), cons(T1, (), T1))), mat(
            [[0, 0, 0], [1, 1, 1], [2, 1, 1], [3, 0, 0], [4, 1, 0], [2, 1, 1]]))

    def test_sheet_1h(self):
        # every one-line `#guard trioRuleMatrixOfSt "s" = some [...]` of TrioFixStripSheet1h.lean
        pat = re.compile(r'^#guard trioRuleMatrixOfSt "([^"]*)" = some (\[.*\])\s*$')
        n = 0
        with open(os.path.join(TRIO, 'TrioFixStripSheet1h.lean')) as f:
            for line in f:
                m = pat.match(line)
                if m:
                    want = mat(eval(m.group(2)))
                    self.assertEqual(R.trio_rule_matrix_of_st(m.group(1)), want, m.group(1))
                    n += 1
        self.assertGreaterEqual(n, 30)

    def test_label_none(self):
        # TrioFixStrip.lean:413: `none` when the label does not parse or names 0
        self.assertIsNone(R.trio_rule_matrix_of_st('psi'))
        self.assertIsNone(R.trio_rule_matrix_of_st('0'))


class Fuel(unittest.TestCase):
    """Trio/TrioFixStripCalibNo.lean:92-98: where the fuel 200 runs out."""

    def test_towers(self):
        self.assertEqual(R.trio_matrix_l_st(tower(202)), trio.trio_e2(tower(202)))
        self.assertNotEqual(R.trio_matrix_l_st(tower(203)), trio.trio_e2(tower(203)))
        self.assertNotEqual(R.trio_matrix_l_st(tower(201)), R.trio_matrix_l_st(tower(202)))
        # TrioFixStripCalibNo.lean:63 trioMatrixLSt_T202
        self.assertEqual(R.trio_matrix_l_st(tower(202)), R.trio_matrix_l_st(tower(203)))

    def test_families(self):
        def f1(k):
            return psi((), cons(T1, (), tower(k)))

        def f2(k):
            return psi((), psi(T1, tower(k)))
        for f, k in ((f1, 200), (f2, 198)):
            self.assertEqual(R.trio_matrix_l_st(f(k)), trio.trio_e2(f(k)))
            self.assertNotEqual(R.trio_matrix_l_st(f(k + 1)), trio.trio_e2(f(k + 1)))


class AgreesWithTree(unittest.TestCase):
    def test_small_frag_6(self):
        # TRIO-FIX-STRIP.md: trioMatrixLSt = trioE2 on smallFrag 6 (610 terms)
        f6 = trio.small_frag(6)
        self.assertEqual(len(f6), 610)
        for a in f6:
            self.assertEqual(R.trio_matrix_l_st(a), trio.trio_e2(a), exb.show(a))


if __name__ == '__main__':
    unittest.main()
