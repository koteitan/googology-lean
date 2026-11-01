"""Tests of maps/pss.py (pairTerm, pairOrdTerm and pss-proof's Trans).

    python3 -m unittest discover -s tests        (from python/trans)

Agreement with Lean on many matrices is checked by gen_lean_pss.py. The values
below are the Lean `#eval` values.
"""

import os
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

from maps import pss  # noqa: E402
from maps.bms import read  # noqa: E402
from notation import exb  # noqa: E402


class TestPssProofGuards(unittest.TestCase):
    """The regression `#guard`s of pss-proof's PSS/Trans.lean, PSS/Red.lean and PSS/Scb.lean."""

    def test_flat(self):
        B, D = pss.BZERO, pss.dprin
        for t in (B, D(2, D(1, B)), pss.BT((pss.BP(0, B), pss.BP(1, B)))):
            self.assertEqual(pss.unflatBT(pss.flatBT(t)), t)
        self.assertEqual(pss.flatBT(pss.BT((pss.BP(0, B), pss.BP(1, B)))),
                         ('lp', ('d', 0), 'zero', 'cm', ('d', 1), 'zero', 'rp'))

    def test_trans_mark(self):
        B, D = pss.BZERO, pss.dprin
        self.assertEqual(pss.Trans([(1, 1), (2, 2)]), D(1, D(2, B)))
        self.assertEqual(pss.Mark([(1, 1), (2, 2)], 0), D(1, D(2, B)))
        self.assertEqual(pss.Mark([(1, 1), (2, 2)], 1), D(2, B))

    def test_red(self):
        self.assertEqual(pss.Red(((0, 0), (0, 2))), ((0, 0), (2, 2)))
        self.assertEqual(pss.Red(((0, 0), (2, 2))), ((0, 0), (1, 1)))


class TestPairTerm(unittest.TestCase):
    # (matrix, pairTerm, pairOrdTerm), printed as exb
    TABLE = [
        ('(0,0)', '0', '1'),
        ('(0,0)(0,0)', '1', '2'),
        ('(0,0)(1,0)', 'w', 'w'),
        ('(0,0)(1,1)', 'e0', 'e0'),
        ('(0,0)(1,1)(1,1)', 'e1', 'e1'),
        ('(0,0)(1,1)(2,0)', 'p0(p1(1))', 'p0(p1(1))'),
        ('(0,0)(1,1)(2,1)', 'z0', 'z0'),
        ('(0,0)(1,1)(2,2)', 'p0(W_2)', 'p0(W_2)'),
        ('(0,0)(1,1)(2,2)(3,3)', 'p0(W_3)', 'p0(W_3)'),
    ]

    def test_table(self):
        from notation import matrix
        for s, t, o in self.TABLE:
            m = matrix.parse(s, 2)
            self.assertEqual(exb.show(pss.pair_term(m)), t, s)
            self.assertEqual(exb.show(pss.pair_ord_term(m)), o, s)

    def test_empty(self):
        self.assertEqual(pss.pair_ord_term(()), exb.ZERO)

    def test_one_row(self):
        for l in [(0,), (0, 0), (0, 1), (0, 1, 0, 1), (0, 1, 1, 2), (0, 1, 2, 1, 2)]:
            m = tuple((a, 0) for a in l)
            self.assertEqual(pss.pair_ord_term(m), read(0, l), l)

    def test_add_nf(self):
        one, w = exb.ONE, exb.OMEGA
        self.assertEqual(pss.add_nf(one, w), w)
        self.assertEqual(pss.add_nf(w, one), w + one)


if __name__ == '__main__':
    unittest.main()
