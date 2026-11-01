"""Fixed values of maps/trio.py and notation/exb_std.py, taken from the Lean files.

    python3 -m unittest discover -s tests        (from python/trans)

The full comparison with Lean is gen_lean_trio.py.
"""

import os
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

from notation import exb, exb_std  # noqa: E402
from notation.exb import ONE, ZERO, psi  # noqa: E402
from maps import trio  # noqa: E402
from maps.errors import DomainError  # noqa: E402

P = exb.parse


def M(lst):
    return tuple(tuple(c) for c in lst)


def add(*ts):
    return sum(ts, ())


class TestStd(unittest.TestCase):
    # Googology/Notation/ExBuchholz/Std.lean:51-63
    def test_is_ot(self):
        for s in ['0', '1', '2', 'w', 'W', 'p0(W)']:
            self.assertTrue(exb_std.is_ot(P(s)), s)
        self.assertFalse(exb_std.is_ot(P('1+w')))
        self.assertFalse(exb_std.is_ot(P('p0(p0(W))')))

    def test_cmp(self):
        self.assertEqual(exb_std.cmp(P('0'), P('1')), -1)
        self.assertEqual(exb_std.cmp(P('w'), P('w')), 0)
        self.assertEqual(exb_std.cmp(P('W'), P('p0(W)')), 1)
        self.assertEqual(exb_std.cmp(P('2'), P('1')), 1)

    def test_countable(self):
        self.assertTrue(exb_std.is_countable_ot(P('p0(W+1)')))
        self.assertFalse(exb_std.is_countable_ot(P('W')))


class TestTrio(unittest.TestCase):
    def test_small_frag(self):
        # TrioTree.lean:633, TrioFixStripTree.lean:933
        self.assertEqual(len(trio.small_frag(6)), 610)

    def test_omega_index(self):
        # Trio/Trio.lean:111-139 (opowT a = psi nil a)
        t1 = ONE
        w = lambda a: psi(ZERO, a)  # noqa: E731
        cases = [
            (t1, [[0, 0, 0], [1, 1, 0]]),
            (add(t1, t1), [[0, 0, 0], [1, 1, 0], [2, 2, 0]]),
            (w(t1), [[0, 0, 0], [1, 1, 1]]),
            (add(w(t1), t1), [[0, 0, 0], [1, 1, 1], [2, 1, 0], [3, 2, 0]]),
            (add(w(t1), w(t1), t1), [[0, 0, 0], [1, 1, 1], [2, 1, 0], [3, 2, 1], [4, 2, 0],
                                     [5, 3, 0]]),
            (add(w(add(t1, t1)), w(add(t1, t1))),
             [[0, 0, 0], [1, 1, 1], [2, 1, 1], [2, 1, 0], [3, 2, 1], [4, 2, 1]]),
        ]
        for a, m in cases:
            self.assertEqual(trio.omega_index_matrix(a), M(m), exb.show(a))
            self.assertEqual(trio.trio_e2(a), M(m), exb.show(a))     # trioE_allNil

    def test_trio_e2(self):
        # TrioFixStrip.lean:457-464 with trioE2_tα, trioE2_tβ (TrioFixStripTree.lean)
        ta = P('p0(p1(p0(W)))')
        tb = P('p0(p1(p0(W+p0(W+1))))')
        self.assertEqual(trio.trio_e2(ta), M([[0, 0, 0], [1, 1, 1], [2, 1, 1], [3, 0, 0],
                                              [4, 1, 0], [5, 0, 0], [6, 1, 0]]))
        self.assertEqual(trio.trio_e2(tb), M([[0, 0, 0], [1, 1, 1], [2, 1, 1], [3, 0, 0],
                                              [4, 1, 0], [5, 0, 0], [6, 1, 0], [6, 0, 0],
                                              [7, 1, 0], [7, 0, 0]]))
        # e0*w: the sheet row of TrioTree.lean:657 (trioE gives a different matrix)
        self.assertEqual(trio.trio_e2(P('p0(W+1)')),
                         M([[0, 0, 0], [1, 1, 1], [2, 1, 1], [3, 0, 0], [4, 1, 0], [2, 1, 1]]))

    def test_order(self):
        # trioE2_lt_iff on smallFrag 5: the Python lists compare as Lean's lists
        fr = sorted(trio.small_frag(5), key=lambda t: [trio.trio_e2(t)])
        for x, y in zip(fr, fr[1:]):
            self.assertEqual(exb_std.cmp(x, y), -1)

    def test_domain(self):
        self.assertTrue(trio.trio_domain(P('p0(W+1)')))
        self.assertFalse(trio.trio_domain(P('W')))              # not < W
        self.assertFalse(trio.trio_domain(P('p0(W_2)')))        # subscript 2
        self.assertFalse(trio.trio_domain(P('1+w')))            # not standard
        with self.assertRaises(DomainError):
            trio.exb_to_bms3(P('p0(W_2)'))


if __name__ == '__main__':
    unittest.main()
