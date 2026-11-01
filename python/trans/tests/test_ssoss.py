"""Tests of maps/ssoss.py (the SSOSS expansion and the value `o`).

    python3 -m unittest discover -s tests        (from python/trans)

Agreement with Lean on `Seq.fs`, `parse` and `encode` is checked by
gen_lean_ssoss.py. The value `o` is noncomputable in Lean, so it is tested here
against the Lean theorems it must satisfy.
"""

import os
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

from maps import ssoss  # noqa: E402
from maps.errors import DomainError  # noqa: E402
from notation import exb  # noqa: E402
from notation.exb_std import is_ot, lt  # noqa: E402


class TestFs(unittest.TestCase):
    def test_handover_guards(self):
        """The `#guard`s of Notation/SSOSS/System.lean."""
        self.assertEqual(ssoss.fs((0, 0, 1), 2), (0, 0, 0, 0))
        self.assertEqual(ssoss.fs((0, 0, 1, 0, 1), 2), (0, 0, 1, 0, 0, 1, 0, 0))
        self.assertEqual(ssoss.fs((0, 0, 1, 1, 0, 1), 2), (0, 0, 1, 1, 0, 0, 1, 1, 0, 0))
        self.assertEqual(ssoss.fs((0, 0, 1, 1, 1), 3), (0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0))
        self.assertEqual(ssoss.fs((0, 0, 2), 2), (0, 0, 1, 1))
        self.assertEqual(ssoss.fs((0, 0, 1, 0), 4), (0, 0, 1))

    def test_empty(self):
        self.assertEqual(ssoss.fs((), 3), ())


class TestValue(unittest.TestCase):
    def test_small(self):
        cases = {(): '0', (0,): '1', (0, 0): '2', (0, 0, 0): '3', (0, 0, 1): 'w',
                 (0, 0, 1, 0): 'w+1', (0, 0, 1, 0, 1): 'p0(2)', (0, 0, 1, 1): 'p0(w)',
                 (0, 0, 1, 1, 1): 'p0(p0(w))'}
        for s, v in cases.items():
            self.assertEqual(exb.show(ssoss.ssoss_to_exb(s)), v, s)

    def test_tower_below_e0(self):
        """`tower_lt_epsilon`: the generators are below e0."""
        prev = exb.ZERO
        for n in range(8):
            v = ssoss.o(ssoss.gen(n))
            self.assertTrue(lt(v, exb.eps(0)))
            self.assertTrue(lt(prev, v) or n == 0)
            prev = v

    def test_append_zero(self):
        """`o_append_zero`: o (S ++ [0]) = o S + 1."""
        for s in ssoss.standard_forms(range(5), (1, 2, 3), 12, 10):
            self.assertEqual(ssoss.o(s + (0,)), ssoss.add(ssoss.o(s), exb.ONE), s)

    def test_domain(self):
        for s in ((0, 0, 2), (1, 1), (0, 1, 0)):
            with self.assertRaises(DomainError):
                ssoss.ssoss_to_exb(s)


class TestStandard(unittest.TestCase):
    FORMS = ssoss.standard_forms(range(6), (1, 2, 3), 14, 12)

    def test_count(self):
        self.assertGreater(len(self.FORMS), 150)

    def test_domain_holds(self):
        """Every generated standard form passes the checks of `ssoss_to_exb`."""
        for s in self.FORMS:
            t = ssoss.ssoss_to_exb(s)
            self.assertTrue(is_ot(t) and lt(t, exb.eps(0)), s)

    def test_decreasing(self):
        """`Below002.decreasing`: one step makes `o` strictly smaller."""
        for s in self.FORMS:
            for k in (1, 2, 3):
                if s and (s[-1] > 0 or k == 1):
                    self.assertTrue(lt(ssoss.o(ssoss.fs(s, k)), ssoss.o(s)), (s, k))

    def test_encode_parse(self):
        """`binary_encode_exists` with `parse_flat`: encode (parse Y) = (0,0) ++ Y."""
        for s in self.FORMS:
            if len(s) >= 2:
                self.assertEqual(ssoss.encode(ssoss.parse(s[2:])), s)


if __name__ == '__main__':
    unittest.main()
