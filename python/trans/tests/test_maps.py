"""Tests of the maps and of the path search (maps/).

Agreement with Lean is checked by gen_lean_check.py.
"""

import os
import random
import subprocess
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

import maps  # noqa: E402
from maps import DomainError, bms  # noqa: E402
from notation import exb  # noqa: E402
from test_notation import random_exb  # noqa: E402
from gen_lean_check import col_lists  # noqa: E402


def zero_subs(rng, depth):
    """A random term whose subscripts are all 0."""
    t = random_exb(rng, depth)

    def strip(t):
        return tuple(((), strip(x)) for _, x in t)
    return strip(t)


class TestBms(unittest.TestCase):
    def test_read(self):
        E = exb.parse
        for s, want in [((), '0'), ((0,), '1'), ((0, 0), '2'), ((0, 1), 'w'),
                        ((0, 1, 1), 'p0(2)'), ((0, 1, 2), 'p0(w)'),
                        ((0, 1, 2, 1, 2), 'p0(w+w)')]:
            self.assertEqual(bms.read(0, s), E(want), s)

    def test_unread_read(self):
        """Lean `unread_read`: unread inverts read on the lists with Col 0."""
        for l in col_lists(8):
            self.assertEqual(bms.unread(0, bms.read(0, l)), l)

    def test_read_unread(self):
        """Lean `read_unread`: read inverts unread on the terms with zero subscripts."""
        rng = random.Random(3)
        for _ in range(2000):
            t = zero_subs(rng, 4)
            self.assertEqual(bms.read(0, bms.unread(0, t)), t)

    def test_domain(self):
        with self.assertRaises(DomainError):
            bms.bms1_to_exb(((1,),))
        with self.assertRaises(DomainError):
            bms.exb_to_bms1(exb.parse('e0'))


class TestPaths(unittest.TestCase):
    def names(self, src, dst):
        return [[e.dst for e in p] for p in maps.paths(src, dst)]

    def test_paths(self):
        self.assertEqual(self.names('bms1', 'bms1'), [[]])
        self.assertEqual(self.names('bms1', 'bms3')[0], ['bms2', 'bms3'])
        self.assertEqual(self.names('dbms1', 'bms2')[0], ['bms1', 'bms2'])
        self.assertEqual(self.names('bms5', 'bms7')[0], ['bms6', 'bms7'])
        self.assertEqual(self.names('y', 'exb'), [])

    def test_convert(self):
        v, path = maps.convert('exb', 'bms3', exb.parse('w+1'))
        self.assertEqual(v, ((0, 0, 0), (1, 0, 0), (0, 0, 0)))
        self.assertEqual([e.name for e in path], ['unread 0', 'toPairS', 'zeroRow'])
        with self.assertRaises(DomainError):
            maps.convert('y', 'exb', (1, 3))


class TestEdges(unittest.TestCase):
    def conv(self, src, dst, text):
        import notation
        v, path = maps.convert(src, dst, notation.get(src).parse(text))
        return notation.get(dst).show(v), [e.name for e in path]

    def test_pss(self):
        for m, want in [('(0,0)', '1'), ('(0,0)(1,0)', 'w'), ('(0,0)(1,1)', 'e0'),
                        ('(0,0)(1,1)(1,1)', 'e1'), ('(0,0)(1,1)(2,1)', 'z0'),
                        ('(0,0)(1,1)(2,2)', 'p0(W_2)'), ('()', '0')]:
            self.assertEqual(self.conv('bms2', 'exb', m), (want, ['pairOrdTerm']), m)
        with self.assertRaises(DomainError):
            maps.convert('bms2', 'exb', ((1, 1),))

    def test_pss_agrees_with_read(self):
        """pairOrdTerm (withZero l) = read 0 l on standard one-row l."""
        for l in col_lists(7):
            try:
                t = bms.bms1_to_exb(bms.of_row(l))
            except DomainError:
                continue
            self.assertEqual(maps.bms2_to_exb(bms.zero_row(bms.of_row(l))), t, l)

    def test_trio(self):
        self.assertEqual(self.conv('exb', 'bms3', 'e0'), ('(0,0,0)(1,1,0)', ['trioE2']))
        self.assertEqual(self.conv('exb', 'bms3', 'p0(W_w)'), ('(0,0,0)(1,1,1)', ['trioE2']))
        self.assertEqual(self.conv('exb', 'bms3', 'w')[1], ['unread 0', 'toPairS', 'zeroRow'])
        with self.assertRaises(DomainError):
            maps.convert('exb', 'bms3', exb.parse('p0(W_(W))'))

    def test_wide(self):
        import notation
        with self.assertRaises(DomainError):
            maps.convert('exb', 'bms3', exb.parse('p0(W_W)'))
        v, path = maps.convert('exb', 'bms3', exb.parse('p0(W_W)'), wide=True)
        self.assertEqual([e.name for e in path], ['trioMatrixLSt'])
        # where trioE2 is proved, it is still the one used
        v, path = maps.convert('exb', 'bms3', exb.parse('e0'), wide=True)
        self.assertEqual([e.name for e in path], ['trioE2'])
        v, path = maps.convert('ord', 'bms3', notation.get('ord').parse('W_w*W'), wide=True)
        self.assertEqual([e.name for e in path], ['trioRuleMatrixSt'])
        with self.assertRaisesRegex(DomainError, 'without --wide'):
            maps.convert('ord', 'bms3', notation.get('ord').parse('W'))

    def test_round_trip_through_exb(self):
        """bms2 -> exb -> bms1 recovers a pair sequence with a zero bottom row."""
        self.assertEqual(self.conv('bms2', 'bms1', '(0,0)(1,0)(2,0)'),
                         ('(0)(1)(2)', ['pairOrdTerm', 'unread 0']))


class TestCli(unittest.TestCase):
    def run_trans(self, *args):
        return subprocess.run([sys.executable, os.path.join(ROOT, 'trans')] + list(args),
                              capture_output=True, text=True)

    def test(self):
        r = self.run_trans('--from', 'prim', '--to', 'exb', '0,1,2', '0,1,1')
        self.assertEqual((r.returncode, r.stdout), (0, 'p0(w)\np0(2)\n'))
        r = self.run_trans('--from', 'exb', '--to', 'dbms2', 'p0(w)+1')
        self.assertEqual((r.returncode, r.stdout), (0, '(0,0)(1,0)(2,0)(0,0)\n'))
        r = self.run_trans('--from', 'bms2', '--to', 'wilken1', '(0,0)(1,1)(2,2)')
        self.assertEqual((r.returncode, r.stdout), (0, 't0(t1(W2))\n'))


if __name__ == '__main__':
    unittest.main()
