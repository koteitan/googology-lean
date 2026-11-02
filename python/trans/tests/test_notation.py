"""Tests of the ASCII notations (notations.md).

    python3 -m unittest discover -s tests        (from python/trans)

Agreement with Lean is checked separately by gen_lean_check.py.
"""

import os
import random
import subprocess
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

import notation  # noqa: E402
from notation import ParseError, exb, inacc, label, matrix, seq  # noqa: E402


class TestMatrix(unittest.TestCase):
    def test_forms(self):
        self.assertEqual(matrix.parse('(0,0)(1,1)(2,2)', 2), ((0, 0), (1, 1), (2, 2)))
        self.assertEqual(matrix.parse(' (0, 0) (1,1) ', 2), ((0, 0), (1, 1)))
        self.assertEqual(matrix.parse('[[0,0],[1,1]]', 2), ((0, 0), (1, 1)))
        self.assertEqual(matrix.parse('0,1,2', 1), ((0,), (1,), (2,)))
        self.assertEqual(matrix.parse('[0,1,2]', 1), ((0,), (1,), (2,)))
        self.assertEqual(matrix.parse('()', 3), ())
        self.assertEqual(matrix.parse('', 3), ())

    def test_errors(self):
        for s, r in [('0,1', 2), ('(0,0', 2), ('(0,0)x', 2),
                     ('(0,1,2)', 1), ('(0,0,0)', 2), ('[[-1]]', 1)]:
            with self.assertRaises(ParseError, msg=s):
                matrix.parse(s, r)

    def test_fill_zeros(self):
        """A shorter column is filled with zeros at the bottom."""
        self.assertEqual(matrix.parse('(0,0)(1)', 2), ((0, 0), (1, 0)))
        self.assertEqual(matrix.parse('[[0,0],[1]]', 2), ((0, 0), (1, 0)))
        self.assertEqual(matrix.parse('(0)(1)', 3), ((0, 0, 0), (1, 0, 0)))

    def test_auto_rows(self):
        """With rows=None, N is the length of the longest column."""
        self.assertEqual(matrix.parse('(0)(1,1,1)'), ((0, 0, 0), (1, 1, 1)))
        self.assertEqual(matrix.parse('0,1,2'), ((0,), (1,), (2,)))
        self.assertEqual(matrix.parse('[[0],[1,1]]'), ((0, 0), (1, 1)))
        self.assertEqual(matrix.rows_of(matrix.parse('()')), 1)
        self.assertEqual(notation.concrete('bms', ((0, 0), (1, 1))), 'bms2')
        self.assertEqual(notation.concrete('dbms', ((0,),)), 'dbms1')
        self.assertEqual(notation.targets('bms', 'bms2'), ['bms2', 'bms1', 'bms3'])
        self.assertEqual(notation.targets('bms', 'exb'), ['bms1', 'bms2', 'bms3'])
        self.assertEqual(notation.targets('exb', 'bms2'), ['exb'])

    def test_show(self):
        self.assertEqual(matrix.show(((0, 0, 0), (1, 1, 1))), '(0,0,0)(1,1,1)')
        self.assertEqual(matrix.show(()), '()')


class TestSeq(unittest.TestCase):
    def test(self):
        self.assertEqual(seq.parse('1,3,4,2,5'), (1, 3, 4, 2, 5))
        self.assertEqual(seq.show((1, 3, 4, 2, 5)), '1,3,4,2,5')
        self.assertEqual(seq.parse('()'), ())
        self.assertEqual(seq.show(()), '()')
        for s in ['(1,3)', '1,,3', '', 'a']:
            with self.assertRaises(ParseError, msg=s):
                seq.parse(s)


def random_exb(rng, depth):
    """A random sum of principal terms, not necessarily standard."""
    n = rng.choice([0, 1, 1, 2, 3]) if depth > 0 else rng.choice([0, 1])
    t = ()
    for _ in range(n):
        if depth == 0 or rng.random() < 0.3:
            t += (exb.P_ONE,) * rng.randint(1, 3)
        else:
            t += exb.psi(random_exb(rng, depth - 1), random_exb(rng, depth - 1))
    return t


class TestExb(unittest.TestCase):
    TABLE = [  # notations.md, section 3
        ('0', '0'), ('3', '3'), ('w+1', 'w+1'), ('p0(2)', 'p0(2)'),
        ('e0', 'e0'), ('p0(W)', 'e0'), ('p0(W+W)', 'e1'), ('p0(W+1)', 'p0(W+1)'),
        ('z0', 'z0'), ('p0(p1(W))', 'z0'), ('z1', 'z1'), ('p0(p1(W)+p1(W))', 'z1'),
        ('p0(W_2)', 'p0(W_2)'), ('p0(W_w)', 'p0(W_w)'), ('p0(W_W)', 'p0(W_W)'),
        ('p0(W_e0)', 'p0(W_e0)'), ('W_1', 'W'), ('p1(0)', 'W'), ('p0(1)', 'w'),
        ('p(0)', '1'), ('p_0(0)+p0(0)', '2'), ('p12(W)', 'p12(W)'),
        ('p_(w+1)(0)', 'W_(w+1)'), ('p_(w+1)(1)', 'p_(w+1)(1)'), ('p_W(1)', 'p_W(1)'),
        ('W_(W+1)', 'W_(W+1)'), ('p0(e1)+w+2', 'p0(e1)+w+2'), ('e12', 'e12'),
        ('p_z0(0)', 'W_z0'), ('1+w', '1+w'), ('0+w', 'w'),
    ]

    def test_table(self):
        for s, want in self.TABLE:
            self.assertEqual(exb.show(exb.parse(s)), want, s)

    def test_values(self):
        self.assertEqual(exb.parse('e0'), exb.psi((), exb.BIG_OMEGA))
        self.assertEqual(exb.parse('3'), exb.numeral(3))
        self.assertEqual(exb.parse('z0'), exb.psi((), exb.psi(exb.ONE, exb.BIG_OMEGA)))

    def test_errors(self):
        for s in ['W_0', 'p', 'p0', 'p0(', 'p0(W', 'w+', '+w', 'ew', 'e(w)', 'W_W_2',
                  'w*2', 'W^2', 'g0', 'x']:
            with self.assertRaises(ParseError, msg=s):
                exb.parse(s)

    def test_round_trip(self):
        rng = random.Random(1)
        for _ in range(3000):
            t = random_exb(rng, 3)
            s = exb.show(t)
            self.assertEqual(exb.parse(s), t, s)
            self.assertEqual(exb.show(exb.parse(s)), s)


def random_inacc(rng, depth):
    k = rng.choice(['zero', 'I', 'Iw', 'add', 'phi', 'om', 'psiS', 'psiI'] if depth else
                   ['zero', 'I', 'Iw'])
    d = depth - 1
    if k == 'zero':
        return inacc.ZERO
    if k == 'I':
        return ('I', rng.randint(0, 3))
    if k == 'Iw':
        return ('Iw',)
    if k in ('add', 'phi', 'psiS'):
        return (k, random_inacc(rng, d), random_inacc(rng, d))
    if k == 'om':
        return ('om', random_inacc(rng, d))
    return ('psiI', rng.randint(0, 3), random_inacc(rng, d))


class TestInacc(unittest.TestCase):
    TABLE = [
        ('0', '0'), ('1', '1'), ('2', '2'), ('phi(0,0)', '1'), ('phi(0,1)', 'w'),
        ('W', 'W'), ('W_1', 'W'), ('W_2', 'W_2'), ('W_w', 'W_w'), ('I_3', 'I_3'),
        ('I_w', 'I_w'), ('pS_0(I_w)', 'pS_0(I_w)'), ('pI_2(W_3+1)', 'pI_2(W_3+1)'),
        ('w+1+1', 'w+2'), ('1+1+w', '1+1+w'), ('(1+1)+w', '(2)+w'), ('W+0', 'W+0'),
        ('pS_(w+1)(0)', 'pS_(w+1)(0)'),
    ]

    def test_table(self):
        for s, want in self.TABLE:
            self.assertEqual(inacc.show(inacc.parse(s)), want, s)

    def test_assoc(self):
        a, b, c = ('I', 1), ('I', 2), ('I', 3)
        self.assertEqual(inacc.parse('I_1+I_2+I_3'), ('add', a, ('add', b, c)))
        self.assertEqual(inacc.parse('(I_1+I_2)+I_3'), ('add', ('add', a, b), c))

    def test_round_trip(self):
        rng = random.Random(2)
        for _ in range(3000):
            t = random_inacc(rng, 4)
            s = inacc.show(t)
            self.assertEqual(inacc.parse(s), t, s)


class TestLabel(unittest.TestCase):
    def test_basic(self):
        W = (('W', label.ONE), 1)
        self.assertEqual(label.parse('W'), (W,))
        self.assertEqual(label.parse('w2'), ((('o', label.ONE), 2),))
        self.assertEqual(label.parse('W2'), ((('W', label.ONE), 2),))
        self.assertEqual(label.parse('p(W)'), label.parse('psi(W)'))
        self.assertEqual(label.parse('p_0(W)'), ((('psi', (), label.parse('W')), 1),))
        for s in ['p0(1)', 'W_', '(W', 'W)', 'x']:
            with self.assertRaises(ParseError, msg=s):
                label.parse(s)


class TestCli(unittest.TestCase):
    def run_trans(self, *args, stdin=''):
        return subprocess.run([sys.executable, os.path.join(ROOT, 'trans')] + list(args),
                              input=stdin, capture_output=True, text=True)

    def test_normalize(self):
        r = self.run_trans('--from', 'exb', 'p0(W)', 'p0(W+W)')
        self.assertEqual((r.returncode, r.stdout), (0, 'e0\ne1\n'))
        r = self.run_trans('--from', 'pss', stdin='(0,0) (1,1)\n[[0,0]]\n')
        self.assertEqual((r.returncode, r.stdout), (0, '(0,0)(1,1)\n(0,0)\n'))

    def test_errors(self):
        r = self.run_trans('--from', 'exb', 'W_0', 'w')
        self.assertEqual((r.returncode, r.stdout), (1, 'w\n'))
        self.assertIn('W_0', r.stderr)
        r = self.run_trans('--from', 'y', '--to', 'exb', '1,3')
        self.assertEqual(r.returncode, 1)
        self.assertIn('no map', r.stderr)
        r = self.run_trans('--from', 'ord', 'W')
        self.assertEqual(r.returncode, 2)

    def test_auto_systems(self):
        r = self.run_trans('--from', 'bms', '(0)(1,1,1)')
        self.assertEqual((r.returncode, r.stdout), (0, '(0,0,0)(1,1,1)\n'))
        r = self.run_trans('--from', 'bms', '--to', 'exb', '(0,0)(1,1)(2,2)')
        self.assertEqual((r.returncode, r.stdout), (0, 'p0(W_2)\n'))
        r = self.run_trans('--from', 'exb', '--to', 'bms', 'w', 'e0')
        self.assertEqual((r.returncode, r.stdout), (0, '(0)(1)\n(0,0,0)(1,1,0)\n'))

    def test_systems(self):
        self.assertEqual(notation.get('trio').name, 'bms3')
        self.assertEqual(notation.get('dbms4').title, 'DBMS with 4 rows')
        with self.assertRaises(KeyError):
            notation.get('bms0')


if __name__ == '__main__':
    unittest.main()
