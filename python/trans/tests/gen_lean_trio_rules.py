#!/usr/bin/env python3
"""Write Lean files whose `#guard`s say that maps/trio_rules.py agrees with Lean.

    python3 tests/gen_lean_trio_rules.py OUTDIR
    leanman check -C <the Lean project> OUTDIR/TrioRulesCheck<Part>.lean   (each file)

The Lean functions (Trio/ is Googology/Trans/ExBuchholz/BMS/Trio/):
- trioRuleMatrixOfSt (Trio/TrioFixStrip.lean:413): parse, then trioRuleMatrixSt (:410)
- trioMatrixLSt      (Trio/TrioFixStrip.lean:422)
- ofTermFix          (Trio/TrioFixOfTerm.lean:144)

Parts (one file each, so that each checks in a few minutes):
- Labels<k>: trioRuleMatrixOfSt on every string literal of the Lean sources under
  Trio/ (the sheet labels; a string that does not parse gives `none` on both sides).
- Frag6, Frag7a, Frag7b: trioMatrixLSt and ofTermFix on smallFrag 7 (TrioTree.lean:629).
- Wide<C|U|W|O>: the same on the families famC, famU, famW, famO of
  Trio/TrioFixStripSheet9Wide.lean (subscripts 0,1,2; below W_2; 0,1,w below W_W;
  0,1,W below W_W_W), on the 42 terms of sheetPairs there, and on random terms with
  larger subscripts (w+1, W+1, W_2, W_w, W_W, ...), standard or not.
- Deep: towers T_k = towerP k (TrioTree.lean:637), k = 190..212, and the nine families
  of Trio/TrioFixStripCalibNo.lean around the index where the fuel runs out.
Each value is compared with `==` against the Python result.
"""

import os
import random
import re
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
REPO = os.path.dirname(os.path.dirname(ROOT))
TRIO = os.path.join(REPO, 'Googology', 'Trans', 'ExBuchholz', 'BMS', 'Trio')
sys.path.insert(0, ROOT)

from notation import exb, exb_std, label  # noqa: E402
from maps import trio, trio_rules as R  # noqa: E402

HEADER = ['import Googology.Trans.ExBuchholz.BMS.Trio.TrioFixStrip',
          '',
          'open Googology.Notation.ExBuchholz Googology.Notation.ExBuchholz.Term',
          'open Googology.Trans.BMS.TrioRules (Od)',
          'open Googology.Trans.BMS.TrioFixStrip (trioRuleMatrixOfSt trioMatrixLSt)',
          'open Googology.Trans.BMS.TrioFixOfTerm (ofTermFix)',
          'open Googology.Trans.BMS.TrioTree (towerP)',
          '']

LABELS_PER_FILE = 800

T1 = exb.ONE
TW = exb.BIG_OMEGA
TWO = exb.numeral(2)
TOMEGA = exb.OMEGA


def cons(a, b, t):
    return ((a, b),) + t


def psi(a, b):
    return ((a, b),)


def lmat(m):
    return '[' + ','.join('[' + ','.join(str(v) for v in c) + ']' for c in m) + ']'


def lterm(t):
    return '(%s : Term)' % exb.lean(t)


def lod(a):
    return '(%s : Od)' % label.lean(a)


def lstr(s):
    assert '"' not in s and '\\' not in s and '\n' not in s
    return '"%s"' % s


# ---------------------------------------------------------------- labels

def labels():
    """Every string literal of the Lean files under Trio/, in file order, once each."""
    seen, out = set(), []
    pat = re.compile(r'"([^"\\\n]*)"')
    for name in sorted(os.listdir(TRIO)):
        if name.endswith('.lean'):
            with open(os.path.join(TRIO, name)) as f:
                for s in pat.findall(f.read()):
                    if s not in seen:
                        seen.add(s)
                        out.append(s)
    return out


def label_guard(s):
    m = R.trio_rule_matrix_of_st(s)
    v = 'none' if m is None else 'some %s' % lmat(m)
    return '#guard trioRuleMatrixOfSt %s == %s' % (lstr(s), v)


# ---------------------------------------------------------------- terms

def term_guards(terms, lean_of=None):
    """trioMatrixLSt and ofTermFix on each term; lean_of(t) is its Lean expression."""
    out = []
    for t in terms:
        e = lean_of(t) if lean_of else lterm(t)
        out.append('#guard trioMatrixLSt %s == %s' % (e, lmat(R.trio_matrix_l_st(t))))
        out.append('#guard ofTermFix %s == %s' % (e, lod(R.of_term_fix(t))))
    return out


# Trio/TrioFixStripSheet9Wide.lean:104  genS,  :114  fam
def gen_s(subs, n):
    tab = [[()]]
    for m in range(n):
        row = []
        for k in range(m + 1):
            for b in tab[k]:
                for t in tab[m - k]:
                    row += [cons(a, b, t) for a in subs]
        tab.append(row)
    return tab


def fam(subs, n, bound):
    tab = gen_s(subs, n)
    return [a for k in range(n + 1) for a in tab[k]
            if exb_std.is_ot(a) and exb_std.lt(a, bound) and a != ()]


def wide_families():
    w2 = psi(TWO, ())
    return {
        'C': fam([(), T1, TWO], 5, TW),                         # :167 famC
        'U': fam([(), T1], 5, w2),                              # :169 famU
        'W': fam([(), T1, TOMEGA], 4, psi(TW, ())),             # :171 famW
        'O': fam([(), T1, TW], 4, psi(psi(TW, ()), ())),        # :173 famO
    }


def sheet_pairs():
    """The 42 terms of sheetPairs (Trio/TrioFixStripSheet9Wide.lean:50)."""
    te0 = exb.eps(0)
    tw = TOMEGA
    w2 = psi(TWO, ())

    def p_om(t):
        return psi((), cons(T1, (), t))
    wp1 = cons((), T1, T1)
    wp2 = cons((), T1, TWO)
    Wp1 = cons(T1, (), T1)
    return [
        te0, cons((), TW, T1), cons((), TW, tw), cons((), TW, psi((), TWO)),
        cons((), TW, psi((), tw)), cons((), TW, te0), p_om(T1), p_om(tw), p_om(te0),
        p_om(p_om(T1)), p_om(p_om(te0)), p_om(p_om(p_om(T1))), p_om(p_om(p_om(te0))),
        p_om(TW), p_om(cons(T1, (), TW)), psi((), psi(T1, T1)), psi((), psi(T1, te0)),
        psi((), psi(T1, TW)), psi((), psi(T1, cons(T1, (), TW))),
        psi((), psi(T1, psi(T1, T1))), psi((), psi(T1, psi(T1, TW))),
        psi((), psi(T1, psi(T1, psi(T1, TW)))), psi((), w2), psi((), psi(TWO, w2)),
        TW, cons(T1, (), T1), psi(T1, T1), cons(T1, T1, T1), psi(T1, TW),
        cons(T1, TW, TW), psi(T1, psi(T1, T1)), cons(T1, (), te0), psi(T1, te0),
        psi(T1, w2), psi(T1, cons(TWO, (), w2)), psi(T1, psi(TWO, TW)), psi(T1, psi(TWO, w2)),
        psi(tw, psi(wp1, ())), psi(tw, psi(wp2, ())), psi(tw, psi(TW, ())),
        psi(TW, psi(Wp1, ())),
        psi(wp1, psi(wp2, ())),
    ]


def rand_term(rng, size, subs):
    """A random term (any order of summands) with about `size` psi's, subscripts from subs."""
    if size <= 0:
        return ()
    out = []
    while size > 0:
        k = rng.randint(0, size - 1)
        out.append((rng.choice(subs), rand_term(rng, k, subs)))
        size -= k + 1
    return tuple(out)


def rich_terms(rng, n_ot, n_other):
    """Random terms whose subscripts reach w+1, W+1, W_2, W_w, W_W: n_ot standard, n_other not."""
    w1 = cons((), T1, T1)                  # w + 1
    W1 = cons(T1, (), T1)                  # W + 1
    subs = [(), T1, TWO, TOMEGA, w1, TW, W1, psi(TWO, ()), psi(TOMEGA, ()), psi(TW, ())]
    ot, other, seen = [], [], set()
    while len(ot) < n_ot or len(other) < n_other:
        t = rand_term(rng, rng.randint(1, 6), subs)
        if t in seen:
            continue
        seen.add(t)
        if exb_std.is_ot(t):
            if len(ot) < n_ot:
                ot.append(t)
        elif len(other) < n_other:
            other.append(t)
    return ot, other


# ---------------------------------------------------------------- deep terms

def tower_p(k):
    """TrioTree.lean:637  towerP: T_0 = 0, T_(k+1) = psi_0(T_k)."""
    t = ()
    for _ in range(k):
        t = psi((), t)
    return t


def g_fam(k):
    """Trio/TrioFixStripCalibNo.lean:101  G: G_0 = 0, G_(k+1) = psi_0(psi_1(G_k) + 1)."""
    t = ()
    for _ in range(k):
        t = psi((), cons(T1, t, T1))
    return t


LEAN_G = ['/-- `G₀ = 0`, `G_{k+1} = ψ_0(ψ_1(G_k) + 1)` (TrioFixStripCalibNo.lean:101). -/',
          'def gT : Nat → Term',
          '  | 0 => nil',
          '  | k + 1 => psi nil (cons t1 (gT k) t1)',
          '']


def deep_families():
    """(Python term, Lean expression) for the nine families of TrioFixStripCalibNo.lean:107
    near their first failing index k, and the towers T_190 .. T_212."""
    tp, tl = tower_p, lambda k: '(towerP %d)' % k
    fams = [  # (python family, lean family, first failing k)
        (tp, tl, 203),
        (lambda k: psi((), cons(T1, (), tp(k))),
         lambda k: '(psi nil (cons t1 nil (towerP %d)))' % k, 201),
        (lambda k: psi((), psi(T1, tp(k))),
         lambda k: '(psi nil (psi t1 (towerP %d)))' % k, 199),
        (lambda k: cons((), tp(k), psi((), tp(k - 1))),
         lambda k: '(cons nil (towerP %d) (psi nil (towerP %d)))' % (k, k - 1), 201),
        (lambda k: cons((), cons((), tp(k - 1), T1), psi((), tp(k))),
         lambda k: '(cons nil (cons nil (towerP %d) t1) (psi nil (towerP %d)))' % (k - 1, k),
         202),
        (lambda k: cons((), cons(T1, (), cons((), tp(k - 1), T1)), psi((), cons(T1, (), tp(k)))),
         lambda k: ('(cons nil (cons t1 nil (cons nil (towerP %d) t1)) '
                    '(psi nil (cons t1 nil (towerP %d))))') % (k - 1, k), 201),
        (lambda k: cons((), cons(T1, tp(k), T1), psi((), psi(T1, tp(k)))),
         lambda k: '(cons nil (cons t1 (towerP %d) t1) (psi nil (psi t1 (towerP %d))))' % (k, k),
         199),
        (g_fam, lambda k: '(gT %d)' % k, 101),
        (lambda k: cons((), cons(T1, g_fam(k - 1), T1), psi((), cons(T1, g_fam(k - 2), T1))),
         lambda k: '(cons nil (cons t1 (gT %d) t1) (psi nil (cons t1 (gT %d) t1)))' % (k - 1, k - 2),
         68),
    ]
    out = [(tp(k), tl(k)) for k in range(190, 213)]
    for f, fl, k0 in fams[1:]:
        for k in range(k0 - 3, k0 + 3):
            out.append((f(k), fl(k)))
    return out


def deep_guards():
    lines = []
    for t, e in deep_families():
        lines.append('#guard trioMatrixLSt %s == %s' % (e, lmat(R.trio_matrix_l_st(t))))
        lines.append('#guard ofTermFix %s == %s' % (e, lod(R.of_term_fix(t))))
    return lines


# ---------------------------------------------------------------- main

def main():
    out_dir = sys.argv[1]
    rng = random.Random(20261102)
    parts = {}

    labs = labels()
    for i in range(0, len(labs), LABELS_PER_FILE):
        chunk = labs[i:i + LABELS_PER_FILE]
        parts['Labels%d' % (i // LABELS_PER_FILE + 1)] = (
            ['-- trioRuleMatrixOfSt on the string literals of Trio/*.lean'] +
            [label_guard(s) for s in chunk], len(chunk))

    f6, f7 = trio.small_frag(6), trio.small_frag(7)
    assert len(f6) == 610 and len(f7) == 2398      # TrioTree.lean:633, TrioFixStripTree.lean:933
    s6 = set(f6)
    rest = [t for t in f7 if t not in s6]
    half = len(rest) // 2
    parts['Frag6'] = (['-- trioMatrixLSt, ofTermFix on smallFrag 6'] + term_guards(f6),
                      2 * len(f6))
    parts['Frag7a'] = (['-- trioMatrixLSt, ofTermFix on smallFrag 7 minus smallFrag 6 (1)']
                       + term_guards(rest[:half]), 2 * half)
    parts['Frag7b'] = (['-- trioMatrixLSt, ofTermFix on smallFrag 7 minus smallFrag 6 (2)']
                       + term_guards(rest[half:]), 2 * (len(rest) - half))

    fams = wide_families()
    assert [len(fams[k]) for k in 'CUWO'] == [491, 524, 537, 537]   # Sheet9Wide.lean:176
    for k in 'CUWO':
        parts['Wide' + k] = (['-- trioMatrixLSt, ofTermFix on fam%s (TrioFixStripSheet9Wide.lean)' % k]
                             + term_guards(fams[k]), 2 * len(fams[k]))
    sp = sheet_pairs()
    assert len(sp) == 42
    ot, other = rich_terms(rng, 300, 60)
    parts['Rich'] = (['-- trioMatrixLSt, ofTermFix on the 42 terms of sheetPairs'] + term_guards(sp)
                     + ['', '-- on random standard terms with subscripts up to W_W']
                     + term_guards(ot)
                     + ['', '-- on random terms that are not standard'] + term_guards(other),
                     2 * (len(sp) + len(ot) + len(other)))

    dg = deep_guards()
    parts['Deep'] = (['set_option maxRecDepth 100000', ''] + LEAN_G +
                     ['-- trioMatrixLSt, ofTermFix on towers and the families of '
                      'TrioFixStripCalibNo.lean'] + dg, len(dg))

    os.makedirs(out_dir, exist_ok=True)
    total = 0
    for name, (lines, n) in parts.items():
        path = os.path.join(out_dir, 'TrioRulesCheck%s.lean' % name)
        with open(path, 'w') as f:
            f.write('\n'.join(HEADER + lines) + '\n')
        print('%s: %d guards' % (path, n), file=sys.stderr)
        total += n
    print('total: %d guards' % total, file=sys.stderr)

    t = tower_p(212)
    t0 = time.time()
    R.clear_cache()
    R.trio_matrix_l_st(t)
    print('trio_matrix_l_st(T_212), cold cache: %.3f s' % (time.time() - t0), file=sys.stderr)


if __name__ == '__main__':
    main()
