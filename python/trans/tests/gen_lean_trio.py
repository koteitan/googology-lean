#!/usr/bin/env python3
"""Write Lean files whose `#guard`s say that maps/trio.py and notation/exb_std.py
agree with Lean.

    python3 tests/gen_lean_trio.py OUTDIR
    leanman check -C <the Lean project> OUTDIR/TrioCheck<Part>.lean   (each file)

Parts (one file each, so that each checks quickly):
- Std:   Term.cmp on random pairs and isOT on random terms, standard or not
         (Googology/Notation/ExBuchholz/Basic.lean:45, Std.lean:39).
- E2:    trioE2 (Trio/TrioFixStripTree.lean:113) on every term of smallFrag 6
         (the proved domain, up to 6 psi's), and on terms outside the domain.
- E2b:   trioE2 on the terms of smallFrag 7 that are not in smallFrag 6.
- E:     trioE (Trio/TrioTree.lean:126) on smallFrag 6.
- Omega: omegaIndexMatrix (Trio/Trio.lean:98) on the terms of smallFrag 7 below e0,
         and on terms outside that domain.
Each value is compared with `==` against the Python result, a `List (List Nat)`
or an `Ordering` / `Bool` literal.
"""

import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)

from notation import exb, exb_std  # noqa: E402
from maps import trio  # noqa: E402

HEADER = ['import Googology.Trans.ExBuchholz.BMS.Trio.TrioFixStripTree',
          '',
          'open Googology.Notation.ExBuchholz Googology.Notation.ExBuchholz.Term',
          '']

ORD = {-1: '.lt', 0: '.eq', 1: '.gt'}


def lmat(m):
    return '[' + ','.join('[' + ','.join(str(v) for v in c) + ']' for c in m) + ']'


def lterm(t):
    return '(%s : Term)' % exb.lean(t)


def rand_term(rng, size, subs):
    """A random term (any order of summands) with about `size` psi's, subscripts from subs."""
    if size <= 0:
        return ()
    out = []
    while size > 0:
        k = rng.randint(0, size - 1)
        a = rng.choice(subs)
        out.append((a, rand_term(rng, k, subs)))
        size -= k + 1
    return tuple(out)


def outside_terms(rng, n):
    """Terms outside the proved domain of trioE2: non-standard, >= W, or subscript 2, w, W."""
    subs = [(), exb.ONE, exb.numeral(2), exb.OMEGA, exb.BIG_OMEGA]
    out, seen = [], set()
    while len(out) < n:
        t = rand_term(rng, rng.randint(1, 6), subs)
        if t not in seen and not trio.trio_domain(t):
            seen.add(t)
            out.append(t)
    return out


def part_std(rng):
    lines = ['-- Term.cmp: Python exb_std.cmp = Lean']
    subs = [(), exb.ONE, exb.numeral(2), exb.OMEGA, exb.BIG_OMEGA]
    pool = trio.small_frag(5) + [rand_term(rng, rng.randint(0, 7), subs) for _ in range(300)]
    n = 0
    for _ in range(300):
        x, y = rng.choice(pool), rng.choice(pool)
        if rng.random() < 0.3:          # near pairs: share a prefix
            y = x[:rng.randint(0, len(x))] + y
        lines.append('#guard Term.cmp %s %s == %s' % (lterm(x), lterm(y), ORD[exb_std.cmp(x, y)]))
        n += 1
    lines += ['', '-- isOT: Python exb_std.is_ot = Lean']
    m = 0
    for t in rng.sample(pool, 300):
        lines.append('#guard isOT %s == %s' % (lterm(t), 'true' if exb_std.is_ot(t) else 'false'))
        m += 1
    return lines, n + m


def guards(fn_lean, fn_py, terms):
    return ['#guard %s %s == %s' % (fn_lean, lterm(t), lmat(fn_py(t))) for t in terms]


def main():
    out_dir = sys.argv[1]
    rng = random.Random(20261102)
    f6, f7 = trio.small_frag(6), trio.small_frag(7)
    s6 = set(f6)
    assert len(f6) == 610 and len(f7) == 2398      # TrioTree.lean:633, TrioFixStripTree.lean:933
    out_e2 = outside_terms(rng, 150)
    e0 = [t for t in f7 if trio.omega_index_domain(t)]
    e2 = 'Googology.Trans.BMS.TrioFixStripTree.trioE2'
    te = 'Googology.Trans.BMS.TrioTree.trioE'
    om = 'Googology.Trans.BMS.omegaIndexMatrix'
    parts = {
        'Std': part_std(rng),
        'E2': (['-- trioE2 on smallFrag 6'] + guards(e2, trio.trio_e2, f6)
               + ['', '-- trioE2 outside the proved domain']
               + guards(e2, trio.trio_e2, out_e2), len(f6) + len(out_e2)),
        'E2b': (['-- trioE2 on smallFrag 7 minus smallFrag 6']
                + guards(e2, trio.trio_e2, [t for t in f7 if t not in s6]), len(f7) - len(f6)),
        'E': (['-- trioE on smallFrag 6'] + guards(te, trio.trio_e, f6), len(f6)),
        'Omega': (['-- omegaIndexMatrix on smallFrag 7 below e0']
                  + guards(om, trio.omega_index_matrix, e0)
                  + ['', '-- omegaIndexMatrix outside its proved domain']
                  + guards(om, trio.omega_index_matrix, out_e2[:50]),
                  len(e0) + 50),
    }
    os.makedirs(out_dir, exist_ok=True)
    total = 0
    for name, (lines, n) in parts.items():
        path = os.path.join(out_dir, 'TrioCheck%s.lean' % name)
        with open(path, 'w') as f:
            f.write('\n'.join(HEADER + lines) + '\n')
        print('%s: %d guards' % (path, n), file=sys.stderr)
        total += n
    print('total: %d guards' % total, file=sys.stderr)


if __name__ == '__main__':
    main()
