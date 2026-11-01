#!/usr/bin/env python3
"""Write a Lean file whose `#guard`s say that maps/ssoss.py agrees with Lean.

    python3 tests/gen_lean_ssoss.py > CheckSsoss.lean
    leanman check -C <the Lean project> CheckSsoss.lean

The sequences are standard by construction (`ssoss.standard_forms`: from
`gen n`, n <= 5, by `Seq.fs` with k = 1, 2, 3 and the erasure of a final 0,
through lengths <= 14, kept at length <= 12). For each:

- `Seq.fs S k` (k = 1, 2, 3) equals the Python `fs`;
- for length >= 2, `encode (parse (S.drop 2)) = S`.

The value `o` is noncomputable in Lean and is not checked here
(see tests/test_ssoss.py).
"""

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)

from maps import ssoss  # noqa: E402
from notation.ssoss import lean  # noqa: E402


def main():
    forms = ssoss.standard_forms(range(6), (1, 2, 3), 14, 12)
    out = ['import Googology.Notation.SSOSS', '',
           'open Googology.Notation.SSOSS', '']
    n = 0
    for s in forms:
        for k in (1, 2, 3):
            out.append('#guard Seq.fs %s %d = %s' % (lean(s), k, lean(ssoss.fs(s, k))))
            n += 1
        if len(s) >= 2:
            out.append('#guard encode (parse (%s.drop 2)) = %s' % (lean(s), lean(s)))
            n += 1
    out.append('-- %d guards' % n)
    print('\n'.join(out))


if __name__ == '__main__':
    main()
