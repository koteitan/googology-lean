"""Ordinals in Veblen normal form, and their extended Buchholz terms.

Used by the candidate value of SSOSS (maps/ssoss_candidate.py). The ordinal
part is a port of `ordinal.py` and `evalord.next_fp` of
https://github.com/koteitan/ssosn (the parts the evaluator uses).

An ordinal is a tuple of principal terms in non-increasing order (0 = ()).
A principal term is ('p', a, b), meaning phi(a, b); omega^b = phi(0, b).
Terms are kept normal: phi(a, phi(c, d)) with c > a collapses to phi(c, d).

`to_exb` writes an ordinal below phi(w, 0) as an extended Buchholz term
(notation/exb.py). It is the usual correspondence of Buchholz's psi_0 below
psi_0(W^w); it is not proved in Lean (see `to_exb`).
"""

import re
from functools import lru_cache

from notation import exb

ZERO = ()


def P(a, b):
    """phi(a, b) as an ordinal (normalized)."""
    if len(b) == 1 and cmp(b[0][1], a) > 0:      # b = phi(c, d), c > a: fixed point
        return b
    return (('p', a, b),)


ONE = (('p', ZERO, ZERO),)
OMEGA = (('p', ZERO, ONE),)


def nat(n):
    return ONE * n


def w(b):
    return P(ZERO, b)


@lru_cache(maxsize=None)
def cmp_p(p, q):
    if p == q:
        return 0
    _, a, b = p
    _, c, d = q
    ca = cmp(a, c)
    if ca == 0:
        return cmp(b, d)
    if ca < 0:                                    # p < q iff b < q
        return -1 if cmp(b, (q,)) < 0 else 1
    return 1 if cmp(d, (p,)) < 0 else -1         # a > c: q < p iff d < p


@lru_cache(maxsize=None)
def cmp(x, y):
    for s, t in zip(x, y):
        c = cmp_p(s, t)
        if c:
            return c
    return (len(x) > len(y)) - (len(x) < len(y))


def lt(x, y):
    return cmp(x, y) < 0


def add(x, y):
    if not y:
        return x
    h = y[0]
    k = len(x)
    while k > 0 and cmp_p(x[k - 1], h) < 0:
        k -= 1
    return x[:k] + y


def succ(x):
    return add(x, ONE)


def next_fp(c, x):
    """The least phi(c, d) > x."""
    base = P(c, ZERO)
    if lt(x, base):
        return base
    p = x[0]
    _, e, f = p
    ce = cmp(e, c)
    if ce == 0:
        return P(c, succ(f))
    if ce > 0:
        return P(c, succ((p,)))
    return next_fp(c, f)


# ---------------------------------------------------------------- printing
# As in the source: w = omega, e = epsilon, z = zeta, h = eta.

def _top(s, chars):
    d = 0
    for ch in s:
        if ch in '({':
            d += 1
        elif ch in ')}':
            d -= 1
        elif d == 0 and ch in chars:
            return True
    return False


def _wrap(s):
    if _top(s, '+·') or re.fullmatch(r'w\d+', s):
        return '(' + s + ')'
    return s


def show(x):
    if not x:
        return '0'
    out = []
    i = 0
    while i < len(x):
        j = i
        while j < len(x) and x[j] == x[i]:
            j += 1
        c = j - i
        s = _show_p(x[i])
        if s == '1':
            s = str(c)
        elif c > 1:
            s = s + str(c) if s == 'w' else s + '·' + str(c)
        out.append(s)
        i = j
    return '+'.join(out)


def _show_p(t):
    _, a, b = t
    if not a:
        if not b:
            return '1'
        if b == ONE:
            return 'w'
        return 'w^' + _wrap(show(b))
    name = {1: 'e', 2: 'z', 3: 'h'}.get(len(a)) if all(u == ONE[0] for u in a) else None
    if name:
        s = show(b)
        return name + (s if s.isdigit() else '_' + _wrap(s))
    return 'phi(' + show(a) + ',' + show(b) + ')'


# ------------------------------------------------- to extended Buchholz psi

class OutOfRange(ValueError):
    """The ordinal is not below phi(w, 0)."""


def _finite(x):
    """n if x is the natural number n, else None."""
    return len(x) if all(t == ONE[0] for t in x) else None


def _largest_fixed(c, n):
    """The largest principal phi(a', e) with a' > n that is <= c, or None.

    Below the leading term phi(a'', d) of c with 0 <= a'' <= n, such a term is
    <= phi(a'', d) iff it is <= d, so the search goes into d.
    """
    while c:
        _, a, d = c[0]
        if cmp(a, nat(n)) > 0:
            return c[0]
        c = d
    return None


def _minus(y, c):
    """-y + c for an additive principal y <= c."""
    return c[1:] if c[0] == y else c


def _times(n, g):
    """W^n * g as an exb term, n >= 1, for g in Cantor normal form:
    W^n * w^beta = w^(W*n + beta) = psi_1(W*(n-1) + beta)."""
    out = ()
    for t in g:
        _, a, b = t
        beta = (t,) if a else b                  # w^beta = t; beta = t when t is a fixed point
        out += exb.psi(exb.ONE, (exb.P_W,) * (n - 1) + to_exb(beta))
    return out


@lru_cache(maxsize=None)
def _arg(t):
    """The argument A of psi_0 with psi_0(A) = phi(a, b), for t = ('p', a, b).

    - w^b with b < e0: psi_0(b).
    - w^b otherwise: e + r = b with e the largest epsilon number <= b, and
      psi_0(A_e + r), where psi_0(A_e) = e.
    - phi(n, c), 1 <= n < w: with y the largest phi(a', e) <= c with a' > n,
      psi_0(W^n * (1 + c)) if there is none, else psi_0(A_y + W^n * d) with
      y + d = c.
    """
    _, a, c = t
    n = _finite(a)
    if n is None:
        raise OutOfRange('to_exb: phi(%s, ...) is not below phi(w, 0)' % show(a))
    y = _largest_fixed(c, n)
    if n == 0:
        if y is None:
            return to_exb(c)
        return _arg(y) + to_exb(_minus(y, c))
    if y is None:
        k = _finite(c)
        g = nat(k + 1) if k is not None else c
        return _times(n, g)
    return _arg(y) + _times(n, _minus(y, c))


def to_exb(x):
    """The extended Buchholz term of an ordinal x below phi(w, 0).

    A sum of principal terms phi(a, b) becomes the sum of the terms psi_0(A)
    given by `_arg`. These are the usual facts about Buchholz's psi below
    psi_0(W^w) (e_b = psi_0(W*(1+b)), z_b = psi_0(W^2*(1+b)), ...); Lean proves
    only the cases e_N and z_0 (notations.md, section 3). The map is checked in
    tests/test_ssoss_candidate.py: its values are standard (`is_ot`) and it
    preserves the order (`exb_std.lt`) on the values of the candidate.
    """
    return tuple(p for t in x for p in exb.psi(exb.ZERO, _arg(t)))
