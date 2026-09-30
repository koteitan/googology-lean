"""TR: the translation T from standard pair-sequence matrices to Wilken's T^1 (tau = 1).

This is the translation of ../proof/PROOF.md section 12.1. Lemma TR (val o T = o) is proved
in ../proof/TR.md.

T^1 terms ([W07a] Def 3.22, Lemma 3.30):
  a term is a sum = tuple of principal terms in non-increasing order (() is 0);
  a principal term is ('t', m, arg) = theta_m(arg), arg a sum with arg < Omega_{m+2}.
  theta_0(()) = 1 = tau, theta_m(()) = Omega_m.
Comparison: level first (theta_m values lie in [Omega_m, Omega_{m+1})); same level by
Lemma 3.30:  th_m(a) < th_m(c)  iff  (a < c and a*_m < th_m(c))  or  th_m(a) <= c*_m,
where x*_m = max of the theta_m-subterms of x not inside a theta_k with k < m.

The code handles all levels (any max y), not only the fragment max y <= 1.
It also contains Wilken's lambda, lh^1 ([W07b] Def 4.1) and the bar operator
([CW12] Def 5.1) on T^1 terms.

[W07a] G. Wilken, Ordinal arithmetic based on Skolem hulling, APAL 145 (2007).
[W07b] G. Wilken, Sigma_1-elementarity and Skolem hull operators, APAL 145 (2007).
[WW11] A. Weiermann, G. Wilken, Ordinal arithmetic with simultaneously defined
       theta-functions, MLQ 57 (2011).
[CW12] T. J. Carlson, G. Wilken, Normal forms for elementary patterns, JSL 77 (2012).

Needs pss.py from this directory (por/). No other dependency.

Usage:  python3 tr.py "(0,0)(1,1)(2,2)"
prints T(M) in the notation of show(): 1, W (= Omega), W2, t0(...), t1(...), ...
"""
import os
import sys
from functools import lru_cache
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pss import parse, from_mat


ZERO = ()


def P(m, arg):
    return ('t', m, arg)


ONE = (P(0, ZERO),)             # theta_0(0) = 1
OMEGA1 = (P(1, ZERO),)          # theta_1(0) = Omega


@lru_cache(maxsize=None)
def pstar(x, m):
    """set of theta_m-subterms of the sum x, not inside theta_k with k < m."""
    out = set()
    for p in x:
        _, k, a = p
        if k < m:
            continue
        if k == m:
            out.add(p)
        out |= pstar(a, m)
    return frozenset(out)


@lru_cache(maxsize=None)
def cmp_p(p, q):
    if p == q:
        return 0
    _, m, a = p
    _, n, c = q
    if m != n:
        return -1 if m < n else 1
    # same level m
    def less(p, a, q, c):
        if cmp_s(a, c) < 0:
            st = pstar(a, m)
            if all(cmp_p(s, q) < 0 for s in st):
                return True
        st = pstar(c, m)
        return any(cmp_p(p, s) <= 0 for s in st)
    if less(p, a, q, c):
        return -1
    if less(q, c, p, a):
        return 1
    raise ValueError('incomparable?')


@lru_cache(maxsize=None)
def cmp_s(x, y):
    for p, q in zip(x, y):
        c = cmp_p(p, q)
        if c:
            return c
    return (len(x) > len(y)) - (len(x) < len(y))


def add(x, y):
    """ordinal sum of two sums (ANF with absorption)."""
    if not y:
        return x
    x = list(x)
    while x and cmp_p(x[-1], y[0]) < 0:
        x.pop()
    return tuple(x) + tuple(y)


def addall(xs):
    r = ZERO
    for x in xs:
        r = add(r, x)
    return r


def is_eps_p(p):
    """theta_0(Delta+eta) is an epsilon number iff Delta > 0 ([W07a] Lemma 4.3)."""
    _, m, a = p
    return m == 0 and len(a) > 0 and a[0][1] >= 1


def is_eps_level(p, m):
    """theta_m(Delta+eta) is an epsilon number above Omega_m iff Delta > 0."""
    _, k, a = p
    return k == m and len(a) > 0 and a[0][1] >= m + 1


def is_eps_p(p):
    return is_eps_level(p, 0)


def is_eps_plus_n(x, m):
    """x = eps + n with eps in E_{>Omega_m} of level m, n >= 0 (n = number of 1s)."""
    return (len(x) >= 1 and is_eps_level(x[0], m)
            and all(q == P(0, ZERO) for q in x[1:]))


def omega_exp(x, m=0):
    """omega^x as a T^1 term of level m, for x in [Omega_m, Omega_{m+1}) (m >= 1) or
    x < Omega_1 (m = 0).  [WW11] Lemma 2.12(b), [CW12] Lemma 5.10."""
    if m == 0 and not x:
        return ONE
    if len(x) == 1 and is_eps_level(x[0], m):
        return x                                  # omega^eps = eps
    if is_eps_plus_n(x, m) and len(x) > 1:
        return (P(m, x[:-1]),)                   # theta_m(eps+n-1) = omega^{eps+n}
    if m >= 1 and x and x[0] == P(m, ZERO):
        return (P(m, x[1:]),)                    # omega^{Omega_m + d} = theta_m(d)
    return (P(m, x),)


@lru_cache(maxsize=None)
def log_omega(p):
    """u with omega^u = p, p principal."""
    _, m, a = p
    if is_eps_level(p, m):
        return (p,)
    if is_eps_plus_n(a, m):
        return a + (P(0, ZERO),)                 # theta_m(eps+n) = omega^{eps+n+1}
    if m == 0:
        return a
    return add((P(m, ZERO),), a) if a else (P(m, ZERO),)


def one_plus(x):
    if x and x[0] != P(0, ZERO):
        return x
    return (P(0, ZERO),) + x


def minus_one_plus(x):
    if x and x[0] == P(0, ZERO):
        return x[1:]
    return x


def split_level(x, m):
    """x = D + rho with D the part of level >= m (an Omega_m-multiple), rho the rest."""
    i = 0
    while i < len(x) and x[i][1] >= m:
        i += 1
    return x[:i], x[i:]


# ------------------------------------------------------------------ the translation
@lru_cache(maxsize=None)
def T_node(o):
    return addall(tuple(T_term(t, 0) for t in o))


def T_root(t):
    return T_term(t, 0)


@lru_cache(maxsize=None)
def T_term(s, k):
    """value of the term s (with y(s) = k) at level k, as a T^1 term."""
    y, ch = s
    assert y == k
    if not ch:
        return (P(k, ZERO),)                     # 1 or Omega_k
    if ch[-1][0] == k + 1:                       # epsilon at level k: all children y = k+1
        return T_eps(s, k)
    hi = tuple(c for c in ch if c[0] == k + 1)
    rest = [c for c in ch if c[0] <= k]
    parts = [T_term((k, hi), k)] if hi else ([(P(k, ZERO),)] if k >= 1 else [])
    parts += [T_term(c, c[0]) for c in rest]
    Z = addall(tuple(parts))
    return omega_exp(Z, k)


@lru_cache(maxsize=None)
def T_eps(s, k):
    Hs = s[1]
    mons = []
    for H in Hs:
        v = T_term(H, k + 1)
        X = log_omega(v[0])
        D, rho = split_level(X, k + 1)
        mons.append((D, rho))
    Delta = mons[-1][0]
    j = len(Hs)
    while j > 0 and mons[j - 1][0] == Delta:
        j -= 1
    c = addall(tuple(omega_exp(rho, 0) if not rho or rho[0][1] == 0 else omega_exp(rho, rho[0][1])
                     for (_, rho) in mons[j:]))
    eta = minus_one_plus(c)
    if j > 0:
        ep = T_term((k, Hs[:j]), k)
        dstar = pstar(Delta, k)
        if not any(cmp_p(ep[0], q) <= 0 for q in dstar):
            eta = add(ep, eta)
    return (P(k, add(Delta, eta)),)


def show(x):
    if not x:
        return '0'
    out = []
    for p in x:
        if p[0] == 'a':
            out.append('ta(%s)' % show(p[1]))
            continue
        _, m, a = p
        if p == P(0, ZERO):
            out.append('1')
        elif a == ZERO:
            out.append('W%d' % m if m > 1 else 'W')
        else:
            out.append('t%d(%s)' % (m, show(a)))
    return '+'.join(out)


# ------------------------------------------------------------------ lambda (all levels)
def split_arg(arg):
    return split_level(arg, 1)


def iota_sum(x, alpha):
    """[W07a] Def 7.1: theta_{k+1}(y) -> theta_k(iota y), theta_1 -> theta^alpha ('a');
    level-0 terms (< alpha) stay as parameters."""
    out = []
    for p in x:
        if p[0] == 'a':
            raise ValueError
        _, m, a = p
        if m == 0:
            if cmp_p(p, alpha) >= 0:
                raise ValueError('level-0 subterm >= alpha in Delta')
            out.append(p)
        elif m == 1:
            out.append(('a', iota_sum(a, alpha)))
        else:
            out.append(('t', m - 1, iota_sum(a, alpha)))
    return tuple(out)


def has_a(x):
    for q in x:
        if q[0] == 'a':
            return True
        if has_a(q[2]):
            return True
    return False


def t_back(x, alpha):
    """[W07a] Def 6.2 t^alpha_tau on T^alpha terms below alpha^+."""
    parts = []
    for q in x:
        if q[0] == 'a':
            xi = q[1]
            if not xi:
                parts.append((alpha,))
                continue
            i = 0
            while i < len(xi) and xi[i][0] == 't' and xi[i][1] >= 1:
                i += 1
            G, rho = xi[:i], xi[i:]
            if not G:
                arg = add((alpha,), minus_one_plus(t_back(rho, alpha)))
            elif not has_a(G):
                arg = add(add(t_back(G, alpha), (alpha,)), t_back(rho, alpha))
            else:
                arg = add(t_back(G, alpha), t_back(rho, alpha))
            parts.append((P(0, arg),))
        elif q[1] == 0:
            parts.append((q,))
        else:
            parts.append((P(q[1], t_back(q[2], alpha)),))
    return addall(tuple(parts))


def logend(x):
    if not x:
        return ZERO
    return log_omega(x[-1])


def zeta(alpha):
    """[W07a] Def 4.11 with Lemma 4.4."""
    _, _, arg = alpha
    Delta, eta = split_arg(arg)
    if len(eta) == 1:
        e = eta[0]
        eD, eE = split_arg(e[2]) if e[1] == 0 else ((), ())
        if e[1] == 0 and cmp_s(eD, Delta) > 0:
            dstar = pstar(Delta, 0)
            if all(cmp_p(s, e) < 0 for s in dstar):
                return ZERO                  # eta = sup_{sigma<eta} theta(Delta+sigma)
    return logend(eta)


def lam(alpha):
    """lambda^1_alpha = iota(Delta) + zeta for epsilon alpha ([W07a] Def 7.5), in T^1."""
    _, _, arg = alpha
    Delta, eta = split_arg(arg)
    return add(t_back(iota_sum(Delta, alpha), alpha), zeta(alpha))


# ------------------------------------------------------------------ Wilken's lh^1 ([W07b] Def 4.1)
def lam_any(alpha):
    """lambda^1 for a principal theta_0 term > 1 ([W07a] Def 7.5)."""
    if is_eps_p(alpha):
        return lam(alpha)
    return zeta(alpha)


@lru_cache(maxsize=None)
def localization(alpha):
    """[W07a] Def 4.6 with tau = 1: alpha_0 = 1, alpha_{n+1} = the theta_0-subterm of alpha
    above alpha_n with maximal argument."""
    subs = set()
    def collect(x):
        for p in x:
            if p[1] == 0:
                subs.add(p)
            collect(p[2])
    collect((alpha,))
    seq = [P(0, ZERO)]
    while seq[-1] != alpha:
        cand = [p for p in subs if cmp_p(p, seq[-1]) > 0]
        best = cand[0]
        for p in cand[1:]:
            if cmp_s(p[2], best[2]) > 0:
                best = p
        seq.append(best)
    return tuple(seq)


@lru_cache(maxsize=None)
def lh1(x):
    """lh^1 of a T^1 value below Omega (sum or principal)."""
    if len(x) != 1:
        return x                                   # decomposable
    alpha = x[0]
    if alpha == P(0, ZERO):
        return x
    lamb = lam_any(alpha)
    if not lamb:
        return x
    delta = lamb[0]                                # (lambda)^* = leading ANF term
    if cmp_p(delta, alpha) <= 0:
        return add(x, lamb)
    loc = localization(delta)
    k = loc.index(alpha)                           # alpha is in the localization of delta
    seq = loc[k:]                                  # alpha = d_0, ..., d_m = delta
    m = len(seq) - 1
    i = m
    for jj in range(1, m):
        lj = lam_any(seq[jj])
        if lj and cmp_s(lj, (delta,)) >= 0:
            i = jj
            break
    if i < m:
        return add(lh1((seq[i],)), lamb)
    rho = lamb[1:]                                 # -delta + lambda
    return add(lh1((delta,)), rho)


# ------------------------------------------------------------------ bar ([CW12] Def 5.1)
def is_sup_point(eta1, Delta):
    """eta1 = sup_{sigma<eta1} theta(Delta+sigma)  iff  eta1 = theta(Gamma+rho) with
    Gamma > Delta and eta1 > Delta*  ([W07a] Lemma 4.4)."""
    if len(eta1) != 1 or eta1[0][1] != 0:
        return False
    G, _ = split_arg(eta1[0][2])
    if cmp_s(G, Delta) <= 0:
        return False
    return all(cmp_p(q, eta1[0]) < 0 for q in pstar(Delta, 0))


def bar(alpha):
    _, _, arg = alpha
    Delta, eta = split_arg(arg)
    if eta:
        eta1, eta0 = eta[:-1], eta[-1]
        if eta0 == P(0, ZERO) or (eta1 and not is_sup_point(eta1, Delta)):
            return (P(0, add(Delta, eta1)),)
    loc = localization(alpha)
    return (loc[-2],)


if __name__ == '__main__':
    for arg in sys.argv[1:]:
        print(arg, '->', show(T_node(from_mat(parse(arg)))))
