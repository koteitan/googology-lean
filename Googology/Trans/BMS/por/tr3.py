"""tr3: a translation T3 from trio matrices (3-row BMS, z < 2) to Wilken's notation for R_2,
and the facts on R_2 that Wilken's Theorem 1.8 decides.

Wilken, "Pure Sigma_2-elementarity beyond the core", APAL 172 (2021) 103001 ([W21]):
  upsilon_0 = 0, upsilon_{i+1} = (upsilon_i)^infty = T^{upsilon_i} cap Omega, sups at limits
  (Def 1.5).  Every ordinal a >= upsilon_1 lies in a unique segment [upsilon_i, upsilon_{i+1}) and is
  a term of T^{tau}, tau = upsilon_i: parameters < tau, +, and theta_0 = theta^tau, theta_1, ...
  (Def 1.3; Lemma 1.2: theta_i(1+a) = wbar^{Omega_i+a}; Lemma 2.26: comparison of theta-terms;
  Lemma 2.29: theta^tau(Delta+eta) is an epsilon number above tau iff Delta > 0).

The translation (this file):
  * A root term N without z = 1 columns is below upsilon_1 = psi_0(Omega_omega); its value is the
    2-row translation T of ../../PSS/por/tr.py (Wilken's T^1).
  * A root term N whose first child is a z = 1 column is read as
        N = psi_0(Omega_omega-part + X + eta)   (extended Buchholz reading)
    - the prefix P = the children that are >= psi_1(Omega_omega) (z = 1 children, and y = 1
      children that are lex >= (1,1,0)(2,2,1)) gives the upsilon-point tau = root(P);
    - the tail (the other children) gives a T^tau term: the 2-row rules of tr.py with theta_0
      read as theta^tau, the bare root read as tau, and level-0 subterms read independently
      (as parameters when they are < tau).
    The identification is  upsilon_{1+xi} = psi_0(Omega_omega + psi_1(Omega_omega) * xi):
      root(P) with P = (1,1,1), K_1, ..., K_r, K_i = (1,1,0)(2,2,1)+(level-0 children a_i)
      is upsilon_iota with iota = 1 + sum_i omega^{a_i}  (psi_1(Omega_omega + a) = psi_1(Omega_omega) omega^a).
    If the prefix does not start with (1,1,1) followed only by such K_i, write it as head + K_1..K_r
    with head maximal; root(head) is a fixed point of upsilon (upsilon_h = h), named by its matrix
    (a "fixed-point name"), and root(prefix) = upsilon_{h + sum_i omega^{a_i}}.

  Order: a W-value is a tuple of principals ('A', p) (p a T^1 principal of tr.py) or
  ('U', ud, p) (p a T^tau principal; parameters inside are ('q', principal)).  Principals are
  compared by segment first, then inside T^tau by Wilken's Lemma 2.26 (tr.py's cmp_p with the
  parameters as a level below 0).

The R_2 facts (R2_le1, R2_le2) use only [W21] Theorem 1.8 (the maximal <_2-chain), Lemma 3.1
(a <_2 b => a is a sup of an infinite <_1-chain), that {b : a <=_1 b} is an interval, and that a
successor has no <=_1-successor.  They answer True / False / None (not decided).  Note: [W21]
describes the pure structure R_2 = (Ord; <=, <=_1, <=_2).  The target of Phi_3 is Carlson's
R_2^+ = (Ord; 0, +; <=, <=_1, <=_2), a different structure (see ../POR.md).

Checks made with this file (Phi_3i test sets, see ../POR.md section 8): T3 is strictly increasing
along the lexicographic order on all 1085 + 305 matrices, and on the nodes of every Phi_3i
pattern; for upsilon_{i+1} the BM4 fundamental sequence is mapped to the chain
theta^tau(theta_1(... theta_n(Omega_{n+1}))), tau = upsilon_i ([W21] Thm 2.18).
Upsilon-points with a fixed-point name are compared by their matrices, so the check says nothing
about their mutual order.

Needs tss.py (this directory) and tr.py, pss.py (../../PSS/por).

Usage: python3 tr3.py "(0,0,0)(1,1,1)(1,1,0)(2,2,1)"
prints T3(M): u[i] is upsilon_i, u*<N> an upsilon-point named by its matrix N, u[i]:t0(...) a term
of T^{upsilon_i}, {x} a parameter below the current upsilon-point.
"""
import os
import sys
from functools import lru_cache

HERE = os.path.dirname(os.path.abspath(__file__))
for p in (HERE, os.path.join(HERE, '..', '..', 'PSS', 'por')):
    if p not in sys.path:
        sys.path.append(p)
import tss  # noqa: E402
import tr   # noqa: E402


class Unsupported(Exception):
    pass


STATS = {'fallback_ud': 0, 'iota_vs_lex_bad': 0}

Z1LEAF = (1, 1, ())
PSI1W = (1, 0, ((2, 1, ()),))       # (1,1,0)(2,2,1) as a child of the root: psi_1(Omega_omega)
ONE_T = (0, 0, ())


@lru_cache(maxsize=None)
def has_z1(t):
    return t[1] == 1 or any(has_z1(c) for c in t[2])


@lru_cache(maxsize=None)
def to_pss(t):
    if t[1]:
        raise Unsupported('z=1 in a T^1 term')
    return (t[0], tuple(to_pss(c) for c in t[2]))


# ------------------------------------------------------------------ T^tau terms
def P(m, arg):
    return ('t', m, arg)


TAU = P(0, ())                        # theta_0(0): tau in T^tau (1 in T^1)
A_ONE = ('A', tr.P(0, ()))            # the ordinal 1 as a W-principal
Q_ONE = ('q', A_ONE)                  # 1 as a parameter of T^tau
W_ONE = (A_ONE,)


def level(p):
    return p[1] if p[0] == 't' else -1


@lru_cache(maxsize=None)
def pstar(x, m):
    out = set()
    for p in x:
        if p[0] == 'q' or p[1] < m:
            continue
        if p[1] == m:
            out.add(p)
        out |= pstar(p[2], m)
    return frozenset(out)


@lru_cache(maxsize=None)
def cmp_p(p, q):
    if p == q:
        return 0
    lp, lq = level(p), level(q)
    if lp != lq:
        return -1 if lp < lq else 1
    if lp == -1:
        return cmpWP(p[1], q[1])
    m = lp
    a, c = p[2], q[2]

    def less(p, a, q, c):
        if cmp_s(a, c) < 0:
            if all(cmp_p(s, q) < 0 for s in pstar(a, m)):
                return True
        return any(cmp_p(p, s) <= 0 for s in pstar(c, m))
    if less(p, a, q, c):
        return -1
    if less(q, c, p, a):
        return 1
    raise ValueError('incomparable T^tau terms %r %r' % (p, q))


@lru_cache(maxsize=None)
def cmp_s(x, y):
    for p, q in zip(x, y):
        c = cmp_p(p, q)
        if c:
            return c
    return (len(x) > len(y)) - (len(x) < len(y))


def add(x, y):
    if not y:
        return x
    x = list(x)
    while x and cmp_p(x[-1], y[0]) < 0:
        x.pop()
    return tuple(x) + tuple(y)


def addall(xs):
    r = ()
    for x in xs:
        r = add(r, x)
    return r


def is_eps_level(p, m):
    return p[0] == 't' and p[1] == m and len(p[2]) > 0 and level(p[2][0]) >= m + 1


def is_eps0(p):
    """epsilon numbers >= tau in T^tau: tau itself and theta^tau(Delta + eta) with Delta > 0."""
    return p == TAU or is_eps_level(p, 0)


def omega_exp(x, m):
    """omega^x at level m >= 1 (x in [Omega_m, Omega_{m+1})), as tr.omega_exp."""
    if len(x) == 1 and is_eps_level(x[0], m):
        return x
    if len(x) > 1 and is_eps_level(x[0], m) and all(q == Q_ONE for q in x[1:]):
        return (P(m, x[:-1]),)
    if x and x[0] == P(m, ()):
        return (P(m, x[1:]),)
    return (P(m, x),)


def log_omega(p):
    """u with omega^u = p, for p principal at a level m >= 1."""
    _, m, a = p
    assert m >= 1
    if is_eps_level(p, m):
        return (p,)
    if len(a) >= 1 and is_eps_level(a[0], m) and all(q == Q_ONE for q in a[1:]):
        return a + (Q_ONE,)
    return add((P(m, ()),), a) if a else (P(m, ()),)


def minus_one_plus(x):
    if x and x[0] == Q_ONE:
        return x[1:]
    return x


def split_level(x, m):
    i = 0
    while i < len(x) and level(x[i]) >= m:
        i += 1
    return x[:i], x[i:]


def omega_exp_rel(x):
    """omega^x for a T^tau sum x >= tau, as a T^tau principal (theta^tau(1+a) = wbar^{tau+a})."""
    lead = x[0]
    if len(x) == 1 and is_eps0(lead):
        return x
    if is_eps0(lead) and len(x) > 1 and all(q == Q_ONE for q in x[1:]):
        y = x[:-1]
    else:
        y = x
    alpha = y[1:] if y[0] == TAU else y
    if alpha and alpha[0] != Q_ONE:
        arg = alpha
    else:
        arg = (Q_ONE,) + alpha
    return (P(0, arg),)


def omega_exp0(x, ud):
    """the ordinal omega^x for a level-0 T^tau sum x (x may be below tau)."""
    if not x:
        return (Q_ONE,)
    if x[0][0] == 'q':
        return embed(Wexp(tuple(q[1] for q in x)), ud)
    return omega_exp_rel(x)


def omega_exp_any(rho, ud):
    if not rho or level(rho[0]) <= 0:
        return omega_exp0(rho, ud)
    return omega_exp(rho, level(rho[0]))


# ------------------------------------------------------------------ W-values
def cmpWP(a, b):
    if a == b:
        return 0
    if a[0] != b[0]:
        return -1 if a[0] == 'A' else 1
    if a[0] == 'A':
        return tr.cmp_p(a[1], b[1])
    c = cmpUD(a[1], b[1])
    if c:
        return c
    return cmp_p(a[2], b[2])


def cmpW(x, y):
    for p, q in zip(x, y):
        c = cmpWP(p, q)
        if c:
            return c
    return (len(x) > len(y)) - (len(x) < len(y))


def udlex(u, v):
    return tss.tcmp((0, 0, u[1]), (0, 0, v[1]))


def cmpUD(u, v):
    """upsilon_iota < upsilon_kappa iff iota < kappa; a fixed point is its own index."""
    if u == v:
        return 0
    if u[2] is None and v[2] is None:
        STATS['fallback_ud'] += 1
        return udlex(u, v)
    wu = u[2] if u[2] is not None else (('U', u, TAU),)
    wv = v[2] if v[2] is not None else (('U', v, TAU),)
    c = cmpW(wu, wv)
    if c != udlex(u, v):
        STATS['iota_vs_lex_bad'] += 1
    return c


def Wadd(x, y):
    if not y:
        return x
    x = list(x)
    while x and cmpWP(x[-1], y[0]) < 0:
        x.pop()
    return tuple(x) + tuple(y)


def Wexp(a):
    """omega^a for a W-value a."""
    if not a:
        return W_ONE
    lead = a[0]
    if lead[0] == 'A':
        return (('A', tr.omega_exp(tuple(c[1] for c in a), 0)[0]),)
    u = lead[1]
    return (('U', u, omega_exp_rel(embed(a, u))[0]),)


def embed(w, ud):
    out = []
    for c in w:
        if c[0] == 'U':
            k = cmpUD(c[1], ud)
            if k == 0:
                out.append(c[2])
                continue
            if k > 0:
                raise Unsupported('parameter above tau')
        out.append(('q', c))
    return tuple(out)


# ------------------------------------------------------------------ the translation
def is_big(kid):
    """kid >= psi_1(Omega_omega) as a child of a root."""
    return kid[1] == 1 or (kid[0] == 1 and tss.tcmp(kid, PSI1W) >= 0)


@lru_cache(maxsize=None)
def split_root(N):
    """(prefix, tail) of a root term with a z = 1 first child."""
    ch = N[2]
    if not ch or ch[0][1] != 1:
        raise Unsupported('z=1 below the root but not in the first child')
    j = 0
    while j < len(ch) and is_big(ch[j]):
        j += 1
    if any(is_big(c) for c in ch[j:]):
        raise Unsupported('children not ordered')
    return ch[:j], ch[j:]


def plain(K):
    """K = (1,1,0)(2,2,1) followed by level-0 children: psi_1(Omega_omega + a), a countable."""
    return (K[1] == 0 and K[0] == 1 and len(K[2]) >= 1 and K[2][0] == (2, 1, ())
            and all(c[0] == 0 for c in K[2][1:]))


@lru_cache(maxsize=None)
def make_ud(prefix):
    """('ud', prefix, iota): the upsilon-point root(prefix) = upsilon_iota.
    prefix = head + plain kids K_1..K_r with K_i = psi_1(Omega_omega + a_i):
      iota = h + sum_i omega^{a_i}, where h = 1 if head = (1,1,1), and h = root(head) otherwise
      (then root(head) is a fixed point of upsilon).  iota = None marks a fixed point."""
    j = len(prefix)
    while j > 1 and plain(prefix[j - 1]):
        j -= 1
    head, kids = prefix[:j], prefix[j:]
    if head == (Z1LEAF,):
        base = W_ONE
    elif not kids:
        return ('ud', prefix, None)
    else:
        base = (('U', make_ud(head), TAU),)
    xi = ()
    for K in kids:
        a = ()
        for c in K[2][1:]:
            a = Wadd(a, (Wterm(c),))
        xi = Wadd(xi, Wexp(a))
    return ('ud', prefix, Wadd(base, xi))


@lru_cache(maxsize=None)
def Wterm(N):
    """W-principal of a root-like term N (y = 0)."""
    assert N[0] == 0
    if not has_z1(N):
        v = tr.T_term(to_pss(N), 0)
        assert len(v) == 1
        return ('A', v[0])
    prefix, tail = split_root(N)
    ud = make_ud(prefix)
    return ('U', ud, root_val(tail, ud)[0])


def Wnode(o):
    """W-value of a node (tuple of root terms)."""
    out = tuple(Wterm(t) for t in o)
    for a, b in zip(out, out[1:]):
        if cmpWP(a, b) < 0:
            raise Unsupported('root terms not in ANF order')
    return out


def val_at(c, ud):
    if c[0] == 0:
        return embed((Wterm(c),), ud)
    return T_rel(c, c[0], ud)


def root_val(ch, ud):
    """the root with children ch, relativized to the upsilon-point ud."""
    if not ch:
        return (TAU,)
    if ch[-1][0] == 1:
        return T_eps_rel((0, 0, ch), 0, ud)
    hi = tuple(c for c in ch if c[0] == 1)
    low = [c for c in ch if c[0] == 0]
    parts = [root_val(hi, ud)] if hi else []
    parts += [val_at(c, ud) for c in low]
    Z = addall(parts)
    return omega_exp_rel(add((TAU,), Z))


def T_rel(s, k, ud):
    y, z, ch = s
    assert y == k
    if k == 0:
        return root_val(ch, ud)
    if z:
        raise Unsupported('z=1 column inside a T^tau tail')
    if not ch:
        return (P(k, ()),)
    if ch[-1][0] == k + 1:
        return T_eps_rel(s, k, ud)
    hi = tuple(c for c in ch if c[0] == k + 1)
    rest = [c for c in ch if c[0] <= k]
    parts = [T_rel((k, 0, hi), k, ud)] if hi else [(P(k, ()),)]
    parts += [val_at(c, ud) for c in rest]
    Z = addall(parts)
    return omega_exp(Z, k)


def T_eps_rel(s, k, ud):
    Hs = s[2]
    mons = []
    for H in Hs:
        if H[0] != k + 1:
            raise Unsupported('mixed children in an epsilon term')
        v = T_rel(H, k + 1, ud)
        X = log_omega(v[0])
        mons.append(split_level(X, k + 1))
    Delta = mons[-1][0]
    j = len(Hs)
    while j > 0 and mons[j - 1][0] == Delta:
        j -= 1
    c = addall(tuple(omega_exp_any(rho, ud) for (_, rho) in mons[j:]))
    eta = minus_one_plus(c)
    if j > 0:
        ep = T_rel((k, 0, Hs[:j]), k, ud)
        if not any(cmp_p(ep[0], q) <= 0 for q in pstar(Delta, k)):
            eta = add(ep, eta)
    return (P(k, add(Delta, eta)),)


# ------------------------------------------------------------------ upsilon-points and R_2 facts
def upoint(o):
    """If the node o is an upsilon-point, return its prefix; else None."""
    if len(o) != 1 or not has_z1(o[0]):
        return None
    prefix, tail = split_root(o[0])
    return prefix if not tail else None


def is_limit_index(prefix):
    return prefix != (Z1LEAF,) and prefix[-1] != PSI1W


def index_in_I(prefix):
    """iota in I = {iota > 1, not lambda + 1 with lambda a limit} ([W21] Thm 1.8)."""
    if prefix == (Z1LEAF,):
        return False                               # iota = 1
    if prefix[-1] != PSI1W:
        return True                                # limit
    pred = prefix[:-1]
    return not is_limit_index(pred)                # successor of 1 or of a successor


def base_of(prefix):
    """the prefix of upsilon_{iota -. 1}."""
    return prefix[:-1] if prefix[-1] == PSI1W and prefix != (Z1LEAF,) else prefix


def segment_next(o):
    """For a node o >= upsilon_1 that is not an upsilon-point: (prefix of upsilon_kappa,
    prefix of upsilon_{kappa+1}) with upsilon_kappa <= o < upsilon_{kappa+1}."""
    N = o[0]
    prefix, tail = split_root(N)
    return prefix, prefix + (PSI1W,)


def term_lex(t):
    return tss.cols_term(t, 0)


def node_lex(o):
    return tss.mat(o)


def R2_le1(x, y):
    """Wilken R_2: x <=_1 y for nodes x < y.  True / False / None (not decided here)."""
    if not x:
        return False
    if x[-1] == ONE_T:
        return False                               # successor: lh(a+1) = a+1
    if not has_z1(x[0]):
        return False if has_z1(y[0]) else None     # upsilon_1 is <=_1-minimal (Thm 1.8.2)
    if upoint(x) is not None:
        return True                                # (upsilon_i)_{i>0} is a <_1-chain; intervals
    kap, nxt = segment_next(x)
    if is_limit_index(kap) and node_lex(y) >= node_lex(((0, 0, nxt),)):
        return False                               # upsilon_{lambda+1} is upsilon_lambda-<=_1-minimal
    return None


def R2_le2(x, y):
    """Wilken R_2: x <_2 y for nodes x < y."""
    l1 = R2_le1(x, y)
    if l1 is False:
        return False
    if x and x[-1] == ONE_T:
        return False
    px, py = upoint(x), upoint(y)
    if py is not None:
        return px is not None and index_in_I(px)   # Thm 1.8.1: <_2-predecessors of upsilon_i
    if px is not None:
        if not index_in_I(px):
            return False                           # Thm 1.8.2
        base = (0, 0, base_of(px))
        if term_lex(y[-1]) >= term_lex(base):
            return True                            # Thm 1.8.3: proper multiples of upsilon_{i -. 1}
    return None


def show_w(w):
    return ' + '.join(show_wp(p) for p in w) if w else '0'


def show_ud(u):
    if u[2] is not None:
        return 'u[%s]' % show_w(u[2])
    return 'u*<%s>' % tss.tshow((0, 0, u[1]))


def show_t(x):
    if not x:
        return '0'
    out = []
    for p in x:
        if p[0] == 'q':
            out.append('{%s}' % show_wp(p[1]))
        elif p == TAU:
            out.append('tau')
        elif p[2] == ():
            out.append('W%d' % p[1] if p[1] > 1 else 'W')
        else:
            out.append('t%d(%s)' % (p[1], show_t(p[2])))
    return '+'.join(out)


def show_wp(p):
    if p[0] == 'A':
        return tr.show((p[1],))
    s = show_t((p[2],))
    return show_ud(p[1]) if s == 'tau' else '%s:%s' % (show_ud(p[1]), s)


if __name__ == '__main__':
    for arg in sys.argv[1:]:
        o = tss.from_mat(tss.parse(arg))
        print(arg, '->', show_w(Wnode(o)))
