"""Phi: a standard pair-sequence matrix -> an additive pattern of resemblance of order 1 (R1+).

See ../POR.md (English) and ../POR-ja.md (Japanese) for the definition, the examples and
the numerical evidence.  This file is the final rule only; the experiment that found it
also tried other variants, which are described (not implemented) in POR.md.

Terms and ordinals are those of pss.py: a term is (y, children) on the row-0 tree, an
ordinal is a tuple of terms (the root segments, a descending sum).  The nodes of the
pattern are again standard pair matrices.

Usage:  python3 phi.py "(0,0)(1,1)(2,2)"
"""
import sys
from functools import lru_cache
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from pss import mat, tcmp, add, addall, from_mat, parse, show

ONE = (0, ())          # the matrix (0,0), i.e. the ordinal 1


def is_eps(t):
    """t = (0, (C_1..C_k)) is epsilon iff k >= 1 and the last child C_k has y >= 1."""
    return t[0] == 0 and len(t[1]) > 0 and t[1][-1][0] >= 1


def log0(t):
    """t = (0, A) not epsilon: the exponent: (0, y>=1 children) followed by the y=0 children."""
    A = t[1]
    hi = tuple(s for s in A if s[0] >= 1)
    lo = tuple(s for s in A if s[0] == 0)
    xi = ((0, hi),) if hi else ()
    return addall(xi + lo)


def lam(t):
    """t not epsilon: the reach offset, from the last child u = C_k."""
    u = t[1][-1]
    if is_eps(u):
        return (u,)
    return log0(u)


def L(s, A):
    """Coll: lowering of the term s at the root whose children are A."""
    y, B = s
    if y == 0:
        return s
    LB = Lsum(B, A)
    if y == 1:
        return (0, add(A, LB))
    return (y - 1, LB)


def Lsum(B, A):
    return addall(tuple(L(s, A) for s in B))


def oplus(S, y):
    """S (+) y: append y if y <= the leading term of S, else continue from the reach of y."""
    if tcmp(y, S[0]) <= 0:
        return add(S, (y,))
    return lh(y)


@lru_cache(maxsize=None)
def lh(t):
    """the reach of the term t: the largest ordinal b with t <=1 b (an ordinal)."""
    if t == ONE or t[0] != 0:
        return (t,)
    if not is_eps(t):
        return add((t,), lam(t))
    A = t[1]
    G = A[-1][1]                                  # children of W = C_k
    ghi = tuple(s for s in G if s[0] >= 2)        # D_1..D_p
    glo = tuple(s for s in G if s[0] <= 1)        # E_1..E_q
    S = (t, t)
    for i in range(1, len(ghi) + 1):
        S = oplus(S, (0, add(A, Lsum(ghi[:i], A))))
    for g in glo:
        S = oplus(S, L(g, A))
    return S


def anchor(t):
    """t without its last child (at least two children)."""
    if t[0] == 0 and len(t[1]) >= 2:
        return (0, t[1][:-1])
    return None


def closure(seeds, cap=400):
    """closure of {0, 1} and the seeds under prefix sums, root segments, anchor and lh."""
    nodes = set([(), (ONE,)])
    work = list(seeds)
    while work:
        o = work.pop()
        if o in nodes:
            continue
        nodes.add(o)
        if len(nodes) > cap:
            raise RuntimeError('too many nodes')
        for k in range(1, len(o) + 1):
            if o[:k] not in nodes:
                work.append(o[:k])
        for s in o:
            if (s,) not in nodes:
                work.append((s,))
        if len(o) == 1:
            t = o[0]
            a = anchor(t)
            if a is not None and (a,) not in nodes:
                work.append((a,))
            h = lh(t)
            if h not in nodes:
                work.append(h)
    return nodes


def build_pattern(t, cap=400):
    """Phi of the term t: (nodes in increasing order, reach index of each node,
    additive decomposition of each node, index of the point)."""
    pt = (t,)
    nodes = sorted(closure([pt], cap=cap), key=lambda o: mat(o))
    idx = {o: i for i, o in enumerate(nodes)}
    reach = []
    for i, o in enumerate(nodes):
        r = i
        if len(o) == 1:
            hm = mat(lh(o[0]))
            j = i
            while j + 1 < len(nodes) and mat(nodes[j + 1]) <= hm:
                j += 1
            r = j
        reach.append(r)
    dec = [[idx[(s,)] for s in o] if len(o) > 1 else [] for o in nodes]
    return nodes, reach, dec, idx[pt]


def pretty(P):
    """the pattern in the notation of POR.md: nodes left to right, ( ) for <=1, * the point."""
    nodes, reach, dec, pt = P
    names, k = {}, 0
    for i, o in enumerate(nodes):
        if len(o) == 1:
            names[i] = 'a' if o == (ONE,) else 'n%d' % k
            if o != (ONE,):
                k += 1
    opens = [0] * len(nodes)
    closes = [0] * len(nodes)
    for i in range(len(nodes)):
        if reach[i] > i:
            opens[i] += 1
            closes[reach[i]] += 1
    toks = []
    for i, o in enumerate(nodes):
        lab = '0' if i == 0 else (names[i] if len(o) == 1 else '+'.join(names[j] for j in dec[i]))
        if i == pt:
            lab = '*' + lab
        toks.append('(' * opens[i] + lab + ')' * closes[i])
    return ' '.join(toks)


if __name__ == '__main__':
    for s in sys.argv[1:]:
        t = from_mat(parse(s))
        if len(t) != 1:
            sys.exit('give a matrix with a single root (one row-0 tree): ' + s)
        P = build_pattern(t[0])
        print(s, '->', pretty(P))
        for i, o in enumerate(P[0]):
            print('   ', i, show(mat(o)), 'reach', P[1][i])
