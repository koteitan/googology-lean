"""Phi3: trio matrix -> additive pattern of order 2 (R2+).  A PARTIAL rule; see ../POR.md.

Version 0 = the 2-row rule (z ignored) as a baseline; extensions are switched on by FLAGS.
The recommended set is z,dbl,idx,lvl,lev (the default below).  z,dbl alone is the first
version, which fits the sheet rows 522-754.

Usage:  python3 phi3.py [--flags=z,dbl,idx,lvl,lev] "(0,0,0)(1,1,1)(1,1,0)(2,2,1)"
"""
import sys
from functools import lru_cache
import tss
from tss import ONE, add, addall, tcmp, ocmp, mat, root

FLAGS = set()


def is_eps(t):
    return t[0] == 0 and len(t[2]) > 0 and t[2][-1][0] >= 1


def log0(t):
    A = t[2]
    hi = tuple(s for s in A if s[0] >= 1)
    lo = tuple(s for s in A if s[0] == 0)
    xi = (root(hi),) if hi else ()
    return addall(xi + lo)


def lam(t):
    u = t[2][-1]
    u = root(u[2])
    if is_eps(u):
        return (u,)
    return log0(u)


def L(s, A):
    y, z, B = s
    if y == 0:
        return s
    if 'z' in FLAGS and z == 1:
        if y == 2:
            return ('W', (2, 1, B))       # marker: wrapped into a level-1 copy by Lsum
        if y >= 3:
            return (y - 1, 1, Lsum(B, A))
    LB = Lsum(B, A)
    if y == 1:
        return root(add(A, LB))
    return (y - 1, z, LB)


def Lsum(B, A):
    out = []
    for s in B:
        r = L(s, A)
        if r[0] == 'W':
            if out and out[-1][0] == 'W':
                out[-1] = ('W', out[-1][1] + (r[1],))
            else:
                out.append(('W', (r[1],)))
        else:
            out.append(r)
    res = []
    for r in out:
        if r[0] == 'W':
            res.append((1, 0, r[1]))
        else:
            res.append(r)
    return addall(tuple(res))


def oplus(S, Y, dbl=False):
    if tcmp(Y, S[0]) <= 0:
        return add(S, (Y,))
    if dbl and 'dbl' in FLAGS and le2_info(Y) is not None:
        return add(lh(Y), (Y,))
    return lh(Y)


LEAF = (0, 0, ())


def Cd(s, A):
    """copy-transform of a descendant of a z=1 column D kept at its level: z=1 columns keep
    their level, z=0 columns are collapsed as by L (y=1 -> Omega_1 -> t, y>=2 -> y-1),
    y=0 columns unchanged."""
    y, z, B = s
    if y == 0:
        return s
    if z == 1:
        return (y, z, tuple(Cd(b, A) for b in B))
    if y == 1:
        return root(add(A, tuple(Cd(b, A) for b in B)))
    return (y - 1, z, tuple(Cd(b, A) for b in B))


def Ca(s, A):
    """transform of a descendant of a root-level z=1 column A when A is copied to level 2:
    y>=2 or z=1 columns go up one level, y=1,z=0 collapse, y=0 unchanged."""
    y, z, B = s
    if y == 0:
        return s
    if y == 1 and z == 0:
        return root(add(A, tuple(Ca(b, A) for b in B)))
    return (y + 1, z, tuple(Ca(b, A) for b in B))


def zdepth(D):
    k = 1
    while D[2] and D[2][-1][1] == 1 and ('lvl' not in FLAGS or D[2][-1][0] == D[0] + 1):
        D = D[2][-1]
        k += 1
    return k


def fixed_last(D):
    """idx: a copied z=1 column D is fixed when its last child is not a z=0 column of y>=1."""
    if not D[2]:
        return True
    c = D[2][-1]
    if c[0] == 0:
        return True
    if c[1] == 1:
        return fixed_last(c)
    if 'lev' in FLAGS and c[0] == D[0] and c[2]:
        return True                           # index column with children
    return False


def fixedD(Dz):
    if 'idx' in FLAGS:
        return fixed_last(Dz[-1])
    return is_fixed(Dz)


def index_last(D):
    return bool(D[2]) and D[2][-1][1] == 0 and D[2][-1][0] == D[0]


def shift1(s):
    y, z, B = s
    if y == 0:
        return s
    return (y - 1 if y >= 1 else y, z, tuple(shift1(b) for b in B))


def Ca_idx(s, A, last):
    """idx copy of a descendant of a root z=1 column: z=1 and y>=2 columns go up one level;
    a y=1,z=0 column is an index column (raised to y=2) unless it is a leaf and the very last
    column of t, in which case it collapses to t (Omega_1 -> t)."""
    y, z, B = s
    if y == 0:
        return s
    kids = tuple(Ca_idx(b, A, last and i == len(B) - 1) for i, b in enumerate(B))
    if y == 1 and z == 0:
        if not B and last:
            return root(A)
        return (2, 0, kids)
    return (y + 1, z, kids)


def split_W(W):
    G = W[2]
    j = 0
    while j < len(G) and G[j][1] == 1:
        j += 1
    return G[:j], G[j:]


def is_fixed(Dz):
    """the level-1 copy of Dz is Dz itself (no y=1,z=0 column to collapse)."""
    def ok(s):
        y, z, B = s
        if y == 0:
            return True
        if z == 0:
            return False
        return all(ok(b) for b in B)
    return all(ok(d) for d in Dz)


def le2_info(t):
    """If t is <=2-able: (A, W, U, q) with t = root(A), W = A[-1] = U + q leaves.  Else None."""
    if 'z' not in FLAGS or t[0] != 0 or not t[2]:
        return None
    A = t[2]
    W = A[-1]
    if W[0] != 1 or W[1] != 0:
        return None
    Dz, rest = split_W(W)
    if not Dz or not rest or any(r != LEAF for r in rest) or not fixedD(Dz):
        return None
    q = len(rest)
    if q > zdepth(Dz[-1]):
        return None
    return A, W, (1, 0, Dz), q


def plus(W, k=1):
    return (W[0], W[1], W[2] + (LEAF,) * k)


def is_dead(t):
    A = t[2]
    if not A:
        return False
    U = A[-1]
    m = 0
    while m < len(A) and A[len(A) - 1 - m] == U:
        m += 1
    if m >= len(A):
        return False
    info = le2_info(root(A[:len(A) - m]))
    return info is not None and info[2] == U and m <= info[3]


@lru_cache(maxsize=None)
def lh(t):
    """<=1-reach of the indecomposable t, as an ordinal."""
    if t == ONE or t[0] != 0:
        return (t,)
    if not is_eps(t):
        return add((t,), lam(t))
    A = t[2]
    W = A[-1]
    if 'z' in FLAGS and W[1] == 1:
        k = 0
        while k < len(A) and A[len(A) - 1 - k][1] == 1 and A[len(A) - 1 - k][0] == 1:
            k += 1
        run = A[len(A) - k:]
        S = (t, t)
        for i in range(1, k + 1):
            if 'idx' in FLAGS:
                cp = []
                for ai, a in enumerate(run[:i]):
                    lastA = (ai == k - 1)
                    cp.append((2, 1, tuple(Ca_idx(b, A, lastA and bi == len(a[2]) - 1) for bi, b in enumerate(a[2]))))
                Y = root(A + ((1, 0, tuple(cp)),))
            else:
                Y = root(A + ((1, 0, tuple((2, 1, tuple(Ca(b, A) for b in a[2])) for a in run[:i])),))
            S = oplus(S, Y)
        return S
    G = W[2]
    if 'z' in FLAGS:
        Dz, rest = split_W(W)
        if Dz:
            if is_dead(t):
                return (t,)
            U = (1, 0, Dz)
            fixed = fixedD(Dz)
            if fixed and not rest:
                Ap = A
                while Ap and Ap[-1] == U:
                    Ap = Ap[:-1]
                return lh(root(Ap + (plus(U),)))
            info = le2_info(t)
            if info is not None:
                q = info[3]
                d = zdepth(Dz[-1])
                if q < d:
                    return lh(root(A[:-1] + (plus(W),)))
                S = (root(A + (U,) * q),)
                if 'idx' in FLAGS:
                    grp = [Dz[-1]]
                    i = len(Dz) - 2
                    while i >= 0 and index_last(Dz[i]) and ('lev' not in FLAGS or not Dz[i + 1][2]):
                        grp.insert(0, Dz[i]); i -= 1
                    for D in grp:
                        for c in D[2]:
                            if c[0] == 0:
                                S = oplus(S, root(c[2]))
                            elif c[1] == 0 and c[0] == D[0]:
                                S = oplus(S, root(add(A, Lsum(tuple(shift1(k) for k in c[2]), A))))
                            elif 'lvl' in FLAGS and c[1] == 1 and c[0] == D[0]:
                                S = oplus(S, S[0])
                            elif 'lev' in FLAGS and c[1] == 0 and c[0] == 1 and not c[2]:
                                S = oplus(S, root(A[:-1] + (U,)))
                    return S
                for c in Dz[-1][2]:
                    if c[0] == 0:
                        S = oplus(S, root(c[2]))
                return S
            D0 = tuple(s for s in rest if s[0] >= 2)
            E0 = tuple(s for s in rest if s[0] <= 1)
            if fixed and E0 and all(e == LEAF for e in E0):
                cons = min(len(E0), zdepth(Dz[-1]))
            else:
                cons = 0
            S = (t, t)
            if 'lev' in FLAGS and fixed:
                base = root(A[:-1] + (U,))
                steps = [Wp for Wp in level_prefixes(Dz, base)] + [Dz]
                for k, Wp in enumerate(steps):
                    Ui = (1, 0, Wp)
                    if cons and k == len(steps) - 1 and not D0:
                        Ui = plus(Ui, cons)
                    S = oplus(S, root(add(A, (Ui,))))
                for k in range(1, len(D0) + 1):
                    S = oplus(S, root(add(A + (U,), Lsum(D0[:k], A))), dbl=True)
                for g in E0[cons:]:
                    S = oplus(S, L(g, A))
                return S
            for i in range(1, len(Dz) + len(D0) + 1):
                Ui = (1, 0, tuple(Cd(d, A) for d in Dz[:min(i, len(Dz))]))
                if cons and i == len(Dz) and not D0:
                    Ui = plus(Ui, cons)       # the <=2-able form using the consumed leaves
                Y = root(add(A + (Ui,), Lsum(D0[:max(0, i - len(Dz))], A)))
                S = oplus(S, Y, dbl=i > len(Dz))
            for g in E0[cons:]:
                S = oplus(S, L(g, A))
            return S
    ghi = tuple(s for s in G if s[0] >= 2)
    glo = tuple(s for s in G if s[0] <= 1)
    S = (t, t)
    for i in range(1, len(ghi) + 1):
        S = oplus(S, root(add(A, Lsum(ghi[:i], A))))
    for g in glo:
        S = oplus(S, L(g, A))
    return S


def level_prefixes(Dz, base):
    """lev: the prefixes of Dz that end a <=2-level (see le2_wit)."""
    out = []
    for i in range(1, len(Dz)):
        Di = Dz[i - 1]
        if index_last(Di) and not Dz[i][2]:
            continue
        if fixed_last(Di):
            Wp = Dz[:i]
        elif index_last(Di):
            Wp = Dz[:i] + ((2, 1, ()),)
        else:
            Wp = Dz[:i - 1] + ((Di[0], Di[1], Di[2][:-1] + ((0, 0, base[2]),)),)
        out.append(Wp)
    return out


@lru_cache(maxsize=None)
def le2_succ(t):
    """explicit <=2-successors of t (tuple of terms)."""
    if 'z' not in FLAGS:
        return ()
    info = le2_info(t)
    if info is None:
        return ()
    A, W, U, q = info
    return tuple(root(A + (U,) * m) for m in range(1, q + 1))


@lru_cache(maxsize=None)
def le2_wit(t):
    """witness nodes inside the <=2-interval of t: smaller <=2-able forms from prefixes of U."""
    if 'z' not in FLAGS:
        return ()
    info = le2_info(t)
    if info is None:
        return ()
    A, W, U, q = info
    if 'idx' in FLAGS and 'lev' in FLAGS:
        Dz = U[2]
        base = root(A[:-1] + (U,))
        out = []
        for i in range(1, len(Dz)):
            Di = Dz[i - 1]
            if index_last(Di) and not Dz[i][2]:
                continue                      # merges into the next (plain) D
            if fixed_last(Di):
                Wp = Dz[:i]
            elif index_last(Di):
                Wp = Dz[:i] + ((2, 1, ()),)
            else:
                Wp = Dz[:i - 1] + ((Di[0], Di[1], Di[2][:-1] + ((0, 0, base[2]),)),)
            out.append(root(A + (plus((1, 0, Wp)),)))
            Dl = Wp[-1]
            if 'lvl' in FLAGS and Dl[2] and Dl[2][-1][1] == 1 and Dl[2][-1][0] == Dl[0]:
                out.append(root(A + ((1, 0, Wp),)))     # its <=1-nesting base is a node too
        return tuple(out)
    if 'idx' in FLAGS:
        return tuple(root(A + (plus((1, 0, U[2][:i])),)) for i in range(1, len(U[2])) if fixed_last(U[2][i - 1]))
    return tuple(root(A + (plus((1, 0, U[2][:i])),)) for i in range(1, len(U[2])))


def anchor(t):
    if t[0] == 0 and len(t[2]) >= 2:
        return root(t[2][:-1])
    return None


def closure(seeds, cap=300):
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
            if 'noanc2' in FLAGS and le2_info(t) is not None:
                a = None
            if a is not None and (a,) not in nodes:
                work.append((a,))
            h = lh(t)
            if h not in nodes:
                work.append(h)
            for s in le2_succ(t) + le2_wit(t):
                if (s,) not in nodes:
                    work.append((s,))
    return nodes


def build(M, cap=300):
    """M: trio matrix (list of columns).  Returns (nodes, reach, le2 pairs, point)."""
    o = tss.from_mat(M)
    pt = o
    nodes = sorted(closure([pt], cap=cap), key=lambda q: mat(q))
    idx = {q: i for i, q in enumerate(nodes)}
    reach = []
    for i, q in enumerate(nodes):
        r = i
        if len(q) == 1:
            hm = mat(lh(q[0]))
            j = i
            while j + 1 < len(nodes) and mat(nodes[j + 1]) <= hm:
                j += 1
            r = j
        reach.append(r)
    le2 = set()
    for i, q in enumerate(nodes):
        if len(q) == 1:
            for s in le2_succ(q[0]):
                le2.add((i, idx[(s,)]))
    return nodes, reach, le2, idx[pt]


def pretty(P):
    nodes, reach, le2, pt = P
    names = {}
    k = 0
    for i, o in enumerate(nodes):
        if len(o) == 1:
            names[i] = 'a' if o == (ONE,) else 'n%d' % k
            if o != (ONE,):
                k += 1
    opens = [''] * len(nodes)
    closes = [''] * len(nodes)
    arcs = [(i, reach[i], '(', ')') for i in range(len(nodes)) if reach[i] > i]
    arcs += [(i, j, '[', ']') for (i, j) in le2]
    arcs.sort(key=lambda a: (a[0], -a[1]))
    for (i, j, o_, c_) in arcs:
        opens[i] += o_
        closes[j] = c_ + closes[j]
    toks = []
    for i, o in enumerate(nodes):
        lab = '0' if i == 0 else (names[i] if len(o) == 1 else '+'.join(names[idx] for idx in [nodes.index((s,)) for s in o]))
        if i == pt:
            lab = '*' + lab
        toks.append(opens[i] + lab + closes[i])
    return ' '.join(toks)


if __name__ == '__main__':
    FLAGS.update({'z', 'dbl', 'idx', 'lvl', 'lev'})
    args = sys.argv[1:]
    for a in [a for a in args if a.startswith('--flags=')]:
        FLAGS.clear()
        FLAGS.update(f for f in a[len('--flags='):].split(',') if f)
    for s in [a for a in args if not a.startswith('--flags=')]:
        P = build(tss.parse(s))
        print(s, '->', pretty(P))
        for i, o in enumerate(P[0]):
            print('   ', i, tss.oshow(o), 'reach', P[1][i])
