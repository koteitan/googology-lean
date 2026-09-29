"""Phi3h = phi3g with omega-ancestor stacks: a z=0 column is an index column of the NEAREST omega
ancestor whose level is <= its own, finite otherwise; a marker collapses to the target of the omega
column that owns it (flags c2rel, lastlo).
See ../../POR.md.  Recommended flags: lastcol,mult,fin,c2rel,lastlo (the default of the command line).
Usage:  python3 phi3h.py [--flags=lastcol,mult,fin,c2rel,lastlo] "(0,0,0)(1,1,1)(2,1,0)"

Phi3g: trio matrix -> R2+ pattern from ONE two-level collapse (no case rules).

Terms t = (y, z, kids) on the row-0 tree (x = depth).  A column is
  finite  : z=0 and (no z=1 ancestor inside the collapsed subtree, or y < that ancestor's y)
  omega   : z=1                                  (an Omega_omega-type level)
  index j : z=0, below a z=1 ancestor a, y = a.y + j   (level omega+j; j=0 is the marker)
C1_N (Omega_1 -> N, Omega_{1+nu} -> Omega_nu), applied to a subtree taken from level >= 1:
  y=0            -> unchanged
  finite y=1     -> the y=0 column root(N.kids + C1(kids))            (collapse)
  finite y>=2    -> y-1
  index          -> unchanged level (fixed point), kids by C1
  omega y=2 (under finite ancestry) -> kept at y=2 and wrapped in one level-1 column
                   (consecutive wraps merge):  psi_1(Omega_omega ...)
  omega y>=3 under finite ancestry -> y-1 ;  omega under an omega ancestor -> unchanged
C2_x (Omega_omega -> x, Omega_{omega+j} -> Omega_j), applied to the kids of a copied z=1 column D:
  y=0 -> unchanged ; index j=0 or finite y=1 -> root(x.kids + C2(kids)) ; index j>=1 -> j
Up (a root z=1 column A lifted into a level-1 copy): A{G} -> (2,1,G') with every y>=1 raised by 1.
lh (<=1-reach) = the 2-row fold  S := 2N ; S (+)= Coll(W|prefix_i) ; S (+)= C1(E_j)
  with  S (+) Y = S+Y if Y <= lead(S);  lh(Y)+Y if Y is <=2-able;  lh(Y) otherwise,
  and the nesting limit: if Coll(W|all omega kids) = W again (C1-fixed), N <=1 root(P,W,W) <=1 ...,
  so lh(N) = lh(root(P', W+1)).
<=2-able: x = root(P, U+q) with U = (1,0,G), G C1-fixed omega columns, 1 <= q <= d(G_last)
  (d = chain of z=1 last children one level up).  lh2 = root(P, U+q, U^q) (successors U^m, m<=q, are
  <=1-dead ends).  lh1(x) = lh2 (+) C2-images of the kids of G_last (same-level z=1 kid: doubling;
  higher z=1 kid with q<d: nesting to U+(q+1)).  Witnesses: root(P,U+q, (1,0,G[:i])+1) for C1-fixed
  proper prefixes (the <=2 analogue of the D-prefix fold)."""
import sys
from functools import lru_cache
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))  # tss.py lives in por/
import tss
from tss import ONE, add, addall, tcmp, mat, root

LEAF = (0, 0, ())
FLAGS = set()


def is_eps(t):
    return t[0] == 0 and len(t[2]) > 0 and t[2][-1][0] >= 1


def log0(t):
    A = t[2]
    hi = tuple(s for s in A if s[0] >= 1)
    lo = tuple(s for s in A if s[0] == 0)
    return addall(((root(hi),) if hi else ()) + lo)


def lam(t):
    u = root(t[2][-1][2])
    return (u,) if is_eps(u) else log0(u)


# ------------------------------------------------------------------ collapses
def _nearest(st, y):
    """nearest omega ancestor (orig_y, shift) whose level is <= y: the column is its index column."""
    for a in reversed(st):
        if a[0] <= y:
            return a
    return None


def C1(s, N, st, last=False):
    """st: stack of omega ancestors (orig_y, shift), outermost first.
    last: s lies on the rightmost path of the last omega summand."""
    y, z, B = s
    if y == 0:
        return s
    if z == 1:
        if st:                                   # omega under omega: moves rigidly with it
            sh = st[-1][1]
            return (y - sh, 1, C1s(B, N, st + ((y, sh),), last))
        if y == 2:
            return ('W', (2, 1, C1s(B, N, ((2, 0),), last)))
        return (y - 1, 1, C1s(B, N, ((y, 1),), last))
    a = _nearest(st, y)
    if a is not None and not ('lastcol' in FLAGS and last and not B and y == a[0] and a is st[0]):
        return (y - a[1], 0, C1s(B, N, st, last))
    kids = C1s(B, N, (), last)                   # below a finite column levels are finite again
    if y == 1:
        return root(add(N[2], kids))
    return (y - 1, 0, kids)


def C1s(B, N, st, last=False, lastidx=None):
    if st is None:
        st = ()
    out = []
    li = len(B) - 1 if lastidx is None else lastidx
    for i, s in enumerate(B):
        r = C1(s, N, st, last and i == li)
        if r[0] == 'W':
            if out and out[-1][0] == 'W':
                out[-1] = ('W', out[-1][1] + (r[1],))
            else:
                out.append(('W', (r[1],)))
        else:
            out.append(r)
    return addall(tuple((1, 0, r[1]) if r[0] == 'W' else r for r in out))


def C2(s, x, Dy, st=(), last=True):
    """Omega_omega -> x, Omega_{omega+j} -> Omega_j on a descendant of a copied omega column D at
    level Dy; st = omega columns of the image above s (orig_y, shift), which move rigidly."""
    y, z, B = s
    if y == 0:
        return s
    if z == 1:
        if st:
            sh = st[-1][1]
            return (y - sh, 1, C2s(B, x, Dy, st + ((y, sh),), last))
        if y - Dy <= 1:                          # an omega level cannot sit at level 1: wrap
            nsh = y - 2
            return (1, 0, ((2, 1, C2s(B, x, Dy, ((y, nsh),), last)),))
        return (y - Dy, 1, C2s(B, x, Dy, ((y, Dy),), last))
    a = _nearest(st, y)
    if a is not None and not ('c2rel' in FLAGS and last and not B and y == a[0] and a[0] - a[1] == 2):
        return (y - a[1], 0, C2s(B, x, Dy, st, last))
    if a is not None:                            # marker of a wrapped omega: its level omega+j of D
        j = y - Dy                               # is read relative to D (Omega_{omega+j} -> Omega_j)
        kids = C2s(B, x, Dy, st, last)
        if j <= 0:
            return root(add(x[2], kids))
        return (j, 0, kids)
    if y < Dy:                                   # a finite (Omega_1-multiplier) column: C1 below it
        return root(add(x[2], C1s(B, x, ())))
    kids = C2s(B, x, Dy, (), last)
    if y == Dy:
        return root(add(x[2], kids))
    return (y - Dy, 0, kids)


def C2s(B, x, Dy, st=(), last=True):
    """C2 on a list of kids; consecutive wrapped omega columns merge into one level-1 column."""
    out = []
    for i, b in enumerate(B):
        r = C2(b, x, Dy, st, last and i == len(B) - 1)
        if b[1] == 1 and not st and r[0] == 1 and r[1] == 0 and out and out[-1][0] == 1 and out[-1][1] == 0 \
                and out[-1][2] and out[-1][2][-1][1] == 1 and B[len(out) - 1][1] == 1:
            out[-1] = (1, 0, out[-1][2] + r[2])
        else:
            out.append(r)
    return addall(tuple(out))


def Up(a, N=None, last=False):
    """lift a root omega column a into a level-2 copy: every column below it with y>=1 goes up one
    level (y=0 columns and their subtrees are unchanged).  With 'lastcol', a marker (y = the y of its
    nearest omega ancestor) that is a leaf and the last column of N is a finite column: the Omega_1
    multiplier, which collapses to N."""
    def r(s, oys, lst):
        y, z, B = s
        if y == 0:
            return s
        if 'lastcol' in FLAGS and lst and not B and z == 0 and N is not None:
            own = [o for o in oys if o <= y]
            if own and len(own) == 1 and own[-1] == y and oys[0] == y:
                return root(N[2])             # an Omega_1-multiplier of the lifted summand a itself
        noys = oys + (y,) if z == 1 else oys
        return (y + 1, z, tuple(r(b, noys, lst and i == len(B) - 1) for i, b in enumerate(B)))
    return (2, 1, tuple(r(b, (a[0],), last and i == len(a[2]) - 1) for i, b in enumerate(a[2])))


# ------------------------------------------------------------------ helpers
def plus(W, k=1):
    return (W[0], W[1], W[2] + (LEAF,) * k)


def split(W):
    G = W[2]
    hi = tuple(g for g in G if g[0] >= 2 or g[1] == 1)
    lo = tuple(g for g in G if not (g[0] >= 2 or g[1] == 1))
    return hi, lo


def omega_prefix(hi):
    j = 0
    while j < len(hi) and hi[j][1] == 1:
        j += 1
    return hi[:j]


def c1fixed(Om, N, last=False):
    """C1 image of the omega columns Om is the single wrapper (1,0,Om).  last: Om ends N."""
    return bool(Om) and C1s(Om, N, (), last) == ((1, 0, Om),)


def zdepth(D):
    k = 1
    while D[2] and D[2][-1][1] == 1 and D[2][-1][0] == D[0] + 1:
        D = D[2][-1]
        k += 1
    return k


def le2_info(t):
    if t[0] != 0 or not t[2]:
        return None
    A = t[2]
    W = A[-1]
    if W[0] != 1 or W[1] != 0:
        return None
    hi, lo = split(W)
    Om = omega_prefix(hi)
    if not Om or Om != hi or not lo or any(g != LEAF for g in lo):
        return None
    if not c1fixed(Om, t, 'mult' in FLAGS):
        return None
    q = len(lo)
    if q > zdepth(Om[-1]):
        return None
    return A, W, (1, 0, Om), q


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


def oplus(S, Y):
    if tcmp(Y, S[0]) <= 0:
        return add(S, (Y,))
    if le2_info(Y) is not None:
        return add(lh(Y), (Y,))
    return lh(Y)


# ------------------------------------------------------------------ reaches
@lru_cache(maxsize=None)
def lh(t):
    if t == ONE or t[0] != 0:
        return (t,)
    if not is_eps(t):
        return add((t,), lam(t))
    if is_dead(t):
        return (t,)
    A = t[2]
    W = A[-1]
    if W[1] == 1:                                   # root omega run
        k = 0
        while k < len(A) and A[len(A) - 1 - k][1] == 1:
            k += 1
        run = A[len(A) - k:]
        S = (t, t)
        for i in range(1, k + 1):
            S = oplus(S, root(A + ((1, 0, tuple(Up(a, t, ai == k - 1) for ai, a in enumerate(run[:i]))),)))
        return S
    info = le2_info(t)
    if info is not None:
        return lh1_le2(t, info)
    hi, lo = split(W)
    Om = omega_prefix(hi)
    U = (1, 0, Om)
    if Om and Om == hi and c1fixed(Om, t, True if 'mult' in FLAGS else not lo):
        if not lo:                                  # nesting limit
            Ap = A
            while Ap and Ap[-1] == U:
                Ap = Ap[:-1]
            return lh(root(Ap + (plus(U),)))
        if all(g == LEAF for g in lo):              # too many +1's for <=2
            d = zdepth(Om[-1])
            S = lh(root(A + (plus(U, d),)))
            for _ in range(len(lo) - d):
                S = oplus(S, ONE)
            return S
    S = (t, t)
    for i in range(1, len(hi) + 1):
        if 'mult' in FLAGS:
            Y = root(add(A, C1s(hi[:i], t, (), bool(Om), min(i, len(Om)) - 1)))
        else:
            Y = root(add(A, C1s(hi[:i], t, (), i == len(hi) and not lo)))
        if Y[2][-1] == W and Y[2][:-1] == A:          # the copy is W itself: nesting
            Ap = A[:-1]
            S = oplus(S, root(Ap + (plus(W),)))
            continue
        S = oplus(S, Y)
    for g in lo:
        S = oplus(S, C1(g, t, (), 'lastlo' in FLAGS and g is lo[-1]) if g[0] >= 1 else g)
    return S


def is_limit(D):
    """the multiplier of the omega summand D ends in Omega_1: the last column on D's rightmost path
    is a z=0 leaf that is a marker (same level) of D itself (nearest omega ancestor with level <= it)."""
    path = [D]
    c = D
    while c[2]:
        c = c[2][-1]
        path.append(c)
    L = path[-1]
    if L is D or L[1] != 0 or L[0] < 1:
        return False
    for a in reversed(path[:-1]):
        if a[1] == 1 and a[0] <= L[0]:
            return a is D and a[0] == L[0]
    return False


def groups(Om):
    """mult: <=2-levels of the omega summands; a unit summand right after a limit summand is its
    successor and belongs to the same level.  Returns list of (start, end) index ranges."""
    out = []
    i = 0
    while i < len(Om):
        j = i
        if 'mult' in FLAGS and is_limit(Om[j]) and j + 1 < len(Om) and not Om[j + 1][2]:
            j += 1
        out.append((i, j))
        i = j + 1
    return out


def lh1_le2(x, info):
    A, W, U, q = info
    S = (root(A + (U,) * q),)
    Om = U[2]
    D = Om[-1]
    d = zdepth(D)
    if q < d:
        return lh(root(A[:-1] + (plus(W),)))
    lo_, hi_ = groups(Om)[-1] if 'mult' in FLAGS else (len(Om) - 1, len(Om) - 1)
    for gi, Dg in enumerate(Om[lo_:hi_ + 1]):
        for ci, c in enumerate(Dg[2]):
            if c[1] == 1:
                if c[0] == Dg[0]:
                    S = oplus(S, S[0])
                continue
            lst = (lo_ + gi == len(Om) - 1) and ci == len(Dg[2]) - 1
            S = oplus(S, C2(c, x, Dg[0], (), lst) if c[0] >= 1 else root(c[2]))
    return S


@lru_cache(maxsize=None)
def le2_succ(t):
    info = le2_info(t)
    if info is None:
        return ()
    A, W, U, q = info
    return tuple(root(A + (U,) * m) for m in range(1, q + 1))


@lru_cache(maxsize=None)
def le2_wit(t):
    info = le2_info(t)
    if info is None:
        return ()
    A, W, U, q = info
    Om = U[2]
    out = []
    ends = [e for (b, e) in groups(Om)][:-1] if 'mult' in FLAGS else list(range(len(Om) - 1))
    for e in ends:
        pre = Om[:e + 1]
        if 'mult' in FLAGS and is_limit(pre[-1]):
            pre = pre + ((2, 1, ()),)          # the level of a limit summand is witnessed at its successor
        w = root(A + (plus((1, 0, pre)),))
        if le2_info(w) is not None:
            out.append(w)
            Dl = pre[-1]
            if Dl[2] and Dl[2][-1][1] == 1 and Dl[2][-1][0] == Dl[0]:
                out.append(root(A + ((1, 0, pre),)))   # doubled level: its <=1-nesting base
    return tuple(out)


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
    o = tss.from_mat(M)
    nodes = sorted(closure([o], cap=cap), key=lambda q: mat(q))
    idx = {q: i for i, q in enumerate(nodes)}
    reach = []
    for i, q in enumerate(nodes):
        r = i
        if len(q) == 1:
            hm = mat(lh(q[0]))
            while r + 1 < len(nodes) and mat(nodes[r + 1]) <= hm:
                r += 1
        reach.append(r)
    le2 = set()
    for i, q in enumerate(nodes):
        if len(q) == 1:
            for s in le2_succ(q[0]):
                le2.add((i, idx[(s,)]))
    return nodes, reach, le2, idx[o]



def show(P):
    """one line per node: index, matrix, <=1-reach (index), <=2-successors (indices)."""
    nodes, reach, le2, pt = P
    out = []
    for i, q in enumerate(nodes):
        succ = sorted(j for (a, j) in le2 if a == i)
        mark = '*' if i == pt else ' '
        out.append('%s %2d %s  reach %d%s' % (mark, i, tss.oshow(q), reach[i],
                                             ('  <=2 ' + ' '.join(map(str, succ))) if succ else ''))
    return '\n'.join(out)


if __name__ == '__main__':
    FLAGS.update({'lastcol', 'mult', 'fin', 'c2rel', 'lastlo'})
    args = sys.argv[1:]
    for a in [a for a in args if a.startswith('--flags=')]:
        FLAGS.clear()
        FLAGS.update(f for f in a[len('--flags='):].split(',') if f)
    for m in [a for a in args if not a.startswith('--flags=')]:
        print(m)
        print(show(build(tss.parse(m))))
