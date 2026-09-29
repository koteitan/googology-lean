"""Phi3def2: Phi3def (../POR.md section 15) with one more rule, kdl0 (section 16): a D-level omega column
read inside a level column after an elder sibling (or nested in a same-level child) is read on the
lowest level of its last chain (d_1 if it has one chain), not above its top.  The definition is otherwise that of phi3def.py, in clauses D1-D11.

A trio matrix M is read as a term tree (y, z, children) on its row-0 parent forest.  Phi_3(M) is the
closure of {0, 1, M} under prefix sums, summands, anchors, the <=1-reach lh, the <=2-successors and the
witnesses (D11), plus the Def 9.4 copies.  The reach lh is the 2-row fold (+) with two collapses:
C1 (Omega_1 -> N, D2) and C2 (Omega_omega -> x, Omega_(omega+j) -> Omega_j, D3), in which every marker
collapses to the target of the omega column that owns it.  A <=2-able node x = root(P, U + q) (D7) has
the successors d_1 < ... < d_q, one for each level column of the last omega column D of U (D6); the
reach of d_m reads the children of its level column (D8), and lh1(x) folds these reads with the blocks
of earlier limit summands (D5, D9).  Witnesses of prefixes go into the last <=2-interval (D10).

Usage:  python3 phi3def2.py "(0,0,0)(1,1,1)(2,2,1)(3,3,1)(4,2,1)"
"""
import sys
from functools import lru_cache
import tss
from tss import ONE, add, addall, tcmp, mat, root
# ---- constants and recursion contexts ----
# KCTX : (x, level, [d_m.kids]) of the omega column being read (kin)
# KDX  : (x, D level) of the level-column read in progress (deep D-level omega columns)
# K1REF: (d_m, K_(m+1)) - the level column that a same-level kid read on d_m shares
# PREBLOCK: x -> lh1(x) before the block of earlier limit summands
# IDXIMG: x -> the frames and blocks made in lh1(x); they are nodes
LEAF = (0, 0, ())
FIN = ('F',)
PREBLOCK = {}
K1REF = []
KDX = []
KCTX = []
IDXIMG = {}

# ==== D1. Terms and levels ====

def is_eps(t):
    """t is a root term whose last child has y >= 1 (an epsilon-like term)."""
    return t[0] == 0 and len(t[2]) > 0 and (t[2][-1][0] >= 1)

def log0(t):
    """the 2-row log: the part of t below its y >= 1 children, as a sum."""
    A = t[2]
    hi = tuple((s for s in A if s[0] >= 1))
    lo = tuple((s for s in A if s[0] == 0))
    return addall(((root(hi),) if hi else ()) + lo)

def lam(t):
    """the 2-row reach increment of a non-epsilon term."""
    u = root(t[2][-1][2])
    return (u,) if is_eps(u) else log0(u)

def _nearest(st, y):
    """the owner of a column at level y: the nearest omega ancestor on the stack with level <= y."""
    for a in reversed(st):
        if a[0] <= y:
            if len(a) > 2 and (not a[2]):
                return None
            return a
    return None

def split(W):
    """the children of a U-form: omega/high columns and the finite low ones."""
    G = W[2]
    hi = tuple((g for g in G if g[0] >= 2 or g[1] == 1))
    lo = tuple((g for g in G if not (g[0] >= 2 or g[1] == 1)))
    return (hi, lo)

def omega_prefix(hi):
    """the leading omega columns of a list."""
    j = 0
    while j < len(hi) and hi[j][1] == 1:
        j += 1
    return hi[:j]

def plus(W, k=1):
    """U + k (k unit leaves)."""
    return (W[0], W[1], W[2] + (LEAF,) * k)

def anchor(t):
    """the anchor of a term: its root without the last child."""
    if t[0] == 0 and len(t[2]) >= 2:
        return root(t[2][:-1])
    return None


# ==== D2. The collapse C1 (Omega_1 -> N) ====

def C1(s, N, st, last=False, merge_next=False):
    """C1_N on one column; st is the stack of omega ancestors (owners).  A final marker of the outermost
    omega column is the Omega_1-multiplier N (lastcol); below a finite column an omega column owns no index
    columns (infin)."""
    (y, z, B) = s
    if y == 0:
        return s
    fin = st == FIN
    if fin:
        st = ()
    if z == 1:
        if st:
            sh = st[-1][1]
            ok = st[-1][2] if len(st[-1]) > 2 else True
            return (y - sh, 1, C1s(B, N, st + ((y, sh, ok),), last))
        ok = not fin or merge_next
        if y == 2:
            return ('W', (2, 1, C1s(B, N, ((2, 0, ok),), last)))
        return (y - 1, 1, C1s(B, N, ((y, 1, ok),), last))
    a = _nearest(st, y)
    if a is not None and (not (last and (not B) and (y == a[0]) and (a is st[0]))):
        return (y - a[1], 0, C1s(B, N, st, last))
    kids = C1s(B, N, FIN, last)
    if y == 1:
        return root(add(N[2], kids))
    return (y - 1, 0, kids)

def C1s(B, N, st, last=False, lastidx=None):
    """C1_N on a list; consecutive wrapped omega columns merge into one level-1 column."""
    if st is None:
        st = ()
    out = []
    li = len(B) - 1 if lastidx is None else lastidx
    for (i, s) in enumerate(B):
        mn = s[1] == 1 and i + 1 < len(B) and (B[i + 1][1] == 1) and (not B[i + 1][2])
        r = C1(s, N, st, last and i == li, mn)
        if r[0] == 'W':
            if out and out[-1][0] == 'W':
                out[-1] = ('W', out[-1][1] + (r[1],))
            else:
                out.append(('W', (r[1],)))
        else:
            out.append(r)
    return addall(tuple(((1, 0, r[1]) if r[0] == 'W' else r for r in out)))

def c1fixed(Om, N, last=False):
    """the omega columns Om are fixed by C1 (they form a U-form)."""
    return bool(Om) and C1s(Om, N, (), last) == ((1, 0, Om),)


# ==== D3. The collapse C2 (Omega_omega -> x) and the read of a same-level omega column ====

def C2(s, x, Dy, st=(), last=True, top=False):
    """C2_x on one column.  A marker collapses to the target of its owner: D-level Omega_omega -> x (also deep
    inside a level column, with its own levels if it was given some, D6), an omega column on the level of
    the current level column is read by Kimg (kin), a wrapped marker is read relative to D (c2rel)."""
    (y, z, B) = s
    if y == 0:
        return s
    if z == 1 and KDX and (KDX[-1] is not None) and (y == KDX[-1][1]) and (y < Dy):
        (x1, Dy1) = KDX[-1]
        KDX.append(None)
        try:
            inf = le2_info(x1)
            if inf is not None and kdl_nested(inf[2][2][-1], level_cols(inf[2][2][-1])) == s:
                dall = [root(x1[2] + (inf[2],) * i)[2] for i in range(1, inf[3] + 1)]
                return Kimg(s, x1, Dy1, dall, None, last, j0=True)
            return Kimg(s, x1, Dy1, x1[2], None, last)
        finally:
            KDX.pop()
    if z == 1 and KCTX and (y == KCTX[-1][1]) and (y == Dy):
        (cx, cDy, cdks) = KCTX[-1]
        return Kimg(s, cx, cDy, cdks, None, last)
    if z == 1:
        if st:
            sh = st[-1][1]
            return (y - sh, 1, C2s(B, x, Dy, st + ((y, sh),), last))
        if y - Dy <= 1:
            nsh = y - 2
            return (1, 0, ((2, 1, C2s(B, x, Dy, ((y, nsh),), last)),))
        return (y - Dy, 1, C2s(B, x, Dy, ((y, Dy),), last))
    a = _nearest(st, y)
    if a is not None and (not (last and (not B) and (y == a[0]) and (a[0] - a[1] == 2))):
        return (y - a[1], 0, C2s(B, x, Dy, st, last))
    if a is not None:
        j = y - Dy
        kids = C2s(B, x, Dy, st, last)
        if j <= 0:
            return root(add(x[2], kids))
        return (j, 0, kids)
    if y < Dy:
        return root(add(x[2], C1s(B, x, ())))
    kids = C2s(B, x, Dy, (), last, top=top)
    if y == Dy:
        return root(add(x[2], kids))
    return (y - Dy, 0, kids)

def C2s(B, x, Dy, st=(), last=True, top=False):
    """C2_x on a list; consecutive wrapped omega columns merge (one U-form)."""
    out = []
    for (i, b) in enumerate(B):
        r = C2(b, x, Dy, st, last and i == len(B) - 1)
        if b[1] == 1 and (not st) and (r[0] == 1) and (r[1] == 0) and out and (out[-1][0] == 1) and (out[-1][1] == 0) and out[-1][2] and (out[-1][2][-1][1] == 1) and (B[len(out) - 1][1] == 1):
            out[-1] = (1, 0, out[-1][2] + r[2])
        else:
            out.append(r)
    return addall(tuple(out))

def KI(B, x, Dy, dk, t0, last):
    """the read of the children of a same-level omega column K: nested same-level K -> Kimg, a final
    marker leaf -> the anchor of x (lastcol one level up), runs of other columns -> C2s."""
    out = []
    run = []

    def flush(lg):
        if run:
            out.extend(C2s(tuple(run), x, Dy, (), lg))
            run.clear()
    for (i, g) in enumerate(B):
        lg = last and i == len(B) - 1
        if g[0] != 0 and (not (g[1] == 1 and g[0] == Dy)) and (not (g[1] == 0 and g[0] >= Dy)):
            run.append(g)
            if i == len(B) - 1:
                flush(lg)
            continue
        flush(False)
        if g[0] == 0:
            out.append(g)
        elif g[1] == 1 and g[0] == Dy:
            out.append(Kimg(g, x, Dy, dk, t0, lg))
        elif g[1] == 0 and g[0] == Dy and (not g[2]) and lg and (t0 is not None):
            out.append(t0)
        elif g[1] == 0 and g[0] == Dy:
            out.append(root(add(x[2], KI(g[2], x, Dy, dk, None, lg))))
        elif g[1] == 0 and g[0] > Dy:
            out.append((g[0] - Dy, 0, KI(g[2], x, Dy, dk, None, lg)))
        else:
            out.append(C2(g, x, Dy, (), lg))
    return addall(tuple(out))

def Kimg(K, x, Dy, dk, t0, last, kb2ok=True, j0=False):
    """the summand of a same-level omega column K: root(d.kids + KI(K.kids)).  d is the level that K reads:
    d_(1+j) with j its leading up-kids (kbase); an up-kid equal to K_1 shares K_1's level (kbcut), each
    further up-kid raises the level by one, capped below the enclosing level column (kb2).  With j0 (kdl0),
    K is read on the lowest level of its last chain (d_1 if it has one chain), not above its top."""
    if isinstance(dk, list):
        B = K[2]
        j = min(zlead(K), len(dk) - 1)
        up = [c for c in B if c[1] == 1 and c[0] == Dy + 1]
        k1r = K1REF[-1] if K1REF and K1REF[-1][0] is x else None
        k1 = k1r[1] if k1r else k1_of(x) if x is not None and le2_info(x) is not None else None
        if up and k1 is not None and (up[0] == k1) and k2kids(up[0], 'all'):
            B = tuple((c for c in B if c is not up[0]))
            j = min(len(up) - 1, len(dk) - 1)
            if kb2ok is not True:
                j = max(0, min(j, kb2ok))
            used = up[1:1 + j]
            B = tuple((c for c in B if not any((c is u for u in used))))
        elif j or up:
            B = tuple((c for c in B if not (c[1] == 1 and c[0] == Dy + 1)))
        if j0:
            lk = level_cols(K)
            j = min(max([i for (i, L) in enumerate(lk) if L is not None and L == lk[0]] + [0]), len(dk) - 1)
            B = tuple((c for c in K[2] if not (c[1] == 1 and c[0] == Dy + 1)))
        base = dk[j]
        return root(add(base, KI(B, x, Dy, dk, None if not last else t0, last)))
    return root(add(dk, KI(K[2], x, Dy, dk, None if not last else t0, last)))

def k1_of(x):
    """the first level column K_1 of x's last omega column D."""
    D = le2_info(x)[2][2][-1]
    up = [g for g in D[2] if g[1] == 1 and g[0] == D[0] + 1]
    return up[0] if up else None

def shares_k1(g, K1):
    """the first up-kid of g equals K_1 (g shares K_1's level)."""
    gu = [c for c in g[2] if c[1] == 1 and c[0] == g[0] + 1]
    return bool(gu) and gu[0] == K1


# ==== D4. The copy of a root omega run ====

def Up(a, N=None, last=False):
    """lift a root omega column into the level-2 copy; a final marker owned only by the lifted column (and by
    D-level columns inside an up-kid) is the Omega_1-multiplier N (lastcol)."""

    def r(s, oys, lst):
        (y, z, B) = s
        if y == 0:
            return s
        if lst and (not B) and (z == 0) and (N is not None):
            own = [o for o in oys if o <= y]
            if own and (len(own) == 1 or (all((o == y for o in own)) and max(oys) > y)) and (own[-1] == y) and (oys[0] == y):
                return root(N[2])
        noys = oys + (y,) if z == 1 else oys
        return (y + 1, z, tuple((r(b, noys, lst and i == len(B) - 1) for (i, b) in enumerate(B))))
    return (2, 1, tuple((r(b, (a[0],), last and i == len(a[2]) - 1) for (i, b) in enumerate(a[2]))))


# ==== D5. Summands of U: limits, groups, blocks ====

def is_limit(D):
    """D is a limit summand: its rightmost leaf is a marker of D (possibly through same-level omega kids)."""
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
            if a is not D and a[0] == D[0] == L[0]:
                continue
            return a is D and a[0] == L[0]
    return False

def levels_only(D):
    """D only adds levels (its children are only up-kid chains)."""
    return all((c[1] == 1 and c[0] == D[0] + 1 and levels_only(c) for c in D[2]))

def strip_marker(D):
    """lambda' of a limit summand lambda = lambda' + Omega_omega."""
    (y, z, B) = D
    if not B:
        return None
    last = strip_marker(B[-1])
    return (y, z, B[:-1] + ((last,) if last is not None else ()))

def covers(D1, D2):
    """the summand D2 after the limit D1 repeats D1's children (or a prefix of them, with D1's levels
    covered): D1's pattern is covered."""
    if has_content(D1) and D1[2]:
        k2 = D2[2]
        if k2 and k2[-1] == LEAF and (len(k2) >= 2) and ends_in_marker(k2[-2], D2[0]):
            k2 = k2[:-1]
        if k2 and len(k2) < len(D1[2]) and (D1[2][:len(k2)] == k2) and (len(level_cols(D1)) <= len(level_cols((D2[0], D2[1], k2)))):
            return True
    if not has_content(D1) or not D1[2] or D1[2][-1] != (D1[0], 0, ()):
        return False
    s1 = strip_marker(D1)
    if s1 is None or not s1[2]:
        return False
    if D2 == s1:
        return True
    return D2[2] and D2[2][-1] == LEAF and (len(D2[2]) >= 2) and ends_in_marker(D2[2][-2], D2[0]) and ((D2[0], D2[1], D2[2][:-1]) == s1)

def groups(Om):
    """the <=2-level groups of the omega columns of U: a limit summand is merged with a following unit,
    a levels-only summand, or a covering summand (mult)."""
    out = []
    i = 0
    while i < len(Om):
        j = i
        if is_limit(Om[j]) and j + 1 < len(Om) and (not Om[j + 1][2]):
            j += 1
        elif is_limit(Om[j]) and j + 1 < len(Om) and levels_only(Om[j + 1]):
            j += 1
        elif is_limit(Om[j]) and j + 1 < len(Om) and covers(Om[j], Om[j + 1]):
            j += 1
        out.append((i, j))
        i = j + 1
    return out

def has_content(D):
    """some level column of D has children other than its chain."""
    if not any((c[1] == 1 and c[0] == D[0] + 1 for c in D[2])):
        return False
    return any((k2kids(c, 'all') for c in subcols(D, top=True)[1:]))

def limx(D, x):
    """D with its final marker replaced by x (the block of a limit summand)."""
    (y, z, B) = D
    if not B:
        return (0, 0, x[2])
    return (y, z, B[:-1] + (limx(B[-1], x),))

def lchain(y, k):
    """the levels-only omega column with k levels."""
    return (y, 1, (lchain(y + 1, k - 1),) if k > 1 else ())


# ==== D6. Level columns ====

def k2kids(K2, kind):
    """the non-chain children of a level column; kind 'cut': those that end its chain (z = 0 children and
    lower omega columns; not if it has a same-level omega child or an index column above it)."""
    rest = [c for c in K2[2] if not (c[1] == 1 and c[0] == K2[0] + 1)]
    if kind == 'cut' and any((c[1] == 1 and c[0] == K2[0] for c in K2[2])):
        return []
    if kind == 'cut' and any((c[1] == 0 and c[0] > K2[0] for c in K2[2])):
        return []
    if kind == 'cut':
        return [c for c in rest if c[1] == 0 and (not c[0] > K2[0]) or c[0] < K2[0]]
    return rest

def subcols(K, top=False):
    """a column followed by the level columns above it: its chain of first up-kids, equal repeats, and after an
    uncut chain the further up-kids (a single bare one is a doubling, not a level)."""
    up = [c for c in K[2] if c[1] == 1 and c[0] == K[0] + 1]
    if not up:
        return [K]
    ch = subcols(up[0])
    cut = bool(k2kids(ch[-1], 'cut'))
    out = [K] + ch
    for S in up[1:]:
        if S == up[0] or cut:
            out += subcols(S)
    if not top and (not cut):
        ext = [S for S in up[1:] if S != up[0]]
        if ext and (not (len(ext) == 1 and (not ext[0][2]))):
            for (i, S) in enumerate(ext):
                if i == 0 and (not S[2]):
                    continue
                out += subcols(S)
    return out

def level_cols(D):
    """the level columns of D: one per <=2-successor d_m (None = a level without a column).  Includes
    the levels of same-level and D-level omega columns inside (lowest), of lower-level columns inside a later
    level column (kdl one level up), the own top level of repeated chains, and the top level unless cut."""
    up = [c for c in D[2] if c[1] == 1 and c[0] == D[0] + 1]
    if not up:
        return [None]
    first = subcols(up[0])
    cols = subcols(D, top=True)[1:]
    ks = [c for c in D[2] if c[1] == 1 and c[0] == D[0]]
    if ks and any((k2kids(c, 'all') for c in cols)) and (not [g for g in ks[0][2] if g[1] == 1 and g[0] == D[0] + 1][:1] == [up[0]]):
        kup = [g for g in ks[0][2] if g[1] == 1 and g[0] == D[0] + 1]
        if not kup:
            cols = [None] + cols
        else:
            cols = level_cols(ks[0]) + cols
    elif any((g[1] == 1 and g[0] == D[0] and (not shares_k1(g, up[0])) for c in cols for g in k2kids(c, 'all'))):
        Kp = [g for c in cols for g in k2kids(c, 'all') if g[1] == 1 and g[0] == D[0] and (not shares_k1(g, up[0]))][0]
        cols = level_cols(Kp) + cols
    elif kdl_nested(D, cols) is not None:
        cols = level_cols(kdl_nested(D, cols)) + cols
    cols = kdl2_insert(cols)
    new = []
    for (i, c) in enumerate(cols):
        new.append(c)
        if c is not None and i + 1 < len(cols) and (cols[i + 1] is not None) and (cols[i + 1] == c and any((g[1] == 1 and g[0] == c[0] for g in c[2])) or (cols[i + 1] == up[0] and up[0][2] and (not k2kids(c, 'cut'))) or any((cols[k] == cols[i + 1] and cols[k][2] and (not k2kids(c, 'cut')) and (i - k + 1 == len(subcols(cols[k]))) for k in range(i + 1)))):
            new.append(None)
    cols = new
    if k2kids(first[-1], 'cut'):
        return cols
    cols = cols + [None]
    ext = [c for c in up[1:] if not any((c is L for L in cols if L is not None))]
    if ext and (not (len(ext) == 1 and (not ext[0][2]))):
        for (i, S) in enumerate(ext):
            if i == 0 and (not S[2]):
                continue
            sc = subcols(S)
            cols = cols + sc
            if any((g[1] == 1 and g[0] == sc[-1][0] for g in sc[-1][2])) or any((g[1] == 0 and g[0] > sc[-1][0] for g in sc[-1][2])):
                cols = cols + [None]
    return cols

def kdl_nested(D, cols):
    """the first D-level omega column inside a same-level kid of a level column."""
    for c in cols:
        if c is None:
            continue
        for g in k2kids(c, 'all'):
            if g[1] == 1 and g[0] == c[0]:
                stack = [g]
                while stack:
                    h = stack.pop(0)
                    for k in h[2]:
                        if k[1] == 1 and k[0] == D[0]:
                            return k
                        if k[1] == 1 and k[0] == c[0]:
                            stack.append(k)
    return None

def kdl2_insert(cols):
    """insert the levels of a column at the previous level found inside a level column right below it."""
    out = []
    for (i, c) in enumerate(cols):
        if c is not None and out:
            prevs = [L for L in out if L is not None]
            if prevs:
                g = [h for h in k2kids(c, 'all') if h[1] == 1 and h[0] == prevs[-1][0] < c[0]]
                if g and g[0] != prevs[-1]:
                    out = out + level_cols(g[0])
        out.append(c)
    return out

def zsib(D):
    """the number of levels of D."""
    up = [c for c in D[2] if c[1] == 1 and c[0] == D[0] + 1]
    if not up:
        return 1
    return len(level_cols(D))

def zdepth(D):
    """the number of levels of D (as zsib)."""
    return zsib(D)

def zlead(K):
    """the number of levels of K above its own."""
    return zsib(K) - 1

def chtop_col(K):
    """a level column that continues its chain and has other children (or one bare extra up-kid)."""
    upk = [c for c in K[2] if c[1] == 1 and c[0] == K[0] + 1]
    if len(upk) >= 2 and (not k2kids(subcols(upk[0])[-1], 'cut')):
        ext = [c for c in upk[1:] if c != upk[0]]
        if len(ext) == 1 and (not ext[0][2]):
            return True
    return bool(k2kids(K, 'all')) and bool(upk)

def has_block(U):
    """some earlier limit summand with content gives a block after d_q."""
    Om = U[2]
    (lo_, hi_) = groups(Om)[-1]
    return any((is_limit(Dg) and has_content(Dg) for Dg in Om[:lo_]))


# ==== D7. <=2-able nodes and successors ====

def le2_info(t):
    """x = root(P, U + q) with U = (1,0,G), G C1-fixed omega columns and 1 <= q <= levels of the last one."""
    if t[0] != 0 or not t[2]:
        return None
    A = t[2]
    W = A[-1]
    if W[0] != 1 or W[1] != 0:
        return None
    (hi, lo) = split(W)
    Om = omega_prefix(hi)
    if not Om or Om != hi or (not lo) or any((g != LEAF for g in lo)):
        return None
    if not c1fixed(Om, t, True):
        return None
    q = len(lo)
    if q > zdepth(Om[-1]):
        return None
    return (A, W, (1, 0, Om), q)

@lru_cache(maxsize=None)
def le2_succ(t):
    """the <=2-successors d_m = root(P, U + q, U^m), m = 1..q."""
    info = le2_info(t)
    if info is None:
        return ()
    (A, W, U, q) = info
    return tuple((root(A + (U,) * m) for m in range(1, q + 1)))

def is_dead(t):
    """t is some d_m (a <=1 dead end unless its level column says otherwise)."""
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
    return info is not None and info[2] == U and (m <= info[3])

def d1_info(t):
    """for t = d_m: (x, K_m, m, q)."""
    A = t[2]
    if len(A) < 2 or A[-1][0] != 1 or A[-1][1] != 0:
        return None
    U = A[-1]
    m = 0
    while m < len(A) and A[len(A) - 1 - m] == U:
        m += 1
    if m >= len(A):
        return None
    x = root(A[:len(A) - m])
    info = le2_info(x)
    if info is None or info[2] != U or m > info[3]:
        return None
    cols = level_cols(U[2][-1])
    if m > len(cols) or cols[m - 1] is None:
        return None
    K = cols[m - 1]
    if not (k2kids(K, 'all') or K[2]):
        return None
    return (x, K, m, info[3])


# ==== D8. The read of a level column's children ====

def level_kids(x1, K2, m, U, q):
    """the non-chain children of K_m as read in lh1(d_m): markers -> their owner's target (also nested in
    same-level kids), D-level and lower-level omega columns -> kimg summands on their own levels; a D-level
    column with an elder sibling in K_m is read on the lowest level of its last chain (kdl0)."""
    kk = tuple(k2kids(K2, 'all'))
    cols = level_cols(U[2][-1])
    own = {U[2][-1][0]: 0}
    for (i, col) in enumerate(cols[:m - 1]):
        if col is not None and col[0] < K2[0]:
            own[col[0]] = i + 1
    kk = tuple((ownleaf(c, own, x1, U) for c in kk))
    kk = tuple((owndeep(c, own, x1, U, K2[0]) for c in kk))
    Dy_ = U[2][-1][0]
    dall = [root(x1[2] + (U,) * i)[2] for i in range(1, q + 1)]
    kk2 = []
    for c in kk:
        if c[1] == 1 and c[0] == Dy_:
            elder = [i for (i, g) in enumerate(K2[2]) if g is c]
            e = Kimg(c, x1, Dy_, dall, None, False, kb2ok=m - 2, j0=bool(elder) and elder[0] > 0)
            IDXIMG.setdefault(x1, set()).add(e)
            c = (0, 0, e[2])
        kk2.append(c)
    kk = tuple(kk2)
    cols = level_cols(U[2][-1])
    pos = m - 1
    kk2 = []
    for c in kk:
        if c[1] == 1 and pos >= 1 and (c[0] < K2[0]):
            prev = [i for i in range(pos) if cols[i] is not None and cols[i][0] == c[0]]
            if prev:
                base = [root(x1[2] + (U,) * (i + 1))[2] for i in range(prev[-1] + 1, pos)]
                if base:
                    e = Kimg(c, x1, c[0], base, None, False)
                    IDXIMG.setdefault(x1, set()).add(e)
                    c = (0, 0, e[2])
        kk2.append(c)
    kk = tuple(kk2)
    return kk

def ownleaf(c, own, x1, U):
    """a marker (with or without children) owned by D or K_j -> d_j, or the frame on d_j."""
    if c[1] == 0 and c[0] >= 1:
        j = own.get(c[0])
        if j is not None:
            dj = root(x1[2] + (U,) * j)
            if not c[2]:
                return (0, 0, dj[2])
            e = root(add(dj[2], C2s(c[2], dj, c[0])))
            IDXIMG.setdefault(x1, set()).add(e)
            return (0, 0, e[2])
    return c

def owndeep(c, own, x1, U, Ky):
    """the same for markers nested in a same-level omega kid."""
    if not (c[1] == 1 and c[0] == Ky):
        return c

    def rec(t):
        (y, z, B) = t
        out = []
        for g in B:
            if g[1] == 0 and (not g[2]) and (g[0] in own) and (g[0] < Ky):
                out.append((0, 0, root(x1[2] + (U,) * own[g[0]])[2]))
            elif g[1] == 1 and g[0] == Ky:
                out.append(rec(g))
            else:
                out.append(g)
        return (y, z, tuple(out))
    return rec(c)

def ends_in_marker(K, Dy):
    """the rightmost leaf of K is a marker at level Dy."""
    while K[2]:
        K = K[2][-1]
    return K[1] == 0 and K[0] == Dy

def _lh1_kids(S, x, Dg, Dy, idx, dk, dks, t0, lastD):
    """the fold of the read of the children of an omega column Dg (level Dy) into S: same-level omega kids
    -> Kimg, index columns -> frames root(dk + image) (consecutive ones accumulate; a <=2-able frame brings
    its nesting base), a unit after a limit level column is absorbed, a single bare extra up-kid doubles
    the top, everything else -> C2."""
    ups = [c for c in Dg[2] if c[1] == 1 and c[0] == Dy + 1]
    chain = subcols(ups[0]) if ups else []
    extra = [c for c in ups[1:] if not any((c is L for L in chain)) and c != ups[0]] if chain and (not k2kids(chain[-1], 'cut')) else []
    one_bare = len(extra) == 1 and (not extra[0][2])
    for (ci, c) in enumerate(Dg[2]):
        lst = lastD and ci == len(Dg[2]) - 1
        if one_bare and c is extra[0] and (len(dks) >= 1) and (x[2] != dks[0]):
            dq = dks[-1]
            S = oplus(S, root(dq) if not c[2] else root(add(dq, KI(c[2], x, Dy, dks, None, lst))))
            continue
        if c == LEAF and ci > 0 and (Dg[2][ci - 1][1] == 1) and (Dg[2][ci - 1][0] == Dy + 1) and ends_in_marker(Dg[2][ci - 1], Dy):
            continue
        if c[1] == 1:
            if c[0] == Dy:
                S = oplus(S, Kimg(c, x, Dy, dks, t0, lst))
            continue
        if c[0] > Dy:
            idx.append(KI((c,), x, Dy, dks, None, lst)[0])
            e = root(add(dk, addall(tuple(idx))))
            IDXIMG.setdefault(x, set()).add(e)
            if le2_info(e) is not None:
                W = e[2][-1]
                IDXIMG[x].add(root(e[2][:-1] + ((W[0], W[1], tuple((g for g in W[2] if g != LEAF))),)))
            S = oplus(S, e)
            continue
        S = oplus(S, C2(c, x, Dy, (), lst, top=True) if c[0] >= 1 else root(c[2]))
    return S


# ==== D9. The <=1-reach lh ====

def oplus(S, Y):
    """the fold step S (+) Y of the 2-row map, with lh(Y) + Y for a <=2-able Y."""
    if tcmp(Y, S[0]) <= 0:
        return add(S, (Y,))
    if le2_info(Y) is not None:
        return add(lh(Y), (Y,))
    return lh(Y)

def scmp(a, b):
    """compare two sums."""
    for (u, v) in zip(a, b):
        c = tcmp(u, v)
        if c:
            return c
    return (len(a) > len(b)) - (len(a) < len(b))

@lru_cache(maxsize=None)
def lh(t):
    """the <=1-reach of a term: 2-row cases, the reach of a level d_m (its chain top, lh1(x), or the read of
    K_m's children), root omega runs (fold over the copies), the nesting limit, <=2-able nodes (lh1_le2),
    and the fold over the collapsed high children and the low children."""
    if t == ONE or t[0] != 0:
        return (t,)
    if not is_eps(t):
        return add((t,), lam(t))
    di = d1_info(t)
    if di is not None:
        (x1, K2, m, q) = di
        U = t[2][-1]
        top = root(x1[2] + (U,) * q)
        if not k2kids(K2, 'all') and (not (m < q and chtop_col(K2))):
            cl = level_cols(U[2][-1])
            sc = subcols(K2)
            (last, seen) = (m - 1, 0)
            for i in range(m - 1, len(cl)):
                if cl[i] is not None and seen < len(sc) and (cl[i] == sc[seen]):
                    seen += 1
                    last = i
                    if seen == len(sc):
                        break
            for mm in range(last + 1, len(cl)):
                if cl[mm] is None:
                    return (root(x1[2] + (U,) * (mm + 1)),)
            return (top,)
        if m < q and chtop_col(K2):
            L = lh(x1)
            return PREBLOCK.get(x1, L)
        nx = root(x1[2] + (U,) * (m + 1)) if m < q else t
        dks = [nx[2]]
        kk = level_kids(x1, K2, m, U, q)
        KCTX.append((t, K2[0], dks))
        KDX.append((x1, U[2][-1][0]))
        try:
            S = _lh1_kids((t,), t, (K2[0], K2[1], kk), K2[0], [], nx[2], dks, None, True)
        finally:
            KCTX.pop()
            KDX.pop()
        if m + 1 == q and any((g[1] == 1 and g[0] == K2[0] for g in K2[2])) and has_block(U):
            Dd = U[2][-1]
            for c in Dd[2]:
                if c[0] == 0:
                    S = oplus(S, root(c[2]) if c[2] else ONE)
        return S
    if is_dead(t):
        return (t,)
    A = t[2]
    W = A[-1]
    if W[1] == 1:
        k = 0
        while k < len(A) and A[len(A) - 1 - k][1] == 1:
            k += 1
        run = A[len(A) - k:]
        S = (t, t)
        for i in range(1, k + 1):
            S = oplus(S, root(A + ((1, 0, tuple((Up(a, t, ai == k - 1) for (ai, a) in enumerate(run[:i])))),)))
        return S
    info = le2_info(t)
    if info is not None:
        return lh1_le2(t, info)
    (hi, lo) = split(W)
    Om = omega_prefix(hi)
    U = (1, 0, Om)
    if Om and Om == hi and c1fixed(Om, t, True):
        if not lo:
            Ap = A
            while Ap and Ap[-1] == U:
                Ap = Ap[:-1]
            return lh(root(Ap + (plus(U),)))
        if all((g == LEAF for g in lo)):
            d = zdepth(Om[-1])
            S = lh(root(A + (plus(U, d),)))
            for _ in range(len(lo) - d):
                S = oplus(S, ONE)
            return S
    S = (t, t)
    for i in range(1, len(hi) + 1):
        Y = root(add(A, C1s(hi[:i], t, (), bool(Om), min(i, len(Om)) - 1)))
        if Y[2][-1] == W and Y[2][:-1] == A:
            Ap = A[:-1]
            S = oplus(S, root(Ap + (plus(W),)))
            continue
        S = oplus(S, Y)
    for g in lo:
        S = oplus(S, C1(g, t, (), g is lo[-1]) if g[0] >= 1 else g)
    return S

def lh1_le2(x, info):
    """lh1(x) for a <=2-able x: q < levels -> nesting; otherwise start from the farthest lh(d_m)."""
    (A, W, U, q) = info
    S = (root(A + (U,) * q),)
    Om = U[2]
    D = Om[-1]
    d = zdepth(D)
    if q < d:
        return lh(root(A[:-1] + (plus(W),)))
    (lo_, hi_) = groups(Om)[-1]
    dk = S[0][2]
    if q >= 2 and len(Om) == 1:
        cl = level_cols(Om[-1])
        ups_ = [c for c in Om[-1][2] if c[1] == 1 and c[0] == Om[-1][0] + 1]
        if len(cl) >= q and cl[q - 1] is None and (cl[q - 2] is not None) and any((g[1] == 1 and g[0] == cl[q - 2][0] for g in cl[q - 2][2])) and all((any((u is L for L in cl if L is not None)) for u in ups_)):
            dk = root(A + (U,) * (q - 1))[2]
    if d1_info(S[0]) is not None:
        S = lh(S[0])
    for m in range(1, q):
        dm = root(A + (U,) * m)
        di_ = d1_info(dm)
        if di_ is not None and di_[2] < q and chtop_col(di_[1]):
            continue
        if di_ is not None:
            L = lh(dm)
            if scmp(L, S) > 0:
                S = L
    dks = [root(A + (U,) * m)[2] for m in range(1, q + 1)]
    t0 = root(A[:-1]) if len(A) >= 2 else None
    return _lh1_groups(S, x, A, U, q, Om, lo_, hi_, dk, dks, t0)

def _lh1_groups(S, x, A, U, q, Om, lo_, hi_, dk, dks, t0):
    """the reads of the last group (a limit summand with its own levels gives its block), the other
    children of chain-continuing level columns (at the top), the doublings, then the block of the earlier
    limit summands (one U-form of all of them)."""
    for (gi, Dg) in enumerate(Om[lo_:hi_ + 1]):
        Dy = Dg[0]
        if lo_ + gi < hi_ and is_limit(Dg) and (zsib(Dg) > zsib(Om[hi_]) or has_content(Dg)) and (not covers(Dg, Om[hi_])):
            e = root(add(root(A + (U,) * q)[2], ((1, 0, (limx(Dg, x),)),)))
            IDXIMG.setdefault(x, set()).add(e)
            S = oplus(S, e)
            continue
        idx = []
        KCTX.append((x, Dy, dks))
        try:
            S = _lh1_kids(S, x, Dg, Dy, idx, dk, dks, t0, lo_ + gi == len(Om) - 1)
        finally:
            KCTX.pop()
    cols = level_cols(Om[-1])
    dq = root(A + (U,) * q)
    for (m, K) in enumerate(cols, 1):
        if K is None or m >= q or (not chtop_col(K)):
            continue
        dm = root(A + (U,) * m)
        dn = root(A + (U,) * (m + 1))
        kk = level_kids(x, K, m, U, q)
        dks_ = [root(A + (U,) * i)[2] for i in range(m + 1, q + 1)]
        KCTX.append((dm, K[0], dks_))
        KDX.append((x, Om[-1][0]))
        nxt = cols[m] if m < len(cols) else None
        K1REF.append((dm, nxt))
        try:
            S = _lh1_kids(S, dm, (K[0], K[1], kk), K[0], [], dq[2], dks_, None, True)
        finally:
            KCTX.pop()
            KDX.pop()
            K1REF.pop()
    dq_ = root(A + (U,) * q)
    for K in level_cols(Om[-1]):
        if K is None:
            continue
        upk = [c for c in K[2] if c[1] == 1 and c[0] == K[0] + 1]
        if len(upk) >= 2 and (not k2kids(subcols(upk[0])[-1], 'cut')):
            ext = [c for c in upk[1:] if c != upk[0]]
            if len(ext) == 1 and (not ext[0][2]):
                S = oplus(S, dq_)
    PREBLOCK[x] = S
    if lo_ >= 2 and is_limit(Om[lo_ - 1]) and has_content(Om[lo_ - 1]):
        e = root(add(root(A + (U,) * q)[2], ((1, 0, Om[:lo_ - 1] + (limx(Om[lo_ - 1], x),)),)))
        IDXIMG.setdefault(x, set()).add(e)
        S = oplus(S, e)
    else:
        for Dg in Om[:lo_]:
            if is_limit(Dg) and has_content(Dg):
                e = root(add(root(A + (U,) * q)[2], ((1, 0, (limx(Dg, x),)),)))
                IDXIMG.setdefault(x, set()).add(e)
                S = oplus(S, e)
    return S


# ==== D10. Witnesses ====

@lru_cache(maxsize=None)
def le2_wit(t):
    """the witness of each proper prefix of U's groups: in the last interval (d_(q-1), d_q), at the successor
    of a limit prefix, or (a covered limit) as its levels-only successor below the highest level it reads."""
    info = le2_info(t)
    if info is None:
        return ()
    (A, W, U, q) = info
    Om = U[2]
    out = []
    ends = [e for (b, e) in groups(Om)][:-1]
    for e in ends:
        pre = Om[:e + 1]
        if is_limit(pre[-1]) and has_content(pre[-1]):
            continue
        if is_limit(pre[-1]) and 1 < zsib(pre[-1]) <= q:
            j = max([min(zlead(c), q - 1) for c in pre[-1][2] if c[1] == 1 and c[0] == pre[-1][0]] + [0])
            out.append(root(A + (U,) * j + ((1, 0, pre + (lchain(pre[-1][0], zsib(pre[-1])),)),)))
            continue
        if is_limit(pre[-1]):
            pre = pre + ((2, 1, ()),)
        w = root(A + (U,) * (q - 1) + (plus((1, 0, pre)),))
        if le2_info(w) is not None:
            out.append(w)
    return tuple(out)


# ==== D11. Closure, the Def 9.4 copies, and the pattern ====

def closure(seeds, cap=300):
    """close {0, 1, M} under prefixes, summands, anchors, lh, index images, successors and witnesses."""
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
            for e in IDXIMG.get(t, ()):
                if (e,) not in nodes:
                    work.append((e,))
            for s in le2_succ(t) + le2_wit(t):
                if (s,) not in nodes:
                    work.append((s,))
    return nodes

def d94_copy(x):
    """the Def 9.4 copy of x: the least non-dead <=1-nesting base root(P, U^m)."""
    info = le2_info(x)
    (A, W, U, q) = info
    P = A[:-1]
    m = 1
    while m < 8:
        e = root(P + (U,) * m)
        if not is_dead(e):
            return e
        m += 1
    return None

def build(M, cap=300):
    """Phi_3(M): the closure, the Def 9.4 copies (while they add nodes), and the relations."""
    o = tss.from_mat(M)
    nodes = closure([o], cap=cap)
    for _ in range(4):
        extra = []
        ind = sorted((q[0] for q in nodes if len(q) == 1), key=lambda t: tss.cols_term(t, 0))
        for x in ind:
            if le2_info(x) is None:
                continue
            L = lh(x)
            if L == (le2_succ(x)[-1],):
                continue
            if any((tcmp(u, x) < 0 and lh(u) == L for u in ind)):
                continue
            e = d94_copy(x)
            if e is not None and (e,) not in nodes:
                extra.append((e,))
        if not extra:
            break
        nodes = closure(list(nodes) + extra, cap=cap)
    nodes = sorted(nodes, key=lambda q: mat(q))
    idx = {q: i for (i, q) in enumerate(nodes)}
    reach = []
    for (i, q) in enumerate(nodes):
        r = i
        if len(q) == 1:
            hm = mat(lh(q[0]))
            while r + 1 < len(nodes) and mat(nodes[r + 1]) <= hm:
                r += 1
        reach.append(r)
    le2 = set()
    for (i, q) in enumerate(nodes):
        if len(q) == 1:
            for s in le2_succ(q[0]):
                le2.add((i, idx[s,]))
    return (nodes, reach, le2, idx[o])

def show(P):
    """one line per node: index, matrix, <=1-reach, <=2-successors."""
    (nodes, reach, le2, pt) = P
    out = []
    for (i, q) in enumerate(nodes):
        succ = sorted((j for (a, j) in le2 if a == i))
        mark = '*' if i == pt else ' '
        out.append('%s %2d %s  reach %d%s' % (mark, i, tss.oshow(q), reach[i], '  <=2 ' + ' '.join(map(str, succ)) if succ else ''))
    return '\n'.join(out)


if __name__ == '__main__':
    for m in sys.argv[1:]:
        print(m)
        print(show(build(tss.parse(m))))
