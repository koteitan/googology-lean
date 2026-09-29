"""Phi3m = Phi3l plus rules for the level columns K_m of the <=2-able nodes above row 1300 (see ../../POR.md
section 12).  Notation as for Phi3l: x = root(P, U+q), d_m = root(P, U+q, U^m), D = the last omega column
of U, K_1, K_2, ... its level columns (k2cut); lh1(d_m) is the C2 read of K_m's kids relative to d_m.
  kown  : a marker leaf below K_m belongs to the omega column that owns it (the nearest one with level
          <= its y, Phi3h rule (b)): a marker of D collapses to x, a marker of K_j (j < m) to d_j.  Before,
          every marker below K_m collapsed to d_m.  Rows 1332-1377.
  kownk : the same for a marker with kids: it is the frame root(d_j.kids + C2 of its kids), a node.
          Rows 1378-1384.
  ksucc : a unit kid of D right after a level column whose rightmost leaf is a marker of D (a limit
          lambda + Omega_omega inside D's multiplier) is its successor (mult inside D) and adds nothing.
  lsup  : a limit summand D_i whose own <=2-pattern has content (a level column with non-chain kids)
          gives its lsucc block after d_q whether or not it is merged with its successor, and then has
          no witness at its successor.  Rows 1307-1330, 1364, 1457-1459.
  kcut2 : a level column with a same-level omega kid is not a cut: the top level stays.
  kmax  : lh1(x) starts from the farthest lh1(d_m), not from lh1(d_q).  Rows 1520-1557, 1624, 1625.
  ksl   : a same-level omega kid Ks of D next to a level column with content has its own levels, the
          lowest ones (one if Ks has no up-kids, else those of Ks read as a D); the level columns move
          up.  Not when Ks's first up-kid equals K_1 (kbcut: then Ks shares K_1's level).
  kdl   : an omega column K' at D's level inside a level column (Omega_omega inside an Omega_(omega+1)
          factor) brings its own level columns (those of K' read as a D) as the lowest levels, cuts the
          chain, and is read as the kimg summand built on its levels (unless it shares K_1's level,
          kbcut).  Rows 1385-1396, 1405, 1406.
  kdeep : such an omega column deeper inside (below a marker frame) collapses to x (the kimg summand
          built on x), as every Omega_omega of D does.  No fit change; removes 3 violations of the order
          test above (2,2,1)(3,0,0).
  kbcut : a leading up-kid of a same-level K that equals D's first level column K_1 (with content)
          shares K_1's level d_1 and is consumed; other leading up-kids with a cut chain are matched
          with K's own levels.  Rows 1315, 1351, 1402, 1440, 1467-1470, 1539.
  lcov2 : a limit summand D_i with content whose marker is its last kid, followed by a summand that
          repeats its lambda' (up to a unit absorbed by ksucc), is covered: merged, no block, the
          marker reads + x.  Rows 1311, 1339, 1399, 1438, 1461, 1538.
  lastkd: lastcol also for a final marker owned by D and by omega columns at D's level inside an
          up-kid (kdl): it is the Omega_1-multiplier N.  Rows 1345, 1366.
  ibase : an index image that is itself <=2-able comes with its <=1-nesting base.  Rows 1122, 1123, 1192.
  lwpos : the witness of a covered limit prefix (lcov) sits just below the highest successor that its
          content reads (a same-level kid with j leading up-kids reads d_(1+j)).  Row 1268.
Recommended flags (the default of the command line):
  lastcol,mult,fin,c2rel,lastlo,infin,d94,nobase,kimg,idx1,zsib,kbase,ubase,kin,klim,k2cut,k2chain,
  wlast,lsucc,lcov,kiwrap,kown,ksucc,kownk,lsup,kcut2,kmax,ksl,ibase,lwpos,kdl,lcov2,kbcut,kdeep,lastkd
Usage:  python3 phi3m.py [--flags=...] "(0,0,0)(1,1,1)(2,2,1)(3,1,0)(2,0,0)"

Phi3l = Phi3k plus rules for the root runs with several summands and for the nested frames of the
sheet rows above 915 (see ../../POR.md section 11).  x = root(P, U+q) is a <=2-able node with successors
d_m = root(P, U+q, U^m), m = 1..q; the omega columns of U are D_1, ..., D_k (the copied summands of the
root run); a limit summand ends in a marker (its multiplier lambda ends in Omega_omega), and mult puts
its level at its successor.
  wlast : the witness of a proper prefix of D_1..D_k lies in the last <=2-interval (d_(q-1), d_q)
          (d_0 = x) instead of (x, d_1).  x <=2 d_q, and by Carlson 2009 Def 5.3(2) every pattern that is
          cofinal below x (the prefix's <=2-pattern is) is cofinal below d_q, hence occurs above d_(q-1).
  lsucc : a merged group (limit D_i, successor D_(i+1)) where D_i has more <=2-levels than its
          successor: the level of D_i is at its successor (mult), and D_i's own levels come from
          lambda = lambda' + Omega_omega.  Under C2 (Omega_omega -> x) the final Omega_omega of lambda
          becomes x, as the final Omega_1 of the whole argument becomes N in lastcol.  So lh1(x) gets
          the summand root(d_q.kids + (1,0,(D_i[marker -> x]))): the <=1-nesting base of the pattern
          of D_i relative to x, built on d_q (a node, like the ubase summands).  Before, mult read the
          kids of D_i one by one, dropped the Omega_(omega+1) factor and lost D_i's levels.
  lcov  : a summand that only adds levels (its kids are only z=1 columns one level up, recursively)
          after a limit summand is its successor too (as a unit summand in mult).  If the limit's own
          levels are covered by x's levels, its kids are read by C2 (the marker gives + x).  A limit
          prefix whose levels are covered is witnessed at its levels-only successor, as a U-form
          (<=1-nesting base) right above x.
  kiwrap: the kimg read KI reads a run of kids with one C2s call, so consecutive wrapped omega columns
          merge into one level-1 column (one U-form), as C2s does for the kids of D (Phi3g).
Rejected (off by default): kfr -- in an index frame (the image of an index column omega+1), a bare
same-level K nested in a K, or after a summand other than some d_m, is the frame's x instead of d_1.
It fits rows 1147, 1150, 1151, but it maps Omega_omega^3 below the image of a lex-smaller marker with
kids, and the oracle certifies iota(Phi3l+kfr(1150)) <= iota(Phi3l(A)) for
A = (0,0,0)(1,1,1)(2,2,0)(3,3,1)(4,3,1)(5,3,0)(6,4,1)(7,4,1) <lex row 1150.
Recommended flags (the default of the command line):
  lastcol,mult,fin,c2rel,lastlo,infin,d94,nobase,kimg,idx1,zsib,kbase,ubase,kin,klim,k2cut,k2chain,
  wlast,lsucc,lcov,kiwrap
Usage:  python3 phi3l.py [--flags=...] "(0,0,0)(1,1,1)(2,2,1)(2,1,0)(1,1,1)"

Phi3k = Phi3j (= Phi3i with the default flags) plus rules for the sheet rows above 915, i.e. the
matrices from (0,0,0)(1,1,1)(2,1,1) on (see ../../POR.md section 10).  All new rules act in the <=1-reach
lh1(x) of a <=2-able node x = root(P, U+q), whose <=2-successors are d_m = root(P, U+q, U^m), m = 1..q,
and D = the last omega column of U.
  kimg   : a z=1 kid K of D on D's own level (Omega_omega * Omega_omega ...) is the summand
           root(d_1.kids + KI(K.kids)) instead of a plain copy of d (the old doubling, which dropped
           K's kids).  KI: a z=1 kid on D's level -> the same rule (nested); a marker leaf that is the
           last column and a direct kid of K -> the anchor of x (the Omega_1-multiplier of the point);
           any other column -> the C2 read (Omega_omega -> x, Omega_(omega+j) -> Omega_j).
  idx1   : an index column of D of level omega+j, j >= 1, is the summand root(d_q.kids + C2 image);
           consecutive ones accumulate (the prefix fold of the 2-row map).  Before, its image was a
           bare Omega_j with no base.
  zsib   : the number q of <=2-levels counts the z=1 kids of D one level up also when they are not
           D's last kids, and equal siblings add one level each (Omega_(omega+1) * k).
  kbase  : a K whose leading kids are z=1 columns one level up (j levels) uses d_(1+j) as its base.
  ubase  : the index-column summands of idx1 are nodes of the pattern.
  kin    : a z=1 column on D's level nested anywhere in D's kids is read by kimg, not moved rigidly.
  klim   : a marker at the end of a same-level K makes D a limit summand (the mult flag of Phi3h).
  k2cut  : the levels of D follow the chain of first up-kids K_1, K_2, ... of D (one level each);
           a column with z=0 kids (a cut column) ends the chain without a further top level, and then
           each later up-kid of D adds its own chain.  The successor d_m of a column K_m with kids is
           not a <=1-dead end: lh1(d_m) is the fold of the C2 read of K_m's kids relative to d_m
           (a same-level z=1 kid of K_m reaches d_(m+1)), and lh1(x) starts from lh1(d_q).
  k2chain: a column K_m whose only kids are chain columns: d_m reaches d_q.
Recommended flags (the default of the command line):
  lastcol,mult,fin,c2rel,lastlo,infin,d94,nobase,kimg,idx1,zsib,kbase,ubase,kin,klim,k2cut,k2chain
Three further flags are off: c2one (rejected in Phi3j); kframe (tried and rejected: in a nested frame
a same-level K read from x instead of d_1; loses 98 rows); kidx (tried and rejected: a marker of D
with kids read by KI instead of C2; loses 40 rows).
Usage:  python3 phi3k.py [--flags=...] "(0,0,0)(1,1,1)(2,2,1)(3,0,0)"

Phi3j = Phi3i plus one optional flag, c2one, which is OFF by default (a rejected experiment; see
../../POR.md section 9):
  c2one  : in the C2 read of a kid of the last omega summand D of a <=2-able node, an index column
           whose C2 image equals the image of the omega column just before it adds nothing (the two
           images are not summed).
  With c2one, rows 907 and 947 fit the sheet (505 rows instead of 503), but the order test then has a
  certified violation: iota(Phi3j(M907)) <= iota(Phi3j(M')) for the lex-smaller
  M' = (0,0,0)(1,1,1)(2,1,0)(3,2,1)(4,2,0)(3,2,0)(4,3,1)(5,2,0)(6,3,1).  So the flag is not used, and
  with the default flags Phi3j is Phi3i.
Usage:  python3 phi3j.py [--flags=...] "(0,0,0)(1,1,1)(2,1,0)"

Phi3i = phi3h plus three flags:
  infin  : below a finite column an omega column owns no index columns; its markers are finite
           coefficients (except a limit summand followed directly by a unit summand);
  d94    : for every <=2-able x with lh1(x) > lh2(x), add the copy x~ given by Carlson 2009
           Def 9.4 (downward 2-reflection): the least <=1-nesting base root(P, U^m) that is not a
           dead end, unless an earlier node already has <=1-reach lh1(x);
  nobase : switch off phi3h's separate nesting-base rule (d94 covers it).
See ../../POR.md.  Recommended flags: lastcol,mult,fin,c2rel,lastlo,infin,d94,nobase (the default of the
command line).
Usage:  python3 phi3i.py [--flags=...] "(0,0,0)(1,1,1)(2,1,0)"

Phi3h = phi3g with omega-ancestor stacks: a z=0 column is an index column of the NEAREST omega
ancestor whose level is <= its own, finite otherwise.
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
    """nearest omega ancestor (orig_y, shift[, idx_ok]) whose level is <= y: the column is its index
    column (only ancestors that own index columns count)."""
    for a in reversed(st):
        if a[0] <= y:
            if len(a) > 2 and not a[2]:
                return None
            return a
    return None


FIN = ('F',)


def C1(s, N, st, last=False, merge_next=False):
    """st: stack of omega ancestors (orig_y, shift[, idx_ok]), outermost first; st == FIN means the
    subtree hangs below a finite column.  With 'infin', an omega column below a finite column owns no
    index columns (its markers are finite, i.e. Omega_1/Omega_2-multipliers that C1 lowers), unless it is
    a limit summand followed by a plain omega summand (mult: the successor keeps it an index).
    last: s lies on the rightmost path of the last omega summand."""
    y, z, B = s
    if y == 0:
        return s
    fin = st == FIN
    if fin:
        st = ()
    if z == 1:
        if st:                                   # omega under omega: moves rigidly with it
            sh = st[-1][1]
            ok = st[-1][2] if len(st[-1]) > 2 else True
            return (y - sh, 1, C1s(B, N, st + ((y, sh, ok),), last))
        ok = not (fin and 'infin' in FLAGS) or merge_next
        if y == 2:
            return ('W', (2, 1, C1s(B, N, ((2, 0, ok),), last)))
        return (y - 1, 1, C1s(B, N, ((y, 1, ok),), last))
    a = _nearest(st, y)
    if a is not None and not ('lastcol' in FLAGS and last and not B and y == a[0] and a is st[0]):
        return (y - a[1], 0, C1s(B, N, st, last))
    kids = C1s(B, N, FIN, last)                  # below a finite column levels are finite again
    if y == 1:
        return root(add(N[2], kids))
    return (y - 1, 0, kids)


def C1s(B, N, st, last=False, lastidx=None):
    if st is None:
        st = ()
    out = []
    li = len(B) - 1 if lastidx is None else lastidx
    for i, s in enumerate(B):
        mn = s[1] == 1 and i + 1 < len(B) and B[i + 1][1] == 1 and not B[i + 1][2]
        r = C1(s, N, st, last and i == li, mn)
        if r[0] == 'W':
            if out and out[-1][0] == 'W':
                out[-1] = ('W', out[-1][1] + (r[1],))
            else:
                out.append(('W', (r[1],)))
        else:
            out.append(r)
    return addall(tuple((1, 0, r[1]) if r[0] == 'W' else r for r in out))


def C2(s, x, Dy, st=(), last=True, top=False):
    """Omega_omega -> x, Omega_{omega+j} -> Omega_j on a descendant of a copied omega column D at
    level Dy; st = omega columns of the image above s (orig_y, shift), which move rigidly."""
    y, z, B = s
    if y == 0:
        return s
    if z == 1 and 'kdeep' in FLAGS and KDX and KDX[-1] is not None and y == KDX[-1][1] and y < Dy:
        # kdeep: an omega column at D's level deep inside a level column K_m (below a marker frame) is
        # an Omega_omega of D: it collapses to D's target x, as the kimg summand built on x
        x1, Dy1 = KDX[-1]
        KDX.append(None)
        try:
            return Kimg(s, x1, Dy1, x1[2], None, last)
        finally:
            KDX.pop()
    if z == 1 and 'kin' in FLAGS and KCTX and y == KCTX[-1][1] and y == Dy:
        # kin: an omega column at the level of the copied D, nested anywhere in D's kids, is read
        # like a same-level kid of D (Kimg with D's successors), not moved rigidly
        cx, cDy, cdks = KCTX[-1]
        return Kimg(s, cx, cDy, cdks, None, last)
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
    kids = C2s(B, x, Dy, (), last, top=top)
    if y == Dy:
        return root(add(x[2], kids))
    return (y - Dy, 0, kids)


def C2s(B, x, Dy, st=(), last=True, top=False):
    """C2 on a list of kids; consecutive wrapped omega columns merge into one level-1 column."""
    out = []
    prev = None
    for i, b in enumerate(B):
        r = C2(b, x, Dy, st, last and i == len(B) - 1)
        if 'c2one' in FLAGS and top and r == prev and b[1] == 0 and B[i - 1][1] == 1:
            continue                            # c2one: an index column whose image equals the image
                                                # of the omega column just before it adds nothing
        prev = r
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
            if own and (len(own) == 1 or ('lastkd' in FLAGS and all(o == y for o in own) and max(oys) > y)) \
                    and own[-1] == y and oys[0] == y:
                # (lastkd: also when the owners are D and omega columns at D's level inside it, kdl)
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
    if 'zsib' in FLAGS:
        return zsib(D)
    k = 1
    while D[2] and D[2][-1][1] == 1 and D[2][-1][0] == D[0] + 1:
        D = D[2][-1]
        k += 1
    return k


def zsib(D):
    """zsib: the number of <=2-levels of an omega column D: 1 + the levels of its first z=1 kid one
    level up + one for each following kid equal to that first kid (Omega_{omega+1}^k); the kids one
    level up need not be the last kids (they come first in a standard matrix)."""
    up = [c for c in D[2] if c[1] == 1 and c[0] == D[0] + 1]
    if not up:
        return 1
    if 'k2cut' in FLAGS:
        return len(level_cols(D))
    k = 1 + zsib(up[0])
    i = 1
    while i < len(up) and up[i] == up[0]:
        k += 1
        i += 1
    return k


def k2kids(K2, kind):
    """k2cut: the kids of the first up-kid K2 of D other than its chain kids (z=1 one level up).
    kind 'cut': those that cut the next <=2-level (any z=0 kid); 'all': all non-chain kids."""
    rest = [c for c in K2[2] if not (c[1] == 1 and c[0] == K2[0] + 1)]
    if kind == 'cut' and 'kcut2' in FLAGS and any(c[1] == 1 and c[0] == K2[0] for c in K2[2]):
        return []                               # kcut2: a same-level omega kid keeps the top level
    if kind == 'cut':
        # (kdl: an omega column below K's level, e.g. at D's level, cuts the chain like a z=0 kid)
        return [c for c in rest if c[1] == 0 or ('kdl' in FLAGS and c[0] < K2[0])]
    return rest


def subcols(K):
    """k2cut: K followed by the level columns above it: the columns of its first up-kid (recursively);
    then those of each later up-kid that equals the first, or of every later up-kid when the first
    one's list ends in a cut column (one with z=0 kids)."""
    up = [c for c in K[2] if c[1] == 1 and c[0] == K[0] + 1]
    if not up:
        return [K]
    ch = subcols(up[0])
    cut = bool(k2kids(ch[-1], 'cut'))
    out = [K] + ch
    for S in up[1:]:
        if S == up[0] or cut:
            out += subcols(S)
    return out


def level_cols(D):
    """k2cut: the column behind each <=2-successor d_m (m = 1..q) of a <=2-able node whose last omega
    column is D; None for the top level without a column.  The top level exists unless the list of
    D's first up-kid ends in a cut column."""
    up = [c for c in D[2] if c[1] == 1 and c[0] == D[0] + 1]
    if not up:
        return [None]
    first = subcols(up[0])
    cols = subcols(D)[1:]
    ks = [c for c in D[2] if c[1] == 1 and c[0] == D[0]]
    if 'ksl' in FLAGS and ks and any(k2kids(c, 'all') for c in cols) and not (
            'kbcut' in FLAGS and [g for g in ks[0][2] if g[1] == 1 and g[0] == D[0] + 1][:1] == [up[0]]):
        # ksl: a same-level omega kid Ks of D next to a K_1 chain with content has its own levels (one
        # if it has no up-kids, else those of Ks read as a D), the lowest ones; K_1's levels move up.
        # kbcut: not when Ks's first up-kid equals K_1 (then Ks shares K_1's level)
        kup = [g for g in ks[0][2] if g[1] == 1 and g[0] == D[0] + 1]
        if not kup:
            cols = [None] + cols
        elif 'kbcut' in FLAGS:
            cols = level_cols(ks[0]) + cols
    elif 'kdl' in FLAGS and any(g[1] == 1 and g[0] == D[0] and not shares_k1(g, up[0])
                                for c in cols for g in k2kids(c, 'all')):
        # kdl: an omega column K' at D's level inside a level column K_m (Omega_omega inside an
        # Omega_(omega+1) factor) brings its own levels (those of K' read as a D), the lowest ones
        Kp = [g for c in cols for g in k2kids(c, 'all') if g[1] == 1 and g[0] == D[0]
              and not shares_k1(g, up[0])][0]
        cols = level_cols(Kp) + cols
    return cols + ([] if k2kids(first[-1], 'cut') else [None])


def d1_info(t):
    """k2cut: if t = root(P, U+q, U^m) is the m-th <=2-successor d_m of x = root(P, U+q) and the m-th
    column K_m of the chain of first up-kids of D (D = U's last omega column; K_1 = D's first z=1 kid one
    level up, K_(j+1) = K_j's) has kids, return (x, K_m, m, q)."""
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
    if m > 1 and 'k2chain' not in FLAGS:
        return None
    cols = level_cols(U[2][-1])
    if m > len(cols) or cols[m - 1] is None:
        return None
    K = cols[m - 1]
    if not (k2kids(K, 'all') or ('k2chain' in FLAGS and K[2])):
        return None
    return x, K, m, info[3]


def zlead(K):
    """kbase: number of <=2-levels a z=1 column K adds above its own level (0 if none)."""
    return zsib(K) - 1


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
    if 'k2cut' in FLAGS:
        di = d1_info(t)
        if di is not None:
            x1, K2, m, q = di
            U = t[2][-1]
            top = root(x1[2] + (U,) * q)
            if not k2kids(K2, 'all'):
                return (top,)                    # k2chain: a chain-only K_m: d_m reaches d_q
            nx = root(x1[2] + (U,) * (m + 1)) if m < q else t
            dks = [nx[2]]
            # d_m reaches the C2 read of K_m's own kids relative to d_m (level of K_m); a same-level
            # omega kid of K_m reaches the next successor d_(m+1)
            kk = tuple(k2kids(K2, 'all'))
            if 'kown' in FLAGS:
                # kown: a marker leaf below K_m belongs to the omega column that owns it (the nearest
                # one with level <= its y): D (level K_m.y - m) or K_j (level D.y + j).  It collapses
                # to that column's target, d_j (d_0 = x), not to d_m (Phi3h rule (b))
                cols = level_cols(U[2][-1])
                own = {U[2][-1][0]: 0}              # level of each owner -> index j of its target d_j
                for i, col in enumerate(cols[:m - 1]):
                    if col is not None and col[0] < K2[0]:
                        own[col[0]] = i + 1         # (K_m owns the markers at its own level)
                kk = tuple(ownleaf(c, own, x1, U) for c in kk)
            if 'kdl' in FLAGS:
                # kdl: such a D-level omega column is the kimg summand built on d_1 (its own level)
                Dy_ = U[2][-1][0]
                dall = [root(x1[2] + (U,) * i)[2] for i in range(1, q + 1)]
                kk2 = []
                for c in kk:
                    if c[1] == 1 and c[0] == Dy_:
                        e = Kimg(c, x1, Dy_, dall, None, False)
                        IDXIMG.setdefault(x1, set()).add(e)
                        c = (0, 0, e[2])
                    kk2.append(c)
                kk = tuple(kk2)
            KCTX.append((t, K2[0], dks))
            KDX.append((x1, U[2][-1][0]))
            try:
                return _lh1_kids((t,), t, (K2[0], K2[1], kk), K2[0], [], t[2], dks,
                                 None, True)
            finally:
                KCTX.pop()
                KDX.pop()
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
            if 'klim' in FLAGS and a is not D and a[0] == D[0] == L[0]:
                continue                        # klim: a same-level omega kid K of D passes the marker up
            return a is D and a[0] == L[0]
    return False


def levels_only(D):
    """lcov: the kids of the omega column D are only z=1 columns one level up, recursively (the
    summand is Omega_omega * Omega_(omega+1)^k-like: it adds <=2-levels and nothing else)."""
    return all(c[1] == 1 and c[0] == D[0] + 1 and levels_only(c) for c in D[2])


def strip_marker(D):
    """lcov2: D without the final marker on its rightmost path (lambda' of lambda = lambda' + Omega_omega)."""
    y, z, B = D
    if not B:
        return None
    last = strip_marker(B[-1])
    return (y, z, B[:-1] + ((last,) if last is not None else ()))


def covers(D1, D2):
    """lcov2: the summand D2 after the limit summand D1 = Omega_omega*(lambda' + Omega_omega) repeats
    lambda' (up to a unit that ksucc absorbs): the pattern of D1 is covered by that of D2."""
    if not has_content(D1) or not D1[2] or D1[2][-1] != (D1[0], 0, ()):
        return False                            # only a limit with content whose marker is a kid of D1
    s1 = strip_marker(D1)
    if s1 is None or not s1[2]:
        return False
    if D2 == s1:
        return True
    return 'ksucc' in FLAGS and D2[2] and D2[2][-1] == LEAF and len(D2[2]) >= 2 \
        and ends_in_marker(D2[2][-2], D2[0]) and (D2[0], D2[1], D2[2][:-1]) == s1


def lchain(y, k):
    """lcov: the levels-only omega column at level y with k <=2-levels (a chain of k-1 up-kids)."""
    return (y, 1, (lchain(y + 1, k - 1),) if k > 1 else ())


def groups(Om):
    """mult: <=2-levels of the omega summands; a unit summand right after a limit summand is its
    successor and belongs to the same level.  Returns list of (start, end) index ranges."""
    out = []
    i = 0
    while i < len(Om):
        j = i
        if 'mult' in FLAGS and is_limit(Om[j]) and j + 1 < len(Om) and not Om[j + 1][2]:
            j += 1
        elif 'lcov' in FLAGS and is_limit(Om[j]) and j + 1 < len(Om) and levels_only(Om[j + 1]):
            j += 1                              # lcov: a summand that only adds levels is a successor too
        elif 'lcov2' in FLAGS and is_limit(Om[j]) and j + 1 < len(Om) and covers(Om[j], Om[j + 1]):
            j += 1                              # lcov2: the successor repeats lambda' (covered)
        out.append((i, j))
        i = j + 1
    return out


def KI(B, x, Dy, dk, t0, last):
    """kimg: images of the kids B of a same-level omega column K (level Dy of the copied D).
    z=1 kid at level Dy -> Kimg (a summand root(d.kids + KI(kids))); a marker leaf that is the last
    column and a direct kid of K -> the anchor t0 of x (the Omega_1-multiplier of the point);
    everything else -> the C2 read (Omega_omega -> x, Omega_{omega+j} -> Omega_j)."""
    out = []
    run = []                                   # kiwrap: pending kids for one C2s call

    def flush(lg):
        if run:
            out.extend(C2s(tuple(run), x, Dy, (), lg))
            run.clear()
    for i, g in enumerate(B):
        lg = last and i == len(B) - 1
        if 'kiwrap' in FLAGS and g[0] != 0 and not (g[1] == 1 and g[0] == Dy) and not (g[1] == 0 and g[0] >= Dy):
            # kiwrap: a run of kids read by C2 is read in one C2s call, so consecutive wrapped omega
            # columns merge into one level-1 column (one U-form), as in C2s
            run.append(g)
            if i == len(B) - 1:
                flush(lg)
            continue
        flush(False)
        if g[0] == 0:
            out.append(g)
        elif g[1] == 1 and g[0] == Dy:
            out.append(Kimg(g, x, Dy, dk, t0, lg, nested=True))
        elif g[1] == 0 and g[0] == Dy and not g[2] and lg and t0 is not None:
            out.append(t0)
        elif g[1] == 0 and g[0] == Dy:
            out.append(root(add(x[2], KI(g[2], x, Dy, dk, None, lg))))
        elif g[1] == 0 and g[0] > Dy:
            out.append((g[0] - Dy, 0, KI(g[2], x, Dy, dk, None, lg)))
        else:
            out.append(C2(g, x, Dy, (), lg))
    return addall(tuple(out))


IDXSET = set()       # kfr: all index-column images of idx1 (the frames of level omega+1)


def is_frame(x):
    """kfr: x = root(A) with A = (..., U+q) lies in an index frame: its <=1-nesting base
    root(A[:-1] + U) is the image of an index column of level omega+1 (idx1)."""
    A = x[2]
    if len(A) < 2:
        return False
    U = (A[-1][0], A[-1][1], tuple(g for g in A[-1][2] if g != LEAF))
    return root(A[:-1] + (U,)) in IDXSET


FRAMEX = []          # kfr: stack of (x, is_frame(x)) of the lh1_le2 calls in progress


def k1_of(x):
    """kbcut: the first up-kid K_1 of the last omega column D of x's U (or None)."""
    D = le2_info(x)[2][2][-1]
    up = [g for g in D[2] if g[1] == 1 and g[0] == D[0] + 1]
    return up[0] if up else None


def shares_k1(g, K1):
    """kdl/kbcut: the omega column g's first up-kid equals K_1 (g shares K_1's level)."""
    if 'kbcut' not in FLAGS:
        return False
    gu = [c for c in g[2] if c[1] == 1 and c[0] == g[0] + 1]
    return bool(gu) and gu[0] == K1


def Kimg(K, x, Dy, dk, t0, last, nested=False):
    """kimg: a same-level omega kid K of D (Omega_omega * Omega_omega ...) is read as the summand
    d * omega^(K's kids): root(d.kids + KI(K.kids)); a bare K gives d itself (the old doubling).
    kbase: with q successors d_1 < ... < d_q of x, d = d_1; a K whose leading kids are z=1 columns one
    level up (j levels) uses d_{1+j} and drops those kids.  dk may be a list [d_1.kids, ..., d_q.kids]."""
    if isinstance(dk, list):
        B = K[2]
        j = 0
        if 'kbase' in FLAGS:
            j = min(zlead(K), len(dk) - 1)
            up = [c for c in B if c[1] == 1 and c[0] == Dy + 1]
            if 'kbcut' in FLAGS and up and x is not None and le2_info(x) is not None \
                    and k1_of(x) is not None and up[0] == k1_of(x) and k2kids(up[0], "all"):
                # kbcut: a first up-kid equal to K_1 shares K_1's level d_1; only it is consumed
                j = 0
                B = tuple(c for c in B if c is not up[0])
            elif j or ('kbcut' in FLAGS and up):
                # kbcut: leading up-kids are matched with levels also when their chain is cut (j = 0):
                # with K_1's level if equal to K_1, else with K's own lowest level (ksl)
                B = tuple(c for c in B if not (c[1] == 1 and c[0] == Dy + 1))
        base = dk[j]
        if 'kfr' in FLAGS and FRAMEX and FRAMEX[-1][1] and FRAMEX[-1][0] == x and j == 0 and nested \
                and not B:
            return x                            # kfr: in an index frame, a bare K nested in a K or
                                                # after a summand other than d_m is the frame's x
        return root(add(base, KI(B, x, Dy, dk, None if not last else t0, last)))
    return root(add(dk, KI(K[2], x, Dy, dk, None if not last else t0, last)))


KDX = []             # kdeep: stack of (x, D.y) of the k2cut reads of lh1(d_m) in progress
KCTX = []            # kin: stack of (x, Dy, [d_1.kids, ...]) of the lh1_le2 calls in progress
IDXIMG = {}          # ubase: x -> the index-column images e = root(d.kids + ...) made in lh1_le2(x)


def lh1_le2(x, info):
    A, W, U, q = info
    S = (root(A + (U,) * q),)
    Om = U[2]
    D = Om[-1]
    d = zdepth(D)
    if q < d:
        return lh(root(A[:-1] + (plus(W),)))
    lo_, hi_ = groups(Om)[-1] if 'mult' in FLAGS else (len(Om) - 1, len(Om) - 1)
    dk = S[0][2]
    if 'k2cut' in FLAGS and d1_info(S[0]) is not None:
        S = lh(S[0])                           # k2cut: x reaches as far as its top successor d_q
    if 'kmax' in FLAGS:
        # kmax: x reaches as far as the farthest of its successors d_1..d_q
        for m in range(1, q):
            dm = root(A + (U,) * m)
            if d1_info(dm) is not None:
                L = lh(dm)
                if scmp(L, S) > 0:
                    S = L
    if 'kbase' in FLAGS:
        dks = [root(A + (U,) * m)[2] for m in range(1, q + 1)]
    else:
        dks = [dk]
    if 'kframe' in FLAGS and len(A) >= 2 and A[-2][1] != 1:
        # kframe: x lies in a nested frame (its prefix ends in a copied U-form, not in a root omega
        # column); there a same-level kid K is read from x itself, not from the successor d_1
        dks = [x[2]] + dks[1:]
    t0 = root(A[:-1]) if len(A) >= 2 else None
    FRAMEX.append((x, 'kfr' in FLAGS and is_frame(x)))
    try:
        return _lh1_groups(S, x, A, U, q, Om, lo_, hi_, dk, dks, t0)
    finally:
        FRAMEX.pop()


def _lh1_groups(S, x, A, U, q, Om, lo_, hi_, dk, dks, t0):
    for gi, Dg in enumerate(Om[lo_:hi_ + 1]):
        Dy = Dg[0]
        if 'lsucc' in FLAGS and lo_ + gi < hi_ and is_limit(Dg) and (zsib(Dg) > zsib(Om[hi_]) or (
                'lsup' in FLAGS and has_content(Dg))) and not ('lcov2' in FLAGS and covers(Dg, Om[hi_])):
            # lsup: also when D_i's own <=2-pattern has content (an up-kid with non-chain kids, e.g.
            # a cut chain [c (d] d+..)), whatever the levels of its successor
            # lsucc: the limit summand Omega_omega*lambda of a merged group (limit, unit).  Its level is
            # at its successor (mult); lambda itself, with its final Omega_omega (the marker) read as x
            # (C2: Omega_omega -> x), is the pattern of a U-form built on the top successor d_q
            e = root(add(root(A + (U,) * q)[2], ((1, 0, (limx(Dg, x),)),)))
            IDXIMG.setdefault(x, set()).add(e)      # a node, like the ubase summands
            S = oplus(S, e)
            continue
        idx = []
        KCTX.append((x, Dy, dks))
        try:
            S = _lh1_kids(S, x, Dg, Dy, idx, dk, dks, t0, lo_ + gi == len(Om) - 1)
        finally:
            KCTX.pop()
    if 'lsup' in FLAGS:
        # lsup: a limit summand with content in an earlier group (not merged with its successor)
        # also gives its block after d_q, instead of a witness at its successor
        for Dg in Om[:lo_]:
            if is_limit(Dg) and has_content(Dg):
                e = root(add(root(A + (U,) * q)[2], ((1, 0, (limx(Dg, x),)),)))
                IDXIMG.setdefault(x, set()).add(e)
                S = oplus(S, e)
    return S


def has_content(D):
    """lsup: some level column of D (its up-kid chain) has kids other than chain columns."""
    if not any(c[1] == 1 and c[0] == D[0] + 1 for c in D[2]):
        return False
    return any(k2kids(c, 'all') for c in subcols(D)[1:])


def limx(D, x):
    """lsucc: D with the final marker on its rightmost path (the Omega_omega that makes D a limit
    summand) replaced by the y=0 column of x (Omega_omega -> x)."""
    y, z, B = D
    if not B:
        return (0, 0, x[2])
    return (y, z, B[:-1] + (limx(B[-1], x),))


def scmp(a, b):
    """kmax: compare two sums (tuples of terms, Cantor normal form) lexicographically."""
    for u, v in zip(a, b):
        c = tcmp(u, v)
        if c:
            return c
    return (len(a) > len(b)) - (len(a) < len(b))


def ownleaf(c, own, x1, U):
    """kown: a z=0 column c that is a marker of D or of a level column K_j below K_m (own: level ->
    index j of the owner's target d_j, d_0 = x): the target d_j, as a y=0 column."""
    if c[1] == 0 and c[0] >= 1:
        j = own.get(c[0])
        if j is not None:
            dj = root(x1[2] + (U,) * j)
            if not c[2]:
                return (0, 0, dj[2])
            if 'kownk' in FLAGS:
                # kownk: a marker with kids is the frame root(d_j.kids + C2 of its kids), read at the
                # level of its owner (Omega_omega -> d_j); the frame is a node
                e = root(add(dj[2], C2s(c[2], dj, c[0])))
                IDXIMG.setdefault(x1, set()).add(e)
                return (0, 0, e[2])
    return c


def ends_in_marker(K, Dy):
    """ksucc: the rightmost path of K ends in a z=0 leaf at level Dy (a marker of D)."""
    while K[2]:
        K = K[2][-1]
    return K[1] == 0 and K[0] == Dy


def _lh1_kids(S, x, Dg, Dy, idx, dk, dks, t0, lastD):
    for ci, c in enumerate(Dg[2]):
        lst = lastD and ci == len(Dg[2]) - 1
        if 'ksucc' in FLAGS and c == LEAF and ci > 0 and Dg[2][ci - 1][1] == 1 \
                and Dg[2][ci - 1][0] == Dy + 1 and ends_in_marker(Dg[2][ci - 1], Dy):
            continue                            # ksucc: a unit right after a limit up-kid is its successor
        if c[1] == 1:
            if c[0] == Dy:
                if 'kimg' in FLAGS:
                    S = oplus(S, Kimg(c, x, Dy, dks, t0, lst,
                                      nested=any(t[2] not in dks for t in S)))
                else:
                    S = oplus(S, S[0])
            continue
        if 'idx1' in FLAGS and c[0] > Dy:
            # an index column of level omega+j (j>=1) of D: its C2 image Omega_j... is a new
            # summand of d; consecutive index columns accumulate (the 2-row prefix fold)
            idx.append(KI((c,), x, Dy, dks, None, lst)[0] if 'kimg' in FLAGS else C2(c, x, Dy, (), lst, top=True))
            e = root(add(dk, addall(tuple(idx))))
            IDXIMG.setdefault(x, set()).add(e)
            IDXSET.add(e)
            if 'ibase' in FLAGS and le2_info(e) is not None:
                # ibase: an index image that is itself <=2-able comes with its <=1-nesting base (its
                # U-form without the leaves), as every <=2-able node reached by the nesting limit
                W = e[2][-1]
                IDXIMG[x].add(root(e[2][:-1] + ((W[0], W[1], tuple(g for g in W[2] if g != LEAF)),)))
            S = oplus(S, e)
            continue
        if 'kidx' in FLAGS and c[0] == Dy and c[2]:
            S = oplus(S, KI((c,), x, Dy, dks, None, lst)[0])
            continue
        S = oplus(S, C2(c, x, Dy, (), lst, top=True) if c[0] >= 1 else root(c[2]))
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
        if 'lsup' in FLAGS and is_limit(pre[-1]) and has_content(pre[-1]):
            continue                            # lsup: its block after d_q replaces the witness
        if 'lcov' in FLAGS and is_limit(pre[-1]) and 1 < zsib(pre[-1]) <= q:
            # lcov: a limit prefix whose own levels are covered by the levels of x is witnessed at its
            # levels-only successor (pre + a chain with the same number of levels), as a U-form (a
            # <=1-nesting base, as in the nesting limit) right above x
            j = 0
            if 'lwpos' in FLAGS:
                # lwpos: the witness sits just below the highest successor its content reads (a same-
                # level kid with j leading up-kids reads d_(1+j), kbase), i.e. in (d_j, d_(j+1))
                j = max([min(zlead(c), q - 1) for c in pre[-1][2] if c[1] == 1 and c[0] == pre[-1][0]] + [0])
            out.append(root(A + (U,) * j + ((1, 0, pre + (lchain(pre[-1][0], zsib(pre[-1])),)),)))
            continue
        if 'mult' in FLAGS and is_limit(pre[-1]):
            pre = pre + ((2, 1, ()),)          # the level of a limit summand is witnessed at its successor
        if 'wlast' in FLAGS:
            # wlast: the witness of a prefix lies in the last <=2-interval (d_(q-1), d_q) (d_0 = x): the
            # pattern it carries is cofinal below x, so by Def 5.3(2) also below d_q, above d_(q-1)
            w = root(A + (U,) * (q - 1) + (plus((1, 0, pre)),))
        else:
            w = root(A + (plus((1, 0, pre)),))
        if le2_info(w) is not None:
            out.append(w)
            Dl = pre[-1]
            if Dl[2] and Dl[2][-1][1] == 1 and Dl[2][-1][0] == Dl[0]:
                if 'nobase' not in FLAGS:
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
            if 'ubase' in FLAGS:
                for e in IDXIMG.get(t, ()):
                    if (e,) not in nodes:
                        work.append((e,))
            for s in le2_succ(t) + le2_wit(t):
                if (s,) not in nodes:
                    work.append((s,))
    return nodes


def d94_copy(x):
    """Carlson Def 9.4: 2-reflecting {x} downward from its <=2-successor to x gives x~ < x with
    x~ <=1 y iff x <=1 y (y >= x): realised as the least non-dead <=1-nesting base root(P, U^m)."""
    info = le2_info(x)
    A, W, U, q = info
    P = A[:-1]
    m = 1
    while is_dead(root(P + (W,) + (U,) * m)) and m < 8:
        m += 1
    e = root(P + (U,) * m) if False else None
    # the nesting base below x: root(P', U^m) where P' = P (x = root(P, U+q)); least non-dead
    m = 1
    while m < 8:
        e = root(P + (U,) * m)
        if not is_dead(e):
            return e
        m += 1
    return None


def build(M, cap=300):
    o = tss.from_mat(M)
    nodes = closure([o], cap=cap)
    if 'd94' in FLAGS:
        for _ in range(4):
            extra = []
            ind = sorted((q[0] for q in nodes if len(q) == 1), key=lambda t: tss.cols_term(t, 0))
            for x in ind:
                if le2_info(x) is None:
                    continue
                L = lh(x)
                if L == (le2_succ(x)[-1],):
                    continue                          # no extras: lh1 = lh2
                if any(tcmp(u, x) < 0 and lh(u) == L for u in ind):
                    continue                          # an earlier node already <=1-reaches lh1(x)
                e = d94_copy(x)
                if e is not None and (e,) not in nodes:
                    extra.append((e,))
            if not extra:
                break
            nodes = closure(list(nodes) + extra, cap=cap)
    nodes = sorted(nodes, key=lambda q: mat(q))
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
    FLAGS.update({'lastcol', 'mult', 'fin', 'c2rel', 'lastlo', 'infin', 'd94', 'nobase', 'kimg', 'idx1',
                  'zsib', 'kbase', 'ubase', 'kin', 'klim', 'k2cut', 'k2chain', 'wlast', 'lsucc', 'lcov',
                  'kiwrap', 'kown', 'ksucc', 'kownk', 'lsup', 'kcut2', 'kmax', 'ksl', 'ibase', 'lwpos', 'kdl',
                  'lcov2', 'kbcut', 'kdeep', 'lastkd'})
    args = sys.argv[1:]
    for a in [a for a in args if a.startswith('--flags=')]:
        FLAGS.clear()
        FLAGS.update(f for f in a[len('--flags='):].split(',') if f)
    for m in [a for a in args if not a.startswith('--flags=')]:
        print(m)
        print(show(build(tss.parse(m))))
