"""exb -> bms3 by the rule program: `trioMatrixLSt` and `trioRuleMatrixSt`.

A port of the rule program of https://github.com/koteitan/trio (rules 1-10 of
tools/probe_eps_range.py) as the Lean library has it after all its fixes:

    trioMatrixLSt alpha = trioRuleMatrixSt (ofTermFix alpha)
                                          (Trio/TrioFixStrip.lean:422)
    trioRuleMatrixSt a  = toRows (MSt a)  (Trio/TrioFixStrip.lean:410)

`Trio/` is Googology/Trans/ExBuchholz/BMS/Trio/. The layers are
- TrioRules.lean       rules 1-10 (ordinals, columns, Ctx, writeLevel, ...),
- TrioRules2.lean      Fixes A-D (MOmega2, MpsiLevel2, leafNameF.rest, findSub),
- TrioRules3.lean      Fix E (MpsiLevel3),
- TrioRulesNonLast.lean Fix N (CtxN, leafNameNF, upgradeNF, fixN, ...),
- TrioRulesAll.lean    the merge (MstepAll; its pieces are used through the copy below),
- TrioFixOfTerm.lean   the reading ofTermFix,
- TrioFixStrip.lean    the strip patch: stripSt, uncollapses and copies of
                       tailBlockF ... MstepAll with them (the functions `*_st` here).
Only what `trioRuleMatrixSt` and `ofTermFix` call is ported, one Python function
per Lean definition, each cited by path:line.

**Fuel.** Every fuel argument is kept exactly as Lean has it (`fuel = 200`,
TrioRules.lean:79, and the structural fuels such as `cs.size + 1`). Above the
fuel the result is Lean's, e.g. the towers T_202 and T_203 get one matrix
(Trio/TrioFixStripCalibNo.lean:63). `cmpF`, `lvlF`, `add` here are fuelled copies
of the unfuelled ones in notation/label.py (that module is not changed).

**Representation.** An `Od` / `Ex` is as in notation/label.py: an Od is a tuple
of pairs (exponent, coefficient); an exponent is ('o', od), ('W', v) or
('psi', v, x). An Ordering is -1, 0, 1. `Option` is None / the value (so
`some []` is `()`, distinct from None). A column `Col` is a tuple (x, y, z),
x y ints, z a bool; `Cols` (Lean `Array Col`) is a tuple of columns. The
builder's state (`StateM Ctx` / `StateM CtxN`) is a mutable object passed
along; every Lean `modify`/`set` is an assignment to it. `Mf` (the builder one
fuel step down) is a Python function Od -> Cols; `MfuelSt n a` is memoised on
(n, a), which is sound because it is a pure function.

A term (exb) is as in notation/exb.py: a tuple of pairs (a, b) = psi_a(b).
The result `List (List Nat)` is a tuple of 3-tuples.
"""

import sys
import threading

from notation.label import O0, ONE, ato, is_atom, nat, wpow
from notation import exb_std

TRIO = 'Googology/Trans/ExBuchholz/BMS/Trio/'

# Trio/TrioRules.lean:79  def fuel : Nat := 200
FUEL = 200


def _cmp(a, b):
    return (a > b) - (a < b)


# ================================================================ TrioRules.lean
# ---------------------------------------------------------------- ordinals

# TrioRules.lean:107  lvlF
#   | 0, _ => none | _+1, .W v => some v
#   | _+1, .psi v _ => match v with | [] => none | [(.W u, 1)] => some u | _ => some v
#   | _+1, .o [] => none | n+1, .o ((e, _) :: _) => lvlF n e
def lvl_f(n, x):
    while True:
        if n == 0:
            return None
        if x[0] == 'W':
            return x[1]
        if x[0] == 'psi':
            v = x[1]
            if v == ():
                return None
            if len(v) == 1 and v[0][1] == 1 and v[0][0][0] == 'W':
                return v[0][0][1]
            return v
        od = x[1]
        if od == ():
            return None
        n -= 1
        x = od[0][0]


# TrioRules.lean:119  lvl x = lvlF fuel x
def lvl(x):
    return lvl_f(FUEL, x)


# TrioRules.lean:122  lvlO a = lvl (.o a)
def lvl_o(a):
    return lvl(('o', a))


# TrioRules.lean:125  isCardPsi: .psi [(.W _, 1)] _ => true
def is_card_psi(x):
    return (x[0] == 'psi' and len(x[1]) == 1 and x[1][0][1] == 1
            and x[1][0][0][0] == 'W')


# TrioRules.lean:131  kindA
def kind_a(x):
    if x[0] == 'W':
        return 0
    return -1 if is_card_psi(x) else 1


# TrioRules.lean:137  argA
def arg_a(x):
    return x[2] if x[0] == 'psi' else ()


# TrioRules.lean:142  cmpAtomWith (cmpF m)
#   (c ((lvl x).getD []) ((lvl y).getD [])).then
#     ((compare (kindA x) (kindA y)).then (match x with | .W _ => .eq | _ => c (argA x) (argA y)))
def _cmp_atom_f(m, x, y):
    lx, ly = lvl(x), lvl(y)
    r = cmp_f(m, () if lx is None else lx, () if ly is None else ly)
    if r:
        return r
    r = _cmp(kind_a(x), kind_a(y))
    if r:
        return r
    if x[0] == 'W':
        return 0
    return cmp_f(m, arg_a(x), arg_a(y))


# TrioRules.lean:150  cmpExpWith (cmpF m)
def _cmp_exp_f(m, x, y):
    if is_atom(x) and is_atom(y):
        return _cmp_atom_f(m, x, y)
    return cmp_f(m, ato(x), ato(y))


# TrioRules.lean:159  cmpF: | 0 => fun _ _ => .eq | n+1 => cmpOrdWith (cmpF n)
# TrioRules.lean:154  cmpOrdWith c a b: the summands lexicographically
#   ((cmpExpWith c) on exponents, then compare on coefficients), then the lengths.
def cmp_f(n, a, b):
    if n == 0:
        return 0
    for (ex, cx), (ey, cy) in zip(a, b):
        r = _cmp_exp_f(n - 1, ex, ey) or _cmp(cx, cy)
        if r:
            return r
    return _cmp(len(a), len(b))


# TrioRules.lean:164  cmpOrd a b = cmpF fuel a b
def cmp_ord(a, b):
    return cmp_f(FUEL, a, b)


# TrioRules.lean:167  cmpExp x y = cmpExpWith (cmpF fuel) x y
def cmp_exp(x, y):
    return _cmp_exp_f(FUEL, x, y)


# TrioRules.lean:170  add
def add(a, b):
    if not b:
        return a
    lead, cb = b[0]
    keep = tuple(t for t in a if cmp_exp(t[0], lead) == 1)
    same = [t for t in a if cmp_exp(t[0], lead) == 0]
    if same:
        return keep + ((lead, same[0][1] + cb),) + b[1:]
    return keep + b


# ---------------------------------------------------------------- pieces of a normal form

# TrioRules.lean:327  units a = a.flatMap fun ec => List.replicate ec.2 ec.1
def units(a):
    return tuple(e for e, c in a for _ in range(c))


# TrioRules.lean:330  predBeta
def pred_beta(beta):
    if not beta:
        return ()
    e, k = beta[0]
    if e == O0:
        return nat(k - 1 if k >= 1 else 0)
    return beta


# ---------------------------------------------------------------- columns

DEFAULT_COL = (0, 0, False)     # TrioRules.lean:361  `deriving Inhabited`: ⟨0, 0, false⟩


# TrioRules.lean:367  colAt cs i = cs.getD i default
def col_at(cs, i):
    return cs[i] if 0 <= i < len(cs) else DEFAULT_COL


# TrioRules.lean:370  lastC cs = colAt cs (cs.size - 1)
def last_c(cs):
    return col_at(cs, max(len(cs) - 1, 0))


# TrioRules.lean:373  setLastY (Array.modify: no change on an empty array)
def set_last_y(cs, y):
    if not cs:
        return cs
    c = cs[-1]
    return cs[:-1] + ((c[0], y, c[2]),)


# TrioRules.lean:376  liftCols
def lift_cols(cs):
    return tuple((x + 1, y + 1, z) for x, y, z in cs)


# TrioRules.lean:379  storeyOf cs y = setLastY (liftCols cs) y
def storey_of(cs, y):
    return set_last_y(lift_cols(cs), y)


_FOREST = {}


# TrioRules.lean:383  forest: each column's nearest earlier column with a smaller x
def forest(cs):
    r = _FOREST.get(cs)
    if r is None:
        out = []
        for i in range(len(cs)):
            xi = cs[i][0]
            p = None
            for j in range(i - 1, -1, -1):
                if cs[j][0] < xi:
                    p = j
                    break
            out.append(p)
        r = tuple(out)
        if len(_FOREST) > 200000:
            _FOREST.clear()
        _FOREST[cs] = r
    return r


def _get(par, i):
    """`par.getD i none`."""
    return par[i] if 0 <= i < len(par) else None


# TrioRules.lean:390  isLevel
def is_level(cs, par, i):
    x, y, z = col_at(cs, i)
    if z or y < 1:
        return False
    p = _get(par, i)
    if p is None:
        return True
    cp = col_at(cs, p)
    if not cp[2]:
        return not (p != 0 and cp[1] == 0)
    gp = _get(par, p)
    if gp is None:
        return True
    return not col_at(cs, gp)[2]


# TrioRules.lean:403  relative
def relative(cs, par, i):
    return col_at(cs, i)[2] or is_level(cs, par, i)


# TrioRules.lean:407  commonPrefix
def common_prefix(a, b):
    n = 0
    for p, q in zip(a, b):
        if p != q:
            break
        n += 1
    return n


# TrioRules.lean:411  lastRootIdx
def last_root_idx(cs):
    par = forest(cs)
    for j in range(len(cs) - 1, -1, -1):
        if col_at(cs, j)[2]:
            p = _get(par, j)
            if p is None or not col_at(cs, p)[2]:
                return j
    return None


# TrioRules.lean:420  lastRootPlain: (level, x) of the last root
def last_root_plain(cs):
    i = last_root_idx(cs)
    if i is None:
        return (0, 0)
    c = col_at(cs, i)
    return (c[1], c[0])


# TrioRules.lean:427  lastRoot
def last_root(cs):
    i = last_root_idx(cs)
    if i is None:
        return (0, 0)
    c = col_at(cs, i)
    return (c[1], c[0] + (1 if last_c(cs)[2] else 0))


# TrioRules.lean:433  lastStorey
def last_storey(cs):
    par = forest(cs)
    idx = [i for i in range(len(cs)) if i >= 1 and is_level(cs, par, i)]
    return idx[-1] if idx else 0


# TrioRules.lean:438  zIdx
def z_idx(seg):
    return [j for j in range(len(seg)) if not col_at(seg, j)[2]]


# TrioRules.lean:441  runEnd (fuel n)
def run_end(cs, n, j):
    while n > 0:
        if (j + 1 < len(cs) and col_at(cs, j + 1)[2]
                and col_at(cs, j + 1)[0] == col_at(cs, j)[0] + 1):
            j += 1
            n -= 1
        else:
            return j
    return j


# TrioRules.lean:448  runsGo (fuel n)
def runs_go(cs, n, i):
    out = []
    while n > 0:
        if i >= len(cs):
            break
        if col_at(cs, i)[2]:
            out.append(i)
            i = run_end(cs, len(cs), i) + 1
        else:
            i += 1
        n -= 1
    return out


# TrioRules.lean:486  isPsiLevel: [(a@(.psi v X), 1)] with v ≠ [] and lvl a = some u, u ≠ v
def is_psi_level(alpha):
    if len(alpha) == 1 and alpha[0][1] == 1 and alpha[0][0][0] == 'psi':
        a = alpha[0][0]
        v, x = a[1], a[2]
        if v == ():
            return None
        u = lvl(a)
        if u is None:
            return None
        return (u, x) if cmp_ord(u, v) != 0 else None
    return None


# ---------------------------------------------------------------- the state

class Ctx:
    """TrioRules.lean:498  structure Ctx (the defaults are Lean's)."""
    __slots__ = ('cols', 'st', 'regime', 'prev', 'storeys', 'level', 'tail_sub',
                 'leaf_level', 'fresh')

    def __init__(self, cols, regime):
        self.cols = cols
        self.st = 0
        self.regime = regime
        self.prev = None
        self.storeys = 0
        self.level = 0
        self.tail_sub = None
        self.leaf_level = None
        self.fresh = False


# TrioRules.lean:510  laySt y: lay a lifted copy of the last storey
def lay_st(c, y):
    seg = storey_of(c.cols[c.st:len(c.cols)], last_c(c.cols)[1] if y is None else y)
    c.st = len(c.cols)
    c.cols = c.cols + seg
    c.prev = None
    c.storeys += 1
    c.fresh = True


# TrioRules.lean:516  copyLoop (fuel n)
def copy_loop(c, n, src, ax):
    while True:
        if n == 0:
            return 0
        dx = ax - col_at(src, 0)[0]
        seg = set_last_y(tuple((x + dx, y + 1, z) for x, y, z in src), last_c(src)[1])
        c.st = len(c.cols)
        c.cols = c.cols + seg
        c.storeys += 1
        c.prev = None
        zs = z_idx(seg)
        if len(zs) <= 3:
            k = len(zs) - 1
            is_one = k == 1
            c.leaf_level = last_c(seg)[1] + (0 if is_one else 1)
            if not is_one and len(zs) >= 2:
                c.tail_sub = seg[zs[len(zs) - 2] + 1:len(seg)]
            return k
        src = seg[0:zs[len(zs) - 2] + 1]
        ax = last_root_plain(c.cols)[1] + 1
        n -= 1


# TrioRules.lean:538  copyStorey ax
def copy_storey(c, ax):
    cs = c.cols
    i0 = last_storey(cs)
    z0 = [j for j in range(len(cs)) if j >= i0 and not col_at(cs, j)[2]]
    return copy_loop(c, FUEL, cs[i0:(z0[-1] if z0 else 0) + 1], ax)


# ---------------------------------------------------------------- given Mf

# TrioRules.lean:553  leafY v = (lastC (Mf v)).y
def leaf_y(mf, v):
    return last_c(mf(v))[1]


# TrioRules.lean:557  suffixOf: the columns after the last z0 column of M(v)
def suffix_of(mf, v):
    cs = mf(v)
    for j in range(len(cs) - 1, -1, -1):
        if not col_at(cs, j)[2]:
            return cs[j + 1:len(cs)]
    return ()


# TrioRules.lean:567  writeLevel (rules 3, 4, 10)
def write_level(mf, v, x, d, arg, ladders):
    base = mf(v)
    if not arg:
        return ((x, last_c(base)[1], False),)
    par = forest(base)
    li = (0, 0)
    for lad in [mf(nat(max(d, 0)))] + list(ladders):      # Mf (nat d.toNat) :: ladders
        for i in range(common_prefix(lad, base)):
            if (i >= 1 and is_level(base, par, i) and col_at(base, i)[1] <= d
                    and i > li[1]):
                li = (col_at(base, i)[1], i)
    tail = base[li[1] + 1:len(base)]
    if not tail:
        return ((x, last_c(base)[1], False),)
    bump = d - li[0]
    dx = x - col_at(tail, 0)[0]
    return tuple((cx + dx, cy + (bump if relative(base, par, li[1] + 1 + i) else 0), cz)
                 for i, (cx, cy, cz) in enumerate(tail))


# TrioRules.lean:585  spent
def spent(mf, c):
    u, v = c.prev, c.regime
    if u is None or v is None:
        return False
    return (cmp_ord(u, v) != 0 and len(suffix_of(mf, v)) != 0
            and leaf_y(mf, u) == leaf_y(mf, v))


# TrioRules.lean:593  appendSuffix (rule 5)
def append_suffix(mf, cols, v, storeys, tail_sub):
    if last_c(cols)[2]:
        return cols
    suf = suffix_of(mf, v)
    if not suf:
        if tail_sub is not None:
            return cols + tail_sub if (tail_sub and lvl_o(v) is not None) else cols
        return cols
    n = len(suf)
    x0 = col_at(suf, 0)[0]
    dx = [c[0] - x0 for c in suf]
    runs = runs_go(cols, len(cols), 0)
    lift0 = max(last_c(cols)[1] - leaf_y(mf, v), 0)
    ks = [lift0] + [j for j in range(storeys, -1, -1) if j != lift0]
    for k in ks:
        pat = [(c[1] + k, c[2]) for c in suf]
        for i in reversed(runs):
            seg = cols[i:i + n]
            if (len(seg) == n and [(c[1], c[2]) for c in seg] == pat
                    and [c[0] - col_at(seg, 0)[0] for c in seg] == dx):
                return cols + seg
    return cols + suf


# TrioRules.lean:739  kidsOf par n i = (List.range n).filter (par.getD c none == some i)
def kids_of(par, n, i):
    return [c for c in range(n) if _get(par, c) == i]


# TrioRules.lean:812  toRows: [x.toNat, y.toNat, if z then 1 else 0]
def to_rows(cs):
    return tuple((max(x, 0), max(y, 0), 1 if z else 0) for x, y, z in cs)


# ================================================================ TrioRules2.lean

# TrioRules2.lean:59  omArg: [(.W w, 1)] => some w
def om_arg(v):
    if len(v) == 1 and v[0][1] == 1 and v[0][0][0] == 'W':
        return v[0][0][1]
    return None


# TrioRules2.lean:65  findSub cs L y2: the last sub-unit (a,L,1)(a+1,L,1)(a+2,y2,0)
def find_sub(cs, L, y2):
    for i in range(len(cs) - 1, -1, -1):
        x, y, z = col_at(cs, i)
        if (i + 2 < len(cs) and z and y == L and col_at(cs, i + 1) == (x + 1, L, True)
                and col_at(cs, i + 2) == (x + 2, y2, False)):
            return cs[i:i + 3]
    return None


# TrioRules2.lean:74  omegaDfs2 (fuel n)
def omega_dfs2(cs, par, kids, drop, plain, n, i, d):
    if n == 0:
        return []
    if drop is not None and drop == i:
        return []
    x, y, z = col_at(cs, i)
    if (is_level(cs, par, i) and plain != i) or i == 0:
        ins = [(d + 1, y + 1, True), (d + 2, y + 1, True), (d + 3, y + 1, False)]
    else:
        ins = []
    out = [(d, y, z)] + ins
    for k in kids[i]:
        out += omega_dfs2(cs, par, kids, drop, plain, n - 1, k, d + 1)
    return out


# TrioRules2.lean:92  MOmega2 (Fix A)
def m_omega2(mf, v):
    cs = mf(v)
    if not cs:
        return ()
    par = forest(cs)
    last = len(cs) - 1
    last_lev = is_level(cs, par, last)
    p = _get(par, last)
    par_lev = (is_level(cs, par, p) or p == 0) if p is not None else False
    drop = last if (last_lev and par_lev) else None
    plain = last if (last_lev and not par_lev) else None
    kids = [kids_of(par, len(cs), i) for i in range(len(cs))]
    return tuple(omega_dfs2(cs, par, kids, drop, plain, len(cs) + 1, 0, 0))


# TrioRules2.lean:106  MpsiLevel2 (rule 9 on the corrected base)
def m_psi_level2(mf, u, x_):
    base = m_omega2(mf, u)
    y0 = last_c(base)[1]
    cols = set_last_y(base, y0 - 1)
    x = last_c(base)[0] + 1
    w = lvl_o(x_)
    if w is None:
        return ()
    if cmp_ord(w, u) == 0:
        return cols + ((x, y0, False),)
    return append_suffix(mf, cols + write_level(mf, w, x, y0 - 1, True, [mf(u), cols]),
                         w, 0, None)


# TrioRules2.lean:132  leafNameF.rest (Fix B 1-2: the old branches)
def leaf_name_rest(mf, c, v, r, unc):
    if c.storeys != 0 and cmp_ord(v, r) == 0:
        if not unc:
            return c.level
        return 0 if c.leaf_level is None else c.leaf_level
    if unc and leaf_y(mf, v) == leaf_y(mf, r) and cmp_ord(v, ONE) != 0:
        u = om_arg(r)
        if not (u is not None and cmp_ord(u, v) == 0):
            return leaf_y(mf, v) + 1
    return None


# ================================================================ TrioRules3.lean

OMEGA = wpow(ONE)                                       # TrioRules3.lean:56  omega
OMEGA_ONE_PLUS_ONE = add(((('W', ONE), 1),), ONE)       # TrioRules3.lean:59  omegaOnePlusOne
OM_OM_TWO = ((('W', ((('W', nat(2)), 1),)), 1),)        # TrioRules3.lean:62  omOmTwo
HEAD_OMEGA_OMEGA = ((0, 0, False), (1, 1, True), (2, 1, True), (3, 1, False),
                    (1, 1, True))                       # TrioRules3.lean:65  headOmegaOmega


# TrioRules3.lean:69  levelOmega: Omega_w <= w < Omega_(w+1)
def level_omega(w):
    return (cmp_ord(w, ((('W', OMEGA), 1),)) != -1
            and cmp_ord(w, ((('W', add(OMEGA, ONE)), 1),)) == -1)


# TrioRules3.lean:77  MpsiLevel3 (Fix E)
def m_psi_level3(mf, u, x_):
    if cmp_ord(u, OMEGA_ONE_PLUS_ONE) != 0:
        return m_psi_level2(mf, u, x_)
    w = lvl_o(x_)
    if w is None:
        return m_psi_level2(mf, u, x_)
    if not level_omega(w):
        return m_psi_level2(mf, u, x_)
    m = mf(w)
    if m[0:5] != HEAD_OMEGA_OMEGA:
        return m_psi_level2(mf, u, x_)
    return m_psi_level2(mf, u, OM_OM_TWO) + tuple((x + 1, y + 1, z) for x, y, z in m[4:])


# ================================================================ TrioRulesNonLast.lean

# TrioRulesNonLast.lean:69  ancestors (fuel n)
def ancestors(par, n, i):
    out = []
    while n > 0:
        p = _get(par, i)
        if p is None:
            break
        out.append(p)
        i = p
        n -= 1
    return out


# TrioRulesNonLast.lean:77  par1: the row-1 parent of each column
def par1(cs):
    par = forest(cs)
    out = []
    for i in range(len(cs)):
        yi = col_at(cs, i)[1]
        q = None
        for j in ancestors(par, len(cs), i):
            if col_at(cs, j)[1] < yi:
                q = j
                break
        out.append(q)
    return tuple(out)


# TrioRulesNonLast.lean:83  reaches (fuel n)
def reaches(p1, s0, n, j):
    while True:
        if n == 0:
            return False
        if j == s0:
            return True
        if j < s0:
            return False
        k = _get(p1, j)
        if k is None:
            return False
        j = k
        n -= 1


# TrioRulesNonLast.lean:94  blift (Fix N 2)
def blift(cs, s0):
    p1 = par1(cs)
    seg = tuple((x + 1, y + (1 if reaches(p1, s0, len(cs) + 1, i) else 0), z)
                for i, (x, y, z) in enumerate(cs) if i >= s0)
    return set_last_y(seg, last_c(seg)[1] - 1)


# TrioRulesNonLast.lean:102  findSubIn cs a b y2
def find_sub_in(cs, a, b, y2):
    for i in range(len(cs) - 1, -1, -1):
        x, y, z = col_at(cs, i)
        if (a <= i and i + 3 <= b and z and col_at(cs, i + 1) == (x + 1, y, True)
                and col_at(cs, i + 2) == (x + 2, y2, False)):
            return cs[i:i + 3]
    return None


# TrioRulesNonLast.lean:110  omChain (fuel n)
def om_chain(n, v):
    out = []
    while n > 0:
        out.append(v)
        w = om_arg(v)
        if w is None:
            break
        v = w
        n -= 1
    return out


# TrioRulesNonLast.lean:117  chainBase v = (omChain fuel v).getLast?.getD v
def chain_base(v):
    ch = om_chain(FUEL, v)
    return ch[-1] if ch else v


class NState:
    """TrioRulesNonLast.lean:122  structure NState."""
    __slots__ = ('cap', 'fst', 'fend', 'fcount', 'fs0', 'capy')

    def __init__(self):
        self.cap = None
        self.fst = None
        self.fend = 0
        self.fcount = 0
        self.fs0 = None
        self.capy = None


class CtxN:
    """TrioRulesNonLast.lean:131  structure CtxN (`liftC`, :136, is `s.c`)."""
    __slots__ = ('c', 'n')

    def __init__(self, c):
        self.c = c
        self.n = NState()


# TrioRulesNonLast.lean:145  leafNameNF (fuel n)
def leaf_name_nf(mf, n, s, v):
    if n == 0:
        return None
    regime = s.c.regime

    def base():
        if regime is None:
            return None
        r = regime
        unc = lvl_o(r) is not None
        w = om_arg(v)
        if w is not None:
            if unc:
                t = leaf_name_nf(mf, n - 1, s, w)
                return (leaf_y(mf, w) if t is None else t) + 1
            return leaf_name_rest(mf, s.c, v, r, unc)
        return leaf_name_rest(mf, s.c, v, r, unc)

    is_r = regime is not None and lvl_o(regime) is not None and cmp_ord(v, regime) == 0
    is_cap = s.n.cap is not None and cmp_ord(v, s.n.cap) == 0
    if is_r and s.n.cap is not None:
        b = base()
        return None if b is None else b + s.n.fcount
    if s.n.capy is not None:
        return s.n.capy if is_cap else base()
    return base()


# TrioRulesNonLast.lean:170  leafNameN s v = leafNameNF Mf fuel s v
def leaf_name_n(mf, s, v):
    return leaf_name_nf(mf, FUEL, s, v)


# TrioRulesNonLast.lean:173  leafNameOrYN
def leaf_name_or_yn(mf, s, v):
    t = leaf_name_n(mf, s, v)
    return leaf_y(mf, v) if t is None else t


# TrioRulesNonLast.lean:178  upgradeNF (fuel n): Fix B 3 with Fix N 3
def upgrade_nf(mf, n, s, cs, t, used):
    while True:
        if n == 0:
            return (cs, t, used)
        r = s.c.regime
        w = om_arg(t)
        if r is None or w is None:
            return (cs, t, used)
        if not (lvl_o(r) is not None and not last_c(cs)[2]):
            return (cs, t, used)
        y2 = leaf_name_or_yn(mf, s, w)
        in_copy = None
        if not used and s.n.fst is not None:
            in_copy = find_sub_in(cs, s.n.fst, s.n.fend, y2)
        sub = in_copy if in_copy is not None else find_sub(cs, last_c(cs)[1], y2)
        if sub is None:
            return (cs, t, used)
        cs, t, used, n = cs + sub, w, True, n - 1


# TrioRulesNonLast.lean:198  suffixIn
def suffix_in(mf, cs, v, a, b):
    if last_c(cs)[2]:
        return None
    suf = suffix_of(mf, v)
    n = len(suf)
    k = max(last_c(cs)[1] - leaf_y(mf, v), 0) + 1
    pat = [(c[1] + k, c[2]) for c in suf]
    x0 = col_at(suf, 0)[0]
    dx = [c[0] - x0 for c in suf]
    for i in range(len(cs) - 1, -1, -1):
        if not (a <= i and i + n <= b):
            continue
        seg = cs[i:i + n]
        if not ([(c[1], c[2]) for c in seg] == pat
                and [c[0] - col_at(seg, 0)[0] for c in seg] == dx):
            continue
        if (i == 0 or not col_at(cs, i - 1)[2]
                or col_at(cs, i - 1)[0] != col_at(cs, i)[0] - 1):
            return cs[i:i + n]
    return None


# TrioRulesNonLast.lean:215  fixNNeeded
def fix_n_needed(mf, s):
    r, p = s.c.regime, s.c.prev
    if r is None or p is None:
        return False
    return (lvl_o(r) is not None and om_arg(r) is not None
            and cmp_ord(chain_base(r), ONE) == 0
            and not last_c(s.c.cols)[2] and not suffix_of(mf, chain_base(p))
            and not any(cmp_ord(p, t) == 0 for t in om_chain(FUEL, r))
            and not (s.n.cap is not None and cmp_ord(p, s.n.cap) == 0))


# TrioRulesNonLast.lean:226  fixN: the upgrade, then the lifted copy; returns `used`
def fix_n(mf, s):
    prev = s.c.prev
    p = () if prev is None else prev
    cols, _t, used = upgrade_nf(mf, FUEL, s, s.c.cols, p, False)
    q = _get(par1(cols), max(len(cols) - 1, 0))
    s0a = 0 if q is None else q
    if s.n.fst is not None and s.n.fs0 is not None:
        s0 = s.n.fst if s.n.fs0 == s0a else s0a
    else:
        s0 = s0a
    seg = blift(cols, s0)
    cols2 = cols + seg
    # set { c := { s.c with cols := cols', st := cols.size, prev := none },
    #       n := { s.n with cap := s.c.prev, fs0 := some s0, fst := some cols.size,
    #              fend := cols'.size, fcount := s.n.fcount + 1,
    #              capy := if used then none else some (lastC cols').y } }
    s.c.cols = cols2
    s.c.st = len(cols)
    s.c.prev = None
    s.n.cap = prev
    s.n.fs0 = s0
    s.n.fst = len(cols)
    s.n.fend = len(cols2)
    s.n.fcount = s.n.fcount + 1
    s.n.capy = None if used else last_c(cols2)[1]
    return used


# ================================================================ TrioFixStrip.lean

# TrioFixStrip.lean:81  chainAtomF (fuel n)
#   | 0, _ => none | _+1, .o [] => none | n+1, .o ((e, _) :: _) => chainAtomF n e
#   | _+1, .W v => some (.W v) | _+1, .psi v X => some (.psi v X)
def chain_atom_f(n, x):
    while True:
        if n == 0:
            return None
        if x[0] == 'o':
            if x[1] == ():
                return None
            n -= 1
            x = x[1][0][0]
            continue
        return x


# TrioFixStrip.lean:89  chainAtom x = chainAtomF fuel x
def chain_atom(x):
    return chain_atom_f(FUEL, x)


# TrioFixStrip.lean:92  chainArg: some X when the chain ends in .psi _ X
def chain_arg(x):
    a = chain_atom(x)
    if a is not None and a[0] == 'psi':
        return a[2]
    return None


# TrioFixStrip.lean:101  stripSt (rule 1, corrected)
def strip_st(delta):
    a = ato(delta)
    if not a:
        return ()
    (h, c), dt = a[0], a[1:]
    rest = (((h, c - 1),) if c > 1 else ()) + dt
    if h[0] == 'psi':
        return add(h[2], rest)
    if h[0] == 'W':
        return rest
    x = chain_arg(h)
    if x is not None:
        return add(x, ((h, c),) + dt)
    return ((h, c),) + dt


# TrioFixStrip.lean:116  uncollapses
def uncollapses(e):
    a = ato(e)
    if a:
        return chain_arg(a[0][0]) is not None
    return False


# TrioFixStrip.lean:162  tailBlockFSt (fuel n)
def tail_block_f_st(n, gamma, arg):
    while True:
        if n == 0:
            return None
        if not gamma:
            return None
        e = gamma[-1][0]
        rest = strip_st(e)
        if rest:
            n, gamma, arg = n - 1, rest, uncollapses(e)
            continue
        return None if arg else lvl(e)


# TrioFixStrip.lean:173  tailBlockSt gamma arg = tailBlockFSt fuel gamma arg
def tail_block_st(gamma, arg):
    return tail_block_f_st(FUEL, gamma, arg)


# TrioFixStrip.lean:176  unitTailLevelSt
def unit_tail_level_st(beta):
    bp = pred_beta(beta)
    if not beta or not bp:
        return None
    e = bp[-1][0]
    return tail_block_st(ato(e), False)


# TrioFixStrip.lean:184  tailLevelSt
def tail_level_st(alpha):
    us = units(alpha)
    if not us:
        return None
    return unit_tail_level_st(ato(us[-1]))


# TrioFixStrip.lean:193  blockNSt (fuel n): the OT embedding (rules 1, 3, 4, 6)
def block_n_st(mf, n, gamma, x0, d0, arg, plvl, py, s):
    if n == 0:
        return
    x, d = x0, d0
    for e, cnt in gamma:
        sub_arg = uncollapses(e)
        for _ in range(cnt):
            if not s.c.fresh and spent(mf, s.c):
                lay_st(s.c, None)
                lx, ly, _z = last_c(s.c.cols)
                x, d = lx, ly
            v = lvl(e)
            if v is None:
                run = ((x, 0, False),)
            elif not arg and plvl is not None and cmp_ord(v, plvl) == 0:
                run = ((x, py, False),)
            elif not arg:
                y = leaf_name_n(mf, s, v)
                if y is not None:
                    run = ((x, y, False),)
                else:
                    run = write_level(mf, v, x, d, arg, [s.c.cols])
            else:
                run = write_level(mf, v, x, d, arg, [s.c.cols])
            s.c.cols = s.c.cols + run
            sub = strip_st(e)
            rx, ry, _z = last_c(run)
            nx, nd = rx + 1, ry
            s.c.prev = None if arg else v
            if sub and not s.c.fresh and spent(mf, s.c):
                lay_st(s.c, None)
                lx, ly, _z = last_c(s.c.cols)
                nx, nd = lx + 1, ly
            block_n_st(mf, n - 1, sub, nx, nd, sub_arg, v, ry, s)
            s.c.prev = tail_block_st(ato(e), arg)


# TrioFixStrip.lean:234  restateSt (Fix N 4): returns (level, root x)
def restate_st(mf, s, digits):
    ly, lx = last_root_plain(s.c.cols)
    y = ly + 1
    x0 = lx + 2
    s.c.cols = s.c.cols + ((lx + 1, ly, False), (x0, y, True))
    s.c.level = y - 1
    for e in digits:
        s.c.cols = s.c.cols + ((x0 + 1, y, True),)
        block_n_st(mf, FUEL, ato(e), x0 + 2, y - 1, False, None, 0, s)
    return (y, x0)


# TrioFixStrip.lean:247  placeUnitsNSt (rules 2, 6-8; Fixes C, D, N)
def place_units_n_st(mf, cols, alpha, level0, root_x0, regime):
    s = CtxN(Ctx(cols, regime))
    level, root_x, skip = level0, root_x0, 0
    if regime is not None and lvl_o(regime) is not None:
        k = copy_storey(s.c, root_x + 1)
        skip = 1 if k == 1 else 0
        level, root_x = last_root_plain(s.c.cols)
        # Fix C: the copy is the first unit's first digit; lay its other digits.
        if skip == 1:
            us = units(alpha)
            if us:
                b0 = us[0]
                alld = units(pred_beta(ato(b0)))
                rest = alld[1:]
                j = 0
                for e in rest:
                    if fix_n_needed(mf, s):
                        if fix_n(mf, s):
                            level, root_x = restate_st(mf, s, alld[:j + 1])
                        else:
                            level, root_x = last_root_plain(s.c.cols)
                    s.c.cols = s.c.cols + ((root_x + 1, level, True),)
                    block_n_st(mf, FUEL, ato(e), root_x + 2, level - 1, False, None, 0, s)
                    j += 1
                if rest:
                    s.c.prev = unit_tail_level_st(ato(b0))
    prev0 = False
    first = True
    for b in units(alpha)[skip:]:
        beta = ato(b)
        s.c.fresh = False
        laid = (not first) and spent(mf, s.c)
        if laid:
            lay_st(s.c, None)
            level, root_x = last_root_plain(s.c.cols)
            prev0 = False
        elif ((not first) or skip == 1) and fix_n_needed(mf, s):
            fix_n(mf, s)
            level, root_x = last_root_plain(s.c.cols)
            prev0 = False
        if not beta and prev0:
            tx, ty, _z = last_c(s.c.cols)
            s.c.cols = s.c.cols + ((tx + 1, ty + 1, False),)
        elif not beta:
            s.c.cols = s.c.cols + ((root_x + 1, level, False), (root_x + 2, level + 1, False))
            s.c.prev = None
        else:
            ax = root_x + 1
            x0 = ax + 1
            y = level + 1
            s.c.level = level
            s.c.cols = s.c.cols + ((ax, level, False), (x0, y, True))
            digits = units(pred_beta(beta))
            i = 0
            for e in digits:
                if i != 0 and not s.c.fresh and spent(mf, s.c):
                    lay_st(s.c, None)
                    y, x0 = last_root_plain(s.c.cols)
                    s.c.level = y - 1
                elif i != 0 and fix_n_needed(mf, s):
                    if fix_n(mf, s):
                        y, x0 = restate_st(mf, s, digits[:i])
                    else:
                        y, x0 = last_root_plain(s.c.cols)
                        s.c.level = y - 1
                s.c.cols = s.c.cols + ((x0 + 1, y, True),)
                block_n_st(mf, FUEL, ato(e), x0 + 2, y - 1, False, None, 0, s)
                # Fix D: a digit too deep for a countable regime, with digits after it.
                p = tail_block_st(ato(e), False)
                if p is not None and regime is not None:
                    r = regime
                    if (i + 1 < len(digits) and lvl_o(r) is None and cmp_ord(p, r) == -1
                            and leaf_y(mf, p) > leaf_y(mf, r)):
                        s.c.cols = set_last_y(s.c.cols, leaf_y(mf, r))
                        for k in range(1, max(leaf_y(mf, p) - leaf_y(mf, r), 0) + 1):
                            lay_st(s.c, leaf_y(mf, r) + k)
                        lay_st(s.c, None)
                        y, x0 = last_root_plain(s.c.cols)
                        s.c.level = y - 1
                i += 1
            root_x = x0
        level = level + 1
        prev0 = not beta
        if beta:
            s.c.prev = unit_tail_level_st(beta)
        p = s.c.prev
        if p is not None and regime is not None:
            r = regime
            if lvl_o(r) is None and not laid and cmp_ord(p, r) == -1:
                dy = leaf_y(mf, p) - leaf_y(mf, r)
                if dy > 0:
                    s.c.cols = set_last_y(s.c.cols, leaf_y(mf, r))
                    for k in range(1, dy + 1):
                        lay_st(s.c, leaf_y(mf, r) + k)
                    level, root_x = last_root_plain(s.c.cols)
                    prev0 = False
        first = False
    return s


# TrioFixStrip.lean:370  finishNSt
def finish_n_st(mf, alpha, s):
    t = tail_level_st(alpha)
    if t is None:
        return s.c.cols
    u_cols, u_t, _used = upgrade_nf(mf, FUEL, s, s.c.cols, t, False)
    in_copy = None
    if s.n.fst is not None:
        a = s.n.fst
        in_copy = None if not suffix_of(mf, u_t) else suffix_in(mf, u_cols, u_t, a, s.n.fend)
    if in_copy is not None:
        return u_cols + in_copy
    return append_suffix(mf, u_cols, u_t, s.c.storeys, None)


# TrioFixStrip.lean:385  MstepSt: one step of the builder
def mstep_st(mf, alpha):
    v = lvl_o(alpha)
    if v is None:
        return finish_n_st(mf, alpha, place_units_n_st(mf, (), alpha, 0, -1, None))
    ux = is_psi_level(alpha)
    if ux is not None:
        return m_psi_level3(mf, ux[0], ux[1])
    if alpha == ((('W', v), 1),):
        return m_omega2(mf, v)
    base = m_omega2(mf, v)
    ya = last_root(base)
    return finish_n_st(mf, alpha, place_units_n_st(mf, base, alpha, ya[0], ya[1] - 1, v))


_MCACHE = {}
_MF = {}


def _mf(n):
    """`MfuelSt n` as a function Od -> Cols (the `Mf` of the step at fuel n + 1)."""
    f = _MF.get(n)
    if f is None:
        def f(a, n=n):
            return mfuel_st(n, a)
        _MF[n] = f
    return f


# TrioFixStrip.lean:401  MfuelSt: | 0, _ => #[] | n+1, a => MstepSt (MfuelSt n) a
def mfuel_st(n, a):
    if n == 0:
        return ()
    key = (n, a)
    r = _MCACHE.get(key)
    if r is None:
        r = mstep_st(_mf(n - 1), a)
        _MCACHE[key] = r
    return r


def clear_cache():
    """Drop the memo tables (they only speed up repeated calls)."""
    _MCACHE.clear()
    _FOREST.clear()


# TrioFixStrip.lean:407  MSt alpha = MfuelSt fuel alpha
def m_st(alpha):
    return mfuel_st(FUEL, alpha)


# ================================================================ TrioFixOfTerm.lean

# TrioFixOfTerm.lean:114  finSub: [] or [(.o [], _)]
def fin_sub(cf):
    return cf == () or (len(cf) == 1 and cf[0][0] == O0)


# TrioFixOfTerm.lean:122  psiAtom
def psi_atom(cf, x):
    if fin_sub(cf):
        return ('psi', cf, x)
    return ('psi', ((('W', add(cf, ONE)), 1),), x)


# TrioFixOfTerm.lean:128  summandFix
def summand_fix(c0, cf, hi, lo):
    if not hi:
        base = () if c0 else ((('W', cf), 1),)
    else:
        base = ((psi_atom(cf, hi), 1),)
    if not lo:
        return base if base else ONE
    return wpow(add(base, lo))


# TrioFixOfTerm.lean:135  partsFix x a = (ofTermFix x, hi, lo)
#   | nil, _ => ([], [], [])
#   | cons c d u, a => let q := partsFix d c
#       let s := summandFix (c == nil) (partsFix c nil).1 q.2.1 q.2.2
#       let p := partsFix u a
#       (add s p.1, if Term.cmp c a == .gt then (add s p.2.1, p.2.2) else (p.2.1, add s p.2.2))
def parts_fix(x, a):
    if not x:
        return ((), (), ())
    (c, d), u = x[0], x[1:]
    q = parts_fix(d, c)
    s = summand_fix(c == (), parts_fix(c, ())[0], q[1], q[2])
    p = parts_fix(u, a)
    if exb_std.cmp(c, a) == 1:
        return (add(s, p[0]), add(s, p[1]), p[2])
    return (add(s, p[0]), p[1], add(s, p[2]))


# ================================================================ public

def _deep(fn, *args):
    """Run fn(*args) on a thread with a large stack: the fuel lets the recursion
    reach a depth that the default Python stack does not hold."""
    out = {}

    def run():
        try:
            out['v'] = fn(*args)
        except BaseException as e:      # pragma: no cover - re-raised below
            out['e'] = e

    old_limit = sys.getrecursionlimit()
    sys.setrecursionlimit(max(old_limit, 1000000))
    old_size = threading.stack_size()
    try:
        threading.stack_size(1 << 30)
        t = threading.Thread(target=run)
        t.start()
        t.join()
    finally:
        threading.stack_size(old_size)
    if 'e' in out:
        raise out['e']
    return out['v']


# TrioFixOfTerm.lean:144  ofTermFix x = (partsFix x nil).1
def of_term_fix(alpha):
    """The reading of an exb term into the rules' normal form (an Od)."""
    return _deep(lambda: parts_fix(alpha, ())[0])


# TrioFixStrip.lean:410  trioRuleMatrixSt alpha = toRows (MSt alpha)
def trio_rule_matrix_st(od):
    """The trio matrix of psi_0(Omega_od) by the rule program (an Od in, columns out)."""
    return _deep(lambda: to_rows(m_st(od)))


# TrioFixStrip.lean:413  trioRuleMatrixOfSt s = do let a ← parse s; if a.isEmpty then none else ...
def trio_rule_matrix_of_st(s):
    """The matrix of a sheet label; None when it does not parse or names 0."""
    from notation import ParseError
    from notation.label import parse
    try:
        a = parse(s)
    except ParseError:
        return None
    return None if not a else trio_rule_matrix_st(a)


# TrioFixStrip.lean:422  trioMatrixLSt α = trioRuleMatrixSt (ofTermFix α)
def trio_matrix_l_st(alpha):
    """The trio matrix of psi_0(Omega_alpha) for an exb term, by the rule program."""
    return _deep(lambda: to_rows(m_st(parts_fix(alpha, ())[0])))


__all__ = ['trio_matrix_l_st', 'trio_rule_matrix_st', 'trio_rule_matrix_of_st',
           'of_term_fix', 'FUEL']
