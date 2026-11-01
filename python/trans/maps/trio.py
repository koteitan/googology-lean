"""exb -> bms3: the trio matrix of psi_0(Omega_alpha).

A faithful port of three Lean maps, function by function. The paths are
relative to the repo root; `Trio/` is Googology/Trans/ExBuchholz/BMS/Trio/.

- `trio_e2`  = `TrioFixStripTree.trioE2`   (Trio/TrioFixStripTree.lean:113)
- `trio_e`   = `TrioTree.trioE`            (Trio/TrioTree.lean:126)
- `omega_index_matrix` = `omegaIndexMatrix` (Trio/Trio.lean:98)

The three differ only in the body of an add unit (`bodyE2`, `bodyE`, `bodyU`).
None of them has a fuel argument in Lean, so none has one here.

Proved domains (each map is order-preserving, injective and gives standard
forms there):

- trio_e2, trio_e: OT alpha, alpha < Omega, Sub01 alpha (every subscript is 0
  or 1). `trio_domain`. Theorems: trioE2_lt_iff, trioE2_injective, trioE2_std
  (TrioFixStripTree.lean); trioE_lt_iff, trioE_injective (TrioTree.lean),
  trioE_std (TrioTreeStd.lean).
- omega_index_matrix: OT alpha, alpha < e0 = psi_0(Omega) (`exbE0.State`,
  Googology/Trans/BMS/ExBuchholz/Equiv.lean:45). `omega_index_domain`.
  Theorems: omegaIndexMatrix_lt_iff, omegaIndexMatrix_injective
  (TrioMono.lean), omegaIndexMatrix_std (TrioStd.lean).

A term is as in notation/exb.py: a tuple of principal terms (a, b) = psi_a(b).
A matrix is a tuple of columns, each a 3-tuple (x, y, z) (notation/matrix.py);
Lean's result type is `List (List Nat)`.
"""

from .errors import DomainError
from notation.exb import BIG_OMEGA, ONE, ZERO, eps
from notation.exb_std import is_ot, lt

T1 = ONE            # Order.lean:143  t1 = psi nil nil
TW = BIG_OMEGA      # Order.lean:149  tW = psi t1 nil
TE0 = eps(0)        # Trans/BMS/ExBuchholz/Basic.lean:81  te0 = psi nil tW


def _cons(a, b, t):
    return ((a, b),) + t


# ---------------------------------------------------------------- domains

# Trio/TrioTree.lean:185  Sub01
#   Sub01 nil = True;  Sub01 (cons a b t) = (a = nil ∨ a = t1) ∧ Sub01 b ∧ Sub01 t
def sub01(x):
    return all((a == ZERO or a == T1) and sub01(b) for a, b in x)


# Googology/Trans/BMS/ExBuchholz/Basic.lean:103  AllNil
def all_nil(x):
    return all(a == ZERO and all_nil(b) for a, b in x)


def trio_domain(alpha):
    """OT alpha ∧ alpha < tW ∧ Sub01 alpha: the hypotheses of trioE2_lt_iff / trioE2_std."""
    return is_ot(alpha) and lt(alpha, TW) and sub01(alpha)


def omega_index_domain(alpha):
    """OT alpha ∧ alpha < te0 (exbE0.State): the hypotheses of omegaIndexMatrix_lt_iff / _std."""
    return is_ot(alpha) and lt(alpha, TE0)


# ---------------------------------------------------------------- Trio.lean

# Googology/Trans/BMS/ExBuchholz/Basic.lean:197  unread
#   unread b nil = [];  unread b (cons _ X Y) = b :: (unread (b+1) X ++ unread b Y)
def unread(b, t):
    out = []
    for _, x in t:
        out.append(b)
        out += unread(b + 1, x)
    return out


# Trio/Trio.lean:54  prSS x γ = (unread 0 γ).map (fun e => [x + e, 0, 0])
def pr_ss(x, g):
    return [(x + e, 0, 0) for e in unread(0, g)]


# Trio/Trio.lean:58  isFiniteT: every summand has argument nil
def is_finite_t(t):
    return all(b == ZERO for _, b in t)


# Trio/Trio.lean:63  dropLastT: the term with its last summand dropped
def drop_last_t(t):
    return t[:-1]


# Trio/Trio.lean:69  peelOne β = if isFiniteT β then dropLastT β else β
def peel_one(b):
    return drop_last_t(b) if is_finite_t(b) else b


# Trio/Trio.lean:73  mulUnits
#   mulUnits x0 y (cons _ g t) = ([x0+1, y, 1] :: prSS (x0+2) g) ++ mulUnits x0 y t
def mul_units(x0, y, t):
    out = []
    for _, g in t:
        out.append((x0 + 1, y, 1))
        out += pr_ss(x0 + 2, g)
    return out


# Trio/Trio.lean:78  bodyU β x0 y = [x0, y, 1] :: mulUnits x0 y (peelOne β)
def body_u(b, x0, y):
    return [(x0, y, 1)] + mul_units(x0, y, peel_one(b))


# Trio/Trio.lean:84 addUnits, Trio/TrioTree.lean:113 addUnitsE,
# Trio/TrioFixStripTree.lean:101 addUnitsE2: the same recursion with the body
# bodyU / bodyE / bodyE2.
#   addUnits rp1 lastX prevZero i (cons _ b t) =
#     if b == nil then
#       if prevZero then [lastX+1, i, 0] :: addUnits rp1 (lastX+1) true (i+1) t
#       else [rp1, i-1, 0] :: [rp1+1, i, 0] :: addUnits rp1 (rp1+1) true (i+1) t
#     else ([rp1, i-1, 0] :: body b (rp1+1) i) ++ addUnits (rp1+2) (rp1+1) false (i+1) t
def _add_units(body, rp1, last_x, prev_zero, i, t):
    out = []
    for _, b in t:
        im1 = max(i - 1, 0)                         # Nat subtraction
        if b == ZERO:
            if prev_zero:
                out.append((last_x + 1, i, 0))
                last_x = last_x + 1
            else:
                out.append((rp1, im1, 0))
                out.append((rp1 + 1, i, 0))
                last_x = rp1 + 1
            prev_zero = True
        else:
            out.append((rp1, im1, 0))
            out += body(b, rp1 + 1, i)
            rp1, last_x, prev_zero = rp1 + 2, rp1 + 1, False
        i += 1
    return out


def add_units(rp1, last_x, prev_zero, i, t):
    return _add_units(body_u, rp1, last_x, prev_zero, i, t)


# Trio/Trio.lean:98  omegaIndexMatrix α = addUnits 0 0 false 1 α
def omega_index_matrix(alpha):
    return tuple(add_units(0, 0, False, 1, alpha))


# ---------------------------------------------------------------- TrioTree.lean

# Trio/TrioTree.lean:84  subY nil = 0, subY (cons ..) = 1
def sub_y(a):
    return 0 if a == ZERO else 1


# Trio/TrioTree.lean:90  treeB
#   treeB x (cons a b t) = ([x, subY a, 0] :: treeB (x+1) b) ++ treeB x t
def tree_b(x, t):
    out = []
    for a, b in t:
        out.append((x, sub_y(a), 0))
        out += tree_b(x + 1, b)
    return out


# Trio/TrioTree.lean:95  mulUnitsE
#   mulUnitsE x0 y (cons _ g t) = ([x0+1, y, 1] :: treeB (x0+2) g) ++ mulUnitsE x0 y t
def mul_units_e(x0, y, t):
    out = []
    for _, g in t:
        out.append((x0 + 1, y, 1))
        out += tree_b(x0 + 2, g)
    return out


# Trio/TrioTree.lean:100  allNilB: every subscript is 0
def all_nil_b(t):
    return all(a == ZERO and all_nil_b(b) for a, b in t)


# Trio/TrioTree.lean:107  peelE b = if allNilB b then peelOne b else psi nil (psi nil b)
def peel_e(b):
    return peel_one(b) if all_nil_b(b) else _cons(ZERO, _cons(ZERO, b, ZERO), ZERO)


# Trio/TrioTree.lean:110  bodyE b x0 y = [x0, y, 1] :: mulUnitsE x0 y (peelE b)
def body_e(b, x0, y):
    return [(x0, y, 1)] + mul_units_e(x0, y, peel_e(b))


# Trio/TrioTree.lean:113  addUnitsE
def add_units_e(rp1, last_x, prev_zero, i, t):
    return _add_units(body_e, rp1, last_x, prev_zero, i, t)


# Trio/TrioTree.lean:126  trioE α = addUnitsE 0 0 false 1 α
def trio_e(alpha):
    return tuple(add_units_e(0, 0, False, 1, alpha))


# ---------------------------------------------------------------- TrioFixStripTree.lean

# Trio/TrioFixStripTree.lean:68  hiPart: the leading summands with a nonzero subscript
def hi_part(t):
    k = 0
    while k < len(t) and t[k][0] != ZERO:
        k += 1
    return t[:k]


# Trio/TrioFixStripTree.lean:73  loPart: the summands from the first one with subscript 0 on
def lo_part(t):
    return t[len(hi_part(t)):]


# Trio/TrioFixStripTree.lean:78  absorbs h nil = false; absorbs h (cons _ g _) = h < g
def absorbs(h, l):
    if not l:
        return False
    return lt(h, l[0][1])


# Trio/TrioFixStripTree.lean:84  expoT
#   expoT g = if allNilB g then g
#             else if absorbs (hiPart g) (loPart g) then loPart g
#             else cons nil (hiPart g) (loPart g)
def expo_t(g):
    if all_nil_b(g):
        return g
    h, l = hi_part(g), lo_part(g)
    if absorbs(h, l):
        return l
    return _cons(ZERO, h, l)


# Trio/TrioFixStripTree.lean:90  mapArgs (cons a g t) = cons a (expoT g) (mapArgs t)
def map_args(t):
    return tuple((a, expo_t(g)) for a, g in t)


# Trio/TrioFixStripTree.lean:95  peelE2 b = if allNilB b then peelOne b else mapArgs (expoT b)
def peel_e2(b):
    return peel_one(b) if all_nil_b(b) else map_args(expo_t(b))


# Trio/TrioFixStripTree.lean:98  bodyE2 b x0 y = [x0, y, 1] :: mulUnitsE x0 y (peelE2 b)
def body_e2(b, x0, y):
    return [(x0, y, 1)] + mul_units_e(x0, y, peel_e2(b))


# Trio/TrioFixStripTree.lean:101  addUnitsE2
def add_units_e2(rp1, last_x, prev_zero, i, t):
    return _add_units(body_e2, rp1, last_x, prev_zero, i, t)


# Trio/TrioFixStripTree.lean:113  trioE2 α = addUnitsE2 0 0 false 1 α
def trio_e2(alpha):
    """The trio matrix of psi_0(Omega_alpha). Proved standard and order-preserving
    on `trio_domain`; outside it the value is what the Lean function computes."""
    return tuple(add_units_e2(0, 0, False, 1, alpha))


# ---------------------------------------------------------------- edges

def exb_to_bms3(alpha):
    """trioE2 on its proved domain (OT, < Omega, subscripts 0/1); DomainError elsewhere."""
    if not is_ot(alpha):
        raise DomainError('trioE2: the term is not standard (isOT)')
    if not lt(alpha, TW):
        raise DomainError('trioE2: the term is not below W')
    if not sub01(alpha):
        raise DomainError('trioE2: a subscript is not 0 or 1 (the term is not below p0(W_2))')
    return trio_e2(alpha)


# ---------------------------------------------------------------- test terms

# Trio/TrioTree.lean:620  genTab, :629  smallFrag
def gen_tab(n):
    """genTab n: tab[k] = the terms with k psi's outside the subscripts, subscripts 0/1."""
    tab = [[ZERO]]
    for m in range(n):
        row = []
        for k in range(m + 1):
            for b in tab[k]:
                for t in tab[m - k]:
                    row += [_cons(ZERO, b, t), _cons(T1, b, t)]
        tab.append(row)
    return tab


def small_frag(n):
    """smallFrag n: the standard countable terms of genTab up to n psi's, in Lean's order."""
    tab = gen_tab(n)
    return [a for k in range(n + 1) for a in tab[k] if is_ot(a) and lt(a, TW)]


__all__ = ['exb_to_bms3', 'trio_e2', 'trio_e', 'omega_index_matrix', 'trio_domain',
           'omega_index_domain', 'sub01', 'small_frag']
