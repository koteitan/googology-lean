import Googology.Trans.BMS.TrioRulesAll

/-!
# Fix U: rule 9 for an uncountable `u` of finite level

A patch on top of `TrioRulesAll.lean` (rules 1–10 of
[koteitan/trio](https://github.com/koteitan/trio) with Fixes A–E and N).  It changes
**only rule 9** (`α = ψ_{Ω_u}(X)`, the function `MpsiLevel3` inside `MstepAll`), and only
when `u` is an uncountable successor of finite level `L`: `Ω_L ≤ u < Ω_{L+1}`, `L ≥ 1`,
`u = s + 1` (for example `Ω+1`, `Ω+2`, `Ω·2+1`, `Ω_2+1`, `Ω_3+1`).  Every other step of
the builder is `MstepAll` unchanged (`MstepU_notPsi`).  The explanation and the numbers
are in [TRIO-FIX-U.md](TRIO-FIX-U.md); the checks are in `TrioFixUSheet.lean`.

**Notation.**  `w` is the level of the argument `X` (`lvlO X`; `X = Ω_w` in the labels).
`M(v)` is the builder one step down (`Mf v`).  `base = low M(Ω_u)` is `M(Ω_u)` with its
leaf lowered by one: every `M(ψ_{Ω_u}(X))` starts with it.  `low(m)` lowers the row-1
entry of the last column by one.  `P = M(ψ_{Ω_u}(Ω_{Ω_{L+1}}))` as `MpsiLevel3` gives it
(for `u = Ω+1` this is sheet row 4467).  `mark = (L+1, L+1, 1)`.  `R_n = (P ++ mark)[n]`
(BM4 expansion, `expandRL 3 n`, proved BM4 in `EntriesR.lean`); `P ++ mark` is the argument
`Ω_{Ω_ω}` and `R_n` the argument `Ω_{Ω_{L+1+n}}`.  `L^L(m[4:])` adds `L` to `x` and `y` of
every column of `m` from index 4 on; `L'^L(m[4:])` adds `L` to `x`, and `L` to `y` only on
the columns whose row-1 ancestry reaches column 0.

**The change.**  `MpsiLevelU` returns, by the range of `w` (checks in this order):

| case | `M(ψ_{Ω_u}(Ω_w))` |
|---|---|
| `u` countable, a limit, or of infinite level | `MpsiLevel3` (unchanged) |
| `w` is `ψ`-headed and `M(w) = low M(Ω_t) ++ tail`, with `t = L+1` or `Ω+1 < t ≤ u` | `reroot (low M(Ω_t)) (low A_u(t)) M(w)` (**collapse**) |
| `w ≤ Ω_{L+1}` | `MpsiLevel3` |
| `w = Ω_m`, `L+1 < m < ω` | `R_{m-L-1}` |
| `Ω_m < w < Ω_{m+1}`, `L+1 ≤ m < ω` | `reroot (low M(Ω_{m+1})) (low R_{m-L}) M(w)` |
| `Ω_ω ≤ w < Ω_{ω+1}` | `P ++ L^L(M(w)[4:])` |
| `Ω_{ω+1} ≤ w < Ω_Ω` | `P ++ L'^L(M(w)[4:])` |
| `w = Ω_Ω` | `P ++ (L+1,L+1,1)(L+2,L+1,1)(L+3,1,0)` |
| `L = 1`, `Ω_Ω < w < Ω_{Ω+1}` | `reroot (low M(Ω_{Ω+1})) P M(w)` |
| otherwise | `MpsiLevel3` |

Here `A_u(t) = M(ψ_{Ω_u}(Ω_{Ω_t}))` by the same table (not a collapse, so no loop), and
`A_u(u) = base ++ (a+1,y0,1)(a+2,y0,1)(a+3,y0,0)` (the formal leaf of `Ω_u`, `a`, `y0` the
`x` of the last column of `base` and its unlowered `y`).  `reroot src img m` (`m` starts
with `src`) is `img` followed by the columns of `m` after `src`: a column whose nearest
row-0 ancestor inside `src` is one of the last three columns of `src`, say `src[-j]`,
is moved by `dx = x(img[-1]) - x(src[-1])` and, when it is a relative column (`z = 1` or a
level column, rule 3), by `dy = y(img[-j]) - y(src[-j])` in row 1; every other column is
copied as it is.  When a guard fails (`M(w)` does not start with the expected prefix, or
not with `B ++ (1,1,1)` for the lifts), the result is `MpsiLevel3`'s.

For `L = 1` the rows `w < Ω_{Ω+1}` of this table are the first version of Fix U (the
patch left by the rate-limited agent), with two changes: the collapse row now also acts
for `t = 2` (`ψ_1`/`ψ_{Ω_2}`-headed `w < Ω_2`, which the old rule 9 writes non-standard),
and for `Ω+1 < t ≤ u` (nested `ψ_{Ω_{Ω+2}}`, … arguments); and a limit `u` is left
alone.  For `L ≥ 2` the table is the same table with `2` shifted to `L+1` (`P`, `mark`,
the lifts by `L`).

**What is claimed.**  `inDomain u w` is the part of the table that the checks support:
`u = Ω+k` (finite `k`) for every `w`; any other `u` of level 1 for `w < Ω_{Ω+1}`;
`u` of finite level `L ≥ 2` for `w ≤ Ω_Ω` and for nested `ψ_{Ω_u}` arguments whose level
is again in the domain.  On all probe labels in the domain the matrices are standard
(yaBMS `bms -s`, outside Lean) and in the order of the labels (`#guard`s in
`TrioFixUSheet.lean`).  Outside the domain the output is not claimed: see "Still open"
in TRIO-FIX-U.md.
-/

namespace Googology.Trans.BMS.TrioFixU

open Googology.Trans.BMS.TrioRules
open Googology.Trans.BMS.TrioRules2
open Googology.Trans.BMS.TrioRules3
open Googology.Trans.BMS.TrioRulesNL
open Googology.Trans.BMS.TrioRulesAll
open Googology.Trans.BMS (expandRL)

/-! ### Columns -/

/-- Three-row lists back to columns (`z = 1` exactly when the entry is `1`). -/
def ofRows (l : List (List Nat)) : Cols :=
  (l.map fun c => (⟨(c.getD 0 0 : Int), (c.getD 1 0 : Int), c.getD 2 0 == 1⟩ : TrioRules.Col)).toArray

/-- `low(m)`: the row-1 entry of the last column lowered by one. -/
def lowerLast (cs : Cols) : Cols := setLastY cs ((lastC cs).y - 1)

/-- BM4 expansion `m[n]` on columns (`expandRL 3 n`, proved BM4 in `EntriesR.lean`). -/
def expandC (n : Nat) (cs : Cols) : Cols := ofRows (expandRL 3 n (toRows cs))

/-- `L^k(m[4:])`: every column from index 4 on, `x+k`, `y+k`. -/
def liftLk (k : Nat) (m : Cols) : Cols :=
  (m.extract 4 m.size).map fun c => { c with x := c.x + k, y := c.y + k }

/-- `L'^k(m[4:])`: from index 4 on, `x+k`, and `y+k` exactly when the row-1 ancestry of
the column reaches column 0 (`ψ_0` nodes `(x,0,0)` stay at `y = 0`). -/
def liftBk (k : Nat) (m : Cols) : Cols :=
  let p1 := par1 m
  ((List.range m.size).filter (· ≥ 4)).toArray.map fun i =>
    let c := colAt m i
    { c with x := c.x + k, y := c.y + (if reaches p1 0 (m.size + 1) i then (k : Int) else 0) }

/-- The nearest row-0 ancestor of `i` (or `i` itself) with index below `n`. -/
def ancBelow (par : Array (Option Nat)) (n : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, i =>
    if i < n then i else
    match par.getD i none with
    | some p => ancBelow par n k p
    | none => 0

/-- The columns of `m` after its prefix `src`, re-hung for `reroot`. -/
def rerootTail (src img m : Cols) : Cols :=
  let n := src.size
  let k := img.size
  let par := forest m
  let dx := (lastC img).x - (lastC src).x
  ((List.range m.size).filter (· ≥ n)).toArray.map fun i =>
    let c := colAt m i
    let j := ancBelow par n (m.size + 1) i
    if j + 3 ≥ n then
      let dy := (colAt img (k + j - n)).y - (colAt src j).y
      { c with x := c.x + dx, y := c.y + (if relative m par i then dy else 0) }
    else c

/-- **`reroot src img m`**: `img`, then the columns of `m` after its prefix `src`; those
hanging (row 0) from the last sub-unit of `src` move with it to the last sub-unit of
`img` (`x + dx`, and on relative columns `y + dy`, `dy` the row-1 offset between the
two sub-unit columns they hang from); the others are copied. -/
def reroot (src img m : Cols) : Cols := img ++ rerootTail src img m

/-- `p` is a proper prefix of `m`. -/
def properPrefix (p m : Cols) : Bool := decide (m.size > p.size) && m.extract 0 p.size == p

/-- The formal leaf of `Ω_u` after `base`: `base ++ (a+1,y0,1)(a+2,y0,1)(a+3,y0,0)`,
with `a` the `x` of the last column of `base` and `y0` one more than its `y`. -/
def formalTop (base : Cols) : Cols :=
  let a := (lastC base).x
  let y0 := (lastC base).y + 1
  base ++ #[⟨a + 1, y0, true⟩, ⟨a + 2, y0, true⟩, ⟨a + 3, y0, false⟩]

/-! ### Ordinals -/

/-- `Ω_v`. -/
def omS (v : Od) : Od := [(.W v, 1)]

/-- `Ω`. -/
def bigOmega : Od := omS one

/-- `Ω_m`. -/
def omN (m : Nat) : Od := omS (nat m)

/-- `Ω_Ω`. -/
def omOm : Od := omS bigOmega

/-- `Ω_{Ω+1}`. -/
def omOmSucc : Od := omS omegaOnePlusOne

/-- `Ω + ω`. -/
def omegaPlusOmega : Od := add bigOmega omega

/-- `a < b`. -/
def lt (a b : Od) : Bool := cmpOrd a b == .lt

/-- `u` is a successor `s + 1`. -/
def isSucc (u : Od) : Bool :=
  match u.getLast? with
  | some (.o [], _) => true
  | _ => false

/-- The finite level `L` of `u` (`Ω_L ≤ u < Ω_{L+1}`), if it is finite. -/
def finLvl (u : Od) : Option Nat :=
  match lvlO u with
  | some [(.o [], k)] => some k
  | _ => none

/-- The finite `m` with `Ω_m ≤ w < Ω_{m+1}`, if any. -/
def finIdx (w : Od) : Option Nat :=
  match lvlO w with
  | some [(.o [], k)] => if lt w (omN k) then (if k ≥ 1 then some (k - 1) else none) else some k
  | _ => none

/-- `B ++ (1,1,1)`, the head of `M(w)` for `w ≥ Ω_ω`. -/
def headOK (m : Cols) : Bool := m.extract 0 5 == headOmegaOmega

/-- The head term of `w` is a `ψ` atom. -/
def psiHead (w : Od) : Bool :=
  match w with
  | (.psi _ _, _) :: _ => true
  | _ => false

/-! ### Fix U -/

section
variable (Mf : Od → Cols)

/-- `P = ψ_{Ω_u}(Ω_{Ω_{L+1}})` as `MpsiLevel3` gives it. -/
def PL (L : Nat) (u : Od) : Cols := MpsiLevel3 Mf u (omS (omN (L + 1)))

/-- The mark `(L+1, L+1, 1)`: `P ++ mark` is the argument `Ω_{Ω_ω}`. -/
def markL (L : Nat) : TrioRules.Col := ⟨((L + 1 : Nat) : Int), ((L + 1 : Nat) : Int), true⟩

/-- `R_n = (P ++ mark)[n]`: the argument `Ω_{Ω_{L+1+n}}`. -/
def RL (L : Nat) (u : Od) (n : Nat) : Cols := expandC n ((PL Mf L u).push (markL L))

/-- The argument `Ω_Ω`: `(L+1,L+1,1)(L+2,L+1,1)(L+3,1,0)` after `P`. -/
def omegaOmegaL (L : Nat) : Cols :=
  #[⟨((L + 1 : Nat) : Int), ((L + 1 : Nat) : Int), true⟩,
    ⟨((L + 2 : Nat) : Int), ((L + 1 : Nat) : Int), true⟩,
    ⟨((L + 3 : Nat) : Int), 1, false⟩]

/-- **The table** for `u` of finite level `L` (all rows but the collapse row). -/
def tableU (L : Nat) (u w : Od) (old : Cols) : Cols :=
  let p := PL Mf L u
  let mw := Mf w
  if !lt (omN (L + 1)) w then old else
  match finIdx w with
  | some m =>
    if w == omN m then RL Mf L u (m - L - 1)
    else
      let src := lowerLast (Mf (omN (m + 1)))
      if properPrefix src mw then reroot src (lowerLast (RL Mf L u (m - L))) mw else old
  | none =>
    if levelOmega w then (if headOK mw then p ++ liftLk L mw else old)
    else if lt w omOm then (if headOK mw then p ++ liftBk L mw else old)
    else if w == omOm then p ++ omegaOmegaL L
    else if L == 1 && lt w omOmSucc then
      let src := lowerLast (Mf omOmSucc)
      if properPrefix src mw then reroot src p mw else old
    else old

/-- Rule 9 without the collapse row: the table for an uncountable successor `u` of
finite level, `MpsiLevel3` otherwise. -/
def ncU (u X : Od) : Cols :=
  let old := MpsiLevel3 Mf u X
  if !lt bigOmega u || !isSucc u then old else
  match lvlO X, finLvl u with
  | some w, some L => if L ≥ 1 then tableU Mf L u w old else old
  | _, _ => old

/-- The collapse index `t` of `w`: `M(w)` starts with `low M(Ω_t)` (tried for `t` the
level of `w` and its successor). -/
def collapseIdx (w : Od) : Option Od :=
  match lvlO w with
  | none => none
  | some l =>
    let mw := Mf w
    if !(Mf (omS l)).isEmpty && properPrefix (lowerLast (Mf (omS l))) mw then some l
    else if properPrefix (lowerLast (Mf (omS (add l one)))) mw then some (add l one)
    else none

/-- `A_u(t) = M(ψ_{Ω_u}(Ω_{Ω_t}))`; at `t = u` the formal leaf of `Ω_u`. -/
def argA (u t : Od) : Cols :=
  if cmpOrd t u == .eq then formalTop ((MpsiLevel3 Mf u (omS u)).pop)
  else ncU Mf u (omS (omS t))

/-- The collapse row acts for `t = L+1` and for `Ω+1 < t ≤ u`. -/
def collapseAt (L : Nat) (u t : Od) : Bool :=
  cmpOrd t (nat (L + 1)) == .eq || (lt omegaOnePlusOne t && cmpOrd t u != .gt)

/-- **Fix U**: rule 9 (see the table in the module docstring). -/
def MpsiLevelU (u X : Od) : Cols :=
  let r := ncU Mf u X
  if !lt bigOmega u || !isSucc u then r else
  match lvlO X, finLvl u with
  | some w, some L =>
    if lt w u || !psiHead w || L == 0 then r else
    match collapseIdx Mf w with
    | some t =>
      if collapseAt L u t then reroot (lowerLast (Mf (omS t))) (lowerLast (argA Mf u t)) (Mf w)
      else r
    | none => r
  | _, _ => r

/-- **Fix U fires**: `MpsiLevelU` is not `MpsiLevel3`. -/
def fixUFires (u X : Od) : Bool := MpsiLevelU Mf u X != MpsiLevel3 Mf u X

/-- One step of the builder: `MstepAll` with rule 9 by `MpsiLevelU`. -/
def MstepU (alpha : Od) : Cols :=
  match lvlO alpha, isPsiLevel alpha with
  | some _, some uX => MpsiLevelU Mf uX.1 uX.2
  | _, _ => MstepAll Mf alpha

/-! ### What is proved about one step -/

/-- On every `α` that is not `ψ_{Ω_u}(X)`, the step is `MstepAll`'s. -/
theorem MstepU_notPsi (alpha : Od) (h : lvlO alpha = none ∨ isPsiLevel alpha = none) :
    MstepU Mf alpha = MstepAll Mf alpha := by
  rcases h with h | h
  · simp [MstepU, h]
  · cases hv : lvlO alpha <;> simp [MstepU, hv, h]

/-- On `α = ψ_{Ω_u}(X)` the step is `MpsiLevelU`, and `MstepAll`'s is `MpsiLevel3`. -/
theorem MstepU_psi (alpha v : Od) (uX : Od × Od) (hv : lvlO alpha = some v)
    (hp : isPsiLevel alpha = some uX) :
    MstepU Mf alpha = MpsiLevelU Mf uX.1 uX.2 ∧ MstepAll Mf alpha = MpsiLevel3 Mf uX.1 uX.2 :=
  ⟨by simp [MstepU, hv, hp], (MstepAll_psi Mf alpha v uX hv hp).2⟩

/-- Rule 9 without the collapse row is `MpsiLevel3` when `u ≤ Ω` or `u` is not a successor. -/
theorem ncU_of_not (u X : Od) (h : (!lt bigOmega u || !isSucc u) = true) :
    ncU Mf u X = MpsiLevel3 Mf u X := by
  simp only [ncU, h, ite_true]

/-- **Fix U does not touch** `u ≤ Ω` (in particular every countable `u`) nor a limit `u`. -/
theorem MpsiLevelU_of_not (u X : Od) (h : (!lt bigOmega u || !isSucc u) = true) :
    MpsiLevelU Mf u X = MpsiLevel3 Mf u X := by
  simp only [MpsiLevelU, h, ite_true, ncU_of_not Mf u X h]

/-- **Fix U does not touch** a `u` of infinite level (`Ω_ω ≤ u`, e.g. `Ω_ω+1`, `Ω_Ω+1`). -/
theorem MpsiLevelU_of_finLvl_none (u X : Od) (h : finLvl u = none) :
    MpsiLevelU Mf u X = MpsiLevel3 Mf u X := by
  unfold MpsiLevelU ncU
  cases lvlO X <;> simp [h]

/-- Nor a countable argument. -/
theorem MpsiLevelU_of_countable_arg (u X : Od) (h : lvlO X = none) :
    MpsiLevelU Mf u X = MpsiLevel3 Mf u X := by
  unfold MpsiLevelU ncU
  simp [h]

/-- The table leaves every argument level `w ≤ Ω_{L+1}` to `MpsiLevel3`. -/
theorem tableU_of_le (L : Nat) (u w : Od) (old : Cols) (h : lt (omN (L + 1)) w = false) :
    tableU Mf L u w old = old := by
  simp [tableU, h]

/-- When Fix U does not fire, the step is `MstepAll`'s. -/
theorem MstepU_eq_MstepAll (alpha : Od) (h : ∀ uX, isPsiLevel alpha = some uX →
    fixUFires Mf uX.1 uX.2 = false) : MstepU Mf alpha = MstepAll Mf alpha := by
  cases hv : lvlO alpha with
  | none => exact MstepU_notPsi Mf alpha (Or.inl hv)
  | some v =>
    cases hp : isPsiLevel alpha with
    | none => exact MstepU_notPsi Mf alpha (Or.inr hp)
    | some uX =>
      have h1 := h uX hp
      unfold fixUFires at h1
      rw [(MstepU_psi Mf alpha v uX hv hp).1, (MstepU_psi Mf alpha v uX hv hp).2]
      simpa using h1

end

/-! ### `reroot` keeps its image as a prefix -/

/-- `reroot src img m` starts with `img`. -/
theorem reroot_prefix (src img m : Cols) : (reroot src img m).extract 0 img.size = img := by
  simp [reroot, Array.extract_append]

/-- The columns of `m` after `src` are all kept: one output column each. -/
theorem rerootTail_size (src img m : Cols) :
    (rerootTail src img m).size = m.size - src.size := by
  simp only [rerootTail, List.size_toArray, Array.size_map]
  induction m.size with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih]
    by_cases h : n ≥ src.size
    · simp [h]; omega
    · simp [h]; omega

/-- `reroot src img m` has `img.size + (m.size - src.size)` columns. -/
theorem reroot_size (src img m : Cols) :
    (reroot src img m).size = img.size + (m.size - src.size) := by
  simp [reroot, rerootTail_size]

/-- The lifts keep every column from index 4 on. -/
theorem liftLk_size (k : Nat) (m : Cols) : (liftLk k m).size = m.size - 4 := by
  simp [liftLk]

/-! ### The builder -/

/-- The builder with fuel. -/
def MfuelU : Nat → Od → Cols
  | 0, _ => #[]
  | n + 1, a => MstepU (MfuelU n) a

/-- `α ↦` the columns of `ψ_0(Ω_α)`, by rules 1–10 with Fixes A–E, N and U. -/
def MU (alpha : Od) : Cols := MfuelU fuel alpha

/-- **The trio matrix of `ψ_0(Ω_α)` with Fixes A–E, N and U.** -/
def trioRuleMatrixU (alpha : Od) : List (List Nat) := toRows (MU alpha)

/-- The matrix for a label of the sheet. -/
def trioRuleMatrixOfU (s : String) : Option (List (List Nat)) := do
  let a ← parse s
  if a.isEmpty then none else some (trioRuleMatrixU a)

/-- The matrix of a label, `[]` when it does not parse. -/
def uOf (s : String) : List (List Nat) := (trioRuleMatrixOfU s).getD []

/-- **Every column is three rows deep with `z < 2`.** -/
theorem WF3_trioRuleMatrixU (alpha : Od) : WF3 (trioRuleMatrixU alpha) := WF3_toRows _

/-- `MU` is one Fix U step on the builder one fuel down. -/
theorem MU_eq_step : MU = MstepU (MfuelU (fuel - 1)) := rfl

/-! ### The claimed domain -/

/-- `ψ_{Ω_u}(Ω_w)` lies in the part of the table that the checks support (fuel `n`
bounds the nesting of `ψ_{Ω_u}` arguments):

* `u` an uncountable successor, `u ≤ w`;
* `u` of level 1: `w < Ω_{Ω+1}`, or `u < Ω+ω` (every `w`);
* `u` of finite level `L ≥ 2`: `w ≤ Ω_Ω`, or `w = ψ_{Ω_u}(Y)` with the level of `Y`
  again in the domain. -/
def inDomainF : Nat → Od → Od → Bool
  | 0, _, _ => false
  | n + 1, u, w =>
    if !lt bigOmega u || !isSucc u || lt w u then false
    else if cmpOrd w u == .eq then true
    else
      let top : Bool := match w with
        | [(.psi [(.W v, 1)] Y, 1)] =>
          cmpOrd v u == .eq && (match lvlO Y with
            | some y => inDomainF n u y
            | none => false)
        | _ => false
      match finLvl u with
      | some 1 => lt w omOmSucc || lt u omegaPlusOmega
      | some L => decide (L ≥ 2) && (top || lt w omOm || w == omOm)
      | none => false

/-- The claimed domain, with nesting depth up to 20. -/
def inDomain (u w : Od) : Bool := inDomainF 20 u w

/-- A label `ψ_{Ω_u}(X)` in the claimed domain. -/
def labelInDomain (a : Od) : Bool :=
  match a with
  | [(.psi [(.W u, 1)] X, 1)] =>
    match lvlO X with
    | some w => inDomain u w
    | none => false
  | _ => false

end Googology.Trans.BMS.TrioFixU
