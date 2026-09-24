import Googology.Trans.BMS.TrioFixU

/-!
# Fix U2: rule 9 where Fix U still gives a wrong matrix

A patch on top of `TrioFixU.lean` (rules 1–10 of
[koteitan/trio](https://github.com/koteitan/trio) with Fixes A–E, N and U).  It changes
**only rule 9** (`α = ψ_{Ω_u}(X)`), and only for an uncountable successor `u`.  Every other
step of the builder is `MstepAll` unchanged (`MstepU2_notPsi`).  Outside the shift row,
every matrix that Fix E or Fix U changes keeps Fix U's matrix (`MpsiLevelU2_of_fixed`); on
the shift row (2 below) Fix U2 replaces Fix U's matrix.  On the probe labels of Fix U's
claimed domain (`inDomain`) only the (a) labels change (checked in `TrioFixU2Sheet.lean`,
numbers in TRIO-FIX-U2.md).  The explanation and the numbers are in
[TRIO-FIX-U2.md](TRIO-FIX-U2.md).

**Notation** as in `TrioFixU.lean`: `w` is the level of the argument `X`, `M(v)` the builder
one step down (`Mf v`), `P = M(ψ_{Ω_u}(Ω_{Ω_{L+1}}))` for `u` of finite level `L`,
`base = low M(Ω_u)`.

**The change** (for merging: replace `MpsiLevelU` by `MpsiLevelU2` in the step).

1. **Fix K (keep).**  Where Fix E and Fix U both leave rule 9 alone (so the matrix is
   `MpsiLevel2`'s: `base ++ writeLevel(M(w)) ++ mark`), `writeLevel` is replaced by
   `writeLevelK`.  `writeLevel` copies the tail of `M(w)` (the part after the prefix the
   ladders cover) with one `x` shift `dx`.  A tail column whose nearest row-0 ancestor in the
   covered prefix is **not** the column the tail hangs from (typically an upgrade mark,
   rule 5, hanging from an early storey anchor) lost its parent under that shift.
   `writeLevelK` keeps such a column **in place** (`x` and `y` unchanged) when its ancestor
   column is also at the same index of `base`.  This is `reroot`'s rule of Fix U ("columns
   that do not hang from the moved part are copied as they are") applied to `writeLevel`.
   It repairs (a): `u = Ω+k`, `w ≥ Ω_{Ω+1}` not headed by `ψ`, e.g.
   `ψ_{Ω_{Ω+2}}(Ω_{Ω_{Ω+1}+Ω_Ω})`: the rules end in `(12,2,0)(5,2,1)(6,2,1)(7,1,0)` (not
   standard), Fix K in `(12,2,0)(2,2,1)(3,2,1)(4,1,0)` (standard; the mark `Ω_Ω` stands at
   the same place as in `M(w)` and in `base`).
2. **The shift row** (for `u` of finite level `L ≥ 2`, `Ω_Ω < w ≤ Ω_{Ω_L}`, before Fix U's
   collapse row).  Then `M(w) = M(Ω_Ω) ++ (1,1,0) ++ T` and
   `M(ψ_{Ω_u}(Ω_w)) = P ++ (L+1,L+1,1)(L+2,L+1,1)(L+3,1,0) ++ T[x + L + 2]`:
   the argument `Ω_Ω` of Fix U's table followed by the rest of `M(w)`, moved right so that
   the column `(1,1,0)` of `M(w)` falls on the `Ω` leaf `(L+3,1,0)`; row 1 is not changed.
   For `L = 1` the range `(Ω_Ω, Ω_{Ω_1}]` is empty, so this row is new only for `L ≥ 2`.
   It repairs (b) below `Ω_{Ω_L}`.  Above `Ω_{Ω_L}` (up to `Ω_u`) the old rule 9 with Fix K
   is used: there `M(w)` starts with `base`, and the old rule equals Fix U's `reroot` onto
   `P`, the same shape as Fix U's row `Ω_Ω < w < Ω_{Ω+1}` for `L = 1`.

**What is claimed.**  `inDomainU2 u w`: Fix U's `inDomain`, and for an uncountable
successor `u` of finite level `L ≥ 2` and `u ≤ w`: every `w` when `u = Ω_L + k`, and
`w < Ω_{Ω_L+1}` for the other `u` (as Fix U's boundary `Ω_{Ω+1}` for `L = 1`).  On the probe labels in it whose
`M(w)` is itself standard and in order, the matrices are standard (yaBMS `bms -s`, outside
Lean) and in the order of the labels (`#guard`s in `TrioFixU2Sheet.lean`).  Faults that come
from `M(w)` (a non-standard or out-of-order `M(w)`) are not repaired by a rule-9 patch and
are listed in TRIO-FIX-U2.md.
-/

namespace Googology.Trans.BMS.TrioFixU2

open Googology.Trans.BMS.TrioRules
open Googology.Trans.BMS.TrioRules2
open Googology.Trans.BMS.TrioRules3
open Googology.Trans.BMS.TrioRulesNL
open Googology.Trans.BMS.TrioRulesAll
open Googology.Trans.BMS.TrioFixU

/-! ### Fix K: `writeLevel` that keeps foreign columns in place -/

section
variable (Mf : Od → Cols)

/-- The ladder coverage of `writeLevel` (rule 10): `(level, index)` of the deepest level
column of `M(v)` covered by a ladder. -/
def coverK (v : Od) (d : Int) (ladders : List Cols) : Int × Nat :=
  let base := Mf v
  let par := forest base
  let step (acc : Int × Nat) (lad : Cols) : Int × Nat :=
    (List.range (commonPrefix lad base)).foldl (fun li i =>
      if i ≥ 1 && isLevel base par i && decide ((colAt base i).y ≤ d) && i > li.2
      then ((colAt base i).y, i) else li) acc
  (Mf (nat d.toNat) :: ladders).foldl step (0, 0)

/-- **`writeLevelK`** (`keep = true`): `writeLevel` with `arg = true`, except that a tail
column whose nearest row-0 ancestor in the covered prefix is not the one the tail hangs from,
and is the same column at the same index of `pre`, is copied in place.  With
`keep = false` it is `writeLevel` (`writeLevelK_false`). -/
def writeLevelK (keep : Bool) (pre : Cols) (v : Od) (x d : Int) (ladders : List Cols) : Cols :=
  let base := Mf v
  let par := forest base
  let li := coverK Mf v d ladders
  let n := li.2 + 1
  let tail := base.extract n base.size
  if tail.isEmpty then #[⟨x, (lastC base).y, false⟩] else
  let bump := d - li.1
  let dx := x - (colAt tail 0).x
  let a0 := ancBelow par n (base.size + 1) n
  tail.mapIdx fun i c =>
    let a := ancBelow par n (base.size + 1) (n + i)
    if keep && a != a0 && decide (a < pre.size) && colAt pre a == colAt base a then c
    else ⟨c.x + dx, c.y + (if relative base par (n + i) then bump else 0), c.z⟩

/-- Rule 9 on the corrected base (`MpsiLevel2`) with `writeLevelK`. -/
def MpsiLevelK (keep : Bool) (u X : Od) : Cols :=
  let base := MOmega2 Mf u
  let y0 := (lastC base).y
  let cols := setLastY base (y0 - 1)
  let x := (lastC base).x + 1
  match lvlO X with
  | none => #[]
  | some w =>
    if cmpOrd w u == .eq then cols.push ⟨x, y0, false⟩
    else appendSuffix Mf (cols ++ writeLevelK Mf keep cols w x (y0 - 1) [Mf u, cols]) w 0 none

/-! ### The shift row -/

/-- `M(Ω_Ω) ++ (1,1,0)`: the first eight columns of `M(w)` for `Ω_Ω < w < Ω_{Ω_ω}`. -/
def headShift : Cols :=
  #[⟨0, 0, false⟩, ⟨1, 1, true⟩, ⟨2, 1, true⟩, ⟨3, 1, false⟩,
    ⟨1, 1, true⟩, ⟨2, 1, true⟩, ⟨3, 1, false⟩, ⟨1, 1, false⟩]

/-- Move columns right by `k`. -/
def shiftX (k : Int) (m : Cols) : Cols := m.map fun c => { c with x := c.x + k }

/-- **The shift row**: `P ++ (L+1,L+1,1)(L+2,L+1,1)(L+3,1,0) ++ M(w)[8:]` moved right by
`L + 2`. -/
def shiftRow (L : Nat) (u : Od) (mw : Cols) : Cols :=
  PL Mf L u ++ omegaOmegaL L ++ shiftX ((L + 2 : Nat) : Int) (mw.extract 8 mw.size)

/-- The shift row applies: `u` of finite level `L ≥ 2`, `Ω_Ω < w ≤ Ω_{Ω_L}`, and `M(w)`
starts with `M(Ω_Ω) ++ (1,1,0)`. -/
def shiftAt (L : Nat) (w : Od) : Bool :=
  decide (L ≥ 2) && lt omOm w && !lt (omS (omN L)) w &&
    decide ((Mf w).size > 8) && (Mf w).extract 0 8 == headShift

/-! ### Fix U2 -/

/-- Neither Fix E nor Fix U changes rule 9 here: the matrix is `MpsiLevel2`'s. -/
def plainRule9 (u X : Od) : Bool :=
  MpsiLevelU Mf u X == MpsiLevel3 Mf u X && MpsiLevel3 Mf u X == MpsiLevel2 Mf u X

/-- **Fix U2**: rule 9. -/
def MpsiLevelU2 (u X : Od) : Cols :=
  let r := MpsiLevelU Mf u X
  if !lt bigOmega u || !isSucc u then r else
  match lvlO X with
  | none => r
  | some w =>
    let k := if plainRule9 Mf u X then MpsiLevelK Mf true u X else r
    match finLvl u with
    | some L => if shiftAt Mf L w then shiftRow Mf L u (Mf w) else k
    | none => k

/-- **Fix U2 fires**: `MpsiLevelU2` is not `MpsiLevelU`. -/
def fixU2Fires (u X : Od) : Bool := MpsiLevelU2 Mf u X != MpsiLevelU Mf u X

/-- One step of the builder: `MstepAll` with rule 9 by `MpsiLevelU2`. -/
def MstepU2 (alpha : Od) : Cols :=
  match lvlO alpha, isPsiLevel alpha with
  | some _, some uX => MpsiLevelU2 Mf uX.1 uX.2
  | _, _ => MstepAll Mf alpha

/-! ### What is proved about one step -/

/-- `writeLevelK` without keeping is `writeLevel` (with `arg = true`). -/
theorem writeLevelK_false (pre : Cols) (v : Od) (x d : Int) (ladders : List Cols) :
    writeLevelK Mf false pre v x d ladders = writeLevel Mf v x d true ladders := by
  simp only [writeLevelK, writeLevel, coverK, Bool.false_and, Bool.false_eq_true, ite_false]
  rfl

/-- So `MpsiLevelK` without keeping is `MpsiLevel2`: Fix K changes nothing but the kept
columns. -/
theorem MpsiLevelK_false (u X : Od) : MpsiLevelK Mf false u X = MpsiLevel2 Mf u X := by
  unfold MpsiLevelK MpsiLevel2
  simp only [writeLevelK_false]
  rfl

/-- Fix K keeps the number of columns `writeLevel` writes. -/
theorem writeLevelK_size (keep : Bool) (pre : Cols) (v : Od) (x d : Int) (ladders : List Cols) :
    (writeLevelK Mf keep pre v x d ladders).size = (writeLevelK Mf false pre v x d ladders).size := by
  unfold writeLevelK
  simp only
  split <;> simp only [Array.size_mapIdx]

/-- On every `α` that is not `ψ_{Ω_u}(X)`, the step is `MstepAll`'s. -/
theorem MstepU2_notPsi (alpha : Od) (h : lvlO alpha = none ∨ isPsiLevel alpha = none) :
    MstepU2 Mf alpha = MstepAll Mf alpha := by
  rcases h with h | h
  · simp [MstepU2, h]
  · cases hv : lvlO alpha <;> simp [MstepU2, hv, h]

/-- On `α = ψ_{Ω_u}(X)` the step is `MpsiLevelU2`, and Fix U's is `MpsiLevelU`. -/
theorem MstepU2_psi (alpha v : Od) (uX : Od × Od) (hv : lvlO alpha = some v)
    (hp : isPsiLevel alpha = some uX) :
    MstepU2 Mf alpha = MpsiLevelU2 Mf uX.1 uX.2 ∧ MstepU Mf alpha = MpsiLevelU Mf uX.1 uX.2 :=
  ⟨by simp [MstepU2, hv, hp], (MstepU_psi Mf alpha v uX hv hp).1⟩

/-- **Fix U2 does not touch** `u ≤ Ω` (every countable `u`) nor a limit `u`: there rule 9 is
Fix U's, which is `MpsiLevel3` (`MpsiLevelU_of_not`). -/
theorem MpsiLevelU2_of_not (u X : Od) (h : (!lt bigOmega u || !isSucc u) = true) :
    MpsiLevelU2 Mf u X = MpsiLevelU Mf u X ∧ MpsiLevelU2 Mf u X = MpsiLevel3 Mf u X := by
  have h1 : MpsiLevelU2 Mf u X = MpsiLevelU Mf u X := by simp only [MpsiLevelU2, h, ite_true]
  exact ⟨h1, h1.trans (MpsiLevelU_of_not Mf u X h)⟩

/-- Nor a countable argument. -/
theorem MpsiLevelU2_of_countable_arg (u X : Od) (h : lvlO X = none) :
    MpsiLevelU2 Mf u X = MpsiLevelU Mf u X := by
  unfold MpsiLevelU2
  split <;> simp [h]

/-- Outside the shift row, where Fix E or Fix U changes rule 9, Fix U2 keeps that matrix. -/
theorem MpsiLevelU2_of_fixed (u X w : Od) (hw : lvlO X = some w)
    (hs : ∀ L, finLvl u = some L → shiftAt Mf L w = false) (hp : plainRule9 Mf u X = false) :
    MpsiLevelU2 Mf u X = MpsiLevelU Mf u X := by
  unfold MpsiLevelU2
  split
  · rfl
  · rw [hw]
    cases hL : finLvl u with
    | none => simp [hp]
    | some L => simp [hs L hL, hp]

/-- When Fix U2 does not fire, the step is Fix U's. -/
theorem MstepU2_eq_MstepU (alpha : Od) (h : ∀ uX, isPsiLevel alpha = some uX →
    fixU2Fires Mf uX.1 uX.2 = false) : MstepU2 Mf alpha = MstepU Mf alpha := by
  cases hv : lvlO alpha with
  | none => rw [MstepU2_notPsi Mf alpha (Or.inl hv), MstepU_notPsi Mf alpha (Or.inl hv)]
  | some v =>
    cases hp : isPsiLevel alpha with
    | none => rw [MstepU2_notPsi Mf alpha (Or.inr hp), MstepU_notPsi Mf alpha (Or.inr hp)]
    | some uX =>
      have h1 := h uX hp
      unfold fixU2Fires at h1
      rw [(MstepU2_psi Mf alpha v uX hv hp).1, (MstepU2_psi Mf alpha v uX hv hp).2]
      simpa using h1

/-- The shift row keeps every column of `M(w)` from index 8 on: `P.size + 3 + (m.size − 8)`
columns. -/
theorem shiftRow_size (L : Nat) (u : Od) (mw : Cols) :
    (shiftRow Mf L u mw).size = (PL Mf L u).size + 3 + (mw.size - 8) := by
  simp [shiftRow, shiftX, omegaOmegaL]
  omega

/-- The shift row starts with `P` followed by the argument `Ω_Ω` of Fix U's table. -/
theorem shiftRow_prefix (L : Nat) (u : Od) (mw : Cols) :
    (shiftRow Mf L u mw).extract 0 ((PL Mf L u).size + 3) = PL Mf L u ++ omegaOmegaL L := by
  have h3 : (omegaOmegaL L).size = 3 := rfl
  have := Array.extract_append (as := PL Mf L u ++ omegaOmegaL L)
    (bs := shiftX ((L + 2 : Nat) : Int) (mw.extract 8 mw.size)) (i := 0)
    (j := (PL Mf L u).size + 3)
  have hs : (PL Mf L u ++ omegaOmegaL L).size = (PL Mf L u).size + 3 := by
    rw [Array.size_append, h3]
  simp only [shiftRow]
  rw [this, ← hs]
  simp only [Nat.zero_sub, Nat.sub_self, Array.extract_size, Array.extract_zero, Array.append_empty]

end

/-! ### The builder -/

/-- The builder with fuel. -/
def MfuelU2 : Nat → Od → Cols
  | 0, _ => #[]
  | n + 1, a => MstepU2 (MfuelU2 n) a

/-- `α ↦` the columns of `ψ_0(Ω_α)`, by rules 1–10 with Fixes A–E, N, U and U2. -/
def MU2 (alpha : Od) : Cols := MfuelU2 fuel alpha

/-- **The trio matrix of `ψ_0(Ω_α)` with Fixes A–E, N, U and U2.** -/
def trioRuleMatrixU2 (alpha : Od) : List (List Nat) := toRows (MU2 alpha)

/-- The matrix for a label of the sheet. -/
def trioRuleMatrixOfU2 (s : String) : Option (List (List Nat)) := do
  let a ← parse s
  if a.isEmpty then none else some (trioRuleMatrixU2 a)

/-- The matrix of a label, `[]` when it does not parse. -/
def u2Of (s : String) : List (List Nat) := (trioRuleMatrixOfU2 s).getD []

/-- **Every column is three rows deep with `z < 2`.** -/
theorem WF3_trioRuleMatrixU2 (alpha : Od) : WF3 (trioRuleMatrixU2 alpha) := WF3_toRows _

/-- `MU2` is one Fix U2 step on the builder one fuel down. -/
theorem MU2_eq_step : MU2 = MstepU2 (MfuelU2 (fuel - 1)) := rfl

/-! ### The claimed domain -/

/-- `ψ_{Ω_u}(Ω_w)` in the part the checks support: Fix U's `inDomain`, and for an
uncountable successor `u` of finite level `L ≥ 2` with `u ≤ w`: every `w` when
`u < Ω_L + ω` (`u = Ω_L + k`), and `w < Ω_{Ω_L+1}` otherwise (the same boundary as Fix U's
for `L = 1`). -/
def inDomainU2 (u w : Od) : Bool :=
  inDomain u w ||
    (lt bigOmega u && isSucc u && !lt w u &&
      match finLvl u with
      | some L => decide (L ≥ 2) &&
          (lt u (add (omN L) omega) || lt w (omS (add (omN L) one)))
      | none => false)

/-- A label `ψ_{Ω_u}(X)` in the claimed domain. -/
def labelInDomainU2 (a : Od) : Bool :=
  match a with
  | [(.psi [(.W u, 1)] X, 1)] =>
    match lvlO X with
    | some w => inDomainU2 u w
    | none => false
  | _ => false

/-- Fix U's domain is part of Fix U2's. -/
theorem inDomain_le_U2 (u w : Od) (h : inDomain u w = true) : inDomainU2 u w = true := by
  simp [inDomainU2, h]

end Googology.Trans.BMS.TrioFixU2
