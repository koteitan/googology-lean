/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/PBStageBCutLeg.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.PBStageBChildren
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeAscLeg

set_option backward.do.legacy false

/-!
# `CutLeg` from `GenLeg` (stage B)

`CutLeg` (`Recon/ParentBelowLowerProfile.lean`, wording unchanged): let `v = (x, k)` be a node of
`M(s)` (`x > c_r`) whose left end is in the column `ℓ` (the source column of the context `ctx'`,
`ℓ ≥ c_r`). Every gap copy `e'` of the copy of `ℓ` (block `i ≥ 1`) whose origin `(ℓ, C')` is
below `v`, or at the row of `v` when the copy of `x` makes a gap copy of `v`, has a gap copy of
the copy of `x` at the same row.

## Proof: the two item trees run in parallel

Call an origin row `r₀` a *target* (`TG`) if it is the row of a node of `ℓ` below `v`, or at the
row of `v` when `x` ascends at the root tops of that row (`AscX`). By the canonical shadow, `x`
has a node at every target row. We follow the items `λ` of the copy of `ℓ` that produce the gap
copy and show that the copy of `x` has an item `ξ` with the same target region related by
`RelC`:

* `λ = ξ` (the same item), or
* `R2`: same source `S` and target, both not cut-bottom, each plain or a clean copy of the root
  top `ρ` of `S`, and `ρ` lies above every target row (`R2Cond`: `row v < row ρ`, or `row ρ = row v`
  and `x` does not ascend there).

The two copies differ only in the top of the column in `S`, in the ascension test, and in the
number `g` of generations of a copied root row. The top is handled by the shadow nodes of `x`.
The ascension test agrees below `v` (`AscLeg.ascLeg`); where it differs, `R2Cond` holds, and the
two items keep the same children in the slots below `ρ` and a plain or clean child in the slot of
`ρ` (`R2`). For the generations we use `GenLeg` (about `M(s)` alone, proved in
`PBStageBGenLeg.lean`): at a row `C` of a node of `ℓ` at or below `v`, the generations of `(ℓ, C)`
are at most those of `(x, C)`. `cutLeg_of_genLeg` is in `PBStageBCutLegMain.lean`.
-/

namespace OmegaY.Official.Classification.Proofs.CopyShape.PBStageB

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr ChainCorr.CopyMonoProof
open Recon.LowerPB

/-! ## The statement about `M(s)` (proved: `genLeg`) -/

/-- (new; proved: `genLeg`, `PBStageBGenLeg.lean`) **Generations along a leg.** Let `v = (x, k)` (`c_r < x ≤ x₀`) have its left end
in the column `ℓ ≥ c_r`. At a row `C` where both `x` and `ℓ` have a node, with the node of `ℓ` at
or below `v`, the generations of the node of `ℓ` are at most those of the node of `x`. -/
def GenLeg : Prop :=
  ∀ (s : List Nat) (M : Mountain) (t : Cell) (root : Ref), Recon.Top s M t root →
    ∀ (x k : Nat) (cp : Cell) (lref : Ref), root.column < x → x ≤ M.size - 1 → 1 ≤ k →
      cell? M ⟨x, k⟩ = some cp → cp.left = some lref → root.column ≤ lref.column →
      ∀ (C : Row) (ax ay : Ref) (cx cy : Cell) (gx gy : Nat),
        nodeAt M x C = some (ax, cx) → nodeAt M lref.column C = some (ay, cy) →
        cy.row ≤ cp.row →
        generations M root.column C (x + 1) ax cx 0 = .ok gx →
        generations M root.column C (lref.column + 1) ay cy 0 = .ok gy → gy ≤ gx

/-! ## The setting -/

/-- The data of `CutLeg`: a node `v = (ctx.x, k)` with cell `cp` whose left end `r` is in the
column `ctx'.x`, two contexts of one block `i ≥ 1`. -/
structure Setup (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i : Nat)
    (ctx ctx' : Context) (k : Nat) (cp : Cell) (r : Ref) : Prop where
  run : Official.expandDiagram s n = .ok R
  top : Recon.Top s M t root
  i1 : 1 ≤ i
  iln : i ≤ n
  B : BCtx M R root.column (M.size - 1) i ctx
  B' : BCtx M R root.column (M.size - 1) i ctx'
  hx : root.column < ctx.x
  hk : 1 ≤ k
  hcp : cell? M ⟨ctx.x, k⟩ = some cp
  hl : cp.left = some r
  hr : r.column = ctx'.x

/-- `x` ascends at every root top of the row of `v`. -/
def AscX (ctx : Context) (cp : Cell) : Prop :=
  ∀ ρ : Ref × Cell, official ρ.2.row = official cp.row → ascends ctx (some ρ) = .ok true

/-- A target origin row: the row of a node of `ℓ` below `v`, or at the row of `v` when `x`
ascends there. -/
def TG (M : Mountain) (ctx ctx' : Context) (cp : Cell) (r0 : Row) : Prop :=
  ∃ (q : Ref) (cq : Cell), q.column = ctx'.x ∧ 1 ≤ q.index ∧ cell? M q = some cq ∧
    official cq.row = r0 ∧ (cq.row < cp.row ∨ (cq.row = cp.row ∧ AscX ctx cp))

/-- The root top `ρ` is above every target row. -/
def R2Cond (ctx : Context) (cp : Cell) (ρrow : Row) : Prop :=
  official cp.row < ρrow ∨ (ρrow = official cp.row ∧ ¬ AscX ctx cp)

/-- The relation of two items with the same target region. -/
def R2 (M : Mountain) (cr : Nat) (ctx : Context) (cp : Cell) (d : Nat) (a b : Item) : Prop :=
  a.source = b.source ∧ a.target = b.target ∧ a.cutBottom = false ∧ b.cutBottom = false ∧
    ∃ ρ : Ref × Cell, topIn M cr d a.source = some ρ ∧ R2Cond ctx cp (official ρ.2.row) ∧
      (a.clean = none ∨ a.clean = some (official ρ.2.row)) ∧
      (b.clean = none ∨ b.clean = some (official ρ.2.row))

def RelC (M : Mountain) (cr : Nat) (ctx : Context) (cp : Cell) (d : Nat) (a b : Item) : Prop :=
  a = b ∨ R2 M cr ctx cp d a b

/-! ## Rows -/

theorem ascends_row {ctx : Context} {a b : Ref × Cell} (h : official a.2.row = official b.2.row) :
    ascends ctx (some a) = ascends ctx (some b) := by
  obtain ⟨ar, ac⟩ := a
  obtain ⟨br, bc⟩ := b
  simp only at h
  show (match nodeAt ctx.source ctx.x (referenceRow (official ac.row)) with
      | none => pure false
      | some (ref, _) => reachesRoot ctx.source ctx.rootColumn (ctx.x + 1) ref) =
    (match nodeAt ctx.source ctx.x (referenceRow (official bc.row)) with
      | none => pure false
      | some (ref, _) => reachesRoot ctx.source ctx.rootColumn (ctx.x + 1) ref)
  rw [h]

namespace Setup

variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} {i : Nat}
  {ctx ctx' : Context} {k : Nat} {cp : Cell} {r : Ref}

theorem V (h : Setup s n R M t root i ctx ctx' k cp r) : MountainValid M :=
  build_valid_of_success h.top.build

theorem cp1 (h : Setup s n R M t root i ctx ctx' k cp r) : (1 : Row) ≤ cp.row :=
  one_le_row h.V h.hcp h.hk

theorem xle (h : Setup s n R M t root i ctx ctx' k cp r) : ctx.x ≤ M.size - 1 := h.B.xle

theorem lge (h : Setup s n R M t root i ctx ctx' k cp r) : root.column ≤ r.column := by
  rw [h.hr]; exact h.B'.xge

theorem tg_le (h : Setup s n R M t root i ctx ctx' k cp r) {r0 : Row}
    (hT : TG M ctx ctx' cp r0) : r0 ≤ official cp.row := by
  obtain ⟨q, cq, _, hq1, hcq, hrow, hor⟩ := hT
  rw [← hrow]
  have h1 := one_le_row h.V hcq hq1
  rcases hor with hlt | ⟨heq, _⟩
  · exact (Recon.official_strictMono h1 hlt).le
  · rw [heq]

/-- **The shadow of a target row**: `x` has a node at every target row. -/
theorem tg_x (h : Setup s n R M t root i ctx ctx' k cp r) {r0 : Row}
    (hT : TG M ctx ctx' cp r0) :
    ∃ kx cx, 1 ≤ kx ∧ cell? M ⟨ctx.x, kx⟩ = some cx ∧ official cx.row = r0 := by
  obtain ⟨q, cq, hqc, hq1, hcq, hrow, hor⟩ := hT
  have hle : cq.row ≤ cp.row := by
    rcases hor with hlt | ⟨heq, _⟩
    · exact hlt.le
    · exact le_of_eq heq
  have hcw : cell? M ⟨r.column, q.index⟩ = some cq := by
    have : q = ⟨r.column, q.index⟩ := by rw [h.hr, ← hqc]
    rw [← this]; exact hcq
  obtain ⟨k'', cv, hk'', hcv, hrv⟩ := shadow h.top.build h.hk h.hcp h.hl hq1 hcw hle
  exact ⟨k'', cv, hk'', hcv, by rw [hrv, hrow]⟩

theorem tg_lt (h : Setup s n R M t root i ctx ctx' k cp r) {r0 ρrow : Row}
    (hT : TG M ctx ctx' cp r0) (hC : R2Cond ctx cp ρrow) : r0 < ρrow := by
  rcases hC with hlt | ⟨heq, hna⟩
  · exact lt_of_le_of_lt (h.tg_le hT) hlt
  · obtain ⟨q, cq, _, hq1, hcq, hrow, hor⟩ := hT
    rcases hor with hlt | ⟨_, hasc⟩
    · rw [heq, ← hrow]
      exact Recon.official_strictMono (one_le_row h.V hcq hq1) hlt
    · exact absurd hasc hna

/-- **Where the two ascension tests differ, `R2Cond` holds.** -/
theorem asc_diff (h : Setup s n R M t root i ctx ctx' k cp r) {d : Nat} {S : Row} {ρr : Ref}
    {ρc : Cell} (hρ : topIn M root.column (d + 2) S = some (ρr, ρc)) {b1 b2 : Bool}
    (h1 : ascends ctx' (some (ρr, ρc)) = .ok b1) (h2 : ascends ctx (some (ρr, ρc)) = .ok b2)
    (hne : b1 ≠ b2) : R2Cond ctx cp (official ρc.row) := by
  rcases lt_trichotomy (official ρc.row) (official cp.row) with hlt | heq | hgt
  · exfalso
    have hiff := AscLeg.ascLeg h.top.build h.hx h.hk h.hcp h.hl h.lge hρ hlt ctx ctx' h.B.source
      h.B'.source h.B.root h.B'.root rfl h.hr.symm
    rw [h1, h2] at hiff
    cases b1 <;> cases b2 <;> simp_all
  · refine Or.inr ⟨heq, fun hA => ?_⟩
    have hx := hA (ρr, ρc) heq
    have hl := AscLeg.ascLegLe h.top.build h.hx h.hk h.hcp h.hl h.lge hρ (le_of_eq heq) ctx ctx'
      h.B.source h.B'.source h.B.root h.B'.root rfl h.hr.symm hx
    rw [h1] at hl
    rw [h2] at hx
    cases b1 <;> cases b2 <;> simp_all
  · exact Or.inl hgt

/-- The top of `x` in a region containing a target row is at least as high. -/
theorem topX (h : Setup s n R M t root i ctx ctx' k cp r) {r0 : Row}
    (hT : TG M ctx ctx' cp r0) {d : Nat} {S : Row} (hin : inRegion (d + 2) S r0 = true) :
    ∃ a, topIn M ctx.x (d + 2) S = some a ∧ r0.coeff d ≤ (official a.2.row).coeff d := by
  obtain ⟨kx, cx, hkx, hcx, hrow⟩ := h.tg_x hT
  have hin' : inRegion (d + 2) S (official cx.row) = true := by rw [hrow]; exact hin
  cases ha : topIn M ctx.x (d + 2) S with
  | none => exact absurd ha (topIn_ne_none_of_node (p := ⟨ctx.x, kx⟩) rfl hkx hcx hin')
  | some a =>
      refine ⟨a, rfl, ?_⟩
      have hle := le_top_of_node h.V (p := ⟨ctx.x, kx⟩) rfl hkx hcx hin' ha
      rw [hrow] at hle
      exact Recon.RowLaw.coeff_le_of_inRegion hin (topIn_inRegion ha) hle

/-- The node of `x` at a target row, as `nodeAt`. -/
theorem nodeAtX (h : Setup s n R M t root i ctx ctx' k cp r) {r0 : Row}
    (hT : TG M ctx ctx' cp r0) : ∃ p, nodeAt M ctx.x r0 = some p := by
  obtain ⟨kx, cx, hkx, hcx, hrow⟩ := h.tg_x hT
  have hmem := mem_realNodes_of_cell' (p := ⟨ctx.x, kx⟩) hcx hkx
  obtain ⟨p', hp'⟩ := Recon.RowLaw.nodeAt_of_mem hmem
  rw [hrow] at hp'
  exact ⟨p', hp'⟩

end Setup

end OmegaY.Official.Classification.Proofs.CopyShape.PBStageB
