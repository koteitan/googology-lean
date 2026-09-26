/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/ParentBelow.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.ParentBelowUpper
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.ParentBelowSplit

set_option backward.do.legacy false

/-!
# `ParentBelowHolds` reduced to the lower part

`ParentBelowHolds` (`ChainSplit.lean`) asks, for a real node `u` of a new column with the
node `u⁺` above it and the stored parent `p = π(u⁺)`, that `row p ≤ row u`. Let `τ` be the
row of the top `t` of the last column of `M(s)`. Proved so far:

* `row u ≥ τ` (the upper part of the column): `parentBelow_upper`;
* `row u⁺ = bump (row u) 0` (both in one region of level 1): `parentBelow_of_bump_zero`.

What remains is `LowerParentBelowHolds`: `row u < τ` and `row u⁺ = bump (row u) e` with
`e ≥ 1`, i.e. `u` is the top of the column in the region `B_{e+1}(row u)` of level `e + 1`
and `u⁺` is the base of the next region. By `parentBelow_of_gap`, it says that the column of
`p` has no node in that region above `row u`.

For `ChainHolds` only the case where the candidate `Q u` is in the column of `p` is needed
(`chainHolds_of_sameColumn`); `LowerSameColumnBelowHolds` is that case.
-/

namespace OmegaY.Official.Recon

open Canonical Expansion Geometry Frame

/-- **Open.** `ParentBelowHolds` in the lower part of a new column, for a step that leaves a
region of level `≥ 2`. -/
def LowerParentBelowHolds : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain), Official.expandDiagram s n = .ok R →
    ∀ (M : Mountain) (col : Column) (t : Cell), Canonical.build s = .ok M →
      M[M.size - 1]? = some col → col.back? = some t →
      ∀ u p up : (Frame.ofMountain R).Node, s.length - 1 ≤ u.1.val → Real u →
        (Frame.ofMountain R).rawParent u = some p → (Frame.ofMountain R).upper u = some up →
        (Frame.ofMountain R).height u < t.row →
        (Frame.ofMountain R).height up ≠ Row.bump ((Frame.ofMountain R).height u) 0 →
        (Frame.ofMountain R).height p ≤ (Frame.ofMountain R).height u

/-- **Open.** `LowerParentBelowHolds` when the candidate `Q u` is in the column of `p`. -/
def LowerSameColumnBelowHolds : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain), Official.expandDiagram s n = .ok R →
    ∀ (M : Mountain) (col : Column) (t : Cell), Canonical.build s = .ok M →
      M[M.size - 1]? = some col → col.back? = some t →
      ∀ u p up q : (Frame.ofMountain R).Node, s.length - 1 ≤ u.1.val → Real u →
        (Frame.ofMountain R).rawParent u = some p → (Frame.ofMountain R).upper u = some up →
        (Frame.ofMountain R).Q u = some q → q.1 = p.1 →
        (Frame.ofMountain R).height u < t.row →
        (Frame.ofMountain R).height up ≠ Row.bump ((Frame.ofMountain R).height u) 0 →
        (Frame.ofMountain R).height p ≤ (Frame.ofMountain R).height u

theorem lowerSameColumn_of_lower (h : LowerParentBelowHolds) : LowerSameColumnBelowHolds :=
  fun s n R hrun M col t hM hcol ht u p up _ hx hu hraw hUp _ _ hlt hne =>
    h s n R hrun M col t hM hcol ht u p up hx hu hraw hUp hlt hne

/-- The top of the last column of `M(s)`, for a run with a new column. -/
theorem run_top {s : List Nat} {n : Nat} {R : Mountain}
    (hrun : Official.expandDiagram s n = .ok R) {X : Nat} (hX : X < R.size)
    (hx : s.length - 1 ≤ X) :
    ∃ M col t, Canonical.build s = .ok M ∧ M[M.size - 1]? = some col ∧ col.back? = some t := by
  obtain ⟨M, col, t, _, hM, hcol, ht, _⟩ := run_new_column hrun hX hx
  exact ⟨M, col, t, hM, hcol, ht⟩

/-- **`ParentBelowHolds` from its lower part.** -/
theorem parentBelowHolds_of_lower (hL : LowerParentBelowHolds) : ParentBelowHolds := by
  intro s n R hrun u p hx hu hraw
  obtain ⟨M, col, t, hM, hcol, ht⟩ := run_top hrun u.1.isLt hx
  obtain ⟨up, hUp, _⟩ := rawParent_spec hraw
  by_cases hτ : t.row ≤ (Frame.ofMountain R).height u
  · exact parentBelow_upper hrun hM hcol ht hx hu hraw hτ
  · by_cases h0 : (Frame.ofMountain R).height up =
        Row.bump ((Frame.ofMountain R).height u) 0
    · exact parentBelow_of_bump_zero hrun hx hu hraw hUp h0
    · exact hL s n R hrun M col t hM hcol ht u p up hx hu hraw hUp (lt_of_not_ge hτ) h0

/-- **`SameColumnBelowHolds` from its lower part.** -/
theorem sameColumnBelowHolds_of_lower (hL : LowerSameColumnBelowHolds) :
    SameColumnBelowHolds := by
  intro s n R hrun u p q hx hu hraw hq hcol
  obtain ⟨M, col, t, hM, hcol', ht⟩ := run_top hrun u.1.isLt hx
  obtain ⟨up, hUp, _⟩ := rawParent_spec hraw
  by_cases hτ : t.row ≤ (Frame.ofMountain R).height u
  · exact parentBelow_upper hrun hM hcol' ht hx hu hraw hτ
  · by_cases h0 : (Frame.ofMountain R).height up =
        Row.bump ((Frame.ofMountain R).height u) 0
    · exact parentBelow_of_bump_zero hrun hx hu hraw hUp h0
    · exact hL s n R hrun M col t hM hcol' ht u p up q hx hu hraw hUp hq hcol
        (lt_of_not_ge hτ) h0

/-- **`ChainHolds` from the lower same-column case and `CrossChainHolds`.** -/
theorem chainHolds_of_lowerSameColumn (hL : LowerSameColumnBelowHolds)
    (hX : CrossChainHolds) : ChainHolds :=
  chainHolds_of_sameColumn (sameColumnBelowHolds_of_lower hL) hX

/-- **`ParentBelowHolds` from the lower same-column case and `CrossChainHolds`.** -/
theorem parentBelowHolds_of_lowerSameColumn (hL : LowerSameColumnBelowHolds)
    (hX : CrossChainHolds) : ParentBelowHolds :=
  parentBelowHolds_of_sameColumn (sameColumnBelowHolds_of_lower hL) hX

end OmegaY.Official.Recon

#print axioms OmegaY.Official.Recon.parentBelowHolds_of_lower
#print axioms OmegaY.Official.Recon.chainHolds_of_lowerSameColumn
#print axioms OmegaY.Official.Recon.parentBelowHolds_of_lowerSameColumn
