/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/ParentBelowSplit.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.ChainSplit

set_option backward.do.legacy false

/-!
# `ParentBelowHolds` only matters when the candidate is in the column of the parent

`chainHolds_of_split` (`ChainSplit.lean`) uses `ParentBelowHolds` at a node `u` only when
the candidate `Q u` lies in the column of the stored parent `p = π(u⁺)`. This file:

* states that weaker hypothesis (`SameColumnBelowHolds`) and proves `ChainHolds` from it
  and `CrossChainHolds` (`chainHolds_of_sameColumn`);
* proves `ParentBelowHolds` from the same two statements (`parentBelowHolds_of_sameColumn`),
  by strong induction on the column: when `Q u` is not in the column of `p`,
  `CrossChainHolds` gives a chain of stored parents `Q u = c₀ → c₁ → … → c → p`, all in
  columns left of `u`, and every stored-parent step there does not raise the row (the
  induction hypothesis in the new columns, the canonical search `P` in the columns of
  `M(s)`), so `row p ≤ row Q u ≤ row u`.

So the part of `ParentBelowHolds` not covered by `CrossChainHolds` is exactly
`SameColumnBelowHolds`.
-/

namespace OmegaY.Official.Recon

open Canonical Expansion Geometry Frame

/-- **`ParentBelowHolds` when the candidate is in the column of the parent.** -/
def SameColumnBelowHolds : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain), Official.expandDiagram s n = .ok R →
    ∀ u p q : (Frame.ofMountain R).Node, s.length - 1 ≤ u.1.val → Real u →
      (Frame.ofMountain R).rawParent u = some p → (Frame.ofMountain R).Q u = some q →
      q.1 = p.1 → (Frame.ofMountain R).height p ≤ (Frame.ofMountain R).height u

theorem sameColumnBelow_of_parentBelow (h : ParentBelowHolds) : SameColumnBelowHolds :=
  fun s n R hrun u p _ hx hu hraw _ _ => h s n R hrun u p hx hu hraw

/-- **`ChainHolds` from `SameColumnBelowHolds` and `CrossChainHolds`.** -/
theorem chainHolds_of_sameColumn (hS : SameColumnBelowHolds) (hX : CrossChainHolds) :
    ChainHolds := by
  intro s n R hrun u p hx hu hraw
  obtain ⟨M, _, _, _, hB⟩ := run_basic hrun
  have hF := hB.valid.toOrdered
  obtain ⟨q, hq⟩ := Q_exists_new hrun hx hu
  by_cases hcol : q.1 = p.1
  · obtain ⟨up, hUp, hmax⟩ := rawParent_max hrun hx hu hraw
    have hlt : (Frame.ofMountain R).height u < (Frame.ofMountain R).height up := by
      obtain ⟨hc1, hc2⟩ := upper_spec hUp
      obtain ⟨uc, ui⟩ := u
      obtain ⟨vc, vi⟩ := up
      simp only at hc1 hc2
      subst hc1
      exact hF.rows_strict _ (show ui < vi by change ui.val < vi.val; omega)
    have he := Q_eq_of_same_column hF hq hcol (hS s n R hrun u p q hx hu hraw hq hcol)
      (fun z hz hzu => hmax z hz (lt_of_le_of_lt hzu hlt))
    subst he
    exact ⟨q, hq, .here q⟩
  · obtain ⟨c, hc, hcp, hv⟩ := hX s n R hrun u p q hx hu hraw hq hcol
    exact chainOK_of_rawChain hB.valid hB.sums hu hq hc hcp hv

/-! ## Rows along chains of stored parents -/

/-- A chain of stored parents from a real node left of column `C` does not raise the row,
if no stored-parent step left of `C` does. -/
theorem RawChain.height_le_of {R : Mountain} (hV : MountainValid R) (hS : MountainSums R)
    {C : Nat}
    (hstep : ∀ a b : (Frame.ofMountain R).Node, a.1.val < C → Real a →
      (Frame.ofMountain R).rawParent a = some b →
      (Frame.ofMountain R).height b ≤ (Frame.ofMountain R).height a)
    {a c : (Frame.ofMountain R).Node} (h : RawChain (Frame.ofMountain R) a c) :
    a.1.val < C → Real a →
      Real c ∧ c.1.val < C ∧ (Frame.ofMountain R).height c ≤ (Frame.ofMountain R).height a := by
  induction h with
  | here c => exact fun hc hr => ⟨hr, hc, le_rfl⟩
  | @step a b p hraw _ ih =>
    intro ha hr
    have hbcol : b.1.val < a.1.val := rawParent_column_lt hV.toOrdered hraw
    obtain ⟨hb, _⟩ := rawParent_step hV hS hr hraw
    obtain ⟨hp, hpC, hle⟩ := ih (by omega) hb
    exact ⟨hp, hpC, hle.trans (hstep a b ha hr hraw)⟩

/-- In the columns of `M(s)` (left of `x₀`), a stored-parent step does not raise the row:
the stored parent is the canonical parent `P`. -/
theorem prefix_rawParent_height {s : List Nat} {n : Nat} {R : Mountain}
    (hrun : Official.expandDiagram s n = .ok R) {a b : (Frame.ofMountain R).Node}
    (ha : a.1.val < s.length - 1) (hr : Real a)
    (hraw : (Frame.ofMountain R).rawParent a = some b) :
    (Frame.ofMountain R).height b ≤ (Frame.ofMountain R).height a := by
  obtain ⟨M, hM, hMs, hI, hB⟩ := run_basic hrun
  have hG := prefix_geometry hM hI a.1.val a.1.isLt (by omega)
  have hP := P_of_columnGeometry hB.valid hG hr hraw
  exact P_height_le hB.valid.toOrdered hP

/-- **`ParentBelowHolds` from `SameColumnBelowHolds` and `CrossChainHolds`.** -/
theorem parentBelowHolds_of_sameColumn (hS : SameColumnBelowHolds) (hX : CrossChainHolds) :
    ParentBelowHolds := by
  intro s n R hrun
  obtain ⟨M, _, _, _, hB⟩ := run_basic hrun
  have hF := hB.valid.toOrdered
  -- every stored-parent step of a real node does not raise the row
  suffices hall : ∀ C, ∀ a b : (Frame.ofMountain R).Node, a.1.val < C → Real a →
      (Frame.ofMountain R).rawParent a = some b →
      (Frame.ofMountain R).height b ≤ (Frame.ofMountain R).height a by
    intro u p _ hu hraw
    exact hall (u.1.val + 1) u p (by omega) hu hraw
  intro C
  induction C with
  | zero => intro a b ha; omega
  | succ C ih =>
    intro u p hC hu hraw
    by_cases hlt : u.1.val < C
    · exact ih u p hlt hu hraw
    by_cases hx : u.1.val < s.length - 1
    · exact prefix_rawParent_height hrun hx hu hraw
    have hx' : s.length - 1 ≤ u.1.val := by omega
    obtain ⟨q, hq⟩ := Q_exists_new hrun hx' hu
    by_cases hcol : q.1 = p.1
    · exact hS s n R hrun u p q hx' hu hraw hq hcol
    · obtain ⟨c, hc, hcp, _⟩ := hX s n R hrun u p q hx' hu hraw hq hcol
      have hqcol : q.1.val < C := by have := Q_column_lt hF hq; omega
      have hqr : Real q := Q_real hF hu hq
      obtain ⟨hcr, hcC, hcq⟩ := hc.height_le_of hB.valid hB.sums
        (fun a b ha hr hr' => ih a b ha hr hr') hqcol hqr
      exact ((ih c p hcC hcr hcp).trans hcq).trans (Q_height_le hF hq)

end OmegaY.Official.Recon

#print axioms OmegaY.Official.Recon.chainHolds_of_sameColumn
#print axioms OmegaY.Official.Recon.parentBelowHolds_of_sameColumn
