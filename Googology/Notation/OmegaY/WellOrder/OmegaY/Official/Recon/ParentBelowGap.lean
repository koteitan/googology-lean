/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/ParentBelowGap.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.ChainSplit

set_option backward.do.legacy false

/-!
# `ParentBelowHolds` at one node from a gap in the column of the parent

In a new column, the stored parent `p` of the node `u⁺` above `u` is the highest node of
its column strictly below the row of `u⁺` (`rawParent_max`, `rawParent_lt_upper`). So
`row p ≤ row u` exactly when the column of `p` has no node strictly between `row u` and
`row u⁺` (`parentBelow_of_gap`).

The gap is empty when `row u⁺ = bump (row u) 0` (the next row in the same region of
level 1, `parentBelow_of_bump_zero`), since no row lies strictly between `a` and
`bump a 0`.
-/

namespace OmegaY.Official.Recon

open Canonical Expansion Geometry Frame

/-- No row lies strictly between `a` and `bump a 0`. -/
theorem Row.bump_zero_le_of_lt {a z : Row} (h : a < z) : Row.bump a 0 ≤ z :=
  (Row.bump_mono_exponent a (Nat.zero_le _)).trans (Row.bump_last_le h)

/-- The stored parent of the node above a real node of a new column is strictly below the
row of that node. -/
theorem rawParent_lt_upper {s : List Nat} {n : Nat} {R : Mountain}
    (hrun : Official.expandDiagram s n = .ok R) {u p up : (Frame.ofMountain R).Node}
    (hx : s.length - 1 ≤ u.1.val) (hu : Real u)
    (hraw : (Frame.ofMountain R).rawParent u = some p)
    (hUp : (Frame.ofMountain R).upper u = some up) :
    (Frame.ofMountain R).height p < (Frame.ofMountain R).height up := by
  obtain ⟨M, _, hMs, hI, hB⟩ := run_basic hrun
  have hF := hB.valid.toOrdered
  obtain ⟨up', hUp', hLeft⟩ := rawParent_spec hraw
  have hee : up' = up := Option.some.inj (hUp'.symm.trans hUp)
  subst hee
  obtain ⟨hc1, hc2⟩ := upper_spec hUp'
  obtain ⟨uc, ui⟩ := u
  obtain ⟨vc, vi⟩ := up'
  simp only at hc1 hc2 hx
  subst hc1
  obtain ⟨_, hN⟩ := hI.2.2 vc.val vc.isLt (by omega)
  have hcell : R[vc.val][vi.val]? = some ((Frame.ofMountain R).cell ⟨vc, vi⟩) :=
    Array.getElem?_eq_getElem vi.isLt
  have hrow : (1 : Row) < ((Frame.ofMountain R).cell ⟨vc, vi⟩).row := by
    have h1 := one_le_height hF hu
    have h2 : (Frame.ofMountain R).height ⟨vc, ui⟩ < (Frame.ofMountain R).height ⟨vc, vi⟩ :=
      hF.rows_strict vc (show ui < vi by change ui.val < vi.val; omega)
    exact lt_of_le_of_lt h1 h2
  obtain ⟨ref, q, nodes, hl, hq, hb⟩ := newCol_left_below hN hcell hrow
  have href : ref = Frame.ref p := Option.some.inj (hl.symm.trans hLeft)
  subst href
  obtain ⟨hqc, cell, hcellp, hlt⟩ := below_result hq hb
  have hq' := Array.getElem?_eq_some_iff.mp hq
  obtain ⟨hqs, hqn⟩ := hq'
  have hnodes : nodes = R[q]'(by
      have := vc.isLt
      change vc.val < R.size at this
      simp at hqs
      omega) := by
    rw [← hqn]
    simp
  have hpc : p.1.val = q := hqc
  have hcp : ((Frame.ofMountain R).cell p) = cell := by
    rw [hnodes] at hcellp
    obtain ⟨pc, pi⟩ := p
    change pc.val = q at hpc
    subst hpc
    have hpi : (Frame.ref (⟨pc, pi⟩ : (Frame.ofMountain R).Node)).index = pi.val := rfl
    rw [hpi, Array.getElem?_eq_getElem pi.isLt] at hcellp
    exact Option.some.inj hcellp
  change ((Frame.ofMountain R).cell p).row < _
  rw [hcp]
  exact hlt

/-- **`ParentBelowHolds` at `u` from a gap.** If every node of the column of the stored
parent `p` above the row of `u` is at or above the row of `u⁺`, then `row p ≤ row u`. -/
theorem parentBelow_of_gap {s : List Nat} {n : Nat} {R : Mountain}
    (hrun : Official.expandDiagram s n = .ok R) {u p up : (Frame.ofMountain R).Node}
    (hx : s.length - 1 ≤ u.1.val) (hu : Real u)
    (hraw : (Frame.ofMountain R).rawParent u = some p)
    (hUp : (Frame.ofMountain R).upper u = some up)
    (hgap : ∀ z : (Frame.ofMountain R).Node, z.1 = p.1 →
      (Frame.ofMountain R).height u < (Frame.ofMountain R).height z →
      (Frame.ofMountain R).height up ≤ (Frame.ofMountain R).height z) :
    (Frame.ofMountain R).height p ≤ (Frame.ofMountain R).height u := by
  by_contra hn
  have h1 := hgap p rfl (lt_of_not_ge hn)
  exact absurd (rawParent_lt_upper hrun hx hu hraw hUp) (not_lt.mpr h1)

/-- **The step inside a region of level 1.** If `row u⁺ = bump (row u) 0`, then
`row π(u⁺) ≤ row u`. -/
theorem parentBelow_of_bump_zero {s : List Nat} {n : Nat} {R : Mountain}
    (hrun : Official.expandDiagram s n = .ok R) {u p up : (Frame.ofMountain R).Node}
    (hx : s.length - 1 ≤ u.1.val) (hu : Real u)
    (hraw : (Frame.ofMountain R).rawParent u = some p)
    (hUp : (Frame.ofMountain R).upper u = some up)
    (h0 : (Frame.ofMountain R).height up = Row.bump ((Frame.ofMountain R).height u) 0) :
    (Frame.ofMountain R).height p ≤ (Frame.ofMountain R).height u :=
  parentBelow_of_gap hrun hx hu hraw hUp (fun _ _ hz => h0 ▸ Row.bump_zero_le_of_lt hz)

end OmegaY.Official.Recon

#print axioms OmegaY.Official.Recon.parentBelow_of_gap
#print axioms OmegaY.Official.Recon.parentBelow_of_bump_zero
