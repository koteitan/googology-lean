/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Canonical/GraftTransfer.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Canonical/GraftTransfer.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.GraftSuffix

set_option backward.do.legacy false

/-!
# Reproducing an old suffix over a different left prefix

Only columns strictly before the old source column are needed.  In particular
the new column may occupy the old source column's index: the new left prefix
need not contain that source column.  The source diagram remains fixed during
the proof; its Normal certificate is never required of the new partial graph.
-/

namespace OmegaY.Canonical

open Geometry

private theorem transfer_cell_eq {a b : Cell}
    (hr : a.row = b.row) (hv : a.value = b.value) (hl : a.left = b.left) : a = b := by
  cases a
  cases b
  simp_all

theorem graft_next_cell_transfer {before left : Mountain}
    (hNormal : (Frame.ofMountain before).Normal)
    {u v : (Frame.ofMountain before).Node} (hReal : Frame.Real u)
    (hUpper : (Frame.ofMountain before).upper u = some v)
    {target : Column} (hTop : target.back? = some ((Frame.ofMountain before).cell u))
    (hRight : u.1.val ≤ left.size)
    (hColumns : ∀ c, c < u.1.val → before[c]? = left[c]?) :
    ∃ p : (Frame.ofMountain before).Node,
      findParent (left.push target) ⟨left.size, target.size - 1⟩ = .ok (Frame.ref p) ∧
      cellAt (left.push target) (Frame.ref p) = .ok ((Frame.ofMountain before).cell p) ∧
      (⟨Row.B ((Frame.ofMountain before).height u) ((Frame.ofMountain before).height p),
        (Frame.ofMountain before).value u - (Frame.ofMountain before).value p,
        some (Frame.ref p)⟩ : Cell) = (Frame.ofMountain before).cell v := by
  obtain ⟨p, hParent, hRow, hValue, hLeft⟩ := hNormal.upper_step u v hReal hUpper
  have hOld : findParent before (Frame.ref u) = .ok (Frame.ref p) :=
    (Executable.findParent_ref_iff hNormal.toOrdered u p).mpr hParent
  have hPrefix : ∀ c, c < u.1.val → before[c]? = (left.push target)[c]? := by
    intro c hc
    have hcl : c < left.size := lt_of_lt_of_le hc hRight
    rw [Array.getElem?_push, if_neg (Nat.ne_of_lt hcl)]
    exact hColumns c hc
  have hMoved := findParent_success_of_same_cell (cellAt_of_frame_node before u)
    (cellAt_current_top hTop) hRight hPrefix hOld
  refine ⟨p, hMoved, ?_, ?_⟩
  · have hpLeft := Frame.P_column_lt hNormal.toOrdered hParent
    have hRead := cellAt_eq_of_column_eq (ref := Frame.ref p) (hPrefix p.1.val hpLeft)
    exact hRead.symm.trans (cellAt_of_frame_node before p)
  · exact transfer_cell_eq hRow.symm hValue.symm hLeft.symm

/-- The target top may be in the old source's column or any later column.
Nothing is assumed about its lower cells or about columns after the retained
strict prefix.  The result contains exactly the full old upper-cell suffix. -/
theorem growColumn_graft_transfer {before left : Mountain}
    (hNormal : (Frame.ofMountain before).Normal) {fuel : Nat}
    {u : (Frame.ofMountain before).Node} (hReal : Frame.Real u) {target : Column}
    (hTop : target.back? = some ((Frame.ofMountain before).cell u))
    (hRight : u.1.val ≤ left.size)
    (hColumns : ∀ c, c < u.1.val → before[c]? = left[c]?)
    (hEnough : (Frame.ofMountain before).value u - 1 ≤ fuel) :
    ∃ result, growColumn left fuel target = .ok result ∧
      result.toList = target.toList ++ upperSuffix before u ∧ TopOne result := by
  induction fuel generalizing u target with
  | zero =>
      have hPositive := hNormal.real_positive u hReal
      have hOne : (Frame.ofMountain before).value u = 1 := by omega
      refine ⟨target, growColumn_top _ hTop hOne, ?_, _, hTop, hOne⟩
      simp only [upperSuffix_of_value_one hNormal hReal hOne, List.append_nil]
  | succ fuel ih =>
      by_cases hOne : (Frame.ofMountain before).value u = 1
      · refine ⟨target, growColumn_top _ hTop hOne, ?_, _, hTop, hOne⟩
        simp only [upperSuffix_of_value_one hNormal hReal hOne, List.append_nil]
      · have hPositive := hNormal.real_positive u hReal
        have hLarge : 1 < (Frame.ofMountain before).value u := by omega
        have hZero : (Frame.ofMountain before).value u ≠ 0 := by omega
        obtain ⟨v, hUpper⟩ := hNormal.upper_exists u hReal hLarge
        obtain ⟨p, hFind, hRead, hNext⟩ :=
          graft_next_cell_transfer hNormal hReal hUpper hTop hRight hColumns
        have hBounds := difference_value_bounds hTop hFind hRead
        have hV : (Frame.ofMountain before).value v =
            (Frame.ofMountain before).value u - (Frame.ofMountain before).value p :=
          (congrArg Cell.value hNext).symm
        have hDecrease : (Frame.ofMountain before).value v <
            (Frame.ofMountain before).value u := by
          rw [hV]
          exact hBounds.2
        have hVReal : Frame.Real v := by
          unfold Frame.Real
          rw [(Frame.upper_spec hUpper).2]
          omega
        have hSameColumn : v.1.val = u.1.val := congrArg Fin.val (Frame.upper_spec hUpper).1
        have hVRight : v.1.val ≤ left.size := hSameColumn ▸ hRight
        have hVColumns : ∀ c, c < v.1.val → before[c]? = left[c]? := by
          intro c hc
          exact hColumns c (by simpa only [hSameColumn] using hc)
        obtain ⟨result, hRun, hList, hFinalTop⟩ := ih hVReal
          (target := target.push ((Frame.ofMountain before).cell v))
          Array.back?_push hVRight hVColumns (by omega)
        refine ⟨result, ?_, ?_, hFinalTop⟩
        · rw [growColumn_step fuel hTop hOne hZero]
          simp only [hFind, hRead, except_bind_ok]
          simp only [Frame.height, Frame.value] at hNext
          rw [hNext]
          exact hRun
        · rw [upperSuffix_of_upper hUpper]
          simpa only [Array.toList_push, List.append_assoc, List.singleton_append] using hList

end OmegaY.Canonical

#print axioms OmegaY.Canonical.graft_next_cell_transfer
#print axioms OmegaY.Canonical.growColumn_graft_transfer
