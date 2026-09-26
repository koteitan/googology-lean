/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/Markers.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/Markers.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.WeakGeometry
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.LoopTotality

set_option backward.do.legacy false

/-! Totality of the actual three nested finite loops in `markers`. -/

namespace OmegaY.Expansion

open Canonical

@[simp] private theorem bind_ok {α β : Type} (a : α) (f : α → Result β) :
    (Except.ok a >>= f) = f a := rfl
@[simp] private theorem pure_eq {α : Type} (a : α) :
    (pure a : Result α) = Except.ok a := rfl

theorem ValidRef.lookup_below_index {mountain : Mountain} {ref : Ref}
    (hv : ValidRef mountain ref) {index : Nat} (hi : index ≤ ref.index) :
    ∃ cell, lookup mountain ⟨ref.column, index⟩ = .ok cell := by
  obtain ⟨cell, column, hc, hcell⟩ := hv
  obtain ⟨hib, _⟩ := Array.getElem?_eq_some_iff.mp hcell
  have hindex : index < column.size := by omega
  exact ⟨column[index], lookup_ok_iff.mpr
    ⟨column, hc, Array.getElem?_eq_getElem hindex⟩⟩

/-- Each lookup is over an existing array prefix and each weak search uses its
proved structural allowance. No success premise for `markers` is assumed. -/
theorem markers_total {mountain : Mountain} (hlocal : WeakLocal mountain)
    {root : Ref} (hroot : ValidRef mountain root) :
    Succeeds (markers mountain root) := by
  unfold markers
  apply succeeds_bind
  · apply succeeds_forIn
    intro rootIndex hri state
    have hri' : rootIndex ≤ root.index := by
      have h := List.mem_range.mp (List.mem_reverse.mp hri)
      omega
    obtain ⟨rootCell, hrootCell⟩ := hroot.lookup_below_index hri'
    dsimp only
    rw [hrootCell]
    simp only [bind_ok]
    apply succeeds_bind
    · apply succeeds_forIn
      intro column hcol state
      have hcb : column < mountain.size := List.mem_range.mp hcol
      by_cases hright : root.column < column
      · simp only [hright, ↓reduceIte]
        have hc := Array.getElem?_eq_getElem hcb
        have hnodes : columnAt mountain column = .ok mountain[column] := by
          simp [columnAt, hc]
        rw [hnodes]
        simp only [bind_ok]
        apply succeeds_bind
        · apply succeeds_forIn
          intro index hindex state
          have hib : index < mountain[column].size := List.mem_range.mp hindex
          have hat : CellAt mountain ⟨column, index⟩ mountain[column][index] :=
            ⟨mountain[column], hc, Array.getElem?_eq_getElem hib⟩
          have hcell := lookup_ok_iff.mpr hat
          rw [hcell]
          simp only [bind_ok]
          by_cases hrow : mountain[column][index].row = rootCell.row
          · simp only [hrow, ↓reduceIte]
            apply succeeds_bind
            · exact weakReaches_total hlocal ⟨_, hat⟩ (Nat.lt_succ_self column)
            · intro found
              cases found <;> exact succeeds_pure _
          · simp only [hrow, ↓reduceIte]
            exact succeeds_pure _
        · intro result
          exact succeeds_pure _
      · simp only [hright, ↓reduceIte]
        exact succeeds_pure _
    · intro result
      exact succeeds_pure _
  · intro result
    exact succeeds_pure _

theorem markers_total_ordered {mountain : Mountain}
    (hF : (Geometry.Frame.ofMountain mountain).Ordered)
    (hleft : ∀ u : (Geometry.Frame.ofMountain mountain).Node,
      Geometry.Frame.Real u → 0 < u.1.val →
      ∃ r, ((Geometry.Frame.ofMountain mountain).cell u).left = some r)
    (root : (Geometry.Frame.ofMountain mountain).Node) :
    ∃ result, markers mountain (Geometry.Frame.ref root) = .ok result :=
  markers_total (weakLocal_of_ordered hF hleft) ⟨_, frame_ref_cellAt mountain root⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.markers_total
#print axioms OmegaY.Expansion.markers_total_ordered
