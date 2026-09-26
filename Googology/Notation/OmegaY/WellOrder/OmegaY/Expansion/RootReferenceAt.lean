/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/RootReferenceAt.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/RootReferenceAt.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.RootPartition
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ReferencePartition

set_option backward.do.legacy false

/-! Exact referenceAt heights for actual root rows and prepared markers.
The source of every interval is the original root column; the selected
height is an actual cell of the decremented final column. -/

namespace OmegaY.Expansion

open Canonical Geometry

theorem Preparation.reduced_root_prefix_read {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {nodes : Column}
    (hColumn : p.initial[p.root.column]? = some nodes)
    {index : Nat} {lower : Cell} (hLower : nodes[index]? = some lower)
    (hIndex : index ≤ p.root.index) :
    ∃ ref cell, Canonical.cellAt p.reduced ref = .ok cell ∧
      ref.column = p.reduced.size - 1 ∧ cell.row = lower.row := by
  have hs := build_size p.reduced_build
  have hLastColumn : front.length = p.reduced.size - 1 := by
    simp only [List.length_append, List.length_singleton] at hs
    omega
  by_cases hi : index = 0
  · subst index
    obtain ⟨hc, hNodes⟩ := Array.getElem?_eq_some_iff.mp hColumn
    have hPhantom : nodes[0]? = some phantom := by
      rw [← hNodes]
      exact (p.initial_valid p.root.column hc).phantom
    have hLowerEq : lower = phantom := Option.some.inj (hLower.symm.trans hPhantom)
    exact ⟨⟨front.length, 0⟩, phantom, p.reduced_last_phantom_read,
      hLastColumn, congrArg Cell.row hLowerEq.symm⟩
  · have hRead : Canonical.cellAt p.initial ⟨p.root.column, index⟩ = .ok lower :=
      cellAt_ok_iff.mpr ⟨nodes, hColumn, hLower⟩
    obtain ⟨w, hRef, hCell⟩ := Canonical.frame_node_of_cellAt hRead
    have hReal : Frame.Real w := by
      have hh := congrArg Ref.index hRef
      unfold Frame.Real
      dsimp only [Frame.ref] at hh
      omega
    have hHeight : (Frame.ofMountain p.initial).height w = lower.row := congrArg Cell.row hCell
    have hColumnEq : w.1.val = p.root.column := congrArg Ref.column hRef
    obtain ⟨v, _, hvColumn, hvRow⟩ := p.reduced_root_row_support hLast w hReal hColumnEq
      (hHeight.trans_le (p.root_prefix_row_le hColumn hLower hIndex))
    exact ⟨Frame.ref v, (Frame.ofMountain p.reduced).cell v,
      cellAt_of_frame_node p.reduced v, hvColumn.trans hLastColumn, hvRow.trans hHeight⟩

/-- The actual selector chooses the reference belonging to this precise
single-power interval; later references are all too low to qualify. -/
theorem Preparation.initial_referenceAt_root_interval {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {nodes : Column}
    (hColumn : p.initial[p.root.column]? = some nodes)
    {index : Nat} {lower : Cell} (hLower : nodes[index]? = some lower)
    (hIndex : index ≤ p.root.index) {references : List Ref}
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references) :
    ∃ ceiling degree ref cell,
      ceiling = Row.bump lower.row degree ∧ ceiling ≤ p.lastTop.row ∧
      below p.reduced (p.reduced.size - 1) ceiling = .ok ref ∧
      Canonical.cellAt p.reduced ref = .ok cell ∧
      referenceAt p.reduced references lower.row = .ok cell.row ∧
      lower.row ≤ cell.row ∧ cell.row < ceiling ∧
      ∀ higherIndex higherCell, index < higherIndex → higherIndex ≤ p.root.index →
        nodes[higherIndex]? = some higherCell → ceiling ≤ higherCell.row := by
  obtain ⟨earlier, ceiling, later, degree, hPartition, hPower, hTop, hLater, hHigher⟩ :=
    p.root_boundary_partition hLast hColumn hLower hIndex
  obtain ⟨floorRef, floorCell, hFloor, hFloorColumn, hFloorRow⟩ :=
    p.reduced_root_prefix_read hLast hColumn hLower hIndex
  have hBelow : floorCell.row < ceiling := by
    rw [hFloorRow, hPower]
    exact Row.lt_bump _ _
  obtain ⟨ref, cell, hSelected, hRead, _, hAbove, hUpper⟩ :=
    below_between p.reduced_valid hFloor hBelow
  rw [hFloorColumn] at hSelected
  rw [hFloorRow] at hAbove
  have hReference := referenceAt_of_boundary_partition
    (Array.getElem?_eq_getElem p.reduced_last_exists) hPartition hMap hSelected
    (lookup_ok_iff.mpr (cellAt_ok_iff.mp hRead)) hAbove hLater
  exact ⟨ceiling, degree, ref, cell, hPower, hTop, hSelected, hRead,
    hReference, hAbove, hUpper, hHigher⟩

/-- Every actual prepared marker inherits a root-prefix row. The original
root-column read is preserved across decrement and gives its power scale. -/
theorem Preparation.marker_root_prefix_read {front : List Nat} {last : Nat}
    (p : Preparation front last) {bucket : Nat} {marker : Ref} {cell : Cell}
    (hMarker : BucketMem p.marked bucket marker)
    (hCell : Canonical.cellAt p.reduced marker = .ok cell) :
    ∃ nodes index lower, p.initial[p.root.column]? = some nodes ∧
      nodes[index]? = some lower ∧ index ≤ p.root.index ∧ lower.row = cell.row := by
  have hRoot : CellAt p.reduced p.root p.rootCell := cellAt_ok_iff.mp p.restored_root
  have hSpec := markers_member_sound
    (weakLocal_of_ordered p.reduced_valid.toOrdered p.reduced_valid.left_sources)
    ⟨p.rootCell, hRoot⟩ p.markers_built hMarker
  obtain ⟨_, _, _, index, hIndex, hPath⟩ := hSpec
  obtain ⟨lower, hLower⟩ :=
    (show ValidRef p.reduced p.root from ⟨p.rootCell, hRoot⟩).lookup_below_index hIndex
  have hLowerRead : Canonical.cellAt p.reduced ⟨p.root.column, index⟩ = .ok lower :=
    cellAt_ok_iff.mpr (lookup_ok_iff.mp hLower)
  have hOldRead : Canonical.cellAt p.initial ⟨p.root.column, index⟩ = .ok lower :=
    (build_changed_last_preserves_ref (ref := ⟨p.root.column, index⟩)
      p.initial_build p.reduced_build p.root_before_last).trans hLowerRead
  obtain ⟨nodes, hColumn, hIndexRead⟩ := cellAt_ok_iff.mp hOldRead
  exact ⟨nodes, index, lower, hColumn, hIndexRead, hIndex,
    (hPath.row_eq (lookup_ok_iff.mp hLower) (cellAt_ok_iff.mp hCell)).symm⟩

/-- The interval control now applies to the markers actually enumerated
by the program, with no independently chosen marker or target hypothesis. -/
theorem Preparation.initial_marker_reference_interval {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {references : List Ref}
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
    {bucket : Nat} {marker : Ref} (hMarker : BucketMem p.marked bucket marker) :
    ∃ sourceCell target ceiling degree,
      Canonical.cellAt p.reduced marker = .ok sourceCell ∧
      referenceAt p.reduced references sourceCell.row = .ok target ∧
      sourceCell.row ≤ target ∧ target < ceiling ∧
      ceiling = Row.bump sourceCell.row degree ∧ ceiling ≤ p.lastTop.row := by
  obtain ⟨cell, hCell, _⟩ := p.marker_cell_row_bound hMarker
  obtain ⟨nodes, index, lower, hColumn, hLower, hIndex, hRow⟩ :=
    p.marker_root_prefix_read hMarker hCell
  obtain ⟨ceiling, degree, _, targetCell, hPower, hTop, _, _, hTarget, hAbove, hUpper, _⟩ :=
    p.initial_referenceAt_root_interval hLast hColumn hLower hIndex hMap
  exact ⟨cell, targetCell.row, ceiling, degree, hCell,
    by simpa only [hRow] using hTarget,
    by simpa only [hRow] using hAbove, hUpper,
    by simpa only [hRow] using hPower, hTop⟩

/-- A higher actual marker is at or above this marker's selected interval
ceiling. It need not be on the immediately adjacent root row. -/
theorem Preparation.initial_marker_reference_below {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {references : List Ref}
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
    {bucket nextBucket : Nat} {marker nextMarker : Ref} {sourceCell nextCell : Cell}
    (hMarker : BucketMem p.marked bucket marker)
    (hSource : Canonical.cellAt p.reduced marker = .ok sourceCell)
    (hNextMarker : BucketMem p.marked nextBucket nextMarker)
    (hNext : Canonical.cellAt p.reduced nextMarker = .ok nextCell)
    (hStrict : sourceCell.row < nextCell.row) :
    ∃ target ceiling degree,
      referenceAt p.reduced references sourceCell.row = .ok target ∧
      sourceCell.row ≤ target ∧ target < ceiling ∧
      ceiling = Row.bump sourceCell.row degree ∧ ceiling ≤ nextCell.row := by
  obtain ⟨nodes, index, lower, hColumn, hLower, hIndex, hRow⟩ :=
    p.marker_root_prefix_read hMarker hSource
  obtain ⟨otherNodes, higherIndex, higherCell, hOtherColumn, hHigherRead, hHigherIndex, hHigherRow⟩ :=
    p.marker_root_prefix_read hNextMarker hNext
  have he : otherNodes = nodes := Option.some.inj (hOtherColumn.symm.trans hColumn)
  subst otherNodes
  have hRootStrict : lower.row < higherCell.row := by simpa only [hRow, hHigherRow] using hStrict
  have hIndexLt : index < higherIndex :=
    (cellAt_row_lt_iff p.initial_valid.toOrdered
      (show CellAt p.initial ⟨p.root.column, index⟩ lower from ⟨nodes, hColumn, hLower⟩)
      (show CellAt p.initial ⟨p.root.column, higherIndex⟩ higherCell from ⟨nodes, hColumn, hHigherRead⟩)
      rfl).mp hRootStrict
  obtain ⟨ceiling, degree, _, targetCell, hPower, _, _, _, hTarget, hAbove, hUpper, hHigher⟩ :=
    p.initial_referenceAt_root_interval hLast hColumn hLower hIndex hMap
  refine ⟨targetCell.row, ceiling, degree, ?_, ?_, hUpper, ?_, ?_⟩
  · simpa only [hRow] using hTarget
  · simpa only [hRow] using hAbove
  · simpa only [hRow] using hPower
  · simpa only [hHigherRow] using hHigher higherIndex higherCell hIndexLt hHigherIndex hHigherRead

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.initial_referenceAt_root_interval
#print axioms OmegaY.Expansion.Preparation.initial_marker_reference_interval
#print axioms OmegaY.Expansion.Preparation.initial_marker_reference_below
