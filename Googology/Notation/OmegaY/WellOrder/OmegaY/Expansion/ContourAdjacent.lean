/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ContourAdjacent.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/ContourAdjacent.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.FillAdjacent
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.SourcePartition

set_option backward.do.legacy false

/-!
# Actual contour adjacency survives the whole copy and finish

These witnesses are about the returned array, not only a row set or a power
law. A source pair visited consecutively by the contour gives consecutive
output rows at their common interval lift. No output normality is assumed.
-/

namespace OmegaY.Expansion

open Canonical

theorem cell_read_of_row_read {cells : List Cell} {index : Nat} {row : Row}
    (h : (cells.map Cell.row)[index]? = some row) :
    ∃ cell, cells[index]? = some cell ∧ cell.row = row := by
  simp only [List.getElem?_map] at h
  cases hr : cells[index]? with
  | none => simp [hr] at h
  | some cell => exact ⟨cell, rfl, by simpa only [hr, Option.map_some, Option.some.injEq] using h⟩

private theorem contour_pair_suffix {nodes : Column} {index : Nat} {first : Cell}
    {rest : List Cell} (hRest : nodes.toList.drop (index + 1) = first :: rest) :
    nodes[index + 1]? = some first ∧ nodes.toList.drop ((index + 1) + 1) = rest := by
  constructor
  · simpa only [List.head?_drop, Array.getElem?_toList, List.head?_cons]
      using congrArg List.head? hRest
  · simpa only [List.tail_drop, List.tail_cons] using congrArg List.tail hRest

/-- No marker or value-one stop can interrupt a pair of consecutive source
nodes before the next marked index. The returned index is in the actual
visited source list, not a synthetic row interpolation. -/
theorem contourSourceCells_pair_of_no_between {nodes : Column}
    (hNoPremature : NoPrematureOne nodes) (markerIndices : List Nat)
    {index sourceIndex : Nat} {current lower upper : Cell}
    (hCurrent : nodes[index]? = some current)
    (hLower : nodes[sourceIndex]? = some lower)
    (hUpper : nodes[sourceIndex + 1]? = some upper) (hIndex : index < sourceIndex)
    (hNoBetween : ∀ middle, index < middle → middle ≤ sourceIndex + 1 → middle ∉ markerIndices)
    {rest : List Cell} (hRest : nodes.toList.drop (index + 1) = rest) :
    ∃ position, (contourSourceCells markerIndices index current rest)[position]? = some lower ∧
      (contourSourceCells markerIndices index current rest)[position + 1]? = some upper := by
  induction rest generalizing index current with
  | nil =>
    have hSize : nodes.size ≤ index + 1 := by
      simpa only [Array.length_toList] using List.drop_eq_nil_iff.mp hRest
    have hBound := (Array.getElem?_eq_some_iff.mp hUpper).1
    omega
  | cons first rest ih =>
    obtain ⟨hFirst, hTail⟩ := contour_pair_suffix hRest
    have hNoStop : ¬ (current.value = 1 ∨ index + 1 ∈ markerIndices) :=
      not_or.mpr ⟨hNoPremature index current first hCurrent hFirst,
        hNoBetween (index + 1) (by omega) (by omega)⟩
    rw [contourSourceCells, if_neg hNoStop]
    by_cases he : index + 1 = sourceIndex
    · have hFirstEq : first = lower := Option.some.inj
        (hFirst.symm.trans (by simpa only [he] using hLower))
      subst first
      have hLowerStop : ¬ (lower.value = 1 ∨ (index + 1) + 1 ∈ markerIndices) :=
        not_or.mpr ⟨by simpa only [he] using hNoPremature sourceIndex lower upper hLower hUpper,
          hNoBetween ((index + 1) + 1) (by omega) (by omega)⟩
      cases rest with
      | nil =>
        have hSize : nodes.size ≤ (index + 1) + 1 := by
          simpa only [Array.length_toList] using List.drop_eq_nil_iff.mp hTail
        have hBound := (Array.getElem?_eq_some_iff.mp hUpper).1
        omega
      | cons second rest =>
        obtain ⟨hSecond, _⟩ := contour_pair_suffix hTail
        have hSecondEq : second = upper := Option.some.inj
          (hSecond.symm.trans (by simpa only [he] using hUpper))
        subst second
        exact ⟨0, rfl, by simp only [contourSourceCells, hLowerStop, ↓reduceIte,
          List.getElem?_cons_zero, List.getElem?_cons_succ]⟩
    · obtain ⟨position, hLo, hHi⟩ := ih hFirst (by omega)
        (fun middle hlo hhi => hNoBetween middle (by omega) hhi) hTail
      exact ⟨position + 1, by simpa only [List.getElem?_cons_succ] using hLo,
        by simpa only [List.getElem?_cons_succ] using hHi⟩

namespace ColumnCopyData

variable {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
  {sourceColumn shift rootColumn : Nat}
  (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)
  (hParentPower : ∀ marker (hm : marker ∈ d.bucket),
    ColumnPowerSteps (d.marker_data marker hm).parentNodes)
  (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (index : Nat) (cell : Cell),
    (d.marker_data marker hm).parentNodes[index]? = some cell ∧
      cell.row = (d.marker_data marker hm).current.row)
  (hNoPremature : NoPrematureOne d.sources)

include hParentPower hParentLow hNoPremature

theorem contour_splice_in_candidates {marker : Ref} (hm : marker ∈ d.bucket) :
    ∃ path before after,
      contour mountain sourceColumn (d.bucket.map Ref.index) shift rootColumn marker.index
        (d.marker_data marker hm).targetCell.row (d.marker_data marker hm).current
        (d.sources.toList.drop (marker.index + 1)) = .ok path ∧
      finishSort d.candidates = before ++ path ++ after := by
  let s := d.marker_data marker hm
  obtain ⟨lowIndex, lowCell, hLowRead, hLowRow⟩ := hParentLow marker hm
  obtain ⟨copied, path, _, hPath, hSegment⟩ := copySegment_sorted_splice d.ambient_valid d.source_column
    d.source_nonzero d.destination.le d.source_top (d.bucket.map Ref.index) s
    (hParentPower marker hm) hLowRead hLowRow (d.segment_run hm)
  obtain ⟨before, after, hSplit⟩ := List.append_of_mem (List.mem_reverse.mpr hm)
  let sortedSegment := fun entry => finishSort (d.segment entry)
  refine ⟨path, before.flatMap sortedSegment ++ [copied] ++
    fillCellsAscending s.parentNodes (s.sourceParent.column + shift) s.current.row s.targetCell.row,
    after.flatMap sortedSegment, hPath, ?_⟩
  rw [d.finishSort_candidates_cells hParentPower hParentLow hNoPremature]
  simp only [ascendingCells, hSplit, List.flatMap_append, List.flatMap_cons]
  rw [hSegment]
  simp only [List.append_assoc, sortedSegment, s]

theorem copyColumn_contour_adjacent {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {marker : Ref} (hm : marker ∈ d.bucket) {index : Nat} {oldLower oldUpper : Cell}
    (hLower : (contourSourceCells (d.bucket.map Ref.index) marker.index
      (d.marker_data marker hm).current (d.sources.toList.drop (marker.index + 1)))[index]? = some oldLower)
    (hUpper : (contourSourceCells (d.bucket.map Ref.index) marker.index
      (d.marker_data marker hm).current (d.sources.toList.drop (marker.index + 1)))[index + 1]? = some oldUpper) :
    ∃ (position : Nat) (lower upper : Cell),
      column[position]? = some lower ∧ column[position + 1]? = some upper ∧
      lower.row = Row.lift (d.marker_data marker hm).current.row
        (d.marker_data marker hm).targetCell.row oldLower.row ∧
      upper.row = Row.lift (d.marker_data marker hm).current.row
        (d.marker_data marker hm).targetCell.row oldUpper.row := by
  let s := d.marker_data marker hm
  obtain ⟨path, before, after, hPath, hSplit⟩ :=
    d.contour_splice_in_candidates hParentPower hParentLow hNoPremature hm
  have hRows := contour_rows_eq_lift_of_success d.ambient_valid d.source_column d.source_nonzero
    d.destination.le d.source_top d.source_power (d.bucket.map Ref.index)
    s.targetCell.row s.current_at rfl hPath
  have hLowerRow : (path.map Cell.row)[index]? = some (Row.lift s.current.row s.targetCell.row oldLower.row) := by
    rw [hRows]
    simp only [List.getElem?_map, hLower, Option.map_some, s]
  have hUpperRow : (path.map Cell.row)[index + 1]? = some (Row.lift s.current.row s.targetCell.row oldUpper.row) := by
    rw [hRows]
    simp only [List.getElem?_map, hUpper, Option.map_some, s]
  obtain ⟨copiedLower, hCopiedLower, hCopiedLowerRow⟩ := cell_read_of_row_read hLowerRow
  obtain ⟨copiedUpper, hCopiedUpper, hCopiedUpperRow⟩ := cell_read_of_row_read hUpperRow
  obtain ⟨lower, upper, hLowerOut, hUpperOut, hLowerShape, hUpperShape⟩ :=
    finish_adjacent_of_splice (d.copyColumn_eq_finish.symm.trans hRun) hSplit hCopiedLower hCopiedUpper
  exact ⟨before.length + index, lower, upper, hLowerOut, hUpperOut,
    hLowerShape.1.symm.trans hCopiedLowerRow, hUpperShape.1.symm.trans hCopiedUpperRow⟩

theorem copyColumn_source_adjacent_of_no_between {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {marker : Ref} (hm : marker ∈ d.bucket) {sourceIndex : Nat} {oldLower oldUpper : Cell}
    (hLower : d.sources[sourceIndex]? = some oldLower)
    (hUpper : d.sources[sourceIndex + 1]? = some oldUpper)
    (hAfter : marker.index < sourceIndex)
    (hNoBetween : ∀ middle, marker.index < middle → middle ≤ sourceIndex + 1 →
      middle ∉ d.bucket.map Ref.index) :
    ∃ (position : Nat) (lower upper : Cell),
      column[position]? = some lower ∧ column[position + 1]? = some upper ∧
      lower.row = Row.lift (d.marker_data marker hm).current.row
        (d.marker_data marker hm).targetCell.row oldLower.row ∧
      upper.row = Row.lift (d.marker_data marker hm).current.row
        (d.marker_data marker hm).targetCell.row oldUpper.row := by
  obtain ⟨position, hLo, hHi⟩ := contourSourceCells_pair_of_no_between hNoPremature
    (d.bucket.map Ref.index) (d.marker_data marker hm).current_at hLower hUpper hAfter hNoBetween rfl
  exact d.copyColumn_contour_adjacent hParentPower hParentLow hNoPremature hRun hm hLo hHi

end ColumnCopyData

#print axioms ColumnCopyData.contour_splice_in_candidates
#print axioms ColumnCopyData.copyColumn_contour_adjacent
#print axioms contourSourceCells_pair_of_no_between
#print axioms ColumnCopyData.copyColumn_source_adjacent_of_no_between

end OmegaY.Expansion
