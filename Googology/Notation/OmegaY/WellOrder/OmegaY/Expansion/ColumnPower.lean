/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ColumnPower.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/ColumnPower.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ColumnCopyData
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.SegmentPower
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ContourSeam
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.PowerSegments

set_option backward.do.legacy false

/-!
# Power steps and reference endpoints of a completed copied column

Each segment has an ascending power-step presentation. Consecutive source
markers supply the exact missing seam, rather than merely a strict row
inequality. Reversing the descending marker bucket orders whole segments;
each individual segment is sorted separately. The resulting presentation
is a permutation of the actual candidates used by the unchanged copier.
-/

namespace OmegaY.Expansion.ColumnCopyData

open Canonical

variable {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
  {sourceColumn shift rootColumn : Nat}
  (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)

def sortedSegmentRows (marker : Ref) : List Row :=
  (finishSort (d.segment marker)).map Cell.row

def ascendingRows : List Row := d.bucket.reverse.flatMap d.sortedSegmentRows

theorem ascendingRows_perm : d.ascendingRows.Perm (d.candidates.map Cell.row) := by
  rw [ascendingRows, candidates, List.map_flatMap]
  apply (List.reverse_perm d.bucket).flatMap
  intro marker _
  exact (finishSort_perm (d.segment marker)).map Cell.row

theorem segment_row_mem_candidates {marker : Ref} (hm : marker ∈ d.bucket) {row : Row}
    (hRow : row ∈ (d.segment marker).map Cell.row) : row ∈ d.candidates.map Cell.row := by
  obtain ⟨cell, hCell, hCellRow⟩ := List.mem_map.mp hRow
  exact List.mem_map.mpr ⟨cell, List.mem_flatMap.mpr ⟨marker, hm, hCell⟩, hCellRow⟩

section ParentRows

variable
  (hParentPower : ∀ marker (hm : marker ∈ d.bucket),
    ColumnPowerSteps (d.marker_data marker hm).parentNodes)
  (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (index : Nat) (cell : Cell),
    (d.marker_data marker hm).parentNodes[index]? = some cell ∧
      cell.row = (d.marker_data marker hm).current.row)

include hParentPower hParentLow

theorem sorted_segment_spec {marker : Ref} (hm : marker ∈ d.bucket) :
    RowsPowerSteps (d.sortedSegmentRows marker) ∧
      (d.sortedSegmentRows marker).head? = some (d.marker_data marker hm).current.row ∧
      (d.sortedSegmentRows marker).getLast? = some
        (Row.run (d.marker_data marker hm).targetCell.row
          (contourExponents (d.bucket.map Ref.index) marker.index
            (d.marker_data marker hm).current (d.sources.toList.drop (marker.index + 1)))) ∧
      (d.marker_data marker hm).targetCell.row ∈ d.sortedSegmentRows marker := by
  let s := d.marker_data marker hm
  obtain ⟨lowIndex, lowCell, hLow, hLowRow⟩ := hParentLow marker hm
  exact copySegment_sorted_power d.ambient_valid d.source_column d.source_nonzero d.destination.le
    d.source_top references (d.bucket.map Ref.index) s.current_at s.upper_at s.upper_left
    s.parent_nodes s.target_at s.reference s.target_lower (hParentPower marker hm) hLow hLowRow
    (d.segment_run hm)

theorem sorted_segment_nonempty {marker : Ref} (hm : marker ∈ d.bucket) :
    d.sortedSegmentRows marker ≠ [] := by
  intro hEmpty
  have hHead := (d.sorted_segment_spec hParentPower hParentLow hm).2.1
  rw [hEmpty] at hHead
  cases hHead

/-- Every adjacent marker pair, in ascending order, has the actual lifted
last contour row connected by one power step to the next physical marker. -/
theorem ascending_marker_seams (hNoPremature : NoPrematureOne d.sources) :
    d.bucket.reverse.IsChain (fun a b =>
      ∀ lower ∈ (d.sortedSegmentRows a).getLast?,
      ∀ upper ∈ (d.sortedSegmentRows b).head?, RowPowerStep lower upper) := by
  have hAscending : d.bucket.reverse.Pairwise (fun a b => a.index < b.index) :=
    List.pairwise_reverse.mpr d.marker_order
  apply List.IsChain.imp_of_mem_imp ?_ (ordered_markers_adjacent hAscending)
  intro a b haReverse hbReverse hAdjacent
  have ha : a ∈ d.bucket := List.mem_reverse.mp haReverse
  have hb : b ∈ d.bucket := List.mem_reverse.mp hbReverse
  let sa := d.marker_data a ha
  let sb := d.marker_data b hb
  have hNoBetween : ∀ middle, a.index < middle → middle < b.index →
      middle ∉ d.bucket.map Ref.index := by
    intro middle hLow hHigh hMem
    obtain ⟨entry, hEntry, hEntryIndex⟩ := List.mem_map.mp hMem
    apply hAdjacent.2 entry (List.mem_reverse.mpr hEntry)
    simpa only [hEntryIndex] using And.intro hLow hHigh
  obtain ⟨scale, hTarget, hCap⟩ := d.reference_caps a ha b hb hAdjacent.1
  have hSeam := contour_lifted_seam d.source_power hNoPremature (d.bucket.map Ref.index)
    sa.current_at sb.current_at (List.mem_map.mpr ⟨b, hb, rfl⟩) hAdjacent.1 hNoBetween rfl
    sa.target_lower hTarget hCap
  have hLast := (d.sorted_segment_spec hParentPower hParentLow ha).2.2.1
  have hHead := (d.sorted_segment_spec hParentPower hParentLow hb).2.1
  intro lower hLower upper hUpper
  have hLowerEq : Row.run sa.targetCell.row
      (contourExponents (d.bucket.map Ref.index) a.index sa.current
        (d.sources.toList.drop (a.index + 1))) = lower := by
    simpa only [hLast, Option.mem_some_iff] using hLower
  have hUpperEq : sb.current.row = upper := by
    simpa only [hHead, Option.mem_some_iff] using hUpper
  rw [← hLowerEq, ← hUpperEq]
  exact hSeam

theorem ascendingRows_power (hNoPremature : NoPrematureOne d.sources) :
    RowsPowerSteps d.ascendingRows := by
  apply RowsPowerSteps.flatMap_of_adjacent d.sortedSegmentRows
  · intro marker hm
    exact d.sorted_segment_nonempty hParentPower hParentLow (List.mem_reverse.mp hm)
  · intro marker hm
    exact (d.sorted_segment_spec hParentPower hParentLow (List.mem_reverse.mp hm)).1
  · exact d.ascending_marker_seams hParentPower hParentLow hNoPremature

/-- The power-step property is transferred through the actual sorting and
backfill of any successful return, without assuming it of that return. -/
theorem copyColumn_power (hNoPremature : NoPrematureOne d.sources) {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column) :
    ColumnPowerSteps column := by
  have hFinish : finish mountain d.candidates = .ok column := d.copyColumn_eq_finish.symm.trans hRun
  exact finish_power_steps hFinish d.ascendingRows_perm
    (d.ascendingRows_power hParentPower hParentLow hNoPremature)

/-- Both original and lifted endpoint rows have actual fresh output-array
indices. Backfill may change values, so only row equalities are asserted. -/
theorem copyColumn_marker_target_reads {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {marker : Ref} (hm : marker ∈ d.bucket) :
    (∃ (index : Nat) (cell : Cell), column[index]? = some cell ∧
      cell.row = (d.marker_data marker hm).current.row) ∧
    (∃ (index : Nat) (cell : Cell), column[index]? = some cell ∧
      cell.row = (d.marker_data marker hm).targetCell.row) := by
  have hFinish : finish mountain d.candidates = .ok column := d.copyColumn_eq_finish.symm.trans hRun
  have hLow := (d.segment_bounds hm).2.1
  have hTargetSorted := (d.sorted_segment_spec hParentPower hParentLow hm).2.2.2
  have hTarget : (d.marker_data marker hm).targetCell.row ∈ (d.segment marker).map Cell.row :=
    ((finishSort_perm (d.segment marker)).map Cell.row).mem_iff.mp hTargetSorted
  exact ⟨finish_row_read hFinish (d.segment_row_mem_candidates hm hLow),
    finish_row_read hFinish (d.segment_row_mem_candidates hm hTarget)⟩

/-- A complete copied column with both geometric induction interfaces:
adjacent power steps and actual marker/reference endpoint preservation. -/
theorem copyColumn_valid_power (hNoPremature : NoPrematureOne d.sources) :
    ∃ column, copyColumn mountain marked references sourceColumn shift rootColumn = .ok column ∧
      FinishedColumn mountain column ∧ ColumnValid mountain mountain.size column ∧
      TopOne column ∧ ColumnPowerSteps column ∧ MountainValid (mountain.push column) ∧
      ∀ marker (hm : marker ∈ d.bucket),
        (∃ (index : Nat) (cell : Cell), column[index]? = some cell ∧
          cell.row = (d.marker_data marker hm).current.row) ∧
        (∃ (index : Nat) (cell : Cell), column[index]? = some cell ∧
          cell.row = (d.marker_data marker hm).targetCell.row) := by
  obtain ⟨column, hRun, hFinished, hValid, hTop, hPush⟩ := d.copyColumn_valid
  exact ⟨column, hRun, hFinished, hValid, hTop,
    d.copyColumn_power hParentPower hParentLow hNoPremature hRun, hPush,
    fun _ hm => d.copyColumn_marker_target_reads hParentPower hParentLow hRun hm⟩

end ParentRows

end OmegaY.Expansion.ColumnCopyData

#print axioms OmegaY.Expansion.ColumnCopyData.ascendingRows_power
#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_power
#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_marker_target_reads
#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_valid_power
