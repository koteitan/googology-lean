/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/FillAdjacent.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/FillAdjacent.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.FillPathActual
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.FinishSupport
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ColumnCopyData
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.SegmentPower
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ColumnPower

set_option backward.do.legacy false

/-!
# Actual reference-ladder cells and their adjacent stored legs

The ascending representation reverses each real fill chunk independently.
The lemmas retain complete cells, so the left endpoint is not lost when
moving from row paths to sorting and numerical backfill.
-/

namespace OmegaY.Expansion

open Canonical

def referenceRung (lower : Row) (column index degree : Nat) : Cell :=
  ⟨Row.bump lower degree, 0, some ⟨column, index⟩⟩

theorem fillChunk_reverse_cells {nodes : Column} {column index : Nat}
    {parent upper : Cell} {low high : Row}
    (hParent : nodes[index]? = some parent) (hUpper : nodes[index + 1]? = some upper)
    (hEligible : low ≤ parent.row ∧ parent.row < high) :
    (fillChunk nodes column low high index).reverse =
      (List.range (Row.jump parent.row upper.row)).map (referenceRung parent.row column index) := by
  simp [fillChunk, hParent, hUpper, hEligible, Row.fillLadder,
    List.map_map, referenceRung, Function.comp_def]

theorem fillChunk_reverse_length {nodes : Column} {column index : Nat}
    {parent upper : Cell} {low high : Row}
    (hParent : nodes[index]? = some parent) (hUpper : nodes[index + 1]? = some upper)
    (hEligible : low ≤ parent.row ∧ parent.row < high) :
    (fillChunk nodes column low high index).reverse.length = Row.jump parent.row upper.row := by
  rw [fillChunk_reverse_cells hParent hUpper hEligible]
  simp

/-- Every rung has an exact position and the actual fill parent's reference. -/
theorem fillChunk_reverse_getElem {nodes : Column} {column index degree : Nat}
    {parent upper : Cell} {low high : Row}
    (hParent : nodes[index]? = some parent) (hUpper : nodes[index + 1]? = some upper)
    (hEligible : low ≤ parent.row ∧ parent.row < high)
    (hDegree : degree < Row.jump parent.row upper.row) :
    (fillChunk nodes column low high index).reverse[degree]? =
      some (referenceRung parent.row column index degree) := by
  rw [fillChunk_reverse_cells hParent hUpper hEligible]
  simp [hDegree]

/-- Consecutive interior rungs keep exactly the same stored left endpoint. -/
theorem fillChunk_reverse_interior {nodes : Column} {column index degree : Nat}
    {parent upper : Cell} {low high : Row}
    (hParent : nodes[index]? = some parent) (hUpper : nodes[index + 1]? = some upper)
    (hEligible : low ≤ parent.row ∧ parent.row < high)
    (hDegree : degree + 1 < Row.jump parent.row upper.row) :
    (fillChunk nodes column low high index).reverse[degree]? =
        some (referenceRung parent.row column index degree) ∧
      (fillChunk nodes column low high index).reverse[degree + 1]? =
        some (referenceRung parent.row column index (degree + 1)) :=
  ⟨fillChunk_reverse_getElem hParent hUpper hEligible (by omega),
    fillChunk_reverse_getElem hParent hUpper hEligible hDegree⟩

/-- At a true parent power step the last rung is its upper endpoint,
with the lower parent's stored reference, at the actual last chunk index. -/
theorem fillChunk_reverse_endpoint {nodes : Column} {column index : Nat}
    {parent upper : Cell} {low high : Row}
    (hParent : nodes[index]? = some parent) (hUpper : nodes[index + 1]? = some upper)
    (hEligible : low ≤ parent.row ∧ parent.row < high)
    (hPower : ColumnPowerSteps nodes) :
    (fillChunk nodes column low high index).reverse[Row.jump parent.row upper.row - 1]? =
      some ⟨upper.row, 0, some ⟨column, index⟩⟩ := by
  have hStep : RowPowerStep parent.row upper.row := hPower index parent upper hParent hUpper
  have hJump : 0 < Row.jump parent.row upper.row := by
    by_contra hn
    have he : parent.row = upper.row := Row.jump_eq_zero.mp (by omega)
    exact (ne_of_lt hStep.lt) he
  have hRead := fillChunk_reverse_getElem (column := column) hParent hUpper hEligible
    (show Row.jump parent.row upper.row - 1 < Row.jump parent.row upper.row by omega)
  change upper.row = Row.bump parent.row (Row.jump parent.row upper.row - 1) at hStep
  simpa only [referenceRung, ← hStep] using hRead

def fillCellsAscending (nodes : Column) (column : Nat) (low high : Row) : List Cell :=
  (List.range nodes.size).flatMap fun index => (fillChunk nodes column low high index).reverse

def fillAscendingOffset (nodes : Column) (column : Nat) (low high : Row) (index : Nat) : Nat :=
  ((List.range index).flatMap fun i => (fillChunk nodes column low high i).reverse).length

theorem fillCellsAscending_rows (nodes : Column) (column : Nat) (low high : Row) :
    (fillCellsAscending nodes column low high).map Cell.row =
      fillCellsAscendingRows nodes column low high := by
  simp only [fillCellsAscending, fillCellsAscendingRows, List.map_flatMap, List.map_reverse]

theorem fillCellsAscending_perm (nodes : Column) (column : Nat) (low high : Row) :
    (fillCellsAscending nodes column low high).Perm (fillCells nodes column low high) := by
  exact List.Perm.flatMap_left _ (fun _ _ => List.reverse_perm _)

theorem fillCellsAscending_strict {nodes : Column} (hStrict : FillRowsStrict nodes)
    {column capIndex : Nat} {cap : Cell} {low high : Row}
    (hCap : nodes[capIndex]? = some cap) (hHigh : high ≤ cap.row) :
    (fillCellsAscending nodes column low high).Pairwise (fun a b => a.row < b.row) := by
  rw [← List.pairwise_map]
  rw [fillCellsAscending_rows]
  exact fillCellsAscendingRows_strict hStrict hCap hHigh

private theorem range_split_at {size index : Nat} (hIndex : index < size) :
    List.range size = List.range index ++ index :: List.range' (index + 1) (size - index - 1) := by
  have hSplit := List.range'_append_1 (s := 0) (m := index) (n := size - index)
  have hCount : size - index = (size - index - 1) + 1 := by omega
  rw [hCount, List.range'_succ] at hSplit
  simpa only [← List.range_eq_range', Nat.zero_add, Nat.add_sub_of_le hIndex.le,
    Nat.sub_add_cancel (show 1 ≤ size - index by omega)] using hSplit.symm

/-- An exact index in the whole actual ascending fill list. The offset is
computed from all earlier executable chunks, including empty chunks. -/
theorem fillCellsAscending_getElem {nodes : Column} {column index degree : Nat}
    {parent upper : Cell} {low high : Row}
    (hParent : nodes[index]? = some parent) (hUpper : nodes[index + 1]? = some upper)
    (hEligible : low ≤ parent.row ∧ parent.row < high)
    (hDegree : degree < Row.jump parent.row upper.row) :
    (fillCellsAscending nodes column low high)[fillAscendingOffset nodes column low high index + degree]? =
      some (referenceRung parent.row column index degree) := by
  have hIndex := (Array.getElem?_eq_some_iff.mp hParent).1
  have hLength := fillChunk_reverse_length (column := column) hParent hUpper hEligible
  have hBefore : ((List.range index).flatMap fun i =>
      (fillChunk nodes column low high i).reverse).length =
        fillAscendingOffset nodes column low high index := rfl
  rw [fillCellsAscending, range_split_at hIndex, List.flatMap_append, List.flatMap_cons]
  rw [List.getElem?_append_right (by rw [hBefore]; omega), hBefore, Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by simpa only [hLength] using hDegree)]
  exact fillChunk_reverse_getElem hParent hUpper hEligible hDegree

theorem fillAscendingOffset_succ (nodes : Column) (column index : Nat) (low high : Row) :
    fillAscendingOffset nodes column low high (index + 1) =
      fillAscendingOffset nodes column low high index +
        (fillChunk nodes column low high index).reverse.length := by
  simp [fillAscendingOffset, List.range_succ, List.flatMap_append]

/-- These two indices are consecutive in the complete fill list, not just
inside an isolated ladder. Both cells carry the same actual parent ref. -/
theorem fillCellsAscending_interior {nodes : Column} {column index degree : Nat}
    {parent upper : Cell} {low high : Row}
    (hParent : nodes[index]? = some parent) (hUpper : nodes[index + 1]? = some upper)
    (hEligible : low ≤ parent.row ∧ parent.row < high)
    (hDegree : degree + 1 < Row.jump parent.row upper.row) :
    let position := fillAscendingOffset nodes column low high index + degree
    (fillCellsAscending nodes column low high)[position]? =
        some (referenceRung parent.row column index degree) ∧
      (fillCellsAscending nodes column low high)[position + 1]? =
        some (referenceRung parent.row column index (degree + 1)) := by
  dsimp only
  exact ⟨fillCellsAscending_getElem hParent hUpper hEligible (by omega),
    by simpa only [Nat.add_assoc] using fillCellsAscending_getElem hParent hUpper hEligible hDegree⟩

/-- Across consecutive eligible parent intervals, the first ladder's
endpoint is immediately followed by the next ladder's first rung. Their
stored left refs are respectively index and index+1. The segment cap is
excluded by requiring that the second parent is itself eligible. -/
theorem fillCellsAscending_seam {nodes : Column} (hPower : ColumnPowerSteps nodes)
    {column index : Nat} {parent middle upper : Cell} {low high : Row}
    (hParent : nodes[index]? = some parent) (hMiddle : nodes[index + 1]? = some middle)
    (hUpper : nodes[(index + 1) + 1]? = some upper)
    (hEligible : low ≤ parent.row ∧ parent.row < high)
    (hNextEligible : low ≤ middle.row ∧ middle.row < high) :
    let position := fillAscendingOffset nodes column low high index + Row.jump parent.row middle.row - 1
    (fillCellsAscending nodes column low high)[position]? =
        some ⟨middle.row, 0, some ⟨column, index⟩⟩ ∧
      (fillCellsAscending nodes column low high)[position + 1]? =
        some (referenceRung middle.row column (index + 1) 0) := by
  have hFirstStep : RowPowerStep parent.row middle.row := hPower index parent middle hParent hMiddle
  have hSecondStep : RowPowerStep middle.row upper.row := hPower (index + 1) middle upper hMiddle hUpper
  have hFirstJump : 0 < Row.jump parent.row middle.row := by
    by_contra hn
    exact (ne_of_lt hFirstStep.lt) (Row.jump_eq_zero.mp (by omega))
  have hSecondJump : 0 < Row.jump middle.row upper.row := by
    by_contra hn
    exact (ne_of_lt hSecondStep.lt) (Row.jump_eq_zero.mp (by omega))
  have hFirst := fillCellsAscending_getElem (column := column) hParent hMiddle hEligible
    (show Row.jump parent.row middle.row - 1 < Row.jump parent.row middle.row by omega)
  have hSecond := fillCellsAscending_getElem (column := column) hMiddle hUpper hNextEligible hSecondJump
  rw [fillAscendingOffset_succ, fillChunk_reverse_length hParent hMiddle hEligible,
    Nat.add_zero] at hSecond
  change middle.row = Row.bump parent.row (Row.jump parent.row middle.row - 1) at hFirstStep
  have hPosition : fillAscendingOffset nodes column low high index + Row.jump parent.row middle.row - 1 =
      fillAscendingOffset nodes column low high index + (Row.jump parent.row middle.row - 1) := by omega
  have hPositionNext : (fillAscendingOffset nodes column low high index + Row.jump parent.row middle.row - 1) + 1 =
      fillAscendingOffset nodes column low high index + Row.jump parent.row middle.row := by omega
  dsimp only
  constructor
  · simpa only [hPosition, referenceRung, ← hFirstStep] using hFirst
  · simpa only [hPositionNext] using hSecond

/-- Strict full-cell presentations identify the real sort. The proof does
not use a row equality to discard or invent stored-left information. -/
theorem finishSort_eq_of_strict_perm {ascending cells : List Cell}
    (hPerm : ascending.Perm cells)
    (hStrict : ascending.Pairwise (fun a b => a.row < b.row)) : finishSort cells = ascending := by
  have hRowsStrict : (ascending.map Cell.row).Pairwise (· < ·) := by
    simpa only [List.pairwise_map] using hStrict
  have hNodup : (cells.map Cell.row).Nodup :=
    (hPerm.map Cell.row).nodup_iff.mp (hRowsStrict.imp (fun h => ne_of_lt h))
  apply List.Perm.eq_of_pairwise
    (fun a b _ _ hab hba => False.elim (lt_asymm hab hba))
    (finishSort_strict hNodup) hStrict
  exact (finishSort_perm cells).trans hPerm.symm

theorem finishSort_fillCells {nodes : Column} (hStrict : FillRowsStrict nodes)
    {column capIndex : Nat} {cap : Cell} {low high : Row}
    (hCap : nodes[capIndex]? = some cap) (hHigh : high ≤ cap.row) :
    finishSort (fillCells nodes column low high) = fillCellsAscending nodes column low high :=
  finishSort_eq_of_strict_perm (fillCellsAscending_perm _ _ _ _)
    (fillCellsAscending_strict hStrict hCap hHigh)

/-- Exact full-cell sorted presentation of the real fill return. The cap
and leftward condition are the existing fill totality inputs, not a claim
about the output adjacency. -/
theorem fill_sorted_cells {mountain : Mountain} {source : Ref} {sourceCell : Cell}
    {sourceParent : Ref} {shift : Nat} {nodes : Column} {low high : Row}
    {capIndex : Nat} {cap : Cell}
    (hSource : lookup mountain source = .ok sourceCell)
    (hLeft : sourceCell.left = some sourceParent)
    (hNodes : mountain[sourceParent.column + shift]? = some nodes)
    (hStrict : FillRowsStrict nodes) (hCap : nodes[capIndex]? = some cap)
    (hHigh : high ≤ cap.row) (hLeftward : sourceParent.column + shift < source.column + shift)
    {result : List Cell} (hRun : fill mountain source shift low high = .ok result) :
    finishSort result = fillCellsAscending nodes (sourceParent.column + shift) low high := by
  have hExact := fill_eq_cells hSource hLeft hNodes hStrict hCap hHigh hLeftward (low := low)
  have he : result = fillCells nodes (sourceParent.column + shift) low high :=
    Except.ok.inj (hRun.symm.trans hExact)
  rw [he]
  exact finishSort_fillCells hStrict hCap hHigh

private theorem splice_getElem {before fragment after : List Cell} {index : Nat} {cell : Cell}
    (hRead : fragment[index]? = some cell) :
    (before ++ fragment ++ after)[before.length + index]? = some cell := by
  have hi := (List.getElem?_eq_some_iff.mp hRead).1
  rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left hi]
  exact hRead

/-- A complete sorted-cell presentation transfers an actually calculated
pair of consecutive input cells through the real finisher. This does not
assume the desired output adjacency: its two output indices and both stored
left refs follow from the exact source-list split and shape preservation. -/
theorem finish_adjacent_of_splice {mountain : Mountain} {cells : List Cell} {column : Column}
    (hRun : finish mountain cells = .ok column)
    {before fragment after : List Cell} (hSorted : finishSort cells = before ++ fragment ++ after)
    {index : Nat} {lower upper : Cell}
    (hLower : fragment[index]? = some lower) (hUpper : fragment[index + 1]? = some upper) :
    ∃ lowerOutput upperOutput,
      column[before.length + index]? = some lowerOutput ∧
      column[(before.length + index) + 1]? = some upperOutput ∧
      SameShape lower lowerOutput ∧ SameShape upper upperOutput := by
  have hShape := (finish_success_spec hRun).1
  change ColumnShape (finishSort cells) column at hShape
  rw [hSorted] at hShape
  obtain ⟨lowerOutput, hLowerOutput, hLowerShape⟩ :=
    hShape.source_getElem (splice_getElem (before := before) (after := after) hLower)
  obtain ⟨upperOutput, hUpperOutput, hUpperShape⟩ :=
    hShape.source_getElem (splice_getElem (before := before) (after := after) hUpper)
  exact ⟨lowerOutput, upperOutput, hLowerOutput,
    by simpa only [Nat.add_assoc] using hUpperOutput, hLowerShape, hUpperShape⟩

/-- The real marker segment's sort has a contiguous full-cell fill block.
Both the marker and contour are the actual executable returns. Thus the
interior/seam indices above cannot be interrupted by a contour or marker
inside this segment. No sorted-output adjacency is a premise. -/
theorem copySegment_sorted_splice {mountain : Mountain} (hValid : MountainValid mountain)
    {sources : Column} {references : List Ref} {sourceColumn shift rootColumn index : Nat}
    (hSources : mountain[sourceColumn]? = some sources) (hSourcePositive : 0 < sourceColumn)
    (hDestination : sourceColumn + shift ≤ mountain.size) (hTop : TopOne sources)
    (markerIndices : List Nat) (s : MarkerCopyData mountain sources references shift index)
    (hParentPower : ColumnPowerSteps s.parentNodes) {lowIndex : Nat} {lowCell : Cell}
    (hParentLow : s.parentNodes[lowIndex]? = some lowCell)
    (hParentLowRow : lowCell.row = s.current.row) {result : List Cell}
    (hRun : copySegment mountain sources references sourceColumn markerIndices shift rootColumn index =
      .ok result) :
    ∃ copied path,
      copyEdge mountain ⟨sourceColumn, index⟩ shift rootColumn s.current.row = .ok copied ∧
      contour mountain sourceColumn markerIndices shift rootColumn index s.targetCell.row s.current
        (sources.toList.drop (index + 1)) = .ok path ∧
      finishSort result = [copied] ++
        fillCellsAscending s.parentNodes (s.sourceParent.column + shift) s.current.row s.targetCell.row ++ path := by
  obtain ⟨copied, path, gap, hResult, hCopied, hCopiedRow, _, hContour, hFill, _, _, _⟩ :=
    copySegment_result_decomposition hValid hSources hSourcePositive hDestination hTop
      references markerIndices s.current_at s.upper_at s.upper_left s.parent_nodes s.target_at
      s.reference s.target_lower hRun
  obtain ⟨hc, hSourceEq⟩ := Array.getElem?_eq_some_iff.mp hSources
  have hSourceValid : ColumnValid mountain sourceColumn sources := hSourceEq ▸ hValid _ hc
  obtain ⟨hp, hParentEq⟩ := Array.getElem?_eq_some_iff.mp s.parent_nodes
  have hParentValid : ColumnValid mountain (s.sourceParent.column + shift) s.parentNodes :=
    hParentEq ▸ hValid _ hp
  have hUpperRead : lookup mountain ⟨sourceColumn, index + 1⟩ = .ok s.upper :=
    lookup_ok_iff.mpr ⟨sources, hSources, s.upper_at⟩
  have hLeftward := (hSourceValid.stored_valid _ _ _ s.upper_at s.upper_left).1
  have hExactFill := fill_eq_cells hUpperRead s.upper_left s.parent_nodes
    (fillRowsStrict_of_columnValid hParentValid) s.target_at le_rfl (Nat.add_lt_add_right hLeftward shift)
    (low := s.current.row)
  have hGapEq : gap = fillCells s.parentNodes (s.sourceParent.column + shift) s.current.row s.targetCell.row :=
    Except.ok.inj (hFill.symm.trans hExactFill)
  have hGapPower := fillCellsAscendingRows_power_steps (fillRowsStrict_of_columnValid hParentValid)
    hParentPower hParentLow s.target_at (by simpa only [hParentLowRow] using s.target_lower)
    (column := s.sourceParent.column + shift)
  rw [hParentLowRow] at hGapPower
  have hContourPower := contour_power_steps_of_success hValid hSources hSourcePositive hDestination
    hTop markerIndices s.targetCell.row s.current_at rfl hContour
  have hWholePower := RowsPowerSteps.append_at hGapPower.1 hGapPower.2 hContourPower
  have hStrict : ([copied] ++ fillCellsAscending s.parentNodes (s.sourceParent.column + shift)
      s.current.row s.targetCell.row ++ path).Pairwise (fun a b => a.row < b.row) := by
    rw [← List.pairwise_map]
    simpa only [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      hCopiedRow, fillCellsAscending_rows] using hWholePower.strict
  have hPerm : ([copied] ++ fillCellsAscending s.parentNodes (s.sourceParent.column + shift)
      s.current.row s.targetCell.row ++ path).Perm result := by
    rw [hResult, hGapEq]
    simp only [List.cons_append]
    exact List.Perm.cons _ (((fillCellsAscending_perm _ _ _ _).append_right path).trans List.perm_append_comm)
  exact ⟨copied, path, hCopied, hContour, finishSort_eq_of_strict_perm hPerm hStrict⟩

namespace ColumnCopyData

variable {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
  {sourceColumn shift rootColumn : Nat}
  (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)

def ascendingCells : List Cell := d.bucket.reverse.flatMap fun marker => finishSort (d.segment marker)

theorem ascendingCells_rows : d.ascendingCells.map Cell.row = d.ascendingRows := by
  simp only [ascendingCells, ascendingRows, List.map_flatMap]
  rfl

theorem ascendingCells_perm : d.ascendingCells.Perm d.candidates := by
  apply (List.reverse_perm d.bucket).flatMap
  intro marker _
  exact finishSort_perm (d.segment marker)

section ParentInputs

variable
  (hParentPower : ∀ marker (hm : marker ∈ d.bucket),
    ColumnPowerSteps (d.marker_data marker hm).parentNodes)
  (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (index : Nat) (cell : Cell),
    (d.marker_data marker hm).parentNodes[index]? = some cell ∧
      cell.row = (d.marker_data marker hm).current.row)
  (hNoPremature : NoPrematureOne d.sources)

include hParentPower hParentLow hNoPremature

theorem finishSort_candidates_cells : finishSort d.candidates = d.ascendingCells := by
  apply finishSort_eq_of_strict_perm d.ascendingCells_perm
  rw [← List.pairwise_map, d.ascendingCells_rows]
  exact (d.ascendingRows_power hParentPower hParentLow hNoPremature).strict

/-- The whole real column candidate sort contains this actual marker's fill
as one contiguous full-cell block. The placement is derived from ordered
markers, segment execution and sorting, rather than assumed as adjacency. -/
theorem fill_splice_in_candidates {marker : Ref} (hm : marker ∈ d.bucket) :
    ∃ before after,
      finishSort d.candidates = before ++
        fillCellsAscending (d.marker_data marker hm).parentNodes
          ((d.marker_data marker hm).sourceParent.column + shift)
          (d.marker_data marker hm).current.row (d.marker_data marker hm).targetCell.row ++ after := by
  let s := d.marker_data marker hm
  obtain ⟨lowIndex, lowCell, hLowRead, hLowRow⟩ := hParentLow marker hm
  obtain ⟨copied, path, _, _, hSegment⟩ := copySegment_sorted_splice d.ambient_valid d.source_column
    d.source_nonzero d.destination.le d.source_top (d.bucket.map Ref.index) s
    (hParentPower marker hm) hLowRead hLowRow (d.segment_run hm)
  obtain ⟨before, after, hSplit⟩ := List.append_of_mem (List.mem_reverse.mpr hm)
  let sortedSegment := fun entry => finishSort (d.segment entry)
  refine ⟨before.flatMap sortedSegment ++ [copied], path ++ after.flatMap sortedSegment, ?_⟩
  rw [d.finishSort_candidates_cells hParentPower hParentLow hNoPremature]
  simp only [ascendingCells, hSplit, List.flatMap_append, List.flatMap_cons]
  rw [hSegment]
  simp only [List.append_assoc, sortedSegment, s]

/-- Every actual internal fill pair survives as a consecutive pair in the
completed copied column, preserving both rows and stored left references.
The original marker and cap-to-contour seam are outside this statement. -/
theorem copyColumn_fill_adjacent {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {marker : Ref} (hm : marker ∈ d.bucket) {index : Nat} {lower upper : Cell}
    (hLower : (fillCellsAscending (d.marker_data marker hm).parentNodes
      ((d.marker_data marker hm).sourceParent.column + shift)
      (d.marker_data marker hm).current.row (d.marker_data marker hm).targetCell.row)[index]? = some lower)
    (hUpper : (fillCellsAscending (d.marker_data marker hm).parentNodes
      ((d.marker_data marker hm).sourceParent.column + shift)
      (d.marker_data marker hm).current.row (d.marker_data marker hm).targetCell.row)[index + 1]? = some upper) :
    ∃ position lowerOutput upperOutput,
      column[position]? = some lowerOutput ∧ column[position + 1]? = some upperOutput ∧
      SameShape lower lowerOutput ∧ SameShape upper upperOutput := by
  obtain ⟨before, after, hSplit⟩ := d.fill_splice_in_candidates hParentPower hParentLow hNoPremature hm
  obtain ⟨lowerOutput, upperOutput, hLowerOutput, hUpperOutput, hLowerShape, hUpperShape⟩ :=
    finish_adjacent_of_splice (d.copyColumn_eq_finish.symm.trans hRun) hSplit hLower hUpper
  exact ⟨before.length + index, lowerOutput, upperOutput,
    hLowerOutput, hUpperOutput, hLowerShape, hUpperShape⟩

end ParentInputs

end ColumnCopyData

end OmegaY.Expansion

#print axioms OmegaY.Expansion.fillChunk_reverse_interior
#print axioms OmegaY.Expansion.fillChunk_reverse_endpoint
#print axioms OmegaY.Expansion.fillCellsAscending_interior
#print axioms OmegaY.Expansion.fillCellsAscending_seam
#print axioms OmegaY.Expansion.finishSort_fillCells
#print axioms OmegaY.Expansion.fill_sorted_cells
#print axioms OmegaY.Expansion.finish_adjacent_of_splice
#print axioms OmegaY.Expansion.copySegment_sorted_splice
#print axioms OmegaY.Expansion.ColumnCopyData.fill_splice_in_candidates
#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_fill_adjacent
