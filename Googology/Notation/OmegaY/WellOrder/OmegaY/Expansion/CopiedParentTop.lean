/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/CopiedParentTop.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/CopiedParentTop.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ContourAdjacent
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ShiftedEdgeInterval

set_option backward.do.legacy false

/-! The original source top has no upper barrier. It lies in the highest
marker's actual contour and becomes the actual last node after copying,
sorting, and backfill. Every greater ceiling therefore selects that node.
No copied top or copied normality is assumed. -/

namespace OmegaY.Expansion

open Canonical

theorem contourSourceCells_eq_suffix_of_no_above {nodes : Column}
    (hNoPremature : NoPrematureOne nodes) (markerIndices : List Nat)
    {index : Nat} {current : Cell} (hCurrent : nodes[index]? = some current)
    (hNoAbove : ∀ next, index < next → next ∉ markerIndices)
    {rest : List Cell} (hRest : nodes.toList.drop (index + 1) = rest) :
    contourSourceCells markerIndices index current rest = rest := by
  induction rest generalizing index current with
  | nil => rfl
  | cons upper rest ih =>
    have hUpper : nodes[index + 1]? = some upper := by
      simpa only [List.head?_drop, Array.getElem?_toList, List.head?_cons] using congrArg List.head? hRest
    have hTail : nodes.toList.drop ((index + 1) + 1) = rest := by
      simpa only [List.tail_drop, List.tail_cons] using congrArg List.tail hRest
    have hNotStop : ¬ (current.value = 1 ∨ index + 1 ∈ markerIndices) :=
      not_or.mpr ⟨hNoPremature index current upper hCurrent hUpper, hNoAbove _ (by omega)⟩
    rw [contourSourceCells, if_neg hNotStop]
    exact congrArg (List.cons upper) (ih hUpper (fun next hn => hNoAbove next (by omega)) hTail)

/-- The actual final stored index is selected by every larger ceiling.
No row-density or upper-neighbour premise is necessary. -/
theorem below_eq_of_top {mountain : Mountain} {column : Nat} {nodes : Column}
    (hNodes : mountain[column]? = some nodes) {top : Cell}
    (hTop : nodes[nodes.size - 1]? = some top) {ceiling : Row} (hCeiling : top.row < ceiling) :
    below mountain column ceiling = .ok ⟨column, nodes.size - 1⟩ := by
  obtain ⟨found, hFound⟩ := (below_succeeds_iff hNodes ceiling).mpr ⟨nodes.size - 1, top, hTop, hCeiling⟩
  obtain ⟨hColumn, actual, hActual, _⟩ := below_result hNodes hFound
  have hAbove := below_max_index hNodes hFound hTop hCeiling
  have hBound := (Array.getElem?_eq_some_iff.mp hActual).1
  have hIndex : found.index = nodes.size - 1 := by omega
  have hRef : found = ⟨column, nodes.size - 1⟩ := by cases found; simp_all only
  simpa only [hRef] using hFound

namespace ColumnCopyData

variable {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
  {sourceColumn shift rootColumn : Nat}
  (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)

include d

theorem highest_marker_exists : ∃ marker ∈ d.bucket,
    ∀ other ∈ d.bucket, other.index ≤ marker.index := by
  cases hBucket : d.bucket with
  | nil =>
    have hPhantom : (⟨sourceColumn, 0⟩ : Ref) ∈ d.bucket := d.phantom_marker
    rw [hBucket] at hPhantom
    cases hPhantom
  | cons marker rest =>
    refine ⟨marker, by simp, ?_⟩
    intro other hOther
    rcases List.mem_cons.mp hOther with rfl | hm
    · exact le_rfl
    · have hOrder : d.bucket.Pairwise (fun higher lower => lower.index < higher.index) := d.marker_order
      rw [hBucket] at hOrder
      exact ((List.pairwise_cons.mp hOrder).1 other hm).le

theorem highest_marker_head {marker : Ref} (hm : marker ∈ d.bucket)
    (hHighest : ∀ other ∈ d.bucket, other.index ≤ marker.index) :
    ∃ rest, d.bucket = marker :: rest := by
  cases hBucket : d.bucket with
  | nil => rw [hBucket] at hm; cases hm
  | cons first rest =>
    have hMarker := hm
    rw [hBucket] at hMarker
    rcases List.mem_cons.mp hMarker with he | hTail
    · exact ⟨rest, by simp only [he]⟩
    · have hOrder : d.bucket.Pairwise (fun higher lower => lower.index < higher.index) := d.marker_order
      rw [hBucket] at hOrder
      have hBelow := (List.pairwise_cons.mp hOrder).1 marker hTail
      have hAbove := hHighest first (by rw [hBucket]; simp)
      omega

theorem highest_marker_no_above {marker : Ref} (_hm : marker ∈ d.bucket)
    (hHighest : ∀ other ∈ d.bucket, other.index ≤ marker.index) :
    ∀ next, marker.index < next → next ∉ d.bucket.map Ref.index := by
  intro next hNext hMem
  obtain ⟨other, hOther, hIndex⟩ := List.mem_map.mp hMem
  have hh := hHighest other hOther
  rw [hIndex] at hh
  omega

theorem marker_before_source_top {marker : Ref} (hm : marker ∈ d.bucket) :
    marker.index < d.sources.size - 1 := by
  have hUpper := (Array.getElem?_eq_some_iff.mp (d.marker_data marker hm).upper_at).1
  omega

theorem source_top_in_highest_contour (hNoPremature : NoPrematureOne d.sources)
    {marker : Ref} (hm : marker ∈ d.bucket)
    (hHighest : ∀ other ∈ d.bucket, other.index ≤ marker.index)
    {oldTop : Cell} (hOldTop : d.sources[d.sources.size - 1]? = some oldTop) :
    oldTop ∈ contourSourceCells (d.bucket.map Ref.index) marker.index
      (d.marker_data marker hm).current (d.sources.toList.drop (marker.index + 1)) := by
  exact mem_contourSourceCells_of_no_between hNoPremature (d.bucket.map Ref.index)
    (d.marker_data marker hm).current_at hOldTop (d.marker_before_source_top hm)
    (fun next hAbove _ => d.highest_marker_no_above hm hHighest next hAbove) rfl

section ParentInputs

variable
  (hParentPower : ∀ marker (hm : marker ∈ d.bucket),
    ColumnPowerSteps (d.marker_data marker hm).parentNodes)
  (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (index : Nat) (cell : Cell),
    (d.marker_data marker hm).parentNodes[index]? = some cell ∧
      cell.row = (d.marker_data marker hm).current.row)
  (hNoPremature : NoPrematureOne d.sources)

include hParentPower hParentLow hNoPremature

theorem copyColumn_lifted_source_top {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {marker : Ref} (hm : marker ∈ d.bucket)
    (hHighest : ∀ other ∈ d.bucket, other.index ≤ marker.index)
    {oldTop : Cell} (hOldTop : d.sources[d.sources.size - 1]? = some oldTop) :
    ∃ top, column[column.size - 1]? = some top ∧
      top.row = Row.lift (d.marker_data marker hm).current.row (d.marker_data marker hm).targetCell.row oldTop.row ∧
      top.value = 1 := by
  let s := d.marker_data marker hm
  obtain ⟨restMarkers, hBucket⟩ := d.highest_marker_head hm hHighest
  have hNoAbove := d.highest_marker_no_above hm hHighest
  have hSuffix := contourSourceCells_eq_suffix_of_no_above hNoPremature (d.bucket.map Ref.index)
    s.current_at hNoAbove rfl
  obtain ⟨lowIndex, lowCell, hLow, hLowRow⟩ := hParentLow marker hm
  obtain ⟨copied, path, _, hContour, hSegment⟩ := copySegment_sorted_splice d.ambient_valid
    d.source_column d.source_nonzero d.destination.le d.source_top (d.bucket.map Ref.index)
    s (hParentPower marker hm) hLow hLowRow (d.segment_run hm)
  have hRows := contour_rows_eq_lift_of_success d.ambient_valid d.source_column d.source_nonzero
    d.destination.le d.source_top d.source_power (d.bucket.map Ref.index) s.targetCell.row s.current_at rfl hContour
  rw [hSuffix] at hRows
  have hSourceLast : d.sources.toList.getLast? = some oldTop := by
    simpa only [List.getLast?_eq_getElem?, Array.length_toList, Array.getElem?_toList] using hOldTop
  have hUpperBound := (Array.getElem?_eq_some_iff.mp s.upper_at).1
  have hSuffixLast : (d.sources.toList.drop (marker.index + 1)).getLast? = some oldTop := by
    rw [List.getLast?_drop]
    simp only [Array.length_toList, show ¬ d.sources.size ≤ marker.index + 1 by omega, ↓reduceIte, hSourceLast]
  have hPathLast : (path.map Cell.row).getLast? = some (Row.lift s.current.row s.targetCell.row oldTop.row) := by
    rw [hRows, List.getLast?_map, hSuffixLast]
    rfl
  have hWhole : finishSort d.candidates =
      ((restMarkers.reverse.flatMap fun entry => finishSort (d.segment entry)) ++ [copied] ++
        fillCellsAscending s.parentNodes (s.sourceParent.column + shift) s.current.row s.targetCell.row) ++ path := by
    rw [d.finishSort_candidates_cells hParentPower hParentLow hNoPremature]
    simp only [ascendingCells, hBucket, List.reverse_cons, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    rw [hSegment]
    simp only [List.append_assoc]
  have hLastRows : ((finishSort d.candidates).map Cell.row).getLast? =
      some (Row.lift s.current.row s.targetCell.row oldTop.row) := by
    rw [hWhole, List.map_append, List.getLast?_append, hPathLast]
    rfl
  obtain ⟨actual, hActual, _, _, hTopOne, _⟩ := d.copyColumn_valid
  have hEq : actual = column := Except.ok.inj (hActual.symm.trans hRun)
  subst actual
  obtain ⟨top, hTop, hValue⟩ := hTopOne
  rw [Array.back?_eq_getElem?] at hTop
  have hShape := (finish_success_spec (d.copyColumn_eq_finish.symm.trans hRun)).1
  change ColumnShape (finishSort d.candidates) column at hShape
  rw [hShape.1] at hLastRows
  have hOutputLast : (column.toList.map Cell.row).getLast? = some top.row := by
    rw [List.getLast?_map]
    simp only [List.getLast?_eq_getElem?, Array.length_toList,
      Array.getElem?_toList, hTop, Option.map_some]
  exact ⟨top, hTop, Option.some.inj (hOutputLast.symm.trans hLastRows), hValue⟩

/-- The original top needs no upper barrier: every ceiling above its lift
selects the actual copied column's final stored node. -/
theorem copyColumn_below_lifted_source_top {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {marker : Ref} (hm : marker ∈ d.bucket)
    (hHighest : ∀ other ∈ d.bucket, other.index ≤ marker.index)
    {oldTop : Cell} (hOldTop : d.sources[d.sources.size - 1]? = some oldTop)
    {ceiling : Row} (hCeiling : Row.lift (d.marker_data marker hm).current.row
      (d.marker_data marker hm).targetCell.row oldTop.row < ceiling) :
    ∃ parent,
      below (mountain.push column) mountain.size ceiling = .ok ⟨mountain.size, column.size - 1⟩ ∧
      column[column.size - 1]? = some parent ∧
      Canonical.cellAt (mountain.push column) ⟨mountain.size, column.size - 1⟩ = .ok parent ∧
      parent.row = Row.lift (d.marker_data marker hm).current.row
        (d.marker_data marker hm).targetCell.row oldTop.row ∧ parent.value = 1 := by
  obtain ⟨top, hTop, hRow, hValue⟩ :=
    d.copyColumn_lifted_source_top hParentPower hParentLow hNoPremature hRun hm hHighest hOldTop
  have hColumn : (mountain.push column)[mountain.size]? = some column := by simp
  exact ⟨top, below_eq_of_top hColumn hTop (by simpa only [hRow] using hCeiling),
    hTop, cellAt_ok_iff.mpr ⟨column, hColumn, hTop⟩, hRow, hValue⟩

/-- Later columns do not alter either the exact chosen final index or
the copied top cell in the preserved parent column. -/
theorem copyColumn_below_lifted_source_top_preserved {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {later : Mountain} (hPreserve : PreservesColumns (mountain.push column) later)
    {marker : Ref} (hm : marker ∈ d.bucket)
    (hHighest : ∀ other ∈ d.bucket, other.index ≤ marker.index)
    {oldTop : Cell} (hOldTop : d.sources[d.sources.size - 1]? = some oldTop)
    {ceiling : Row} (hCeiling : Row.lift (d.marker_data marker hm).current.row
      (d.marker_data marker hm).targetCell.row oldTop.row < ceiling) :
    ∃ parent,
      below later mountain.size ceiling = .ok ⟨mountain.size, column.size - 1⟩ ∧
      Canonical.cellAt later ⟨mountain.size, column.size - 1⟩ = .ok parent ∧
      parent.row = Row.lift (d.marker_data marker hm).current.row
        (d.marker_data marker hm).targetCell.row oldTop.row ∧ parent.value = 1 := by
  obtain ⟨top, hBelow, hTop, _, hRow, hValue⟩ :=
    d.copyColumn_below_lifted_source_top hParentPower hParentLow hNoPremature hRun hm hHighest hOldTop hCeiling
  have hOldColumn : (mountain.push column)[mountain.size]? = some column := by simp
  have hNewColumn : later[mountain.size]? = some column := hPreserve.column_read hOldColumn
  exact ⟨top, (hPreserve.below (by simp) ceiling).trans hBelow,
    cellAt_ok_iff.mpr ⟨column, hNewColumn, hTop⟩, hRow, hValue⟩

/-- The maximal marker is obtained from the real nonempty bucket, so a
caller with a source-top read need not supply any stopping or marker choice. -/
theorem copyColumn_source_top {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {oldTop : Cell} (hOldTop : d.sources[d.sources.size - 1]? = some oldTop) :
    ∃ (marker : Ref) (hm : marker ∈ d.bucket),
      (∀ other ∈ d.bucket, other.index ≤ marker.index) ∧
      oldTop ∈ contourSourceCells (d.bucket.map Ref.index) marker.index
        (d.marker_data marker hm).current (d.sources.toList.drop (marker.index + 1)) ∧
      ∃ top, column[column.size - 1]? = some top ∧
        top.row = Row.lift (d.marker_data marker hm).current.row
          (d.marker_data marker hm).targetCell.row oldTop.row ∧ top.value = 1 := by
  obtain ⟨marker, hm, hHighest⟩ := d.highest_marker_exists
  exact ⟨marker, hm, hHighest, d.source_top_in_highest_contour hNoPremature hm hHighest hOldTop,
    d.copyColumn_lifted_source_top hParentPower hParentLow hNoPremature hRun hm hHighest hOldTop⟩

end ParentInputs

end ColumnCopyData

end OmegaY.Expansion

#print axioms OmegaY.Expansion.below_eq_of_top
#print axioms OmegaY.Expansion.contourSourceCells_eq_suffix_of_no_above
#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_lifted_source_top
#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_below_lifted_source_top
#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_below_lifted_source_top_preserved
#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_source_top
