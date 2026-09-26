/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/AdjacentOrigin.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/AdjacentOrigin.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.FillAdjacent

set_option backward.do.legacy false

/-! Exhaustive provenance for an actual adjacent output pair. Positions
are reconstructed from the real sorted candidate list. A pair is inside
one executed marker segment, or crosses exactly two consecutive segments;
neither output adjacency nor the desired parent geometry is assumed. -/

namespace OmegaY.Expansion

open Canonical

universe u v

/-- Exact positions in a flattened list of nonempty pieces. A seam records
an actual adjacent pair of source items, not merely two ordered members. -/
inductive FlatMapAdjacentOrigin {α : Type u} {β : Type v}
    (items : List α) (pieces : α → List β) (index : Nat) (lower upper : β) : Prop where
  | inside (before : List α) (item : α) (after : List α) (localIndex : Nat)
      (split : items = before ++ item :: after)
      (position : index = (before.flatMap pieces).length + localIndex)
      (lower_read : (pieces item)[localIndex]? = some lower)
      (upper_read : (pieces item)[localIndex + 1]? = some upper) :
      FlatMapAdjacentOrigin items pieces index lower upper
  | seam (before : List α) (lowItem highItem : α) (after : List α)
      (split : items = before ++ lowItem :: highItem :: after)
      (position : index = (before.flatMap pieces).length + (pieces lowItem).length - 1)
      (lower_read : (pieces lowItem).getLast? = some lower)
      (upper_read : (pieces highItem).head? = some upper) :
      FlatMapAdjacentOrigin items pieces index lower upper

theorem flatMap_adjacent_origin {α : Type u} {β : Type v}
    (items : List α) (pieces : α → List β)
    (hNonempty : ∀ item ∈ items, pieces item ≠ [])
    {index : Nat} {lower upper : β}
    (hLower : (items.flatMap pieces)[index]? = some lower)
    (hUpper : (items.flatMap pieces)[index + 1]? = some upper) :
    FlatMapAdjacentOrigin items pieces index lower upper := by
  induction items generalizing index with
  | nil => simp at hLower
  | cons first rest ih =>
    rw [List.flatMap_cons] at hLower hUpper
    by_cases hInside : index + 1 < (pieces first).length
    · refine .inside [] first rest index rfl (by simp) ?_ ?_
      · simpa only [List.getElem?_append_left (by omega : index < (pieces first).length)] using hLower
      · simpa only [List.getElem?_append_left hInside] using hUpper
    · by_cases hFirst : index < (pieces first).length
      · have hEnd : index + 1 = (pieces first).length := by omega
        have hLast : (pieces first).getLast? = some lower := by
          rw [List.getLast?_eq_getElem?]
          have hIndex : (pieces first).length - 1 = index := by omega
          rw [hIndex]
          simpa only [List.getElem?_append_left hFirst] using hLower
        have hAfter : (rest.flatMap pieces)[0]? = some upper := by
          rw [List.getElem?_append_right (by omega : (pieces first).length ≤ index + 1)] at hUpper
          simpa only [hEnd, Nat.sub_self] using hUpper
        cases rest with
        | nil => simp at hAfter
        | cons next tail =>
          have hNextNonempty := hNonempty next (by simp)
          have hHead : (pieces next).head? = some upper := by
            rw [← List.head?_eq_getElem?, List.flatMap_cons,
              List.head?_append_of_ne_nil _ hNextNonempty] at hAfter
            exact hAfter
          exact .seam [] first next tail rfl (by simp; omega) hLast hHead
      · have hLowerTail : (rest.flatMap pieces)[index - (pieces first).length]? = some lower := by
          simpa only [List.getElem?_append_right (by omega : (pieces first).length ≤ index)] using hLower
        have hUpperTail : (rest.flatMap pieces)[(index - (pieces first).length) + 1]? = some upper := by
          have hIndex : index + 1 - (pieces first).length = (index - (pieces first).length) + 1 := by omega
          simpa only [List.getElem?_append_right (by omega : (pieces first).length ≤ index + 1),
            hIndex] using hUpper
        have hOrigin := ih (fun item hm => hNonempty item (List.mem_cons_of_mem first hm))
          hLowerTail hUpperTail
        cases hOrigin with
        | inside before item after localIndex hSplit hPosition hLow hUp =>
          refine .inside (first :: before) item after localIndex ?_ ?_ hLow hUp
          · simp only [List.cons_append, hSplit]
          · simp only [List.flatMap_cons, List.length_append]
            omega
        | seam before lowItem highItem after hSplit hPosition hLow hUp =>
          refine .seam (first :: before) lowItem highItem after ?_ ?_ hLow hUp
          · simp only [List.cons_append, hSplit]
          · have hPieceNonempty : pieces lowItem ≠ [] := by
              apply hNonempty lowItem
              simp only [List.mem_cons]
              right
              rw [hSplit]
              simp
            have hPiecePositive : 0 < (pieces lowItem).length := List.length_pos_iff.mpr hPieceNonempty
            simp only [List.flatMap_cons, List.length_append]
            omega

/-- The five possible positions of a pair in one real ascending segment.
The fill may be empty; in that case the marker meets the contour directly. -/
inductive SegmentAdjacentOrigin (marker : Cell) (fill path : List Cell)
    (index : Nat) (lower upper : Cell) : Prop where
  | marker_fill (position : index = 0) (lower_eq : lower = marker)
      (upper_read : fill.head? = some upper) :
      SegmentAdjacentOrigin marker fill path index lower upper
  | marker_contour (position : index = 0) (lower_eq : lower = marker)
      (fill_empty : fill = []) (upper_read : path.head? = some upper) :
      SegmentAdjacentOrigin marker fill path index lower upper
  | fill_inside (localIndex : Nat) (position : index = 1 + localIndex)
      (lower_read : fill[localIndex]? = some lower)
      (upper_read : fill[localIndex + 1]? = some upper) :
      SegmentAdjacentOrigin marker fill path index lower upper
  | fill_contour (fill_nonempty : fill ≠ []) (position : index = fill.length)
      (lower_read : fill.getLast? = some lower) (upper_read : path.head? = some upper) :
      SegmentAdjacentOrigin marker fill path index lower upper
  | contour_inside (localIndex : Nat) (position : index = 1 + fill.length + localIndex)
      (lower_read : path[localIndex]? = some lower)
      (upper_read : path[localIndex + 1]? = some upper) :
      SegmentAdjacentOrigin marker fill path index lower upper

theorem segment_adjacent_origin (marker : Cell) (fill path : List Cell)
    {index : Nat} {lower upper : Cell}
    (hLower : ([marker] ++ fill ++ path)[index]? = some lower)
    (hUpper : ([marker] ++ fill ++ path)[index + 1]? = some upper) :
    SegmentAdjacentOrigin marker fill path index lower upper := by
  cases index with
  | zero =>
    have hLowerEq : lower = marker := by simpa using hLower.symm
    cases hFill : fill with
    | nil =>
      exact .marker_contour rfl hLowerEq rfl (by simpa [hFill, ← List.head?_eq_getElem?] using hUpper)
    | cons first rest =>
      have hUpperEq : first = upper := by simpa [hFill] using hUpper
      exact .marker_fill rfl hLowerEq (by simp only [List.head?_cons, hUpperEq])
  | succ localIndex =>
    have hLow : (fill ++ path)[localIndex]? = some lower := by
      simpa only [List.singleton_append, List.cons_append, List.nil_append, List.getElem?_cons_succ] using hLower
    have hUp : (fill ++ path)[localIndex + 1]? = some upper := by
      simpa only [List.singleton_append, List.cons_append, List.nil_append, Nat.succ_add,
        List.getElem?_cons_succ] using hUpper
    by_cases hInside : localIndex + 1 < fill.length
    · exact .fill_inside localIndex (by omega)
        (by simpa only [List.getElem?_append_left (by omega : localIndex < fill.length)] using hLow)
        (by simpa only [List.getElem?_append_left hInside] using hUp)
    · by_cases hFirst : localIndex < fill.length
      · have hPosition : localIndex + 1 = fill.length := by omega
        have hLast : fill.getLast? = some lower := by
          rw [List.getLast?_eq_getElem?]
          have hIndex : fill.length - 1 = localIndex := by omega
          rw [hIndex]
          simpa only [List.getElem?_append_left hFirst] using hLow
        have hHead : path.head? = some upper := by
          rw [List.getElem?_append_right (by omega : fill.length ≤ localIndex + 1)] at hUp
          simpa only [hPosition, Nat.sub_self, ← List.head?_eq_getElem?] using hUp
        exact .fill_contour (List.length_pos_iff.mp (by omega)) hPosition hLast hHead
      · have hNextIndex : localIndex + 1 - fill.length = (localIndex - fill.length) + 1 := by omega
        exact .contour_inside (localIndex - fill.length) (by omega)
          (by simpa only [List.getElem?_append_right (by omega : fill.length ≤ localIndex)] using hLow)
          (by simpa only [List.getElem?_append_right (by omega : fill.length ≤ localIndex + 1),
            hNextIndex] using hUp)

/-- Exhaustive five-way provenance inside the actual sort of one executed
segment. The marker and contour are real executable returns; the fill is
the proved exact ascending presentation of its real fill return. -/
theorem copySegment_adjacent_origin {mountain : Mountain} (hValid : MountainValid mountain)
    {sources : Column} {references : List Ref} {sourceColumn shift rootColumn sourceIndex : Nat}
    (hSources : mountain[sourceColumn]? = some sources) (hSourcePositive : 0 < sourceColumn)
    (hDestination : sourceColumn + shift ≤ mountain.size) (hTop : TopOne sources)
    (markerIndices : List Nat) (s : MarkerCopyData mountain sources references shift sourceIndex)
    (hParentPower : ColumnPowerSteps s.parentNodes) {lowIndex : Nat} {lowCell : Cell}
    (hParentLow : s.parentNodes[lowIndex]? = some lowCell)
    (hParentLowRow : lowCell.row = s.current.row) {result : List Cell}
    (hRun : copySegment mountain sources references sourceColumn markerIndices shift rootColumn sourceIndex =
      .ok result) {index : Nat} {lower upper : Cell}
    (hLower : (finishSort result)[index]? = some lower)
    (hUpper : (finishSort result)[index + 1]? = some upper) :
    ∃ copied path,
      copyEdge mountain ⟨sourceColumn, sourceIndex⟩ shift rootColumn s.current.row = .ok copied ∧
      contour mountain sourceColumn markerIndices shift rootColumn sourceIndex s.targetCell.row s.current
        (sources.toList.drop (sourceIndex + 1)) = .ok path ∧
      SegmentAdjacentOrigin copied
        (fillCellsAscending s.parentNodes (s.sourceParent.column + shift) s.current.row s.targetCell.row)
        path index lower upper := by
  obtain ⟨copied, path, hCopy, hContour, hSorted⟩ := copySegment_sorted_splice hValid hSources
    hSourcePositive hDestination hTop markerIndices s hParentPower hParentLow hParentLowRow hRun
  rw [hSorted] at hLower hUpper
  exact ⟨copied, path, hCopy, hContour, segment_adjacent_origin copied _ path hLower hUpper⟩

/-- A complete actual output-pair classification. Every stored shape is
tied to its own original cell; the cross-segment case records source
marker adjacency and excludes every intervening marked source index. -/
inductive CopiedAdjacentOrigin {mountain : Mountain} {marked : Array (List Ref)}
    {references : List Ref} {sourceColumn shift rootColumn : Nat}
    (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)
    (index : Nat) (lower upper : Cell) : Prop where
  | inside (before : List Ref) (marker : Ref) (after : List Ref) (localIndex : Nat)
      (originalLower originalUpper : Cell)
      (member : marker ∈ d.bucket)
      (split : d.bucket.reverse = before ++ marker :: after)
      (position : index = (before.flatMap (fun entry => finishSort (d.segment entry))).length + localIndex)
      (lower_read : (finishSort (d.segment marker))[localIndex]? = some originalLower)
      (upper_read : (finishSort (d.segment marker))[localIndex + 1]? = some originalUpper)
      (lower_shape : SameShape originalLower lower)
      (upper_shape : SameShape originalUpper upper) :
      CopiedAdjacentOrigin d index lower upper
  | seam (before : List Ref) (lowMarker highMarker : Ref) (after : List Ref)
      (originalLower originalUpper : Cell)
      (low_member : lowMarker ∈ d.bucket) (high_member : highMarker ∈ d.bucket)
      (split : d.bucket.reverse = before ++ lowMarker :: highMarker :: after)
      (marker_order : lowMarker.index < highMarker.index)
      (no_between : ∀ marker ∈ d.bucket,
        ¬ (lowMarker.index < marker.index ∧ marker.index < highMarker.index))
      (position : index = (before.flatMap (fun entry => finishSort (d.segment entry))).length +
        (finishSort (d.segment lowMarker)).length - 1)
      (lower_read : (finishSort (d.segment lowMarker)).getLast? = some originalLower)
      (upper_read : (finishSort (d.segment highMarker)).head? = some originalUpper)
      (lower_shape : SameShape originalLower lower)
      (upper_shape : SameShape originalUpper upper) :
      CopiedAdjacentOrigin d index lower upper

namespace ColumnCopyData

variable {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
  {sourceColumn shift rootColumn : Nat}
  (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)

theorem adjacent_markers_of_split {before after : List Ref} {lowMarker highMarker : Ref}
    (hSplit : d.bucket.reverse = before ++ lowMarker :: highMarker :: after) :
    lowMarker ∈ d.bucket ∧ highMarker ∈ d.bucket ∧ lowMarker.index < highMarker.index ∧
      ∀ marker ∈ d.bucket, ¬ (lowMarker.index < marker.index ∧ marker.index < highMarker.index) := by
  have hAscending : d.bucket.reverse.Pairwise (fun a b => a.index < b.index) :=
    List.pairwise_reverse.mpr d.marker_order
  have hAdjacent := List.isChain_iff_forall_rel_of_append_cons_cons.mp
    (ordered_markers_adjacent hAscending) hSplit
  exact ⟨List.mem_reverse.mp (by rw [hSplit]; simp),
    List.mem_reverse.mp (by rw [hSplit]; simp), hAdjacent.1,
    fun marker hm => hAdjacent.2 marker (List.mem_reverse.mpr hm)⟩

section ParentInputs

variable
  (hParentPower : ∀ marker (hm : marker ∈ d.bucket),
    ColumnPowerSteps (d.marker_data marker hm).parentNodes)
  (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (index : Nat) (cell : Cell),
    (d.marker_data marker hm).parentNodes[index]? = some cell ∧
      cell.row = (d.marker_data marker hm).current.row)
  (hNoPremature : NoPrematureOne d.sources)

include hParentPower hParentLow

/-- The inside branch of `copyColumn_adjacent_origin` can be refined to
the five executable segment origins without any further output premise. -/
theorem sorted_segment_adjacent_origin {marker : Ref} (hm : marker ∈ d.bucket)
    {index : Nat} {lower upper : Cell}
    (hLower : (finishSort (d.segment marker))[index]? = some lower)
    (hUpper : (finishSort (d.segment marker))[index + 1]? = some upper) :
    ∃ copied path,
      copyEdge mountain ⟨sourceColumn, marker.index⟩ shift rootColumn
        (d.marker_data marker hm).current.row = .ok copied ∧
      contour mountain sourceColumn (d.bucket.map Ref.index) shift rootColumn marker.index
        (d.marker_data marker hm).targetCell.row (d.marker_data marker hm).current
        (d.sources.toList.drop (marker.index + 1)) = .ok path ∧
      SegmentAdjacentOrigin copied
        (fillCellsAscending (d.marker_data marker hm).parentNodes
          ((d.marker_data marker hm).sourceParent.column + shift)
          (d.marker_data marker hm).current.row (d.marker_data marker hm).targetCell.row)
        path index lower upper := by
  obtain ⟨lowIndex, lowCell, hLow, hLowRow⟩ := hParentLow marker hm
  exact copySegment_adjacent_origin d.ambient_valid d.source_column d.source_nonzero d.destination.le
    d.source_top (d.bucket.map Ref.index) (d.marker_data marker hm)
    (hParentPower marker hm) hLow hLowRow (d.segment_run hm) hLower hUpper

include hNoPremature

/-- Every actual consecutive output pair has one of the two source-piece
origins. The index is the caller's actual output index, and shape witnesses
are obtained at that same index after the real sort and backfill. -/
theorem copyColumn_adjacent_origin {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {index : Nat} {lower upper : Cell}
    (hLower : column[index]? = some lower) (hUpper : column[index + 1]? = some upper) :
    CopiedAdjacentOrigin d index lower upper := by
  have hFinish := d.copyColumn_eq_finish.symm.trans hRun
  have hShape := (finish_success_spec hFinish).1
  change ColumnShape (finishSort d.candidates) column at hShape
  rw [d.finishSort_candidates_cells hParentPower hParentLow hNoPremature] at hShape
  obtain ⟨originalLower, hOriginalLower, hLowerShape⟩ := hShape.getElem hLower
  obtain ⟨originalUpper, hOriginalUpper, hUpperShape⟩ := hShape.getElem hUpper
  have hNonempty : ∀ marker ∈ d.bucket.reverse, finishSort (d.segment marker) ≠ [] := by
    intro marker hm hEmpty
    apply d.sorted_segment_nonempty hParentPower hParentLow (List.mem_reverse.mp hm)
    simp only [sortedSegmentRows, hEmpty, List.map_nil]
  have hOrigin := flatMap_adjacent_origin d.bucket.reverse (fun marker => finishSort (d.segment marker))
    hNonempty hOriginalLower hOriginalUpper
  cases hOrigin with
  | inside before marker after localIndex hSplit hPosition hLow hUp =>
    exact .inside before marker after localIndex originalLower originalUpper
      (List.mem_reverse.mp (by rw [hSplit]; simp)) hSplit hPosition hLow hUp hLowerShape hUpperShape
  | seam before lowMarker highMarker after hSplit hPosition hLow hUp =>
    obtain ⟨hLowMember, hHighMember, hOrder, hNoBetween⟩ := d.adjacent_markers_of_split hSplit
    exact .seam before lowMarker highMarker after originalLower originalUpper
      hLowMember hHighMember hSplit hOrder hNoBetween hPosition hLow hUp hLowerShape hUpperShape

end ParentInputs

end ColumnCopyData

end OmegaY.Expansion

#print axioms OmegaY.Expansion.flatMap_adjacent_origin
#print axioms OmegaY.Expansion.segment_adjacent_origin
#print axioms OmegaY.Expansion.copySegment_adjacent_origin
#print axioms OmegaY.Expansion.ColumnCopyData.sorted_segment_adjacent_origin
#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_adjacent_origin
