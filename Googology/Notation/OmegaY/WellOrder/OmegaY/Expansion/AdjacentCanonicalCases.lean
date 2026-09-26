/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/AdjacentCanonicalCases.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/AdjacentCanonicalCases.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.AdjacentOrigin
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.FillContourSeam

set_option backward.do.legacy false

/-! Existing canonical fill certificates are located at the caller's
actual output indices by strict row uniqueness. This removes solved fill
cases from the exhaustive adjacent-origin classification without assuming
normality of the copied output or guessing any numerical parent value. -/

namespace OmegaY.Expansion

open Canonical

/-- A canonical certificate for precisely the given actual output pair. -/
def CopiedCanonicalAt (mountain : Mountain) (column : Column) (index : Nat)
    (lower upper : Cell) : Prop :=
  ∃ parentRef parent, ∃ step : ActualFillStep mountain column parentRef parent,
    step.position = index ∧ step.lower = lower ∧ step.upper = upper

theorem CopiedCanonicalAt.parent_geometry {mountain : Mountain} {column : Column}
    {index : Nat} {lower upper : Cell} (h : CopiedCanonicalAt mountain column index lower upper) :
    ∃ parentRef parent, upper.left = some parentRef ∧
      Canonical.cellAt (mountain.push column) parentRef = .ok parent ∧
      Canonical.findParent (mountain.push column) ⟨mountain.size, index⟩ = .ok parentRef ∧
      upper.row = Row.B lower.row parent.row := by
  obtain ⟨parentRef, parent, step, hPosition, hLower, hUpper⟩ := h
  exact ⟨parentRef, parent, by simpa only [hUpper] using step.upper_left, step.parent_at,
    by simpa only [hPosition] using step.parent_found,
    by simpa only [hLower, hUpper] using step.upper_row⟩

theorem column_read_index_eq_of_row {mountain : Mountain} {c : Nat} {column : Column}
    (hValid : ColumnValid mountain c column) {i j : Nat} {a b : Cell}
    (ha : column[i]? = some a) (hb : column[j]? = some b) (hRow : a.row = b.row) : i = j := by
  rcases lt_trichotomy i j with hlt | he | hgt
  · exact False.elim ((ne_of_lt (hValid.rows_strict _ _ _ _ ha hb hlt)) hRow)
  · exact he
  · exact False.elim ((ne_of_lt (hValid.rows_strict _ _ _ _ hb ha hgt)) hRow.symm)

/-- Matching the lower row locates the entire real step: the upper node
then has the same successor index, not a separately chosen row witness. -/
theorem ActualFillStep.locate {mountain : Mountain} {column : Column} {parentRef : Ref} {parent : Cell}
    (step : ActualFillStep mountain column parentRef parent)
    (hValid : ColumnValid mountain mountain.size column) {index : Nat} {lower upper : Cell}
    (hLower : column[index]? = some lower) (hUpper : column[index + 1]? = some upper)
    (hRow : step.lower.row = lower.row) :
    step.position = index ∧ step.lower = lower ∧ step.upper = upper := by
  have hIndex := column_read_index_eq_of_row hValid step.lower_at hLower hRow
  have hStepLower : column[index]? = some step.lower := by simpa only [hIndex] using step.lower_at
  have hStepUpper : column[index + 1]? = some step.upper := by simpa only [hIndex] using step.upper_at
  exact ⟨hIndex, Option.some.inj (hStepLower.symm.trans hLower),
    Option.some.inj (hStepUpper.symm.trans hUpper)⟩

namespace ColumnCopyData

variable {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
  {sourceColumn shift rootColumn : Nat}
  (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)

include d

private theorem valid_of_actual_copy {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column) :
    ColumnValid mountain mountain.size column := by
  obtain ⟨other, hOther, _, hValid, _, _⟩ := d.copyColumn_valid
  have he : other = column := Except.ok.inj (hOther.symm.trans hRun)
  exact he ▸ hValid

section ParentInputs

variable
  (hParentPower : ∀ marker (hm : marker ∈ d.bucket),
    ColumnPowerSteps (d.marker_data marker hm).parentNodes)
  (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (index : Nat) (cell : Cell),
    (d.marker_data marker hm).parentNodes[index]? = some cell ∧
      cell.row = (d.marker_data marker hm).current.row)
  (hNoPremature : NoPrematureOne d.sources)

include hParentPower hParentLow hNoPremature

/-- Any actual pair whose lower node is a fill rung strictly below the
target is one of the already established canonical fill steps. Rung
membership decides whether to reuse an interior or a parent-interval seam. -/
theorem fill_below_target_canonical_at {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {marker : Ref} (hm : marker ∈ d.bucket) {index : Nat} {lower upper original : Cell}
    (hLower : column[index]? = some lower) (hUpper : column[index + 1]? = some upper)
    (hOriginal : original ∈ fillCellsAscending (d.marker_data marker hm).parentNodes
      ((d.marker_data marker hm).sourceParent.column + shift)
      (d.marker_data marker hm).current.row (d.marker_data marker hm).targetCell.row)
    (hShape : SameShape original lower)
    (hBelow : lower.row < (d.marker_data marker hm).targetCell.row) :
    CopiedCanonicalAt mountain column index lower upper := by
  let s := d.marker_data marker hm
  have hValid := d.valid_of_actual_copy hRun
  obtain ⟨hp, hNodesEq⟩ := Array.getElem?_eq_some_iff.mp s.parent_nodes
  have hParentValid : ColumnValid mountain (s.sourceParent.column + shift) s.parentNodes :=
    hNodesEq ▸ d.ambient_valid _ hp
  have hStrict := fillRowsStrict_of_columnValid hParentValid
  have hMember : original ∈ fillCells s.parentNodes (s.sourceParent.column + shift)
      s.current.row s.targetCell.row :=
    (fillCellsAscending_perm _ _ _ _).mem_iff.mp hOriginal
  obtain ⟨parentIndex, parent, parentUpper, hParent, hParentUpper, hLow, hHigh,
      hParentRow, _, hRung, _, _⟩ := mem_fillCells hStrict s.target_at le_rfl hMember
  obtain ⟨degree, hDegree, hDegreeRow⟩ := Row.mem_fillLadder.mp hRung
  by_cases hInterior : degree + 1 < Row.jump parent.row parentUpper.row
  · obtain ⟨step, hStepLower, _⟩ := d.copyColumn_fill_interior hParentPower hParentLow hNoPremature
      hRun hm hParent hParentUpper ⟨hLow, hHigh⟩ hInterior
    refine ⟨_, _, step, step.locate hValid hLower hUpper ?_⟩
    exact hStepLower.1.symm.trans (hDegreeRow.trans hShape.1)
  · have hDegreeEq : degree = Row.jump parent.row parentUpper.row - 1 := by omega
    have hParentUpperRow : parentUpper.row = original.row := by
      calc
        parentUpper.row = Row.bump parent.row (Row.jump parent.row parentUpper.row - 1) :=
          hParentPower marker hm parentIndex parent parentUpper hParent hParentUpper
        _ = Row.bump parent.row degree := by rw [hDegreeEq]
        _ = original.row := hDegreeRow
    have hUpperBelow : parentUpper.row < s.targetCell.row := by
      rw [hParentUpperRow, hShape.1]
      exact hBelow
    obtain ⟨nextParent, hNextParent, _, _⟩ := fill_successor hStrict s.target_at le_rfl hParentUpper hUpperBelow
    obtain ⟨step, hStepLower, _⟩ := d.copyColumn_fill_seam hParentPower hParentLow hNoPremature
      hRun hm hParent hParentUpper hNextParent ⟨hLow, hHigh⟩
      ⟨hLow.trans hParentRow.le, hUpperBelow⟩
    refine ⟨_, _, step, step.locate hValid hLower hUpper ?_⟩
    exact hStepLower.1.symm.trans (hParentUpperRow.trans hShape.1)

/-- This discharges every `fill_inside` origin at its original output
indices, including an adjacency crossing two eligible parent intervals. -/
theorem fill_inside_canonical_at {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {marker : Ref} (hm : marker ∈ d.bucket) {index localIndex : Nat}
    {lower upper originalLower originalUpper : Cell}
    (hLower : column[index]? = some lower) (hUpper : column[index + 1]? = some upper)
    (hOriginalLower : (fillCellsAscending (d.marker_data marker hm).parentNodes
      ((d.marker_data marker hm).sourceParent.column + shift)
      (d.marker_data marker hm).current.row (d.marker_data marker hm).targetCell.row)[localIndex]? =
      some originalLower)
    (hOriginalUpper : (fillCellsAscending (d.marker_data marker hm).parentNodes
      ((d.marker_data marker hm).sourceParent.column + shift)
      (d.marker_data marker hm).current.row (d.marker_data marker hm).targetCell.row)[localIndex + 1]? =
      some originalUpper)
    (hLowerShape : SameShape originalLower lower) (hUpperShape : SameShape originalUpper upper) :
    CopiedCanonicalAt mountain column index lower upper := by
  let s := d.marker_data marker hm
  have hValid := d.valid_of_actual_copy hRun
  have hPairLt := hValid.rows_strict _ _ _ _ hLower hUpper (Nat.lt_succ_self index)
  obtain ⟨hp, hNodesEq⟩ := Array.getElem?_eq_some_iff.mp s.parent_nodes
  have hParentValid : ColumnValid mountain (s.sourceParent.column + shift) s.parentNodes :=
    hNodesEq ▸ d.ambient_valid _ hp
  have hMember := (fillCellsAscending_perm s.parentNodes (s.sourceParent.column + shift)
    s.current.row s.targetCell.row).mem_iff.mp (List.mem_of_getElem? hOriginalUpper)
  have hBound := (fillCells_row_bounds (fillRowsStrict_of_columnValid hParentValid) s.target_at le_rfl hMember).2
  apply d.fill_below_target_canonical_at hParentPower hParentLow hNoPremature hRun hm hLower hUpper
    (List.mem_of_getElem? hOriginalLower) hLowerShape
  exact hPairLt.trans_le (hUpperShape.1.symm ▸ hBound)

end ParentInputs

end ColumnCopyData

/-- A nonempty actual fill ends at the selected target. Its existing
canonical cap-to-contour certificate is thus the caller's actual pair. -/
theorem ColumnCopyData.prepared_fill_contour_canonical_at {front : List Nat} {last : Nat}
    {p : Preparation front last} {mountain : Mountain} {references : List Ref}
    {sourceColumn shift : Nat}
    (d : ColumnCopyData mountain p.marked references sourceColumn shift p.root.column)
    (hSource : p.reduced[sourceColumn]? = some d.sources)
    (hParentPower : ∀ marker (hm : marker ∈ d.bucket),
      ColumnPowerSteps (d.marker_data marker hm).parentNodes)
    (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (index : Nat) (cell : Cell),
      (d.marker_data marker hm).parentNodes[index]? = some cell ∧
        cell.row = (d.marker_data marker hm).current.row)
    (hNoPremature : NoPrematureOne d.sources) {column : Column}
    (hRun : copyColumn mountain p.marked references sourceColumn shift p.root.column = .ok column)
    {marker : Ref} (hm : marker ∈ d.bucket) {index : Nat} {lower upper original : Cell}
    (hLower : column[index]? = some lower) (hUpper : column[index + 1]? = some upper)
    (hLastFill : (fillCellsAscending (d.marker_data marker hm).parentNodes
      ((d.marker_data marker hm).sourceParent.column + shift)
      (d.marker_data marker hm).current.row (d.marker_data marker hm).targetCell.row).getLast? = some original)
    (hShape : SameShape original lower) : CopiedCanonicalAt mountain column index lower upper := by
  let s := d.marker_data marker hm
  obtain ⟨hp, hNodesEq⟩ := Array.getElem?_eq_some_iff.mp s.parent_nodes
  have hParentValid : ColumnValid mountain (s.sourceParent.column + shift) s.parentNodes :=
    hNodesEq ▸ d.ambient_valid _ hp
  have hStrict := fillRowsStrict_of_columnValid hParentValid
  have hMember : original ∈ fillCells s.parentNodes (s.sourceParent.column + shift)
      s.current.row s.targetCell.row :=
    (fillCellsAscending_perm _ _ _ _).mem_iff.mp (List.mem_of_getLast? hLastFill)
  have hBounds := fillCells_row_bounds hStrict s.target_at le_rfl hMember
  have hRaised : s.current.row < s.targetCell.row := hBounds.1.trans_le hBounds.2
  obtain ⟨lowIndex, lowCell, hLow, hLowRow⟩ := hParentLow marker hm
  obtain ⟨parentIndex, parent, before, _, _, hFill⟩ := fillCellsAscending_last hStrict
    (hParentPower marker hm) hLow s.target_at (by simpa only [hLowRow] using hRaised)
    (column := s.sourceParent.column + shift)
  rw [hLowRow] at hFill
  have hOriginal : original = ⟨s.targetCell.row, 0, some ⟨s.sourceParent.column + shift, parentIndex⟩⟩ := by
    have hLast := hLastFill
    change (fillCellsAscending s.parentNodes (s.sourceParent.column + shift)
      s.current.row s.targetCell.row).getLast? = some original at hLast
    rw [hFill] at hLast
    simpa using hLast.symm
  obtain ⟨step, hStepLower, _⟩ := d.prepared_fill_contour_seam hSource hParentPower hParentLow
    hNoPremature hRun hm hRaised
  refine ⟨_, _, step, step.locate (d.valid_of_actual_copy hRun) hLower hUpper ?_⟩
  exact hStepLower.trans ((congrArg Cell.row hOriginal).symm.trans hShape.1)

/-- Complete executed-segment provenance retained for an unresolved pair.
All indices refer either to the real sorted source segment or to the
caller's actual output, with their offset explicitly recorded. -/
structure ExecutedSegmentPair {mountain : Mountain} {marked : Array (List Ref)}
    {references : List Ref} {sourceColumn shift rootColumn : Nat}
    (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)
    (index : Nat) (lower upper : Cell) where
  marker : Ref
  member : marker ∈ d.bucket
  before : List Ref
  after : List Ref
  localIndex : Nat
  originalLower : Cell
  originalUpper : Cell
  copied : Cell
  path : List Cell
  bucket_split : d.bucket.reverse = before ++ marker :: after
  position : index = (before.flatMap (fun entry => finishSort (d.segment entry))).length + localIndex
  lower_sorted : (finishSort (d.segment marker))[localIndex]? = some originalLower
  upper_sorted : (finishSort (d.segment marker))[localIndex + 1]? = some originalUpper
  lower_shape : SameShape originalLower lower
  upper_shape : SameShape originalUpper upper
  copy_run : copyEdge mountain ⟨sourceColumn, marker.index⟩ shift rootColumn
    (d.marker_data marker member).current.row = .ok copied
  contour_run : contour mountain sourceColumn (d.bucket.map Ref.index) shift rootColumn marker.index
    (d.marker_data marker member).targetCell.row (d.marker_data marker member).current
    (d.sources.toList.drop (marker.index + 1)) = .ok path

def ExecutedSegmentPair.fill {mountain : Mountain} {marked : Array (List Ref)}
    {references : List Ref} {sourceColumn shift rootColumn : Nat}
    {d : ColumnCopyData mountain marked references sourceColumn shift rootColumn}
    {index : Nat} {lower upper : Cell} (pair : ExecutedSegmentPair d index lower upper) : List Cell :=
  fillCellsAscending (d.marker_data pair.marker pair.member).parentNodes
    ((d.marker_data pair.marker pair.member).sourceParent.column + shift)
    (d.marker_data pair.marker pair.member).current.row (d.marker_data pair.marker pair.member).targetCell.row

structure ExecutedSegmentSeam {mountain : Mountain} {marked : Array (List Ref)}
    {references : List Ref} {sourceColumn shift rootColumn : Nat}
    (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)
    (index : Nat) (lower upper : Cell) where
  lowMarker : Ref
  highMarker : Ref
  low_member : lowMarker ∈ d.bucket
  high_member : highMarker ∈ d.bucket
  before : List Ref
  after : List Ref
  originalLower : Cell
  originalUpper : Cell
  bucket_split : d.bucket.reverse = before ++ lowMarker :: highMarker :: after
  marker_order : lowMarker.index < highMarker.index
  no_between : ∀ marker ∈ d.bucket, ¬ (lowMarker.index < marker.index ∧ marker.index < highMarker.index)
  position : index = (before.flatMap (fun entry => finishSort (d.segment entry))).length +
    (finishSort (d.segment lowMarker)).length - 1
  lower_last : (finishSort (d.segment lowMarker)).getLast? = some originalLower
  upper_head : (finishSort (d.segment highMarker)).head? = some originalUpper
  lower_shape : SameShape originalLower lower
  upper_shape : SameShape originalUpper upper

/-- Exactly the four remaining origin classes. The canonical fill interior
and the raised fill-to-contour seam have been removed by proved search
certificates, rather than by adding them to an output invariant. -/
inductive RemainingCopiedOrigin {mountain : Mountain} {marked : Array (List Ref)}
    {references : List Ref} {sourceColumn shift rootColumn : Nat}
    (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)
    (index : Nat) (lower upper : Cell) : Prop where
  | marker_fill (pair : ExecutedSegmentPair d index lower upper)
      (position : pair.localIndex = 0) (lower_eq : pair.originalLower = pair.copied)
      (upper_head : pair.fill.head? = some pair.originalUpper) :
      RemainingCopiedOrigin d index lower upper
  | marker_contour (pair : ExecutedSegmentPair d index lower upper)
      (position : pair.localIndex = 0) (lower_eq : pair.originalLower = pair.copied)
      (fill_empty : pair.fill = []) (upper_head : pair.path.head? = some pair.originalUpper) :
      RemainingCopiedOrigin d index lower upper
  | contour_inside (pair : ExecutedSegmentPair d index lower upper) (pathIndex : Nat)
      (position : pair.localIndex = 1 + pair.fill.length + pathIndex)
      (lower_read : pair.path[pathIndex]? = some pair.originalLower)
      (upper_read : pair.path[pathIndex + 1]? = some pair.originalUpper) :
      RemainingCopiedOrigin d index lower upper
  | cross_segment (seam : ExecutedSegmentSeam d index lower upper) :
      RemainingCopiedOrigin d index lower upper

/-- Every actual prepared-column pair is either proved canonical at its
actual index or belongs to one of the four explicitly remaining classes. -/
theorem ColumnCopyData.prepared_adjacent_canonical_cases {front : List Nat} {last : Nat}
    {p : Preparation front last} {mountain : Mountain} {references : List Ref}
    {sourceColumn shift : Nat}
    (d : ColumnCopyData mountain p.marked references sourceColumn shift p.root.column)
    (hSource : p.reduced[sourceColumn]? = some d.sources)
    (hParentPower : ∀ marker (hm : marker ∈ d.bucket),
      ColumnPowerSteps (d.marker_data marker hm).parentNodes)
    (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (index : Nat) (cell : Cell),
      (d.marker_data marker hm).parentNodes[index]? = some cell ∧
        cell.row = (d.marker_data marker hm).current.row)
    (hNoPremature : NoPrematureOne d.sources) {column : Column}
    (hRun : copyColumn mountain p.marked references sourceColumn shift p.root.column = .ok column)
    {index : Nat} {lower upper : Cell}
    (hLower : column[index]? = some lower) (hUpper : column[index + 1]? = some upper) :
    CopiedCanonicalAt mountain column index lower upper ∨ RemainingCopiedOrigin d index lower upper := by
  have hOrigin := d.copyColumn_adjacent_origin hParentPower hParentLow hNoPremature hRun hLower hUpper
  cases hOrigin with
  | inside before marker after localIndex originalLower originalUpper hm hSplit hPosition hLow hUp hLowShape hUpShape =>
    obtain ⟨copied, path, hCopy, hContour, hSegment⟩ :=
      d.sorted_segment_adjacent_origin hParentPower hParentLow hm hLow hUp
    let pair : ExecutedSegmentPair d index lower upper := {
      marker := marker
      member := hm
      before := before
      after := after
      localIndex := localIndex
      originalLower := originalLower
      originalUpper := originalUpper
      copied := copied
      path := path
      bucket_split := hSplit
      position := hPosition
      lower_sorted := hLow
      upper_sorted := hUp
      lower_shape := hLowShape
      upper_shape := hUpShape
      copy_run := hCopy
      contour_run := hContour }
    cases hSegment with
    | marker_fill hZero hEq hHead => exact Or.inr (.marker_fill pair hZero hEq hHead)
    | marker_contour hZero hEq hEmpty hHead => exact Or.inr (.marker_contour pair hZero hEq hEmpty hHead)
    | fill_inside fillIndex _ hFillLow hFillUp =>
      exact Or.inl (d.fill_inside_canonical_at hParentPower hParentLow hNoPremature hRun hm
        hLower hUpper hFillLow hFillUp hLowShape hUpShape)
    | fill_contour _ _ hLastFill _ =>
      exact Or.inl (d.prepared_fill_contour_canonical_at hSource hParentPower hParentLow hNoPremature
        hRun hm hLower hUpper hLastFill hLowShape)
    | contour_inside pathIndex hPathPosition hPathLow hPathUp =>
      exact Or.inr (.contour_inside pair pathIndex hPathPosition hPathLow hPathUp)
  | seam before lowMarker highMarker after originalLower originalUpper hLowMember hHighMember
      hSplit hOrder hNoBetween hPosition hLow hUp hLowShape hUpShape =>
    exact Or.inr (.cross_segment {
      lowMarker := lowMarker
      highMarker := highMarker
      low_member := hLowMember
      high_member := hHighMember
      before := before
      after := after
      originalLower := originalLower
      originalUpper := originalUpper
      bucket_split := hSplit
      marker_order := hOrder
      no_between := hNoBetween
      position := hPosition
      lower_last := hLow
      upper_head := hUp
      lower_shape := hLowShape
      upper_shape := hUpShape })

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ActualFillStep.locate
#print axioms OmegaY.Expansion.CopiedCanonicalAt.parent_geometry
#print axioms OmegaY.Expansion.ColumnCopyData.fill_below_target_canonical_at
#print axioms OmegaY.Expansion.ColumnCopyData.fill_inside_canonical_at
#print axioms OmegaY.Expansion.ColumnCopyData.prepared_fill_contour_canonical_at
#print axioms OmegaY.Expansion.ColumnCopyData.prepared_adjacent_canonical_cases
