/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/FillCanonical.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/FillCanonical.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.FillAdjacent
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.FinishAdjacent
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.ReferenceLadder

set_option backward.do.legacy false

/-!
# Actual canonical steps inside copied reference filling

The output neighbours come from the executable fill/sort bridge. Positive
differences come from actual backfill. The numerical parent is then proved
by a first-candidate hit, without assuming copied-column normality.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- The local fields of a real canonical difference step at fresh output
indices. The parent is the explicit existing fill-column reference. -/
structure ActualFillStep (mountain : Mountain) (column : Column) (parentRef : Ref) (parent : Cell) where
  position : Nat
  lower : Cell
  upper : Cell
  lower_at : column[position]? = some lower
  upper_at : column[position + 1]? = some upper
  position_positive : 0 < position
  lower_large : 1 < lower.value
  parent_left : parentRef.column < mountain.size
  parent_at : Canonical.cellAt (mountain.push column) parentRef = .ok parent
  parent_found : Canonical.findParent (mountain.push column) ⟨mountain.size, position⟩ = .ok parentRef
  upper_row : upper.row = Row.B lower.row parent.row
  upper_value : upper.value = lower.value - parent.value
  upper_left : upper.left = some parentRef

private theorem frame_upper_of_refs {F : Frame} {before after : F.Node} {column index : Nat}
    (hBefore : Frame.ref before = ⟨column, index⟩)
    (hAfter : Frame.ref after = ⟨column, index + 1⟩) : F.upper before = some after := by
  rcases before with ⟨c, i⟩
  rcases after with ⟨d, j⟩
  simp only [Frame.ref, Ref.mk.injEq] at hBefore hAfter
  have hc : d = c := Fin.ext (hAfter.1.trans hBefore.1.symm)
  subst d
  have hBound : i.val + 1 < F.length c := by have := j.isLt; omega
  simp only [Frame.upper, hBound, ↓reduceDIte, Option.some.injEq]
  apply Executable.ref_injective F
  simp only [Frame.ref, Ref.mk.injEq]
  exact ⟨trivial, by omega⟩

private theorem interior_search_of_reads {mountain : Mountain}
    (hOrdered : (Frame.ofMountain mountain).Ordered)
    {source : Ref} {current parent parentUpper : Cell} {parentColumn parentIndex degree scale surplus : Nat}
    (hCurrent : Canonical.cellAt mountain source = .ok current)
    (hParent : Canonical.cellAt mountain ⟨parentColumn, parentIndex⟩ = .ok parent)
    (hParentUpper : Canonical.cellAt mountain ⟨parentColumn, parentIndex + 1⟩ = .ok parentUpper)
    (hLeft : current.left = some ⟨parentColumn, parentIndex⟩)
    (hParentRow : parentUpper.row = Row.bump parent.row scale)
    (hRow : current.row = Row.bump parent.row degree) (hDegree : degree < scale)
    (hPositive : 0 < parent.value) (hSurplus : 0 < surplus)
    (hValue : current.value = surplus + parent.value) :
    Canonical.findParent mountain source = .ok ⟨parentColumn, parentIndex⟩ := by
  obtain ⟨u, hURef, hUCell⟩ := Canonical.frame_node_of_cellAt hCurrent
  obtain ⟨p, hPRef, hPCell⟩ := Canonical.frame_node_of_cellAt hParent
  obtain ⟨pUpper, hPURef, hPUCell⟩ := Canonical.frame_node_of_cellAt hParentUpper
  have hUpper := frame_upper_of_refs hPRef hPURef
  have hFound := Executable.reference_interior_findParent hOrdered
    (u := u) (parent := p) (parentUpper := pUpper)
    (by rw [hUCell, hPRef]; exact hLeft) hUpper
    (by simpa only [Frame.height, hPUCell, hPCell] using hParentRow)
    (by simpa only [Frame.height, hUCell, hPCell] using hRow) hDegree
    (by simpa only [Frame.value, hPCell] using hPositive) hSurplus
    (by simpa only [Frame.value, hUCell, hPCell] using hValue)
  simpa only [hURef, hPRef] using hFound

private theorem endpoint_search_of_reads {mountain : Mountain}
    (hOrdered : (Frame.ofMountain mountain).Ordered)
    {source : Ref} {current parent parentUpper : Cell} {parentColumn parentIndex scale surplus : Nat}
    (hCurrent : Canonical.cellAt mountain source = .ok current)
    (hParent : Canonical.cellAt mountain ⟨parentColumn, parentIndex⟩ = .ok parent)
    (hParentUpper : Canonical.cellAt mountain ⟨parentColumn, parentIndex + 1⟩ = .ok parentUpper)
    (hLeft : current.left = some ⟨parentColumn, parentIndex⟩)
    (hParentRow : parentUpper.row = Row.bump parent.row scale)
    (hRow : current.row = Row.bump parent.row scale)
    (hPositive : 0 < parentUpper.value) (hSurplus : 0 < surplus)
    (hValue : current.value = surplus + parentUpper.value) :
    Canonical.findParent mountain source = .ok ⟨parentColumn, parentIndex + 1⟩ := by
  obtain ⟨u, hURef, hUCell⟩ := Canonical.frame_node_of_cellAt hCurrent
  obtain ⟨p, hPRef, hPCell⟩ := Canonical.frame_node_of_cellAt hParent
  obtain ⟨pUpper, hPURef, hPUCell⟩ := Canonical.frame_node_of_cellAt hParentUpper
  have hUpper := frame_upper_of_refs hPRef hPURef
  have hFound := Executable.reference_endpoint_findParent hOrdered
    (u := u) (parent := p) (parentUpper := pUpper)
    (by rw [hUCell, hPRef]; exact hLeft) hUpper
    (by simpa only [Frame.height, hPUCell, hPCell] using hParentRow)
    (by simpa only [Frame.height, hUCell, hPCell] using hRow)
    (by simpa only [Frame.value, hPUCell] using hPositive) hSurplus
    (by simpa only [Frame.value, hUCell, hPUCell] using hValue)
  simpa only [hURef, hPURef] using hFound

private theorem positive_position {mountain : Mountain} {column : Column}
    (hValid : ColumnValid mountain mountain.size column) {position : Nat} {lower : Cell}
    (hLower : column[position]? = some lower) (hRow : 0 < lower.row) : 0 < position := by
  by_contra hn
  have he : position = 0 := by omega
  subst position
  have hCell : lower = phantom := Option.some.inj (hLower.symm.trans hValid.phantom)
  simp only [hCell, phantom, lt_self_iff_false] at hRow

/-- All numerical information is extracted from the actual finisher and
the specified upper stored leg, before proving any numerical search. -/
private theorem adjacent_values_at_parent {mountain : Mountain} {column : Column}
    (hFinished : FinishedColumn mountain column) (hValid : ColumnValid mountain mountain.size column)
    {position : Nat} {lower upper parent : Cell} {parentRef : Ref}
    (hLower : column[position]? = some lower) (hUpper : column[position + 1]? = some upper)
    (hRow : 0 < lower.row) (hLeft : upper.left = some parentRef)
    (hParent : Canonical.cellAt (mountain.push column) parentRef = .ok parent) :
    0 < position ∧ 1 < lower.value ∧ parentRef.column < mountain.size ∧
      0 < parent.value ∧ 0 < upper.value ∧ lower.value = upper.value + parent.value ∧
      upper.value = lower.value - parent.value := by
  have hPosition := positive_position hValid hLower hRow
  obtain ⟨hLarge, ref, actualParent, hActualLeft, hActualParent, hLeftward, hPositive, hSum, hDifference⟩ :=
    hFinished.adjacent_difference hValid hLower hUpper hPosition
  have hRefEq : ref = parentRef := Option.some.inj (hActualLeft.symm.trans hLeft)
  subst ref
  have hParentEq : actualParent = parent := Except.ok.inj (hActualParent.symm.trans hParent)
  subst actualParent
  exact ⟨hPosition, hLarge, hLeftward, hPositive,
    hValid.real_positive (position + 1) upper hUpper (by omega), hSum, hDifference⟩

namespace ColumnCopyData

variable {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
  {sourceColumn shift rootColumn : Nat}
  (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)

include d

private theorem actual_copy_facts {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column) :
    FinishedColumn mountain column ∧ ColumnValid mountain mountain.size column ∧
      MountainValid (mountain.push column) := by
  obtain ⟨other, hOther, hFinished, hValid, _, hMountain⟩ := d.copyColumn_valid
  have he : other = column := Except.ok.inj (hOther.symm.trans hRun)
  subst other
  exact ⟨hFinished, hValid, hMountain⟩

section ParentInputs

variable
  (hParentPower : ∀ marker (hm : marker ∈ d.bucket),
    ColumnPowerSteps (d.marker_data marker hm).parentNodes)
  (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (index : Nat) (cell : Cell),
    (d.marker_data marker hm).parentNodes[index]? = some cell ∧
      cell.row = (d.marker_data marker hm).current.row)
  (hNoPremature : NoPrematureOne d.sources)

include hParentPower hParentLow hNoPremature

/-- The actual output step between two interior rungs satisfies the real
canonical numerical search and exact B/difference rule. Only actual input
parent reads and eligibility are supplied; output adjacency is derived. -/
theorem copyColumn_fill_interior {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {marker : Ref} (hm : marker ∈ d.bucket) {parentIndex degree : Nat} {parent parentUpper : Cell}
    (hParent : (d.marker_data marker hm).parentNodes[parentIndex]? = some parent)
    (hParentUpper : (d.marker_data marker hm).parentNodes[parentIndex + 1]? = some parentUpper)
    (hEligible : (d.marker_data marker hm).current.row ≤ parent.row ∧
      parent.row < (d.marker_data marker hm).targetCell.row)
    (hDegree : degree + 1 < Row.jump parent.row parentUpper.row) :
    ∃ step : ActualFillStep mountain column
        ⟨(d.marker_data marker hm).sourceParent.column + shift, parentIndex⟩ parent,
      SameShape (referenceRung parent.row ((d.marker_data marker hm).sourceParent.column + shift)
        parentIndex degree) step.lower ∧
      SameShape (referenceRung parent.row ((d.marker_data marker hm).sourceParent.column + shift)
        parentIndex (degree + 1)) step.upper := by
  let s := d.marker_data marker hm
  obtain ⟨hFinished, hColumnValid, hMountainValid⟩ := d.actual_copy_facts hRun
  obtain ⟨hLowRung, hHighRung⟩ := fillCellsAscending_interior
    (column := s.sourceParent.column + shift) hParent hParentUpper hEligible hDegree
  obtain ⟨position, lower, upper, hLower, hUpper, hLowerShape, hUpperShape⟩ :=
    d.copyColumn_fill_adjacent hParentPower hParentLow hNoPremature hRun hm hLowRung hHighRung
  have hLowerRow : lower.row = Row.bump parent.row degree := hLowerShape.1.symm
  have hUpperRow : upper.row = Row.bump parent.row (degree + 1) := hUpperShape.1.symm
  have hLowerLeft : lower.left = some ⟨s.sourceParent.column + shift, parentIndex⟩ := hLowerShape.2.symm
  have hUpperLeft : upper.left = some ⟨s.sourceParent.column + shift, parentIndex⟩ := hUpperShape.2.symm
  have hParentColumn := (Array.getElem?_eq_some_iff.mp s.parent_nodes).1
  have hParentFull : Canonical.cellAt (mountain.push column)
      ⟨s.sourceParent.column + shift, parentIndex⟩ = .ok parent := by
    rw [Canonical.cellAt_push_left hParentColumn]
    exact Canonical.cellAt_ok_iff.mpr ⟨s.parentNodes, s.parent_nodes, hParent⟩
  have hParentUpperFull : Canonical.cellAt (mountain.push column)
      ⟨s.sourceParent.column + shift, parentIndex + 1⟩ = .ok parentUpper := by
    rw [Canonical.cellAt_push_left hParentColumn]
    exact Canonical.cellAt_ok_iff.mpr ⟨s.parentNodes, s.parent_nodes, hParentUpper⟩
  have hLowerFull : Canonical.cellAt (mountain.push column) ⟨mountain.size, position⟩ = .ok lower :=
    Canonical.cellAt_ok_iff.mpr ⟨column, by simp, hLower⟩
  have hRowPositive : 0 < lower.row := by
    rw [hLowerRow]
    exact (Row.zero_le _).trans_lt (Row.lt_bump _ _)
  obtain ⟨hPosition, hLarge, hLeftward, hParentPositive, hUpperPositive, hSum, hDifference⟩ :=
    adjacent_values_at_parent hFinished hColumnValid hLower hUpper hRowPositive hUpperLeft hParentFull
  have hParentStep := hParentPower marker hm parentIndex parent parentUpper hParent hParentUpper
  have hSearch := interior_search_of_reads hMountainValid.toOrdered hLowerFull hParentFull hParentUpperFull
    hLowerLeft hParentStep hLowerRow (by omega) hParentPositive hUpperPositive hSum
  refine ⟨{
    position := position
    lower := lower
    upper := upper
    lower_at := hLower
    upper_at := hUpper
    position_positive := hPosition
    lower_large := hLarge
    parent_left := hLeftward
    parent_at := hParentFull
    parent_found := hSearch
    upper_row := ?_
    upper_value := hDifference
    upper_left := hUpperLeft }, hLowerShape, hUpperShape⟩
  rw [hUpperRow, hLowerRow, Row.B_reference_rung]

/-- The last rung of a nonfinal parent interval climbs to the actual next
parent; the following rung stores that next parent's reference. The real
search, B height and difference equation are all consequences. -/
theorem copyColumn_fill_seam {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {marker : Ref} (hm : marker ∈ d.bucket) {parentIndex : Nat} {parent middle parentUpper : Cell}
    (hParent : (d.marker_data marker hm).parentNodes[parentIndex]? = some parent)
    (hMiddle : (d.marker_data marker hm).parentNodes[parentIndex + 1]? = some middle)
    (hParentUpper : (d.marker_data marker hm).parentNodes[(parentIndex + 1) + 1]? = some parentUpper)
    (hEligible : (d.marker_data marker hm).current.row ≤ parent.row ∧
      parent.row < (d.marker_data marker hm).targetCell.row)
    (hNextEligible : (d.marker_data marker hm).current.row ≤ middle.row ∧
      middle.row < (d.marker_data marker hm).targetCell.row) :
    ∃ step : ActualFillStep mountain column
        ⟨(d.marker_data marker hm).sourceParent.column + shift, parentIndex + 1⟩ middle,
      SameShape (⟨middle.row, 0, some ⟨(d.marker_data marker hm).sourceParent.column + shift,
        parentIndex⟩⟩ : Cell) step.lower ∧
      SameShape (referenceRung middle.row ((d.marker_data marker hm).sourceParent.column + shift)
        (parentIndex + 1) 0) step.upper := by
  let s := d.marker_data marker hm
  obtain ⟨hFinished, hColumnValid, hMountainValid⟩ := d.actual_copy_facts hRun
  obtain ⟨hLowRung, hHighRung⟩ := fillCellsAscending_seam (hParentPower marker hm)
    (column := s.sourceParent.column + shift) hParent hMiddle hParentUpper hEligible hNextEligible
  obtain ⟨position, lower, upper, hLower, hUpper, hLowerShape, hUpperShape⟩ :=
    d.copyColumn_fill_adjacent hParentPower hParentLow hNoPremature hRun hm hLowRung hHighRung
  have hLowerRow : lower.row = middle.row := hLowerShape.1.symm
  have hUpperRow : upper.row = Row.bump middle.row 0 := hUpperShape.1.symm
  have hLowerLeft : lower.left = some ⟨s.sourceParent.column + shift, parentIndex⟩ := hLowerShape.2.symm
  have hUpperLeft : upper.left = some ⟨s.sourceParent.column + shift, parentIndex + 1⟩ := hUpperShape.2.symm
  have hParentColumn := (Array.getElem?_eq_some_iff.mp s.parent_nodes).1
  have hParentFull : Canonical.cellAt (mountain.push column)
      ⟨s.sourceParent.column + shift, parentIndex⟩ = .ok parent := by
    rw [Canonical.cellAt_push_left hParentColumn]
    exact Canonical.cellAt_ok_iff.mpr ⟨s.parentNodes, s.parent_nodes, hParent⟩
  have hMiddleFull : Canonical.cellAt (mountain.push column)
      ⟨s.sourceParent.column + shift, parentIndex + 1⟩ = .ok middle := by
    rw [Canonical.cellAt_push_left hParentColumn]
    exact Canonical.cellAt_ok_iff.mpr ⟨s.parentNodes, s.parent_nodes, hMiddle⟩
  have hLowerFull : Canonical.cellAt (mountain.push column) ⟨mountain.size, position⟩ = .ok lower :=
    Canonical.cellAt_ok_iff.mpr ⟨column, by simp, hLower⟩
  have hParentStep := hParentPower marker hm parentIndex parent middle hParent hMiddle
  have hRowPositive : 0 < lower.row := by
    rw [hLowerRow, hParentStep]
    exact (Row.zero_le _).trans_lt (Row.lt_bump _ _)
  obtain ⟨hPosition, hLarge, hLeftward, hParentPositive, hUpperPositive, hSum, hDifference⟩ :=
    adjacent_values_at_parent hFinished hColumnValid hLower hUpper hRowPositive hUpperLeft hMiddleFull
  have hSearch := endpoint_search_of_reads hMountainValid.toOrdered hLowerFull hParentFull hMiddleFull
    hLowerLeft hParentStep (hLowerRow.trans hParentStep) hParentPositive hUpperPositive hSum
  refine ⟨{
    position := position
    lower := lower
    upper := upper
    lower_at := hLower
    upper_at := hUpper
    position_positive := hPosition
    lower_large := hLarge
    parent_left := hLeftward
    parent_at := hMiddleFull
    parent_found := hSearch
    upper_row := ?_
    upper_value := hDifference
    upper_left := hUpperLeft }, hLowerShape, hUpperShape⟩
  rw [hUpperRow, hLowerRow, Row.B_self]

end ParentInputs

end ColumnCopyData

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_fill_interior
#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_fill_seam
