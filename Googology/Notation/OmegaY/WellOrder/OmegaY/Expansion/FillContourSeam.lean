/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/FillContourSeam.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/FillContourSeam.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.FillCanonical
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.BoundarySelection
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.DynamicBlockStep

set_option backward.do.legacy false

/-!
# The actual reference-cap to contour seam

The next contour node is forced to exist by the actual marker reference caps.
Its left endpoint is selected by the executable `below`, and the two output
neighbours are obtained from the real segment sort and numerical finish.
No copied numerical-normality or desired adjacency is an input.
-/

namespace OmegaY.Expansion

open Canonical Geometry

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

@[simp] private theorem bind_ok {α β : Type} (a : α) (f : α → Result β) :
    (Except.ok a >>= f) = f a := rfl
@[simp] private theorem pure_ok {α : Type} (a : α) :
    (pure a : Result α) = Except.ok a := rfl
@[simp] private theorem bind_error {α β : Type} (e : Error) (f : α → Result β) :
    (Except.error e >>= f) = .error e := rfl

/-- An actual row is the unique eligible maximum below its successor. This
does not require a dense parent column. -/
theorem below_bump_zero_of_read {mountain : Mountain} (hValid : MountainValid mountain)
    {ref : Ref} {cell : Cell} (hRead : Canonical.cellAt mountain ref = .ok cell) :
    below mountain ref.column (Row.bump cell.row 0) = .ok ref := by
  obtain ⟨found, actual, hFound, hActual, hColumn, hLower, hUpper⟩ :=
    below_between hValid hRead (Row.lt_bump cell.row 0)
  have hRows : cell.row = actual.row := Row.jump_eq_zero.mp
    (Nat.eq_zero_of_le_zero (Row.jump_le_of_lt_bump hLower hUpper))
  obtain ⟨nodes, hNodes, hCell⟩ := cellAt_ok_iff.mp hRead
  obtain ⟨actualNodes, hActualNodes, hActualCell⟩ := cellAt_ok_iff.mp hActual
  have hNodesEq : actualNodes = nodes := Option.some.inj
    (hActualNodes.symm.trans (by simpa only [hColumn] using hNodes))
  subst actualNodes
  obtain ⟨hc, hNodesValue⟩ := Array.getElem?_eq_some_iff.mp hNodes
  have hCV : ColumnValid mountain ref.column nodes := hNodesValue ▸ hValid _ hc
  have hIndex : found.index = ref.index := by
    rcases lt_trichotomy found.index ref.index with hlt | he | hgt
    · exact False.elim ((ne_of_lt (hCV.rows_strict _ _ _ _ hActualCell hCell hlt)) hRows.symm)
    · exact he
    · exact False.elim ((ne_of_lt (hCV.rows_strict _ _ _ _ hCell hActualCell hgt)) hRows)
  have hRef : found = ref := by cases found; cases ref; simp_all only
  simpa only [hRef] using hFound

/-- The final actual fill cell points to the immediate predecessor of the
target, and occurs at the end of the whole ascending fill list. -/
theorem fillCellsAscending_last {nodes : Column} (hStrict : FillRowsStrict nodes)
    (hPower : ColumnPowerSteps nodes) {column lowIndex highIndex : Nat}
    {lowCell highCell : Cell} (hLow : nodes[lowIndex]? = some lowCell)
    (hHigh : nodes[highIndex]? = some highCell) (hRow : lowCell.row < highCell.row) :
    ∃ parentIndex parent before, parentIndex + 1 = highIndex ∧
      nodes[parentIndex]? = some parent ∧
      fillCellsAscending nodes column lowCell.row highCell.row =
        before ++ [⟨highCell.row, 0, some ⟨column, parentIndex⟩⟩] := by
  obtain ⟨parentIndex, parent, hNext, hParent, _, hMem⟩ :=
    fillCells_contains_high hStrict hPower hLow hHigh hRow (column := column)
  have hMemAscending := (fillCellsAscending_perm nodes column lowCell.row highCell.row).mem_iff.mpr hMem
  obtain ⟨before, after, hSplit⟩ := List.append_of_mem hMemAscending
  have hAsc := fillCellsAscending_strict hStrict hHigh (le_refl highCell.row)
    (column := column) (low := lowCell.row)
  have hAfter : after = [] := by
    cases after with
    | nil => rfl
    | cons next rest =>
      have hPair := (List.pairwise_append.mp (hSplit ▸ hAsc)).2.1
      have hNextLt : highCell.row < next.row :=
        (List.pairwise_cons.mp hPair).1 next (by simp)
      have hNextMem : next ∈ fillCells nodes column lowCell.row highCell.row := by
        apply (fillCellsAscending_perm nodes column lowCell.row highCell.row).mem_iff.mp
        rw [hSplit]
        simp
      have hNextBound := (fillCells_row_bounds hStrict hHigh (le_refl highCell.row) hNextMem).2
      exact False.elim ((not_lt_of_ge hNextBound) hNextLt)
  exact ⟨parentIndex, parent, before, hNext, hParent, by simpa only [hAfter] using hSplit⟩

namespace ColumnCopyData

variable {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
  {sourceColumn shift rootColumn : Nat}
  (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)

include d

/-- A raised target cannot stop immediately at another marker when the
source upper is exactly the source row's successor. -/
theorem raised_successor_not_marked {marker : Ref} (hm : marker ∈ d.bucket)
    (hUpper : (d.marker_data marker hm).upper.row = Row.bump (d.marker_data marker hm).current.row 0)
    (hRaised : (d.marker_data marker hm).current.row < (d.marker_data marker hm).targetCell.row) :
    marker.index + 1 ∉ d.bucket.map Ref.index := by
  intro hMember
  obtain ⟨higher, hHigher, hIndex⟩ := List.mem_map.mp hMember
  have hCurrentEq : (d.marker_data higher hHigher).current = (d.marker_data marker hm).upper :=
    Option.some.inj ((d.marker_data higher hHigher).current_at.symm.trans
      (by simpa only [hIndex] using (d.marker_data marker hm).upper_at))
  obtain ⟨scale, hTarget, hCap⟩ := d.reference_caps marker hm higher hHigher (by omega)
  have hSmall : (d.marker_data marker hm).targetCell.row <
      Row.bump (d.marker_data marker hm).current.row 0 := by
    exact hTarget.trans_le (by simpa only [hCurrentEq, hUpper] using hCap)
  have hEqual := Row.jump_eq_zero.mp (Nat.eq_zero_of_le_zero
    (Row.jump_le_of_lt_bump (le_of_lt hRaised) hSmall))
  exact (ne_of_lt hRaised) hEqual

/-- The actual first copied contour cell has successor row and stores the
selected target reference itself. -/
theorem raised_successor_contour_head (hNoPremature : NoPrematureOne d.sources)
    {marker : Ref} (hm : marker ∈ d.bucket)
    (hUpper : (d.marker_data marker hm).upper.row = Row.bump (d.marker_data marker hm).current.row 0)
    (hRoot : rootColumn ≤ (d.marker_data marker hm).sourceParent.column)
    (hRaised : (d.marker_data marker hm).current.row < (d.marker_data marker hm).targetCell.row)
    {path : List Cell}
    (hRun : contour mountain sourceColumn (d.bucket.map Ref.index) shift rootColumn marker.index
      (d.marker_data marker hm).targetCell.row (d.marker_data marker hm).current
      (d.sources.toList.drop (marker.index + 1)) = .ok path) :
    ∃ tail, path =
      (⟨Row.bump (d.marker_data marker hm).targetCell.row 0, 0,
        some ⟨(d.marker_data marker hm).sourceParent.column + shift,
          (d.marker_data marker hm).targetIndex⟩⟩ : Cell) :: tail := by
  let s := d.marker_data marker hm
  change rootColumn ≤ s.sourceParent.column at hRoot
  change contour mountain sourceColumn (d.bucket.map Ref.index) shift rootColumn marker.index
    s.targetCell.row s.current (d.sources.toList.drop (marker.index + 1)) = .ok path at hRun
  have hNotMarked := d.raised_successor_not_marked hm hUpper hRaised
  have hNotOne := hNoPremature marker.index s.current s.upper s.current_at s.upper_at
  have hNotStop : ¬ (s.current.value = 1 ∨ marker.index + 1 ∈ d.bucket.map Ref.index) :=
    not_or.mpr ⟨hNotOne, hNotMarked⟩
  have hStrict : s.current.row < s.upper.row := by
    rw [show s.upper.row = Row.bump s.current.row 0 from hUpper]
    exact Row.lt_bump _ _
  have hDegree : Row.jump s.current.row s.upper.row - 1 = 0 := by
    rw [show s.upper.row = Row.bump s.current.row 0 from hUpper]
    simp only [Row.jump_bump, Nat.add_sub_cancel]
  have hHead : (d.sources.toList.drop (marker.index + 1)).head? = some s.upper := by
    simpa only [List.head?_drop, Array.getElem?_toList] using s.upper_at
  obtain ⟨rest, hRest⟩ : ∃ rest, d.sources.toList.drop (marker.index + 1) = s.upper :: rest := by
    cases hRest : d.sources.toList.drop (marker.index + 1) with
    | nil => simp only [hRest, List.head?_nil, reduceCtorEq] at hHead
    | cons other rest =>
      have he : other = s.upper := Option.some.inj (by simpa only [hRest, List.head?_cons] using hHead)
      exact ⟨rest, by simp only [he]⟩
  have hUpperRead : lookup mountain ⟨sourceColumn, marker.index + 1⟩ = .ok s.upper :=
    lookup_ok_iff.mpr ⟨d.sources, d.source_column, s.upper_at⟩
  have hNonzero : s.upper.row ≠ 0 := ne_of_gt ((Row.zero_le s.current.row).trans_lt hStrict)
  have hTargetRead : Canonical.cellAt mountain ⟨s.sourceParent.column + shift, s.targetIndex⟩ =
      .ok s.targetCell := cellAt_ok_iff.mpr ⟨s.parentNodes, s.parent_nodes, s.target_at⟩
  have hBelow := below_bump_zero_of_read d.ambient_valid hTargetRead
  have hParentDest : s.sourceParent.column + shift < sourceColumn + shift := by
    rw [d.destination]
    exact (Array.getElem?_eq_some_iff.mp s.parent_nodes).1
  have hCopy : copyEdge mountain ⟨sourceColumn, marker.index + 1⟩ shift rootColumn
      (Row.bump s.targetCell.row 0) =
      .ok ⟨Row.bump s.targetCell.row 0, 0, some ⟨s.sourceParent.column + shift, s.targetIndex⟩⟩ := by
    simp only [copyEdge, hUpperRead, bind_ok, hNonzero, ↓reduceIte, leftOf, s.upper_left,
      not_lt_of_ge hRoot, hBelow, hParentDest, not_true_eq_false, pure_ok]
  rw [hRest] at hRun
  simp only [contour, hNotStop, ↓reduceIte, hStrict, not_true_eq_false, hDegree, hCopy,
    bind_ok, pure_ok] at hRun
  cases hTail : contour mountain sourceColumn (d.bucket.map Ref.index) shift rootColumn
      (marker.index + 1) (Row.bump s.targetCell.row 0) s.upper rest with
  | error e => simp only [hTail, bind_error, reduceCtorEq] at hRun
  | ok tail =>
    exact ⟨tail, (Except.ok.inj (by simpa only [hTail, bind_ok] using hRun)).symm⟩

section ParentInputs

variable
  (hParentPower : ∀ marker (hm : marker ∈ d.bucket),
    ColumnPowerSteps (d.marker_data marker hm).parentNodes)
  (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (index : Nat) (cell : Cell),
    (d.marker_data marker hm).parentNodes[index]? = some cell ∧
      cell.row = (d.marker_data marker hm).current.row)
  (hNoPremature : NoPrematureOne d.sources)

include hParentPower hParentLow hNoPremature

/-- The reference cap and first contour edge form a contiguous two-cell
block in the actual candidate sort. Neither adjacency nor contour success
is a premise. -/
theorem fill_contour_splice {marker : Ref} (hm : marker ∈ d.bucket)
    (hUpper : (d.marker_data marker hm).upper.row = Row.bump (d.marker_data marker hm).current.row 0)
    (hRoot : rootColumn ≤ (d.marker_data marker hm).sourceParent.column)
    (hRaised : (d.marker_data marker hm).current.row < (d.marker_data marker hm).targetCell.row) :
    ∃ parentIndex parent before after,
      parentIndex + 1 = (d.marker_data marker hm).targetIndex ∧
      (d.marker_data marker hm).parentNodes[parentIndex]? = some parent ∧
      finishSort d.candidates = before ++
        [⟨(d.marker_data marker hm).targetCell.row, 0,
            some ⟨(d.marker_data marker hm).sourceParent.column + shift, parentIndex⟩⟩,
          ⟨Row.bump (d.marker_data marker hm).targetCell.row 0, 0,
            some ⟨(d.marker_data marker hm).sourceParent.column + shift,
              (d.marker_data marker hm).targetIndex⟩⟩] ++ after := by
  let s := d.marker_data marker hm
  obtain ⟨lowIndex, lowCell, hLowRead, hLowRow⟩ := hParentLow marker hm
  obtain ⟨copied, path, _, hContour, hSegment⟩ := copySegment_sorted_splice
    d.ambient_valid d.source_column d.source_nonzero d.destination.le d.source_top
    (d.bucket.map Ref.index) s (hParentPower marker hm) hLowRead hLowRow (d.segment_run hm)
  obtain ⟨tail, hPath⟩ := d.raised_successor_contour_head hNoPremature hm hUpper hRoot hRaised hContour
  obtain ⟨hp, hNodesEq⟩ := Array.getElem?_eq_some_iff.mp s.parent_nodes
  have hParentValid : ColumnValid mountain (s.sourceParent.column + shift) s.parentNodes :=
    hNodesEq ▸ d.ambient_valid _ hp
  obtain ⟨parentIndex, parent, gapBefore, hNext, hParent, hGap⟩ := fillCellsAscending_last
    (fillRowsStrict_of_columnValid hParentValid) (hParentPower marker hm) hLowRead s.target_at
    (by simpa only [hLowRow] using hRaised) (column := s.sourceParent.column + shift)
  rw [hLowRow] at hGap
  obtain ⟨before, after, hSplit⟩ := List.append_of_mem (List.mem_reverse.mpr hm)
  let sortedSegment := fun entry => finishSort (d.segment entry)
  refine ⟨parentIndex, parent, before.flatMap sortedSegment ++ [copied] ++ gapBefore,
    tail ++ after.flatMap sortedSegment, hNext, hParent, ?_⟩
  rw [d.finishSort_candidates_cells hParentPower hParentLow hNoPremature]
  simp only [ascendingCells, hSplit, List.flatMap_append, List.flatMap_cons]
  rw [hSegment, hGap, hPath]
  simp only [List.append_assoc, List.cons_append, List.nil_append, sortedSegment, s]

/-- The highest reference rung and first contour cell form an actual
canonical difference step in the returned column. The parent is the actual
selected target in the completed shifted parent column. -/
theorem copyColumn_fill_contour_seam {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {marker : Ref} (hm : marker ∈ d.bucket)
    (hUpper : (d.marker_data marker hm).upper.row = Row.bump (d.marker_data marker hm).current.row 0)
    (hRoot : rootColumn ≤ (d.marker_data marker hm).sourceParent.column)
    (hRaised : (d.marker_data marker hm).current.row < (d.marker_data marker hm).targetCell.row) :
    ∃ step : ActualFillStep mountain column
        ⟨(d.marker_data marker hm).sourceParent.column + shift, (d.marker_data marker hm).targetIndex⟩
        (d.marker_data marker hm).targetCell,
      step.lower.row = (d.marker_data marker hm).targetCell.row ∧
      step.upper.row = Row.bump (d.marker_data marker hm).targetCell.row 0 := by
  let s := d.marker_data marker hm
  obtain ⟨other, hOther, hFinished, hColumnValid, _, hMountainValid⟩ := d.copyColumn_valid
  have he : other = column := Except.ok.inj (hOther.symm.trans hRun)
  subst other
  obtain ⟨parentIndex, parent, before, after, hNext, hParent, hSplit⟩ :=
    d.fill_contour_splice hParentPower hParentLow hNoPremature hm hUpper hRoot hRaised
  obtain ⟨lower, upper, hLower, hUpperOut, hLowerShape, hUpperShape⟩ := finish_adjacent_of_splice
    (d.copyColumn_eq_finish.symm.trans hRun) hSplit (index := 0) rfl rfl
  simp only [Nat.add_zero] at hLower hUpperOut
  have hLowerRow : lower.row = s.targetCell.row := hLowerShape.1.symm
  have hUpperRow : upper.row = Row.bump s.targetCell.row 0 := hUpperShape.1.symm
  have hLowerLeft : lower.left = some ⟨s.sourceParent.column + shift, parentIndex⟩ := hLowerShape.2.symm
  have hUpperLeft : upper.left = some ⟨s.sourceParent.column + shift, s.targetIndex⟩ := hUpperShape.2.symm
  have hParentColumn := (Array.getElem?_eq_some_iff.mp s.parent_nodes).1
  have hTargetAt : s.parentNodes[parentIndex + 1]? = some s.targetCell := by
    simpa only [hNext] using s.target_at
  have hParentFull : Canonical.cellAt (mountain.push column)
      ⟨s.sourceParent.column + shift, parentIndex⟩ = .ok parent := by
    rw [Canonical.cellAt_push_left hParentColumn]
    exact Canonical.cellAt_ok_iff.mpr ⟨s.parentNodes, s.parent_nodes, hParent⟩
  have hTargetFull : Canonical.cellAt (mountain.push column)
      ⟨s.sourceParent.column + shift, s.targetIndex⟩ = .ok s.targetCell := by
    rw [Canonical.cellAt_push_left hParentColumn]
    exact Canonical.cellAt_ok_iff.mpr ⟨s.parentNodes, s.parent_nodes, s.target_at⟩
  have hTargetFullNext : Canonical.cellAt (mountain.push column)
      ⟨s.sourceParent.column + shift, parentIndex + 1⟩ = .ok s.targetCell := by
    simpa only [hNext] using hTargetFull
  have hLowerFull : Canonical.cellAt (mountain.push column) ⟨mountain.size, before.length⟩ = .ok lower :=
    Canonical.cellAt_ok_iff.mpr ⟨column, by simp, hLower⟩
  have hPosition : 0 < before.length := by
    by_contra hn
    have hz : before.length = 0 := by omega
    have hLowerZero : column[0]? = some lower := by simpa only [hz] using hLower
    have hCell : lower = phantom := Option.some.inj
      (hLowerZero.symm.trans hColumnValid.phantom)
    have hPositive : 0 < lower.row := by
      rw [hLowerRow]
      exact (Row.zero_le s.current.row).trans_lt hRaised
    simp only [hCell, phantom, lt_self_iff_false] at hPositive
  obtain ⟨hLarge, ref, actualParent, hActualLeft, hActualParent, hLeftward, hPositive, hSum, hDifference⟩ :=
    hFinished.adjacent_difference hColumnValid hLower hUpperOut hPosition
  have hRefEq : ref = ⟨s.sourceParent.column + shift, s.targetIndex⟩ :=
    Option.some.inj (hActualLeft.symm.trans hUpperLeft)
  subst ref
  have hParentEq : actualParent = s.targetCell := Except.ok.inj (hActualParent.symm.trans hTargetFull)
  subst actualParent
  have hParentStep := hParentPower marker hm parentIndex parent s.targetCell hParent hTargetAt
  have hSearch := endpoint_search_of_reads hMountainValid.toOrdered hLowerFull hParentFull hTargetFullNext
    hLowerLeft hParentStep (hLowerRow.trans hParentStep) hPositive
    (hColumnValid.real_positive _ _ hUpperOut (by omega)) hSum
  refine ⟨{
    position := before.length
    lower := lower
    upper := upper
    lower_at := hLower
    upper_at := hUpperOut
    position_positive := hPosition
    lower_large := hLarge
    parent_left := hLeftward
    parent_at := hTargetFull
    parent_found := by simpa only [hNext] using hSearch
    upper_row := by rw [hUpperRow, hLowerRow, Row.B_self]
    upper_value := hDifference
    upper_left := hUpperLeft }, hLowerRow, hUpperRow⟩

end ParentInputs

end ColumnCopyData

/-- The two source hypotheses for a raised cap are derived from the actual
prepared weak marker and canonical source construction. -/
theorem ColumnCopyData.prepared_marker_successor {front : List Nat} {last : Nat}
    {p : Preparation front last} {mountain : Mountain} {references : List Ref}
    {sourceColumn shift : Nat}
    (d : ColumnCopyData mountain p.marked references sourceColumn shift p.root.column)
    (hSource : p.reduced[sourceColumn]? = some d.sources)
    {marker : Ref} (hm : marker ∈ d.bucket)
    (hRaised : (d.marker_data marker hm).current.row < (d.marker_data marker hm).targetCell.row) :
    (d.marker_data marker hm).upper.row = Row.bump (d.marker_data marker hm).current.row 0 ∧
      p.root.column ≤ (d.marker_data marker hm).sourceParent.column := by
  let md := d.marker_data marker hm
  change md.current.row < md.targetCell.row at hRaised
  have hMarkerColumn := d.marker_columns marker hm
  obtain ⟨rootIndex, parent, current, upper, parentCell, _, hCurrent, hUpper,
    hLeft, _, hParent, hParentRow, hParentCase⟩ :=
    markers_upper_parent
      (weakLocal_of_ordered p.reduced_valid.toOrdered p.reduced_valid.left_sources)
      p.root_valid p.markers_built hm
  have hCurrentMd : Canonical.cellAt p.reduced marker = .ok md.current :=
    cellAt_ok_iff.mpr ⟨d.sources, by simpa only [hMarkerColumn] using hSource, md.current_at⟩
  have hUpperMd : Canonical.cellAt p.reduced ⟨marker.column, marker.index + 1⟩ = .ok md.upper :=
    cellAt_ok_iff.mpr ⟨d.sources, by simpa only [hMarkerColumn] using hSource, md.upper_at⟩
  have hCurrentEq : current = md.current := Except.ok.inj ((cellAt_ok_iff.mpr hCurrent).symm.trans hCurrentMd)
  have hUpperEq : upper = md.upper := Except.ok.inj ((cellAt_ok_iff.mpr hUpper).symm.trans hUpperMd)
  subst current
  subst upper
  have hParentEq : parent = md.sourceParent := Option.some.inj (hLeft.symm.trans md.upper_left)
  subst parent
  have hRoot : p.root.column ≤ md.sourceParent.column := by
    rcases hParentCase with hRoot | hEarlier
    · exact Nat.le_of_eq (congrArg Ref.column hRoot).symm
    · exact Nat.le_of_lt (p.marker_iff.mp hEarlier).2.1
  have hIndex : 0 < marker.index := by
    by_contra hn
    have hz : marker.index = 0 := by omega
    have hCurrentZero : md.current.row = 0 := by
      have hRead : d.sources[0]? = some md.current := by simpa only [hz] using md.current_at
      have he : md.current = phantom := Option.some.inj (hRead.symm.trans d.source_valid.phantom)
      simp only [he, phantom]
    have hTargetZero := d.target_zero hm hCurrentZero
    change md.targetCell.row = 0 at hTargetZero
    have hImpossible : (0 : Row) < 0 := by simpa only [hCurrentZero, hTargetZero] using hRaised
    exact (lt_irrefl _) hImpossible
  obtain ⟨hc, hColumnEq⟩ := Array.getElem?_eq_some_iff.mp hSource
  have hSteps : ColumnSteps p.reduced sourceColumn d.sources := hColumnEq ▸ build_steps p.reduced_build sourceColumn hc
  obtain ⟨_, actualRef, actualParent, _, _, hActualParent, hRow, _, hActualLeft⟩ :=
    hSteps marker.index md.current md.upper md.current_at md.upper_at hIndex
  have hActualRefEq : actualRef = md.sourceParent := Option.some.inj (hActualLeft.symm.trans md.upper_left)
  subst actualRef
  have hActualParentEq : actualParent = parentCell := Except.ok.inj
    (hActualParent.symm.trans (cellAt_ok_iff.mpr hParent))
  subst actualParent
  exact ⟨by simpa only [hParentRow, Row.B_self] using hRow, hRoot⟩

/-- On an actual prepared source, the cap-to-contour conclusion has no
extra source-row or root-parent hypothesis. -/
theorem ColumnCopyData.prepared_fill_contour_seam {front : List Nat} {last : Nat}
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
    {marker : Ref} (hm : marker ∈ d.bucket)
    (hRaised : (d.marker_data marker hm).current.row < (d.marker_data marker hm).targetCell.row) :
    ∃ step : ActualFillStep mountain column
        ⟨(d.marker_data marker hm).sourceParent.column + shift, (d.marker_data marker hm).targetIndex⟩
        (d.marker_data marker hm).targetCell,
      step.lower.row = (d.marker_data marker hm).targetCell.row ∧
      step.upper.row = Row.bump (d.marker_data marker hm).targetCell.row 0 := by
  obtain ⟨hUpper, hRoot⟩ := d.prepared_marker_successor hSource hm hRaised
  exact d.copyColumn_fill_contour_seam hParentPower hParentLow hNoPremature hRun hm hUpper hRoot hRaised

/-- Every raised reference cap in a real dynamic copy state gives the
corresponding actual canonical step in the returned next column. All local
parent support and source facts are supplied by the state construction. -/
theorem DynamicBlockState.copy_next_fill_contour_seam {front : List Nat} {last : Nat}
    {p : Preparation front last} {block : Nat} {start : Mountain} {references : List Ref}
    {next : Nat} {ambient : Mountain} (s : DynamicBlockState p block start references next ambient)
    (hLast : 1 < last) (hNext : next < p.reduced.size) {column : Column}
    (hRun : copyColumn ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column)
    {marker : Ref} (hMarker : BucketMem p.marked next marker) {current : Cell}
    (hCurrent : Canonical.cellAt p.reduced marker = .ok current) {target : Row}
    (hReference : referenceAt ambient references current.row = .ok target)
    (hRaised : current.row < target) :
    ∃ parentRef parent, ∃ step : ActualFillStep ambient column parentRef parent,
      parent.row = target ∧ step.lower.row = target ∧ step.upper.row = Row.bump target 0 := by
  obtain ⟨d, hNoPremature, hParentPower, hParentLow⟩ := s.column_data hLast hNext
  have hSource : p.reduced[next]? = some d.sources :=
    (s.base_ambient next hNext).symm.trans d.source_column
  let md := d.marker_data marker hMarker
  have hMarkerColumn := d.marker_columns marker hMarker
  have hCurrentMd : Canonical.cellAt p.reduced marker = .ok md.current :=
    cellAt_ok_iff.mpr ⟨d.sources, by simpa only [hMarkerColumn] using hSource, md.current_at⟩
  have hCurrentEq : current = md.current := Except.ok.inj (hCurrent.symm.trans hCurrentMd)
  have hRefMd : referenceAt ambient references md.current.row = .ok target := by
    simpa only [hCurrentEq] using hReference
  have hTargetEq : target = md.targetCell.row := Except.ok.inj
    (hRefMd.symm.trans md.reference)
  obtain ⟨step, hLower, hUpper⟩ := d.prepared_fill_contour_seam hSource hParentPower hParentLow
    hNoPremature hRun hMarker (by simpa only [hCurrentEq, hTargetEq] using hRaised)
  exact ⟨_, _, step, hTargetEq.symm, hLower.trans hTargetEq.symm,
    hUpper.trans (congrArg (fun r => Row.bump r 0) hTargetEq.symm)⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.below_bump_zero_of_read
#print axioms OmegaY.Expansion.fillCellsAscending_last
#print axioms OmegaY.Expansion.ColumnCopyData.raised_successor_not_marked
#print axioms OmegaY.Expansion.ColumnCopyData.raised_successor_contour_head
#print axioms OmegaY.Expansion.ColumnCopyData.fill_contour_splice
#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_fill_contour_seam
#print axioms OmegaY.Expansion.ColumnCopyData.prepared_marker_successor
#print axioms OmegaY.Expansion.ColumnCopyData.prepared_fill_contour_seam
#print axioms OmegaY.Expansion.DynamicBlockState.copy_next_fill_contour_seam
