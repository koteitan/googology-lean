/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/MarkerContourGeometry.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/MarkerContourGeometry.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.MarkerFillGeometry
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ActualIntervalEdge

set_option backward.do.legacy false

/-!
# Raw B geometry when a physical marker meets the contour

An empty actual fill forces the reference target to equal the physical
marker row. Executed weak-marker ancestry makes the next source row its
successor. The first actual contour edge therefore selects the real target
node in the parent column. This identifies the stored leg and B row but
does not assert numerical first-smaller recovery at the physical marker.
-/

namespace OmegaY.Expansion

open Canonical Geometry

@[simp] private theorem bind_ok {α β : Type} (a : α) (f : α → Result β) :
    (Except.ok a >>= f) = f a := rfl
@[simp] private theorem pure_ok {α : Type} (a : α) : (pure a : Result α) = .ok a := rfl
@[simp] private theorem bind_error {α β : Type} (e : Error) (f : α → Result β) :
    (Except.error e >>= f) = .error e := rfl

/-- The successor fact is a property of every real prepared marker,
independently of whether its reference target is raised. -/
theorem ColumnCopyData.prepared_real_marker_successor
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {mountain : Mountain} {references : List Ref} {sourceColumn shift : Nat}
    (d : ColumnCopyData mountain p.marked references sourceColumn shift p.root.column)
    (hSource : p.reduced[sourceColumn]? = some d.sources)
    {marker : Ref} (hm : marker ∈ d.bucket) (hIndex : 0 < marker.index) :
    (d.marker_data marker hm).upper.row = Row.bump (d.marker_data marker hm).current.row 0 ∧
      p.root.column ≤ (d.marker_data marker hm).sourceParent.column := by
  let md := d.marker_data marker hm
  have hMarkerColumn := d.marker_columns marker hm
  obtain ⟨_, parent, current, upper, parentCell, _, hCurrent, hUpper,
    hLeft, _, hParent, hParentRow, hParentCase⟩ :=
    markers_upper_parent (weakLocal_of_ordered p.reduced_valid.toOrdered p.reduced_valid.left_sources)
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
  obtain ⟨hc, hColumnEq⟩ := Array.getElem?_eq_some_iff.mp hSource
  have hSteps : ColumnSteps p.reduced sourceColumn d.sources := hColumnEq ▸ build_steps p.reduced_build sourceColumn hc
  obtain ⟨_, actualRef, actualParent, _, _, hActualParent, hRow, _, hActualLeft⟩ :=
    hSteps marker.index md.current md.upper md.current_at md.upper_at hIndex
  have hRefEq : actualRef = md.sourceParent := Option.some.inj (hActualLeft.symm.trans md.upper_left)
  subst actualRef
  have hCellEq : actualParent = parentCell := Except.ok.inj
    (hActualParent.symm.trans (cellAt_ok_iff.mpr hParent))
  subst actualParent
  exact ⟨by simpa only [hParentRow, Row.B_self] using hRow, hRoot⟩

theorem ColumnCopyData.successor_contour_head_of_read
    {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
    {sourceColumn shift rootColumn : Nat}
    (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)
    {marker : Ref} (hm : marker ∈ d.bucket)
    (hUpper : (d.marker_data marker hm).upper.row = Row.bump (d.marker_data marker hm).current.row 0)
    (hRoot : rootColumn ≤ (d.marker_data marker hm).sourceParent.column)
    {path : List Cell} {head : Cell}
    (hRun : contour mountain sourceColumn (d.bucket.map Ref.index) shift rootColumn marker.index
      (d.marker_data marker hm).targetCell.row (d.marker_data marker hm).current
      (d.sources.toList.drop (marker.index + 1)) = .ok path)
    (hHead : path.head? = some head) :
    head = ⟨Row.bump (d.marker_data marker hm).targetCell.row 0, 0,
      some ⟨(d.marker_data marker hm).sourceParent.column + shift,
        (d.marker_data marker hm).targetIndex⟩⟩ := by
  let md := d.marker_data marker hm
  change rootColumn ≤ md.sourceParent.column at hRoot
  have hSourceHead : (d.sources.toList.drop (marker.index + 1)).head? = some md.upper := by
    simpa only [List.head?_drop, Array.getElem?_toList] using md.upper_at
  obtain ⟨rest, hRest⟩ : ∃ rest, d.sources.toList.drop (marker.index + 1) = md.upper :: rest := by
    cases he : d.sources.toList.drop (marker.index + 1) with
    | nil => simp only [he, List.head?_nil, reduceCtorEq] at hSourceHead
    | cons other rest =>
      have hs : other = md.upper := Option.some.inj (by simpa only [he, List.head?_cons] using hSourceHead)
      exact ⟨rest, by simp only [hs]⟩
  change contour mountain sourceColumn (d.bucket.map Ref.index) shift rootColumn marker.index
    md.targetCell.row md.current (d.sources.toList.drop (marker.index + 1)) = .ok path at hRun
  rw [hRest] at hRun
  have hNotStop : ¬ (md.current.value = 1 ∨ marker.index + 1 ∈ d.bucket.map Ref.index) := by
    intro hStop
    have hEmpty : path = [] := Except.ok.inj
      (by simpa only [contour, if_pos hStop, pure_ok] using hRun.symm)
    simp only [hEmpty, List.head?_nil, reduceCtorEq] at hHead
  have hStrict : md.current.row < md.upper.row := by
    rw [show md.upper.row = Row.bump md.current.row 0 from hUpper]
    exact Row.lt_bump _ _
  have hDegree : Row.jump md.current.row md.upper.row - 1 = 0 := by
    rw [show md.upper.row = Row.bump md.current.row 0 from hUpper]
    simp only [Row.jump_bump, Nat.add_sub_cancel]
  have hRead : lookup mountain ⟨sourceColumn, marker.index + 1⟩ = .ok md.upper :=
    lookup_ok_iff.mpr ⟨d.sources, d.source_column, md.upper_at⟩
  have hNonzero : md.upper.row ≠ 0 := ne_of_gt ((Row.zero_le md.current.row).trans_lt hStrict)
  have hTargetRead : Canonical.cellAt mountain ⟨md.sourceParent.column + shift, md.targetIndex⟩ = .ok md.targetCell :=
    cellAt_ok_iff.mpr ⟨md.parentNodes, md.parent_nodes, md.target_at⟩
  have hBelow := below_bump_zero_of_read d.ambient_valid hTargetRead
  have hDest : md.sourceParent.column + shift < sourceColumn + shift := by
    rw [d.destination]
    exact (Array.getElem?_eq_some_iff.mp md.parent_nodes).1
  have hCopy : copyEdge mountain ⟨sourceColumn, marker.index + 1⟩ shift rootColumn
      (Row.bump md.targetCell.row 0) =
      .ok ⟨Row.bump md.targetCell.row 0, 0, some ⟨md.sourceParent.column + shift, md.targetIndex⟩⟩ := by
    simp only [copyEdge, hRead, bind_ok, hNonzero, ↓reduceIte, leftOf, md.upper_left,
      not_lt_of_ge hRoot, hBelow, hDest, not_true_eq_false, pure_ok]
  simp only [contour, hNotStop, ↓reduceIte, hStrict, not_true_eq_false, hDegree, hCopy,
    bind_ok, pure_ok] at hRun
  cases hTail : contour mountain sourceColumn (d.bucket.map Ref.index) shift rootColumn
      (marker.index + 1) (Row.bump md.targetCell.row 0) md.upper rest with
  | error e => simp only [hTail, bind_error, reduceCtorEq] at hRun
  | ok tail =>
    have hPath := (Except.ok.inj (by simpa only [hTail, bind_ok] using hRun)).symm
    rw [hPath] at hHead
    exact Option.some.inj hHead.symm

/-- This discharges the raw row/left-reference geometry of the actual
marker-contour origin. The current numerical parent search remains open. -/
theorem ExecutedSegmentPair.marker_contour_geometry
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {mountain : Mountain} {references : List Ref} {sourceColumn shift : Nat}
    {d : ColumnCopyData mountain p.marked references sourceColumn shift p.root.column}
    (hSource : p.reduced[sourceColumn]? = some d.sources)
    (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (i : Nat) (cell : Cell),
      (d.marker_data marker hm).parentNodes[i]? = some cell ∧ cell.row = (d.marker_data marker hm).current.row)
    {index : Nat} {lower upper : Cell} (pair : ExecutedSegmentPair d index lower upper)
    (hReal : lower.row ≠ 0) (hLowerEq : pair.originalLower = pair.copied)
    (hEmpty : pair.fill = []) (hHead : pair.path.head? = some pair.originalUpper) :
    ∃ parentRef parent, upper.left = some parentRef ∧
      Canonical.cellAt mountain parentRef = .ok parent ∧ parentRef.column < mountain.size ∧
      parent.row = lower.row ∧ upper.row = Row.B lower.row parent.row := by
  let md := d.marker_data pair.marker pair.member
  have hCopiedRow := copyEdge_return_row pair.copy_run
  have hLowerRow : lower.row = md.current.row :=
    (pair.lower_shape.1.symm.trans (congrArg Cell.row hLowerEq)).trans hCopiedRow
  have hIndex : 0 < pair.marker.index := by
    by_contra hn
    have hz : pair.marker.index = 0 := by omega
    have hZeroRead : d.sources[0]? = some md.current := by simpa only [hz] using md.current_at
    have hSame : md.current = phantom := Option.some.inj
      (hZeroRead.symm.trans d.source_valid.phantom)
    exact hReal (hLowerRow.trans (by rw [hSame]; rfl))
  obtain ⟨hUpperRow, hRoot⟩ := d.prepared_real_marker_successor hSource pair.member hIndex
  have hExpected := d.successor_contour_head_of_read pair.member hUpperRow hRoot pair.contour_run hHead
  obtain ⟨hp, hNodesEq⟩ := Array.getElem?_eq_some_iff.mp md.parent_nodes
  have hCV : ColumnValid mountain (md.sourceParent.column + shift) md.parentNodes :=
    hNodesEq ▸ d.ambient_valid _ hp
  obtain ⟨lowIndex, lowCell, hLow, hLowRow⟩ := hParentLow pair.marker pair.member
  have hTargetEq : md.targetCell.row = md.current.row := by
    apply le_antisymm _ md.target_lower
    apply le_of_not_gt
    intro hRaised
    have hFirst := fillCellsAscending_head (fillRowsStrict_of_columnValid hCV) hLow md.target_at
      (by rw [hLowRow]; exact hRaised) (column := md.sourceParent.column + shift)
    rw [hLowRow] at hFirst
    change (pair.fill).head? = some _ at hFirst
    simp only [hEmpty, List.head?_nil, reduceCtorEq] at hFirst
  have hRead : Canonical.cellAt mountain ⟨md.sourceParent.column + shift, md.targetIndex⟩ = .ok md.targetCell :=
    cellAt_ok_iff.mpr ⟨md.parentNodes, md.parent_nodes, md.target_at⟩
  refine ⟨⟨md.sourceParent.column + shift, md.targetIndex⟩, md.targetCell, ?_, hRead, hp,
    hTargetEq.trans hLowerRow.symm, ?_⟩
  · rw [← pair.upper_shape.2, hExpected]
  · rw [← pair.upper_shape.1, hExpected]
    change Row.bump md.targetCell.row 0 = Row.B lower.row md.targetCell.row
    rw [hTargetEq, hLowerRow, Row.B_self]

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ColumnCopyData.prepared_real_marker_successor
#print axioms OmegaY.Expansion.ColumnCopyData.successor_contour_head_of_read
#print axioms OmegaY.Expansion.ExecutedSegmentPair.marker_contour_geometry
