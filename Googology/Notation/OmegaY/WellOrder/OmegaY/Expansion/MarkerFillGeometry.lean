/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/MarkerFillGeometry.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/MarkerFillGeometry.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.AdjacentCanonicalCases

set_option backward.do.legacy false

/-!
# The physical marker to first-fill row equation

The first ascending fill cell is derived from the actual parent column's
low node and strict row order. Its stored left endpoint is retained through
the actual adjacent-origin shapes. These are row and stored-reference
results, not numerical first-smaller or copied-normality assertions.
-/

namespace OmegaY.Expansion

open Canonical

/-- Every executable fill chunk before the actual low node is empty, so
the low node's first rung has offset zero in the full ascending fill. -/
theorem fillAscendingOffset_at_low_zero {nodes : Column} (hStrict : FillRowsStrict nodes)
    {column lowIndex : Nat} {lowCell : Cell} (hLow : nodes[lowIndex]? = some lowCell)
    (high : Row) : fillAscendingOffset nodes column lowCell.row high lowIndex = 0 := by
  have hLowBound := (Array.getElem?_eq_some_iff.mp hLow).1
  have hEmpty : ((List.range lowIndex).flatMap fun i =>
      (fillChunk nodes column lowCell.row high i).reverse) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro i hi
    have hBefore := List.mem_range.mp hi
    have hiBound : i < nodes.size := by omega
    have hRead : nodes[i]? = some nodes[i] := Array.getElem?_eq_getElem hiBound
    have hRow := hStrict i lowIndex nodes[i] lowCell hRead hLow hBefore
    have hNotEligible : ¬ (lowCell.row ≤ nodes[i].row ∧ nodes[i].row < high) :=
      fun h => (not_le_of_gt hRow) h.1
    simp only [fillChunk, hRead, Option.getD_some, hNotEligible, ↓reduceIte, List.reverse_nil]
  change ((List.range lowIndex).flatMap fun i =>
    (fillChunk nodes column lowCell.row high i).reverse).length = 0
  rw [hEmpty]
  rfl

/-- A nonempty interval with actual endpoints starts with the degree-zero
rung of its actual low node. No parent power or first-fill shape is assumed. -/
theorem fillCellsAscending_head {nodes : Column} (hStrict : FillRowsStrict nodes)
    {column lowIndex highIndex : Nat} {lowCell highCell : Cell}
    (hLow : nodes[lowIndex]? = some lowCell) (hHigh : nodes[highIndex]? = some highCell)
    (hRow : lowCell.row < highCell.row) :
    (fillCellsAscending nodes column lowCell.row highCell.row).head? =
      some (referenceRung lowCell.row column lowIndex 0) := by
  obtain ⟨upper, hUpper, hUpperRow, _⟩ := fill_successor hStrict hHigh le_rfl hLow hRow
  have hDegree : 0 < Row.jump lowCell.row upper.row := by
    by_contra hn
    exact (ne_of_lt hUpperRow) (Row.jump_eq_zero.mp (by omega))
  have hRead := fillCellsAscending_getElem (column := column) hLow hUpper
    (show lowCell.row ≤ lowCell.row ∧ lowCell.row < highCell.row from ⟨le_rfl, hRow⟩) hDegree
  rw [fillAscendingOffset_at_low_zero hStrict hLow, Nat.zero_add] at hRead
  simpa only [List.head?_eq_getElem?] using hRead

/-- At the caller's actual marker-fill adjacency, the upper cell points
to the actual low node of the shifted parent column. That node has the
physical marker row, so the next row is exactly B(marker, marker).
The given head is only the actual origin classification; its concrete
rung shape is proved here from parent-column reads. -/
theorem ExecutedSegmentPair.marker_fill_geometry
    {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
    {sourceColumn shift rootColumn : Nat}
    {d : ColumnCopyData mountain marked references sourceColumn shift rootColumn}
    {index : Nat} {lower upper : Cell} (pair : ExecutedSegmentPair d index lower upper)
    (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (lowIndex : Nat) (lowCell : Cell),
      (d.marker_data marker hm).parentNodes[lowIndex]? = some lowCell ∧
        lowCell.row = (d.marker_data marker hm).current.row)
    {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    (hLower : column[index]? = some lower) (hUpper : column[index + 1]? = some upper)
    (hLowerEq : pair.originalLower = pair.copied)
    (hHead : pair.fill.head? = some pair.originalUpper) :
    ∃ (parentRef : Ref) (parent : Cell),
      upper.left = some parentRef ∧
      Canonical.cellAt (mountain.push column) parentRef = .ok parent ∧
      parentRef.column < mountain.size ∧ parent.row = lower.row ∧
      upper.row = Row.B lower.row parent.row := by
  let s := d.marker_data pair.marker pair.member
  obtain ⟨copied, _, _, _, hCopied, hCopiedRow, _⟩ :=
    copySegment_result_decomposition d.ambient_valid d.source_column d.source_nonzero
      d.destination.le d.source_top references (d.bucket.map Ref.index)
      s.current_at s.upper_at s.upper_left s.parent_nodes s.target_at s.reference s.target_lower
      (d.segment_run pair.member)
  have hCopiedEq : copied = pair.copied := Except.ok.inj (hCopied.symm.trans pair.copy_run)
  have hPairCopiedRow : pair.copied.row = s.current.row :=
    (congrArg Cell.row hCopiedEq).symm.trans hCopiedRow
  have hLowerRow : lower.row = s.current.row :=
    (pair.lower_shape.1.symm.trans (congrArg Cell.row hLowerEq)).trans hPairCopiedRow
  obtain ⟨hp, hParentNodesEq⟩ := Array.getElem?_eq_some_iff.mp s.parent_nodes
  have hParentValid : ColumnValid mountain (s.sourceParent.column + shift) s.parentNodes :=
    hParentNodesEq ▸ d.ambient_valid _ hp
  have hStrict := fillRowsStrict_of_columnValid hParentValid
  have hFillMember : pair.originalUpper ∈ fillCells s.parentNodes (s.sourceParent.column + shift)
      s.current.row s.targetCell.row := by
    apply (fillCellsAscending_perm _ _ _ _).mem_iff.mp
    exact List.mem_of_head? hHead
  have hUpperBound : upper.row ≤ s.targetCell.row :=
    pair.upper_shape.1.symm.trans_le
      (fillCells_row_bounds hStrict s.target_at le_rfl hFillMember).2
  obtain ⟨actualColumn, hActualRun, _, hValid, _, _⟩ := d.copyColumn_valid
  have hColumnEq : actualColumn = column := Except.ok.inj (hActualRun.symm.trans hRun)
  subst actualColumn
  have hPairRow := hValid.rows_strict _ _ _ _ hLower hUpper (Nat.lt_succ_self index)
  have hRaised : s.current.row < s.targetCell.row := by
    rw [← hLowerRow]
    exact hPairRow.trans_le hUpperBound
  obtain ⟨lowIndex, lowCell, hLow, hLowRow⟩ := hParentLow pair.marker pair.member
  have hFirst := fillCellsAscending_head hStrict hLow s.target_at
    (show lowCell.row < s.targetCell.row by rw [hLowRow]; exact hRaised)
    (column := s.sourceParent.column + shift)
  rw [hLowRow] at hFirst
  have hExpected : pair.originalUpper = referenceRung s.current.row
      (s.sourceParent.column + shift) lowIndex 0 := Option.some.inj (hHead.symm.trans hFirst)
  have hActualParent : Canonical.cellAt mountain ⟨s.sourceParent.column + shift, lowIndex⟩ = .ok lowCell :=
    cellAt_ok_iff.mpr ⟨s.parentNodes, s.parent_nodes, hLow⟩
  have hUpperLeft : upper.left = some ⟨s.sourceParent.column + shift, lowIndex⟩ := by
    rw [← pair.upper_shape.2, hExpected]
    rfl
  have hUpperRow : upper.row = Row.bump s.current.row 0 := by
    rw [← pair.upper_shape.1, hExpected]
    rfl
  exact ⟨⟨s.sourceParent.column + shift, lowIndex⟩, lowCell, hUpperLeft,
    (cellAt_push_left hp).trans hActualParent, hp, hLowRow.trans hLowerRow.symm,
    by rw [hUpperRow, hLowerRow, hLowRow, Row.B_self]⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.fillAscendingOffset_at_low_zero
#print axioms OmegaY.Expansion.fillCellsAscending_head
#print axioms OmegaY.Expansion.ExecutedSegmentPair.marker_fill_geometry
