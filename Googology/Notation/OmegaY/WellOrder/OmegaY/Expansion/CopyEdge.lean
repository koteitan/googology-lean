/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/CopyEdge.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/CopyEdge.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.BoundarySelection

set_option backward.do.legacy false

/-!
# Actual copying of one stored edge

The source's stored left endpoint is derived from concrete mountain validity.
In the translated case, the target column's phantom supplies an actual node
below every positive requested row. Thus success of `below` is a conclusion.
This module does not assume that the copied output column is already valid.
-/

namespace OmegaY.Expansion

open Canonical

@[simp] private theorem edge_bind_ok {α β : Type} (a : α) (f : α → Result β) :
    (Except.ok a >>= f) = f a := rfl
@[simp] private theorem edge_pure_ok {α : Type} (a : α) :
    (pure a : Result α) = .ok a := rfl
@[simp] private theorem edge_throw {α : Type} (e : Error) :
    (throw e : Result α) = .error e := rfl

/-- Every nonphantom source in a nonfirst column has its concrete stored
left endpoint, strictly to the left, with height at most the source height. -/
theorem stored_left_of_lookup {mountain : Mountain} (hValid : MountainValid mountain)
    {source : Ref} {sourceCell : Cell} (hSource : lookup mountain source = .ok sourceCell)
    (hColumn : 0 < source.column) (hNonzero : sourceCell.row ≠ 0) :
    ∃ (parent : Ref) (parentCell : Cell), sourceCell.left = some parent ∧
      parent.column < source.column ∧ lookup mountain parent = .ok parentCell ∧
      parentCell.row ≤ sourceCell.row := by
  obtain ⟨nodes, hNodes, hCell⟩ := lookup_ok_iff.mp hSource
  obtain ⟨hc, hNodesEq⟩ := Array.getElem?_eq_some_iff.mp hNodes
  have hColValid : ColumnValid mountain source.column nodes := by
    rw [← hNodesEq]
    exact hValid source.column hc
  have hReal : 0 < source.index := by
    by_contra hn
    have hi : source.index = 0 := by omega
    rw [hi, hColValid.phantom] at hCell
    have he : sourceCell = phantom := Option.some.inj hCell.symm
    exact hNonzero (by rw [he]; rfl)
  obtain ⟨parent, hLeft⟩ := hColValid.stored_exists _ _ hCell hReal hColumn
  obtain ⟨hParentLeft, parentCell, hParent, hRow⟩ := hColValid.stored_valid _ _ _ hCell hLeft
  exact ⟨parent, parentCell, hLeft, hParentLeft,
    lookup_ok_iff.mpr (cellAt_ok_iff.mp hParent), hRow⟩

theorem copyEdge_phantom {mountain : Mountain} {source : Ref} {sourceCell : Cell}
    (hSource : lookup mountain source = .ok sourceCell) (hZero : sourceCell.row = 0)
    (shift rootColumn : Nat) (targetRow : Row) :
    copyEdge mountain source shift rootColumn targetRow = .ok ⟨targetRow, 0, none⟩ := by
  simp [copyEdge, hSource, hZero]

/-- The exact source-relative choice of endpoint. Fixed parents retain their
old height bound; translated parents are selected strictly below the new row. -/
def CopyEndpoint (mountain : Mountain) (source : Ref) (sourceCell : Cell)
    (shift rootColumn : Nat) (targetRow : Row) (parent : Ref) (parentCell : Cell) : Prop :=
  ∃ oldParent : Ref, sourceCell.left = some oldParent ∧ oldParent.column < source.column ∧
    ((oldParent.column < rootColumn ∧ parent = oldParent ∧ parentCell.row ≤ sourceCell.row) ∨
      (rootColumn ≤ oldParent.column ∧ parent.column = oldParent.column + shift ∧
        below mountain (oldParent.column + shift) targetRow = .ok parent ∧ parentCell.row < targetRow))

theorem copyEdge_nonphantom_total {mountain : Mountain} (hValid : MountainValid mountain)
    {source : Ref} {sourceCell : Cell} (hSource : lookup mountain source = .ok sourceCell)
    (hColumn : 0 < source.column) {shift rootColumn : Nat} {targetRow : Row}
    (hDestination : source.column + shift ≤ mountain.size)
    (hNonzero : sourceCell.row ≠ 0) (hPositive : 0 < targetRow) :
    ∃ (copied : Cell) (parent : Ref) (parentCell : Cell),
      copyEdge mountain source shift rootColumn targetRow = .ok copied ∧
      copied.row = targetRow ∧ copied.value = 0 ∧ copied.left = some parent ∧
      lookup mountain parent = .ok parentCell ∧ parent.column < source.column + shift ∧
      CopyEndpoint mountain source sourceCell shift rootColumn targetRow parent parentCell := by
  obtain ⟨oldParent, oldParentCell, hLeft, hParentLeft, hOldRead, hOldRow⟩ :=
    stored_left_of_lookup hValid hSource hColumn hNonzero
  by_cases hFixed : oldParent.column < rootColumn
  · have hDest : oldParent.column < source.column + shift := by omega
    refine ⟨⟨targetRow, 0, some oldParent⟩, oldParent, oldParentCell,
      ?_, rfl, rfl, rfl, hOldRead, hDest,
      oldParent, hLeft, hParentLeft, Or.inl ⟨hFixed, rfl, hOldRow⟩⟩
    have hNot : ¬ source.column + shift ≤ oldParent.column := by omega
    simp [copyEdge, hSource, hNonzero, leftOf, hLeft, hFixed, hNot]
  · have hc : oldParent.column + shift < mountain.size := by omega
    obtain ⟨parent, hBelow⟩ := below_positive_total hValid hc hPositive
    have hNodes := Array.getElem?_eq_getElem hc
    obtain ⟨hParentColumn, parentCell, hParentIndex, hParentRow⟩ := below_result hNodes hBelow
    have hParentRead : lookup mountain parent = .ok parentCell :=
      lookup_ok_iff.mpr ⟨mountain[oldParent.column + shift],
        by simpa only [hParentColumn] using hNodes, hParentIndex⟩
    have hDest : parent.column < source.column + shift := by omega
    refine ⟨⟨targetRow, 0, some parent⟩, parent, parentCell,
      ?_, rfl, rfl, rfl, hParentRead, hDest,
      oldParent, hLeft, hParentLeft,
      Or.inr ⟨Nat.le_of_not_gt hFixed, hParentColumn, hBelow, hParentRow⟩⟩
    have hNot : ¬ source.column + shift ≤ parent.column := by omega
    simp [copyEdge, hSource, hNonzero, leftOf, hLeft, hFixed, hBelow, hNot]

/-- A lightweight totality interface for the contour and marker loops. -/
theorem copyEdge_total {mountain : Mountain} (hValid : MountainValid mountain)
    {source : Ref} {sourceCell : Cell} (hSource : lookup mountain source = .ok sourceCell)
    (hColumn : 0 < source.column) {shift rootColumn : Nat} {targetRow : Row}
    (hDestination : source.column + shift ≤ mountain.size)
    (hPositive : sourceCell.row ≠ 0 → 0 < targetRow) :
    ∃ copied, copyEdge mountain source shift rootColumn targetRow = .ok copied ∧
      copied.row = targetRow ∧ copied.value = 0 := by
  by_cases hZero : sourceCell.row = 0
  · exact ⟨⟨targetRow, 0, none⟩, copyEdge_phantom hSource hZero _ _ _, rfl, rfl⟩
  · obtain ⟨copied, parent, parentCell, hCopy, hRow, hValue, _⟩ :=
      copyEdge_nonphantom_total hValid hSource hColumn hDestination hZero (hPositive hZero)
    exact ⟨copied, hCopy, hRow, hValue⟩

theorem CopyEndpoint.row_le {mountain : Mountain} {source : Ref} {sourceCell : Cell}
    {shift rootColumn : Nat} {targetRow : Row} {parent : Ref} {parentCell : Cell}
    (hEndpoint : CopyEndpoint mountain source sourceCell shift rootColumn targetRow parent parentCell)
    (hLift : sourceCell.row ≤ targetRow) : parentCell.row ≤ targetRow := by
  obtain ⟨_, _, _, hFixed | hShifted⟩ := hEndpoint
  · exact hFixed.2.2.trans hLift
  · exact hShifted.2.2.2.le

/-- If the requested row is no lower than the source row, both endpoint
branches give the row bound required by the concrete stored-leg invariant. -/
theorem copyEdge_nonphantom_row_bound {mountain : Mountain} (hValid : MountainValid mountain)
    {source : Ref} {sourceCell : Cell} (hSource : lookup mountain source = .ok sourceCell)
    (hColumn : 0 < source.column) {shift rootColumn : Nat} {targetRow : Row}
    (hDestination : source.column + shift ≤ mountain.size)
    (hNonzero : sourceCell.row ≠ 0) (hPositive : 0 < targetRow)
    (hLift : sourceCell.row ≤ targetRow) :
    ∃ (copied : Cell) (parent : Ref) (parentCell : Cell),
      copyEdge mountain source shift rootColumn targetRow = .ok copied ∧
      copied.row = targetRow ∧ copied.value = 0 ∧ copied.left = some parent ∧
      lookup mountain parent = .ok parentCell ∧ parent.column < source.column + shift ∧
      parentCell.row ≤ copied.row := by
  obtain ⟨copied, parent, parentCell, hCopy, hRow, hValue, hLeft, hRead, hDest, hEndpoint⟩ :=
    copyEdge_nonphantom_total hValid hSource hColumn hDestination hNonzero hPositive
  exact ⟨copied, parent, parentCell, hCopy, hRow, hValue, hLeft, hRead, hDest,
    hRow ▸ hEndpoint.row_le hLift⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.stored_left_of_lookup
#print axioms OmegaY.Expansion.copyEdge_nonphantom_total
#print axioms OmegaY.Expansion.copyEdge_total
#print axioms OmegaY.Expansion.copyEdge_nonphantom_row_bound
