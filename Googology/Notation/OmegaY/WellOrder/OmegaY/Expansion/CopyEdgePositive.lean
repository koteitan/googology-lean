/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/CopyEdgePositive.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/CopyEdgePositive.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.CopyEdge
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.RealLegs

set_option backward.do.legacy false

/-! The extra positive-parent interface needed by numerical backfill.
Fixed endpoints use an explicit positive source-parent read. Shifted endpoints
use the real row-1 bottom below a target strictly above 1. No copied Normal
certificate or successful-backfill hypothesis is assumed. -/

namespace OmegaY.Expansion

open Canonical

theorem lookup_positive_of_row_nonzero {mountain : Mountain}
    (hValid : MountainValid mountain) {ref : Ref} {cell : Cell}
    (hRead : lookup mountain ref = .ok cell) (hNonzero : cell.row ≠ 0) : 0 < cell.value := by
  obtain ⟨nodes, hNodes, hCell⟩ := lookup_ok_iff.mp hRead
  obtain ⟨hc, hNodesEq⟩ := Array.getElem?_eq_some_iff.mp hNodes
  have hCV : ColumnValid mountain ref.column nodes := by
    rw [← hNodesEq]
    exact hValid ref.column hc
  have hReal : 0 < ref.index := by
    by_contra hn
    have hi : ref.index = 0 := by omega
    rw [hi, hCV.phantom] at hCell
    have he : cell = phantom := Option.some.inj hCell.symm
    exact hNonzero (by rw [he]; rfl)
  exact hCV.real_positive ref.index cell hCell hReal

/-- A target above row 1 makes the actual real bottom eligible. The selected
highest lower node is therefore real and has positive value. -/
theorem below_above_one_total {mountain : Mountain} (hValid : MountainValid mountain)
    {column : Nat} (hc : column < mountain.size) {target : Row} (hAbove : (1 : Row) < target) :
    ∃ (parent : Ref) (parentCell : Cell), below mountain column target = .ok parent ∧
      lookup mountain parent = .ok parentCell ∧ parent.column = column ∧
      (1 : Row) ≤ parentCell.row ∧ parentCell.row < target ∧ 0 < parentCell.value := by
  have hi : 1 < mountain[column].size := by have := (hValid column hc).size_ge_two; omega
  let bottom := mountain[column][1]
  have hBottom : mountain[column][1]? = some bottom := Array.getElem?_eq_getElem hi
  have hBottomRow : bottom.row = 1 := (hValid column hc).bottom_row bottom hBottom
  have hRead : Canonical.cellAt mountain ⟨column, 1⟩ = .ok bottom :=
    cellAt_ok_iff.mpr ⟨mountain[column], Array.getElem?_eq_getElem hc, hBottom⟩
  obtain ⟨parent, parentCell, hBelow, hParent, hColumn, hLow, hHigh⟩ :=
    below_between hValid hRead (by simpa only [hBottomRow] using hAbove)
  have hLookup := lookup_ok_iff.mpr (cellAt_ok_iff.mp hParent)
  have hOne : (1 : Row) ≤ parentCell.row := by simpa only [hBottomRow] using hLow
  have hNonzero : parentCell.row ≠ 0 := ne_of_gt (Row.zero_lt_one.trans_le hOne)
  exact ⟨parent, parentCell, hBelow, hLookup, hColumn, hOne, hHigh,
    lookup_positive_of_row_nonzero hValid hLookup hNonzero⟩

/-- Both endpoint branches have positive values under their distinct concrete
premises. This strengthens copyEdge totality only where backfill needs it. -/
theorem copyEdge_positive_parent {mountain : Mountain} (hValid : MountainValid mountain)
    {source : Ref} {sourceCell : Cell} (hSource : lookup mountain source = .ok sourceCell)
    (hColumn : 0 < source.column) {shift rootColumn : Nat} {targetRow : Row}
    (hDestination : source.column + shift ≤ mountain.size) (hNonzero : sourceCell.row ≠ 0)
    (hAbove : (1 : Row) < targetRow)
    {oldParent : Ref} {oldParentCell : Cell} (hOldLeft : sourceCell.left = some oldParent)
    (hOldRead : lookup mountain oldParent = .ok oldParentCell) (hOldPositive : 0 < oldParentCell.value) :
    ∃ (copied : Cell) (parent : Ref) (parentCell : Cell),
      copyEdge mountain source shift rootColumn targetRow = .ok copied ∧
      copied.row = targetRow ∧ copied.value = 0 ∧ copied.left = some parent ∧
      lookup mountain parent = .ok parentCell ∧ parent.column < source.column + shift ∧
      0 < parentCell.value := by
  obtain ⟨copied, parent, parentCell, hCopy, hRow, hValue, hLeft, hRead, hDest, hEndpoint⟩ :=
    copyEdge_nonphantom_total hValid hSource hColumn hDestination hNonzero
      (Row.zero_lt_one.trans hAbove)
  refine ⟨copied, parent, parentCell, hCopy, hRow, hValue, hLeft, hRead, hDest, ?_⟩
  obtain ⟨sourceParent, hSourceLeft, hSourceParentLeft, hFixed | hShifted⟩ := hEndpoint
  · have hEq : sourceParent = oldParent := Option.some.inj (hSourceLeft.symm.trans hOldLeft)
    have hp : parent = oldParent := hFixed.2.1.trans hEq
    have hCellEq : parentCell = oldParentCell := by
      rw [hp] at hRead
      exact Except.ok.inj (hRead.symm.trans hOldRead)
    exact hCellEq ▸ hOldPositive
  · have hc : sourceParent.column + shift < mountain.size := by omega
    obtain ⟨found, foundCell, hFound, hFoundRead, _, _, _, hPositive⟩ :=
      below_above_one_total hValid hc hAbove
    have he : found = parent := Except.ok.inj (hFound.symm.trans hShifted.2.2.1)
    subst found
    have hCellEq : foundCell = parentCell := Except.ok.inj (hFoundRead.symm.trans hRead)
    exact hCellEq ▸ hPositive

end OmegaY.Expansion

#print axioms OmegaY.Expansion.lookup_positive_of_row_nonzero
#print axioms OmegaY.Expansion.below_above_one_total
#print axioms OmegaY.Expansion.copyEdge_positive_parent
