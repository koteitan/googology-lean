/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ShiftedEdgeInterval.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/ShiftedEdgeInterval.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.CopyEdge
import Googology.Notation.OmegaY.WellOrder.OmegaY.Rows.EdgeTransport

set_option backward.do.legacy false

/-! Actual adjacent parent nodes identify the strict-below selector. The
lifted-edge theorem requires those real parent-interval witnesses; mere
row occurrence or a power-step property is deliberately not substituted. -/

namespace OmegaY.Expansion

open Canonical

theorem below_eq_of_adjacent {mountain : Mountain} (hValid : MountainValid mountain)
    {column index : Nat} {nodes : Column} (hNodes : mountain[column]? = some nodes)
    {lower upper : Cell} (hLower : nodes[index]? = some lower)
    (hUpper : nodes[index + 1]? = some upper) {ceiling : Row}
    (hLow : lower.row < ceiling) (hHigh : ceiling ≤ upper.row) :
    below mountain column ceiling = .ok ⟨column, index⟩ := by
  obtain ⟨found, hFound⟩ := (below_succeeds_iff hNodes ceiling).mpr ⟨index, lower, hLower, hLow⟩
  obtain ⟨hColumn, cell, hCell, hCellRow⟩ := below_result hNodes hFound
  have hIndexLow := below_max_index hNodes hFound hLower hLow
  obtain ⟨hc, hNodesEq⟩ := Array.getElem?_eq_some_iff.mp hNodes
  have hCV : ColumnValid mountain column nodes := hNodesEq ▸ hValid column hc
  have hIndexHigh : found.index < index + 1 := by
    by_contra h
    have hLe : index + 1 ≤ found.index := by omega
    have hUpperLe : upper.row ≤ cell.row := by
      rcases eq_or_lt_of_le hLe with he | hlt
      · have hSame : upper = cell := Option.some.inj ((he ▸ hUpper).symm.trans hCell)
        rw [hSame]
      · exact (hCV.rows_strict _ _ _ _ hUpper hCell hlt).le
    exact (not_lt_of_ge (hHigh.trans hUpperLe)) hCellRow
  have hIndexEq : found.index = index := by omega
  have hRef : found = ⟨column, index⟩ := by
    cases found
    simp_all only
  simpa only [hRef] using hFound

theorem copyEdge_shifted_exact {mountain : Mountain} (hValid : MountainValid mountain)
    {source : Ref} {sourceCell : Cell} (hSource : lookup mountain source = .ok sourceCell)
    (hReal : sourceCell.row ≠ 0) {oldParent : Ref} (hLeft : sourceCell.left = some oldParent)
    (hLeftward : oldParent.column < source.column) {shift rootColumn index : Nat}
    (hMoved : rootColumn ≤ oldParent.column) {nodes : Column}
    (hNodes : mountain[oldParent.column + shift]? = some nodes)
    {lower upper : Cell} (hLower : nodes[index]? = some lower)
    (hUpper : nodes[index + 1]? = some upper) {target : Row}
    (hLow : lower.row < target) (hHigh : target ≤ upper.row) :
    copyEdge mountain source shift rootColumn target =
      .ok ⟨target, 0, some ⟨oldParent.column + shift, index⟩⟩ := by
  have hBelow := below_eq_of_adjacent hValid hNodes hLower hUpper hLow hHigh
  have hNotFixed : ¬ oldParent.column < rootColumn := Nat.not_lt_of_ge hMoved
  simp [copyEdge, hSource, hReal, leftOf, hLeft, hNotFixed, hBelow, hLeftward]

/-- When both old lower and old parent lie above the same lift root, actual
support and an actual adjacent upper barrier identify the moved parent.
The exact B formula is a conclusion, via lift_B and actual copyEdge. -/
theorem copyEdge_lifted_parent_interval {mountain : Mountain} (hValid : MountainValid mountain)
    {source : Ref} {sourceCell oldLower oldParentCell : Cell}
    (hSource : lookup mountain source = .ok sourceCell) (hReal : sourceCell.row ≠ 0)
    {oldParent : Ref} (hLeft : sourceCell.left = some oldParent)
    (hLeftward : oldParent.column < source.column)
    (hOldB : sourceCell.row = Row.B oldLower.row oldParentCell.row)
    {shift rootColumn index : Nat} (hMoved : rootColumn ≤ oldParent.column)
    {root target : Row} (hRootLower : root ≤ oldLower.row) (hRootParent : root ≤ oldParentCell.row)
    {nodes : Column} (hNodes : mountain[oldParent.column + shift]? = some nodes)
    {parent barrier : Cell} (hParent : nodes[index]? = some parent)
    (hBarrier : nodes[index + 1]? = some barrier)
    (hParentRow : parent.row = Row.lift root target oldParentCell.row)
    (hParentLow : parent.row < Row.lift root target sourceCell.row)
    (hParentHigh : Row.lift root target sourceCell.row ≤ barrier.row) :
    copyEdge mountain source shift rootColumn (Row.lift root target sourceCell.row) =
      .ok ⟨Row.lift root target sourceCell.row, 0, some ⟨oldParent.column + shift, index⟩⟩ ∧
      Row.lift root target sourceCell.row = Row.B (Row.lift root target oldLower.row) parent.row := by
  refine ⟨copyEdge_shifted_exact hValid hSource hReal hLeft hLeftward hMoved hNodes
    hParent hBarrier hParentLow hParentHigh, ?_⟩
  rw [hOldB, hParentRow]
  exact Row.lift_B hRootLower hRootParent

end OmegaY.Expansion

#print axioms OmegaY.Expansion.below_eq_of_adjacent
#print axioms OmegaY.Expansion.copyEdge_lifted_parent_interval
