/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Canonical/RealLegs.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Canonical/RealLegs.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Domain

set_option backward.do.legacy false

/-! Positive stored left endpoints above the real bottom in actual canonical
source mountains. These facts use the proved Normal certificate of the source;
MountainValid alone deliberately does not assert this stronger property. -/

namespace OmegaY.Canonical

open Geometry

theorem build_above_bottom_left {values : List Nat} {mountain : Mountain}
    (hBuild : build values = .ok mountain) (u : (Frame.ofMountain mountain).Node)
    (hIndex : 1 < u.2.val) :
    ∃ p : (Frame.ofMountain mountain).Node,
      ((Frame.ofMountain mountain).cell u).left = some (Frame.ref p) ∧
      0 < (Frame.ofMountain mountain).value p ∧
      (1 : Row) ≤ (Frame.ofMountain mountain).height p ∧
      (Frame.ofMountain mountain).height p < (Frame.ofMountain mountain).height u ∧
      p.1.val < u.1.val := by
  have hN := build_normal_of_success hBuild
  rcases u with ⟨c, i⟩
  change 1 < i.val at hIndex
  have hLowerIndex : i.val - 1 < (Frame.ofMountain mountain).length c := by
    have hi := i.isLt
    omega
  let lower : (Frame.ofMountain mountain).Node := ⟨c, ⟨i.val - 1, hLowerIndex⟩⟩
  have hLowerReal : Frame.Real lower := by change 0 < i.val - 1; omega
  have hUpper : (Frame.ofMountain mountain).upper lower = some ⟨c, i⟩ := by
    have he : i.val - 1 + 1 = i.val := by omega
    simp [Frame.upper, lower, he, i.isLt]
  obtain ⟨p, hParent, hRow, _hValue, hLeft⟩ := hN.upper_step lower ⟨c, i⟩ hLowerReal hUpper
  have hPositive := (Frame.P_value hN.toOrdered hParent).1
  have hReal := Frame.real_of_value_pos hN.toOrdered hPositive
  have hLowerAbove : (Frame.ofMountain mountain).height lower <
      (Frame.ofMountain mountain).height ⟨c, i⟩ := by
    rw [hRow]
    exact Row.lt_B _ _
  have hColumn : p.1.val < c.val := by
    simpa only [lower] using Frame.P_column_lt hN.toOrdered hParent
  exact ⟨p, hLeft, hPositive, Frame.one_le_height hN.toOrdered hReal,
    (Frame.P_height_le hN.toOrdered hParent).trans_lt hLowerAbove,
    hColumn⟩

/-- The strong source-leg fact stated entirely in actual stored references
and reads, suitable for later fixed-endpoint copy arguments. -/
theorem build_above_bottom_stored_parent {values : List Nat} {mountain : Mountain}
    (hBuild : build values = .ok mountain) {source : Ref} {sourceCell : Cell}
    (hSource : cellAt mountain source = .ok sourceCell) (hIndex : 1 < source.index) :
    ∃ (parent : Ref) (parentCell : Cell), sourceCell.left = some parent ∧
      cellAt mountain parent = .ok parentCell ∧ 0 < parentCell.value ∧
      (1 : Row) ≤ parentCell.row ∧ parentCell.row < sourceCell.row ∧
      parent.column < source.column := by
  obtain ⟨u, hRef, hCell⟩ := frame_node_of_cellAt hSource
  have hUIndex : 1 < u.2.val := by
    have hi := congrArg Ref.index hRef
    change u.2.val = source.index at hi
    omega
  obtain ⟨p, hLeft, hPositive, hOne, hRow, hColumn⟩ := build_above_bottom_left hBuild u hUIndex
  refine ⟨Frame.ref p, (Frame.ofMountain mountain).cell p, ?_,
    cellAt_of_frame_node mountain p, hPositive, hOne, ?_, ?_⟩
  · simpa only [hCell] using hLeft
  · simpa only [Frame.height, hCell] using hRow
  · have hc := congrArg Ref.column hRef
    change u.1.val = source.column at hc
    change p.1.val < source.column
    omega

/-- The exceptional real bottom has exactly row 1. Its phantom left endpoint
is covered separately by BottomLegs, and is not asserted positive here. -/
theorem build_bottom_row_of_read {values : List Nat} {mountain : Mountain}
    (hBuild : build values = .ok mountain) {source : Ref} {sourceCell : Cell}
    (hSource : cellAt mountain source = .ok sourceCell) (hIndex : source.index = 1) :
    sourceCell.row = 1 := by
  obtain ⟨nodes, hNodes, hCell⟩ := cellAt_ok_iff.mp hSource
  obtain ⟨hc, hNodesEq⟩ := Array.getElem?_eq_some_iff.mp hNodes
  have hValid : ColumnValid mountain source.column nodes := by
    rw [← hNodesEq]
    exact build_valid_of_success hBuild source.column hc
  exact hValid.bottom_row sourceCell (by simpa only [hIndex] using hCell)

end OmegaY.Canonical

#print axioms OmegaY.Canonical.build_above_bottom_left
#print axioms OmegaY.Canonical.build_above_bottom_stored_parent
#print axioms OmegaY.Canonical.build_bottom_row_of_read
