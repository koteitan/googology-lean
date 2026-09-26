/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualMovedEdge.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/ActualMovedEdge.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ActualIntervalParent

set_option backward.do.legacy false

/-!
# Exact moved copyEdge calls in an actual root interval

The source upper read and stored parent are obtained from source normality
and preservation of the frozen source columns. The actual below result is
then executed by copyEdge. This describes one copied edge, not adjacency or
numerical reconstruction of an already completed child column.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- Actual parent selection determines the real copied cell, its stored
left reference, and its exact B row. No copy success, stored-left identity,
source nonzero proof, or destination condition is supplied by the caller. -/
theorem DynamicBlockState.copyEdge_moved_interval_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {index : Nat} {sourceRow : Row}
    (a : ActualRootInterval p start ambient references index sourceRow)
    (hRaised : sourceRow < a.target.row)
    {child parent upper : (Frame.ofMountain p.reduced).Node}
    (hChild : Frame.RootInterval (Frame.ofMountain p.reduced) a.root
      (Row.bump sourceRow a.degree) child)
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next)
    (hUpper : (Frame.ofMountain p.reduced).upper child = some upper)
    (hParentColumn : p.root.column ≤ parent.1.val) :
    ∃ (copied : Cell) (actualRef : Ref) (actualParent : Cell),
      copyEdge ambient (Frame.ref upper) (block * (p.reduced.size - 1 - p.root.column)) p.root.column
        (Row.lift sourceRow a.target.row ((Frame.ofMountain p.reduced).height upper)) = .ok copied ∧
      copied.row = Row.lift sourceRow a.target.row ((Frame.ofMountain p.reduced).height upper) ∧
      copied.value = 0 ∧ copied.left = some actualRef ∧
      actualRef.column = parent.1.val + block * (p.reduced.size - 1 - p.root.column) ∧
      Canonical.cellAt ambient actualRef = .ok actualParent ∧
      actualParent.row = Row.lift sourceRow a.target.row ((Frame.ofMountain p.reduced).height parent) ∧
      copied.row = Row.B (Row.lift sourceRow a.target.row ((Frame.ofMountain p.reduced).height child))
        actualParent.row := by
  let F := Frame.ofMountain p.reduced
  obtain ⟨actualRef, actualParent, hRefColumn, hBelow, hRead, hParentRow, hB⟩ :=
    s.actual_interval_parent history hLast a hRaised hChild hParent hChildColumn hUpper hParentColumn
  have hNormal := build_normal_of_success p.reduced_build
  have hChildReal : Frame.Real child := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  obtain ⟨oldParent, hOldParent, _, _, hStored⟩ := hNormal.upper_step child upper hChildReal hUpper
  have hParentEq : oldParent = parent := Option.some.inj (hOldParent.symm.trans hParent)
  subst oldParent
  change (F.cell upper).left = some (Frame.ref parent) at hStored
  have hSourceRead : lookup ambient (Frame.ref upper) = .ok (F.cell upper) :=
    lookup_ok_iff.mpr (cellAt_ok_iff.mp
      (p.cell_read_preserved s.base_ambient (cellAt_of_frame_node p.reduced upper)))
  have hUpperReal : Frame.Real upper := by
    have hi := (Frame.upper_spec hUpper).2
    unfold Frame.Real
    omega
  have hNonzero : (F.cell upper).row ≠ 0 := by
    intro hz
    have hPositive := Frame.one_le_height hNormal.toOrdered hUpperReal
    change (1 : Row) ≤ (F.cell upper).row at hPositive
    rw [hz] at hPositive
    exact (not_le_of_gt Row.zero_lt_one) hPositive
  have hDestination : actualRef.column <
      (Frame.ref upper).column + block * (p.reduced.size - 1 - p.root.column) := by
    rw [hRefColumn]
    apply Nat.add_lt_add_right
    change parent.1.val < upper.1.val
    rw [(Frame.upper_spec hUpper).1]
    exact Frame.P_column_lt hNormal.toOrdered hParent
  let copied : Cell :=
    ⟨Row.lift sourceRow a.target.row (F.height upper), 0, some actualRef⟩
  refine ⟨copied, actualRef, actualParent, ?_, rfl, rfl, rfl, hRefColumn, hRead, hParentRow, hB⟩
  change below ambient ((Frame.ref parent).column + block * (p.reduced.size - 1 - p.root.column))
    (Row.lift sourceRow a.target.row ((Frame.ofMountain p.reduced).height upper)) = .ok actualRef at hBelow
  have hMoved : ¬ (Frame.ref parent).column < p.root.column := Nat.not_lt_of_ge hParentColumn
  simp [copyEdge, copied, hSourceRead, hNonzero, leftOf, hStored,
    hMoved, hBelow, Nat.not_le_of_gt hDestination]
  rfl

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.copyEdge_moved_interval_parent
