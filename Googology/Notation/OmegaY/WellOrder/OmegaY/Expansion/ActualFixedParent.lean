/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualFixedParent.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/ActualFixedParent.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ActualRootInterval
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.RootTransport

set_option backward.do.legacy false

/-!
# Actual fixed parents left of the bad-root column

The source upper's stored endpoint is obtained from the successful source
build. The dynamic state preserves its entire source column. At an exit to
the left of the bad root, the upper row is above the actual reference cap
and stays fixed; the copied edge keeps the same stored parent and satisfies
the B equation with the lifted lower endpoint.

This is an exact copyEdge statement. Numerical first-smaller recovery on
the completed child column is a separate obligation.
-/

namespace OmegaY.Expansion

open Canonical Geometry

theorem DynamicBlockState.copyEdge_fixed_interval_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    {index : Nat} {sourceRow : Row}
    (a : ActualRootInterval p start ambient references index sourceRow)
    (hRaised : sourceRow < a.target.row)
    {child parent upper : (Frame.ofMountain p.reduced).Node}
    (hParent : findParent p.reduced (Frame.ref child) = .ok (Frame.ref parent))
    (hChild : Frame.RootInterval (Frame.ofMountain p.reduced) a.root
      (Row.bump sourceRow a.degree) child)
    (hUpper : (Frame.ofMountain p.reduced).upper child = some upper)
    (hFixed : parent.1.val < p.root.column) :
    copyEdge ambient (Frame.ref upper)
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column
      (Row.lift sourceRow a.target.row ((Frame.ofMountain p.reduced).height upper)) =
        .ok ⟨(Frame.ofMountain p.reduced).height upper, 0, some (Frame.ref parent)⟩ ∧
    Canonical.cellAt ambient (Frame.ref parent) = .ok ((Frame.ofMountain p.reduced).cell parent) ∧
    (Frame.ofMountain p.reduced).height upper =
      Row.B (Row.lift sourceRow a.target.row ((Frame.ofMountain p.reduced).height child))
        ((Frame.ofMountain p.reduced).height parent) ∧
    (Frame.ofMountain p.reduced).height parent < sourceRow := by
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  have hp : F.P child = some parent :=
    (Executable.findParent_ref_iff hNormal.toOrdered child parent).mp hParent
  have hRootColumn : a.root.1.val = p.root.column := congrArg Ref.column a.root_ref
  have hBarrier : ∀ rootUpper, F.upper a.root = some rootUpper →
      Row.bump (F.height a.root) a.degree ≤ F.height rootUpper := by
    simpa only [F, a.root_row] using a.root_upper_barrier
  have hInside : Frame.RootInterval F a.root (Row.bump (F.height a.root) a.degree) child := by
    simpa only [F, a.root_row] using hChild
  obtain ⟨hParentLow, _, hUpperFixed, hB⟩ := Frame.root_interval_fixed_exit hNormal a.root_real
    (a.raised_degree hRaised) hBarrier hp hInside hUpper
    (by rw [hRootColumn]; exact hFixed)
    (a.root_row.trans_le a.target_lower)
    (by simpa only [a.root_row] using a.target_below)
  have hChildReal : Frame.Real child := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hp).1.trans (Frame.P_value hNormal.toOrdered hp).2)
  obtain ⟨actualParent, hActualParent, _, _, hLeft⟩ := hNormal.upper_step child upper hChildReal hUpper
  have hParentEq : actualParent = parent := Option.some.inj (hActualParent.symm.trans hp)
  subst actualParent
  change (F.cell upper).left = some (Frame.ref parent) at hLeft
  have hSourceRead : lookup ambient (Frame.ref upper) = .ok (F.cell upper) :=
    lookup_ok_iff.mpr (cellAt_ok_iff.mp
      (p.cell_read_preserved s.base_ambient (cellAt_of_frame_node p.reduced upper)))
  have hParentRead := p.cell_read_preserved s.base_ambient (cellAt_of_frame_node p.reduced parent)
  have hUpperReal : Frame.Real upper := by
    have hi := (Frame.upper_spec hUpper).2
    unfold Frame.Real
    omega
  have hNonzero : (F.cell upper).row ≠ 0 := by
    intro hz
    have hOne := Frame.one_le_height hNormal.toOrdered hUpperReal
    change (1 : Row) ≤ (F.cell upper).row at hOne
    rw [hz] at hOne
    exact (not_le_of_gt Row.zero_lt_one) hOne
  have hLeftward : (Frame.ref parent).column < (Frame.ref upper).column := by
    change parent.1.val < upper.1.val
    rw [(Frame.upper_spec hUpper).1]
    exact Frame.P_column_lt hNormal.toOrdered hp
  have hDestination : (Frame.ref parent).column <
      (Frame.ref upper).column + block * (p.reduced.size - 1 - p.root.column) :=
    hLeftward.trans_le (Nat.le_add_right _ _)
  have hFixQuery : Row.lift sourceRow a.target.row (F.height upper) = F.height upper := by
    simpa only [a.root_row] using hUpperFixed
  refine ⟨?_, hParentRead, by simpa only [a.root_row] using hB,
    by simpa only [a.root_row] using hParentLow⟩
  rw [hFixQuery]
  simp [copyEdge, hSourceRead, hNonzero, leftOf, hLeft,
    show (Frame.ref parent).column < p.root.column from hFixed,
    Nat.not_le_of_gt hDestination]
  rfl

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.copyEdge_fixed_interval_parent
