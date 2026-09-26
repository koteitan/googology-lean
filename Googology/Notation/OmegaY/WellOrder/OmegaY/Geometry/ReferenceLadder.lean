/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Geometry/ReferenceLadder.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Geometry/ReferenceLadder.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.Executable
import Googology.Notation.OmegaY.WellOrder.OmegaY.Rows.FillLadder

set_option backward.do.legacy false

/-!
# Immediate candidate hits inside a reference ladder

Only the concrete frame's ordered rows and stored left leg are required.
Neither numerical canonicality nor a well-founded expansion relation is a
premise. The interior and last rung have different candidates. These lemmas
do not include the original physical marker below the inserted ladder.

Application to the executable fill/finish output still has to identify the
actual adjacent copied cells and their stored legs after sorting.
-/

namespace OmegaY.Row

/-- The next interior rung has exactly the canonical B height, not merely
some power-step height. -/
theorem B_reference_rung (lower : Row) (degree : Nat) :
    B (bump lower degree) lower = bump lower (degree + 1) := by
  rw [B, jump_comm, jump_bump]
  exact fillLadder_adjacent lower degree

end OmegaY.Row

namespace OmegaY.Geometry.Frame

/-- A rung strictly below the actual next parent row cannot climb its
stored left leg. This uses the parent's actual successor, not just a cap. -/
theorem reference_interior_Q {F : Frame} (hF : F.Ordered)
    {u parent parentUpper : F.Node} {degree scale : Nat}
    (hLeft : (F.cell u).left = some (ref parent))
    (hParentUpper : F.upper parent = some parentUpper)
    (hParentRow : F.height parentUpper = Row.bump (F.height parent) scale)
    (hRow : F.height u = Row.bump (F.height parent) degree)
    (hDegree : degree < scale) : F.Q u = some parent := by
  apply Q_eq_left_of_barrier hF hLeft
  · rw [hRow]
    exact (Row.lt_bump _ _).le
  · intro next hNext
    have he : next = parentUpper := Option.some.inj (hNext.symm.trans hParentUpper)
    rw [he, hRow, hParentRow]
    exact Row.bump_strictMono_exponent _ hDegree

/-- At the last rung the climb reaches the next parent node, rather than
staying at the old stored left endpoint. -/
theorem reference_endpoint_Q {F : Frame} (hF : F.Ordered)
    {u parent parentUpper : F.Node} {scale : Nat}
    (hLeft : (F.cell u).left = some (ref parent))
    (hParentUpper : F.upper parent = some parentUpper)
    (hParentRow : F.height parentUpper = Row.bump (F.height parent) scale)
    (hRow : F.height u = Row.bump (F.height parent) scale) :
    F.Q u = some parentUpper :=
  Q_eq_upper_at_equal hF hLeft hParentUpper (hParentRow.trans hRow.symm)

/-- Positive backfill makes an already identified first Q candidate the
actual numerical parent. No later Q candidate or P path is assumed. -/
theorem P_of_Q_positive_sum {F : Frame} (hF : F.Ordered)
    {u parent : F.Node} {surplus : Nat} (hQ : F.Q u = some parent)
    (hParentPositive : 0 < F.value parent) (hSurplus : 0 < surplus)
    (hValue : F.value u = surplus + F.value parent) : F.P u = some parent := by
  apply (P_iff hF).mpr
  exact ⟨parent, hQ, .here hParentPositive (by omega)⟩

theorem reference_interior_P {F : Frame} (hF : F.Ordered)
    {u parent parentUpper : F.Node} {degree scale surplus : Nat}
    (hLeft : (F.cell u).left = some (ref parent))
    (hParentUpper : F.upper parent = some parentUpper)
    (hParentRow : F.height parentUpper = Row.bump (F.height parent) scale)
    (hRow : F.height u = Row.bump (F.height parent) degree)
    (hDegree : degree < scale) (hParentPositive : 0 < F.value parent)
    (hSurplus : 0 < surplus) (hValue : F.value u = surplus + F.value parent) :
    F.P u = some parent :=
  P_of_Q_positive_sum hF
    (reference_interior_Q hF hLeft hParentUpper hParentRow hRow hDegree)
    hParentPositive hSurplus hValue

theorem reference_endpoint_P {F : Frame} (hF : F.Ordered)
    {u parent parentUpper : F.Node} {scale surplus : Nat}
    (hLeft : (F.cell u).left = some (ref parent))
    (hParentUpper : F.upper parent = some parentUpper)
    (hParentRow : F.height parentUpper = Row.bump (F.height parent) scale)
    (hRow : F.height u = Row.bump (F.height parent) scale)
    (hParentPositive : 0 < F.value parentUpper) (hSurplus : 0 < surplus)
    (hValue : F.value u = surplus + F.value parentUpper) :
    F.P u = some parentUpper :=
  P_of_Q_positive_sum hF
    (reference_endpoint_Q hF hLeft hParentUpper hParentRow hRow)
    hParentPositive hSurplus hValue

end OmegaY.Geometry.Frame

namespace OmegaY.Geometry.Executable

/-- The immediate-hit result applies to the real, value-thresholded
constructor search, including its actual column-derived fuel. -/
theorem reference_interior_findParent {mountain : Canonical.Mountain}
    (hF : (Frame.ofMountain mountain).Ordered)
    {u parent parentUpper : (Frame.ofMountain mountain).Node} {degree scale surplus : Nat}
    (hLeft : ((Frame.ofMountain mountain).cell u).left = some (Frame.ref parent))
    (hParentUpper : (Frame.ofMountain mountain).upper parent = some parentUpper)
    (hParentRow : (Frame.ofMountain mountain).height parentUpper =
      Row.bump ((Frame.ofMountain mountain).height parent) scale)
    (hRow : (Frame.ofMountain mountain).height u =
      Row.bump ((Frame.ofMountain mountain).height parent) degree)
    (hDegree : degree < scale) (hParentPositive : 0 < (Frame.ofMountain mountain).value parent)
    (hSurplus : 0 < surplus)
    (hValue : (Frame.ofMountain mountain).value u = surplus + (Frame.ofMountain mountain).value parent) :
    Canonical.findParent mountain (Frame.ref u) = .ok (Frame.ref parent) :=
  (findParent_ref_iff hF u parent).mpr
    (Frame.reference_interior_P hF hLeft hParentUpper hParentRow hRow hDegree
      hParentPositive hSurplus hValue)

theorem reference_endpoint_findParent {mountain : Canonical.Mountain}
    (hF : (Frame.ofMountain mountain).Ordered)
    {u parent parentUpper : (Frame.ofMountain mountain).Node} {scale surplus : Nat}
    (hLeft : ((Frame.ofMountain mountain).cell u).left = some (Frame.ref parent))
    (hParentUpper : (Frame.ofMountain mountain).upper parent = some parentUpper)
    (hParentRow : (Frame.ofMountain mountain).height parentUpper =
      Row.bump ((Frame.ofMountain mountain).height parent) scale)
    (hRow : (Frame.ofMountain mountain).height u =
      Row.bump ((Frame.ofMountain mountain).height parent) scale)
    (hParentPositive : 0 < (Frame.ofMountain mountain).value parentUpper)
    (hSurplus : 0 < surplus)
    (hValue : (Frame.ofMountain mountain).value u =
      surplus + (Frame.ofMountain mountain).value parentUpper) :
    Canonical.findParent mountain (Frame.ref u) = .ok (Frame.ref parentUpper) :=
  (findParent_ref_iff hF u parentUpper).mpr
    (Frame.reference_endpoint_P hF hLeft hParentUpper hParentRow hRow
      hParentPositive hSurplus hValue)

end OmegaY.Geometry.Executable

#print axioms OmegaY.Row.B_reference_rung
#print axioms OmegaY.Geometry.Frame.reference_interior_Q
#print axioms OmegaY.Geometry.Frame.reference_endpoint_Q
#print axioms OmegaY.Geometry.Executable.reference_interior_findParent
#print axioms OmegaY.Geometry.Executable.reference_endpoint_findParent
