/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Geometry/RootTransport.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Geometry/RootTransport.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.RootInterval
import Googology.Notation.OmegaY.WellOrder.OmegaY.Rows.EdgeTransport

set_option backward.do.legacy false

/-!
# The exact source-edge row rule with the actual column split

The choice to fix or lift the parent uses its column, as the copy algorithm
does. The source interval theorem supplies the missing row/cone facts. This
does not by itself prove that a new column's strict-below search selects the
required stored node; that separate support/barrier obligation remains.
-/

namespace OmegaY.Geometry.Frame

def intervalParentRow (F : Frame) (root : F.Node) (target : Row) (parent : F.Node) : Row :=
  if parent.1.val < root.1.val then F.height parent
  else Row.lift (F.height root) target (F.height parent)

theorem root_interval_edge_transport {F : Frame} (hF : F.Normal)
    {root : F.Node} {degree : Nat} (hRootReal : Real root) (hDegree : 0 < degree)
    (hRootBarrier : ∀ upper, F.upper root = some upper →
      Row.bump (F.height root) degree ≤ F.height upper)
    {u p upper : F.Node} (hp : F.P u = some p)
    (hu : RootInterval F root (Row.bump (F.height root) degree) u)
    (hUpper : F.upper u = some upper)
    {target : Row} (hTargetLow : F.height root ≤ target)
    (hTargetHigh : target < Row.bump (F.height root) degree) :
    Row.lift (F.height root) target (F.height upper) =
      Row.B (Row.lift (F.height root) target (F.height u))
        (intervalParentRow F root target p) := by
  have hRow : F.height upper = Row.B (F.height u) (F.height p) :=
    (aboveHeight_of_upper hUpper).symm.trans (hF.above_row hp)
  rcases root_interval_parent_bump hF hRootReal hDegree hRootBarrier hp hu with hInside | ⟨hBefore, hBarrier⟩
  · have hColumn := RootCone.column_le hF.toOrdered hInside.1
    rw [intervalParentRow, if_neg (Nat.not_lt_of_ge hColumn), hRow]
    exact Row.lift_B hu.2.1 hInside.2.1
  · rw [hF.above_row hp] at hBarrier
    rw [intervalParentRow, if_pos hBefore.1, hRow]
    exact Row.lift_B_fixed_parent hTargetLow hTargetHigh hu.2.1 hu.2.2 hBefore.2.le hBarrier

/-- An actual parent left of the root forces the source upper endpoint out
of the interval. It stays fixed under the lift, and the exact B rule holds. -/
theorem root_interval_fixed_exit {F : Frame} (hF : F.Normal)
    {root : F.Node} {degree : Nat} (hRootReal : Real root) (hDegree : 0 < degree)
    (hRootBarrier : ∀ upper, F.upper root = some upper →
      Row.bump (F.height root) degree ≤ F.height upper)
    {u p upper : F.Node} (hp : F.P u = some p)
    (hu : RootInterval F root (Row.bump (F.height root) degree) u)
    (hUpper : F.upper u = some upper) (hFixed : p.1.val < root.1.val)
    {target : Row} (hTargetLow : F.height root ≤ target)
    (hTargetHigh : target < Row.bump (F.height root) degree) :
    F.height p < F.height root ∧
      Row.bump (F.height root) degree ≤ F.height upper ∧
      Row.lift (F.height root) target (F.height upper) = F.height upper ∧
      F.height upper = Row.B (Row.lift (F.height root) target (F.height u)) (F.height p) := by
  have hOut : ¬ RootInterval F root (Row.bump (F.height root) degree) p := by
    intro h
    exact not_lt_of_ge (RootCone.column_le hF.toOrdered h.1) hFixed
  rcases root_interval_parent_bump hF hRootReal hDegree hRootBarrier hp hu with h | ⟨hBefore, hBarrier⟩
  · exact False.elim (hOut h)
  · rw [aboveHeight_of_upper hUpper] at hBarrier
    have hFixedUpper := Row.lift_eq_of_ge_cap hTargetLow hTargetHigh hBarrier
    refine ⟨hBefore.2, hBarrier, hFixedUpper, ?_⟩
    have hTransport := root_interval_edge_transport hF hRootReal hDegree hRootBarrier
      hp hu hUpper hTargetLow hTargetHigh
    simpa only [hFixedUpper, intervalParentRow, if_pos hFixed] using hTransport

#print axioms root_interval_edge_transport
#print axioms root_interval_fixed_exit

end OmegaY.Geometry.Frame
