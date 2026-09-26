/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Geometry/IntervalLegTransport.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Geometry/IntervalLegTransport.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.RootInterval
import Googology.Notation.OmegaY.WellOrder.OmegaY.Rows.EdgeTransport

set_option backward.do.legacy false

/-!
# Exact B transport of source legs in one root interval

A marker has two different endpoints: its incoming physical row remains
at the old root row, while its effective outgoing row is the filled target.
The definitions below retain that distinction. They describe a single
interval's row transport, not an already reconstructed copied mountain.
-/

namespace OmegaY.Geometry.Frame

/-- Pull the same-row root path in the father's column back to an actual
root-row path in the child's column, using numerical-parent row shadows. -/
theorem root_cone_child_of_parent {F : Frame} (hF : F.Normal)
    {root child parent : F.Node} (hParent : F.P child = some parent)
    (hCone : RootCone F root parent) (hLower : F.height root ≤ F.height parent) :
    RootCone F root child ∧ F.height root ≤ F.height child := by
  obtain ⟨low, hReal, hColumn, hRow, hPath⟩ := hCone
  obtain ⟨shadow, hShadowReal, hShadowColumn, hShadowBelow, hShadowRow, hShadowPath⟩ :=
    P_rowShadow hF hParent low hReal hColumn (by rw [hRow]; exact hLower)
  have hSame : F.height shadow = F.height root := hShadowRow.trans hRow
  exact ⟨⟨shadow, hShadowReal, hShadowColumn, hSame, hShadowPath.trans hPath⟩,
    hSame ▸ hShadowBelow⟩

/-- An active father can only have an active child or a child at or above
the cap; the alternative is derived from the actual source P edge. -/
theorem root_interval_child_or_above_cap {F : Frame} (hF : F.Normal)
    {root child parent : F.Node} {cap : Row} (hParent : F.P child = some parent)
    (hInside : RootInterval F root cap parent) :
    RootInterval F root cap child ∨ cap ≤ F.height child := by
  obtain ⟨hCone, hLower⟩ := root_cone_child_of_parent hF hParent hInside.1 hInside.2.1
  rcases lt_or_ge (F.height child) cap with hBelow | hAbove
  · exact Or.inl ⟨hCone, hLower, hBelow⟩
  · exact Or.inr hAbove

/-- Outgoing child and parent endpoints include the marker's filled target. -/
noncomputable def effectiveRow (F : Frame) (root : F.Node) (cap target : Row)
    (node : F.Node) : Row := by
  classical
  exact if RootInterval F root cap node then Row.lift (F.height root) target (F.height node)
    else F.height node

/-- Incoming endpoints exclude the marker itself at the root row. -/
def IncomingInterval (F : Frame) (root : F.Node) (cap : Row) (node : F.Node) : Prop :=
  RootCone F root node ∧ F.height root < F.height node ∧ F.height node < cap

noncomputable def incomingRow (F : Frame) (root : F.Node) (cap target : Row)
    (node : F.Node) : Row := by
  classical
  exact if IncomingInterval F root cap node then Row.lift (F.height root) target (F.height node)
    else F.height node

theorem effectiveRow_of_inside {F : Frame} {root node : F.Node} {cap target : Row}
    (hInside : RootInterval F root cap node) :
    F.effectiveRow root cap target node = Row.lift (F.height root) target (F.height node) := by
  simp only [effectiveRow, if_pos hInside]

theorem effectiveRow_of_outside {F : Frame} {root node : F.Node} {cap target : Row}
    (hOutside : ¬ RootInterval F root cap node) :
    F.effectiveRow root cap target node = F.height node := by
  simp only [effectiveRow, if_neg hOutside]

/-- At a physical marker the incoming endpoint stays at the source root
row, whereas the outgoing endpoint is precisely the fill target. -/
theorem marker_endpoint_rows {F : Frame} {root node : F.Node} {cap target : Row}
    (hInside : RootInterval F root cap node) (hRow : F.height node = F.height root) :
    F.incomingRow root cap target node = F.height root ∧
      F.effectiveRow root cap target node = target := by
  have hNot : ¬ IncomingInterval F root cap node := by
    intro h
    have hStrict := h.2.1
    rw [hRow] at hStrict
    exact (lt_irrefl _) hStrict
  constructor
  · rw [incomingRow, if_neg hNot, hRow]
  · rw [effectiveRow_of_inside hInside, hRow, Row.lift_at_root]

/-- Crossing into a column's real root row from below can only arrive at
that row itself, since no physical node lies between adjacent source nodes. -/
theorem upper_at_root_of_crossing {F : Frame} (hF : F.Ordered)
    {root child upper : F.Node} (hUpper : F.upper child = some upper)
    (hCone : RootCone F root upper) (hBelow : F.height child < F.height root)
    (hAbove : F.height root ≤ F.height upper) : F.height upper = F.height root := by
  apply le_antisymm _ hAbove
  apply le_of_not_gt
  intro hStrict
  obtain ⟨low, _, hColumn, hRow, _⟩ := hCone
  have hLow : F.height low ≤ F.height child :=
    height_le_lower_of_lt_upper hF hUpper hColumn (by rw [hRow]; exact hStrict)
  rw [hRow] at hLow
  exact (not_lt_of_ge hLow) hBelow

/-- Actual adjacency prevents an upper endpoint entering strictly inside
the root interval from a child outside it. In particular, an edge arriving
at the physical marker has its upper at exactly the root row and is fixed. -/
theorem upper_not_incoming_of_child_outside {F : Frame} (hF : F.Ordered)
    {root child upper : F.Node} {cap : Row} (hUpper : F.upper child = some upper)
    (hChild : ¬ RootInterval F root cap child) : ¬ IncomingInterval F root cap upper := by
  rintro ⟨hCone, hAboveRoot, hBelowCap⟩
  have hChildCone : RootCone F root child := hCone.same_column (upper_spec hUpper).1
  have hChildBelowUpper : F.height child < F.height upper := by
    obtain ⟨hColumn, hIndex⟩ := upper_spec hUpper
    rcases upper with ⟨column, index⟩
    dsimp only at hColumn
    subst column
    change index.val = child.2.val + 1 at hIndex
    exact hF.rows_strict child.1 (by change child.2.val < index.val; omega)
  obtain ⟨low, _, hLowColumn, hLowRow, _⟩ := hCone
  have hRootBelowChild : F.height root ≤ F.height child := by
    rw [← hLowRow]
    exact height_le_lower_of_lt_upper hF hUpper hLowColumn (by rw [hLowRow]; exact hAboveRoot)
  exact hChild ⟨hChildCone, hRootBelowChild, hChildBelowUpper.trans hBelowCap⟩

theorem incomingRow_upper_of_child_outside {F : Frame} (hF : F.Ordered)
    {root child upper : F.Node} {cap target : Row} (hUpper : F.upper child = some upper)
    (hChild : ¬ RootInterval F root cap child) :
    F.incomingRow root cap target upper = F.height upper := by
  simp only [incomingRow, if_neg (upper_not_incoming_of_child_outside hF hUpper hChild)]

/-- Above an active child, the incoming row agrees with the full lift;
at and beyond the cap that lift is already the identity. -/
theorem incomingRow_upper_of_child_inside {F : Frame} (hF : F.Normal)
    {root child parent upper : F.Node} {target : Row} {degree : Nat}
    (hTarget : F.height root ≤ target) (hTargetCap : target < Row.bump (F.height root) degree)
    (hParent : F.P child = some parent) (hUpper : F.upper child = some upper)
    (hChild : RootInterval F root (Row.bump (F.height root) degree) child) :
    F.incomingRow root (Row.bump (F.height root) degree) target upper =
      Row.lift (F.height root) target (F.height upper) := by
  have hUpperFormula : F.height upper = Row.B (F.height child) (F.height parent) :=
    (aboveHeight_of_upper hUpper).symm.trans (hF.above_row hParent)
  have hAboveRoot : F.height root < F.height upper := by
    rw [hUpperFormula]
    exact hChild.2.1.trans_lt (Row.lt_B _ _)
  by_cases hBelow : F.height upper < Row.bump (F.height root) degree
  · have hIncoming : IncomingInterval F root (Row.bump (F.height root) degree) upper :=
      ⟨hChild.1.same_column (upper_spec hUpper).1.symm, hAboveRoot, hBelow⟩
    simp only [incomingRow, if_pos hIncoming]
  · have hNotIncoming : ¬ IncomingInterval F root (Row.bump (F.height root) degree) upper :=
      fun h => hBelow h.2.2
    rw [incomingRow, if_neg hNotIncoming,
      Row.lift_eq_of_ge_cap hTarget hTargetCap (le_of_not_gt hBelow)]

/-- Every actual source P edge transports by the exact B formula under one
root-interval lift. The physical incoming marker row and effective filled
marker endpoint are deliberately different functions in this statement. -/
theorem interval_leg_B_transport {F : Frame} (hF : F.Normal)
    {root child parent upper : F.Node} {target : Row} {degree : Nat}
    (hRoot : Real root) (hDegree : 0 < degree)
    (hRootBarrier : ∀ rootUpper, F.upper root = some rootUpper →
      Row.bump (F.height root) degree ≤ F.height rootUpper)
    (hTarget : F.height root ≤ target) (hTargetCap : target < Row.bump (F.height root) degree)
    (hParent : F.P child = some parent) (hUpper : F.upper child = some upper) :
    F.incomingRow root (Row.bump (F.height root) degree) target upper =
      Row.B (F.effectiveRow root (Row.bump (F.height root) degree) target child)
        (F.effectiveRow root (Row.bump (F.height root) degree) target parent) := by
  have hSource : F.height upper = Row.B (F.height child) (F.height parent) :=
    (aboveHeight_of_upper hUpper).symm.trans (hF.above_row hParent)
  by_cases hChild : RootInterval F root (Row.bump (F.height root) degree) child
  · rw [incomingRow_upper_of_child_inside hF hTarget hTargetCap hParent hUpper hChild,
      effectiveRow_of_inside hChild, hSource]
    by_cases hFather : RootInterval F root (Row.bump (F.height root) degree) parent
    · rw [effectiveRow_of_inside hFather]
      exact Row.lift_B hChild.2.1 hFather.2.1
    · rw [effectiveRow_of_outside hFather]
      have hExit : BeforeRoot F root parent ∧
          Row.bump (F.height root) degree ≤ F.aboveHeight child :=
        (root_interval_parent_bump hF hRoot hDegree hRootBarrier hParent hChild).resolve_left hFather
      have hCap : Row.bump (F.height root) degree ≤ Row.B (F.height child) (F.height parent) := by
        simpa only [hF.above_row hParent] using hExit.2
      exact Row.lift_B_fixed_parent hTarget hTargetCap hChild.2.1 hChild.2.2 hExit.1.2.le hCap
  · rw [incomingRow_upper_of_child_outside hF.toOrdered hUpper hChild,
      effectiveRow_of_outside hChild, hSource]
    by_cases hFather : RootInterval F root (Row.bump (F.height root) degree) parent
    · rw [effectiveRow_of_inside hFather]
      have hAbove := (root_interval_child_or_above_cap hF hParent hFather).resolve_left hChild
      exact (Row.B_fixed_child_lift_parent hTarget hTargetCap hFather.2.1 hFather.2.2 hAbove).symm
    · rw [effectiveRow_of_outside hFather]

end OmegaY.Geometry.Frame

#print axioms OmegaY.Geometry.Frame.root_cone_child_of_parent
#print axioms OmegaY.Geometry.Frame.root_interval_child_or_above_cap
#print axioms OmegaY.Geometry.Frame.marker_endpoint_rows
#print axioms OmegaY.Geometry.Frame.upper_at_root_of_crossing
#print axioms OmegaY.Geometry.Frame.upper_not_incoming_of_child_outside
#print axioms OmegaY.Geometry.Frame.incomingRow_upper_of_child_inside
#print axioms OmegaY.Geometry.Frame.interval_leg_B_transport
