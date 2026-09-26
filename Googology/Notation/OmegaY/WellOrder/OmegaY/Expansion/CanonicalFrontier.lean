/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/CanonicalFrontier.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/CanonicalFrontier.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.FrontierCuts
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Domain

set_option backward.do.legacy false

/-!
# Actual event-frontier closure in a canonical source frame

Source Normal supplies the true numerical parent and the father-upper
bound. These imply parent-frontier closure; it is not an extra premise.
The raw stored parent and its B rule are also recovered from Normal.

These are source-frame theorems. They do not assert that an expansion output
is Normal, or supply the still separate numerical recovery for such an
output.
-/

namespace OmegaY.Geometry.Frame

/-- On real source nodes, the upper cell stores exactly the numerical P
parent. Phantom nodes are intentionally excluded. -/
theorem Normal.rawParent_eq_P {F : Frame} (hF : F.Normal) {node : F.Node}
    (hReal : Real node) : F.rawParent node = F.P node := by
  cases hUpper : F.upper node with
  | none =>
    have hRaw := rawParent_none_of_upper_none hUpper
    rw [hRaw]
    cases hParent : F.P node with
    | none => rfl
    | some parent =>
      obtain ⟨upper, hSome⟩ := hF.upper_of_parent hParent
      rw [hUpper] at hSome
      cases hSome
  | some upper =>
    obtain ⟨parent, hParent, _, _, hLeft⟩ := hF.upper_step node upper hReal hUpper
    exact (rawParent_eq_of_upper_left hUpper hLeft).trans hParent.symm

theorem Normal.raw_B {F : Frame} (hF : F.Normal) {node upper parent : F.Node}
    (hReal : Real node) (hUpper : F.upper node = some upper)
    (hParent : F.rawParent node = some parent) :
    F.height parent ≤ F.height node ∧
      F.height upper = Row.B (F.height node) (F.height parent) := by
  have hP : F.P node = some parent := (hF.rawParent_eq_P hReal).symm.trans hParent
  exact ⟨P_height_le hF.toOrdered hP,
    (aboveHeight_of_upper hUpper).symm.trans (hF.above_row hP)⟩

theorem Normal.value_one_of_upper_none {F : Frame} (hF : F.Normal) {node : F.Node}
    (hReal : Real node) (hUpper : F.upper node = none) : F.value node = 1 := by
  have hPositive := hF.real_positive node hReal
  have hNotLarge : ¬ 1 < F.value node := by
    intro hLarge
    obtain ⟨upper, hSome⟩ := hF.upper_exists node hReal hLarge
    rw [hUpper] at hSome
    cases hSome
  omega

/-- The parent's upper neighbour lies above the child's upper neighbour,
which lies above the cut. Together with P_height_le, this identifies the
parent as the actual maximum in its column below the same cut. -/
theorem Normal.frontierAt_parent {F : Frame} (hF : F.Normal) {cut : Row}
    (hCut : (1 : Row) ≤ cut) (column : Fin F.width) {parent : F.Node}
    (hParent : F.P (frontierAt hF.toOrdered cut hCut column) = some parent) :
    frontierAt hF.toOrdered cut hCut parent.1 = parent := by
  have hSpec := frontierAt_spec hF.toOrdered hCut column
  apply frontierAt_eq_of_upper_barrier hF.toOrdered hCut
  · exact (P_height_le hF.toOrdered hParent).trans hSpec.2.2.1
  · intro parentUpper hParentUpper
    obtain ⟨upper, hUpper⟩ := hF.upper_of_parent hParent
    exact (hSpec.2.2.2.2 upper hUpper).trans_le
      (father_upper_bound_nodes hF hParent hUpper hParentUpper)

theorem Normal.frontierAt_raw_parent {F : Frame} (hF : F.Normal) {cut : Row}
    (hCut : (1 : Row) ≤ cut) (column : Fin F.width) {parent : F.Node}
    (hParent : F.rawParent (frontierAt hF.toOrdered cut hCut column) = some parent) :
    frontierAt hF.toOrdered cut hCut parent.1 = parent := by
  apply hF.frontierAt_parent hCut column
  exact (hF.rawParent_eq_P (frontierAt_spec hF.toOrdered hCut column).2.1).symm.trans hParent

theorem Normal.eventFrontier_parent {F : Frame} (hF : F.Normal) (event : Nat)
    (column : Fin F.width) {parent : F.Node}
    (hParent : F.P (eventFrontier hF.toOrdered event column) = some parent) :
    eventFrontier hF.toOrdered event parent.1 = parent :=
  hF.frontierAt_parent (F.eventCut_one_le event) column hParent

theorem Normal.eventFrontier_raw_parent {F : Frame} (hF : F.Normal) (event : Nat)
    (column : Fin F.width) {parent : F.Node}
    (hParent : F.rawParent (eventFrontier hF.toOrdered event column) = some parent) :
    eventFrontier hF.toOrdered event parent.1 = parent :=
  hF.frontierAt_raw_parent (F.eventCut_one_le event) column hParent

theorem Normal.eventFrontier_last_value {F : Frame} (hF : F.Normal) (column : Fin F.width) :
    F.value (eventFrontier hF.toOrdered F.lastEvent column) = 1 :=
  hF.value_one_of_upper_none (eventFrontier_spec hF.toOrdered F.lastEvent column).2.1
    (eventFrontier_last_upper_none hF.toOrdered column)

/-- The all-natural-column interface required by FrontierGeometry. On every
valid column this is exactly eventFrontier; only out-of-range queries are
clamped. A width witness is explicit, so no node is invented for an empty
frame. -/
noncomputable def eventFrontierNat {F : Frame} (hF : F.Ordered) (hWidth : 0 < F.width)
    (event column : Nat) : F.Node :=
  eventFrontier hF event ⟨min column (F.width - 1),
    (Nat.min_le_right _ _).trans_lt (by omega)⟩

theorem eventFrontierNat_eq {F : Frame} (hF : F.Ordered) (hWidth : 0 < F.width)
    (event : Nat) {column : Nat} (hColumn : column < F.width) :
    eventFrontierNat hF hWidth event column = eventFrontier hF event ⟨column, hColumn⟩ := by
  have hLe : column ≤ F.width - 1 := by omega
  simp only [eventFrontierNat, Nat.min_eq_left hLe]

/-- All seven geometry fields are derived for the actual event sequence of
a Normal source. In particular, neither parent closure nor the raw B rule
is supplied as a new hypothesis. -/
theorem Normal.eventFrontier_geometry {F : Frame} (hF : F.Normal) (hWidth : 0 < F.width)
    {bound : Nat} (hBound : bound < F.width) :
    FrontierGeometry F (eventFrontierNat hF.toOrdered hWidth) F.eventCut bound 0 F.lastEvent := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro event _ _ column hColumn
    rw [eventFrontierNat_eq hF.toOrdered hWidth event (hColumn.trans_lt hBound)]
    exact congrArg Fin.val (eventFrontier_spec hF.toOrdered event ⟨column, hColumn.trans_lt hBound⟩).1
  · intro event _ _ column hColumn
    rw [eventFrontierNat_eq hF.toOrdered hWidth event (hColumn.trans_lt hBound)]
    exact (eventFrontier_spec hF.toOrdered event ⟨column, hColumn.trans_lt hBound⟩).2.1
  · intro event _ _ column hColumn
    rw [eventFrontierNat_eq hF.toOrdered hWidth event (hColumn.trans_lt hBound)]
    exact (eventFrontier_spec hF.toOrdered event ⟨column, hColumn.trans_lt hBound⟩).2.2.1
  · intro event _ _ column hColumn upper hUpper
    rw [eventFrontierNat_eq hF.toOrdered hWidth event (hColumn.trans_lt hBound)] at hUpper
    exact (eventFrontier_spec hF.toOrdered event ⟨column, hColumn.trans_lt hBound⟩).2.2.2.2 upper hUpper
  · intro event _ hEvent column hColumn hChanged
    have hc := hColumn.trans_lt hBound
    simp only [frontierMoves, eventFrontierNat_eq hF.toOrdered hWidth _ hc] at hChanged ⊢
    exact eventFrontier_advance hF.toOrdered hEvent ⟨column, hc⟩ hChanged
  · intro event _ _ column hColumn parent hParent
    have hc := hColumn.trans_lt hBound
    rw [eventFrontierNat_eq hF.toOrdered hWidth event hc] at hParent
    rw [eventFrontierNat_eq hF.toOrdered hWidth event parent.1.isLt]
    exact hF.eventFrontier_raw_parent event ⟨column, hc⟩ hParent
  · intro event _ _ column hColumn upper parent hUpper hParent
    have hc := hColumn.trans_lt hBound
    rw [eventFrontierNat_eq hF.toOrdered hWidth event hc] at hUpper hParent ⊢
    exact hF.raw_B (eventFrontier_spec hF.toOrdered event ⟨column, hc⟩).2.1 hUpper hParent

end OmegaY.Geometry.Frame

namespace OmegaY.Canonical

open Geometry

/-- The source parent read is the executable findParent, not an abstract
relation selected independently of the successful source build. -/
theorem build_eventFrontier_parent {values : List Nat} {mountain : Mountain}
    (hBuild : build values = .ok mountain) (event : Nat)
    (column : Fin (Frame.ofMountain mountain).width)
    {parent : (Frame.ofMountain mountain).Node}
    (hParent : findParent mountain
      (Frame.ref (Frame.eventFrontier (build_normal_of_success hBuild).toOrdered event column)) =
      .ok (Frame.ref parent)) :
    Frame.eventFrontier (build_normal_of_success hBuild).toOrdered event parent.1 = parent := by
  have hNormal := build_normal_of_success hBuild
  exact hNormal.eventFrontier_parent event column
    ((Executable.findParent_ref_iff hNormal.toOrdered _ parent).mp hParent)

theorem build_eventFrontier_geometry {values : List Nat} {mountain : Mountain}
    (hBuild : build values = .ok mountain) (hWidth : 0 < mountain.size)
    {bound : Nat} (hBound : bound < mountain.size) :
    Frame.FrontierGeometry (Frame.ofMountain mountain)
      (Frame.eventFrontierNat (build_normal_of_success hBuild).toOrdered hWidth)
      (Frame.ofMountain mountain).eventCut bound 0 (Frame.ofMountain mountain).lastEvent :=
  (build_normal_of_success hBuild).eventFrontier_geometry hWidth hBound

end OmegaY.Canonical

namespace OmegaY.Expansion

open Canonical Geometry

/-- The synchronous additive frontier laws for an actual canonical build.
This wrapper uses the independently established source sums and validity.
It does not assume or conclude output canonicality or NumericSuffix. -/
theorem build_eventFrontier_synchronousBackfill {values : List Nat} {mountain : Mountain}
    (hBuild : Canonical.build values = .ok mountain) (hWidth : 0 < mountain.size)
    {bound : Nat} (hBound : bound < mountain.size) (initial : ZeroY.ParentMap) :
    Forests.SynchronousBackfill
      ((Frame.ofMountain mountain).frontierForests initial
        (Frame.eventFrontierNat (build_normal_of_success hBuild).toOrdered hWidth) bound)
      ((Frame.ofMountain mountain).frontierValue
        (Frame.eventFrontierNat (build_normal_of_success hBuild).toOrdered hWidth))
      (Frame.frontierMoves (Frame.eventFrontierNat (build_normal_of_success hBuild).toOrdered hWidth))
      bound 0 (Frame.ofMountain mountain).lastEvent :=
  synchronousBackfill_of_frontier_geometry (build_valid_of_success hBuild)
    (build_mountain_sums hBuild) (build_eventFrontier_geometry hBuild hWidth hBound) initial

end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.Normal.rawParent_eq_P
#print axioms OmegaY.Geometry.Frame.Normal.frontierAt_parent
#print axioms OmegaY.Geometry.Frame.Normal.eventFrontier_raw_parent
#print axioms OmegaY.Geometry.Frame.Normal.eventFrontier_last_value
#print axioms OmegaY.Geometry.Frame.Normal.eventFrontier_geometry
#print axioms OmegaY.Canonical.build_eventFrontier_parent
#print axioms OmegaY.Canonical.build_eventFrontier_geometry
#print axioms OmegaY.Expansion.build_eventFrontier_synchronousBackfill
