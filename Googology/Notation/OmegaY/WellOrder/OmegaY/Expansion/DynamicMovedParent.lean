/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/DynamicMovedParent.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/DynamicMovedParent.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.DynamicParentInterval
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.PreparedParentCap
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.MarkerParentInterval

set_option backward.do.legacy false

/-!
# Actual moved-parent selection throughout a dynamic block

Execution history supplies the earlier parent-column copy and its input
data. The parent may be a marker, an interior contour node, a node whose
upper neighbour crosses the cap, or the source top. No classification of
the parent's upper neighbour is required by the combined theorem.

The reference target remains explicitly below the chosen root interval
cap. Parents in the root column itself are outside this moved-column case.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- A source parent strictly above the root row is selected in the actual
current ambient mountain. All earlier-copy inputs and the parent-upper
case split are discharged from the real history and source construction. -/
theorem DynamicBlockState.below_parent_above_root
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start : Mountain} {references : List Ref}
    {next : Nat} {ambient : Mountain}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient)
    (hLast : 1 < last)
    {root child parent childUpper : (Frame.ofMountain p.reduced).Node}
    {degree : Nat} (hRootReal : Frame.Real root) (hDegree : 0 < degree)
    (hRootColumn : root.1.val = p.root.column) (hRootIndex : root.2.val ≤ p.root.index)
    (hRootBarrier : ∀ upper, (Frame.ofMountain p.reduced).upper root = some upper →
      Row.bump ((Frame.ofMountain p.reduced).height root) degree ≤
        (Frame.ofMountain p.reduced).height upper)
    (hParent : findParent p.reduced (Frame.ref child) = .ok (Frame.ref parent))
    (hChild : Frame.RootInterval (Frame.ofMountain p.reduced) root
      (Row.bump ((Frame.ofMountain p.reduced).height root) degree) child)
    (hChildColumn : child.1.val = next)
    (hChildUpper : (Frame.ofMountain p.reduced).upper child = some childUpper)
    (hParentAbove : (Frame.ofMountain p.reduced).height root <
      (Frame.ofMountain p.reduced).height parent)
    {target : Row}
    (hTarget : referenceAt start references ((Frame.ofMountain p.reduced).height root) = .ok target)
    (hTargetCap : target < Row.bump ((Frame.ofMountain p.reduced).height root) degree) :
    ∃ (index : Nat) (actualParent : Cell),
      below ambient (parent.1.val + block * (p.reduced.size - 1 - p.root.column))
        (Row.lift ((Frame.ofMountain p.reduced).height root) target
          ((Frame.ofMountain p.reduced).height childUpper)) =
        .ok ⟨parent.1.val + block * (p.reduced.size - 1 - p.root.column), index⟩ ∧
      Canonical.cellAt ambient
        ⟨parent.1.val + block * (p.reduced.size - 1 - p.root.column), index⟩ = .ok actualParent ∧
      actualParent.row = Row.lift ((Frame.ofMountain p.reduced).height root) target
        ((Frame.ofMountain p.reduced).height parent) := by
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_legal (build_success_legal p.reduced_build) p.reduced_build
  have hp : F.P child = some parent :=
    (Executable.findParent_ref_iff hNormal.toOrdered child parent).mp hParent
  have hParentInside : Frame.RootInterval F root (Row.bump (F.height root) degree) parent :=
    (Frame.root_interval_parent_iff_height hNormal hRootReal
      (Row.bump_strictMono_exponent _ hDegree) hRootBarrier hp hChild).mpr hParentAbove.le
  have hRight : p.root.column < parent.1.val := by
    rw [← hRootColumn]
    exact hParentInside.column_lt_of_height_lt hNormal.toOrdered hRootBarrier hParentAbove
  have hBeforeNext : parent.1.val < next := by
    simpa only [hChildColumn] using Frame.P_column_lt hNormal.toOrdered hp
  obtain ⟨before, column, d, hRun, hPreserve, hSource, _, hParentPower,
    hParentLow, hQueries, _⟩ := s.prior_column_data history hLast hRight hBeforeNext
  have hCurrentTarget : referenceAt ambient references (F.height root) = .ok target :=
    (s.referenceAt_preserved (F.height root)).trans hTarget
  have hBeforeTarget : referenceAt before references (F.height root) = .ok target :=
    (hQueries (F.height root)).trans hCurrentTarget
  obtain ⟨index, actualParent, hBelow, hCell, hRow⟩ :=
    d.prepared_below_parent_above_root hSource hRootReal hDegree hRootColumn hRootIndex hRootBarrier
      hParent hChild hChildUpper rfl hRight hBeforeTarget hParentPower hParentLow
      hParentAbove hRun hTargetCap
  have hCurrentBelow : below ambient before.size
      (Row.lift (F.height root) target (F.height childUpper)) = .ok ⟨before.size, index⟩ :=
    (hPreserve.below (by simp) _).trans hBelow
  obtain ⟨actualNodes, hNodes, hRead⟩ := cellAt_ok_iff.mp hCell
  have hCurrentCell : Canonical.cellAt ambient ⟨before.size, index⟩ = .ok actualParent :=
    cellAt_ok_iff.mpr ⟨actualNodes, hPreserve.column_read hNodes, hRead⟩
  rw [← d.destination] at hCurrentBelow hCurrentCell
  exact ⟨index, actualParent, hCurrentBelow, hCurrentCell, hRow⟩

/-- All source parents strictly to the right of the bad-root column are
selected by their lifted row. The source root-interval theorem supplies
the parent-row lower bound, so neither a parent-height classification nor
any earlier-column copy certificate is an input. -/
theorem DynamicBlockState.below_moved_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start : Mountain} {references : List Ref}
    {next : Nat} {ambient : Mountain}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient)
    (hLast : 1 < last)
    {root child parent childUpper : (Frame.ofMountain p.reduced).Node}
    {degree : Nat} (hRootReal : Frame.Real root) (hDegree : 0 < degree)
    (hRootColumn : root.1.val = p.root.column) (hRootIndex : root.2.val ≤ p.root.index)
    (hRootBarrier : ∀ upper, (Frame.ofMountain p.reduced).upper root = some upper →
      Row.bump ((Frame.ofMountain p.reduced).height root) degree ≤
        (Frame.ofMountain p.reduced).height upper)
    (hParent : findParent p.reduced (Frame.ref child) = .ok (Frame.ref parent))
    (hChild : Frame.RootInterval (Frame.ofMountain p.reduced) root
      (Row.bump ((Frame.ofMountain p.reduced).height root) degree) child)
    (hChildColumn : child.1.val = next)
    (hChildUpper : (Frame.ofMountain p.reduced).upper child = some childUpper)
    (hRight : p.root.column < parent.1.val)
    {target : Row}
    (hTarget : referenceAt start references ((Frame.ofMountain p.reduced).height root) = .ok target)
    (hTargetCap : target < Row.bump ((Frame.ofMountain p.reduced).height root) degree) :
    ∃ (index : Nat) (actualParent : Cell),
      below ambient (parent.1.val + block * (p.reduced.size - 1 - p.root.column))
        (Row.lift ((Frame.ofMountain p.reduced).height root) target
          ((Frame.ofMountain p.reduced).height childUpper)) =
        .ok ⟨parent.1.val + block * (p.reduced.size - 1 - p.root.column), index⟩ ∧
      Canonical.cellAt ambient
        ⟨parent.1.val + block * (p.reduced.size - 1 - p.root.column), index⟩ = .ok actualParent ∧
      actualParent.row = Row.lift ((Frame.ofMountain p.reduced).height root) target
        ((Frame.ofMountain p.reduced).height parent) := by
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_legal (build_success_legal p.reduced_build) p.reduced_build
  have hp : F.P child = some parent :=
    (Executable.findParent_ref_iff hNormal.toOrdered child parent).mp hParent
  have hParentInside : Frame.RootInterval F root (Row.bump (F.height root) degree) parent :=
    (Frame.root_interval_parent_iff_column hNormal hRootReal
      (Row.bump_strictMono_exponent _ hDegree) hRootBarrier hp hChild).mpr
      (by rw [hRootColumn]; exact hRight.le)
  rcases hParentInside.2.1.eq_or_lt with hEqual | hAbove
  · exact s.below_marker_parent hRootReal hDegree hRootColumn hRootIndex hRootBarrier
      hParent hChild hChildUpper hChildColumn hRight hEqual.symm hTarget
  · exact s.below_parent_above_root history hLast hRootReal hDegree hRootColumn hRootIndex
      hRootBarrier hParent hChild hChildColumn hChildUpper hAbove hTarget hTargetCap

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.below_parent_above_root
#print axioms OmegaY.Expansion.DynamicBlockState.below_moved_parent
