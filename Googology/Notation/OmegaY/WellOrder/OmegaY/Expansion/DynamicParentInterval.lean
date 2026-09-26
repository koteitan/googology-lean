/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/DynamicParentInterval.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/DynamicParentInterval.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.HistoryColumnData
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.PreparedParentInterval

set_option backward.do.legacy false

/-!
# Actual interior copied parents in the current block state

An earlier parent column is recovered from the actual copy history, with
its original input state and execution. The same fresh block reference map
identifies its lift target. Exact selection in that completed column is
then preserved into the current mountain.
-/

namespace OmegaY.Geometry.Frame

/-- A node strictly above the root but still below its next-row barrier
cannot occupy the root column itself. Sparse rows suffice. -/
theorem RootInterval.column_lt_of_height_lt {F : Frame} (hOrdered : F.Ordered)
    {root node : F.Node} {cap : Row}
    (hBarrier : ∀ upper, F.upper root = some upper → cap ≤ F.height upper)
    (hInside : RootInterval F root cap node) (hAbove : F.height root < F.height node) :
    root.1.val < node.1.val := by
  have hColumnLe := hInside.1.column_le hOrdered
  by_contra hn
  have hc : node.1 = root.1 := Fin.ext (by omega)
  cases root with
  | mk c i =>
    cases node with
    | mk d j =>
      dsimp only at hc
      subst d
      change (F.cells c i).row < (F.cells c j).row at hAbove
      have hij : i < j := (hOrdered.rows_strict c).lt_iff_lt.mp hAbove
      have hNext : i.val + 1 < F.length c := by have := j.isLt; change i.val < j.val at hij; omega
      let nextNode : F.Node := ⟨c, ⟨i.val + 1, hNext⟩⟩
      have hUpper : F.upper ⟨c, i⟩ = some nextNode := by
        simp only [Frame.upper, hNext, ↓reduceDIte, nextNode]
      have hCap : cap ≤ F.height nextNode := hBarrier nextNode hUpper
      have hRow : F.height nextNode ≤ F.height ⟨c, j⟩ := by
        apply (hOrdered.rows_strict c).monotone
        change i.val + 1 ≤ j.val
        exact Nat.succ_le_of_lt hij
      exact not_lt_of_ge (hCap.trans hRow) hInside.2.2

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry

/-- The ordinary internal-parent case is now stated at the actual current
copy state. All earlier-column copy data are derived from execution history;
only the original source geometry and the block-start reference query are
premises. The current child column has not yet been copied. -/
theorem DynamicBlockState.below_internal_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start : Mountain} {references : List Ref}
    {next : Nat} {ambient : Mountain}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient)
    (hLast : 1 < last)
    {root child parent childUpper parentUpper : (Frame.ofMountain p.reduced).Node}
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
    (hParentUpper : (Frame.ofMountain p.reduced).upper parent = some parentUpper)
    (hParentAbove : (Frame.ofMountain p.reduced).height root < (Frame.ofMountain p.reduced).height parent)
    (hParentCap : (Frame.ofMountain p.reduced).height parentUpper <
      Row.bump ((Frame.ofMountain p.reduced).height root) degree)
    {target : Row}
    (hTarget : referenceAt start references ((Frame.ofMountain p.reduced).height root) = .ok target) :
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
    d.prepared_below_internal_parent hSource hParentPower hParentLow
      hRootReal hDegree hRootColumn hRootIndex hRootBarrier hParent hChild
      hChildUpper hParentUpper rfl hRight hParentAbove hParentCap hBeforeTarget hRun
  have hCurrentBelow : below ambient before.size
      (Row.lift (F.height root) target (F.height childUpper)) = .ok ⟨before.size, index⟩ :=
    (hPreserve.below (by simp) _).trans hBelow
  obtain ⟨actualNodes, hNodes, hRead⟩ := cellAt_ok_iff.mp hCell
  have hCurrentCell : Canonical.cellAt ambient ⟨before.size, index⟩ = .ok actualParent :=
    cellAt_ok_iff.mpr ⟨actualNodes, hPreserve.column_read hNodes, hRead⟩
  rw [← d.destination] at hCurrentBelow hCurrentCell
  exact ⟨index, actualParent, hCurrentBelow, hCurrentCell, hRow⟩

#print axioms Frame.RootInterval.column_lt_of_height_lt
#print axioms DynamicBlockState.below_internal_parent

end OmegaY.Expansion
