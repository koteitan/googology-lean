/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/RootGeometry.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/RootGeometry.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.Preparation
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Values
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.RowSupport
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Domain

set_option backward.do.legacy false

/-!
# Root geometry in the old last column

The root is identified with the actual numerical father of the top's lower
neighbor. All nodes below refer to the original, successful canonical build.
Nothing in this module asserts preservation in the decremented mountain.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- Concrete nodes witnessing the old final top and its root edge. -/
structure RootGeometry {front : List Nat} {last : Nat} (p : Preparation front last) where
  topNode : (Frame.ofMountain p.initial).Node
  lower : (Frame.ofMountain p.initial).Node
  rootNode : (Frame.ofMountain p.initial).Node
  top_column : topNode.1.val = front.length
  top_last : topNode.2.val + 1 = (Frame.ofMountain p.initial).length topNode.1
  top_cell : (Frame.ofMountain p.initial).cell topNode = p.lastTop
  top_index_gt_one : 1 < topNode.2.val
  lower_column : lower.1.val = front.length
  lower_real : Frame.Real lower
  lower_upper : (Frame.ofMountain p.initial).upper lower = some topNode
  root_real : Frame.Real rootNode
  root_ref : Frame.ref rootNode = p.root
  root_cell : (Frame.ofMountain p.initial).cell rootNode = p.rootCell
  lower_parent : (Frame.ofMountain p.initial).P lower = some rootNode
  lower_actual_parent : findParent p.initial (Frame.ref lower) = .ok p.root
  top_row : p.lastTop.row =
    Row.B ((Frame.ofMountain p.initial).height lower) p.rootCell.row
  root_le_lower : p.rootCell.row ≤ (Frame.ofMountain p.initial).height lower
  lower_lt_top : (Frame.ofMountain p.initial).height lower < p.lastTop.row

/-- A final input greater than one forces a genuine top edge, whose stored
root is its lower node's numerical father. No root-realness premise is used. -/
theorem Preparation.root_geometry {front : List Nat} {last : Nat}
    (p : Preparation front last) (hlast : 1 < last) :
    Nonempty (RootGeometry p) := by
  have hLegal := build_success_legal p.initial_build
  obtain ⟨nodes, hColumn, hBottom⟩ := build_bottom_at p.initial_build
    (show (front ++ [last])[front.length]? = some last by simp)
  obtain ⟨hc, hNodes⟩ := Array.getElem?_eq_some_iff.mp hColumn
  subst nodes
  let nodes : Column := p.initial[front.length]
  change bottomValue nodes = some last at hBottom
  have hValid := p.initial_valid front.length hc
  have hSize : 2 ≤ nodes.size := hValid.size_ge_two
  have hTop : nodes.back? = some p.lastTop := by
    simpa only [hColumn, Option.bind_some] using p.initial_top
  obtain ⟨built, hBuilt, _, hTops⟩ := build_total hLegal
  have heBuilt : built = p.initial := Except.ok.inj (hBuilt.symm.trans p.initial_build)
  subst built
  obtain ⟨topCell, hTopCell, hTopOne⟩ := hTops front.length hc
  have heTop : topCell = p.lastTop := Option.some.inj (hTopCell.symm.trans hTop)
  have hOne : p.lastTop.value = 1 := heTop ▸ hTopOne
  have hTopRead : nodes[nodes.size - 1]? = some p.lastTop := by
    simpa only [Array.back?_eq_getElem?] using hTop
  have hTopHigh : 1 < nodes.size - 1 := by
    by_contra hn
    have hi : nodes.size - 1 = 1 := by omega
    rw [hi] at hTopRead
    have hValue : p.lastTop.value = last := by
      simpa only [bottomValue, hTopRead, Option.map_some, Option.some.injEq] using hBottom
    omega
  let c : Fin p.initial.size := ⟨front.length, hc⟩
  let topNode : (Frame.ofMountain p.initial).Node :=
    ⟨c, ⟨nodes.size - 1, by change nodes.size - 1 < nodes.size; omega⟩⟩
  let lower : (Frame.ofMountain p.initial).Node :=
    ⟨c, ⟨nodes.size - 2, by change nodes.size - 2 < nodes.size; omega⟩⟩
  have hLowerReal : Frame.Real lower := by unfold Frame.Real; dsimp [lower]; omega
  have hTopTyped : (Frame.ofMountain p.initial).cell topNode = p.lastTop := by
    exact (Array.getElem?_eq_some_iff.mp hTopRead).2
  have hLowerUpper : (Frame.ofMountain p.initial).upper lower = some topNode := by
    have he : nodes.size - 2 + 1 = nodes.size - 1 := by omega
    have hi : nodes.size - 1 < (Frame.ofMountain p.initial).length c := by
      change nodes.size - 1 < nodes.size
      omega
    simp [Frame.upper, lower, topNode, he, hi]
  have hNormal := build_normal_of_legal hLegal p.initial_build
  obtain ⟨rootNode, hParent, hRow, _, hLeft⟩ :=
    hNormal.upper_step lower topNode hLowerReal hLowerUpper
  rw [hTopTyped] at hLeft
  have hRootRef : Frame.ref rootNode = p.root :=
    Option.some.inj (hLeft.symm.trans p.top_left)
  have hRootRead := cellAt_of_frame_node p.initial rootNode
  rw [hRootRef] at hRootRead
  have hRootCell : (Frame.ofMountain p.initial).cell rootNode = p.rootCell :=
    Except.ok.inj (hRootRead.symm.trans p.initial_root)
  have hRootHeight : (Frame.ofMountain p.initial).height rootNode = p.rootCell.row := by
    exact congrArg Cell.row hRootCell
  have hTopHeight : (Frame.ofMountain p.initial).height topNode = p.lastTop.row :=
    congrArg Cell.row hTopTyped
  have hB : p.lastTop.row = Row.B ((Frame.ofMountain p.initial).height lower) p.rootCell.row := by
    simpa only [hTopHeight, hRootHeight] using hRow
  refine ⟨{
    topNode := topNode
    lower := lower
    rootNode := rootNode
    top_column := rfl
    top_last := by dsimp [topNode]; change nodes.size - 1 + 1 = nodes.size; omega
    top_cell := hTopTyped
    top_index_gt_one := hTopHigh
    lower_column := rfl
    lower_real := hLowerReal
    lower_upper := hLowerUpper
    root_real := Frame.real_of_value_pos hNormal.toOrdered (Frame.P_value hNormal.toOrdered hParent).1
    root_ref := hRootRef
    root_cell := hRootCell
    lower_parent := hParent
    lower_actual_parent := ?_
    top_row := hB
    root_le_lower := ?_
    lower_lt_top := ?_ }⟩
  · rw [← hRootRef]
    exact (Executable.findParent_ref_iff hNormal.toOrdered lower rootNode).mpr hParent
  · simpa only [hRootHeight] using Frame.P_height_le hNormal.toOrdered hParent
  · rw [hB]
    exact Row.lt_B _ _

theorem Preparation.root_index_pos {front : List Nat} {last : Nat}
    (p : Preparation front last) (hlast : 1 < last) : 0 < p.root.index := by
  obtain ⟨g⟩ := p.root_geometry hlast
  have he : g.rootNode.2.val = p.root.index := congrArg Ref.index g.root_ref
  exact he ▸ g.root_real

theorem Preparation.root_row_lt_top {front : List Nat} {last : Nat}
    (p : Preparation front last) (hlast : 1 < last) : p.rootCell.row < p.lastTop.row := by
  obtain ⟨g⟩ := p.root_geometry hlast
  exact lt_of_le_of_lt g.root_le_lower g.lower_lt_top

theorem Preparation.top_row_gt_one {front : List Nat} {last : Nat}
    (p : Preparation front last) (hlast : 1 < last) : (1 : Row) < p.lastTop.row := by
  obtain ⟨g⟩ := p.root_geometry hlast
  have hNormal := build_normal_of_success p.initial_build
  exact lt_of_le_of_lt (Frame.one_le_height hNormal.toOrdered g.lower_real) g.lower_lt_top

/-- Every real row at or below the root already occurs strictly below the
old last top. This conclusion concerns the initial mountain only. -/
theorem Preparation.root_row_support {front : List Nat} {last : Nat}
    (p : Preparation front last) (hlast : 1 < last)
    (w : (Frame.ofMountain p.initial).Node) (hwReal : Frame.Real w)
    (hwColumn : w.1.val = p.root.column)
    (hwRow : (Frame.ofMountain p.initial).height w ≤ p.rootCell.row) :
    ∃ v : (Frame.ofMountain p.initial).Node,
      Frame.Real v ∧ v.1.val = front.length ∧
      (Frame.ofMountain p.initial).height v < p.lastTop.row ∧
      (Frame.ofMountain p.initial).height v = (Frame.ofMountain p.initial).height w := by
  obtain ⟨g⟩ := p.root_geometry hlast
  have hNormal := build_normal_of_success p.initial_build
  have hRootColumn : g.rootNode.1.val = p.root.column := congrArg Ref.column g.root_ref
  have hRootRow : (Frame.ofMountain p.initial).height g.rootNode = p.rootCell.row :=
    congrArg Cell.row g.root_cell
  have hIn : (Frame.ofMountain p.initial).height w ∈
      (Frame.ofMountain p.initial).rowsBelow g.rootNode :=
    (Frame.mem_rowsBelow_iff_height hNormal.toOrdered).mpr
      ⟨w, hwReal, Fin.ext (hwColumn.trans hRootColumn.symm), by simpa only [hRootRow] using hwRow, rfl⟩
  have hLowerIn := Frame.P_rowsBelow hNormal g.lower_parent hIn
  obtain ⟨v, hvReal, hvColumn, hvRow, hvEq⟩ :=
    (Frame.mem_rowsBelow_iff_height hNormal.toOrdered).mp hLowerIn
  exact ⟨v, hvReal, (congrArg Fin.val hvColumn).trans g.lower_column,
    lt_of_le_of_lt hvRow g.lower_lt_top, hvEq⟩

#print axioms Preparation.root_geometry
#print axioms Preparation.root_row_support

end OmegaY.Expansion
