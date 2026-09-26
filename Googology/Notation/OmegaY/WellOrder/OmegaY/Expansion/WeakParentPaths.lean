/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/WeakParentPaths.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/WeakParentPaths.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.MarkerCompleteness
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Normal
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Domain
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.RootInterval

set_option backward.do.legacy false

/-!
# Actual weak paths and same-row numerical parent paths

This equivalence uses normality only on the source mountain. The root row
must be real: auxiliary row-zero paths are supplied separately by the
existing `PhantomChain` theorems.
-/

namespace OmegaY.Expansion

open Canonical Geometry

private theorem frame_upper_of_refs {F : Frame} {before after : F.Node} {column index : Nat}
    (hBefore : Frame.ref before = ⟨column, index⟩)
    (hAfter : Frame.ref after = ⟨column, index + 1⟩) : F.upper before = some after := by
  rcases before with ⟨c, i⟩
  rcases after with ⟨d, j⟩
  simp only [Frame.ref, Ref.mk.injEq] at hBefore hAfter
  have hc : d = c := Fin.ext (hAfter.1.trans hBefore.1.symm)
  subst d
  have hBound : i.val + 1 < F.length c := by have := j.isLt; omega
  simp only [Frame.upper, hBound, ↓reduceDIte, Option.some.injEq]
  apply Executable.ref_injective F
  simp only [Frame.ref, Ref.mk.injEq]
  exact ⟨trivial, by omega⟩

private theorem real_of_height_pos {F : Frame} (hF : F.Ordered) {u : F.Node}
    (hHeight : 0 < F.height u) : Frame.Real u := by
  by_contra hn
  have hi : u.2.val = 0 := by unfold Frame.Real at hn; omega
  have hi' : u.2 = ⟨0, by have := u.2.isLt; omega⟩ := Fin.ext hi
  change 0 < (F.cells u.1 u.2).row at hHeight
  rw [hi', hF.phantom] at hHeight
  exact (lt_irrefl (0 : Row)) hHeight

/-- A real actual two-leg edge is precisely a numerical-parent edge at
the same row. This statement refers to the executable stored left leg. -/
theorem twoLeg_iff_same_row_parent {mountain : Mountain}
    (hNormal : (Frame.ofMountain mountain).Normal)
    {u p : (Frame.ofMountain mountain).Node} (hReal : Frame.Real u) :
    TwoLeg mountain (Frame.ref p) (Frame.ref u) ↔
      (Frame.ofMountain mountain).P u = some p ∧
        (Frame.ofMountain mountain).height p = (Frame.ofMountain mountain).height u := by
  let F := Frame.ofMountain mountain
  constructor
  · rintro ⟨nodes, current, upper, parent, hNodes, hCurrent, hUpper, hLeft, _, hParent, hRow⟩
    have hCurrentCell : current = F.cell u := CellAt.unique
      ⟨nodes, hNodes, hCurrent⟩ (frame_ref_cellAt mountain u)
    have hParentCell : parent = F.cell p := CellAt.unique hParent (frame_ref_cellAt mountain p)
    obtain ⟨v, hVRef, hVCell⟩ := Canonical.frame_node_of_cellAt
      (cellAt_ok_iff.mpr (show CellAt mountain ⟨(Frame.ref u).column, (Frame.ref u).index + 1⟩ upper
        from ⟨nodes, hNodes, hUpper⟩))
    have hUV := frame_upper_of_refs (show Frame.ref u = ⟨(Frame.ref u).column, (Frame.ref u).index⟩ from rfl) hVRef
    obtain ⟨actualParent, hP, _, _, hStored⟩ := hNormal.upper_step u v hReal hUV
    have hParentRefEq : Frame.ref actualParent = Frame.ref p := Option.some.inj
      (hStored.symm.trans (by simpa only [hVCell] using hLeft))
    have hParentEq := Executable.ref_injective F hParentRefEq
    exact ⟨by simpa only [hParentEq] using hP,
      by simpa only [Frame.height, hCurrentCell, hParentCell] using hRow⟩
  · rintro ⟨hP, hRow⟩
    obtain ⟨v, hUV⟩ := hNormal.upper_of_parent hP
    obtain ⟨actualParent, hActual, _, _, hStored⟩ := hNormal.upper_step u v hReal hUV
    have hParentEq : actualParent = p := Option.some.inj (hActual.symm.trans hP)
    subst actualParent
    obtain ⟨hVCol, hVIndex⟩ := Frame.upper_spec hUV
    have hVRef : Frame.ref v = ⟨(Frame.ref u).column, (Frame.ref u).index + 1⟩ := by
      simp only [Frame.ref, Ref.mk.injEq]
      exact ⟨congrArg Fin.val hVCol, hVIndex⟩
    obtain ⟨nodes, hNodes, hCurrent⟩ := frame_ref_cellAt mountain u
    obtain ⟨upperNodes, hUpperNodes, hUpperRead⟩ := frame_ref_cellAt mountain v
    have hNodesEq : upperNodes = nodes := Option.some.inj
      (hUpperNodes.symm.trans (by simpa only [hVRef] using hNodes))
    subst upperNodes
    refine ⟨nodes, F.cell u, F.cell v, F.cell p, hNodes, hCurrent, ?_, hStored,
      Frame.P_column_lt hNormal.toOrdered hP, frame_ref_cellAt mountain p, hRow⟩
    simpa only [hVRef] using hUpperRead

private theorem forwardWeakPath_to_parentPath {mountain : Mountain}
    (hNormal : (Frame.ofMountain mountain).Normal)
    {root : (Frame.ofMountain mountain).Node} (hRoot : Frame.Real root)
    {current : Ref} (path : ForwardWeakPath mountain (Frame.ref root) current)
    {u : (Frame.ofMountain mountain).Node} (hURef : Frame.ref u = current) :
    Frame.ParentPath (Frame.ofMountain mountain) u root := by
  let F := Frame.ofMountain mountain
  induction path generalizing u with
  | root =>
    have he : u = root := Executable.ref_injective F hURef
    subst u
    exact .refl _
  | @step parent current previous edge ih =>
    have edgeCopy := edge
    obtain ⟨nodes, currentCell, upper, parentCell, hNodes, hCurrent, _, _, _, hParent, _⟩ := edgeCopy
    obtain ⟨p, hPRef, _⟩ := frame_node_of_cellAt hParent
    have hParentPath := ih hPRef
    have hPath : ForwardWeakPath mountain (Frame.ref root) current := .step previous edge
    have hCurrentAt : CellAt mountain current (F.cell u) := by
      simpa only [hURef] using frame_ref_cellAt mountain u
    have hRow : F.height u = F.height root :=
      hPath.row_eq (frame_ref_cellAt mountain root) hCurrentAt
    have hReal : Frame.Real u := real_of_height_pos hNormal.toOrdered
      (by rw [hRow]; exact Row.zero_lt_one.trans_le (Frame.one_le_height hNormal.toOrdered hRoot))
    have hEdge : TwoLeg mountain (Frame.ref p) (Frame.ref u) := by
      simpa only [hPRef, hURef] using edge
    have hP := ((twoLeg_iff_same_row_parent hNormal hReal).mp hEdge).1
    exact .cons hP hParentPath

private theorem parentPath_to_forwardWeakPath {mountain : Mountain}
    (hNormal : (Frame.ofMountain mountain).Normal)
    {root u : (Frame.ofMountain mountain).Node} (hRoot : Frame.Real root)
    (path : Frame.ParentPath (Frame.ofMountain mountain) u root)
    (hRow : (Frame.ofMountain mountain).height u = (Frame.ofMountain mountain).height root) :
    ForwardWeakPath mountain (Frame.ref root) (Frame.ref u) := by
  induction path with
  | refl _ => exact .root
  | @cons u p root hP rest ih =>
    have hParentRow : (Frame.ofMountain mountain).height p = (Frame.ofMountain mountain).height root :=
      le_antisymm ((Frame.P_height_le hNormal.toOrdered hP).trans hRow.le)
        (rest.height_le hNormal.toOrdered)
    have hReal : Frame.Real u := Frame.real_of_value_pos hNormal.toOrdered
      ((Frame.P_value hNormal.toOrdered hP).1.trans (Frame.P_value hNormal.toOrdered hP).2)
    have hEdge := (twoLeg_iff_same_row_parent hNormal hReal).mpr ⟨hP, hParentRow.trans hRow.symm⟩
    exact .step (ih hRoot hParentRow) hEdge

/-- Exact agreement of executable weak paths with the same-row part of the
actual numerical-parent graph. Positive root rows exclude the independently
handled auxiliary phantom chain. -/
theorem forwardWeakPath_iff_same_row_parentPath {mountain : Mountain}
    (hNormal : (Frame.ofMountain mountain).Normal)
    {root u : (Frame.ofMountain mountain).Node} (hRoot : Frame.Real root) :
    ForwardWeakPath mountain (Frame.ref root) (Frame.ref u) ↔
      Frame.ParentPath (Frame.ofMountain mountain) u root ∧
        (Frame.ofMountain mountain).height u = (Frame.ofMountain mountain).height root := by
  constructor
  · intro path
    exact ⟨forwardWeakPath_to_parentPath hNormal hRoot path rfl,
      path.row_eq (frame_ref_cellAt mountain root) (frame_ref_cellAt mountain u)⟩
  · rintro ⟨path, hRow⟩
    exact parentPath_to_forwardWeakPath hNormal hRoot path hRow

/-- The real executable Boolean recognizer, with its source-column-derived
allowance, recognizes exactly these numerical paths. -/
theorem weakReaches_iff_same_row_parentPath {mountain : Mountain}
    (hNormal : (Frame.ofMountain mountain).Normal)
    {root u : (Frame.ofMountain mountain).Node} (hRoot : Frame.Real root)
    {fuel : Nat} (hFuel : (Frame.ref u).column ≤ fuel) :
    weakReaches mountain (Frame.ref root) fuel (Frame.ref u) = .ok true ↔
      Frame.ParentPath (Frame.ofMountain mountain) u root ∧
        (Frame.ofMountain mountain).height u = (Frame.ofMountain mountain).height root := by
  rw [weakReaches_forward_iff hFuel, forwardWeakPath_iff_same_row_parentPath hNormal hRoot]

/-- Numerical root cones are precisely columns containing an actual
weak-reachable node at this real root row. -/
theorem rootCone_iff_forwardWeakPath {mountain : Mountain}
    (hNormal : (Frame.ofMountain mountain).Normal)
    {root u : (Frame.ofMountain mountain).Node} (hRoot : Frame.Real root) :
    Frame.RootCone (Frame.ofMountain mountain) root u ↔
      ∃ low : (Frame.ofMountain mountain).Node, low.1 = u.1 ∧
        ForwardWeakPath mountain (Frame.ref root) (Frame.ref low) := by
  constructor
  · rintro ⟨low, _, hColumn, hRow, path⟩
    exact ⟨low, hColumn, (forwardWeakPath_iff_same_row_parentPath hNormal hRoot).mpr ⟨path, hRow⟩⟩
  · rintro ⟨low, hColumn, path⟩
    obtain ⟨parentPath, hRow⟩ := (forwardWeakPath_iff_same_row_parentPath hNormal hRoot).mp path
    have hReal : Frame.Real low := real_of_height_pos hNormal.toOrdered
      (by rw [hRow]; exact Row.zero_lt_one.trans_le (Frame.one_le_height hNormal.toOrdered hRoot))
    exact ⟨low, hReal, hColumn, hRow, parentPath⟩

/-- For a real source node, the actual marker-array membership is exactly
a same-row numerical-parent path to an actual real root-prefix node.
The strict-right condition intentionally excludes the root column itself. -/
theorem markers_real_member_iff_parentPath {mountain : Mountain}
    (hNormal : (Frame.ofMountain mountain).Normal) (hLocal : WeakLocal mountain)
    {root u : (Frame.ofMountain mountain).Node} {marked : Array (List Ref)}
    (hMarkers : markers mountain (Frame.ref root) = .ok marked) (hReal : Frame.Real u) :
    BucketMem marked (Frame.ref u).column (Frame.ref u) ↔
      root.1.val < u.1.val ∧ ∃ low : (Frame.ofMountain mountain).Node,
        Frame.Real low ∧ low.1 = root.1 ∧ low.2.val ≤ root.2.val ∧
          Frame.ParentPath (Frame.ofMountain mountain) u low ∧
            (Frame.ofMountain mountain).height u = (Frame.ofMountain mountain).height low := by
  let F := Frame.ofMountain mountain
  have hRootValid : ValidRef mountain (Frame.ref root) := ⟨_, frame_ref_cellAt mountain root⟩
  rw [markers_member_iff hLocal hRootValid hMarkers]
  constructor
  · rintro ⟨_, hRight, _, index, hIndex, path⟩
    let low : F.Node := ⟨root.1, ⟨index, by
      have := root.2.isLt
      change index < (Frame.ofMountain mountain).length root.1
      change index ≤ root.2.val at hIndex
      omega⟩⟩
    have hLowRef : Frame.ref low = ⟨(Frame.ref root).column, index⟩ := rfl
    have hPath : ForwardWeakPath mountain (Frame.ref low) (Frame.ref u) := by
      simpa only [hLowRef] using path
    have hRow : F.height u = F.height low :=
      hPath.row_eq (frame_ref_cellAt mountain low) (frame_ref_cellAt mountain u)
    have hLowReal : Frame.Real low := real_of_height_pos hNormal.toOrdered
      (by rw [← hRow]; exact Row.zero_lt_one.trans_le (Frame.one_le_height hNormal.toOrdered hReal))
    exact ⟨hRight, low, hLowReal, rfl, hIndex,
      ((forwardWeakPath_iff_same_row_parentPath hNormal hLowReal).mp hPath).1, hRow⟩
  · rintro ⟨hRight, low, hLowReal, hColumn, hIndex, path, hRow⟩
    have hPath := (forwardWeakPath_iff_same_row_parentPath hNormal hLowReal).mpr ⟨path, hRow⟩
    have hLowRef : Frame.ref low = ⟨(Frame.ref root).column, low.2.val⟩ := by
      simp only [Frame.ref, Ref.mk.injEq]
      exact ⟨congrArg Fin.val hColumn, trivial⟩
    exact ⟨rfl, hRight, ⟨_, frame_ref_cellAt mountain u⟩, low.2.val, hIndex,
      by simpa only [hLowRef] using hPath⟩

/-- A real root cone supplies an actual marker in every strict-right
column of that cone, at the root row. This is the bridge from root-interval
geometry to the marker buckets used by `copyColumn`. -/
theorem rootCone_marker_witness {mountain : Mountain}
    (hNormal : (Frame.ofMountain mountain).Normal) (hLocal : WeakLocal mountain)
    {badRoot root u : (Frame.ofMountain mountain).Node} {marked : Array (List Ref)}
    (hMarkers : markers mountain (Frame.ref badRoot) = .ok marked)
    (hRootReal : Frame.Real root) (hRootColumn : root.1 = badRoot.1)
    (hRootIndex : root.2.val ≤ badRoot.2.val) (hRight : badRoot.1.val < u.1.val)
    (hCone : Frame.RootCone (Frame.ofMountain mountain) root u) :
    ∃ low : (Frame.ofMountain mountain).Node,
      low.1 = u.1 ∧ (Frame.ofMountain mountain).height low = (Frame.ofMountain mountain).height root ∧
        BucketMem marked (Frame.ref u).column (Frame.ref low) := by
  obtain ⟨low, hLowReal, hColumn, hRow, path⟩ := hCone
  have hMember := (markers_real_member_iff_parentPath hNormal hLocal hMarkers hLowReal).mpr
    ⟨by simpa only [hColumn] using hRight, root, hRootReal, hRootColumn, hRootIndex, path, hRow⟩
  exact ⟨low, hColumn, hRow, by simpa only [Frame.ref, hColumn] using hMember⟩

/-- Actual successful construction supplies normality and all stored-edge
validity needed for the marker equivalence; neither is an extra premise. -/
theorem build_markers_real_member_iff_parentPath {values : List Nat} {mountain : Mountain}
    (hBuild : build values = .ok mountain)
    {root u : (Frame.ofMountain mountain).Node} {marked : Array (List Ref)}
    (hMarkers : markers mountain (Frame.ref root) = .ok marked) (hReal : Frame.Real u) :
    BucketMem marked (Frame.ref u).column (Frame.ref u) ↔
      root.1.val < u.1.val ∧ ∃ low : (Frame.ofMountain mountain).Node,
        Frame.Real low ∧ low.1 = root.1 ∧ low.2.val ≤ root.2.val ∧
          Frame.ParentPath (Frame.ofMountain mountain) u low ∧
            (Frame.ofMountain mountain).height u = (Frame.ofMountain mountain).height low := by
  have hLegal := build_success_legal hBuild
  obtain ⟨actual, hActual, hValid, _⟩ := build_total hLegal
  have he : actual = mountain := Except.ok.inj (hActual.symm.trans hBuild)
  subst actual
  exact markers_real_member_iff_parentPath (build_normal_of_legal hLegal hBuild)
    (weakLocal_of_ordered hValid.toOrdered hValid.left_sources) hMarkers hReal

end OmegaY.Expansion

#print axioms OmegaY.Expansion.twoLeg_iff_same_row_parent
#print axioms OmegaY.Expansion.forwardWeakPath_iff_same_row_parentPath
#print axioms OmegaY.Expansion.weakReaches_iff_same_row_parentPath
#print axioms OmegaY.Expansion.rootCone_iff_forwardWeakPath
#print axioms OmegaY.Expansion.markers_real_member_iff_parentPath
#print axioms OmegaY.Expansion.rootCone_marker_witness
#print axioms OmegaY.Expansion.build_markers_real_member_iff_parentPath
