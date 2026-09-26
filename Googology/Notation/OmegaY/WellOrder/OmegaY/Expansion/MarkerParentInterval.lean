/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/MarkerParentInterval.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/MarkerParentInterval.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.FillContourSeam
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.WeakParentPaths

set_option backward.do.legacy false

/-!
# Actual copied-parent selection at the marker row

The source successor row is derived from its same-row parent path and the
father upper bound. It is not assumed as a copied-edge certificate. The
actual copied marker target is then selected below its own successor,
including the unraised target case.
-/

namespace OmegaY.Geometry.Frame

/-- At the root row, the weak-cone witness is the given physical node. -/
theorem RootCone.parentPath_at_root {F : Frame} (hF : F.Ordered)
    {root u : F.Node} (hCone : RootCone F root u)
    (hRow : F.height u = F.height root) : ParentPath F u root := by
  obtain ⟨low, _, hColumn, hLowRow, hPath⟩ := hCone
  have hEq : low = u := node_eq_of_column_height hF hColumn (hLowRow.trans hRow.symm)
  simpa only [hEq] using hPath

/-- A strict-right real-row cone node has a first same-row parent edge and
an actual upper node at the successor of the marker row. -/
theorem RootCone.successor_at_root {F : Frame} (hF : F.Normal)
    {root u : F.Node} (hCone : RootCone F root u)
    (hRow : F.height u = F.height root) (hRight : root.1.val < u.1.val) :
    ∃ parent upper, F.P u = some parent ∧ F.height parent = F.height root ∧
      F.upper u = some upper ∧ F.height upper = Row.bump (F.height root) 0 := by
  have hPath := hCone.parentPath_at_root hF.toOrdered hRow
  cases hPath with
  | refl => exact False.elim ((lt_irrefl _) hRight)
  | @cons u parent root hParent rest =>
    have hParentRow : F.height parent = F.height root :=
      le_antisymm ((P_height_le hF.toOrdered hParent).trans hRow.le)
        (rest.height_le hF.toOrdered)
    obtain ⟨upper, hUpper⟩ := hF.upper_of_parent hParent
    refine ⟨parent, upper, hParent, hParentRow, hUpper, ?_⟩
    calc
      F.height upper = Row.B (F.height u) (F.height parent) :=
        (aboveHeight_of_upper hUpper).symm.trans (hF.above_row hParent)
      _ = Row.bump (F.height root) 0 := by rw [hRow, hParentRow, Row.B_self]

/-- If the actual source father is exactly a strict-right marker, the
father bound forces its child to the same marker row and successor. -/
theorem marker_parent_successor {F : Frame} (hF : F.Normal)
    {root child parent childUpper : F.Node}
    (hParent : F.P child = some parent) (hCone : RootCone F root parent)
    (hRow : F.height parent = F.height root) (hRight : root.1.val < parent.1.val)
    (hUpper : F.upper child = some childUpper) :
    F.height child = F.height root ∧
      F.height childUpper = Row.bump (F.height root) 0 := by
  obtain ⟨_, parentUpper, _, _, hParentUpper, hParentUpperRow⟩ :=
    hCone.successor_at_root hF hRow hRight
  have hLower : F.height root ≤ F.height child := by
    simpa only [hRow] using P_height_le hF.toOrdered hParent
  have hUpperBound : F.height childUpper ≤ Row.bump (F.height root) 0 := by
    rw [← hParentUpperRow]
    exact father_upper_bound_nodes hF hParent hUpper hParentUpper
  have hStep : F.height childUpper = Row.B (F.height child) (F.height parent) :=
    (aboveHeight_of_upper hUpper).symm.trans (hF.above_row hParent)
  have hStrict : F.height child < F.height childUpper := by
    rw [hStep]
    exact Row.lt_B _ _
  have hBelow : F.height child < Row.bump (F.height root) 0 := hStrict.trans_le hUpperBound
  have hChildRow : F.height child = F.height root :=
    (Row.jump_eq_zero.mp (Nat.eq_zero_of_le_zero
      (Row.jump_le_of_lt_bump hLower hBelow))).symm
  exact ⟨hChildRow, by rw [hStep, hChildRow, hRow, Row.B_self]⟩

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry

/-- The executable preparation and the child's root interval supply the
actual parent's marker membership and both source row identities. -/
theorem Preparation.parent_at_root_marker_successor
    {front : List Nat} {last : Nat} (p : Preparation front last)
    {root child parent childUpper : (Frame.ofMountain p.reduced).Node}
    {degree : Nat} (hRootReal : Frame.Real root) (hDegree : 0 < degree)
    (hRootColumn : root.1.val = p.root.column) (hRootIndex : root.2.val ≤ p.root.index)
    (hRootBarrier : ∀ upper, (Frame.ofMountain p.reduced).upper root = some upper →
      Row.bump ((Frame.ofMountain p.reduced).height root) degree ≤
        (Frame.ofMountain p.reduced).height upper)
    (hParent : findParent p.reduced (Frame.ref child) = .ok (Frame.ref parent))
    (hChild : Frame.RootInterval (Frame.ofMountain p.reduced) root
      (Row.bump ((Frame.ofMountain p.reduced).height root) degree) child)
    (hChildUpper : (Frame.ofMountain p.reduced).upper child = some childUpper)
    (hRight : p.root.column < parent.1.val)
    (hParentRow : (Frame.ofMountain p.reduced).height parent =
      (Frame.ofMountain p.reduced).height root) :
    BucketMem p.marked parent.1.val (Frame.ref parent) ∧
      (Frame.ofMountain p.reduced).height child = (Frame.ofMountain p.reduced).height root ∧
      (Frame.ofMountain p.reduced).height childUpper =
        Row.bump ((Frame.ofMountain p.reduced).height root) 0 := by
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_legal (build_success_legal p.reduced_build) p.reduced_build
  have hp : F.P child = some parent :=
    (Executable.findParent_ref_iff hNormal.toOrdered child parent).mp hParent
  have hParentInside : Frame.RootInterval F root (Row.bump (F.height root) degree) parent :=
    (Frame.root_interval_parent_iff_column hNormal hRootReal
      (Row.bump_strictMono_exponent _ hDegree) hRootBarrier hp hChild).mpr
      (by rw [hRootColumn]; exact hRight.le)
  have hRows := Frame.marker_parent_successor hNormal hp hParentInside.1 hParentRow
    (by simpa only [hRootColumn] using hRight) hChildUpper
  obtain ⟨badRoot, hBadRef, _⟩ := frame_node_of_cellAt (cellAt_ok_iff.mp p.restored_root)
  have hBadColumn : badRoot.1.val = p.root.column := congrArg Ref.column hBadRef
  have hBadIndex : badRoot.2.val = p.root.index := congrArg Ref.index hBadRef
  have hMarkers : markers p.reduced (Frame.ref badRoot) = .ok p.marked := by
    simpa only [hBadRef] using p.markers_built
  obtain ⟨low, hLowColumn, hLowRow, hMember⟩ := rootCone_marker_witness hNormal
    (weakLocal_of_ordered p.reduced_valid.toOrdered p.reduced_valid.left_sources)
    hMarkers hRootReal (Fin.ext (hRootColumn.trans hBadColumn.symm))
    (by rw [hBadIndex]; exact hRootIndex)
    (by rw [hBadColumn]; exact hRight) hParentInside.1
  have hLowEq : low = parent := Frame.node_eq_of_column_height hNormal.toOrdered
    hLowColumn (hLowRow.trans hParentRow.symm)
  have hRefEq : Frame.ref low = Frame.ref parent := congrArg Frame.ref hLowEq
  change BucketMem p.marked parent.1.val (Frame.ref low) at hMember
  rw [hRefEq] at hMember
  exact ⟨hMember, hRows⟩

/-- The real output target node, with its fresh index, is selected below
its successor even when no gap was filled because the target did not rise. -/
theorem ColumnCopyData.copyColumn_below_marker_target
    {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
    {sourceColumn shift rootColumn : Nat}
    (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)
    (hParentPower : ∀ marker (hm : marker ∈ d.bucket),
      ColumnPowerSteps (d.marker_data marker hm).parentNodes)
    (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (index : Nat) (cell : Cell),
      (d.marker_data marker hm).parentNodes[index]? = some cell ∧
        cell.row = (d.marker_data marker hm).current.row)
    {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {marker : Ref} (hm : marker ∈ d.bucket) :
    ∃ (index : Nat) (cell : Cell),
      below (mountain.push column) mountain.size
        (Row.bump (d.marker_data marker hm).targetCell.row 0) = .ok ⟨mountain.size, index⟩ ∧
      Canonical.cellAt (mountain.push column) ⟨mountain.size, index⟩ = .ok cell ∧
      cell.row = (d.marker_data marker hm).targetCell.row := by
  obtain ⟨index, cell, hRead, hRow⟩ :=
    (d.copyColumn_marker_target_reads hParentPower hParentLow hRun hm).2
  have hActual : Canonical.cellAt (mountain.push column) ⟨mountain.size, index⟩ = .ok cell :=
    cellAt_ok_iff.mpr ⟨column, by simp, hRead⟩
  obtain ⟨actual, hActualRun, _, _, _, hValid⟩ := d.copyColumn_valid
  have he : actual = column := Except.ok.inj (hActualRun.symm.trans hRun)
  subst actual
  refine ⟨index, cell, ?_, hActual, hRow⟩
  simpa only [hRow] using below_bump_zero_of_read hValid hActual

/-- Prepared same-root-row source parents give exact actual shifted-column
selection below the lifted child upper. No source successor identity or
copied-normality condition is a premise. -/
theorem ColumnCopyData.prepared_below_marker_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {mountain : Mountain} {references : List Ref} {sourceColumn shift : Nat}
    (d : ColumnCopyData mountain p.marked references sourceColumn shift p.root.column)
    (hSource : p.reduced[sourceColumn]? = some d.sources)
    (hParentPower : ∀ marker (hm : marker ∈ d.bucket),
      ColumnPowerSteps (d.marker_data marker hm).parentNodes)
    (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (index : Nat) (cell : Cell),
      (d.marker_data marker hm).parentNodes[index]? = some cell ∧
        cell.row = (d.marker_data marker hm).current.row)
    {root child parent childUpper : (Frame.ofMountain p.reduced).Node}
    {degree : Nat} (hRootReal : Frame.Real root) (hDegree : 0 < degree)
    (hRootColumn : root.1.val = p.root.column) (hRootIndex : root.2.val ≤ p.root.index)
    (hRootBarrier : ∀ upper, (Frame.ofMountain p.reduced).upper root = some upper →
      Row.bump ((Frame.ofMountain p.reduced).height root) degree ≤
        (Frame.ofMountain p.reduced).height upper)
    (hParent : findParent p.reduced (Frame.ref child) = .ok (Frame.ref parent))
    (hChild : Frame.RootInterval (Frame.ofMountain p.reduced) root
      (Row.bump ((Frame.ofMountain p.reduced).height root) degree) child)
    (hChildUpper : (Frame.ofMountain p.reduced).upper child = some childUpper)
    (hParentColumn : parent.1.val = sourceColumn) (hRight : p.root.column < sourceColumn)
    (hParentRow : (Frame.ofMountain p.reduced).height parent =
      (Frame.ofMountain p.reduced).height root)
    {target : Row}
    (hTarget : referenceAt mountain references ((Frame.ofMountain p.reduced).height root) = .ok target)
    {column : Column}
    (hRun : copyColumn mountain p.marked references sourceColumn shift p.root.column = .ok column) :
    ∃ (index : Nat) (actualParent : Cell),
      below (mountain.push column) mountain.size
        (Row.lift ((Frame.ofMountain p.reduced).height root) target
          ((Frame.ofMountain p.reduced).height childUpper)) = .ok ⟨mountain.size, index⟩ ∧
      Canonical.cellAt (mountain.push column) ⟨mountain.size, index⟩ = .ok actualParent ∧
      actualParent.row = Row.lift ((Frame.ofMountain p.reduced).height root) target
        ((Frame.ofMountain p.reduced).height parent) := by
  let F := Frame.ofMountain p.reduced
  obtain ⟨hMember, _, hChildUpperRow⟩ := p.parent_at_root_marker_successor hRootReal hDegree
    hRootColumn hRootIndex hRootBarrier hParent hChild hChildUpper
    (by simpa only [hParentColumn] using hRight) hParentRow
  have hm : Frame.ref parent ∈ d.bucket := by
    change BucketMem p.marked sourceColumn (Frame.ref parent)
    simpa only [hParentColumn] using hMember
  let md := d.marker_data (Frame.ref parent) hm
  obtain ⟨nodes, hNodes, hRead⟩ := cellAt_ok_iff.mp (cellAt_of_frame_node p.reduced parent)
  have hNodesEq : nodes = d.sources := Option.some.inj
    (hNodes.symm.trans (by simpa only [Frame.ref, hParentColumn] using hSource))
  have hCurrentEq : md.current = F.cell parent := Option.some.inj
    (md.current_at.symm.trans (by simpa only [hNodesEq, Frame.ref] using hRead))
  have hMarkerRow : md.current.row = F.height root := by
    rw [hCurrentEq]
    exact hParentRow
  have hTargetEq : md.targetCell.row = target := Except.ok.inj
    (md.reference.symm.trans (by simpa only [hMarkerRow] using hTarget))
  obtain ⟨index, actualParent, hBelow, hCell, hRow⟩ :=
    d.copyColumn_below_marker_target hParentPower hParentLow hRun hm
  change below (mountain.push column) mountain.size (Row.bump md.targetCell.row 0) = _ at hBelow
  change actualParent.row = md.targetCell.row at hRow
  rw [hTargetEq] at hBelow hRow
  have hCeiling : Row.lift (F.height root) target (F.height childUpper) = Row.bump target 0 := by
    rw [hChildUpperRow, Row.lift_bump (le_refl (F.height root)), Row.lift_at_root]
  exact ⟨index, actualParent, by rw [hCeiling]; exact hBelow, hCell,
    by simpa only [hParentRow, Row.lift_at_root] using hRow⟩

/-- During a real block, the earlier copied parent column already contains
the selected reference target. Its exact new index is selected in the current
ambient mountain, without inspecting a hypothetical new child column. -/
theorem DynamicBlockState.below_marker_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    {root child parent childUpper : (Frame.ofMountain p.reduced).Node}
    {degree : Nat} (hRootReal : Frame.Real root) (hDegree : 0 < degree)
    (hRootColumn : root.1.val = p.root.column) (hRootIndex : root.2.val ≤ p.root.index)
    (hRootBarrier : ∀ upper, (Frame.ofMountain p.reduced).upper root = some upper →
      Row.bump ((Frame.ofMountain p.reduced).height root) degree ≤
        (Frame.ofMountain p.reduced).height upper)
    (hParent : findParent p.reduced (Frame.ref child) = .ok (Frame.ref parent))
    (hChild : Frame.RootInterval (Frame.ofMountain p.reduced) root
      (Row.bump ((Frame.ofMountain p.reduced).height root) degree) child)
    (hChildUpper : (Frame.ofMountain p.reduced).upper child = some childUpper)
    (hChildColumn : child.1.val = next) (hRight : p.root.column < parent.1.val)
    (hParentRow : (Frame.ofMountain p.reduced).height parent =
      (Frame.ofMountain p.reduced).height root)
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
  obtain ⟨hMember, _, hChildUpperRow⟩ := p.parent_at_root_marker_successor hRootReal hDegree
    hRootColumn hRootIndex hRootBarrier hParent hChild hChildUpper hRight hParentRow
  have hNormal := build_normal_of_legal (build_success_legal p.reduced_build) p.reduced_build
  have hp : F.P child = some parent :=
    (Executable.findParent_ref_iff hNormal.toOrdered child parent).mp hParent
  have hParentLeft : parent.1.val < next := by
    simpa only [hChildColumn] using Frame.P_column_lt hNormal.toOrdered hp
  obtain ⟨column, hColumn, _, hRows⟩ := s.copied_columns parent.1.val hRight hParentLeft
  have hCurrentRead := cellAt_of_frame_node p.reduced parent
  have hCurrentTarget : referenceAt start references (F.cell parent).row = .ok target := by
    change referenceAt start references (F.height parent) = .ok target
    rw [hParentRow]
    exact hTarget
  obtain ⟨index, actualParent, hRead, hRow⟩ :=
    (hRows (Frame.ref parent) hMember (F.cell parent) hCurrentRead target hCurrentTarget).2
  have hActual : Canonical.cellAt ambient
      ⟨parent.1.val + block * (p.reduced.size - 1 - p.root.column), index⟩ = .ok actualParent :=
    cellAt_ok_iff.mpr ⟨column, hColumn, hRead⟩
  have hBelow := below_bump_zero_of_read s.ambient_valid hActual
  rw [hRow] at hBelow
  have hCeiling : Row.lift (F.height root) target (F.height childUpper) = Row.bump target 0 := by
    rw [hChildUpperRow, Row.lift_bump (le_refl (F.height root)), Row.lift_at_root]
  exact ⟨index, actualParent, by rw [hCeiling]; exact hBelow, hActual,
    by simpa only [hParentRow, Row.lift_at_root] using hRow⟩

end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.RootCone.parentPath_at_root
#print axioms OmegaY.Geometry.Frame.RootCone.successor_at_root
#print axioms OmegaY.Geometry.Frame.marker_parent_successor
#print axioms OmegaY.Expansion.Preparation.parent_at_root_marker_successor
#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_below_marker_target
#print axioms OmegaY.Expansion.ColumnCopyData.prepared_below_marker_parent
#print axioms OmegaY.Expansion.DynamicBlockState.below_marker_parent
