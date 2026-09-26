/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/PreparedParentInterval.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/PreparedParentInterval.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.CopiedParentInterval
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.MarkerIntervalGap
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.RootInterval

set_option backward.do.legacy false

/-!
# Interior copied parents selected from actual prepared source geometry

The parent marker, lack of intervening markers, source lower/upper bounds,
actual output adjacency and strict-below selection are all derived. The
statement covers source parents strictly above the interval root whose own
upper neighbour is strictly below the cap. Endpoint cases are separate.
-/

namespace OmegaY.Expansion

set_option maxHeartbeats 1000000

open Canonical Geometry

theorem ColumnCopyData.frame_source_read {mountain base : Mountain}
    {marked : Array (List Ref)} {references : List Ref} {sourceColumn shift rootColumn : Nat}
    (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)
    (hSource : base[sourceColumn]? = some d.sources) {u : (Frame.ofMountain base).Node}
    (hColumn : u.1.val = sourceColumn) :
    d.sources[u.2.val]? = some ((Frame.ofMountain base).cell u) := by
  obtain ⟨nodes, hNodes, hRead⟩ := cellAt_ok_iff.mp (cellAt_of_frame_node base u)
  have he : nodes = d.sources := Option.some.inj
    (hNodes.symm.trans (by simpa only [Frame.ref, hColumn] using hSource))
  simpa only [he, Frame.ref] using hRead

theorem ColumnCopyData.prepared_below_internal_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {mountain : Mountain} {references : List Ref} {sourceColumn shift : Nat}
    (d : ColumnCopyData mountain p.marked references sourceColumn shift p.root.column)
    (hSource : p.reduced[sourceColumn]? = some d.sources)
    (hParentPower : ∀ marker (hm : marker ∈ d.bucket),
      ColumnPowerSteps (d.marker_data marker hm).parentNodes)
    (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (index : Nat) (cell : Cell),
      (d.marker_data marker hm).parentNodes[index]? = some cell ∧
        cell.row = (d.marker_data marker hm).current.row)
    {root child parent childUpper parentUpper : (Frame.ofMountain p.reduced).Node}
    {degree : Nat} (hRootReal : Frame.Real root) (hDegree : 0 < degree)
    (hRootColumn : root.1.val = p.root.column) (hRootIndex : root.2.val ≤ p.root.index)
    (hRootBarrier : ∀ upper, (Frame.ofMountain p.reduced).upper root = some upper →
      Row.bump ((Frame.ofMountain p.reduced).height root) degree ≤
        (Frame.ofMountain p.reduced).height upper)
    (hParent : findParent p.reduced (Frame.ref child) = .ok (Frame.ref parent))
    (hChild : Frame.RootInterval (Frame.ofMountain p.reduced) root
      (Row.bump ((Frame.ofMountain p.reduced).height root) degree) child)
    (hChildUpper : (Frame.ofMountain p.reduced).upper child = some childUpper)
    (hParentUpper : (Frame.ofMountain p.reduced).upper parent = some parentUpper)
    (hParentColumn : parent.1.val = sourceColumn) (hRight : p.root.column < sourceColumn)
    (hParentAbove : (Frame.ofMountain p.reduced).height root < (Frame.ofMountain p.reduced).height parent)
    (hParentCap : (Frame.ofMountain p.reduced).height parentUpper <
      Row.bump ((Frame.ofMountain p.reduced).height root) degree)
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
  have hNormal := build_normal_of_legal (build_success_legal p.reduced_build) p.reduced_build
  have hp : F.P child = some parent :=
    (Executable.findParent_ref_iff hNormal.toOrdered child parent).mp hParent
  have hParentInside : Frame.RootInterval F root (Row.bump (F.height root) degree) parent :=
    (Frame.root_interval_parent_iff_column hNormal hRootReal
      (Row.bump_strictMono_exponent _ hDegree) hRootBarrier hp hChild).mpr
      (by rw [hRootColumn, hParentColumn]; exact hRight.le)
  obtain ⟨badRoot, hBadRef, _⟩ := frame_node_of_cellAt (cellAt_ok_iff.mp p.restored_root)
  have hBadColumn : badRoot.1.val = p.root.column := congrArg Ref.column hBadRef
  have hBadIndex : badRoot.2.val = p.root.index := congrArg Ref.index hBadRef
  have hMarkers : markers p.reduced (Frame.ref badRoot) = .ok p.marked := by
    simpa only [hBadRef] using p.markers_built
  obtain ⟨low, hLowColumn, hLowRow, hMember⟩ := rootCone_marker_witness hNormal
    (weakLocal_of_ordered p.reduced_valid.toOrdered p.reduced_valid.left_sources)
    hMarkers hRootReal (Fin.ext (hRootColumn.trans hBadColumn.symm))
    (by rw [hBadIndex]; exact hRootIndex)
    (by rw [hBadColumn, hParentColumn]; exact hRight) hParentInside.1
  have hm : Frame.ref low ∈ d.bucket := by
    change BucketMem p.marked sourceColumn (Frame.ref low)
    simpa only [Frame.ref, hParentColumn] using hMember
  let md := d.marker_data (Frame.ref low) hm
  have hLowRead := d.frame_source_read hSource (show low.1.val = sourceColumn by
    rw [hLowColumn, hParentColumn])
  have hCurrentEq : md.current = F.cell low := Option.some.inj (md.current_at.symm.trans hLowRead)
  have hMarkerRow : md.current.row = F.height root := by
    change md.current.row = (F.cell root).row
    rw [hCurrentEq]
    exact hLowRow
  have hTargetEq : md.targetCell.row = target := Except.ok.inj
    (md.reference.symm.trans (by simpa only [hMarkerRow] using hTarget))
  have hLowerRead := d.frame_source_read hSource hParentColumn
  have hUpperRead : d.sources[parent.2.val + 1]? = some (F.cell parentUpper) := by
    have h := d.frame_source_read hSource (show parentUpper.1.val = sourceColumn by
      rw [(Frame.upper_spec hParentUpper).1, hParentColumn])
    simpa only [(Frame.upper_spec hParentUpper).2] using h
  have hAfter : (Frame.ref low).index < parent.2.val := by
    by_contra hn
    have hLe : parent.2.val ≤ (Frame.ref low).index := by omega
    have hRow : (F.cell parent).row ≤ md.current.row := by
      rcases eq_or_lt_of_le hLe with he | hl
      · have hc : F.cell parent = md.current := Option.some.inj
          (hLowerRead.symm.trans (by simpa only [he] using md.current_at))
        exact congrArg Cell.row hc |>.le
      · exact (d.source_valid.rows_strict _ _ _ _ hLowerRead md.current_at hl).le
    rw [hMarkerRow] at hRow
    exact not_lt_of_ge hRow hParentAbove
  have hNoBetween := d.prepared_no_markers_through_source_index hSource hRootColumn
    hRootBarrier hm hMarkerRow hUpperRead hParentCap
  have hChildRow : F.height childUpper = Row.B (F.height child) (F.height parent) :=
    (Frame.aboveHeight_of_upper hChildUpper).symm.trans (hNormal.above_row hp)
  have hLow : (F.cell parent).row < F.height childUpper := by
    rw [hChildRow]
    exact (Frame.P_height_le hNormal.toOrdered hp).trans_lt (Row.lt_B _ _)
  have hHigh : F.height childUpper ≤ (F.cell parentUpper).row :=
    Frame.father_upper_bound_nodes hNormal hp hChildUpper hParentUpper
  obtain ⟨index, actualParent, hBelow, _, hCell, hRow⟩ :=
    d.copyColumn_below_lifted_source_pair hParentPower hParentLow
      (build_source_no_premature_one p.reduced_build hSource)
      hRun hm hLowerRead hUpperRead hAfter hNoBetween hLow hHigh
  have hLift : (fun r => Row.lift md.current.row md.targetCell.row r) =
      (fun r => Row.lift (F.height root) target r) := by rw [hMarkerRow, hTargetEq]
  exact ⟨index, actualParent,
    (congrArg (below (mountain.push column) mountain.size) (congrFun hLift (F.height childUpper))).symm.trans hBelow,
    hCell, hRow.trans (congrFun hLift (F.height parent))⟩

#print axioms ColumnCopyData.prepared_below_internal_parent

end OmegaY.Expansion
