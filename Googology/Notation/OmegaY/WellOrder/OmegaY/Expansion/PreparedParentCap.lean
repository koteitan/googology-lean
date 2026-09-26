/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/PreparedParentCap.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/PreparedParentCap.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.PreparedParentInterval
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ContourCapBarrier
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.CopiedParentTop

set_option backward.do.legacy false

/-!
# Actual prepared parents at a crossed cap or at the source top

The source numerical parent and root interval supply its real root-row
marker. Query-height bounds are proved from the source B equation and the
common lift. A target below the chosen cap is an explicit reference-interval
input; it is not inferred from an arbitrary smaller root barrier.
-/

namespace OmegaY.Expansion

open Canonical Geometry

namespace ColumnCopyData

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {mountain : Mountain} {references : List Ref} {sourceColumn shift : Nat}
  (d : ColumnCopyData mountain p.marked references sourceColumn shift p.root.column)
  (hSource : p.reduced[sourceColumn]? = some d.sources)
  {root child parent childUpper : (Frame.ofMountain p.reduced).Node} {degree : Nat}
  (hRootReal : Frame.Real root) (hDegree : 0 < degree)
  (hRootColumn : root.1.val = p.root.column) (hRootIndex : root.2.val ≤ p.root.index)
  (hRootBarrier : ∀ upper, (Frame.ofMountain p.reduced).upper root = some upper →
    Row.bump ((Frame.ofMountain p.reduced).height root) degree ≤
      (Frame.ofMountain p.reduced).height upper)
  (hParent : findParent p.reduced (Frame.ref child) = .ok (Frame.ref parent))
  (hChild : Frame.RootInterval (Frame.ofMountain p.reduced) root
    (Row.bump ((Frame.ofMountain p.reduced).height root) degree) child)
  (hChildUpper : (Frame.ofMountain p.reduced).upper child = some childUpper)
  (hParentColumn : parent.1.val = sourceColumn) (hRight : p.root.column < sourceColumn)
  {target : Row}
  (hTarget : referenceAt mountain references ((Frame.ofMountain p.reduced).height root) = .ok target)

include d hSource hRootReal hDegree hRootColumn hRootIndex hRootBarrier hParent hChild
  hChildUpper hParentColumn hRight hTarget

/-- The real source parent supplies the marker used by its copied contour,
with the exact actual reference target and source B equation. -/
theorem prepared_parent_marker_data :
    ∃ (marker : Ref) (hm : marker ∈ d.bucket),
      Frame.RootInterval (Frame.ofMountain p.reduced) root
        (Row.bump ((Frame.ofMountain p.reduced).height root) degree) parent ∧
      (d.marker_data marker hm).current.row = (Frame.ofMountain p.reduced).height root ∧
      (d.marker_data marker hm).targetCell.row = target ∧
      (Frame.ofMountain p.reduced).height childUpper =
        Row.B ((Frame.ofMountain p.reduced).height child) ((Frame.ofMountain p.reduced).height parent) := by
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
    rw [hCurrentEq]
    exact hLowRow
  have hTargetEq : md.targetCell.row = target := Except.ok.inj
    (md.reference.symm.trans (by simpa only [hMarkerRow] using hTarget))
  exact ⟨Frame.ref low, hm, hParentInside, hMarkerRow, hTargetEq,
    (Frame.aboveHeight_of_upper hChildUpper).symm.trans (hNormal.above_row hp)⟩

section ParentInputs

variable
  (hParentPower : ∀ marker (hm : marker ∈ d.bucket),
    ColumnPowerSteps (d.marker_data marker hm).parentNodes)
  (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (index : Nat) (cell : Cell),
    (d.marker_data marker hm).parentNodes[index]? = some cell ∧
      cell.row = (d.marker_data marker hm).current.row)
  (hParentAbove : (Frame.ofMountain p.reduced).height root < (Frame.ofMountain p.reduced).height parent)
  {column : Column}
  (hRun : copyColumn mountain p.marked references sourceColumn shift p.root.column = .ok column)

include hParentPower hParentLow hParentAbove hRun

/-- The cap-crossing parent is selected by the lifted actual child-upper
row. No query-ceiling bound is assumed: both bounds follow from the source
parent relation and the lifted B equation. -/
theorem prepared_below_cap_parent
    {parentUpper : (Frame.ofMountain p.reduced).Node}
    (hParentUpper : (Frame.ofMountain p.reduced).upper parent = some parentUpper)
    (hParentCap : Row.bump ((Frame.ofMountain p.reduced).height root) degree ≤
      (Frame.ofMountain p.reduced).height parentUpper)
    (hTargetCap : target < Row.bump ((Frame.ofMountain p.reduced).height root) degree) :
    ∃ (index : Nat) (actualParent : Cell),
      below (mountain.push column) mountain.size
        (Row.lift ((Frame.ofMountain p.reduced).height root) target
          ((Frame.ofMountain p.reduced).height childUpper)) = .ok ⟨mountain.size, index⟩ ∧
      Canonical.cellAt (mountain.push column) ⟨mountain.size, index⟩ = .ok actualParent ∧
      actualParent.row = Row.lift ((Frame.ofMountain p.reduced).height root) target
        ((Frame.ofMountain p.reduced).height parent) := by
  let F := Frame.ofMountain p.reduced
  obtain ⟨marker, hm, hParentInside, hMarkerRow, hTargetEq, hChildRow⟩ :=
    d.prepared_parent_marker_data hSource hRootReal hDegree hRootColumn hRootIndex hRootBarrier
      hParent hChild hChildUpper hParentColumn hRight hTarget
  let md := d.marker_data marker hm
  have hLowerRead := d.frame_source_read hSource hParentColumn
  have hUpperRead : d.sources[parent.2.val + 1]? = some (F.cell parentUpper) := by
    have h := d.frame_source_read hSource (show parentUpper.1.val = sourceColumn by
      rw [(Frame.upper_spec hParentUpper).1, hParentColumn])
    simpa only [(Frame.upper_spec hParentUpper).2] using h
  obtain ⟨index, actualParent, hActual, hActualRow, _, hBelow⟩ :=
    d.prepared_crossed_cap_below hSource hParentPower hParentLow
      (build_source_no_premature_one p.reduced_build hSource) hRootColumn hRootBarrier hRun hm
      hMarkerRow hLowerRead hUpperRead hParentAbove hParentInside.2.2 hParentCap
      (by simpa only [hTargetEq] using hTargetCap)
  have hTargetLower : F.height root ≤ target := by
    simpa only [md, hMarkerRow, hTargetEq] using md.target_lower
  have hLiftChild := Row.lift_mem_interval hTargetLower hTargetCap hChild.2.1 hChild.2.2
  have hLiftParent := Row.lift_mem_interval hTargetLower hTargetCap hParentInside.2.1 hParentInside.2.2
  have hNormal := build_normal_of_legal (build_success_legal p.reduced_build) p.reduced_build
  have hp : F.P child = some parent :=
    (Executable.findParent_ref_iff hNormal.toOrdered child parent).mp hParent
  have hQuery : Row.lift (F.height root) target (F.height childUpper) =
      Row.B (Row.lift (F.height root) target (F.height child))
        (Row.lift (F.height root) target (F.height parent)) := by
    rw [hChildRow, Row.lift_B hChild.2.1 hParentInside.2.1]
  have hQueryLow : actualParent.row < Row.lift (F.height root) target (F.height childUpper) := by
    rw [hActualRow, hTargetEq, hQuery]
    exact (Row.lift_monotone hParentInside.2.1 (Frame.P_height_le hNormal.toOrdered hp)).trans_lt (Row.lt_B _ _)
  have hQueryHigh : Row.lift (F.height root) target (F.height childUpper) ≤ Row.bump (F.height root) degree := by
    rw [hQuery]
    exact Row.B_le_cap_of_same_interval hLiftChild.1 hLiftChild.2 hLiftParent.1 hLiftParent.2
  exact ⟨index, actualParent, hBelow _ hQueryLow hQueryHigh,
    cellAt_ok_iff.mpr ⟨column, by simp, hActual⟩,
    by simpa only [hTargetEq, Frame.height] using hActualRow⟩

omit hParentAbove in
/-- A source parent without an upper neighbour is the actual source top.
The root marker is the highest marker of this column, so copying preserves
the lifted parent as the actual completed top. No target-cap inequality or
assumed query-height inequality is needed for this case. -/
theorem prepared_below_source_top_parent
    (hParentTop : (Frame.ofMountain p.reduced).upper parent = none) :
    ∃ (index : Nat) (actualParent : Cell),
      below (mountain.push column) mountain.size
        (Row.lift ((Frame.ofMountain p.reduced).height root) target
          ((Frame.ofMountain p.reduced).height childUpper)) = .ok ⟨mountain.size, index⟩ ∧
      Canonical.cellAt (mountain.push column) ⟨mountain.size, index⟩ = .ok actualParent ∧
      actualParent.row = Row.lift ((Frame.ofMountain p.reduced).height root) target
        ((Frame.ofMountain p.reduced).height parent) := by
  let F := Frame.ofMountain p.reduced
  obtain ⟨marker, hm, hParentInside, hMarkerRow, hTargetEq, hChildRow⟩ :=
    d.prepared_parent_marker_data hSource hRootReal hDegree hRootColumn hRootIndex hRootBarrier
      hParent hChild hChildUpper hParentColumn hRight hTarget
  have hLowerRead := d.frame_source_read hSource hParentColumn
  have hColumnRead : p.reduced[parent.1.val]? = some d.sources := by
    simpa only [hParentColumn] using hSource
  have hLength : F.length parent.1 = d.sources.size := by
    change p.reduced[parent.1.val].size = d.sources.size
    exact congrArg Array.size (Array.getElem?_eq_some_iff.mp hColumnRead).2
  have hNoUpper : ¬ parent.2.val + 1 < F.length parent.1 := by
    intro hBound
    change F.upper parent = none at hParentTop
    simp only [Frame.upper, hBound, ↓reduceDIte, reduceCtorEq] at hParentTop
  have hTopIndex : parent.2.val = d.sources.size - 1 := by
    have hIndex : parent.2.val < F.length parent.1 := parent.2.isLt
    omega
  have hTopRead : d.sources[d.sources.size - 1]? = some (F.cell parent) := by
    simpa only [hTopIndex] using hLowerRead
  have hNoBetween := d.prepared_no_markers_through_source_index hSource hRootColumn hRootBarrier
    hm hMarkerRow hLowerRead hParentInside.2.2
  have hHighest : ∀ other ∈ d.bucket, other.index ≤ marker.index := by
    intro other hOther
    by_contra hn
    have hIndex := (Array.getElem?_eq_some_iff.mp (d.marker_data other hOther).upper_at).1
    exact hNoBetween other.index (by omega) (by omega) (List.mem_map.mpr ⟨other, hOther, rfl⟩)
  have hNormal := build_normal_of_legal (build_success_legal p.reduced_build) p.reduced_build
  have hp : F.P child = some parent :=
    (Executable.findParent_ref_iff hNormal.toOrdered child parent).mp hParent
  have hQueryLow : Row.lift (d.marker_data marker hm).current.row
      (d.marker_data marker hm).targetCell.row (F.cell parent).row <
      Row.lift (F.height root) target (F.height childUpper) := by
    change Row.lift (d.marker_data marker hm).current.row
      (d.marker_data marker hm).targetCell.row (F.height parent) < _
    rw [hMarkerRow, hTargetEq, hChildRow, Row.lift_B hChild.2.1 hParentInside.2.1]
    exact (Row.lift_monotone hParentInside.2.1 (Frame.P_height_le hNormal.toOrdered hp)).trans_lt (Row.lt_B _ _)
  obtain ⟨actualParent, hBelow, _, hActual, hRow, _⟩ :=
    d.copyColumn_below_lifted_source_top hParentPower hParentLow
      (build_source_no_premature_one p.reduced_build hSource) hRun hm hHighest hTopRead hQueryLow
  exact ⟨column.size - 1, actualParent, hBelow, hActual,
    by simpa only [hMarkerRow, hTargetEq, Frame.height] using hRow⟩

/-- Complete strict-above-root parent selection. The parent may have its
upper inside the interval, at or above the cap, or have no upper at all.
The actual query ceiling is always derived rather than supplied. -/
theorem prepared_below_parent_above_root
    (hTargetCap : target < Row.bump ((Frame.ofMountain p.reduced).height root) degree) :
    ∃ (index : Nat) (actualParent : Cell),
      below (mountain.push column) mountain.size
        (Row.lift ((Frame.ofMountain p.reduced).height root) target
          ((Frame.ofMountain p.reduced).height childUpper)) = .ok ⟨mountain.size, index⟩ ∧
      Canonical.cellAt (mountain.push column) ⟨mountain.size, index⟩ = .ok actualParent ∧
      actualParent.row = Row.lift ((Frame.ofMountain p.reduced).height root) target
        ((Frame.ofMountain p.reduced).height parent) := by
  cases hParentUpper : (Frame.ofMountain p.reduced).upper parent with
  | none =>
    exact d.prepared_below_source_top_parent hSource hRootReal hDegree hRootColumn hRootIndex hRootBarrier
      hParent hChild hChildUpper hParentColumn hRight hTarget hParentPower hParentLow hRun hParentUpper
  | some parentUpper =>
    by_cases hCap : (Frame.ofMountain p.reduced).height parentUpper <
        Row.bump ((Frame.ofMountain p.reduced).height root) degree
    · exact d.prepared_below_internal_parent hSource hParentPower hParentLow hRootReal hDegree
        hRootColumn hRootIndex hRootBarrier hParent hChild hChildUpper hParentUpper hParentColumn hRight
        hParentAbove hCap hTarget hRun
    · exact d.prepared_below_cap_parent hSource hRootReal hDegree hRootColumn hRootIndex hRootBarrier
        hParent hChild hChildUpper hParentColumn hRight hTarget hParentPower hParentLow hParentAbove hRun
        hParentUpper (le_of_not_gt hCap) hTargetCap

end ParentInputs

end ColumnCopyData

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ColumnCopyData.prepared_parent_marker_data
#print axioms OmegaY.Expansion.ColumnCopyData.prepared_below_cap_parent
#print axioms OmegaY.Expansion.ColumnCopyData.prepared_below_source_top_parent
#print axioms OmegaY.Expansion.ColumnCopyData.prepared_below_parent_above_root
