/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/InitialSegmentData.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/InitialSegmentData.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.InitialSegment
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.PreparedPhantom

set_option backward.do.legacy false

/-! Actual reusable input data for a marker of the first copied column.
The target lies in the particular shifted parent column required by fill.
These fields are derived from preparation, not assumed copying invariants. -/

namespace OmegaY.Expansion

open Canonical

structure FirstSegmentData {front : List Nat} {last : Nat}
    (p : Preparation front last) (references : List Ref) (marker : Ref) where
  sources : Column
  current : Cell
  upper : Cell
  sourceParent : Ref
  parentNodes : Column
  targetIndex : Nat
  targetCell : Cell
  marker_column : marker.column = p.root.column + 1
  source_column : p.reduced[p.root.column + 1]? = some sources
  current_at : sources[marker.index]? = some current
  upper_at : sources[marker.index + 1]? = some upper
  upper_left : upper.left = some sourceParent
  parent_column : sourceParent.column = p.root.column
  parent_nodes : p.reduced[sourceParent.column + (p.reduced.size - 1 - p.root.column)]? = some parentNodes
  target_at : parentNodes[targetIndex]? = some targetCell
  reference : referenceAt p.reduced references current.row = .ok targetCell.row
  target_lower : current.row ≤ targetCell.row
  source_top : TopOne sources
  destination : p.root.column + 1 + (p.reduced.size - 1 - p.root.column) ≤ p.reduced.size

theorem FirstSegmentData.current_read {front : List Nat} {last : Nat}
    {p : Preparation front last} {references : List Ref} {marker : Ref}
    (d : FirstSegmentData p references marker) :
    Canonical.cellAt p.reduced marker = .ok d.current :=
  cellAt_ok_iff.mpr ⟨d.sources, by simpa only [d.marker_column] using d.source_column, d.current_at⟩

theorem FirstSegmentData.source_valid {front : List Nat} {last : Nat}
    {p : Preparation front last} {references : List Ref} {marker : Ref}
    (d : FirstSegmentData p references marker) :
    ColumnValid p.reduced (p.root.column + 1) d.sources := by
  obtain ⟨hc, hSources⟩ := Array.getElem?_eq_some_iff.mp d.source_column
  exact hSources ▸ p.reduced_valid _ hc

theorem FirstSegmentData.target_zero {front : List Nat} {last : Nat}
    {p : Preparation front last} {references : List Ref} {marker : Ref}
    (d : FirstSegmentData p references marker) (hLast : 1 < last)
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
    (hZero : d.current.row = 0) : d.targetCell.row = 0 := by
  have hReference := d.reference
  rw [hZero] at hReference
  exact Except.ok.inj (hReference.symm.trans (p.initial_referenceAt_zero hLast hMap))

theorem Preparation.first_segment_data {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {references : List Ref}
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
    {marker : Ref} (hMarker : BucketMem p.marked (p.root.column + 1) marker) :
    Nonempty (FirstSegmentData p references marker) := by
  obtain ⟨current, upper, sourceParent, parentCell, hMarkerColumn, hCurrent,
    hUpper, hLeft, hParentColumn, _, _⟩ := p.first_marker_upper_parent hMarker
  obtain ⟨sources, hSources, hCurrentIndex⟩ := hCurrent
  have hSourceColumn : p.reduced[p.root.column + 1]? = some sources := by
    simpa only [hMarkerColumn] using hSources
  obtain ⟨otherSources, hOtherSources, hUpperIndex⟩ := hUpper
  have he : otherSources = sources := Option.some.inj (hOtherSources.symm.trans hSources)
  subst otherSources
  have hCurrentRead : Canonical.cellAt p.reduced marker = .ok current :=
    cellAt_ok_iff.mpr ⟨sources, hSources, hCurrentIndex⟩
  obtain ⟨rootNodes, index, lower, hRootColumn, hLower, hRootIndex, hLowerRow⟩ :=
    p.marker_root_prefix_read hMarker hCurrentRead
  obtain ⟨_, _, targetRef, targetCell, _, _, hBelow, hTargetRead, hReference, hLow, _, _⟩ :=
    p.initial_referenceAt_root_interval hLast hRootColumn hLower hRootIndex hMap
  have hTargetColumn : targetRef.column = p.reduced.size - 1 :=
    (below_result (Array.getElem?_eq_getElem p.reduced_last_exists) hBelow).1
  obtain ⟨parentNodes, hParentNodes, hTargetIndex⟩ := cellAt_ok_iff.mp hTargetRead
  have hSize := build_size p.reduced_build
  simp only [List.length_append, List.length_singleton] at hSize
  have hRootLeft := p.root_before_last
  have hShift : sourceParent.column + (p.reduced.size - 1 - p.root.column) =
      p.reduced.size - 1 := by omega
  have hShiftedParent : p.reduced[sourceParent.column +
      (p.reduced.size - 1 - p.root.column)]? = some parentNodes := by
    simpa only [hTargetColumn, hShift] using hParentNodes
  obtain ⟨built, hBuilt, _, hTops⟩ := build_total (build_success_legal p.reduced_build)
  have hBuiltEq : built = p.reduced := Except.ok.inj (hBuilt.symm.trans p.reduced_build)
  subst built
  obtain ⟨hc, hSourcesEq⟩ := Array.getElem?_eq_some_iff.mp hSourceColumn
  exact ⟨{
    sources := sources
    current := current
    upper := upper
    sourceParent := sourceParent
    parentNodes := parentNodes
    targetIndex := targetRef.index
    targetCell := targetCell
    marker_column := hMarkerColumn
    source_column := hSourceColumn
    current_at := hCurrentIndex
    upper_at := hUpperIndex
    upper_left := hLeft
    parent_column := hParentColumn
    parent_nodes := hShiftedParent
    target_at := hTargetIndex
    reference := by simpa only [hLowerRow] using hReference
    target_lower := by simpa only [hLowerRow] using hLow
    source_top := hSourcesEq ▸ hTops (p.root.column + 1) hc
    destination := by omega }⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.first_segment_data
