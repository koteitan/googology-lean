/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/InitialSegment.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/InitialSegment.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.CopySegment
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.RootReferenceAt
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.PreparedMarkers

set_option backward.do.legacy false

/-!
# Actual marker segments of the first copied column

In the first source column to the right of the root, the upper edge of an
actual marker must point into the root column itself. Its shifted parent
column is therefore the existing decremented final column. The actual
selected target is already present in precisely that column: no target-
support premise is supplied by the caller.

These theorems concern individual actual marker segments. They do not yet
concatenate all segments, establish cross-segment separation, or run finish.
-/

namespace OmegaY.Expansion

open Canonical

/-- No earlier marker column fits strictly between the root and its immediate
right neighbor, so the actual weak parent lies in the root column. -/
theorem Preparation.first_marker_upper_parent {front : List Nat} {last : Nat}
    (p : Preparation front last) {marker : Ref}
    (hMarker : BucketMem p.marked (p.root.column + 1) marker) :
    ∃ current upper parent parentCell,
      marker.column = p.root.column + 1 ∧
      CellAt p.reduced marker current ∧
      CellAt p.reduced ⟨marker.column, marker.index + 1⟩ upper ∧
      upper.left = some parent ∧ parent.column = p.root.column ∧
      CellAt p.reduced parent parentCell ∧ parentCell.row = current.row := by
  have hSpec := p.marker_iff.mp hMarker
  obtain ⟨rootIndex, parent, current, upper, parentCell,
    _hIndex, hCurrent, hUpper, hLeft, hLeftward, hParent, hRow, hCase⟩ :=
    markers_upper_parent
      (weakLocal_of_ordered p.reduced_valid.toOrdered p.reduced_valid.left_sources)
      p.root_valid p.markers_built hMarker
  have hParentColumn : parent.column = p.root.column := by
    rcases hCase with hRoot | hEarlier
    · simpa only using congrArg Ref.column hRoot
    · have hParentSpec := p.marker_iff.mp hEarlier
      have hSourceColumn := hSpec.1
      have hParentRight := hParentSpec.2.1
      omega
  exact ⟨current, upper, parent, parentCell, hSpec.1,
    hCurrent, hUpper, hLeft, hParentColumn, hParent, hRow⟩

/-- Every actual marker of the first source column produces a successful,
internally non-overlapping segment at the first actual copy shift. -/
theorem Preparation.initial_segment_total_nodup {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {references : List Ref}
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
    {marker : Ref} (hMarker : BucketMem p.marked (p.root.column + 1) marker) :
    ∃ sources result,
      p.reduced[p.root.column + 1]? = some sources ∧
      copySegment p.reduced sources references (p.root.column + 1)
        ((p.marked[p.root.column + 1]?.getD []).map Ref.index)
        (p.reduced.size - 1 - p.root.column) p.root.column marker.index = .ok result ∧
      (result.map Cell.row).Nodup := by
  obtain ⟨current, upper, sourceParent, parentCell, hMarkerColumn, hCurrent,
    hUpper, hLeft, hParentColumn, _hParent, _hParentRow⟩ :=
    p.first_marker_upper_parent hMarker
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
  obtain ⟨ceiling, degree, targetRef, targetCell, _hPower, _hTop,
    hBelow, hTargetRead, hReference, hLow, _hTargetUpper, _hHigher⟩ :=
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
  have hDestination : p.root.column + 1 + (p.reduced.size - 1 - p.root.column) ≤
      p.reduced.size := by omega
  have hReferenceCurrent : referenceAt p.reduced references current.row = .ok targetCell.row := by
    simpa only [hLowerRow] using hReference
  have hLowCurrent : current.row ≤ targetCell.row := by
    simpa only [hLowerRow] using hLow
  obtain ⟨built, hBuilt, _hValid, hTops⟩ := build_total (build_success_legal p.reduced_build)
  have hBuiltEq : built = p.reduced := Except.ok.inj (hBuilt.symm.trans p.reduced_build)
  subst built
  obtain ⟨hc, hSourcesEq⟩ := Array.getElem?_eq_some_iff.mp hSourceColumn
  have hTop : TopOne sources := hSourcesEq ▸ hTops (p.root.column + 1) hc
  obtain ⟨copied, upperPath, gap, _hCopy, _hCopyRow, _hZero, _hContour,
    _hFill, hSegment, hNodup, _hContourStrict, _hContourParents, _hGapNodup, _hGapSpec⟩ :=
    copySegment_total_nodup p.reduced_valid hSourceColumn (by omega) hDestination hTop
      references ((p.marked[p.root.column + 1]?.getD []).map Ref.index)
      hCurrentIndex hUpperIndex hLeft hShiftedParent hTargetIndex hReferenceCurrent hLowCurrent
      (rootColumn := p.root.column)
  exact ⟨sources, [copied] ++ upperPath ++ gap, hSourceColumn, hSegment, hNodup⟩

/-- The actual boundary map is also supplied by preparation; callers need
only give a nontrivial prepared input and choose its enumerated markers. -/
theorem Preparation.initial_segments_total_nodup {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) :
    ∃ references,
      p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references ∧
      ∀ marker, BucketMem p.marked (p.root.column + 1) marker →
        ∃ sources result, p.reduced[p.root.column + 1]? = some sources ∧
          copySegment p.reduced sources references (p.root.column + 1)
            ((p.marked[p.root.column + 1]?.getD []).map Ref.index)
            (p.reduced.size - 1 - p.root.column) p.root.column marker.index = .ok result ∧
          (result.map Cell.row).Nodup := by
  obtain ⟨references, hMap, _hPaired⟩ := p.initial_references hLast
  exact ⟨references, hMap, fun _ hMarker => p.initial_segment_total_nodup hLast hMap hMarker⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.initial_segment_total_nodup
#print axioms OmegaY.Expansion.Preparation.initial_segments_total_nodup
