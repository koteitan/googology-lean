/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/SegmentBounds.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/SegmentBounds.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.CopySegment
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ContourBound

set_option backward.do.legacy false

/-!
# Bounds on arbitrary actual segment results

The public decomposition keeps all three actual calls visible. Lower bounds
follow from their local row ranges. The next-marker upper bound uses the
actual contour theorem and determinism of execution, rather than assuming
that a segment stays in its intended interval.
-/

namespace OmegaY.Expansion

open Canonical

section Local

variable {mountain : Mountain} (hValid : MountainValid mountain)
  {sourceColumn shift rootColumn index : Nat} {sources : Column}
  (hSources : mountain[sourceColumn]? = some sources)
  (hSourcePositive : 0 < sourceColumn)
  (hDestination : sourceColumn + shift ≤ mountain.size) (hTop : TopOne sources)
  (references : List Ref) (markerIndices : List Nat)
  {current upper : Cell} (hCurrent : sources[index]? = some current)
  (hUpper : sources[index + 1]? = some upper) {sourceParent : Ref}
  (hLeft : upper.left = some sourceParent) {parentNodes : Column}
  (hParentNodes : mountain[sourceParent.column + shift]? = some parentNodes)
  {targetIndex : Nat} {targetCell : Cell}
  (hTarget : parentNodes[targetIndex]? = some targetCell)
  (hReference : referenceAt mountain references current.row = .ok targetCell.row)
  (hLow : current.row ≤ targetCell.row)

include hValid hSources hSourcePositive hDestination hTop hCurrent hUpper hLeft
  hParentNodes hTarget hReference hLow

/-- Every successful return is the marker, the actual contour, and the
actual filling, with their certified local ranges and internal no-duplicate
property. This applies to any claimed output of the executable helper. -/
theorem copySegment_result_decomposition {result : List Cell}
    (hRun : copySegment mountain sources references sourceColumn markerIndices
      shift rootColumn index = .ok result) :
    ∃ copied upperPath gap,
      result = [copied] ++ upperPath ++ gap ∧
      copyEdge mountain ⟨sourceColumn, index⟩ shift rootColumn current.row = .ok copied ∧
      copied.row = current.row ∧ copied.value = 0 ∧
      contour mountain sourceColumn markerIndices shift rootColumn index targetCell.row
        current (sources.toList.drop (index + 1)) = .ok upperPath ∧
      fill mountain ⟨sourceColumn, index + 1⟩ shift current.row targetCell.row = .ok gap ∧
      (result.map Cell.row).Nodup ∧
      (targetCell.row :: upperPath.map Cell.row).Pairwise (· < ·) ∧
      ∀ cell ∈ gap, current.row < cell.row ∧ cell.row ≤ targetCell.row := by
  obtain ⟨copied, upperPath, gap, hCopy, hCopyRow, hZero, hContour, hFill,
    hSegment, hNodup, hStrict, _, _, hGap⟩ :=
    copySegment_total_nodup hValid hSources hSourcePositive hDestination hTop
      references markerIndices hCurrent hUpper hLeft hParentNodes hTarget hReference hLow
      (rootColumn := rootColumn)
  have hResult : result = [copied] ++ upperPath ++ gap :=
    Except.ok.inj (hRun.symm.trans hSegment)
  refine ⟨copied, upperPath, gap, hResult, hCopy, hCopyRow, hZero, hContour, hFill,
    hResult ▸ hNodup, hStrict, ?_⟩
  intro cell hCell
  exact ⟨(hGap cell hCell).1, (hGap cell hCell).2.1⟩

/-- Each output lies at or above its marker, and that marker row actually
occurs. No power-step hypothesis is needed for this lower bound. -/
theorem copySegment_result_bounds {result : List Cell}
    (hRun : copySegment mountain sources references sourceColumn markerIndices
      shift rootColumn index = .ok result) :
    (result.map Cell.row).Nodup ∧ current.row ∈ result.map Cell.row ∧
      ∀ cell ∈ result, current.row ≤ cell.row := by
  obtain ⟨copied, upperPath, gap, hResult, _, hCopyRow, _, _, _, hNodup, hStrict, hGap⟩ :=
    copySegment_result_decomposition hValid hSources hSourcePositive hDestination hTop
      references markerIndices hCurrent hUpper hLeft hParentNodes hTarget hReference hLow hRun
  refine ⟨hNodup, ?_, ?_⟩
  · rw [hResult]
    exact List.mem_map.mpr ⟨copied, by simp, hCopyRow⟩
  · intro cell hCell
    rw [hResult] at hCell
    rcases List.mem_append.mp hCell with hFirst | hGapMem
    · rcases List.mem_append.mp hFirst with hCopyMem | hPathMem
      · have he : cell = copied := List.mem_singleton.mp hCopyMem
        rw [he, hCopyRow]
      · have hAbove : targetCell.row < cell.row :=
          (List.pairwise_cons.mp hStrict).1 cell.row (List.mem_map.mpr ⟨cell, hPathMem, rfl⟩)
        exact (hLow.trans_lt hAbove).le
    · exact (hGap cell hGapMem).1.le

/-- The strict source marker above the current index is not copied by the
contour. A target inside a source power interval therefore keeps every
piece of the actual segment strictly below that higher marker. -/
theorem copySegment_result_lt_next_marker {result : List Cell}
    (hRun : copySegment mountain sources references sourceColumn markerIndices
      shift rootColumn index = .ok result)
    (hPower : ColumnPowerSteps sources) {nextIndex : Nat} {nextMarker : Cell}
    (hNext : sources[nextIndex]? = some nextMarker) (hMarked : nextIndex ∈ markerIndices)
    (hIndex : index < nextIndex) {scale : Nat}
    (hTargetUpper : targetCell.row < Row.bump current.row scale)
    (hCap : Row.bump current.row scale ≤ nextMarker.row) :
    ∀ cell ∈ result, cell.row < nextMarker.row := by
  obtain ⟨copied, upperPath, gap, hResult, _, hCopyRow, _, hContour, _, _, _, hGap⟩ :=
    copySegment_result_decomposition hValid hSources hSourcePositive hDestination hTop
      references markerIndices hCurrent hUpper hLeft hParentNodes hTarget hReference hLow hRun
  obtain ⟨boundedPath, hBoundedRun, hBounded, _⟩ :=
    contour_total_below_next_marker hValid hSources hSourcePositive hDestination hTop
      hPower markerIndices targetCell.row hCurrent hNext hMarked hIndex rfl
      hLow hTargetUpper hCap (rootColumn := rootColumn)
  have hPathEq : upperPath = boundedPath := Except.ok.inj (hContour.symm.trans hBoundedRun)
  have hTargetBelow : targetCell.row < nextMarker.row := hTargetUpper.trans_le hCap
  intro cell hCell
  rw [hResult] at hCell
  rcases List.mem_append.mp hCell with hFirst | hGapMem
  · rcases List.mem_append.mp hFirst with hCopyMem | hPathMem
    · have he : cell = copied := List.mem_singleton.mp hCopyMem
      rw [he, hCopyRow]
      exact hLow.trans_lt hTargetBelow
    · exact hBounded cell (hPathEq ▸ hPathMem)
  · exact (hGap cell hGapMem).2.trans_lt hTargetBelow

end Local

end OmegaY.Expansion

#print axioms OmegaY.Expansion.copySegment_result_decomposition
#print axioms OmegaY.Expansion.copySegment_result_bounds
#print axioms OmegaY.Expansion.copySegment_result_lt_next_marker
