/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/SegmentPositive.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/SegmentPositive.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ContourFrozen
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.SegmentBounds
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.FillEndpoints
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.FinishGeometry

set_option backward.do.legacy false

/-! Positive numerical parents in a full copied segment, using only local
source facts and a valid ambient mountain. No normality or power steps are
assumed of the target parent column or of generated output. -/

namespace OmegaY.Expansion

open Canonical

theorem ColumnValid.row_zero_of_index_zero {mountain : Mountain} {sourceColumn : Nat}
    {sources : Column} (hValid : ColumnValid mountain sourceColumn sources)
    {index : Nat} {current : Cell} (hCurrent : sources[index]? = some current)
    (hZero : index = 0) : current.row = 0 := by
  have hRead : sources[0]? = some current := by simpa only [hZero] using hCurrent
  have he : current = phantom := Option.some.inj (hRead.symm.trans hValid.phantom)
  rw [he]
  rfl

theorem ColumnValid.index_above_one_of_row {mountain : Mountain} {sourceColumn : Nat}
    {sources : Column} (hValid : ColumnValid mountain sourceColumn sources)
    {index : Nat} {current : Cell} (hCurrent : sources[index]? = some current)
    (hAbove : (1 : Row) < current.row) : 1 < index := by
  by_contra h
  by_cases hZero : index = 0
  · rw [ColumnValid.row_zero_of_index_zero hValid hCurrent hZero] at hAbove
    exact (not_lt_of_ge (Row.zero_le 1)) hAbove
  · have hOne : index = 1 := by omega
    have hRow : current.row = 1 := hValid.bottom_row current
      (by simpa only [hOne] using hCurrent)
    rw [hRow] at hAbove
    exact (lt_irrefl (1 : Row)) hAbove

section Local

variable {mountain : Mountain} (hValid : MountainValid mountain)
  {sourceColumn shift rootColumn index : Nat} {sources : Column}
  (hSources : mountain[sourceColumn]? = some sources)
  (hSourcePositive : 0 < sourceColumn)
  (hDestination : sourceColumn + shift ≤ mountain.size) (hTop : TopOne sources)
  (hPower : ColumnPowerSteps sources) (hPositive : SourceAboveBottomPositive mountain sources)
  (references : List Ref) (markerIndices : List Nat)
  {current upper : Cell} (hCurrent : sources[index]? = some current)
  (hUpper : sources[index + 1]? = some upper) {sourceParent : Ref}
  (hLeft : upper.left = some sourceParent) {parentNodes : Column}
  (hParentNodes : mountain[sourceParent.column + shift]? = some parentNodes)
  {targetIndex : Nat} {targetCell : Cell}
  (hTarget : parentNodes[targetIndex]? = some targetCell)
  (hReference : referenceAt mountain references current.row = .ok targetCell.row)
  (hLow : current.row ≤ targetCell.row)
  (hAuxiliary : current.row = 0 → targetCell.row = 0)

include hValid hSources hSourcePositive hDestination hTop hPower hPositive hCurrent hUpper
  hLeft hParentNodes hTarget hReference hLow hAuxiliary

/-- The marker, contour and filler all retain readable positive parents
whenever their output row is above one. -/
theorem copySegment_positive_of_source {result : List Cell}
    (hRun : copySegment mountain sources references sourceColumn markerIndices
      shift rootColumn index = .ok result) :
    ∀ cell ∈ result, (1 : Row) < cell.row →
      ∃ parent parentCell, cell.left = some parent ∧ lookup mountain parent = .ok parentCell ∧
        0 < parentCell.value := by
  obtain ⟨hc, hNodes⟩ := Array.getElem?_eq_some_iff.mp hSources
  have hSourceValid : ColumnValid mountain sourceColumn sources := hNodes ▸ hValid sourceColumn hc
  obtain ⟨copied, upperPath, gap, hResult, hCopy, hCopyRow, _hZero, hContour,
    hFill, _hNodup, _hStrict, hGapBounds⟩ := copySegment_result_decomposition
      hValid hSources hSourcePositive hDestination hTop references markerIndices
      hCurrent hUpper hLeft hParentNodes hTarget hReference hLow hRun
  have hCurrentRead : lookup mountain ⟨sourceColumn, index⟩ = .ok current :=
    lookup_ok_iff.mpr ⟨sources, hSources, hCurrent⟩
  have hUpperRead : lookup mountain ⟨sourceColumn, index + 1⟩ = .ok upper :=
    lookup_ok_iff.mpr ⟨sources, hSources, hUpper⟩
  have hZeroTarget : index = 0 → targetCell.row = 0 := by
    intro hi
    exact hAuxiliary (ColumnValid.row_zero_of_index_zero hSourceValid hCurrent hi)
  have hPathPositive := contour_positive_of_source hValid hSources hSourcePositive
    hDestination hPower hPositive markerIndices targetCell.row hCurrent rfl hLow
    hZeroTarget hContour
  intro cell hCell hAbove
  rw [hResult] at hCell
  rcases List.mem_append.mp hCell with hFirst | hGap
  · rcases List.mem_append.mp hFirst with hMarker | hPath
    · have hCellEq : cell = copied := List.mem_singleton.mp hMarker
      subst cell
      have hCurrentAbove : (1 : Row) < current.row := by simpa only [hCopyRow] using hAbove
      have hIndex := ColumnValid.index_above_one_of_row hSourceValid hCurrent hCurrentAbove
      obtain ⟨oldParent, oldParentCell, hOldLeft, hOldRead, hOldPositive⟩ :=
        hPositive index current hCurrent hIndex
      obtain ⟨positiveCopy, parent, parentCell, hPositiveCopy, _hRow, _hValue,
        hCopiedLeft, hParent, _hParentColumn, hParentPositive⟩ :=
        copyEdge_positive_parent hValid hCurrentRead hSourcePositive hDestination
          (ne_of_gt (Row.zero_lt_one.trans hCurrentAbove)) hCurrentAbove hOldLeft
          hOldRead hOldPositive (rootColumn := rootColumn)
      have he : positiveCopy = copied := Except.ok.inj (hPositiveCopy.symm.trans hCopy)
      subst positiveCopy
      exact ⟨parent, parentCell, hCopiedLeft, hParent, hParentPositive⟩
    · obtain ⟨parent, parentCell, hCopiedLeft, hParent, hParentPositive, _⟩ :=
        hPathPositive cell hPath hAbove
      exact ⟨parent, parentCell, hCopiedLeft, hParent, hParentPositive⟩
  · by_cases hZero : current.row = 0
    · have hTargetZero := hAuxiliary hZero
      obtain ⟨hGapLow, hGapHigh⟩ := hGapBounds cell hGap
      rw [hZero] at hGapLow
      rw [hTargetZero] at hGapHigh
      exact False.elim ((not_lt_of_ge hGapHigh) hGapLow)
    · obtain ⟨hp, hParents⟩ := Array.getElem?_eq_some_iff.mp hParentNodes
      have hParentValid : ColumnValid mountain (sourceParent.column + shift) parentNodes :=
        hParents ▸ hValid _ hp
      have hLeftward : sourceParent.column < sourceColumn :=
        (hSourceValid.stored_valid _ _ _ hUpper hLeft).1
      obtain ⟨positiveGap, hPositiveGap, hGapPositive⟩ :=
        fill_with_positive_parents hUpperRead hLeft hParentNodes hParentValid hTarget le_rfl
          (row_one_le_of_ne_zero hZero) hLeftward (high := targetCell.row)
      have he : positiveGap = gap := Except.ok.inj (hPositiveGap.symm.trans hFill)
      subst positiveGap
      obtain ⟨parent, parentCell, hCopiedLeft, hParent, _hIndex, hParentPositive⟩ :=
        hGapPositive cell hGap
      exact ⟨parent, parentCell, hCopiedLeft, hParent, hParentPositive⟩

/-- Actual segment success and internal row uniqueness are derived together
with numerical parent positivity; no successful run is an input premise. -/
theorem copySegment_total_positive_of_source :
    ∃ result,
      copySegment mountain sources references sourceColumn markerIndices
        shift rootColumn index = .ok result ∧
      (result.map Cell.row).Nodup ∧
      ∀ cell ∈ result, (1 : Row) < cell.row →
        ∃ parent parentCell, cell.left = some parent ∧ lookup mountain parent = .ok parentCell ∧
          0 < parentCell.value := by
  obtain ⟨copied, upperPath, gap, _hCopy, _hCopyRow, _hZero, _hContour, _hFill,
    hSegment, hNodup, _⟩ := copySegment_total_nodup hValid hSources hSourcePositive
      hDestination hTop references markerIndices hCurrent hUpper hLeft hParentNodes
      hTarget hReference hLow (rootColumn := rootColumn)
  exact ⟨[copied] ++ upperPath ++ gap, hSegment, hNodup,
    copySegment_positive_of_source hValid hSources hSourcePositive hDestination hTop
      hPower hPositive references markerIndices hCurrent hUpper hLeft hParentNodes
      hTarget hReference hLow hAuxiliary hSegment⟩

end Local

end OmegaY.Expansion

#print axioms OmegaY.Expansion.copySegment_positive_of_source
#print axioms OmegaY.Expansion.copySegment_total_positive_of_source
