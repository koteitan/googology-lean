/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/InitialCandidateLegs.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/InitialCandidateLegs.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.InitialSegmentData
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.SegmentBounds
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ContourParentRows

set_option backward.do.legacy false

/-!
# Stored-leg certificates for the actual first-column candidates

All nonzero-row candidates have a stored left endpoint. Every stored
endpoint, including any endpoint presented by the caller, is an actual
earlier node no higher than its child. Phantom markers have no endpoint.
No canonicality or validity of the unfinished candidate column is assumed.
-/

namespace OmegaY.Expansion

open Canonical

def CellLegs (mountain : Mountain) (destination : Nat) (cell : Cell) : Prop :=
  (cell.row ≠ 0 → ∃ parent, cell.left = some parent) ∧
  ∀ parent, cell.left = some parent → ∃ parentCell,
    lookup mountain parent = .ok parentCell ∧ parent.column < destination ∧
    parentCell.row ≤ cell.row

theorem CellLegs.of_parent {mountain : Mountain} {destination : Nat} {cell parentCell : Cell}
    {parent : Ref} (hLeft : cell.left = some parent)
    (hRead : lookup mountain parent = .ok parentCell) (hColumn : parent.column < destination)
    (hRow : parentCell.row ≤ cell.row) : CellLegs mountain destination cell := by
  constructor
  · intro _
    exact ⟨parent, hLeft⟩
  · intro other hOther
    have he : other = parent := Option.some.inj (hOther.symm.trans hLeft)
    subst other
    exact ⟨parentCell, hRead, hColumn, hRow⟩

theorem CellLegs.of_zero_none {mountain : Mountain} {destination : Nat} {cell : Cell}
    (hZero : cell.row = 0) (hNone : cell.left = none) : CellLegs mountain destination cell := by
  constructor
  · intro hn
    exact False.elim (hn hZero)
  · intro parent hParent
    rw [hNone] at hParent
    cases hParent

/-- Copying a marker at its own row preserves the stored-leg row bound;
the auxiliary marker instead has no stored endpoint. -/
theorem copyEdge_same_row_legs {mountain : Mountain} (hValid : MountainValid mountain)
    {source : Ref} {sourceCell copied : Cell}
    (hSource : lookup mountain source = .ok sourceCell) (hSourcePositive : 0 < source.column)
    {shift rootColumn : Nat} (hDestination : source.column + shift ≤ mountain.size)
    (hRun : copyEdge mountain source shift rootColumn sourceCell.row = .ok copied) :
    CellLegs mountain (source.column + shift) copied := by
  by_cases hZero : sourceCell.row = 0
  · have hPhantom := copyEdge_phantom hSource hZero shift rootColumn sourceCell.row
    have he : copied = ⟨sourceCell.row, 0, none⟩ := Except.ok.inj (hRun.symm.trans hPhantom)
    apply CellLegs.of_zero_none
    · simpa only [he] using hZero
    · rw [he]
  · have hPositive : 0 < sourceCell.row := lt_of_le_of_ne (Row.zero_le _) (Ne.symm hZero)
    obtain ⟨other, parent, parentCell, hOther, _, _, hLeft, hRead, hColumn, hRow⟩ :=
      copyEdge_nonphantom_row_bound hValid hSource hSourcePositive hDestination hZero
        hPositive le_rfl (rootColumn := rootColumn)
    have he : other = copied := Except.ok.inj (hOther.symm.trans hRun)
    subst other
    exact CellLegs.of_parent hLeft hRead hColumn hRow

/-- The input data was derived from actual preparation. Marker, contour,
and gap executions are aligned with the supplied successful result by
determinism before their parent certificates are combined. -/
theorem FirstSegmentData.result_legs {front : List Nat} {last : Nat}
    {p : Preparation front last} {references : List Ref} {marker : Ref}
    (d : FirstSegmentData p references marker) {result : List Cell}
    (hRun : copySegment p.reduced d.sources references (p.root.column + 1)
      ((p.marked[p.root.column + 1]?.getD []).map Ref.index)
      (p.reduced.size - 1 - p.root.column) p.root.column marker.index = .ok result) :
    ∀ cell ∈ result, CellLegs p.reduced p.reduced.size cell := by
  have hSize := build_size p.reduced_build
  simp only [List.length_append, List.length_singleton] at hSize
  have hRootLeft := p.root_before_last
  have hDestination : p.root.column + 1 + (p.reduced.size - 1 - p.root.column) = p.reduced.size := by
    omega
  obtain ⟨copied, upperPath, gap, hResult, hCopy, _, _, hContour, hFill, _, _, _⟩ :=
    copySegment_result_decomposition p.reduced_valid d.source_column (by omega)
      d.destination d.source_top references ((p.marked[p.root.column + 1]?.getD []).map Ref.index)
      d.current_at d.upper_at d.upper_left d.parent_nodes d.target_at d.reference d.target_lower hRun
  have hCurrentRead : lookup p.reduced ⟨p.root.column + 1, marker.index⟩ = .ok d.current :=
    lookup_ok_iff.mpr ⟨d.sources, d.source_column, d.current_at⟩
  have hCopiedLegs : CellLegs p.reduced p.reduced.size copied := by
    simpa only [hDestination] using
      copyEdge_same_row_legs p.reduced_valid hCurrentRead (Nat.zero_lt_succ p.root.column)
        d.destination hCopy
  have hContourParents := contour_parent_rows_of_success p.reduced_valid d.source_column (by omega)
    d.destination (build_column_power_steps_of_read p.reduced_build d.source_column)
    ((p.marked[p.root.column + 1]?.getD []).map Ref.index) d.targetCell.row d.current_at rfl
    d.target_lower hContour
  have hUpperRead : lookup p.reduced ⟨p.root.column + 1, marker.index + 1⟩ = .ok d.upper :=
    lookup_ok_iff.mpr ⟨d.sources, d.source_column, d.upper_at⟩
  obtain ⟨hp, hParentNodes⟩ := Array.getElem?_eq_some_iff.mp d.parent_nodes
  have hParentValid : ColumnValid p.reduced
      (d.sourceParent.column + (p.reduced.size - 1 - p.root.column)) d.parentNodes :=
    hParentNodes ▸ p.reduced_valid _ hp
  have hParentLeft : d.sourceParent.column < p.root.column + 1 := by
    rw [d.parent_column]
    omega
  obtain ⟨certifiedGap, hCertified, _, _, hGapParents⟩ :=
    fill_spec_of_valid_column hUpperRead d.upper_left d.parent_nodes hParentValid d.target_at
      hParentLeft (low := d.current.row)
  have hGapEq : certifiedGap = gap := Except.ok.inj (hCertified.symm.trans hFill)
  rw [hGapEq] at hGapParents
  intro cell hCell
  rw [hResult] at hCell
  rcases List.mem_append.mp hCell with hFirst | hGapMem
  · rcases List.mem_append.mp hFirst with hCopyMem | hContourMem
    · have he : cell = copied := List.mem_singleton.mp hCopyMem
      exact he ▸ hCopiedLegs
    · obtain ⟨parent, parentCell, hLeft, hRead, hColumn, hRow⟩ := hContourParents cell hContourMem
      exact CellLegs.of_parent hLeft hRead (by simpa only [hDestination] using hColumn) hRow
  · obtain ⟨_, _, _, parent, parentCell, hLeft, hRead, hColumn, hRow⟩ := hGapParents cell hGapMem
    exact CellLegs.of_parent hLeft hRead (by simpa only [hDestination] using hColumn) hRow.le

/-- Initial actual marker membership supplies all local data needed for
the leg certificate; no auxiliary copied-column invariant is an input. -/
theorem Preparation.initial_segment_legs {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {references : List Ref}
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
    {sources : Column} (hSources : p.reduced[p.root.column + 1]? = some sources)
    {marker : Ref} (hMarker : BucketMem p.marked (p.root.column + 1) marker)
    {result : List Cell}
    (hRun : copySegment p.reduced sources references (p.root.column + 1)
      ((p.marked[p.root.column + 1]?.getD []).map Ref.index)
      (p.reduced.size - 1 - p.root.column) p.root.column marker.index = .ok result) :
    ∀ cell ∈ result, CellLegs p.reduced p.reduced.size cell := by
  obtain ⟨d⟩ := p.first_segment_data hLast hMap hMarker
  have hSourcesEq : d.sources = sources := Option.some.inj (d.source_column.symm.trans hSources)
  apply d.result_legs
  simpa only [hSourcesEq] using hRun

/-- The exact candidate concatenation used by the original first-column
loop has all stored-leg certificates required before and after finishing. -/
theorem Preparation.initial_candidate_legs {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {references : List Ref}
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
    {sources : Column} (hSources : p.reduced[p.root.column + 1]? = some sources)
    (segments : Ref → List Cell)
    (hSegments : ∀ marker ∈ p.marked[p.root.column + 1]?.getD [],
      copySegment p.reduced sources references (p.root.column + 1)
        ((p.marked[p.root.column + 1]?.getD []).map Ref.index)
        (p.reduced.size - 1 - p.root.column) p.root.column marker.index = .ok (segments marker)) :
    ∀ cell ∈ (p.marked[p.root.column + 1]?.getD []).flatMap segments,
      CellLegs p.reduced p.reduced.size cell := by
  intro cell hCell
  obtain ⟨marker, hMarker, hCell⟩ := List.mem_flatMap.mp hCell
  exact p.initial_segment_legs hLast hMap hSources hMarker (hSegments marker hMarker) cell hCell

end OmegaY.Expansion

#print axioms OmegaY.Expansion.copyEdge_same_row_legs
#print axioms OmegaY.Expansion.FirstSegmentData.result_legs
#print axioms OmegaY.Expansion.Preparation.initial_candidate_legs
