/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/InitialBaseRows.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/InitialBaseRows.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.InitialSegmentData
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.SegmentBounds

set_option backward.do.legacy false

/-! Actual occurrence of the phantom and real bottom among the first copied
column's candidates. The bottom is either copied as a marker or is the first
step of the zero-target phantom contour. -/

namespace OmegaY.Expansion

open Canonical

theorem contour_phantom_contains_one {mountain : Mountain} (hValid : MountainValid mountain)
    {sourceColumn shift rootColumn : Nat} {sources : Column}
    (hSources : mountain[sourceColumn]? = some sources) (hPositive : 0 < sourceColumn)
    (hDestination : sourceColumn + shift ≤ mountain.size) (hTop : TopOne sources)
    (markerIndices : List Nat) (hNotMarked : 1 ∉ markerIndices)
    {result : List Cell}
    (hRun : contour mountain sourceColumn markerIndices shift rootColumn 0 0 phantom
      (sources.toList.drop 1) = .ok result) : (1 : Row) ∈ result.map Cell.row := by
  obtain ⟨hc, hSourcesEq⟩ := Array.getElem?_eq_some_iff.mp hSources
  have hCV : ColumnValid mountain sourceColumn sources := hSourcesEq ▸ hValid sourceColumn hc
  have hSize := hCV.size_ge_two
  have hb : 1 < sources.size := by omega
  let bottom := sources[1]
  have hBottom : sources[1]? = some bottom := Array.getElem?_eq_getElem hb
  have hBottomRow := hCV.bottom_row bottom hBottom
  have hRest : sources.toList.drop 1 = bottom :: sources.toList.drop 2 := by
    have hh := List.drop_eq_getElem_cons (l := sources.toList) (i := 1) (by simpa using hb)
    change sources.toList.drop 1 = sources[1] :: sources.toList.drop 2 at hh
    exact hh
  obtain ⟨path, hPath, hRows, _⟩ := contour_total hValid hSources hPositive hDestination hTop
    markerIndices (0 : Row) hCV.phantom rfl (rootColumn := rootColumn)
  have he : path = result := Except.ok.inj (hPath.symm.trans hRun)
  subst path
  rw [hRows, hRest]
  have hStep : Row.bump (0 : Row) (Row.jump 0 1 - 1) = 1 := by
    rw [← zero_bump_zero, Row.jump_bump]
  simp only [contourExponents, phantom, Nat.zero_add, Nat.zero_ne_one, false_or,
    hNotMarked, ↓reduceIte, bumpTrace, hBottomRow, hStep]
  exact List.mem_cons_self

section Candidates

variable {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
  {references : List Ref}
  (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
  {sources : Column} (hSources : p.reduced[p.root.column + 1]? = some sources)
  (segments : Ref → List Cell)
  (hSegments : ∀ marker ∈ p.marked[p.root.column + 1]?.getD [],
    copySegment p.reduced sources references (p.root.column + 1)
      ((p.marked[p.root.column + 1]?.getD []).map Ref.index)
      (p.reduced.size - 1 - p.root.column) p.root.column marker.index = .ok (segments marker))

include hLast hMap hSources hSegments

theorem Preparation.initial_candidates_phantom :
    phantom ∈ (p.marked[p.root.column + 1]?.getD []).flatMap segments := by
  have hc := (Array.getElem?_eq_some_iff.mp hSources).1
  have hMarker := p.phantom_marker (Nat.lt_succ_self _) hc
  let marker : Ref := ⟨p.root.column + 1, 0⟩
  obtain ⟨d⟩ := p.first_segment_data hLast hMap hMarker
  have hSourceEq : d.sources = sources := Option.some.inj (d.source_column.symm.trans hSources)
  have hCurrentEq : d.current = phantom :=
    Option.some.inj (d.current_at.symm.trans d.source_valid.phantom)
  have hRun := hSegments marker hMarker
  rw [← hSourceEq] at hRun
  obtain ⟨copied, path, gap, hResult, hCopy, _, _, _, _, _, _, _⟩ :=
    copySegment_result_decomposition p.reduced_valid d.source_column (by omega) d.destination
      d.source_top references ((p.marked[p.root.column + 1]?.getD []).map Ref.index)
      d.current_at d.upper_at d.upper_left d.parent_nodes d.target_at d.reference d.target_lower hRun
  have hPhantomRead : lookup p.reduced ⟨p.root.column + 1, 0⟩ = .ok phantom := by
    apply lookup_ok_iff.mpr
    exact ⟨d.sources, d.source_column, d.source_valid.phantom⟩
  have hCopyPhantom : copied = phantom := by
    rw [hCurrentEq] at hCopy
    exact Except.ok.inj (hCopy.symm.trans (copyEdge_phantom hPhantomRead rfl _ _ 0))
  apply List.mem_flatMap.mpr
  exact ⟨marker, hMarker, by rw [hResult, hCopyPhantom]; simp⟩

theorem Preparation.initial_candidates_one :
    (1 : Row) ∈ ((p.marked[p.root.column + 1]?.getD []).flatMap segments).map Cell.row := by
  obtain ⟨hc, hSourcesEq⟩ := Array.getElem?_eq_some_iff.mp hSources
  have hCV : ColumnValid p.reduced (p.root.column + 1) sources :=
    hSourcesEq ▸ p.reduced_valid _ hc
  have hSize := hCV.size_ge_two
  have hb : 1 < sources.size := by omega
  let bottom := sources[1]
  let bottomRef : Ref := ⟨p.root.column + 1, 1⟩
  have hBottom : sources[1]? = some bottom := Array.getElem?_eq_getElem hb
  have hBottomRow := hCV.bottom_row bottom hBottom
  by_cases hBottomMarker : BucketMem p.marked (p.root.column + 1) bottomRef
  · obtain ⟨d⟩ := p.first_segment_data hLast hMap hBottomMarker
    have hSourceEq : d.sources = sources := Option.some.inj (d.source_column.symm.trans hSources)
    have hCurrentEq : d.current = bottom := by
      have hRead := d.current_at
      rw [hSourceEq] at hRead
      exact Option.some.inj (hRead.symm.trans hBottom)
    have hRun := hSegments bottomRef hBottomMarker
    rw [← hSourceEq] at hRun
    obtain ⟨_, hMember, _⟩ := copySegment_result_bounds p.reduced_valid d.source_column (by omega)
      d.destination d.source_top references ((p.marked[p.root.column + 1]?.getD []).map Ref.index)
      d.current_at d.upper_at d.upper_left d.parent_nodes d.target_at d.reference d.target_lower hRun
    obtain ⟨cell, hCell, hRow⟩ := List.mem_map.mp hMember
    exact List.mem_map.mpr ⟨cell, List.mem_flatMap.mpr ⟨bottomRef, hBottomMarker, hCell⟩,
      hRow.trans ((congrArg Cell.row hCurrentEq).trans hBottomRow)⟩
  · have hNotMarked : 1 ∉ (p.marked[p.root.column + 1]?.getD []).map Ref.index := by
      intro hm
      obtain ⟨entry, hEntry, hIndex⟩ := List.mem_map.mp hm
      have hColumn := (p.marker_iff.mp hEntry).1
      have he : entry = bottomRef := by
        cases entry
        simp_all only [bottomRef]
      exact hBottomMarker (he ▸ hEntry)
    have hMarker := p.phantom_marker (Nat.lt_succ_self _) hc
    let marker : Ref := ⟨p.root.column + 1, 0⟩
    obtain ⟨d⟩ := p.first_segment_data hLast hMap hMarker
    have hSourceEq : d.sources = sources := Option.some.inj (d.source_column.symm.trans hSources)
    have hCurrentEq : d.current = phantom :=
      Option.some.inj (d.current_at.symm.trans d.source_valid.phantom)
    have hZero : d.targetCell.row = 0 := d.target_zero hLast hMap (congrArg Cell.row hCurrentEq)
    have hRun := hSegments marker hMarker
    rw [← hSourceEq] at hRun
    obtain ⟨copied, path, gap, hResult, _, _, _, hContour, _, _, _, _⟩ :=
      copySegment_result_decomposition p.reduced_valid d.source_column (by omega) d.destination
        d.source_top references ((p.marked[p.root.column + 1]?.getD []).map Ref.index)
        d.current_at d.upper_at d.upper_left d.parent_nodes d.target_at d.reference d.target_lower hRun
    rw [hCurrentEq, hZero] at hContour
    have hOne := contour_phantom_contains_one p.reduced_valid d.source_column (by omega)
      d.destination d.source_top ((p.marked[p.root.column + 1]?.getD []).map Ref.index) hNotMarked hContour
    obtain ⟨cell, hCell, hRow⟩ := List.mem_map.mp hOne
    apply List.mem_map.mpr
    refine ⟨cell, List.mem_flatMap.mpr ⟨marker, hMarker, ?_⟩, hRow⟩
    rw [hResult]
    simp [hCell]

end Candidates

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.initial_candidates_phantom
#print axioms OmegaY.Expansion.Preparation.initial_candidates_one
