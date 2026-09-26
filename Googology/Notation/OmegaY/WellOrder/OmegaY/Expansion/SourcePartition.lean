/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/SourcePartition.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/SourcePartition.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ColumnCopyData
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.SourceStopping

set_option backward.do.legacy false

/-!
# Every actual source node belongs to a marker segment

Choose the greatest marker index at or below the requested source index.
The phantom ensures this finite choice is nonempty. No intervening marker
and no premature value-one node can stop its source contour before the
requested node. This is an input-source theorem; no copied execution or
new-column normality is assumed.
-/

namespace OmegaY.Expansion

open Canonical

private theorem partition_suffix_cons {nodes : Column} {index : Nat} {upper : Cell}
    {rest : List Cell} (hRest : nodes.toList.drop (index + 1) = upper :: rest) :
    nodes[index + 1]? = some upper ∧ nodes.toList.drop ((index + 1) + 1) = rest := by
  constructor
  · simpa only [List.head?_drop, Array.getElem?_toList, List.head?_cons]
      using congrArg List.head? hRest
  · simpa only [List.tail_drop, List.tail_cons] using congrArg List.tail hRest

/-- Inclusive exclusion at sourceIndex is essential: when that index is
itself marked, the algorithm stops before inserting it in a lower contour. -/
theorem mem_contourSourceCells_of_no_between {nodes : Column}
    (hNoPremature : NoPrematureOne nodes) (markerIndices : List Nat)
    {index sourceIndex : Nat} {current sourceCell : Cell}
    (hCurrent : nodes[index]? = some current) (hSource : nodes[sourceIndex]? = some sourceCell)
    (hIndex : index < sourceIndex)
    (hNoBetween : ∀ middle, index < middle → middle ≤ sourceIndex → middle ∉ markerIndices)
    {rest : List Cell} (hRest : nodes.toList.drop (index + 1) = rest) :
    sourceCell ∈ contourSourceCells markerIndices index current rest := by
  induction rest generalizing index current with
  | nil =>
    have hSize : nodes.size ≤ index + 1 := by
      simpa only [Array.length_toList] using List.drop_eq_nil_iff.mp hRest
    have hBound := (Array.getElem?_eq_some_iff.mp hSource).1
    omega
  | cons upper rest ih =>
    obtain ⟨hUpper, hTail⟩ := partition_suffix_cons hRest
    have hNotOne := hNoPremature index current upper hCurrent hUpper
    have hNotMarked := hNoBetween (index + 1) (by omega) (by omega)
    have hNotStop : ¬ (current.value = 1 ∨ index + 1 ∈ markerIndices) :=
      not_or.mpr ⟨hNotOne, hNotMarked⟩
    simp only [contourSourceCells, hNotStop, ↓reduceIte]
    by_cases hAdjacent : index + 1 = sourceIndex
    · have hSame : upper = sourceCell := Option.some.inj
        (hUpper.symm.trans (by simpa only [hAdjacent] using hSource))
      exact List.mem_cons.mpr (Or.inl hSame.symm)
    · exact List.mem_cons.mpr (Or.inr (ih hUpper (by omega)
        (fun middle hlo hhi => hNoBetween middle (by omega) hhi) hTail))

/-- A finite nonempty set of eligible markers has a greatest eligible
index, without an ordering assumption on the given marker list. -/
theorem maximal_marker_before (markers : List Ref) (limit : Nat)
    (hEligible : ∃ marker ∈ markers, marker.index ≤ limit) :
    ∃ marker ∈ markers, marker.index ≤ limit ∧
      ∀ other ∈ markers, other.index ≤ limit → other.index ≤ marker.index := by
  induction markers with
  | nil => simp at hEligible
  | cons first rest ih =>
    by_cases hRest : ∃ marker ∈ rest, marker.index ≤ limit
    · obtain ⟨chosen, hChosen, hBound, hMax⟩ := ih hRest
      by_cases hFirst : first.index ≤ limit ∧ chosen.index < first.index
      · refine ⟨first, by simp, hFirst.1, ?_⟩
        intro other hOther hOtherBound
        rcases List.mem_cons.mp hOther with rfl | hOther
        · exact le_rfl
        · exact (hMax other hOther hOtherBound).trans hFirst.2.le
      · refine ⟨chosen, by simp [hChosen], hBound, ?_⟩
        intro other hOther hOtherBound
        rcases List.mem_cons.mp hOther with rfl | hOther
        · omega
        · exact hMax other hOther hOtherBound
    · obtain ⟨eligible, hMember, hBound⟩ := hEligible
      have hFirstBound : first.index ≤ limit := by
        rcases List.mem_cons.mp hMember with rfl | hMember
        · exact hBound
        · exact False.elim (hRest ⟨eligible, hMember, hBound⟩)
      refine ⟨first, by simp, hFirstBound, ?_⟩
      intro other hOther hOtherBound
      rcases List.mem_cons.mp hOther with rfl | hOther
      · exact le_rfl
      · exact False.elim (hRest ⟨other, hOther, hOtherBound⟩)

namespace ColumnCopyData

variable {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
  {sourceColumn shift rootColumn : Nat}
  (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)

/-- The selected marker is maximal at or below the actual source node,
including when the node itself is a marker. The no-between conclusion is
stated on the exact marker-index list used by the executable contour. -/
theorem maximal_source_marker (sourceIndex : Nat) :
    ∃ (marker : Ref) (_hm : marker ∈ d.bucket), marker.index ≤ sourceIndex ∧
      (∀ middle, marker.index < middle → middle ≤ sourceIndex →
        middle ∉ d.bucket.map Ref.index) := by
  obtain ⟨marker, hm, hBound, hMax⟩ := maximal_marker_before d.bucket sourceIndex
    ⟨⟨sourceColumn, 0⟩, d.phantom_marker, Nat.zero_le sourceIndex⟩
  refine ⟨marker, hm, hBound, ?_⟩
  intro middle hlo hhi hMarked
  obtain ⟨other, hOther, hOtherIndex⟩ := List.mem_map.mp hMarked
  have hOtherBound : other.index ≤ sourceIndex := by simpa only [hOtherIndex] using hhi
  have hOtherMax := hMax other hOther hOtherBound
  rw [hOtherIndex] at hOtherMax
  omega

/-- All actual source nodes occur either as the chosen physical marker or
inside its actual source contour. No source row is silently omitted when
using marker/contour arguments to establish copied-row support. -/
theorem source_partition (hNoPremature : NoPrematureOne d.sources)
    {sourceIndex : Nat} {sourceCell : Cell}
    (hSource : d.sources[sourceIndex]? = some sourceCell) :
    ∃ (marker : Ref) (hm : marker ∈ d.bucket),
      marker.index ≤ sourceIndex ∧
      (∀ middle, marker.index < middle → middle ≤ sourceIndex →
        middle ∉ d.bucket.map Ref.index) ∧
      (d.marker_data marker hm).current.row ≤ sourceCell.row ∧
      ((sourceIndex = marker.index ∧ sourceCell = (d.marker_data marker hm).current) ∨
        (marker.index < sourceIndex ∧ sourceCell ∈
          contourSourceCells (d.bucket.map Ref.index) marker.index
            (d.marker_data marker hm).current (d.sources.toList.drop (marker.index + 1)))) := by
  obtain ⟨marker, hm, hBound, hNoBetween⟩ := d.maximal_source_marker sourceIndex
  let s := d.marker_data marker hm
  refine ⟨marker, hm, hBound, hNoBetween, ?_, ?_⟩
  · rcases eq_or_lt_of_le hBound with he | hl
    · have hSame : s.current = sourceCell := Option.some.inj
        (s.current_at.symm.trans (by simpa only [he] using hSource))
      exact le_of_eq (congrArg Cell.row hSame)
    · exact (d.source_valid.rows_strict _ _ _ _ s.current_at hSource hl).le
  · rcases eq_or_lt_of_le hBound with he | hl
    · have hSame : s.current = sourceCell := Option.some.inj
        (s.current_at.symm.trans (by simpa only [he] using hSource))
      exact Or.inl ⟨he.symm, hSame.symm⟩
    · exact Or.inr ⟨hl, mem_contourSourceCells_of_no_between hNoPremature
        (d.bucket.map Ref.index) s.current_at hSource hl hNoBetween rfl⟩

end ColumnCopyData

end OmegaY.Expansion

#print axioms OmegaY.Expansion.mem_contourSourceCells_of_no_between
#print axioms OmegaY.Expansion.ColumnCopyData.maximal_source_marker
#print axioms OmegaY.Expansion.ColumnCopyData.source_partition
