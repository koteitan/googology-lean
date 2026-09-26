/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ContourBound.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/ContourBound.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ContourTransport

set_option backward.do.legacy false

/-!
# Actual contour output stays below the next marked source node

The index in markerIndices is a real stored node above the current source.
The source-side loop stops before that index. A target in the source power
interval remains below its cap or rejoins the old source rows, so the copied
output also stays below the next marker whenever that cap is below it.
-/

namespace OmegaY.Expansion

open Canonical

private theorem bound_suffix_cons {nodes : Column} {index : Nat} {upper : Cell}
    {rest : List Cell} (hRest : nodes.toList.drop (index + 1) = upper :: rest) :
    nodes[index + 1]? = some upper ∧ nodes.toList.drop ((index + 1) + 1) = rest := by
  constructor
  · simpa only [List.head?_drop, Array.getElem?_toList, List.head?_cons]
      using congrArg List.head? hRest
  · simpa only [List.tail_drop, List.tail_cons] using congrArg List.tail hRest

/-- The exact stopping test prevents even visiting the next marked node. -/
theorem contourSourceCells_lt_next_marker {mountain : Mountain} {sourceColumn : Nat}
    {nodes : Column} (hValid : ColumnValid mountain sourceColumn nodes)
    (markerIndices : List Nat) {index nextIndex : Nat} {current nextMarker : Cell}
    (hCurrent : nodes[index]? = some current) (hNext : nodes[nextIndex]? = some nextMarker)
    (hMarked : nextIndex ∈ markerIndices) (hIndex : index < nextIndex)
    {rest : List Cell} (hRest : nodes.toList.drop (index + 1) = rest) :
    ∀ cell ∈ contourSourceCells markerIndices index current rest, cell.row < nextMarker.row := by
  induction rest generalizing index current with
  | nil => simp [contourSourceCells]
  | cons upper rest ih =>
    by_cases hStop : current.value = 1 ∨ index + 1 ∈ markerIndices
    · simp [contourSourceCells, hStop]
    · obtain ⟨hUpper, hTail⟩ := bound_suffix_cons hRest
      have hStrictIndex : index + 1 < nextIndex := by
        have hNotMarked : index + 1 ∉ markerIndices := fun hm => hStop (Or.inr hm)
        have hNe : index + 1 ≠ nextIndex := fun he => hNotMarked (he ▸ hMarked)
        omega
      have hUpperBelow := hValid.rows_strict _ _ _ _ hUpper hNext hStrictIndex
      intro cell hCell
      simp only [contourSourceCells, hStop, ↓reduceIte] at hCell
      rcases List.mem_cons.mp hCell with rfl | hCell
      · exact hUpperBelow
      · exact ih hUpper hStrictIndex hTail cell hCell

/-- A pointwise same-or-below-cap comparison transfers a strict upper bound
from the source list when the cap does not exceed that bound. -/
theorem forall₂_same_or_below_bound {sources targets : List Row} {cap ceiling : Row}
    (hPaired : List.Forall₂ (fun a b => a = b ∨ (a < cap ∧ b < cap)) sources targets)
    (hSource : ∀ row ∈ sources, row < ceiling) (hCap : cap ≤ ceiling) :
    ∀ row ∈ targets, row < ceiling := by
  revert hSource
  induction hPaired with
  | nil => simp
  | @cons source target sources targets hRelation hPaired ih =>
    intro hSource row hRow
    rcases List.mem_cons.mp hRow with rfl | hRow
    · rcases hRelation with he | hBelow
      · rw [← he]
        exact hSource source (by simp)
      · exact hBelow.2.trans_le hCap
    · exact ih (fun row hRow => hSource row (by simp [hRow])) row hRow

/-- Transport cannot cross the next marker: before a reset both tracks
remain below the cap, and after a reset the new track equals the old one. -/
theorem contour_trace_lt_next_marker {mountain : Mountain} {sourceColumn : Nat}
    {nodes : Column} (hValid : ColumnValid mountain sourceColumn nodes)
    (hPower : ColumnPowerSteps nodes) (markerIndices : List Nat)
    {index nextIndex : Nat} {current nextMarker : Cell}
    (hCurrent : nodes[index]? = some current) (hNext : nodes[nextIndex]? = some nextMarker)
    (hMarked : nextIndex ∈ markerIndices) (hIndex : index < nextIndex)
    {rest : List Cell} (hRest : nodes.toList.drop (index + 1) = rest)
    {target : Row} {scale : Nat} (hLower : current.row ≤ target)
    (hUpper : target < Row.bump current.row scale)
    (hCap : Row.bump current.row scale ≤ nextMarker.row) :
    ∀ row ∈ bumpTrace target (contourExponents markerIndices index current rest),
      row < nextMarker.row := by
  have hSource := contourSourceCells_lt_next_marker hValid markerIndices hCurrent hNext
    hMarked hIndex hRest
  have hPaired := bumpTrace_same_or_below (root := current.row) le_rfl
    (Row.lt_bump current.row scale) hLower hUpper
    (contourExponents markerIndices index current rest)
  rw [contour_source_trace hPower markerIndices hCurrent hRest] at hPaired
  apply forall₂_same_or_below_bound hPaired ?_ hCap
  intro row hRow
  obtain ⟨cell, hCell, rfl⟩ := List.mem_map.mp hRow
  exact hSource cell hCell

/-- This bound concerns actual successful contour output. Source validity
and source power steps are sufficient; copied-column normality is absent. -/
theorem contour_total_below_next_marker {mountain : Mountain} (hValid : MountainValid mountain)
    {sourceColumn shift rootColumn : Nat} {nodes : Column}
    (hColumn : mountain[sourceColumn]? = some nodes) (hSourcePositive : 0 < sourceColumn)
    (hDestination : sourceColumn + shift ≤ mountain.size) (hTop : TopOne nodes)
    (hPower : ColumnPowerSteps nodes) (markerIndices : List Nat)
    {index nextIndex : Nat} {current nextMarker : Cell} (target : Row)
    (hCurrent : nodes[index]? = some current) (hNext : nodes[nextIndex]? = some nextMarker)
    (hMarked : nextIndex ∈ markerIndices) (hIndex : index < nextIndex)
    {rest : List Cell} (hRest : nodes.toList.drop (index + 1) = rest) {scale : Nat}
    (hLower : current.row ≤ target) (hUpper : target < Row.bump current.row scale)
    (hCap : Row.bump current.row scale ≤ nextMarker.row) :
    ∃ result,
      contour mountain sourceColumn markerIndices shift rootColumn index target current rest = .ok result ∧
      (∀ cell ∈ result, cell.row < nextMarker.row) ∧
      ContourParents mountain (sourceColumn + shift) result := by
  obtain ⟨sourceBound, hNodes⟩ := Array.getElem?_eq_some_iff.mp hColumn
  have hNodesValid : ColumnValid mountain sourceColumn nodes :=
    hNodes ▸ hValid sourceColumn sourceBound
  obtain ⟨result, hRun, hRows, hParents⟩ := contour_total hValid hColumn hSourcePositive
    hDestination hTop markerIndices target hCurrent hRest (rootColumn := rootColumn)
  have hTraceBound := contour_trace_lt_next_marker hNodesValid hPower markerIndices hCurrent hNext
    hMarked hIndex hRest hLower hUpper hCap
  refine ⟨result, hRun, ?_, hParents⟩
  intro cell hCell
  apply hTraceBound cell.row
  rw [← hRows]
  exact List.mem_map.mpr ⟨cell, hCell, rfl⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.contourSourceCells_lt_next_marker
#print axioms OmegaY.Expansion.contour_trace_lt_next_marker
#print axioms OmegaY.Expansion.contour_total_below_next_marker
