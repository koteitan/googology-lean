/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/FinishSupport.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/FinishSupport.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.FinishPreservation

set_option backward.do.legacy false

/-! Candidate rows and concrete left endpoints survive actual sorting and
backfill. Witnesses refer to the returned array, and therefore remain usable
after it is appended. Numerical values are deliberately not identified. -/

namespace OmegaY.Expansion

open Canonical

theorem ColumnShape.source_getElem {source : List Cell} {column : Column}
    (h : ColumnShape source column) {index : Nat} {original : Cell}
    (hRead : source[index]? = some original) :
    ∃ cell, column[index]? = some cell ∧ SameShape original cell := by
  have hi : index < source.length := (List.getElem?_eq_some_iff.mp hRead).1
  have hc : index < column.size := by rw [← h.length]; exact hi
  have hCell : column[index]? = some column[index] := Array.getElem?_eq_getElem hc
  obtain ⟨other, hOther, hSame⟩ := h.getElem hCell
  have he : other = original := Option.some.inj (hOther.symm.trans hRead)
  exact ⟨column[index], hCell, he ▸ hSame⟩

/-- Each candidate survives as one concrete returned node with both its row
and its left reference. The sorted index may differ from its input index. -/
theorem finish_candidate_read {mountain : Mountain} {cells : List Cell} {column : Column}
    (hRun : finish mountain cells = .ok column) {original : Cell}
    (hOriginal : original ∈ cells) :
    ∃ (index : Nat) (cell : Cell), column[index]? = some cell ∧ SameShape original cell := by
  have hShape := (finish_success_spec hRun).1
  have hSorted : original ∈ finishSort cells := (finishSort_perm cells).mem_iff.mpr hOriginal
  obtain ⟨index, hIndex⟩ := List.mem_iff_getElem?.mp hSorted
  obtain ⟨cell, hCell, hSame⟩ := hShape.source_getElem hIndex
  exact ⟨index, cell, hCell, hSame⟩

theorem finish_row_read {mountain : Mountain} {cells : List Cell} {column : Column}
    (hRun : finish mountain cells = .ok column) {row : Row}
    (hRow : row ∈ cells.map Cell.row) :
    ∃ (index : Nat) (cell : Cell), column[index]? = some cell ∧ cell.row = row := by
  obtain ⟨original, hOriginal, hOriginalRow⟩ := List.mem_map.mp hRow
  obtain ⟨index, cell, hRead, hSame⟩ := finish_candidate_read hRun hOriginal
  exact ⟨index, cell, hRead, hSame.1.symm.trans hOriginalRow⟩

/-- Finishing neither adds nor removes row labels, even though it changes
values and orders the candidate list. -/
theorem finish_rows_mem_iff {mountain : Mountain} {cells : List Cell} {column : Column}
    (hRun : finish mountain cells = .ok column) (row : Row) :
    row ∈ column.toList.map Cell.row ↔ row ∈ cells.map Cell.row := by
  rw [← (finish_success_spec hRun).1.1]
  exact ((finishSort_perm cells).map Cell.row).mem_iff

theorem finish_appended_row_read {mountain : Mountain} {cells : List Cell} {column : Column}
    (hRun : finish mountain cells = .ok column) {row : Row}
    (hRow : row ∈ cells.map Cell.row) :
    ∃ ref cell, ref.column = mountain.size ∧
      lookup (mountain.push column) ref = .ok cell ∧ cell.row = row := by
  obtain ⟨index, cell, hRead, hCellRow⟩ := finish_row_read hRun hRow
  exact ⟨⟨mountain.size, index⟩, cell, rfl,
    lookup_ok_iff.mpr ⟨column, by simp, hRead⟩, hCellRow⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.finish_candidate_read
#print axioms OmegaY.Expansion.finish_appended_row_read
