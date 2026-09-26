/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Canonical/DecrementRows.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Canonical/DecrementRows.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.DecrementBuild

set_option backward.do.legacy false

/-!
# Row support under exact decrement and suffix grafting

Rows are treated as the actually occurring sparse ordinal labels. No interval
of rows is filled in by definition, and no continuity assumption is used.
-/

namespace OmegaY.Canonical

open Geometry

def RowIn (cells : List Cell) (row : Row) : Prop :=
  ∃ cell ∈ cells, cell.row = row

def RowOccurs (mountain : Mountain) (row : Row) : Prop :=
  ∃ column ∈ mountain.toList, RowIn column.toList row

def RowsSubset (after before : Mountain) : Prop :=
  ∀ row, RowOccurs after row → RowOccurs before row

theorem rowOccurs_iff_cellAt {mountain : Mountain} {row : Row} :
    RowOccurs mountain row ↔ ∃ ref cell, cellAt mountain ref = .ok cell ∧ cell.row = row := by
  constructor
  · rintro ⟨column, hColumn, cell, hCell, hRow⟩
    obtain ⟨c, hc⟩ := List.mem_iff_getElem?.mp hColumn
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hCell
    refine ⟨⟨c, i⟩, cell, cellAt_ok_iff.mpr ⟨column, ?_, ?_⟩, hRow⟩
    · simpa only [Array.getElem?_toList] using hc
    · simpa only [Array.getElem?_toList] using hi
  · rintro ⟨ref, cell, hRead, hRow⟩
    obtain ⟨column, hc, hi⟩ := cellAt_ok_iff.mp hRead
    refine ⟨column, List.mem_iff_getElem?.mpr ⟨ref.column, ?_⟩,
      cell, List.mem_iff_getElem?.mpr ⟨ref.index, ?_⟩, hRow⟩
    · simpa only [Array.getElem?_toList] using hc
    · simpa only [Array.getElem?_toList] using hi

@[simp] theorem rowIn_append (front tail : List Cell) (row : Row) :
    RowIn (front ++ tail) row ↔ RowIn front row ∨ RowIn tail row := by
  simp only [RowIn, List.mem_append, or_and_right, exists_or]

@[simp] theorem rowOccurs_push (mountain : Mountain) (column : Column) (row : Row) :
    RowOccurs (mountain.push column) row ↔ RowOccurs mountain row ∨ RowIn column.toList row := by
  simp [RowOccurs, Array.toList_push, List.mem_append, or_and_right, exists_or]

theorem RowOccurs.frame_cell {mountain : Mountain} (u : (Frame.ofMountain mountain).Node) :
    RowOccurs mountain ((Frame.ofMountain mountain).height u) := by
  refine ⟨mountain[u.1.val], Array.getElem_mem_toList u.1.isLt,
    (Frame.ofMountain mountain).cell u, ?_, rfl⟩
  exact Array.getElem_mem_toList u.2.isLt

theorem upperSuffix_rows {mountain : Mountain} (u : (Frame.ofMountain mountain).Node)
    {row : Row} (hRow : RowIn (upperSuffix mountain u) row) : RowOccurs mountain row := by
  obtain ⟨cell, hCell, hEq⟩ := hRow
  exact ⟨mountain[u.1.val], Array.getElem_mem_toList u.1.isLt,
    cell, List.mem_of_mem_drop hCell, hEq⟩

theorem LeftSuffix.rows {mountain : Mountain} {column : Nat} {tail : List Cell}
    (hTail : LeftSuffix mountain column tail) {row : Row} (hRow : RowIn tail row) :
    RowOccurs mountain row := by
  rcases hTail with rfl | ⟨u, _hColumn, _hReal, rfl⟩
  · obtain ⟨cell, hCell, _⟩ := hRow
    cases hCell
  · obtain ⟨cell, hCell, hEq⟩ := hRow
    rcases List.mem_cons.mp hCell with he | hSuffix
    · subst cell
      exact hEq ▸ RowOccurs.frame_cell u
    · exact upperSuffix_rows u ⟨cell, hSuffix, hEq⟩

theorem decrementPrefix_rows {cells : List Cell} {row : Row}
    (hRow : RowIn (decrementPrefix cells) row) : RowIn cells row := by
  obtain ⟨cell, hCell, hEq⟩ := hRow
  obtain ⟨old, hOld, rfl⟩ := List.mem_map.mp hCell
  exact ⟨old, List.dropLast_subset cells hOld, hEq⟩

/-- Every old non-top cell is retained with precisely its decremented value,
its old row, and its old stored left endpoint. -/
theorem decrement_prefix_retained {oldColumn newColumn : Column} {tail : List Cell}
    (hFormula : newColumn.toList = decrementPrefix oldColumn.toList ++ tail)
    {cell : Cell} (hCell : cell ∈ oldColumn.toList.dropLast) :
    decCell cell ∈ newColumn.toList := by
  rw [hFormula]
  exact List.mem_append_left tail (List.mem_map.mpr ⟨cell, hCell, rfl⟩)

theorem decrement_non_top_row_retained {oldColumn newColumn : Column} {tail : List Cell}
    (hFormula : newColumn.toList = decrementPrefix oldColumn.toList ++ tail)
    {cell : Cell} (hCell : cell ∈ oldColumn.toList.dropLast) :
    RowIn newColumn.toList cell.row :=
  ⟨decCell cell, decrement_prefix_retained hFormula hCell, rfl⟩

/-- The preservation is at the same actual array index, not only row membership. -/
theorem decrement_prefix_at {oldColumn newColumn : Column} {tail : List Cell}
    (hFormula : newColumn.toList = decrementPrefix oldColumn.toList ++ tail)
    {i : Nat} {cell : Cell} (hi : i + 1 < oldColumn.size)
    (hRead : oldColumn[i]? = some cell) : newColumn[i]? = some (decCell cell) := by
  have hBound : i < (decrementPrefix oldColumn.toList).length := by
    simp only [decrementPrefix, List.length_map, List.length_dropLast, Array.length_toList]
    omega
  have hList : newColumn.toList[i]? = some (decCell cell) := by
    rw [hFormula, List.getElem?_append_left hBound]
    simp only [decrementPrefix, List.getElem?_map, List.getElem?_dropLast,
      Array.length_toList, if_pos (show i < oldColumn.size - 1 by omega),
      Array.getElem?_toList, hRead, Option.map_some]
  simpa only [Array.getElem?_toList] using hList

/-- Any new row comes either from the preserved old last-column prefix or
from an actual earlier-column suffix. -/
theorem decrement_new_column_rows {before : Mountain} {oldColumn newColumn : Column}
    {columnIndex : Nat} {tail : List Cell}
    (hOldColumn : oldColumn ∈ before.toList)
    (hFormula : newColumn.toList = decrementPrefix oldColumn.toList ++ tail)
    (hTail : LeftSuffix before columnIndex tail) {row : Row}
    (hRow : RowIn newColumn.toList row) : RowOccurs before row := by
  rw [hFormula, rowIn_append] at hRow
  rcases hRow with hOld | hGraft
  · exact ⟨oldColumn, hOldColumn, decrementPrefix_rows hOld⟩
  · exact hTail.rows hGraft

/-- Replacing only the last column by its exact decrement/graft output cannot
introduce any ordinal row absent from the complete old mountain. -/
theorem decrement_push_rows_subset {left : Mountain} {oldColumn newColumn : Column}
    {tail : List Cell}
    (hFormula : newColumn.toList = decrementPrefix oldColumn.toList ++ tail)
    (hTail : LeftSuffix (left.push oldColumn) left.size tail) :
    RowsSubset (left.push newColumn) (left.push oldColumn) := by
  intro row hRow
  rcases (rowOccurs_push left newColumn row).mp hRow with hLeft | hNew
  · exact (rowOccurs_push left oldColumn row).mpr (Or.inl hLeft)
  · exact decrement_new_column_rows (by simp) hFormula hTail hNew

theorem RowsSubset.preserves_row_bound {after before : Mountain}
    (hSubset : RowsSubset after before) {bound : Row}
    (hBound : ∀ row, RowOccurs before row → row ≤ bound) :
    ∀ row, RowOccurs after row → row ≤ bound :=
  fun row hRow => hBound row (hSubset row hRow)

/-- Every row in the actual decremented build already occurs somewhere in
the actual old build.  Success of both builds is provided independently by
canonical totality; neither row-support inclusion nor normality is a premise. -/
theorem build_decrement_rows_subset {front : List Nat} {last : Nat}
    {before after : Mountain}
    (hBefore : build (front ++ [last]) = .ok before)
    (hAfter : build (front ++ [last - 1]) = .ok after) (hlast : 1 < last) :
    RowsSubset after before := by
  obtain ⟨left, oldColumn, newColumn, tail, _, _, _, hBeforeShape, hAfterShape,
    _, hFormula, hTail, _⟩ := build_decrement_columns hBefore hAfter hlast
  subst before
  subst after
  exact decrement_push_rows_subset hFormula hTail

/-- Every non-top old last-column cell is found at the identical reference
in the new build, with row/left unchanged and value decreased by one. -/
theorem build_decrement_prefix_cell {front : List Nat} {last : Nat}
    {before after : Mountain}
    (hBefore : build (front ++ [last]) = .ok before)
    (hAfter : build (front ++ [last - 1]) = .ok after) (hlast : 1 < last)
    {column : Column} (hColumn : before[front.length]? = some column)
    {i : Nat} {cell : Cell} (hi : i + 1 < column.size)
    (hCell : column[i]? = some cell) :
    cellAt after ⟨front.length, i⟩ = .ok (decCell cell) := by
  obtain ⟨left, oldColumn, newColumn, tail, _, _, _, hBeforeShape, hAfterShape,
    hSize, hFormula, _hTail, _⟩ := build_decrement_columns hBefore hAfter hlast
  have he : oldColumn = column := by
    rw [hBeforeShape, ← hSize] at hColumn
    simpa only [Array.getElem?_push, if_true, Option.some.injEq] using hColumn
  subst column
  apply cellAt_ok_iff.mpr
  refine ⟨newColumn, ?_, decrement_prefix_at hFormula hi hCell⟩
  rw [hAfterShape, ← hSize]
  simp

theorem build_decrement_retains_non_top_rows {front : List Nat} {last : Nat}
    {before after : Mountain}
    (hBefore : build (front ++ [last]) = .ok before)
    (hAfter : build (front ++ [last - 1]) = .ok after) (hlast : 1 < last)
    {column : Column} (hColumn : before[front.length]? = some column)
    {row : Row} (hRow : RowIn column.toList.dropLast row) : RowOccurs after row := by
  obtain ⟨left, oldColumn, newColumn, tail, _, _, _, hBeforeShape, hAfterShape,
    hSize, hFormula, _hTail, _⟩ := build_decrement_columns hBefore hAfter hlast
  have he : oldColumn = column := by
    rw [hBeforeShape, ← hSize] at hColumn
    simpa only [Array.getElem?_push, if_true, Option.some.injEq] using hColumn
  subst column
  obtain ⟨cell, hCell, hEq⟩ := hRow
  rw [hAfterShape, rowOccurs_push]
  exact Or.inr ⟨decCell cell, decrement_prefix_retained hFormula hCell, hEq⟩

theorem build_decrement_preserves_row_bound {front : List Nat} {last : Nat}
    {before after : Mountain}
    (hBefore : build (front ++ [last]) = .ok before)
    (hAfter : build (front ++ [last - 1]) = .ok after) (hlast : 1 < last)
    {bound : Row} (hBound : ∀ row, RowOccurs before row → row ≤ bound) :
    ∀ row, RowOccurs after row → row ≤ bound :=
  (build_decrement_rows_subset hBefore hAfter hlast).preserves_row_bound hBound

/-- The same upper-bound conclusion phrased entirely with actual reads. -/
theorem build_decrement_cell_row_bound {front : List Nat} {last : Nat}
    {before after : Mountain}
    (hBefore : build (front ++ [last]) = .ok before)
    (hAfter : build (front ++ [last - 1]) = .ok after) (hlast : 1 < last)
    {bound : Row}
    (hBound : ∀ ref cell, cellAt before ref = .ok cell → cell.row ≤ bound) :
    ∀ ref cell, cellAt after ref = .ok cell → cell.row ≤ bound := by
  intro ref cell hRead
  have hNew : RowOccurs after cell.row := rowOccurs_iff_cellAt.mpr ⟨ref, cell, hRead, rfl⟩
  have hOld := build_decrement_rows_subset hBefore hAfter hlast cell.row hNew
  obtain ⟨oldRef, oldCell, hOldRead, hRow⟩ := rowOccurs_iff_cellAt.mp hOld
  exact hRow ▸ hBound oldRef oldCell hOldRead

end OmegaY.Canonical

#print axioms OmegaY.Canonical.decrement_prefix_at
#print axioms OmegaY.Canonical.decrement_push_rows_subset
#print axioms OmegaY.Canonical.build_decrement_rows_subset
#print axioms OmegaY.Canonical.build_decrement_prefix_cell
#print axioms OmegaY.Canonical.build_decrement_retains_non_top_rows
#print axioms OmegaY.Canonical.build_decrement_preserves_row_bound
#print axioms OmegaY.Canonical.build_decrement_cell_row_bound
