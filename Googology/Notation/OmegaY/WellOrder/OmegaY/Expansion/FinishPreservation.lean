/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/FinishPreservation.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/FinishPreservation.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.FinishGeometry
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Totality

set_option backward.do.legacy false

/-!
# Validity of the actual finished column

The extra hypotheses describe candidate stored legs, before sorting: every
nonzero candidate has a left reference, and every stored reference is an
actual readable earlier parent with a weakly smaller row. They are not a
ColumnValid or canonical-normality certificate for the output.
-/

namespace OmegaY.Expansion

open Canonical

/-- Every zero-row entry actually produced by backfill has value zero. -/
theorem Backfilled.zero_value {mountain : Mountain} {upper : Cell} {cells : List Cell}
    (h : Backfilled mountain upper cells) :
    ∀ cell ∈ cells, cell.row = 0 → cell.value = 0 := by
  induction h with
  | nil upper => simp
  | phantom upper lower hRow hValue =>
    intro cell hMem _
    have he := List.mem_singleton.mp hMem
    exact he ▸ hValue
  | @next upper lower rest ref parent hRow hLeft hRead hPositive hValue hTail ih =>
    intro cell hMem hZero
    rcases List.mem_cons.mp hMem with he | ht
    · exact False.elim (hRow (he ▸ hZero))
    · exact ih cell ht hZero

theorem FinishedColumn.topOne {mountain : Mountain} {column : Column}
    (h : FinishedColumn mountain column) : TopOne column := by
  obtain ⟨upper, rest, hReverse, hValue, _, _⟩ := h
  have hList : column.toList = rest.reverse ++ [upper] := by
    simpa using congrArg List.reverse hReverse
  have hColumn : column = (rest.reverse ++ [upper]).toArray := by
    simpa using congrArg List.toArray hList
  refine ⟨upper, ?_, hValue⟩
  rw [hColumn]
  simp

/-- Separate row/left list equalities preserve both fields at the same
actual index; source matching is not selected independently by value. -/
theorem ColumnShape.getElem {source : List Cell} {column : Column}
    (h : ColumnShape source column) {index : Nat} {cell : Cell}
    (hRead : column[index]? = some cell) :
    ∃ original, source[index]? = some original ∧ SameShape original cell := by
  have hRows := congrArg (fun rows : List Row => rows[index]?) h.1
  have hLefts := congrArg (fun refs : List (Option Ref) => refs[index]?) h.2
  simp only [List.getElem?_map, Array.getElem?_toList, hRead, Option.map_some] at hRows hLefts
  cases hSource : source[index]? with
  | none => simp [hSource] at hRows
  | some original =>
    refine ⟨original, rfl, ?_, ?_⟩
    · exact Option.some.inj (by simpa only [hSource, Option.map_some] using hRows)
    · exact Option.some.inj (by simpa only [hSource, Option.map_some] using hLefts)

theorem ColumnShape.length {source : List Cell} {column : Column}
    (h : ColumnShape source column) : source.length = column.size := by
  simpa using congrArg List.length h.1

theorem ColumnShape.strict {source : List Cell} {column : Column}
    (h : ColumnShape source column) (hStrict : source.Pairwise (fun a b => a.row < b.row)) :
    column.toList.Pairwise (fun a b => a.row < b.row) := by
  have hRows : (source.map Cell.row).Pairwise (· < ·) := by
    simpa only [List.pairwise_map] using hStrict
  rw [h.1] at hRows
  simpa only [List.pairwise_map] using hRows

/-- The second sorted row is exactly the supplied real bottom row. -/
theorem FinishInput.sorted_bottom {mountain : Mountain} {cells : List Cell}
    (h : FinishInput mountain cells) :
    ∃ bottom rest, finishSort cells = phantom :: bottom :: rest ∧ bottom.row = 1 := by
  obtain ⟨tail, hPhantom⟩ := h.sorted_phantom
  obtain ⟨bottom, hBottom, hBottomRow⟩ := h.bottom_mem
  have hMem : bottom ∈ finishSort cells := (finishSort_perm cells).mem_iff.mpr hBottom
  have hStrict := finishSort_strict h.rows_nodup
  rw [hPhantom] at hMem hStrict
  have hInTail : bottom ∈ tail := by
    rcases List.mem_cons.mp hMem with he | ht
    · have hBad : (0 : Row) = 1 := by simpa only [he, phantom] using hBottomRow
      exact False.elim ((ne_of_lt Row.zero_lt_one) hBad)
    · exact ht
  cases tail with
  | nil => cases hInTail
  | cons next rest =>
    refine ⟨next, rest, hPhantom, ?_⟩
    have hPositive := (List.pairwise_cons.mp hStrict).1 next (by simp)
    have hOne : (1 : Row) ≤ next.row := row_one_le_of_ne_zero (ne_of_gt hPositive)
    rcases List.mem_cons.mp hInTail with he | ht
    · simpa only [he] using hBottomRow
    · have hBelow := (List.pairwise_cons.mp (List.pairwise_cons.mp hStrict).2).1 bottom ht
      rw [hBottomRow] at hBelow
      exact False.elim ((not_lt_of_ge hOne) hBelow)

/-- The value-1 seed at the top is real, so a zero-row output belongs to the
backfilled tail and receives the phantom value from Backfilled.zero_value. -/
theorem FinishInput.output_zero_value {mountain : Mountain} {cells : List Cell}
    (hInput : FinishInput mountain cells) {column : Column}
    (hShape : ColumnShape (finishSort cells) column) (hFinished : FinishedColumn mountain column)
    {cell : Cell} (hMem : cell ∈ column.toList) (hZero : cell.row = 0) : cell.value = 0 := by
  obtain ⟨sourceTop, sourceRest, hSourceReverse, hSourceReal⟩ := hInput.sorted_real_top
  obtain ⟨upper, rest, hReverse, _hValue, hBackfilled, _hPositive⟩ := hFinished
  have hRows : (finishSort cells).reverse.map Cell.row = column.toList.reverse.map Cell.row := by
    simpa only [List.map_reverse] using congrArg List.reverse hShape.1
  rw [hSourceReverse, hReverse, List.map_cons, List.map_cons] at hRows
  have hTopRow := (List.cons.inj hRows).1
  have hTopReal : upper.row ≠ 0 := by
    intro hz
    exact hSourceReal (hTopRow.trans hz)
  have hInReverse : cell ∈ upper :: rest := by
    rw [← hReverse]
    exact List.mem_reverse.mpr hMem
  rcases List.mem_cons.mp hInReverse with he | ht
  · exact False.elim (hTopReal (he ▸ hZero))
  · exact hBackfilled.zero_value cell ht hZero

private theorem cell_eq_phantom {cell : Cell}
    (hRow : cell.row = 0) (hValue : cell.value = 0) (hLeft : cell.left = none) :
    cell = phantom := by
  cases cell
  simp_all [phantom]

/-- Output structural fields supplied solely by exact shape preservation,
sorting, and actual backfill equations. No stored-leg premises are needed. -/
theorem FinishInput.output_geometry {mountain : Mountain} {cells : List Cell}
    (hInput : FinishInput mountain cells) {column : Column}
    (hShape : ColumnShape (finishSort cells) column) (hFinished : FinishedColumn mountain column) :
    2 ≤ column.size ∧ column[0]? = some phantom ∧
      (∀ cell, column[1]? = some cell → cell.row = 1) ∧
      (∀ (i j : Nat) (a b : Cell), column[i]? = some a → column[j]? = some b → i < j → a.row < b.row) ∧
      (∀ i cell, column[i]? = some cell → 0 < i → 0 < cell.value) ∧ TopOne column := by
  obtain ⟨bottom, rest, hSorted, hBottomRow⟩ := hInput.sorted_bottom
  have hSize : 2 ≤ column.size := by
    have hLength := hShape.length
    rw [hSorted] at hLength
    simp only [List.length_cons] at hLength
    omega
  have hIndexed : ∀ (i j : Nat) (a b : Cell), column[i]? = some a → column[j]? = some b →
      i < j → a.row < b.row := by
    intro i j a b ha hb hij
    obtain ⟨hi, hA⟩ := Array.getElem?_eq_some_iff.mp ha
    obtain ⟨hj, hB⟩ := Array.getElem?_eq_some_iff.mp hb
    have hStrict := hShape.strict (finishSort_strict hInput.rows_nodup)
    have hAB := List.pairwise_iff_getElem.mp hStrict i j hi hj hij
    simpa only [Array.getElem_toList, hA, hB] using hAB
  have hFirstRead : column[0]? = some column[0] := Array.getElem?_eq_getElem (by omega)
  obtain ⟨original, hOriginal, hFirstShape⟩ := hShape.getElem hFirstRead
  have hOriginalEq : original = phantom := by
    rw [hSorted] at hOriginal
    exact Option.some.inj hOriginal.symm
  have hFirstRow : column[0].row = 0 := by simpa only [hOriginalEq, SameShape, phantom] using hFirstShape.1.symm
  have hFirstLeft : column[0].left = none := by simpa only [hOriginalEq, SameShape, phantom] using hFirstShape.2.symm
  have hFirstValue : column[0].value = 0 := hInput.output_zero_value hShape hFinished
    (List.mem_of_getElem? (by simpa only [Array.getElem?_toList] using hFirstRead)) hFirstRow
  have hFirstEq := cell_eq_phantom hFirstRow hFirstValue hFirstLeft
  have hPhantom : column[0]? = some phantom := hFirstRead.trans (congrArg some hFirstEq)
  refine ⟨hSize, hPhantom, ?_, hIndexed, ?_, hFinished.topOne⟩
  · intro cell hRead
    obtain ⟨source, hSource, hCellShape⟩ := hShape.getElem hRead
    rw [hSorted] at hSource
    have he : source = bottom := Option.some.inj hSource.symm
    exact hCellShape.1.symm.trans ((congrArg Cell.row he).trans hBottomRow)
  · intro i cell hRead hi
    have hRow := hIndexed 0 i phantom cell hPhantom hRead hi
    have hReal : cell.row ≠ 0 := ne_of_gt hRow
    obtain ⟨upper, rest, hReverse, _hTop, _hBackfilled, hPositive⟩ := hFinished
    apply hPositive cell _ hReal
    rw [← hReverse]
    exact List.mem_reverse.mpr (List.mem_of_getElem? (by simpa only [Array.getElem?_toList] using hRead))

/-- The real finished output is a valid next column, provided candidate legs
are already readable to the left and respect their row bounds. -/
theorem FinishInput.output_valid {mountain : Mountain} {cells : List Cell}
    (hInput : FinishInput mountain cells) (hSize : 0 < mountain.size)
    (hExists : ∀ cell ∈ cells, cell.row ≠ 0 → ∃ ref, cell.left = some ref)
    (hStored : ∀ cell ∈ cells, ∀ ref, cell.left = some ref →
      ∃ parent, lookup mountain ref = .ok parent ∧ ref.column < mountain.size ∧ parent.row ≤ cell.row)
    {column : Column} (hShape : ColumnShape (finishSort cells) column)
    (hFinished : FinishedColumn mountain column) :
    ColumnValid mountain mountain.size column ∧ TopOne column := by
  obtain ⟨hTwo, hPhantom, hBottom, hStrict, hPositive, hTop⟩ :=
    hInput.output_geometry hShape hFinished
  refine ⟨{
    size_ge_two := hTwo
    phantom := hPhantom
    bottom_row := hBottom
    rows_strict := hStrict
    real_positive := hPositive
    stored_valid := ?_
    stored_exists := ?_
    first_values := ?_ }, hTop⟩
  · intro i cell ref hRead hLeft
    obtain ⟨source, hSource, hSame⟩ := hShape.getElem hRead
    have hSourceMem : source ∈ cells := (finishSort_perm cells).mem_iff.mp (List.mem_of_getElem? hSource)
    obtain ⟨parent, hParent, hLeftward, hRow⟩ :=
      hStored source hSourceMem ref (hSame.2.trans hLeft)
    exact ⟨hLeftward, parent, cellAt_ok_iff.mpr (lookup_ok_iff.mp hParent), hRow.trans_eq hSame.1⟩
  · intro i cell hRead hi _hDestination
    obtain ⟨source, hSource, hSame⟩ := hShape.getElem hRead
    have hSourceMem : source ∈ cells := (finishSort_perm cells).mem_iff.mp (List.mem_of_getElem? hSource)
    have hRow := hStrict 0 i phantom cell hPhantom hRead hi
    have hNonzero : source.row ≠ 0 := by
      intro hz
      exact (ne_of_gt hRow) (hSame.1.symm.trans hz)
    obtain ⟨ref, hLeft⟩ := hExists source hSourceMem hNonzero
    exact ⟨ref, hSame.2.symm.trans hLeft⟩
  · intro i cell hRead hi hZero
    omega

theorem FinishInput.finish_valid {mountain : Mountain} {cells : List Cell}
    (hInput : FinishInput mountain cells) (hSize : 0 < mountain.size)
    (hExists : ∀ cell ∈ cells, cell.row ≠ 0 → ∃ ref, cell.left = some ref)
    (hStored : ∀ cell ∈ cells, ∀ ref, cell.left = some ref →
      ∃ parent, lookup mountain ref = .ok parent ∧ ref.column < mountain.size ∧ parent.row ≤ cell.row) :
    ∃ column, OmegaY.Expansion.finish mountain cells = .ok column ∧
      ColumnShape (finishSort cells) column ∧ FinishedColumn mountain column ∧
      ColumnValid mountain mountain.size column ∧ TopOne column := by
  obtain ⟨column, hRun, hShape, hFinished⟩ := hInput.finish
  obtain ⟨hValid, hTop⟩ := hInput.output_valid hSize hExists hStored hShape hFinished
  exact ⟨column, hRun, hShape, hFinished, hValid, hTop⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.FinishInput.output_geometry
#print axioms OmegaY.Expansion.FinishInput.finish_valid
