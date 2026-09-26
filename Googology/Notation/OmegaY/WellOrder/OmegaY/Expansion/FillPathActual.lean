/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/FillPathActual.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/FillPathActual.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.FillPowerSteps

set_option backward.do.legacy false

/-!
# The entire actual fill loop is a consecutive interval path

The low and high rows are actual nodes of the parent column. Strict source
order identifies the executable eligibility condition with a contiguous
index interval. Each ladder is reversed individually, exactly as in
fillCellsAscendingRows; no full-list reversal or gap-success premise is used.
-/

namespace OmegaY.Expansion

open Canonical

private theorem read_row_le_iff {nodes : Column} (hStrict : FillRowsStrict nodes)
    {i j : Nat} {a b : Cell} (ha : nodes[i]? = some a) (hb : nodes[j]? = some b) :
    a.row ≤ b.row ↔ i ≤ j := by
  constructor
  · intro hRow
    by_contra hIndex
    exact (not_lt_of_ge hRow) (hStrict j i b a hb ha (by omega))
  · intro hIndex
    rcases eq_or_lt_of_le hIndex with he | hl
    · subst j
      have he := Option.some.inj (ha.symm.trans hb)
      exact le_of_eq (congrArg Cell.row he)
    · exact (hStrict i j a b ha hb hl).le

private theorem read_row_lt_iff {nodes : Column} (hStrict : FillRowsStrict nodes)
    {i j : Nat} {a b : Cell} (ha : nodes[i]? = some a) (hb : nodes[j]? = some b) :
    a.row < b.row ↔ i < j := by
  constructor
  · intro hRow
    have hNot : ¬ j ≤ i := by
      intro hji
      exact (not_lt_of_ge ((read_row_le_iff hStrict hb ha).mpr hji)) hRow
    omega
  · exact hStrict i j a b ha hb

private theorem range_flatMap_interval {α : Type} (f g : Nat → List α)
    {low high size : Nat} (hOrder : low ≤ high) (hSize : high ≤ size)
    (hBefore : ∀ i, i < low → f i = [])
    (hMiddle : ∀ i, low ≤ i → i < high → f i = g i)
    (hAfter : ∀ i, high ≤ i → i < size → f i = []) :
    (List.range size).flatMap f = (List.range' low (high - low)).flatMap g := by
  have hLeft : List.range low ++ List.range' low (high - low) = List.range high := by
    simpa only [List.range_eq_range', Nat.zero_add, Nat.add_sub_of_le hOrder] using
      (List.range'_append_1 (s := 0) (m := low) (n := high - low))
  have hRight : List.range high ++ List.range' high (size - high) = List.range size := by
    simpa only [List.range_eq_range', Nat.zero_add, Nat.add_sub_of_le hSize] using
      (List.range'_append_1 (s := 0) (m := high) (n := size - high))
  have hSplit : List.range size =
      (List.range low ++ List.range' low (high - low)) ++ List.range' high (size - high) := by
    rw [hLeft, hRight]
  have hBeforeNil : (List.range low).flatMap f = [] :=
    List.flatMap_eq_nil_iff.mpr (fun i hi => hBefore i (List.mem_range.mp hi))
  have hAfterNil : (List.range' high (size - high)).flatMap f = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro i hi
    obtain ⟨hlo, hhi⟩ := List.mem_range'_1.mp hi
    exact hAfter i hlo (by omega)
  rw [hSplit, List.flatMap_append, List.flatMap_append, hBeforeNil, hAfterNil,
    List.nil_append, List.append_nil]
  apply List.flatMap_congr
  intro i hi
  obtain ⟨hlo, hhi⟩ := List.mem_range'_1.mp hi
  exact hMiddle i hlo (by omega)

/-- The actual row read function is used only on indices whose existence is
proved below. Its default never contributes an eligible interval. -/
def parentRowAt (nodes : Column) (index : Nat) : Row :=
  (nodes[index]?.getD phantom).row

/-- The consecutive upper endpoints after the low node, through high. -/
def parentIntervalRows (nodes : Column) (lowIndex highIndex : Nat) : List Row :=
  (List.range' (lowIndex + 1) (highIndex - lowIndex)).map (parentRowAt nodes)

theorem interval_ladders_eq_fillPath (rowAt : Nat → Row) (start count : Nat) :
    (List.range' start count).flatMap (fun i =>
      (Row.fillLadder (rowAt i) (rowAt (i + 1))).reverse) =
      fillPath (rowAt start) ((List.range' (start + 1) count).map rowAt) := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    simp only [List.range'_succ, List.flatMap_cons, List.map_cons, fillPath]
    rw [ih]

theorem interval_rows_power_steps (rowAt : Nat → Row) (start count : Nat)
    (hPower : ∀ i, start ≤ i → i < start + count → RowPowerStep (rowAt i) (rowAt (i + 1))) :
    RowsPowerSteps (rowAt start :: (List.range' (start + 1) count).map rowAt) := by
  induction count generalizing start with
  | zero => exact .singleton _
  | succ count ih =>
    simp only [List.range'_succ, List.map_cons]
    apply List.IsChain.cons_cons
    · exact hPower start le_rfl (by omega)
    · exact ih (start + 1) (fun i hlo hhi => hPower i (by omega) (by omega))

theorem interval_rows_last (rowAt : Nat → Row) (start count : Nat) :
    (rowAt start :: (List.range' (start + 1) count).map rowAt).getLast? =
      some (rowAt (start + count)) := by
  induction count generalizing start with
  | zero => simp
  | succ count ih =>
    simpa only [List.range'_succ, List.map_cons, List.getLast?_cons_cons,
      Nat.add_assoc, Nat.add_comm 1 count] using ih (start + 1)

/-- Exact identification of every executable eligible chunk with the
consecutive parent-index interval. Equal endpoints give the empty interval. -/
theorem fillCellsAscendingRows_eq_fillPath {nodes : Column}
    (hStrict : FillRowsStrict nodes) {column lowIndex highIndex : Nat}
    {lowCell highCell : Cell}
    (hLow : nodes[lowIndex]? = some lowCell) (hHigh : nodes[highIndex]? = some highCell)
    (hOrder : lowCell.row ≤ highCell.row) :
    fillCellsAscendingRows nodes column lowCell.row highCell.row =
      fillPath lowCell.row (parentIntervalRows nodes lowIndex highIndex) := by
  have hIndexOrder : lowIndex ≤ highIndex := (read_row_le_iff hStrict hLow hHigh).mp hOrder
  have hHighBound := (Array.getElem?_eq_some_iff.mp hHigh).1
  let actual := fun i => ((fillChunk nodes column lowCell.row highCell.row i).map Cell.row).reverse
  let ladder := fun i => (Row.fillLadder (parentRowAt nodes i) (parentRowAt nodes (i + 1))).reverse
  have hChunk : ∀ i, i < nodes.size → actual i =
      if lowIndex ≤ i ∧ i < highIndex then ladder i else [] := by
    intro i hi
    have hRead : nodes[i]? = some nodes[i] := Array.getElem?_eq_getElem hi
    have hEligible : (lowCell.row ≤ nodes[i].row ∧ nodes[i].row < highCell.row) ↔
        lowIndex ≤ i ∧ i < highIndex :=
      and_congr (read_row_le_iff hStrict hLow hRead) (read_row_lt_iff hStrict hRead hHigh)
    simp only [actual, fillChunk_rows, hRead, Option.getD_some]
    by_cases hIndices : lowIndex ≤ i ∧ i < highIndex
    · have hRows := hEligible.mpr hIndices
      simp only [hRows, hIndices, and_self, ↓reduceIte, ladder, parentRowAt, hRead, Option.getD_some]
    · have hRows := mt hEligible.mp hIndices
      simp only [hRows, hIndices, ↓reduceIte, List.reverse_nil]
  have hRestricted := range_flatMap_interval actual ladder hIndexOrder (Nat.le_of_lt hHighBound)
    (by
      intro i hi
      rw [hChunk i (by omega)]
      simp only [show ¬ (lowIndex ≤ i ∧ i < highIndex) by omega, ↓reduceIte])
    (by
      intro i hlo hhi
      rw [hChunk i (by omega)]
      simp only [hlo, hhi, and_self, ↓reduceIte])
    (by
      intro i hlo hhi
      rw [hChunk i hhi]
      simp only [show ¬ (lowIndex ≤ i ∧ i < highIndex) by omega, ↓reduceIte])
  change (List.range nodes.size).flatMap actual = _
  rw [hRestricted]
  change (List.range' lowIndex (highIndex - lowIndex)).flatMap
    (fun i => (Row.fillLadder (parentRowAt nodes i) (parentRowAt nodes (i + 1))).reverse) = _
  rw [interval_ladders_eq_fillPath]
  simp only [parentRowAt, hLow, Option.getD_some, parentIntervalRows]

/-- The old canonical power-step certificate can be used on precisely the
actual parent rows between the two requested endpoints. -/
theorem parentIntervalRows_power_steps {nodes : Column} (hPower : ColumnPowerSteps nodes)
    {lowIndex highIndex : Nat} {lowCell highCell : Cell}
    (hLow : nodes[lowIndex]? = some lowCell) (hHigh : nodes[highIndex]? = some highCell)
    (hIndexOrder : lowIndex ≤ highIndex) :
    RowsPowerSteps (lowCell.row :: parentIntervalRows nodes lowIndex highIndex) := by
  have hHighBound := (Array.getElem?_eq_some_iff.mp hHigh).1
  have h := interval_rows_power_steps (parentRowAt nodes) lowIndex (highIndex - lowIndex) (by
    intro i hlo hhi
    have hi : i < nodes.size := by omega
    have hu : i + 1 < nodes.size := by omega
    have hRead : nodes[i]? = some nodes[i] := Array.getElem?_eq_getElem hi
    have hUpper : nodes[i + 1]? = some nodes[i + 1] := Array.getElem?_eq_getElem hu
    simpa only [parentRowAt, hRead, hUpper, Option.getD_some, RowPowerStep] using
      hPower i nodes[i] nodes[i + 1] hRead hUpper)
  simpa only [parentRowAt, hLow, Option.getD_some, parentIntervalRows] using h

theorem parentIntervalRows_last {nodes : Column} {lowIndex highIndex : Nat}
    {lowCell highCell : Cell}
    (hLow : nodes[lowIndex]? = some lowCell) (hHigh : nodes[highIndex]? = some highCell)
    (hIndexOrder : lowIndex ≤ highIndex) :
    (lowCell.row :: parentIntervalRows nodes lowIndex highIndex).getLast? = some highCell.row := by
  have h := interval_rows_last (parentRowAt nodes) lowIndex (highIndex - lowIndex)
  simpa only [parentRowAt, hLow, Option.getD_some, parentIntervalRows,
    Nat.add_sub_of_le hIndexOrder, hHigh] using h

/-- The whole actual fill output, in ascending order and with the low seed,
has power steps and ends exactly at the actual high node. This includes low=high. -/
theorem fillCellsAscendingRows_power_steps {nodes : Column}
    (hStrict : FillRowsStrict nodes) (hPower : ColumnPowerSteps nodes)
    {column lowIndex highIndex : Nat} {lowCell highCell : Cell}
    (hLow : nodes[lowIndex]? = some lowCell) (hHigh : nodes[highIndex]? = some highCell)
    (hOrder : lowCell.row ≤ highCell.row) :
    RowsPowerSteps (lowCell.row :: fillCellsAscendingRows nodes column lowCell.row highCell.row) ∧
      (lowCell.row :: fillCellsAscendingRows nodes column lowCell.row highCell.row).getLast? =
        some highCell.row := by
  have hIndexOrder := (read_row_le_iff hStrict hLow hHigh).mp hOrder
  have hParentPower := parentIntervalRows_power_steps hPower hLow hHigh hIndexOrder
  rw [fillCellsAscendingRows_eq_fillPath hStrict hLow hHigh hOrder]
  exact ⟨fillPath_power_steps _ _ hParentPower,
    (fillPath_last _ _ hParentPower).trans (parentIntervalRows_last hLow hHigh hIndexOrder)⟩

theorem fillCellsAscendingRows_self (nodes : Column) (column : Nat) (row : Row) :
    fillCellsAscendingRows nodes column row row = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro i _
  rw [fillChunk_rows]
  have hNo : ¬ (row ≤ (nodes[i]?.getD phantom).row ∧ (nodes[i]?.getD phantom).row < row) := by
    intro h
    exact (not_lt_of_ge h.1) h.2
  simp only [hNo, ↓reduceIte, List.reverse_nil]

/-- A sorted permutation of the actual fill rows inherits the same complete
path theorem. Sorting success is not an assumption about canonicality. -/
theorem fill_sorted_rows_power_steps {nodes : Column}
    (hStrict : FillRowsStrict nodes) (hPower : ColumnPowerSteps nodes)
    {column lowIndex highIndex : Nat} {lowCell highCell : Cell}
    (hLow : nodes[lowIndex]? = some lowCell) (hHigh : nodes[highIndex]? = some highCell)
    (hOrder : lowCell.row ≤ highCell.row) {sorted : List Row}
    (hPerm : sorted.Perm ((fillCells nodes column lowCell.row highCell.row).map Cell.row))
    (hSorted : sorted.Pairwise (· < ·)) :
    RowsPowerSteps (lowCell.row :: sorted) ∧
      (lowCell.row :: sorted).getLast? = some highCell.row := by
  rw [fillCellsAscendingRows_eq_of_sorted_perm hStrict hHigh le_rfl hPerm hSorted]
  exact fillCellsAscendingRows_power_steps hStrict hPower hLow hHigh hOrder

end OmegaY.Expansion

#print axioms OmegaY.Expansion.fillCellsAscendingRows_eq_fillPath
#print axioms OmegaY.Expansion.fillCellsAscendingRows_power_steps
#print axioms OmegaY.Expansion.fill_sorted_rows_power_steps
