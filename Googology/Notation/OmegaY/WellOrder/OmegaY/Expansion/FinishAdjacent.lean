/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/FinishAdjacent.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/FinishAdjacent.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.FinishPreservation
import Mathlib.Data.List.Chain

set_option backward.do.legacy false

/-! Exact numerical equations at adjacent indices of the actual output.
This turns the downward backfill certificate into the upward array interface
needed by canonical reconstruction, without assuming any search rule. -/

namespace OmegaY.Expansion

open Canonical

def AdjacentSum (mountain : Mountain) (lower upper : Cell) : Prop :=
  lower.row ≠ 0 → ∃ ref parent,
    upper.left = some ref ∧ lookup mountain ref = .ok parent ∧
      0 < parent.value ∧ lower.value = upper.value + parent.value

theorem Backfilled.adjacent_sums {mountain : Mountain} {upper : Cell} {rest : List Cell}
    (h : Backfilled mountain upper rest) :
    (upper :: rest).IsChain (fun up low => AdjacentSum mountain low up) := by
  induction h with
  | nil upper => exact List.isChain_singleton _
  | phantom upper lower hRow _ =>
    simp [List.isChain_cons_cons, AdjacentSum, hRow]
  | @next upper lower rest ref parent _ hLeft hParent hPositive hSum _ ih =>
    rw [List.isChain_cons_cons]
    exact ⟨fun _ => ⟨ref, parent, hLeft, hParent, hPositive, hSum⟩, ih⟩

theorem FinishedColumn.adjacent_sums {mountain : Mountain} {column : Column}
    (h : FinishedColumn mountain column) : column.toList.IsChain (AdjacentSum mountain) := by
  obtain ⟨upper, rest, hReverse, _, hFilled, _⟩ := h
  have hChain := hFilled.adjacent_sums
  rw [← hReverse] at hChain
  exact List.isChain_reverse.mp hChain

theorem FinishedColumn.adjacent_sum {mountain : Mountain} {column : Column}
    (h : FinishedColumn mountain column) {index : Nat} {lower upper : Cell}
    (hLower : column[index]? = some lower) (hUpper : column[index + 1]? = some upper)
    (hReal : lower.row ≠ 0) :
    ∃ ref parent, upper.left = some ref ∧ lookup mountain ref = .ok parent ∧
      0 < parent.value ∧ lower.value = upper.value + parent.value := by
  have hi := (Array.getElem?_eq_some_iff.mp hLower).1
  have hj := (Array.getElem?_eq_some_iff.mp hUpper).1
  have hLowerEq : column.toList[index] = lower := by
    simpa only [Array.getElem_toList, Array.getElem?_eq_getElem hi, Option.some.injEq] using hLower
  have hUpperEq : column.toList[index + 1] = upper := by
    simpa only [Array.getElem_toList, Array.getElem?_eq_getElem hj, Option.some.injEq] using hUpper
  have hStep := (List.isChain_iff_getElem.mp h.adjacent_sums) index
    (by simpa only [Array.length_toList] using hj)
  rw [hLowerEq, hUpperEq] at hStep
  exact hStep hReal

theorem FinishedColumn.adjacent_difference {mountain : Mountain} {column : Column}
    (h : FinishedColumn mountain column) (hValid : ColumnValid mountain mountain.size column)
    {index : Nat} {lower upper : Cell}
    (hLower : column[index]? = some lower) (hUpper : column[index + 1]? = some upper)
    (hIndex : 0 < index) :
    1 < lower.value ∧ ∃ ref parent,
      upper.left = some ref ∧ Canonical.cellAt (mountain.push column) ref = .ok parent ∧
      ref.column < mountain.size ∧ 0 < parent.value ∧
      lower.value = upper.value + parent.value ∧ upper.value = lower.value - parent.value := by
  have hRow : lower.row ≠ 0 := by
    have hStrict := hValid.rows_strict 0 index phantom lower hValid.phantom hLower hIndex
    exact ne_of_gt hStrict
  obtain ⟨ref, parent, hLeft, hParent, hPositive, hSum⟩ := h.adjacent_sum hLower hUpper hRow
  have hUpperPositive := hValid.real_positive (index + 1) upper hUpper (by omega)
  have hLeftward := (hValid.stored_valid (index + 1) upper ref hUpper hLeft).1
  have hRead : Canonical.cellAt mountain ref = .ok parent :=
    cellAt_ok_iff.mpr (lookup_ok_iff.mp hParent)
  refine ⟨by omega, ref, parent, hLeft, ?_, hLeftward, hPositive, hSum, by omega⟩
  rw [cellAt_push_left hLeftward]
  exact hRead

end OmegaY.Expansion

#print axioms OmegaY.Expansion.FinishedColumn.adjacent_sum
#print axioms OmegaY.Expansion.FinishedColumn.adjacent_difference
