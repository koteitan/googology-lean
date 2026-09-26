/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/FinishGeometry.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/FinishGeometry.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.Finish
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.WeakTotality
import Mathlib.Data.List.Nodup

set_option backward.do.legacy false

/-!
# Geometric input conditions for the actual finisher

The conditions are on the unsorted candidate list. The actual mergeSort
supplies its order; positive readable parents are needed only above row 1.
The row-1 cell's left reference is not read when backfill reaches the phantom.
No numerical sums, row-power-step invariant, canonicality, successful sort
validation, or successful finish are assumed.
-/

namespace OmegaY.Expansion

open Canonical

/-- There is no ordinal row strictly between zero and one. -/
theorem row_one_le_of_ne_zero {row : Row} (h : row ≠ 0) : (1 : Row) ≤ row := by
  apply le_of_not_gt
  intro hlt
  obtain ⟨i, hhigh, hi⟩ := Row.lt_iff.mp hlt
  cases i with
  | zero =>
    have hzero : Row.coeff row 0 = 0 := by
      change Row.coeff row 0 < 1 at hi
      omega
    apply h
    apply Row.ext
    intro j
    cases j with
    | zero => simpa using hzero
    | succ j =>
      have he := hhigh (j + 1) (by omega)
      change Row.coeff row (j + 1) = Row.coeff (1 : Nat) (j + 1) at he
      simpa using he
  | succ i =>
    change Row.coeff row (i + 1) < Row.coeff (1 : Nat) (i + 1) at hi
    simp at hi

/-- All inputs needed by the actual finisher, before sorting. Row uniqueness
also makes the included phantom the unique row-zero cell. -/
structure FinishInput (mountain : Mountain) (cells : List Cell) : Prop where
  rows_nodup : (cells.map Cell.row).Nodup
  phantom_mem : phantom ∈ cells
  bottom_mem : ∃ bottom ∈ cells, bottom.row = 1
  parents_above_one : ∀ cell ∈ cells, (1 : Row) < cell.row →
    ∃ ref parent, cell.left = some ref ∧ lookup mountain ref = .ok parent ∧ 0 < parent.value

/-- The sorting expression is exactly the one in executable `finish`. -/
def finishSort (cells : List Cell) : List Cell :=
  cells.mergeSort (fun a b => decide (a.row ≤ b.row))

theorem finishSort_perm (cells : List Cell) : (finishSort cells).Perm cells :=
  List.mergeSort_perm _ _

theorem finishSort_strict {cells : List Cell} (hNodup : (cells.map Cell.row).Nodup) :
    (finishSort cells).Pairwise (fun a b => a.row < b.row) := by
  have hLE : (finishSort cells).Pairwise (fun a b => a.row ≤ b.row) := by
    have hSorted := List.pairwise_mergeSort
      (le := fun a b : Cell => decide (a.row ≤ b.row))
      (fun a b c hab hbc => by simpa using le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
      (fun a b => by simpa using le_total a.row b.row) cells
    simpa only [finishSort, decide_eq_true_eq] using hSorted
  have hRows : ((finishSort cells).map Cell.row).Nodup :=
    ((finishSort_perm cells).map Cell.row).nodup_iff.mpr hNodup
  have hNE : (finishSort cells).Pairwise (fun a b => a.row ≠ b.row) := by
    simpa only [List.Nodup, List.pairwise_map] using hRows
  exact (List.pairwise_and_iff.mpr ⟨hLE, hNE⟩).imp
    (fun h => lt_of_le_of_ne h.1 h.2)

/-- Strict row order implies the exact adjacency check used by the program. -/
theorem adjacent_rows_ne {cells : List Cell}
    (hStrict : cells.Pairwise (fun a b => a.row < b.row)) :
    ∀ pair ∈ cells.zip cells.tail, pair.1.row ≠ pair.2.row := by
  induction cells with
  | nil => simp
  | cons first tail ih =>
    cases tail with
    | nil => simp
    | cons second rest =>
      obtain ⟨hFirst, hTail⟩ := List.pairwise_cons.mp hStrict
      intro pair hPair
      rcases List.mem_cons.mp hPair with he | ht
      · subst pair
        exact ne_of_lt (hFirst second (by simp))
      · exact ih hTail pair ht

/-- A strictly decreasing row list can be backfilled as soon as the upper
nodes above row 1 have readable positive parents. A zero lower node must be
the last list entry; its predecessor's parent is deliberately not required. -/
theorem backfillReady_of_strict {mountain : Mountain} {upper : Cell} {rest : List Cell}
    (hStrict : (upper :: rest).Pairwise (fun a b => b.row < a.row))
    (hParents : ∀ cell ∈ upper :: rest, (1 : Row) < cell.row →
      ∃ ref parent, cell.left = some ref ∧ lookup mountain ref = .ok parent ∧ 0 < parent.value) :
    BackfillReady mountain upper rest := by
  induction rest generalizing upper with
  | nil => exact .nil upper
  | cons lower tail ih =>
    obtain ⟨hUpper, hTail⟩ := List.pairwise_cons.mp hStrict
    by_cases hZero : lower.row = 0
    · have hEmpty : tail = [] := by
        cases tail with
        | nil => rfl
        | cons first rest =>
          have hBelow := (List.pairwise_cons.mp hTail).1 first (by simp)
          rw [hZero] at hBelow
          exact False.elim ((not_lt_of_ge (Row.zero_le first.row)) hBelow)
      subst tail
      exact .phantom upper lower hZero
    · have hAbove : (1 : Row) < upper.row :=
        (row_one_le_of_ne_zero hZero).trans_lt (hUpper lower (by simp))
      obtain ⟨ref, parent, hLeft, hRead, hPositive⟩ := hParents upper (by simp) hAbove
      exact .next hZero hLeft hRead hPositive
        (ih hTail (fun cell hCell hRow => hParents cell (by simp [hCell]) hRow))

/-- The actual sorted list begins with the actual included phantom. -/
theorem FinishInput.sorted_phantom {mountain : Mountain} {cells : List Cell}
    (h : FinishInput mountain cells) : ∃ tail, finishSort cells = phantom :: tail := by
  have hMem : phantom ∈ finishSort cells := (finishSort_perm cells).mem_iff.mpr h.phantom_mem
  have hStrict := finishSort_strict h.rows_nodup
  cases hSorted : finishSort cells with
  | nil => simp [hSorted] at hMem
  | cons first tail =>
    rw [hSorted] at hMem hStrict
    rcases List.mem_cons.mp hMem with he | ht
    · subst first
      exact ⟨tail, rfl⟩
    · have hBelow := (List.pairwise_cons.mp hStrict).1 phantom ht
      exact False.elim ((not_lt_of_ge (Row.zero_le first.row)) hBelow)

/-- A real row-1 input guarantees a real highest row after sorting. -/
theorem FinishInput.sorted_real_top {mountain : Mountain} {cells : List Cell}
    (h : FinishInput mountain cells) :
    ∃ upper rest, (finishSort cells).reverse = upper :: rest ∧ upper.row ≠ 0 := by
  obtain ⟨bottom, hBottom, hBottomRow⟩ := h.bottom_mem
  have hMem : bottom ∈ (finishSort cells).reverse := List.mem_reverse.mpr
    ((finishSort_perm cells).mem_iff.mpr hBottom)
  have hDescending : (finishSort cells).reverse.Pairwise (fun a b => b.row < a.row) :=
    List.pairwise_reverse.mpr (finishSort_strict h.rows_nodup)
  cases hReverse : (finishSort cells).reverse with
  | nil => simp [hReverse] at hMem
  | cons upper rest =>
    refine ⟨upper, rest, rfl, ?_⟩
    rw [hReverse] at hMem hDescending
    rcases List.mem_cons.mp hMem with he | ht
    · have hRow : upper.row = 1 := by simpa only [he] using hBottomRow
      exact ne_of_gt (hRow ▸ Row.zero_lt_one)
    · have hAbove := (List.pairwise_cons.mp hDescending).1 bottom ht
      rw [hBottomRow] at hAbove
      exact ne_of_gt (Row.zero_lt_one.trans hAbove)

/-- The original finite-list geometry supplies the program's full readiness
condition, including its actual sorting and actual downward parent reads. -/
theorem FinishInput.ready {mountain : Mountain} {cells : List Cell}
    (h : FinishInput mountain cells) : FinishReady mountain cells := by
  obtain ⟨tail, hPhantom⟩ := h.sorted_phantom
  obtain ⟨upper, rest, hReverse, hReal⟩ := h.sorted_real_top
  change ∃ first tail upper rest,
    finishSort cells = first :: tail ∧ (finishSort cells).reverse = upper :: rest ∧
    first.row = 0 ∧ upper.row ≠ 0 ∧
    (∀ pair ∈ (finishSort cells).zip (finishSort cells).tail, pair.1.row ≠ pair.2.row) ∧
    BackfillReady mountain upper rest
  refine ⟨phantom, tail, upper, rest, hPhantom, hReverse, rfl, hReal,
    adjacent_rows_ne (finishSort_strict h.rows_nodup), ?_⟩
  apply backfillReady_of_strict
  · rw [← hReverse]
    exact List.pairwise_reverse.mpr (finishSort_strict h.rows_nodup)
  · intro cell hCell hAbove
    rw [← hReverse] at hCell
    exact h.parents_above_one cell
      ((finishSort_perm cells).mem_iff.mp (List.mem_reverse.mp hCell)) hAbove

/-- The actual `finish` succeeds from the unsorted local certificate and
preserves every sorted row/left endpoint, with all backfill sums verified. -/
theorem FinishInput.finish {mountain : Mountain} {cells : List Cell}
    (h : FinishInput mountain cells) :
    ∃ column, finish mountain cells = .ok column ∧
      ColumnShape (finishSort cells) column ∧ FinishedColumn mountain column :=
  finish_correct h.ready

/-- An actual readable parent already lies in the completed mountain; this
index bound need not be separately required by the finishing certificate. -/
theorem finish_parent_column_lt {mountain : Mountain} {ref : Ref} {parent : Cell}
    (hRead : lookup mountain ref = .ok parent) : ref.column < mountain.size := by
  obtain ⟨column, hColumn, _hCell⟩ := lookup_ok_iff.mp hRead
  exact (Array.getElem?_eq_some_iff.mp hColumn).1

end OmegaY.Expansion

#print axioms OmegaY.Expansion.FinishInput.ready
#print axioms OmegaY.Expansion.FinishInput.finish
