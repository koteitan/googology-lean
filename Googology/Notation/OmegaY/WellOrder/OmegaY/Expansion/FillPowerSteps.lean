/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/FillPowerSteps.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/FillPowerSteps.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ContourPowerSteps
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.FillEndpoints

set_option backward.do.legacy false

/-!
# Power steps along reference-fill ladders

The executable fill loop stores each individual ladder in descending order,
while iterating its parent intervals in ascending order. We reverse each
ladder separately. Reversing the entire loop output would be incorrect.
-/

namespace OmegaY.Expansion

open Canonical

theorem RowPowerStep.lt {lower upper : Row} (h : RowPowerStep lower upper) :
    lower < upper := by
  rw [h]
  exact Row.lt_bump _ _

theorem RowsPowerSteps.strict {rows : List Row} (h : RowsPowerSteps rows) :
    rows.Pairwise (· < ·) := by
  apply List.isChain_iff_pairwise.mp
  exact h.imp (fun _ _ hStep => hStep.lt)

theorem fillLadder_reverse_eq (lower upper : Row) :
    (Row.fillLadder lower upper).reverse =
      (List.range (Row.jump lower upper)).map (Row.bump lower) := by
  simp [Row.fillLadder]

/-- The seed-to-first rung and all consecutive rungs are power steps. -/
theorem fillLadder_reverse_power_steps (lower upper : Row) :
    RowsPowerSteps (lower :: (Row.fillLadder lower upper).reverse) := by
  rw [fillLadder_reverse_eq]
  apply List.isChain_iff_getElem.mpr
  intro i hi
  cases i with
  | zero =>
    simpa only [List.getElem_cons_zero, List.getElem_cons_succ,
      List.getElem_map, List.getElem_range] using RowPowerStep.bump lower 0
  | succ i =>
    simp only [List.getElem_cons_succ, List.getElem_map, List.getElem_range]
    have h := RowPowerStep.bump (Row.bump lower i) (i + 1)
    rwa [Row.fillLadder_adjacent] at h

/-- A source power step makes the last rung exactly the next parent row. -/
theorem fillLadder_reverse_last {lower upper : Row} (hStep : RowPowerStep lower upper) :
    (Row.fillLadder lower upper).reverse.getLast? = some upper := by
  have hn : Row.jump lower upper ≠ 0 := by
    intro he
    exact (ne_of_lt hStep.lt) (Row.jump_eq_zero.mp he)
  rw [fillLadder_reverse_eq, List.getLast?_map, List.getLast?_range]
  simp only [hn, ↓reduceIte, Option.map_some]
  exact congrArg some hStep.symm

/-- Join two power-step paths at the same actual boundary, without inserting
the boundary a second time. -/
theorem RowsPowerSteps.append_at {start middle : Row} {before after : List Row}
    (hBefore : RowsPowerSteps (start :: before))
    (hLast : (start :: before).getLast? = some middle)
    (hAfter : RowsPowerSteps (middle :: after)) :
    RowsPowerSteps (start :: (before ++ after)) := by
  apply RowsPowerSteps.append hBefore hAfter.tail
  intro lower hl upper hu
  have he : middle = lower := by simpa only [hLast, Option.mem_some_iff] using hl
  subst lower
  exact hAfter.rel_head? hu

/-- Fill consecutive parent intervals, preserving their ascending interval
order and reversing only each ladder. No sorting is hidden in this definition. -/
def fillPath : Row → List Row → List Row
  | _, [] => []
  | lower, upper :: rest =>
      (Row.fillLadder lower upper).reverse ++ fillPath upper rest

theorem fillPath_last (start : Row) (rows : List Row)
    (hPower : RowsPowerSteps (start :: rows)) :
    (start :: fillPath start rows).getLast? = (start :: rows).getLast? := by
  induction rows generalizing start with
  | nil => rfl
  | cons upper rest ih =>
    have hStep : RowPowerStep start upper := hPower.rel
    have hLadderLast := fillLadder_reverse_last hStep
    have hStartLast : (start :: (Row.fillLadder start upper).reverse).getLast? = some upper := by
      cases hList : (Row.fillLadder start upper).reverse with
      | nil => simp [hList] at hLadderLast
      | cons head tail => simpa only [hList, List.getLast?_cons_cons] using hLadderLast
    have hRest := ih upper hPower.tail
    cases hTail : fillPath upper rest with
    | nil =>
      simp only [fillPath, hTail, List.append_nil, List.getLast?_cons_cons]
      rw [hStartLast]
      simpa only [hTail, List.getLast?_singleton] using hRest
    | cons head tail =>
      change ((start :: (Row.fillLadder start upper).reverse) ++ fillPath upper rest).getLast? = _
      rw [hTail, List.getLast?_append_of_ne_nil _ (by simp)]
      simpa only [hTail, List.getLast?_cons_cons] using hRest

theorem fillPath_power_steps (start : Row) (rows : List Row)
    (hPower : RowsPowerSteps (start :: rows)) :
    RowsPowerSteps (start :: fillPath start rows) := by
  induction rows generalizing start with
  | nil => exact .singleton _
  | cons upper rest ih =>
    have hStep : RowPowerStep start upper := hPower.rel
    have hLast := fillLadder_reverse_last hStep
    have hStartLast : (start :: (Row.fillLadder start upper).reverse).getLast? = some upper := by
      cases hList : (Row.fillLadder start upper).reverse with
      | nil => simp [hList] at hLast
      | cons head tail => simpa only [hList, List.getLast?_cons_cons] using hLast
    exact RowsPowerSteps.append_at (fillLadder_reverse_power_steps start upper) hStartLast
      (ih upper hPower.tail)

/-- The actual one-interval chunk differs from its ascending power-step path
only by list permutation. The actual parent read fixes the stored left leg. -/
theorem fillChunk_power_steps {nodes : Column} {column index : Nat} {lower upper : Cell}
    (hLower : nodes[index]? = some lower) (hUpper : nodes[index + 1]? = some upper)
    (hPower : ColumnPowerSteps nodes) {low high : Row}
    (hEligible : low ≤ lower.row ∧ lower.row < high) :
    let ascending := ((fillChunk nodes column low high index).map Cell.row).reverse
    RowsPowerSteps (lower.row :: ascending) ∧ ascending.getLast? = some upper.row ∧
      ascending.Perm ((fillChunk nodes column low high index).map Cell.row) := by
  dsimp only
  rw [fillChunk_rows]
  simp only [hLower, hUpper, Option.getD_some, hEligible]
  exact ⟨fillLadder_reverse_power_steps _ _,
    fillLadder_reverse_last (hPower index lower upper hLower hUpper), List.reverse_perm _⟩

/-- The ascending candidate order reverses every ladder independently. -/
def fillCellsAscendingRows (nodes : Column) (column : Nat) (low high : Row) : List Row :=
  (List.range nodes.size).flatMap fun i =>
    ((fillChunk nodes column low high i).map Cell.row).reverse

theorem fillCellsAscendingRows_perm (nodes : Column) (column : Nat) (low high : Row) :
    (fillCellsAscendingRows nodes column low high).Perm
      ((fillCells nodes column low high).map Cell.row) := by
  rw [fillCells, List.map_flatMap]
  exact List.Perm.flatMap_left _ (fun _ _ => List.reverse_perm _)

theorem fillChunk_reverse_strict (nodes : Column) (column : Nat) (low high : Row) (index : Nat) :
    (((fillChunk nodes column low high index).map Cell.row).reverse).Pairwise (· < ·) := by
  rw [fillChunk_rows]
  split
  · exact (fillLadder_reverse_power_steps _ _).strict.tail
  · exact .nil

theorem fillCellsAscendingRows_strict {nodes : Column} (hStrict : FillRowsStrict nodes)
    {column capIndex : Nat} {cap : Cell} {low high : Row}
    (hCap : nodes[capIndex]? = some cap) (hHigh : high ≤ cap.row) :
    (fillCellsAscendingRows nodes column low high).Pairwise (· < ·) := by
  apply List.pairwise_flatMap.mpr
  refine ⟨fun i _ => fillChunk_reverse_strict _ _ _ _ i, ?_⟩
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij a ha b hb
  simp only [List.length_range, List.getElem_range] at hi hj ha hb
  obtain ⟨ca, hca, hcaRow⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
  obtain ⟨cb, hcb, hcbRow⟩ := List.mem_map.mp (List.mem_reverse.mp hb)
  obtain ⟨pa, ua, hpa, hua, _, _, hpua, _, hla, _, _⟩ :=
    mem_fillChunk hStrict hCap hHigh hi hca
  obtain ⟨pb, ub, hpb, hub, _, _, hpub, _, hlb, _, _⟩ :=
    mem_fillChunk hStrict hCap hHigh hj hcb
  have hMiddle : ua.row ≤ pb.row := by
    rcases eq_or_lt_of_le (show i + 1 ≤ j by omega) with he | hl
    · have heq : ua = pb := Option.some.inj (hua.symm.trans (he ▸ hpb))
      exact le_of_eq (congrArg Cell.row heq)
    · exact (hStrict _ _ _ _ hua hpb hl).le
  simpa only [hcaRow, hcbRow] using Row.fillLadders_separated hpua hMiddle hpub hla hlb

/-- Any increasing ordering of the actual fill rows has exactly the
per-interval ascending order above. This applies in particular to the actual
finisher's sorted row list, once its existing permutation theorem is supplied. -/
theorem fillCellsAscendingRows_eq_of_sorted_perm {nodes : Column}
    (hStrict : FillRowsStrict nodes) {column capIndex : Nat} {cap : Cell} {low high : Row}
    (hCap : nodes[capIndex]? = some cap) (hHigh : high ≤ cap.row) {sorted : List Row}
    (hPerm : sorted.Perm ((fillCells nodes column low high).map Cell.row))
    (hSorted : sorted.Pairwise (· < ·)) :
    sorted = fillCellsAscendingRows nodes column low high := by
  exact (hPerm.trans (fillCellsAscendingRows_perm nodes column low high).symm).eq_of_pairwise'
    hSorted (fillCellsAscendingRows_strict hStrict hCap hHigh)

end OmegaY.Expansion

#print axioms OmegaY.Expansion.fillLadder_reverse_power_steps
#print axioms OmegaY.Expansion.fillPath_power_steps
#print axioms OmegaY.Expansion.fillChunk_power_steps
#print axioms OmegaY.Expansion.fillCellsAscendingRows_eq_of_sorted_perm
