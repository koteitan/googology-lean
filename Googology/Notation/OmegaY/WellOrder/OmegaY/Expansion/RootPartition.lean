/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/RootPartition.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/RootPartition.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.RootIntervals

set_option backward.do.legacy false

/-! Exact position of the boundary associated with a root-prefix row in
the executable boundary list. Every later boundary is at or below that
row, so its selected strict-below reference cannot qualify for referenceAt. -/

namespace OmegaY.Expansion

open Canonical Geometry

def nonzeroRows (cells : List Cell) : List Row :=
  cells.filterMap fun cell => if cell.row = 0 then none else some cell.row

theorem root_prefix_rows_bound {mountain : Mountain} {column : Nat} {nodes : Column}
    (hValid : ColumnValid mountain column nodes) {index : Nat} {lower : Cell}
    (hLower : nodes[index]? = some lower) :
    ∀ row ∈ nonzeroRows ((nodes.toList.take (index + 1)).reverse), row ≤ lower.row := by
  intro row hRow
  obtain ⟨cell, hMem, hMap⟩ := List.mem_filterMap.mp hRow
  have he : cell.row = row := by
    by_cases hz : cell.row = 0
    · simp [hz] at hMap
    · simpa [hz] using hMap
  obtain ⟨j, hj, hCell⟩ := List.mem_take_iff_getElem.mp (List.mem_reverse.mp hMem)
  have hRead : nodes[j]? = some cell := by
    have hList : nodes.toList[j]? = some cell :=
      List.getElem?_eq_some_iff.mpr ⟨by omega, hCell⟩
    simpa only [Array.getElem?_toList] using hList
  have hji : j ≤ index := by omega
  rw [← he]
  rcases eq_or_lt_of_le hji with hEq | hLt
  · rw [hEq] at hRead
    exact (congrArg Cell.row (Option.some.inj (hRead.symm.trans hLower))).le
  · exact (hValid.rows_strict _ _ _ _ hRead hLower hLt).le

/-- This is a split of the actual boundary list, not just the existence of
some boundary in it. The middle entry is precisely one power above lower. -/
theorem Preparation.root_boundary_partition {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {nodes : Column}
    (hColumn : p.initial[p.root.column]? = some nodes)
    {index : Nat} {lower : Cell} (hLower : nodes[index]? = some lower)
    (hIndex : index ≤ p.root.index) :
    ∃ earlier ceiling later degree,
      p.boundaries = earlier ++ ceiling :: later ∧
      ceiling = Row.bump lower.row degree ∧ ceiling ≤ p.lastTop.row ∧
      (∀ row ∈ later, row ≤ lower.row) ∧
      ∀ higherIndex higherCell, index < higherIndex → higherIndex ≤ p.root.index →
        nodes[higherIndex]? = some higherCell → ceiling ≤ higherCell.row := by
  obtain ⟨rootNodes, hRootColumn, hRootCell⟩ := cellAt_ok_iff.mp p.initial_root
  have he : rootNodes = nodes := Option.some.inj (hRootColumn.symm.trans hColumn)
  subst rootNodes
  obtain ⟨hc, hNodes⟩ := Array.getElem?_eq_some_iff.mp hColumn
  have hValid : ColumnValid p.initial p.root.column nodes :=
    hNodes ▸ p.initial_valid p.root.column hc
  by_cases hi : index = p.root.index
  · subst index
    have hLowerEq : lower = p.rootCell := Option.some.inj (hLower.symm.trans hRootCell)
    obtain ⟨g⟩ := p.root_geometry hLast
    refine ⟨[], p.lastTop.row, nonzeroRows ((nodes.toList.take (p.root.index + 1)).reverse),
      Row.jump ((Frame.ofMountain p.initial).height g.lower) p.rootCell.row,
      p.boundaries_of_column hColumn, ?_, le_rfl, root_prefix_rows_bound hValid hLower, ?_⟩
    · rw [hLowerEq, g.top_row, B_from_right]
    · intro higherIndex higherCell hGt hLe hRead
      omega
  · have hr := (Array.getElem?_eq_some_iff.mp hRootCell).1
    have hn : index + 1 < nodes.size := by omega
    let upper : Cell := nodes[index + 1]
    have hUpper : nodes[index + 1]? = some upper := Array.getElem?_eq_getElem hn
    have hStep := build_column_power_steps_of_read p.initial_build hColumn index lower upper hLower hUpper
    have hStrict := hValid.rows_strict _ _ _ _ hLower hUpper (Nat.lt_succ_self index)
    have hNonzero : upper.row ≠ 0 := ne_of_gt ((Row.zero_le lower.row).trans_lt hStrict)
    let suffix := (nodes.toList.drop (index + 2)).take (p.root.index - index - 1)
    have hPrefix : nodes.toList.take (p.root.index + 1) =
        (nodes.toList.take (index + 1) ++ [upper]) ++ suffix := by
      have hLength : p.root.index + 1 = (index + 2) + (p.root.index - index - 1) := by omega
      rw [hLength, List.take_add]
      have hTake : nodes.toList.take (index + 2) = nodes.toList.take (index + 1) ++ [upper] := by
        simp only [List.take_add_one, Array.getElem?_toList, hUpper, Option.toList_some]
      rw [hTake]
    refine ⟨p.lastTop.row :: nonzeroRows suffix.reverse, upper.row,
      nonzeroRows ((nodes.toList.take (index + 1)).reverse),
      Row.jump lower.row upper.row - 1, ?_, hStep, ?_, root_prefix_rows_bound hValid hLower, ?_⟩
    · rw [p.boundaries_of_column hColumn, hPrefix]
      simp [nonzeroRows, List.reverse_append, List.filterMap_append, hNonzero]
    · exact (p.root_prefix_row_le hColumn hUpper (by omega)).trans (p.root_row_lt_top hLast).le
    · intro higherIndex higherCell hGt _hLe hRead
      by_cases hEq : index + 1 = higherIndex
      · rw [hEq] at hUpper
        exact (congrArg Cell.row (Option.some.inj (hUpper.symm.trans hRead))).le
      · exact (hValid.rows_strict _ _ _ _ hUpper hRead (by omega)).le

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.root_boundary_partition
