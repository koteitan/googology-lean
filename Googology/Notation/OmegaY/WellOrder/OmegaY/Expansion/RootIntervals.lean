/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/RootIntervals.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/RootIntervals.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.PowerSteps
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.PreparedBoundaries

set_option backward.do.legacy false

/-! Actual successive root-prefix rows, followed by the old final top,
form single-power intervals. The initial strict-below references lie in
these intervals because the reduced last column contains their lower ends.
This does not assume dense ordinal rows or preservation by later copies. -/

namespace OmegaY.Expansion

open Canonical Geometry

theorem Preparation.root_prefix_row_le {front : List Nat} {last : Nat}
    (p : Preparation front last) {nodes : Column}
    (hColumn : p.initial[p.root.column]? = some nodes)
    {index : Nat} {cell : Cell} (hCell : nodes[index]? = some cell)
    (hIndex : index ≤ p.root.index) : cell.row ≤ p.rootCell.row := by
  obtain ⟨rootNodes, hRootColumn, hRootCell⟩ := cellAt_ok_iff.mp p.initial_root
  have he : rootNodes = nodes := Option.some.inj (hRootColumn.symm.trans hColumn)
  subst rootNodes
  obtain ⟨hc, hNodes⟩ := Array.getElem?_eq_some_iff.mp hColumn
  have hValid : ColumnValid p.initial p.root.column nodes :=
    hNodes ▸ p.initial_valid p.root.column hc
  by_cases hi : index = p.root.index
  · subst index
    have he := Option.some.inj (hCell.symm.trans hRootCell)
    exact (congrArg Cell.row he).le
  · exact (hValid.rows_strict _ _ _ _ hCell hRootCell (by omega)).le

theorem Preparation.root_prefix_mem_boundaries {front : List Nat} {last : Nat}
    (p : Preparation front last) {nodes : Column}
    (hColumn : p.initial[p.root.column]? = some nodes)
    {index : Nat} {cell : Cell} (hCell : nodes[index]? = some cell)
    (hIndex : index ≤ p.root.index) (hNonzero : cell.row ≠ 0) :
    cell.row ∈ p.boundaries := by
  rw [p.boundaries_of_column hColumn]
  apply List.mem_cons_of_mem
  apply List.mem_filterMap.mpr
  refine ⟨cell, List.mem_reverse.mpr ?_, by simp [hNonzero]⟩
  apply List.mem_of_getElem? (i := index)
  rw [List.getElem?_take]
  simp only [Array.getElem?_toList, hCell, show index < p.root.index + 1 by omega, ↓reduceIte]

/-- For every actual root-prefix node, its next root node (or the old top
at the root itself) is a positive boundary one ordinal power above it. -/
theorem Preparation.root_interval {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {nodes : Column}
    (hColumn : p.initial[p.root.column]? = some nodes)
    {index : Nat} {lower : Cell} (hLower : nodes[index]? = some lower)
    (hIndex : index ≤ p.root.index) :
    ∃ ceiling degree, ceiling ∈ p.boundaries ∧
      ceiling = Row.bump lower.row degree ∧ ceiling ≤ p.lastTop.row := by
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
    refine ⟨p.lastTop.row, Row.jump ((Frame.ofMountain p.initial).height g.lower) p.rootCell.row,
      by simp [Preparation.boundaries], ?_, le_rfl⟩
    rw [hLowerEq, g.top_row, B_from_right]
  · have hr := (Array.getElem?_eq_some_iff.mp hRootCell).1
    have hn : index + 1 < nodes.size := by omega
    let upper : Cell := nodes[index + 1]
    have hUpper : nodes[index + 1]? = some upper := Array.getElem?_eq_getElem hn
    have hStep := build_column_power_steps_of_read p.initial_build hColumn index lower upper hLower hUpper
    have hStrict := hValid.rows_strict _ _ _ _ hLower hUpper (Nat.lt_succ_self index)
    refine ⟨upper.row, Row.jump lower.row upper.row - 1,
      p.root_prefix_mem_boundaries hColumn hUpper (by omega)
        (ne_of_gt ((Row.zero_le lower.row).trans_lt hStrict)), hStep, ?_⟩
    exact (p.root_prefix_row_le hColumn hUpper (by omega)).trans
      (p.root_row_lt_top hLast).le

/-- Actual initial selection supplies an actual cell inside each root
power interval, including the auxiliary interval starting at zero. -/
theorem Preparation.initial_root_interval {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {nodes : Column}
    (hColumn : p.initial[p.root.column]? = some nodes)
    {index : Nat} {lower : Cell} (hLower : nodes[index]? = some lower)
    (hIndex : index ≤ p.root.index) :
    ∃ ceiling degree found foundCell, ceiling ∈ p.boundaries ∧
      ceiling = Row.bump lower.row degree ∧ ceiling ≤ p.lastTop.row ∧
      below p.reduced (p.reduced.size - 1) ceiling = .ok found ∧
      Canonical.cellAt p.reduced found = .ok foundCell ∧
      lower.row ≤ foundCell.row ∧ foundCell.row < ceiling := by
  obtain ⟨ceiling, degree, hMem, hPower, hTop⟩ := p.root_interval hLast hColumn hLower hIndex
  have hBelow : lower.row < ceiling := hPower ▸ Row.lt_bump lower.row degree
  by_cases hi : index = 0
  · subst index
    obtain ⟨hc, hNodes⟩ := Array.getElem?_eq_some_iff.mp hColumn
    have hPhantom : nodes[0]? = some phantom := by
      rw [← hNodes]
      exact (p.initial_valid p.root.column hc).phantom
    have hLowerEq : lower = phantom := Option.some.inj (hLower.symm.trans hPhantom)
    obtain ⟨found, cell, hFound, hRead, _, hAbove, hBound⟩ := below_between p.reduced_valid
      p.reduced_last_phantom_read (by simpa only [hLowerEq] using hBelow)
    have hs := build_size p.reduced_build
    have hLastColumn : front.length = p.reduced.size - 1 := by
      simp only [List.length_append, List.length_singleton] at hs
      omega
    exact ⟨ceiling, degree, found, cell, hMem, hPower, hTop,
      by simpa only [hLastColumn] using hFound, hRead, hLowerEq ▸ hAbove, hBound⟩
  · have hRead : Canonical.cellAt p.initial ⟨p.root.column, index⟩ = .ok lower :=
      cellAt_ok_iff.mpr ⟨nodes, hColumn, hLower⟩
    obtain ⟨w, hRef, hCell⟩ := Canonical.frame_node_of_cellAt hRead
    have hReal : Frame.Real w := by
      have hh := congrArg Ref.index hRef
      unfold Frame.Real
      dsimp only [Frame.ref] at hh
      omega
    have hHeight : (Frame.ofMountain p.initial).height w = lower.row := congrArg Cell.row hCell
    have hColumnEq : w.1.val = p.root.column := congrArg Ref.column hRef
    obtain ⟨found, cell, hFound, hFoundCell, hAbove, hBound⟩ :=
      p.reference_above_root_row hLast w hReal hColumnEq
        (hHeight.trans_le (p.root_prefix_row_le hColumn hLower hIndex))
        (hHeight.trans_lt hBelow)
    exact ⟨ceiling, degree, found, cell, hMem, hPower, hTop, hFound, hFoundCell,
      by simpa only [hHeight] using hAbove, hBound⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.root_interval
#print axioms OmegaY.Expansion.Preparation.initial_root_interval
