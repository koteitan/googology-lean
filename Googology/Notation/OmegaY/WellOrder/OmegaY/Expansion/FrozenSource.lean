/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/FrozenSource.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/FrozenSource.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.AppendLocality
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ContourPositive

set_option backward.do.legacy false

/-! Canonical facts about unchanged complete source columns survive in an
arbitrary extended ambient mountain. Appended columns need not be canonical.
The numerical interface deliberately excludes the real bottom at index one. -/

namespace OmegaY.Expansion

open Canonical

def SourceAboveBottomPositive (mountain : Mountain) (nodes : Column) : Prop :=
  ∀ index cell, nodes[index]? = some cell → 1 < index →
    ∃ parent parentCell, cell.left = some parent ∧
      lookup mountain parent = .ok parentCell ∧ 0 < parentCell.value

theorem PreservesColumns.column_read {before after : Mountain}
    (hPreserve : PreservesColumns before after) {column : Nat} {nodes : Column}
    (hColumn : before[column]? = some nodes) : after[column]? = some nodes := by
  exact (hPreserve column (Array.getElem?_eq_some_iff.mp hColumn).1).trans hColumn

theorem SourceAboveBottomPositive.preserve {before after : Mountain} {nodes : Column}
    (hPositive : SourceAboveBottomPositive before nodes)
    (hPreserve : PreservesColumns before after) : SourceAboveBottomPositive after nodes := by
  intro index cell hCell hIndex
  obtain ⟨parent, parentCell, hLeft, hRead, hPositive⟩ := hPositive index cell hCell hIndex
  obtain ⟨parentNodes, hParentColumn, hParentIndex⟩ := lookup_ok_iff.mp hRead
  exact ⟨parent, parentCell, hLeft,
    (hPreserve.lookup (Array.getElem?_eq_some_iff.mp hParentColumn).1).trans hRead,
    hPositive⟩

theorem build_source_above_bottom_positive {values : List Nat} {mountain : Mountain}
    (hBuild : Canonical.build values = .ok mountain)
    {sourceColumn : Nat} {nodes : Column}
    (hColumn : mountain[sourceColumn]? = some nodes) : SourceAboveBottomPositive mountain nodes := by
  intro index cell hCell hIndex
  have hRead : Canonical.cellAt mountain ⟨sourceColumn, index⟩ = .ok cell :=
    cellAt_ok_iff.mpr ⟨nodes, hColumn, hCell⟩
  obtain ⟨parent, parentCell, hLeft, hParent, hPositive, _⟩ :=
    build_above_bottom_stored_parent hBuild hRead hIndex
  exact ⟨parent, parentCell, hLeft, lookup_ok_iff.mpr (cellAt_ok_iff.mp hParent), hPositive⟩

/-- These are source facts; the ambient mountain is not assumed canonical or
normal, and its newly appended columns have no power-step premise. -/
theorem frozen_source_facts {values : List Nat} {source ambient : Mountain}
    (hBuild : Canonical.build values = .ok source)
    (hPreserve : PreservesColumns source ambient)
    {sourceColumn : Nat} {nodes : Column}
    (hColumn : source[sourceColumn]? = some nodes) :
    ambient[sourceColumn]? = some nodes ∧ TopOne nodes ∧ ColumnPowerSteps nodes ∧
      SourceAboveBottomPositive ambient nodes := by
  obtain ⟨built, hBuilt, _hValid, hTops⟩ := build_total (build_success_legal hBuild)
  have he : built = source := Except.ok.inj (hBuilt.symm.trans hBuild)
  subst built
  obtain ⟨hc, hNodes⟩ := Array.getElem?_eq_some_iff.mp hColumn
  exact ⟨hPreserve.column_read hColumn, hNodes ▸ hTops sourceColumn hc,
    build_column_power_steps_of_read hBuild hColumn,
    (build_source_above_bottom_positive hBuild hColumn).preserve hPreserve⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.SourceAboveBottomPositive.preserve
#print axioms OmegaY.Expansion.build_source_above_bottom_positive
#print axioms OmegaY.Expansion.frozen_source_facts
