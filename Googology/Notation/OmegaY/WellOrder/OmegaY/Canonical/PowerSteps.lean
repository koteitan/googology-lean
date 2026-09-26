/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Canonical/PowerSteps.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Canonical/PowerSteps.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Domain

set_option backward.do.legacy false

/-! Each actual adjacent row is one ordinal power step. This is weaker than
normality: it specifies rows only and does not assert any numerical search
rule for a later copied column. The auxiliary-to-bottom step is included. -/

namespace OmegaY.Canonical

def ColumnPowerSteps (column : Column) : Prop :=
  ∀ i lower upper, column[i]? = some lower → column[i + 1]? = some upper →
    upper.row = Row.bump lower.row (Row.jump lower.row upper.row - 1)

theorem zero_bump_zero : Row.bump (0 : Row) 0 = 1 := by
  apply Row.ext
  intro i
  cases i with
  | zero => change Row.coeff (Row.bump 0 0) 0 = Row.coeff (1 : Nat) 0; simp
  | succ i => change Row.coeff (Row.bump 0 0) (i+1) = Row.coeff (1 : Nat) (i+1); simp

theorem build_column_power_steps {values : List Nat} {mountain : Mountain}
    (hBuild : build values = .ok mountain) (column : Nat) (hc : column < mountain.size) :
    ColumnPowerSteps mountain[column] := by
  have hValid := build_valid_of_success hBuild
  intro i lower upper hLower hUpper
  cases i with
  | zero =>
    have hPhantom : lower = phantom :=
      Option.some.inj (hLower.symm.trans (hValid column hc).phantom)
    have hBottom : upper.row = 1 := (hValid column hc).bottom_row upper hUpper
    rw [hPhantom, hBottom]
    change (1 : Row) = Row.bump 0 (Row.jump 0 1 - 1)
    rw [← zero_bump_zero, Row.jump_bump]
  | succ i =>
    obtain ⟨_, parentRef, parent, _hLeft, _hFind, _hRead, hRow, _hValue, _hStored⟩ :=
      build_steps hBuild column hc (i + 1) lower upper hLower hUpper (by omega)
    rw [hRow]
    unfold Row.B
    rw [Row.jump_bump]
    simp

theorem build_column_power_steps_of_read {values : List Nat} {mountain : Mountain}
    (hBuild : build values = .ok mountain) {index : Nat} {column : Column}
    (hColumn : mountain[index]? = some column) : ColumnPowerSteps column := by
  obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.mp hColumn
  exact he ▸ build_column_power_steps hBuild index hi

/-- The row produced by B can equally be expressed as a power step from
its right endpoint. In particular the old top forms a power interval above
the actual bad root, even when its own column's lower node is higher. -/
theorem B_from_right (a b : Row) : Row.B a b = Row.bump b (Row.jump a b) :=
  Row.bump_eq_of_jump_le (Nat.le_refl _)

end OmegaY.Canonical

#print axioms OmegaY.Canonical.build_column_power_steps
#print axioms OmegaY.Canonical.B_from_right
