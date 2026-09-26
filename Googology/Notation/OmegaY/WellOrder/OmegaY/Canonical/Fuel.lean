/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Canonical/Fuel.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Canonical/Fuel.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Search

set_option backward.do.legacy false

/-!
# The value-derived column allowance is sufficient

This module uses the actual successful parent search to prove strict decrease
of the current positive value.  Once the allowance is at least `value - 1`,
adding any further allowance leaves the complete result unchanged, including
explicit structural/search failures.  Thus the chosen value-derived allowance
does not truncate a longer successful construction.  No parent-existence or
legal-input success theorem is assumed here.
-/

namespace OmegaY.Canonical

theorem cellAt_current_top {leftColumns : Mountain} {column : Column} {child : Cell}
    (hTop : column.back? = some child) :
    cellAt (leftColumns.push column) ⟨leftColumns.size, column.size - 1⟩ = .ok child := by
  have hc : column[column.size - 1]? = some child := by
    simpa only [Array.back?_eq_getElem?] using hTop
  simp [cellAt, hc]

/-- Every actual successful difference step produces a positive smaller value. -/
theorem difference_value_bounds {leftColumns : Mountain} {column : Column}
    {child parent : Cell} {parentRef : Ref}
    (hTop : column.back? = some child)
    (hParent : findParent (leftColumns.push column)
      ⟨leftColumns.size, column.size - 1⟩ = .ok parentRef)
    (hCell : cellAt (leftColumns.push column) parentRef = .ok parent) :
    0 < child.value - parent.value ∧ child.value - parent.value < child.value := by
  obtain ⟨found, hFound, hPositive, hSmall⟩ :=
    findParent_result (cellAt_current_top hTop) hParent
  have he : found = parent := Except.ok.inj (hFound.symm.trans hCell)
  subst found
  omega

theorem growColumn_top {leftColumns : Mountain} {column : Column} {child : Cell}
    (fuel : Nat) (hTop : column.back? = some child) (hOne : child.value = 1) :
    growColumn leftColumns fuel column = .ok column := by
  rw [growColumn]
  simp [hTop, hOne]

theorem growColumn_step {leftColumns : Mountain} {column : Column} {child : Cell}
    (fuel : Nat) (hTop : column.back? = some child)
    (hOne : child.value ≠ 1) (hZero : child.value ≠ 0) :
    growColumn leftColumns (fuel + 1) column = (do
      let parentRef ← findParent (leftColumns.push column)
        ⟨leftColumns.size, column.size - 1⟩
      let parent ← cellAt (leftColumns.push column) parentRef
      growColumn leftColumns fuel (column.push {
        row := Row.B child.row parent.row
        value := child.value - parent.value
        left := some parentRef })) := by
  rw [growColumn]
  simp [hTop, hOne, hZero]

/-- Additional column allowance cannot change the result once the current
positive value minus one is available.  This is unconditional on success of
the intervening structural searches. -/
theorem growColumn_fuel_stable {leftColumns : Mountain} {fuel extra : Nat}
    {column : Column} {child : Cell}
    (hTop : column.back? = some child) (hPositive : 0 < child.value)
    (hEnough : child.value - 1 ≤ fuel) :
    growColumn leftColumns fuel column = growColumn leftColumns (fuel + extra) column := by
  induction fuel generalizing column child with
  | zero =>
      have hOne : child.value = 1 := by omega
      rw [growColumn_top _ hTop hOne, growColumn_top _ hTop hOne]
  | succ fuel ih =>
      by_cases hOne : child.value = 1
      · rw [growColumn_top _ hTop hOne, growColumn_top _ hTop hOne]
      · have hZero : child.value ≠ 0 := by omega
        rw [Nat.succ_add,
          growColumn_step fuel hTop hOne hZero,
          growColumn_step (fuel + extra) hTop hOne hZero]
        cases hParent : findParent (leftColumns.push column)
            ⟨leftColumns.size, column.size - 1⟩ with
        | error error =>
            simp
        | ok parentRef =>
            cases hCell : cellAt (leftColumns.push column) parentRef with
            | error error =>
                simp [hCell]
            | ok parent =>
                have hBounds := difference_value_bounds hTop hParent hCell
                let next : Cell := {
                  row := Row.B child.row parent.row
                  value := child.value - parent.value
                  left := some parentRef }
                have hNext : (column.push next).back? = some next := Array.back?_push
                have hRun := ih (column := column.push next) (child := next) hNext
                  hBounds.1 (show next.value - 1 ≤ fuel by dsimp [next]; omega)
                simpa [hParent, hCell, next] using hRun

/-- The executable `buildColumn` uses a sufficient value-derived allowance;
no larger finite allowance can turn its failure into success or change output. -/
theorem buildColumn_eq_larger_allowance {leftColumns : Mountain} {value extra : Nat}
    (hPositive : 0 < value) :
    buildColumn leftColumns value = growColumn leftColumns (value - 1 + extra)
      (initialColumn leftColumns.size value) := by
  have hZero : value ≠ 0 := by omega
  unfold buildColumn
  rw [if_neg hZero]
  apply growColumn_fuel_stable
    (child := ⟨1, value, if leftColumns.size = 0 then none else some ⟨leftColumns.size - 1, 0⟩⟩)
  · simp [initialColumn]
  · exact hPositive
  · exact Nat.le_refl _

/-- Explicit no-lost-success corollary: if a larger value-derived allowance
succeeds, the exact executable builder already returns that same column. -/
theorem buildColumn_success_of_larger_allowance
    {leftColumns : Mountain} {value extra : Nat} {result : Column}
    (hPositive : 0 < value)
    (hSuccess : growColumn leftColumns (value - 1 + extra)
      (initialColumn leftColumns.size value) = .ok result) :
    buildColumn leftColumns value = .ok result :=
  (buildColumn_eq_larger_allowance hPositive).trans hSuccess

#print axioms difference_value_bounds
#print axioms growColumn_fuel_stable
#print axioms buildColumn_eq_larger_allowance
#print axioms buildColumn_success_of_larger_allowance

end OmegaY.Canonical
