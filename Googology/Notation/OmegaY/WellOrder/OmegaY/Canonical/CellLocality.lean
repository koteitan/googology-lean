/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Canonical/CellLocality.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Canonical/CellLocality.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Locality

set_option backward.do.legacy false

/-!
# Relocating the same cell to a later column

The actual Q search reads the cell and its earlier columns.  Once its first
candidate is reached, all remaining searches run at unchanged references.
Consequently an already successful search survives moving the current cell
to a later column.  Orderedness, normality, and expansion termination are not
assumed; successful old searches themselves supply every leftward bound used.
-/

namespace OmegaY.Canonical

/-- A successful actual Q step is unchanged when its current cell is moved
rightward and every complete column strictly before the old cell is retained.
The old and new indices need not agree. -/
theorem nextCandidate_success_of_same_cell
    {before after : Mountain} {oldCurrent newCurrent found : Ref} {cell : Cell}
    (hOld : cellAt before oldCurrent = .ok cell)
    (hNew : cellAt after newCurrent = .ok cell)
    (hRight : oldCurrent.column ≤ newCurrent.column)
    (hColumns : ∀ c, c < oldCurrent.column → before[c]? = after[c]?)
    (hRun : nextCandidate before oldCurrent = .ok found) :
    nextCandidate after newCurrent = .ok found := by
  cases hLeft : cell.left with
  | none => simp [nextCandidate, hOld, hLeft] at hRun
  | some left =>
      by_cases hlt : left.column < oldCurrent.column
      · have hnewlt : left.column < newCurrent.column := lt_of_lt_of_le hlt hRight
        have hRead := cellAt_eq_of_column_eq (ref := left) (hColumns left.column hlt)
        have hOldNot : ¬ oldCurrent.column ≤ left.column := by omega
        have hNewNot : ¬ newCurrent.column ≤ left.column := by omega
        simpa only [nextCandidate, hOld, hNew, except_bind_ok, hLeft,
          not_lt, hOldNot, hNewNot, if_false, hRead, hColumns left.column hlt]
          using hRun
      · have hle : oldCurrent.column ≤ left.column := Nat.le_of_not_gt hlt
        simp [nextCandidate, hOld, hLeft, hle] at hRun

/-- At any fixed allowance, an old successful threshold search transfers.
The proof uses the first Q step and exact search locality at the common
candidate, rather than a new numerical-normality assumption. -/
theorem findParentAux_success_of_same_cell
    {before after : Mountain} {oldCurrent newCurrent found : Ref} {cell : Cell}
    (hOld : cellAt before oldCurrent = .ok cell)
    (hNew : cellAt after newCurrent = .ok cell)
    (hRight : oldCurrent.column ≤ newCurrent.column)
    (hColumns : ∀ c, c < oldCurrent.column → before[c]? = after[c]?)
    {threshold fuel : Nat}
    (hRun : findParentAux before threshold fuel oldCurrent = .ok found) :
    findParentAux after threshold fuel newCurrent = .ok found := by
  cases fuel with
  | zero => cases hRun
  | succ fuel =>
      rw [findParentAux] at hRun ⊢
      cases hQ : nextCandidate before oldCurrent with
      | error e => simp only [hQ, except_bind_error] at hRun; cases hRun
      | ok next =>
          have hQNew := nextCandidate_success_of_same_cell hOld hNew hRight hColumns hQ
          have hlt := nextCandidate_column_lt hQ
          have hRead := cellAt_eq_of_column_eq (ref := next) (hColumns next.column hlt)
          have hRest := findParentAux_eq_of_left_columns hRead
            (fun c hc => hColumns c (lt_trans hc hlt)) threshold fuel
          simpa only [hQ, hQNew, except_bind_ok, hRead, hRest] using hRun

/-- The original column bound remains sufficient after relocation; one need
not increase the allowance to the new column index. -/
theorem relocated_search_sufficient
    {before after : Mountain} {oldCurrent newCurrent found : Ref} {cell : Cell}
    (hOld : cellAt before oldCurrent = .ok cell)
    (hNew : cellAt after newCurrent = .ok cell)
    (hRight : oldCurrent.column ≤ newCurrent.column)
    (hColumns : ∀ c, c < oldCurrent.column → before[c]? = after[c]?)
    {threshold : Nat} (trace : FirstSmaller before threshold oldCurrent found)
    (fuel : Nat) (hFuel : oldCurrent.column ≤ fuel) :
    findParentAux after threshold fuel newCurrent = .ok found :=
  findParentAux_success_of_same_cell hOld hNew hRight hColumns (trace.run fuel hFuel)

theorem FirstSmaller.relocate
    {before after : Mountain} {oldCurrent newCurrent found : Ref} {cell : Cell}
    (trace : FirstSmaller before cell.value oldCurrent found)
    (hOld : cellAt before oldCurrent = .ok cell)
    (hNew : cellAt after newCurrent = .ok cell)
    (hRight : oldCurrent.column ≤ newCurrent.column)
    (hColumns : ∀ c, c < oldCurrent.column → before[c]? = after[c]?) :
    FirstSmaller after cell.value newCurrent found :=
  findParentAux_sound (relocated_search_sufficient hOld hNew hRight hColumns trace
    oldCurrent.column le_rfl)

/-- The actual parent, including its reference and every rejected candidate,
is unchanged.  The new search's own derived fuel is automatically sufficient. -/
theorem findParent_success_of_same_cell
    {before after : Mountain} {oldCurrent newCurrent found : Ref} {cell : Cell}
    (hOld : cellAt before oldCurrent = .ok cell)
    (hNew : cellAt after newCurrent = .ok cell)
    (hRight : oldCurrent.column ≤ newCurrent.column)
    (hColumns : ∀ c, c < oldCurrent.column → before[c]? = after[c]?)
    (hRun : findParent before oldCurrent = .ok found) :
    findParent after newCurrent = .ok found := by
  have trace := (findParent_iff hOld).mp hRun
  exact (findParent_iff hNew).mpr (trace.relocate hOld hNew hRight hColumns)

end OmegaY.Canonical

#print axioms OmegaY.Canonical.nextCandidate_success_of_same_cell
#print axioms OmegaY.Canonical.findParentAux_success_of_same_cell
#print axioms OmegaY.Canonical.relocated_search_sufficient
#print axioms OmegaY.Canonical.findParent_success_of_same_cell
