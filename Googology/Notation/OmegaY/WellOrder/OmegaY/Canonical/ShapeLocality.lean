/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Canonical/ShapeLocality.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Canonical/ShapeLocality.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Locality

set_option backward.do.legacy false

/-! A fixed-threshold search ignores the current cell's numerical value.
This is the comparison needed while two decrement builds still share rows
and left endpoints but have current values differing by one. After the first
candidate, all cells are in the common complete left columns. -/

namespace OmegaY.Canonical

theorem nextCandidate_eq_of_same_shape {before after : Mountain} {current : Ref}
    {oldCell newCell : Cell}
    (hOld : cellAt before current = .ok oldCell)
    (hNew : cellAt after current = .ok newCell)
    (hRow : oldCell.row = newCell.row) (hLeft : oldCell.left = newCell.left)
    (hColumns : ∀ c, c < current.column → before[c]? = after[c]?) :
    nextCandidate before current = nextCandidate after current := by
  cases hl : newCell.left with
  | none => simp [nextCandidate, hOld, hNew, hLeft, hl]
  | some left =>
    by_cases hlt : left.column < current.column
    · have hCell := cellAt_eq_of_column_eq (ref := left) (hColumns left.column hlt)
      simp only [nextCandidate, hOld, hNew, except_bind_ok, hLeft, hl,
        hlt, not_true_eq_false, ↓reduceIte]
      rw [hCell, hColumns left.column hlt, hRow]
    · have hle : current.column ≤ left.column := Nat.le_of_not_gt hlt
      simp [nextCandidate, hOld, hNew, hLeft, hl, hle]

/-- Both the exact successful result and every error are preserved at a
fixed threshold and fuel. In particular no decrease-case success is assumed. -/
theorem findParentAux_eq_of_same_shape {before after : Mountain} {current : Ref}
    {oldCell newCell : Cell}
    (hOld : cellAt before current = .ok oldCell)
    (hNew : cellAt after current = .ok newCell)
    (hRow : oldCell.row = newCell.row) (hLeft : oldCell.left = newCell.left)
    (hColumns : ∀ c, c < current.column → before[c]? = after[c]?)
    (threshold fuel : Nat) :
    findParentAux before threshold fuel current =
      findParentAux after threshold fuel current := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have hNext := nextCandidate_eq_of_same_shape hOld hNew hRow hLeft hColumns
    cases hn : nextCandidate after current with
    | error e => simp [findParentAux, hNext, hn]
    | ok next =>
      have hlt := nextCandidate_column_lt hn
      have hCell := cellAt_eq_of_column_eq (ref := next) (hColumns next.column hlt)
      have hRest := findParentAux_eq_of_left_columns hCell
        (fun c hc => hColumns c (Nat.lt_trans hc hlt)) threshold fuel
      simp only [findParentAux, hNext, hn, except_bind_ok, hCell, hRest]

/-- The new numerical parent is exactly the old diagram's search at the new
threshold. It is not asserted to equal the old numerical parent. -/
theorem findParent_eq_lowered_search {before after : Mountain} {current : Ref}
    {oldCell newCell : Cell}
    (hOld : cellAt before current = .ok oldCell)
    (hNew : cellAt after current = .ok newCell)
    (hRow : oldCell.row = newCell.row) (hLeft : oldCell.left = newCell.left)
    (hColumns : ∀ c, c < current.column → before[c]? = after[c]?) :
    findParent after current = findParentAux before newCell.value current.column current := by
  simp only [findParent, hNew, except_bind_ok]
  exact (findParentAux_eq_of_same_shape hOld hNew hRow hLeft hColumns _ _).symm

end OmegaY.Canonical

#print axioms OmegaY.Canonical.findParentAux_eq_of_same_shape
#print axioms OmegaY.Canonical.findParent_eq_lowered_search
