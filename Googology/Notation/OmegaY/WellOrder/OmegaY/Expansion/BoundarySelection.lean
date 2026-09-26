/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/BoundarySelection.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/BoundarySelection.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.Selection
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Invariant

set_option backward.do.legacy false

/-! Total boundary selection on actual valid columns. A supplied floor is
an actual stored cell, not an assumed dense ordinal interval. The selected
reference is bounded below by that floor and strictly below its ceiling. -/

namespace OmegaY.Expansion

open Canonical

@[simp] private theorem bind_ok {α β : Type} (a : α) (f : α → Result β) :
    (Except.ok a >>= f) = f a := rfl
@[simp] private theorem pure_ok {α : Type} (a : α) :
    (pure a : Result α) = Except.ok a := rfl

theorem below_between {mountain : Mountain} (hValid : MountainValid mountain)
    {floor : Ref} {floorCell : Cell} (hFloor : Canonical.cellAt mountain floor = .ok floorCell)
    {ceiling : Row} (hBound : floorCell.row < ceiling) :
    ∃ (found : Ref) (foundCell : Cell),
      below mountain floor.column ceiling = .ok found ∧
      Canonical.cellAt mountain found = .ok foundCell ∧ found.column = floor.column ∧
      floorCell.row ≤ foundCell.row ∧ foundCell.row < ceiling := by
  obtain ⟨nodes, hColumn, hIndex⟩ := cellAt_ok_iff.mp hFloor
  obtain ⟨hc, hcEq⟩ := Array.getElem?_eq_some_iff.mp hColumn
  have hColumnValid : ColumnValid mountain floor.column nodes := by
    rw [← hcEq]
    exact hValid floor.column hc
  obtain ⟨found, hFound⟩ := (below_succeeds_iff hColumn ceiling).mpr
    ⟨floor.index, floorCell, hIndex, hBound⟩
  obtain ⟨hSameColumn, foundCell, hFoundIndex, hBelow⟩ := below_result hColumn hFound
  have hStrict : StrictMono (fun i : Fin nodes.size => nodes[i.val].row) := by
    intro i j hij
    exact hColumnValid.rows_strict i.val j.val _ _
      (Array.getElem?_eq_getElem i.isLt) (Array.getElem?_eq_getElem j.isLt) hij
  have hAbove := below_max_row hColumn hStrict hFound hFoundIndex hIndex hBound
  refine ⟨found, foundCell, hFound, ?_, hSameColumn, hAbove, hBelow⟩
  apply cellAt_ok_iff.mpr
  exact ⟨nodes, by simpa only [hSameColumn] using hColumn, hFoundIndex⟩

/-- The actual phantom supplies a witness below every positive boundary. -/
theorem below_positive_total {mountain : Mountain} (hValid : MountainValid mountain)
    {column : Nat} (hc : column < mountain.size) {ceiling : Row} (hPositive : 0 < ceiling) :
    Succeeds (below mountain column ceiling) := by
  apply (below_succeeds_iff (Array.getElem?_eq_getElem hc) ceiling).mpr
  exact ⟨0, phantom, (hValid column hc).phantom, hPositive⟩

/-- Every requested positive boundary is processed by the actual mapM.
This establishes the reference-selection part of a block on a valid mountain,
not validity preservation of the subsequent copied columns. -/
theorem boundary_references_total {mountain : Mountain} (hValid : MountainValid mountain)
    {column : Nat} (hc : column < mountain.size) (boundaries : List Row)
    (hPositive : ∀ row ∈ boundaries, 0 < row) :
    ∃ references, boundaries.mapM (below mountain column) = .ok references ∧
      List.Forall₂ (fun ceiling ref => below mountain column ceiling = .ok ref)
        boundaries references := by
  induction boundaries with
  | nil => exact ⟨[], rfl, .nil⟩
  | cons ceiling rest ih =>
    obtain ⟨found, hFound⟩ := below_positive_total hValid hc (hPositive ceiling (by simp))
    obtain ⟨references, hReferences, hPaired⟩ := ih
      (fun row hrow => hPositive row (by simp [hrow]))
    refine ⟨found :: references, ?_, .cons hFound hPaired⟩
    simp [List.mapM_cons, hFound, hReferences]

end OmegaY.Expansion

#print axioms OmegaY.Expansion.below_between
#print axioms OmegaY.Expansion.boundary_references_total
