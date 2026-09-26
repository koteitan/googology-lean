/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Canonical/DecrementLists.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Canonical/DecrementLists.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.GraftSuffix

set_option backward.do.legacy false

/-!
# Cell/list algebra for complete decrement synchronization

These operations use exact natural-number subtraction.  The phantom's zero
value therefore remains zero.  The old last top is removed by `dropLast`,
not by an assumed or chosen early stopping prefix.
-/

namespace OmegaY.Canonical

open Geometry

def decCell (cell : Cell) : Cell := ⟨cell.row, cell.value - 1, cell.left⟩

@[simp] theorem decCell_row (cell : Cell) : (decCell cell).row = cell.row := rfl
@[simp] theorem decCell_value (cell : Cell) : (decCell cell).value = cell.value - 1 := rfl
@[simp] theorem decCell_left (cell : Cell) : (decCell cell).left = cell.left := rfl
@[simp] theorem decCell_phantom : decCell phantom = phantom := rfl

theorem decCell_positive {cell : Cell} (h : 1 < cell.value) : 0 < (decCell cell).value := by
  simp only [decCell_value]
  omega

theorem decCell_value_add_one {cell : Cell} (h : 0 < cell.value) :
    (decCell cell).value + 1 = cell.value := by simp only [decCell_value]; omega

/-- Equality of the complete cell follows from shape equality and exactly one
unit of numerical difference; absolute stored parent references are retained. -/
theorem decCell_eq_of_value_add_one {oldCell newCell : Cell}
    (hrow : oldCell.row = newCell.row) (hleft : oldCell.left = newCell.left)
    (hvalue : newCell.value + 1 = oldCell.value) : decCell oldCell = newCell := by
  cases oldCell
  cases newCell
  simp only [decCell, Cell.mk.injEq] at *
  exact ⟨hrow, by omega, hleft⟩

theorem decCell_eq_of_fields {oldCell newCell : Cell}
    (hrow : newCell.row = oldCell.row) (hleft : newCell.left = oldCell.left)
    (hvalue : newCell.value + 1 = oldCell.value) : newCell = decCell oldCell :=
  (decCell_eq_of_value_add_one hrow.symm hleft.symm hvalue).symm

/-- Subtracting one commutes with the scalar difference when the parent stays
fixed.  Positivity of a generated cell is supplied separately by search. -/
theorem decCell_difference (child parent : Cell) (parentRef : Ref) :
    decCell (⟨Row.B child.row parent.row, child.value - parent.value, some parentRef⟩ : Cell) =
      ⟨Row.B (decCell child).row parent.row, (decCell child).value - parent.value,
        some parentRef⟩ := by
  simp only [decCell, Cell.mk.injEq]
  exact ⟨True.intro, by omega, True.intro⟩

def decrementPrefix (cells : List Cell) : List Cell := cells.dropLast.map decCell

@[simp] theorem decrementPrefix_nil : decrementPrefix [] = [] := rfl
@[simp] theorem decrementPrefix_singleton (cell : Cell) : decrementPrefix [cell] = [] := rfl

theorem decrementPrefix_cons {cell : Cell} {tail : List Cell} (htail : tail ≠ []) :
    decrementPrefix (cell :: tail) = decCell cell :: decrementPrefix tail := by
  simp [decrementPrefix, List.dropLast_cons_of_ne_nil htail]

theorem decrementPrefix_append {front suffix : List Cell} (hsuffix : suffix ≠ []) :
    decrementPrefix (front ++ suffix) = front.map decCell ++ decrementPrefix suffix := by
  simp [decrementPrefix, List.dropLast_append_of_ne_nil hsuffix]

@[simp] theorem decrementPrefix_append_singleton (front : List Cell) (top : Cell) :
    decrementPrefix (front ++ [top]) = front.map decCell := by
  rw [decrementPrefix_append (by simp : [top] ≠ [])]
  simp

theorem upper_real {mountain : Mountain} {u v : (Frame.ofMountain mountain).Node}
    (hupper : (Frame.ofMountain mountain).upper u = some v) : Frame.Real v := by
  unfold Frame.Real
  rw [(Frame.upper_spec hupper).2]
  omega

theorem upperSuffix_nonempty {mountain : Mountain}
    (hNormal : (Frame.ofMountain mountain).Normal)
    {u : (Frame.ofMountain mountain).Node} (hReal : Frame.Real u)
    (hLarge : 1 < (Frame.ofMountain mountain).value u) : upperSuffix mountain u ≠ [] := by
  obtain ⟨v, hv⟩ := hNormal.upper_exists u hReal hLarge
  rw [upperSuffix_of_upper hv]
  simp

/-- A normal upper node has value one exactly when the parent is one unit below
its child.  This includes the equal-parent decrement seam. -/
theorem upper_value_one_iff_parent_add_one {mountain : Mountain}
    (hNormal : (Frame.ofMountain mountain).Normal)
    {u p v : (Frame.ofMountain mountain).Node}
    (hp : (Frame.ofMountain mountain).P u = some p)
    (hv : (Frame.ofMountain mountain).upper u = some v) :
    (Frame.ofMountain mountain).value v = 1 ↔
      (Frame.ofMountain mountain).value p + 1 = (Frame.ofMountain mountain).value u := by
  have hvalues := Frame.P_value hNormal.toOrdered hp
  have hreal := Frame.real_of_value_pos hNormal.toOrdered (Nat.lt_trans hvalues.1 hvalues.2)
  obtain ⟨q, hq, _, hvalue, _⟩ := hNormal.upper_step u v hreal hv
  have he : q = p := Option.some.inj (hq.symm.trans hp)
  subst q
  rw [hvalue]
  omega

theorem upper_value_one_of_value_two {mountain : Mountain}
    (hNormal : (Frame.ofMountain mountain).Normal)
    {u v : (Frame.ofMountain mountain).Node}
    (hu : (Frame.ofMountain mountain).value u = 2)
    (hv : (Frame.ofMountain mountain).upper u = some v) :
    (Frame.ofMountain mountain).value v = 1 := by
  obtain ⟨p, hp⟩ := hNormal.parent_exists (by omega : 1 < (Frame.ofMountain mountain).value u)
  have hvalues := Frame.P_value hNormal.toOrdered hp
  apply (upper_value_one_iff_parent_add_one hNormal hp hv).mpr
  omega

theorem upper_value_eq_one_of_value_two {mountain : Mountain}
    (hNormal : (Frame.ofMountain mountain).Normal)
    {u v : (Frame.ofMountain mountain).Node} (_hReal : Frame.Real u)
    (hUpper : (Frame.ofMountain mountain).upper u = some v)
    (hTwo : (Frame.ofMountain mountain).value u = 2) :
    (Frame.ofMountain mountain).value v = 1 :=
  upper_value_one_of_value_two hNormal hTwo hUpper

/-- Once the next old node has value one, it is the sole remaining old node. -/
theorem upperSuffix_eq_singleton_of_upper_one {mountain : Mountain}
    (hNormal : (Frame.ofMountain mountain).Normal)
    {u v : (Frame.ofMountain mountain).Node}
    (hv : (Frame.ofMountain mountain).upper u = some v)
    (hone : (Frame.ofMountain mountain).value v = 1) :
    upperSuffix mountain u = [(Frame.ofMountain mountain).cell v] := by
  rw [upperSuffix_of_upper hv, upperSuffix_of_value_one hNormal (upper_real hv) hone]

theorem decrementPrefix_upperSuffix_of_upper_one {mountain : Mountain}
    (hNormal : (Frame.ofMountain mountain).Normal)
    {u v : (Frame.ofMountain mountain).Node}
    (hv : (Frame.ofMountain mountain).upper u = some v)
    (hone : (Frame.ofMountain mountain).value v = 1) :
    decrementPrefix (upperSuffix mountain u) = [] := by
  rw [upperSuffix_eq_singleton_of_upper_one hNormal hv hone]
  rfl

/-- Every old next node whose value is greater than one remains in the full
decrement prefix, with exactly one subtracted from its value. -/
theorem decrementPrefix_upperSuffix_step {mountain : Mountain}
    (hNormal : (Frame.ofMountain mountain).Normal)
    {u v : (Frame.ofMountain mountain).Node}
    (hv : (Frame.ofMountain mountain).upper u = some v)
    (hlarge : 1 < (Frame.ofMountain mountain).value v) :
    decrementPrefix (upperSuffix mountain u) =
      decCell ((Frame.ofMountain mountain).cell v) :: decrementPrefix (upperSuffix mountain v) := by
  obtain ⟨w, hw⟩ := hNormal.upper_exists v (upper_real hv) hlarge
  have htail : upperSuffix mountain v ≠ [] := by
    rw [upperSuffix_of_upper hw]
    simp
  rw [upperSuffix_of_upper hv, decrementPrefix_cons htail]

theorem value_two_remaining_prefix_empty {mountain : Mountain}
    (hNormal : (Frame.ofMountain mountain).Normal)
    {u : (Frame.ofMountain mountain).Node}
    (hu : (Frame.ofMountain mountain).value u = 2) :
    decrementPrefix (upperSuffix mountain u) = [] := by
  have hreal := Frame.real_of_value_pos hNormal.toOrdered (by omega : 0 < (Frame.ofMountain mountain).value u)
  obtain ⟨v, hv⟩ := hNormal.upper_exists u hreal (by omega)
  exact decrementPrefix_upperSuffix_of_upper_one hNormal hv (upper_value_one_of_value_two hNormal hu hv)

end OmegaY.Canonical

#print axioms OmegaY.Canonical.decCell_eq_of_value_add_one
#print axioms OmegaY.Canonical.upper_value_one_of_value_two
#print axioms OmegaY.Canonical.decrementPrefix_upperSuffix_step
#print axioms OmegaY.Canonical.value_two_remaining_prefix_empty
