/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Canonical/DecrementStep.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Canonical/DecrementStep.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Decrement
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.ShapeLocality
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Domain

set_option backward.do.legacy false

/-!
# One actual construction step after lowering the current value

The old diagram is the result of the executable canonical build. The new
diagram is required only to share the current row/left leg and complete
earlier columns. It need not be normal, complete, or a successful build.
-/

namespace OmegaY.Canonical

open Geometry

/-- Exactly the cell expression appended by `growColumn` after its reads. -/
def decrementNextCell (current parent : Cell) (parentRef : Ref) : Cell :=
  ⟨Row.B current.row parent.row, current.value - parent.value, some parentRef⟩

/-- Results of the actual parent search and the complete local dichotomy. -/
structure DecrementStepWitness (before after : Mountain)
    (u : (Frame.ofMountain before).Node) (newCell : Cell) (b : Nat) where
  oldParent : (Frame.ofMountain before).Node
  oldUpper : (Frame.ofMountain before).Node
  newParent : (Frame.ofMountain before).Node
  old_parent : findParent before (Frame.ref u) = .ok (Frame.ref oldParent)
  source_upper : (Frame.ofMountain before).upper u = some oldUpper
  new_parent : findParent after (Frame.ref u) = .ok (Frame.ref newParent)
  parent_read : cellAt after (Frame.ref newParent) =
    .ok ((Frame.ofMountain before).cell newParent)
  cases :
    (newParent = oldParent ∧ (Frame.ofMountain before).value oldParent < b ∧
      (decrementNextCell newCell ((Frame.ofMountain before).cell newParent)
        (Frame.ref newParent)).row = (Frame.ofMountain before).height oldUpper ∧
      (decrementNextCell newCell ((Frame.ofMountain before).cell newParent)
        (Frame.ref newParent)).left = ((Frame.ofMountain before).cell oldUpper).left ∧
      (decrementNextCell newCell ((Frame.ofMountain before).cell newParent)
        (Frame.ref newParent)).value + 1 = (Frame.ofMountain before).value oldUpper) ∨
    ((Frame.ofMountain before).value oldParent = b ∧
      findParent before (Frame.ref oldParent) = .ok (Frame.ref newParent) ∧
      ∃ pplus : (Frame.ofMountain before).Node,
        (Frame.ofMountain before).upper oldParent = some pplus ∧
        decrementNextCell newCell ((Frame.ofMountain before).cell newParent)
          (Frame.ref newParent) = (Frame.ofMountain before).cell pplus)

/-- Lowering `b+1` to `b>1` either retains the old parent, lowering the next
value by exactly one, or skips an equal parent and exactly copies its upper
cell. Both old-parent existence and new-search success are conclusions. -/
theorem build_decrement_step {values : List Nat} {before after : Mountain}
    (hBuild : build values = .ok before)
    {u : (Frame.ofMountain before).Node} {newCell : Cell} {b : Nat}
    (hb : 1 < b) (hOldValue : (Frame.ofMountain before).value u = b + 1)
    (hNewRead : cellAt after (Frame.ref u) = .ok newCell) (hNewValue : newCell.value = b)
    (hRow : (Frame.ofMountain before).height u = newCell.row)
    (hLeft : ((Frame.ofMountain before).cell u).left = newCell.left)
    (hColumns : ∀ c, c < u.1.val → before[c]? = after[c]?) :
    Nonempty (DecrementStepWitness before after u newCell b) := by
  have hLegal := build_success_legal hBuild
  have hNormal := build_normal_of_success hBuild
  have hLarge : 1 < (Frame.ofMountain before).value u := by omega
  have hReal := Frame.real_of_value_pos hNormal.toOrdered (Nat.zero_lt_of_lt hLarge)
  obtain ⟨p, hP⟩ := hNormal.parent_exists hLarge
  have hOldParent := (Executable.findParent_ref_iff hNormal.toOrdered u p).mpr hP
  obtain ⟨uplus, hUpper⟩ := hNormal.upper_of_parent hP
  obtain ⟨recorded, hRecorded, hOldRow, hOldNextValue, hOldLeft⟩ :=
    hNormal.upper_step u uplus hReal hUpper
  have heRecorded : recorded = p := Option.some.inj (hRecorded.symm.trans hP)
  subst recorded
  obtain ⟨r, hSearch, hCases⟩ := build_decrement_search hLegal hBuild hb hOldValue hOldParent
  have hNewParent : findParent after (Frame.ref u) = .ok (Frame.ref r) := by
    rw [findParent_eq_lowered_search (cellAt_of_frame_node before u) hNewRead hRow hLeft hColumns]
    rw [hNewValue]
    exact hSearch
  have hRLeft : r.1.val < u.1.val := (findParentAux_sound hSearch).column_lt
  have hNewParentRead : cellAt after (Frame.ref r) = .ok ((Frame.ofMountain before).cell r) :=
    (cellAt_eq_of_column_eq (hColumns r.1.val hRLeft)).symm.trans (cellAt_of_frame_node before r)
  refine ⟨{
    oldParent := p
    oldUpper := uplus
    newParent := r
    old_parent := hOldParent
    source_upper := hUpper
    new_parent := hNewParent
    parent_read := hNewParentRead
    cases := ?_ }⟩
  rcases hCases with ⟨he, hSmall⟩ | ⟨hEqual, hParentOfParent⟩
  · subst r
    refine Or.inl ⟨rfl, hSmall, ?_, ?_, ?_⟩
    · change Row.B newCell.row ((Frame.ofMountain before).height p) =
        (Frame.ofMountain before).height uplus
      rw [← hRow]
      exact hOldRow.symm
    · exact hOldLeft.symm
    · change newCell.value - (Frame.ofMountain before).value p + 1 =
        (Frame.ofMountain before).value uplus
      rw [hNewValue, hOldNextValue, hOldValue]
      omega
  · have hPParent := (Executable.findParent_ref_iff hNormal.toOrdered p r).mp hParentOfParent
    obtain ⟨pplus, hPplus⟩ := hNormal.upper_of_parent hPParent
    refine Or.inr ⟨hEqual, hParentOfParent, pplus, hPplus, ?_⟩
    change (⟨Row.B newCell.row ((Frame.ofMountain before).height r),
      newCell.value - (Frame.ofMountain before).value r, some (Frame.ref r)⟩ : Cell) =
        (Frame.ofMountain before).cell pplus
    rw [← hRow, hNewValue, ← hEqual]
    exact build_decrement_seam_cell hLegal hBuild hOldParent hParentOfParent hPplus

#print axioms build_decrement_step

end OmegaY.Canonical
