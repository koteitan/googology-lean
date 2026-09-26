/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Canonical/DecrementSync.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Canonical/DecrementSync.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.DecrementStep
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.DecrementLists
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.GraftTransfer

set_option backward.do.legacy false

/-!
# Complete synchronization of a decremented column continuation

While the old and new current values differ by one, their rows and stored
left endpoints agree. At either exit the next old cell is its value-one top.
Thus all old cells except that top are retained, with values decreased by one.
The only possible extra suffix consists of complete original cells from a
strictly earlier column. The statement below runs the actual growColumn.
-/

namespace OmegaY.Canonical

open Geometry

/-- Either no graft, or an actual inclusive suffix of a strictly earlier
source column. References are those of the original complete mountain. -/
def LeftSuffix (before : Mountain) (column : Nat) (tail : List Cell) : Prop :=
  tail = [] ∨ ∃ u : (Frame.ofMountain before).Node,
    u.1.val < column ∧ Frame.Real u ∧
      tail = (Frame.ofMountain before).cell u :: upperSuffix before u

private theorem current_ref {before left : Mountain}
    {u : (Frame.ofMountain before).Node} {target : Column}
    (hColumn : u.1.val = left.size) (hSize : target.size = u.2.val + 1) :
    Frame.ref u = ⟨left.size, target.size - 1⟩ := by
  simp only [Frame.ref, Ref.mk.injEq]
  exact ⟨hColumn, by omega⟩

private theorem prefix_push_columns {before left : Mountain}
    (hColumns : ∀ c, c < left.size → before[c]? = left[c]?) (target : Column) :
    ∀ c, c < left.size → before[c]? = (left.push target)[c]? := by
  intro c hc
  rw [hColumns c hc]
  simp [Array.getElem?_push, Nat.ne_of_lt hc]

theorem growColumn_decrement_sync {values : List Nat} {before left : Mountain}
    (hBuild : build values = .ok before)
    {fuel : Nat} {u : (Frame.ofMountain before).Node} {target : Column}
    (hLarge : 1 < (Frame.ofMountain before).value u)
    (hTop : target.back? = some (decCell ((Frame.ofMountain before).cell u)))
    (hColumn : u.1.val = left.size) (hSize : target.size = u.2.val + 1)
    (hColumns : ∀ c, c < left.size → before[c]? = left[c]?)
    (hEnough : (Frame.ofMountain before).value u - 2 ≤ fuel) :
    ∃ result tail, growColumn left fuel target = .ok result ∧
      result.toList = target.toList ++ decrementPrefix (upperSuffix before u) ++ tail ∧
      LeftSuffix before left.size tail ∧ TopOne result := by
  have hN := build_normal_of_success hBuild
  induction fuel generalizing u target with
  | zero =>
    have hTwo : (Frame.ofMountain before).value u = 2 := by omega
    have hReal := Frame.real_of_value_pos hN.toOrdered (by omega : 0 < (Frame.ofMountain before).value u)
    obtain ⟨v, hv⟩ := hN.upper_exists u hReal hLarge
    have hOne := upper_value_eq_one_of_value_two hN hReal hv hTwo
    have hvReal : Frame.Real v := by
      unfold Frame.Real
      rw [(Frame.upper_spec hv).2]
      omega
    have hSuffix : upperSuffix before u = [(Frame.ofMountain before).cell v] := by
      rw [upperSuffix_of_upper hv, upperSuffix_of_value_one hN hvReal hOne]
    have hCurrent : (decCell ((Frame.ofMountain before).cell u)).value = 1 := by
      change (Frame.ofMountain before).value u - 1 = 1
      omega
    refine ⟨target, [], growColumn_top _ hTop hCurrent, ?_, Or.inl rfl, _, hTop, hCurrent⟩
    simp [hSuffix, decrementPrefix]
  | succ fuel ih =>
    by_cases hTwo : (Frame.ofMountain before).value u = 2
    · have hReal := Frame.real_of_value_pos hN.toOrdered (by omega : 0 < (Frame.ofMountain before).value u)
      obtain ⟨v, hv⟩ := hN.upper_exists u hReal hLarge
      have hOne := upper_value_eq_one_of_value_two hN hReal hv hTwo
      have hvReal : Frame.Real v := by
        unfold Frame.Real
        rw [(Frame.upper_spec hv).2]
        omega
      have hSuffix : upperSuffix before u = [(Frame.ofMountain before).cell v] := by
        rw [upperSuffix_of_upper hv, upperSuffix_of_value_one hN hvReal hOne]
      have hCurrent : (decCell ((Frame.ofMountain before).cell u)).value = 1 := by
        change (Frame.ofMountain before).value u - 1 = 1
        omega
      refine ⟨target, [], growColumn_top _ hTop hCurrent, ?_, Or.inl rfl, _, hTop, hCurrent⟩
      simp [hSuffix, decrementPrefix]
    · let oldCell := (Frame.ofMountain before).cell u
      let newCell := decCell oldCell
      have hNewValue : 1 < newCell.value := by
        change 1 < (Frame.ofMountain before).value u - 1
        omega
      have hOldValue : (Frame.ofMountain before).value u = newCell.value + 1 := by
        change (Frame.ofMountain before).value u = (Frame.ofMountain before).value u - 1 + 1
        omega
      have hRef := current_ref hColumn hSize
      have hRead : cellAt (left.push target) (Frame.ref u) = .ok newCell := by
        rw [hRef]
        exact cellAt_current_top hTop
      obtain ⟨step⟩ := build_decrement_step hBuild hNewValue hOldValue hRead rfl
        (show (Frame.ofMountain before).height u = newCell.row from rfl)
        (show ((Frame.ofMountain before).cell u).left = newCell.left from rfl)
        (fun c hc => prefix_push_columns hColumns target c (by omega))
      let next := decrementNextCell newCell ((Frame.ofMountain before).cell step.newParent)
        (Frame.ref step.newParent)
      have hFind : findParent (left.push target) ⟨left.size, target.size - 1⟩ =
          .ok (Frame.ref step.newParent) := by simpa only [hRef] using step.new_parent
      have hBounds := difference_value_bounds hTop hFind step.parent_read
      have hNextPos : 0 < next.value := hBounds.1
      have hNextSmall : next.value < newCell.value := hBounds.2
      have hRun : growColumn left (fuel + 1) target =
          growColumn left fuel (target.push next) := by
        rw [growColumn_step fuel hTop (by change newCell.value ≠ 1; omega)
          (by change newCell.value ≠ 0; omega)]
        simp only [hFind, step.parent_read, except_bind_ok]
        rfl
      have hUpperReal : Frame.Real step.oldUpper := by
        unfold Frame.Real
        rw [(Frame.upper_spec step.source_upper).2]
        omega
      rcases step.cases with ⟨hSame, hSmall, hRow, hLeft, hValue⟩ |
        ⟨hEqual, hParentOfParent, pplus, hPplus, hNextEq⟩
      · have hNextEq : next = decCell ((Frame.ofMountain before).cell step.oldUpper) :=
          decCell_eq_of_fields hRow hLeft hValue
        have hUpperLarge : 1 < (Frame.ofMountain before).value step.oldUpper := by
          change next.value + 1 = (Frame.ofMountain before).value step.oldUpper at hValue
          omega
        have hUpperColumn : step.oldUpper.1.val = left.size :=
          (congrArg Fin.val (Frame.upper_spec step.source_upper).1).trans hColumn
        have hUpperSize : (target.push next).size = step.oldUpper.2.val + 1 := by
          rw [Array.size_push, (Frame.upper_spec step.source_upper).2]
          omega
        have hFuel : (Frame.ofMountain before).value step.oldUpper - 2 ≤ fuel := by
          change next.value + 1 = (Frame.ofMountain before).value step.oldUpper at hValue
          omega
        obtain ⟨result, tail, hResult, hList, hTail, hTopOne⟩ := ih hUpperLarge
          (target := target.push next) (by rw [← hNextEq]; exact Array.back?_push)
          hUpperColumn hUpperSize hFuel
        refine ⟨result, tail, hRun.trans hResult, ?_, hTail, hTopOne⟩
        rw [upperSuffix_of_upper step.source_upper,
          decrementPrefix_cons (upperSuffix_nonempty hN hUpperReal hUpperLarge)]
        simpa only [Array.toList_push, hNextEq, List.append_assoc,
          List.singleton_append] using hList
      · have hP := (Executable.findParent_ref_iff hN.toOrdered u step.oldParent).mp step.old_parent
        have hNextCell : next = (Frame.ofMountain before).cell pplus := hNextEq
        obtain ⟨recorded, hRecorded, _hr, hOldUpperValue, _hl⟩ := hN.upper_step u step.oldUpper
          (Frame.real_of_value_pos hN.toOrdered (by omega)) step.source_upper
        have heRecorded : recorded = step.oldParent := Option.some.inj (hRecorded.symm.trans hP)
        subst recorded
        have hOldUpperOne : (Frame.ofMountain before).value step.oldUpper = 1 := by
          rw [hOldUpperValue, hOldValue, hEqual]
          omega
        have hSuffix : upperSuffix before u = [(Frame.ofMountain before).cell step.oldUpper] := by
          rw [upperSuffix_of_upper step.source_upper,
            upperSuffix_of_value_one hN hUpperReal hOldUpperOne]
        have hpLeft : pplus.1.val < left.size := by
          have hlt := Frame.P_column_lt hN.toOrdered hP
          rw [(congrArg Fin.val (Frame.upper_spec hPplus).1)]
          omega
        have hpReal : Frame.Real pplus := by
          unfold Frame.Real
          rw [(Frame.upper_spec hPplus).2]
          omega
        have hpValue : (Frame.ofMountain before).value pplus = next.value :=
          (congrArg Cell.value hNextEq).symm
        obtain ⟨result, hResult, hList, hTopOne⟩ := growColumn_graft_transfer hN hpReal
          (target := target.push next) (by rw [← hNextEq]; exact Array.back?_push)
          hpLeft.le (fun c hc => hColumns c (hc.trans hpLeft))
          (fuel := fuel) (by rw [hpValue]; omega)
        refine ⟨result, (Frame.ofMountain before).cell pplus :: upperSuffix before pplus,
          hRun.trans hResult, ?_, Or.inr ⟨pplus, hpLeft, hpReal, rfl⟩, hTopOne⟩
        simpa [hSuffix, decrementPrefix, Array.toList_push, hNextCell, List.append_assoc] using hList

end OmegaY.Canonical

#print axioms OmegaY.Canonical.growColumn_decrement_sync
