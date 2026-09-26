/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Canonical/DecrementBuild.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Canonical/DecrementBuild.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.BuildSplit
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.DecrementSync

set_option backward.do.legacy false

/-!
# Exact comparison of two actual final-column builds

The common left mountain comes from the validated successful front build.
Synchronization starts at the actual old bottom and the new initial column.
The final equation retains every old cell except its last top, decrements
those retained values, and appends only a complete earlier-column suffix.
-/

namespace OmegaY.Canonical

open Geometry

private theorem column_eq_two_cells_drop {column : Column} {a b : Cell}
    (ha : column[0]? = some a) (hb : column[1]? = some b) :
    column.toList = [a, b] ++ column.toList.drop 2 := by
  obtain ⟨hZero, hA⟩ := Array.getElem?_eq_some_iff.mp ha
  obtain ⟨hOne, hB⟩ := Array.getElem?_eq_some_iff.mp hb
  have he0 : column.toList = column[0] :: column.toList.drop 1 :=
    List.drop_eq_getElem_cons (l := column.toList) (i := 0) hZero
  have he1 : column.toList.drop 1 = column[1] :: column.toList.drop 2 :=
    List.drop_eq_getElem_cons (l := column.toList) (i := 1) hOne
  calc
    column.toList = column[0] :: column.toList.drop 1 := he0
    _ = [a, b] ++ column.toList.drop 2 := by rw [he1, hA, hB]; rfl

private theorem upperSuffix_eq_drop_two {before : Mountain}
    {u : (Frame.ofMountain before).Node} {column : Column}
    (hColumn : before[u.1.val]? = some column) (hIndex : u.2.val = 1) :
    upperSuffix before u = column.toList.drop 2 := by
  have hc : u.1.val < before.size := u.1.isLt
  have hRead : before[u.1.val] = column := (Array.getElem?_eq_some_iff.mp hColumn).2
  change (before[u.1.val]'hc).toList.drop (u.2.val + 1) = column.toList.drop 2
  rw [hRead, hIndex]

/-- Complete actual-build comparison, including the shared validated front.
Both build successes are explicit inputs; they are supplied independently by
the canonical totality theorem for the two legal sequences. -/
theorem build_decrement_columns {front : List Nat} {last : Nat} {before after : Mountain}
    (hBefore : build (front ++ [last]) = .ok before)
    (hAfter : build (front ++ [last - 1]) = .ok after) (hlast : 1 < last) :
    ∃ (left : Mountain) (oldColumn newColumn : Column) (tail : List Cell),
      build front = .ok left ∧
      buildColumn left last = .ok oldColumn ∧
      buildColumn left (last - 1) = .ok newColumn ∧
      before = left.push oldColumn ∧ after = left.push newColumn ∧
      left.size = front.length ∧
      newColumn.toList = decrementPrefix oldColumn.toList ++ tail ∧
      LeftSuffix before left.size tail ∧ TopOne newColumn := by
  obtain ⟨left, oldColumn, newColumn, hFront, hOldColumn, hBeforeShape,
      hNewColumn, hAfterShape, hSize, hPrefixes⟩ := build_split_common_front hBefore hAfter
  obtain ⟨u, hRef, hReal, hCell, _, hValue⟩ := build_last_bottom_node hBefore
  have hIndex : u.2.val = 1 := congrArg Ref.index hRef
  have hColumn : u.1.val = left.size := (congrArg Ref.column hRef).trans hSize.symm
  have hLarge : 1 < (Frame.ofMountain before).value u := by rw [hValue]; exact hlast
  let target := initialColumn left.size (last - 1)
  have hTop : target.back? = some (decCell ((Frame.ofMountain before).cell u)) := by
    rw [hCell, ← hSize]
    rfl
  have hTargetSize : target.size = u.2.val + 1 := by simp [target, initialColumn, hIndex]
  have hEnough : (Frame.ofMountain before).value u - 2 ≤ (last - 1) - 1 := by
    rw [hValue]
    omega
  obtain ⟨result, tail, hResult, hList, hTail, hTopOne⟩ := growColumn_decrement_sync
    hBefore hLarge hTop hColumn hTargetSize (fun c hc => (hPrefixes c hc).1) hEnough
  have hNewRun : growColumn left ((last - 1) - 1) target = .ok newColumn := by
    simpa only [buildColumn, show last - 1 ≠ 0 by omega, ↓reduceIte, target] using hNewColumn
  have heResult : result = newColumn := Except.ok.inj (hResult.symm.trans hNewRun)
  subst result
  have hOldRun : growColumn left (last - 1) (initialColumn left.size last) = .ok oldColumn := by
    simpa only [buildColumn, show last ≠ 0 by omega, ↓reduceIte] using hOldColumn
  have hPhantom : oldColumn[0]? = some phantom := by
    have hp := growColumn_preserves_cells hOldRun (i := 0)
      (show 0 < (initialColumn left.size last).size by simp [initialColumn])
    simpa [initialColumn] using hp
  have hOldList : oldColumn.toList =
      [phantom, initialBottom left.size last] ++ oldColumn.toList.drop 2 :=
    column_eq_two_cells_drop hPhantom (buildColumn_bottom hOldColumn)
  have hSourceColumn : before[u.1.val]? = some oldColumn := by
    rw [hColumn, hBeforeShape]
    simp
  have hSuffix := upperSuffix_eq_drop_two hSourceColumn hIndex
  have hSuffixNonempty := upperSuffix_nonempty (build_normal_of_success hBefore) hReal hLarge
  have hDropNonempty : oldColumn.toList.drop 2 ≠ [] := by simpa only [hSuffix] using hSuffixNonempty
  have hDecOld : decrementPrefix oldColumn.toList =
      target.toList ++ decrementPrefix (upperSuffix before u) := by
    calc
      decrementPrefix oldColumn.toList =
          [phantom, initialBottom left.size last].map decCell ++
            decrementPrefix (oldColumn.toList.drop 2) :=
        (congrArg decrementPrefix hOldList).trans (decrementPrefix_append hDropNonempty)
      _ = target.toList ++ decrementPrefix (upperSuffix before u) := by
        rw [hSuffix]
        rfl
  refine ⟨left, oldColumn, newColumn, tail, hFront, hOldColumn, hNewColumn,
    hBeforeShape, hAfterShape, hSize, ?_, hTail, hTopOne⟩
  calc
    newColumn.toList = target.toList ++ decrementPrefix (upperSuffix before u) ++ tail := hList
    _ = decrementPrefix oldColumn.toList ++ tail := by rw [hDecOld, List.append_assoc]

#print axioms build_decrement_columns

end OmegaY.Canonical
