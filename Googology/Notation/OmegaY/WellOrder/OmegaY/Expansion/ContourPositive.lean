/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ContourPositive.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/ContourPositive.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ContourTransport
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.CopyEdgePositive

set_option backward.do.legacy false

/-!
# Positive parents of actual contour nodes above row one

The ambient source is an actual successful canonical build. Its stored
power steps and positive real legs are proved source facts, not assumptions
about the newly generated column. An auxiliary start stays at target zero,
so its first real node is copied to row one and is correctly exempted from
the positive-parent requirement.
-/

namespace OmegaY.Expansion

open Canonical

def ContourPositiveParents (mountain : Mountain) (destination : Nat) (cells : List Cell) : Prop :=
  ∀ cell ∈ cells, (1 : Row) < cell.row →
    ∃ parent parentCell, cell.left = some parent ∧ lookup mountain parent = .ok parentCell ∧
      0 < parentCell.value ∧ parent.column < destination

private theorem positive_suffix_cons {nodes : Column} {index : Nat} {upper : Cell}
    {rest : List Cell} (hRest : nodes.toList.drop (index + 1) = upper :: rest) :
    nodes[index + 1]? = some upper ∧ nodes.toList.drop ((index + 1) + 1) = rest := by
  constructor
  · simpa only [List.head?_drop, Array.getElem?_toList, List.head?_cons]
      using congrArg List.head? hRest
  · simpa only [List.tail_drop, List.tail_cons] using congrArg List.tail hRest

/-- If an adjacent copied row is above one, it cannot originate at the real
bottom. The auxiliary-origin case forces the copied target to be exactly one. -/
theorem contour_next_above_one_index {mountain : Mountain} {sourceColumn : Nat} {nodes : Column}
    (hValid : ColumnValid mountain sourceColumn nodes) (hPower : ColumnPowerSteps nodes)
    {index : Nat} {current upper : Cell}
    (hCurrent : nodes[index]? = some current) (hUpper : nodes[index + 1]? = some upper)
    {target : Row} (hAuxiliary : index = 0 → target = 0)
    (hAbove : (1 : Row) < Row.bump target (Row.jump current.row upper.row - 1)) :
    1 < index + 1 := by
  by_contra h
  have hIndex : index = 0 := by omega
  have hCurrentZero : current = phantom := Option.some.inj
    ((show nodes[0]? = some current by simpa only [hIndex] using hCurrent).symm.trans hValid.phantom)
  have hUpperOne : upper.row = 1 := hValid.bottom_row upper
    (by simpa only [hIndex, Nat.zero_add] using hUpper)
  have hTargetCurrent : target = current.row := by
    rw [hAuxiliary hIndex, hCurrentZero]
    rfl
  have hStep := hPower index current upper hCurrent hUpper
  rw [hTargetCurrent, ← hStep, hUpperOne] at hAbove
  exact (lt_irrefl (1 : Row)) hAbove

/-- Positivity for an actual successful execution. The total wrapper below
derives success separately; it is not left as the sole algorithm premise. -/
theorem contour_positive_of_success {values : List Nat} {mountain : Mountain}
    (hBuild : Canonical.build values = .ok mountain)
    {sourceColumn shift rootColumn : Nat} {nodes : Column}
    (hColumn : mountain[sourceColumn]? = some nodes) (hSourcePositive : 0 < sourceColumn)
    (hDestination : sourceColumn + shift ≤ mountain.size) (markerIndices : List Nat)
    {index : Nat} {current : Cell} (target : Row)
    (hCurrent : nodes[index]? = some current) {rest : List Cell}
    (hRest : nodes.toList.drop (index + 1) = rest) (hLift : current.row ≤ target)
    (hAuxiliary : index = 0 → target = 0) {result : List Cell}
    (hRun : contour mountain sourceColumn markerIndices shift rootColumn index target current rest = .ok result) :
    ContourPositiveParents mountain (sourceColumn + shift) result := by
  have hValid := build_valid_of_success hBuild
  obtain ⟨hc, hNodes⟩ := Array.getElem?_eq_some_iff.mp hColumn
  have hColumnValid : ColumnValid mountain sourceColumn nodes := hNodes ▸ hValid sourceColumn hc
  have hPower := build_column_power_steps_of_read hBuild hColumn
  induction rest generalizing index current target result with
  | nil =>
    by_cases hOne : current.value = 1
    · have he : result = [] := by simpa only [contour, hOne, ↓reduceIte, Except.ok.injEq] using hRun.symm
      subst result
      simp [ContourPositiveParents]
    · simp [contour, hOne] at hRun
  | cons upper rest ih =>
    by_cases hStop : current.value = 1 ∨ index + 1 ∈ markerIndices
    · have he : result = [] := by simpa [contour, hStop] using hRun.symm
      subst result
      simp [ContourPositiveParents]
    · obtain ⟨hUpper, hTail⟩ := positive_suffix_cons hRest
      have hRows := hColumnValid.rows_strict index (index + 1) current upper hCurrent hUpper
        (Nat.lt_succ_self index)
      let nextTarget := Row.bump target (Row.jump current.row upper.row - 1)
      have hNextPositive : 0 < nextTarget := (Row.zero_le target).trans_lt (Row.lt_bump target _)
      have hUpperNonzero : upper.row ≠ 0 := ne_of_gt ((Row.zero_le current.row).trans_lt hRows)
      have hNextLift : upper.row ≤ nextTarget := by
        rw [hPower index current upper hCurrent hUpper]
        exact Row.bump_monotone _ hLift
      have hUpperCanonical : Canonical.cellAt mountain ⟨sourceColumn, index + 1⟩ = .ok upper :=
        cellAt_ok_iff.mpr ⟨nodes, hColumn, hUpper⟩
      have hUpperRead : lookup mountain ⟨sourceColumn, index + 1⟩ = .ok upper :=
        lookup_ok_iff.mpr ⟨nodes, hColumn, hUpper⟩
      obtain ⟨copied, hCopy, hCopyRow, _hZero⟩ := copyEdge_total hValid hUpperRead
        hSourcePositive hDestination (fun _ => hNextPositive) (rootColumn := rootColumn)
      cases hRemaining : contour mountain sourceColumn markerIndices shift rootColumn
          (index + 1) nextTarget upper rest with
      | error error =>
        dsimp only [nextTarget] at hCopy hRemaining
        simp [contour, hStop, hRows, hCopy, hRemaining] at hRun
      | ok remaining =>
        have hResult : copied :: remaining = result := by
          dsimp only [nextTarget] at hCopy hRemaining
          simpa [contour, hStop, hRows, hCopy, hRemaining] using hRun
        subst result
        have hRemainingPositive := ih nextTarget hUpper hTail hNextLift
          (fun hZero => False.elim (by omega)) hRemaining
        intro cell hCell hAbove
        rcases List.mem_cons.mp hCell with rfl | hCell
        · have hNextAbove : (1 : Row) < nextTarget := by simpa only [hCopyRow] using hAbove
          have hSourceIndex := contour_next_above_one_index hColumnValid hPower hCurrent hUpper
            hAuxiliary hNextAbove
          obtain ⟨oldParent, oldParentCell, hOldLeft, hOldRead, hOldPositive, _, _, _⟩ :=
            build_above_bottom_stored_parent hBuild hUpperCanonical hSourceIndex
          obtain ⟨positiveCopy, parent, parentCell, hPositiveCopy, _hPositiveRow, _hPositiveZero,
            hLeft, hParent, hParentLeft, hParentPositive⟩ :=
            copyEdge_positive_parent hValid hUpperRead hSourcePositive hDestination hUpperNonzero
              hNextAbove hOldLeft (lookup_ok_iff.mpr (cellAt_ok_iff.mp hOldRead)) hOldPositive
              (rootColumn := rootColumn)
          have he : positiveCopy = cell := Except.ok.inj (hPositiveCopy.symm.trans hCopy)
          subst positiveCopy
          exact ⟨parent, parentCell, hLeft, hParent, hParentPositive, hParentLeft⟩
        · exact hRemainingPositive cell hCell hAbove

/-- Complete actual contour success, all readable parents, positive parents
above row one, and pointwise row transport from the actual source cells. -/
theorem contour_total_positive {values : List Nat} {mountain : Mountain}
    (hBuild : Canonical.build values = .ok mountain)
    {sourceColumn shift rootColumn : Nat} {nodes : Column}
    (hColumn : mountain[sourceColumn]? = some nodes) (hSourcePositive : 0 < sourceColumn)
    (hDestination : sourceColumn + shift ≤ mountain.size) (markerIndices : List Nat)
    {index : Nat} {current : Cell} (target : Row)
    (hCurrent : nodes[index]? = some current) {rest : List Cell}
    (hRest : nodes.toList.drop (index + 1) = rest) (hLift : current.row ≤ target)
    (hAuxiliary : index = 0 → target = 0) :
    ∃ result,
      contour mountain sourceColumn markerIndices shift rootColumn index target current rest = .ok result ∧
      ContourParents mountain (sourceColumn + shift) result ∧
      ContourPositiveParents mountain (sourceColumn + shift) result ∧
      List.Forall₂ (fun source copied => source.row ≤ copied.row)
        (contourSourceCells markerIndices index current rest) result := by
  obtain ⟨built, hBuilt, hValid, hTops⟩ := build_total (build_success_legal hBuild)
  have he : built = mountain := Except.ok.inj (hBuilt.symm.trans hBuild)
  subst built
  obtain ⟨hc, hNodes⟩ := Array.getElem?_eq_some_iff.mp hColumn
  have hTop : TopOne nodes := hNodes ▸ hTops sourceColumn hc
  obtain ⟨result, hRun, hTransport, hParents⟩ := contour_total_transport hValid hColumn
    hSourcePositive hDestination hTop (build_column_power_steps_of_read hBuild hColumn)
    markerIndices target hCurrent hRest hLift (rootColumn := rootColumn)
  exact ⟨result, hRun, hParents,
    contour_positive_of_success hBuild hColumn hSourcePositive hDestination markerIndices
      target hCurrent hRest hLift hAuxiliary hRun, hTransport⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.contour_next_above_one_index
#print axioms OmegaY.Expansion.contour_positive_of_success
#print axioms OmegaY.Expansion.contour_total_positive
