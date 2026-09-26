/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ContourFrozen.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/ContourFrozen.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.FrozenSource

set_option backward.do.legacy false

/-! Contour positivity needs canonical facts only about frozen source cells.
The ambient mountain may already contain completed copied columns. -/

namespace OmegaY.Expansion

open Canonical

private theorem frozen_suffix_cons {nodes : Column} {index : Nat} {upper : Cell}
    {rest : List Cell} (hRest : nodes.toList.drop (index + 1) = upper :: rest) :
    nodes[index + 1]? = some upper ∧ nodes.toList.drop ((index + 1) + 1) = rest := by
  constructor
  · simpa only [List.head?_drop, Array.getElem?_toList, List.head?_cons]
      using congrArg List.head? hRest
  · simpa only [List.tail_drop, List.tail_cons] using congrArg List.tail hRest

/-- Only the ambient validity and local source interfaces are assumed. In
particular, no canonical or normal certificate for copied columns is used. -/
theorem contour_positive_of_source {mountain : Mountain}
    (hValid : MountainValid mountain)
    {sourceColumn shift rootColumn : Nat} {nodes : Column}
    (hColumn : mountain[sourceColumn]? = some nodes) (hSourcePositive : 0 < sourceColumn)
    (hDestination : sourceColumn + shift ≤ mountain.size)
    (hPower : ColumnPowerSteps nodes) (hPositive : SourceAboveBottomPositive mountain nodes)
    (markerIndices : List Nat) {index : Nat} {current : Cell} (target : Row)
    (hCurrent : nodes[index]? = some current) {rest : List Cell}
    (hRest : nodes.toList.drop (index + 1) = rest) (hLift : current.row ≤ target)
    (hAuxiliary : index = 0 → target = 0) {result : List Cell}
    (hRun : contour mountain sourceColumn markerIndices shift rootColumn index target current rest = .ok result) :
    ContourPositiveParents mountain (sourceColumn + shift) result := by
  obtain ⟨hc, hNodes⟩ := Array.getElem?_eq_some_iff.mp hColumn
  have hColumnValid : ColumnValid mountain sourceColumn nodes := hNodes ▸ hValid sourceColumn hc
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
    · obtain ⟨hUpper, hTail⟩ := frozen_suffix_cons hRest
      have hRows := hColumnValid.rows_strict index (index + 1) current upper hCurrent hUpper
        (Nat.lt_succ_self index)
      let nextTarget := Row.bump target (Row.jump current.row upper.row - 1)
      have hNextPositive : 0 < nextTarget := (Row.zero_le target).trans_lt (Row.lt_bump target _)
      have hUpperNonzero : upper.row ≠ 0 := ne_of_gt ((Row.zero_le current.row).trans_lt hRows)
      have hNextLift : upper.row ≤ nextTarget := by
        rw [hPower index current upper hCurrent hUpper]
        exact Row.bump_monotone _ hLift
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
          obtain ⟨oldParent, oldParentCell, hOldLeft, hOldRead, hOldPositive⟩ :=
            hPositive (index + 1) upper hUpper hSourceIndex
          obtain ⟨positiveCopy, parent, parentCell, hPositiveCopy, _hPositiveRow, _hPositiveZero,
            hLeft, hParent, hParentLeft, hParentPositive⟩ :=
            copyEdge_positive_parent hValid hUpperRead hSourcePositive hDestination hUpperNonzero
              hNextAbove hOldLeft hOldRead hOldPositive (rootColumn := rootColumn)
          have he : positiveCopy = cell := Except.ok.inj (hPositiveCopy.symm.trans hCopy)
          subst positiveCopy
          exact ⟨parent, parentCell, hLeft, hParent, hParentPositive, hParentLeft⟩
        · exact hRemainingPositive cell hCell hAbove

/-- Full contour execution from local source facts. Success is derived by the
actual recursive algorithm and is not an input certificate. -/
theorem contour_total_positive_of_source {mountain : Mountain}
    (hValid : MountainValid mountain)
    {sourceColumn shift rootColumn : Nat} {nodes : Column}
    (hColumn : mountain[sourceColumn]? = some nodes) (hSourcePositive : 0 < sourceColumn)
    (hDestination : sourceColumn + shift ≤ mountain.size)
    (hTop : TopOne nodes) (hPower : ColumnPowerSteps nodes)
    (hPositive : SourceAboveBottomPositive mountain nodes)
    (markerIndices : List Nat) {index : Nat} {current : Cell} (target : Row)
    (hCurrent : nodes[index]? = some current) {rest : List Cell}
    (hRest : nodes.toList.drop (index + 1) = rest) (hLift : current.row ≤ target)
    (hAuxiliary : index = 0 → target = 0) :
    ∃ result,
      contour mountain sourceColumn markerIndices shift rootColumn index target current rest = .ok result ∧
      ContourParents mountain (sourceColumn + shift) result ∧
      ContourPositiveParents mountain (sourceColumn + shift) result ∧
      List.Forall₂ (fun source copied => source.row ≤ copied.row)
        (contourSourceCells markerIndices index current rest) result := by
  obtain ⟨result, hRun, hTransport, hParents⟩ := contour_total_transport hValid hColumn
    hSourcePositive hDestination hTop hPower markerIndices target hCurrent hRest hLift
    (rootColumn := rootColumn)
  exact ⟨result, hRun, hParents,
    contour_positive_of_source hValid hColumn hSourcePositive hDestination hPower hPositive
      markerIndices target hCurrent hRest hLift hAuxiliary hRun, hTransport⟩

/-- Frozen-build wrapper: only unchanged complete source columns are canonical;
the current ambient mountain is merely valid. -/
theorem contour_total_positive_frozen {values : List Nat} {source ambient : Mountain}
    (hBuild : Canonical.build values = .ok source)
    (hPreserve : PreservesColumns source ambient) (hValid : MountainValid ambient)
    {sourceColumn shift rootColumn : Nat} {nodes : Column}
    (hColumn : source[sourceColumn]? = some nodes) (hSourcePositive : 0 < sourceColumn)
    (hDestination : sourceColumn + shift ≤ ambient.size)
    (markerIndices : List Nat) {index : Nat} {current : Cell} (target : Row)
    (hCurrent : nodes[index]? = some current) {rest : List Cell}
    (hRest : nodes.toList.drop (index + 1) = rest) (hLift : current.row ≤ target)
    (hAuxiliary : index = 0 → target = 0) :
    ∃ result,
      contour ambient sourceColumn markerIndices shift rootColumn index target current rest = .ok result ∧
      ContourParents ambient (sourceColumn + shift) result ∧
      ContourPositiveParents ambient (sourceColumn + shift) result ∧
      List.Forall₂ (fun original copied => original.row ≤ copied.row)
        (contourSourceCells markerIndices index current rest) result := by
  obtain ⟨hAmbient, hTop, hPower, hPositive⟩ := frozen_source_facts hBuild hPreserve hColumn
  exact contour_total_positive_of_source hValid hAmbient hSourcePositive hDestination
    hTop hPower hPositive markerIndices target hCurrent hRest hLift hAuxiliary

end OmegaY.Expansion

#print axioms OmegaY.Expansion.contour_positive_of_source
#print axioms OmegaY.Expansion.contour_total_positive_of_source
#print axioms OmegaY.Expansion.contour_total_positive_frozen
