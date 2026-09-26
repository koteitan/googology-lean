/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ContourParentRows.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/ContourParentRows.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ContourTransport

set_option backward.do.legacy false

/-! Actual contour parents remain no higher than their generated children.
Only source power steps and local ambient validity are used; the ambient
mountain need not be canonical and the output is not assumed valid. -/

namespace OmegaY.Expansion

open Canonical

def ContourParentRows (mountain : Mountain) (destination : Nat) (cells : List Cell) : Prop :=
  ∀ cell ∈ cells, ∃ parent parentCell, cell.left = some parent ∧
    lookup mountain parent = .ok parentCell ∧ parent.column < destination ∧
    parentCell.row ≤ cell.row

private theorem parent_rows_suffix_cons {nodes : Column} {index : Nat} {upper : Cell}
    {rest : List Cell} (hRest : nodes.toList.drop (index + 1) = upper :: rest) :
    nodes[index + 1]? = some upper ∧ nodes.toList.drop ((index + 1) + 1) = rest := by
  constructor
  · simpa only [List.head?_drop, Array.getElem?_toList, List.head?_cons]
      using congrArg List.head? hRest
  · simpa only [List.tail_drop, List.tail_cons] using congrArg List.tail hRest

/-- Positive target steps and source power steps give the row lift needed
by both the fixed-parent and the translated-parent copy branches. -/
theorem contour_parent_rows_of_success {mountain : Mountain} (hValid : MountainValid mountain)
    {sourceColumn shift rootColumn : Nat} {nodes : Column}
    (hColumn : mountain[sourceColumn]? = some nodes) (hSourcePositive : 0 < sourceColumn)
    (hDestination : sourceColumn + shift ≤ mountain.size) (hPower : ColumnPowerSteps nodes)
    (markerIndices : List Nat) {index : Nat} {current : Cell} (target : Row)
    (hCurrent : nodes[index]? = some current) {rest : List Cell}
    (hRest : nodes.toList.drop (index + 1) = rest) (hLift : current.row ≤ target)
    {result : List Cell}
    (hRun : contour mountain sourceColumn markerIndices shift rootColumn index target current rest =
      .ok result) : ContourParentRows mountain (sourceColumn + shift) result := by
  obtain ⟨hc, hNodes⟩ := Array.getElem?_eq_some_iff.mp hColumn
  have hColumnValid : ColumnValid mountain sourceColumn nodes := hNodes ▸ hValid sourceColumn hc
  induction rest generalizing index current target result with
  | nil =>
    by_cases hOne : current.value = 1
    · have he : result = [] := by
        simpa only [contour, hOne, ↓reduceIte, Except.ok.injEq] using hRun.symm
      subst result
      simp [ContourParentRows]
    · simp [contour, hOne] at hRun
  | cons upper rest ih =>
    by_cases hStop : current.value = 1 ∨ index + 1 ∈ markerIndices
    · have he : result = [] := by simpa [contour, hStop] using hRun.symm
      subst result
      simp [ContourParentRows]
    · obtain ⟨hUpper, hTail⟩ := parent_rows_suffix_cons hRest
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
      obtain ⟨copied, parent, parentCell, hCopy, _, _, hLeft, hParent, hParentColumn, hParentRow⟩ :=
        copyEdge_nonphantom_row_bound hValid hUpperRead hSourcePositive hDestination
          hUpperNonzero hNextPositive hNextLift (rootColumn := rootColumn)
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
        have hRestParents := ih nextTarget hUpper hTail hNextLift hRemaining
        intro cell hCell
        rcases List.mem_cons.mp hCell with rfl | hCell
        · exact ⟨parent, parentCell, hLeft, hParent, hParentColumn, hParentRow⟩
        · exact hRestParents cell hCell

/-- Successful construction and the parent row certificate, without an
assumption that the actual contour call succeeds. -/
theorem contour_total_parent_rows {mountain : Mountain} (hValid : MountainValid mountain)
    {sourceColumn shift rootColumn : Nat} {nodes : Column}
    (hColumn : mountain[sourceColumn]? = some nodes) (hSourcePositive : 0 < sourceColumn)
    (hDestination : sourceColumn + shift ≤ mountain.size) (hTop : TopOne nodes)
    (hPower : ColumnPowerSteps nodes) (markerIndices : List Nat)
    {index : Nat} {current : Cell} (target : Row) (hCurrent : nodes[index]? = some current)
    {rest : List Cell} (hRest : nodes.toList.drop (index + 1) = rest)
    (hLift : current.row ≤ target) :
    ∃ result, contour mountain sourceColumn markerIndices shift rootColumn index target current rest =
      .ok result ∧ ContourParentRows mountain (sourceColumn + shift) result := by
  obtain ⟨result, hRun, _, _⟩ := contour_total hValid hColumn hSourcePositive hDestination hTop
    markerIndices target hCurrent hRest (rootColumn := rootColumn)
  exact ⟨result, hRun, contour_parent_rows_of_success hValid hColumn hSourcePositive hDestination
    hPower markerIndices target hCurrent hRest hLift hRun⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.contour_parent_rows_of_success
#print axioms OmegaY.Expansion.contour_total_parent_rows
