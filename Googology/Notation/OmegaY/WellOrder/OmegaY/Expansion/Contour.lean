/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/Contour.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/Contour.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.CopyEdge
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Totality
import Googology.Notation.OmegaY.WellOrder.OmegaY.Rows.Intervals

set_option backward.do.legacy false

/-!
# Totality and exact row trace of the actual contour loop

The remaining path is the actual stored source-column suffix. The source
column has a value-one top, but the ambient mountain is only MountainValid;
no canonical reconstruction or single-bump law is assumed for copied columns.
-/

namespace OmegaY.Expansion

open Canonical

/-- Exactly the exponents visited before the executable stopping condition. -/
def contourExponents (markerIndices : List Nat) : Nat → Cell → List Cell → List Nat
  | _, _, [] => []
  | index, current, upper :: rest =>
      if current.value = 1 ∨ index + 1 ∈ markerIndices then []
      else (Row.jump current.row upper.row - 1) ::
        contourExponents markerIndices (index + 1) upper rest

/-- Every successive target, without the initial target. -/
def bumpTrace (target : Row) : List Nat → List Row
  | [] => []
  | exponent :: rest =>
      let next := Row.bump target exponent
      next :: bumpTrace next rest

@[simp] theorem bumpTrace_length (target : Row) (exponents : List Nat) :
    (bumpTrace target exponents).length = exponents.length := by
  induction exponents generalizing target with
  | nil => rfl
  | cons exponent rest ih => simp [bumpTrace, ih]

theorem bumpTrace_strict (target : Row) (exponents : List Nat) :
    (target :: bumpTrace target exponents).Pairwise (· < ·) := by
  induction exponents generalizing target with
  | nil => simp [bumpTrace]
  | cons exponent rest ih =>
    change (target :: Row.bump target exponent ::
      bumpTrace (Row.bump target exponent) rest).Pairwise (· < ·)
    have hTail := ih (Row.bump target exponent)
    apply List.pairwise_cons.mpr
    refine ⟨?_, hTail⟩
    intro row hRow
    rcases List.mem_cons.mp hRow with rfl | hRow
    · exact Row.lt_bump target exponent
    · exact (Row.lt_bump target exponent).trans
        ((List.pairwise_cons.mp hTail).1 row hRow)

/-- The last target is the existing Row.run on the same exponents. -/
theorem bumpTrace_last (target : Row) (exponents : List Nat) :
    (target :: bumpTrace target exponents).getLast? = some (Row.run target exponents) := by
  induction exponents generalizing target with
  | nil => rfl
  | cons exponent rest ih =>
    change (target :: Row.bump target exponent ::
      bumpTrace (Row.bump target exponent) rest).getLast? = _
    rw [List.getLast?_cons_cons]
    exact ih (Row.bump target exponent)

/-- Each generated nonphantom contour cell has value zero and an actually
readable parent strictly before the destination column. -/
def ContourParents (mountain : Mountain) (destination : Nat) (cells : List Cell) : Prop :=
  ∀ cell ∈ cells, cell.value = 0 ∧
    ∃ parent parentCell, cell.left = some parent ∧ lookup mountain parent = .ok parentCell ∧
      parent.column < destination

private theorem contour_suffix_end {nodes : Column} {index : Nat} {current : Cell}
    (hCurrent : nodes[index]? = some current) (hRest : nodes.toList.drop (index + 1) = [])
    (hTop : TopOne nodes) : current.value = 1 := by
  obtain ⟨topCell, hTopRead, hOne⟩ := hTop
  have hi := (Array.getElem?_eq_some_iff.mp hCurrent).1
  have hSize : nodes.size ≤ index + 1 := by
    simpa only [Array.length_toList] using (List.drop_eq_nil_iff.mp hRest)
  have hIndex : index = nodes.size - 1 := by omega
  have hLast : nodes.back? = some current := by
    simpa only [Array.back?_eq_getElem?, hIndex] using hCurrent
  have he : current = topCell := Option.some.inj (hLast.symm.trans hTopRead)
  exact he ▸ hOne

private theorem contour_suffix_cons {nodes : Column} {index : Nat} {upper : Cell}
    {rest : List Cell} (hRest : nodes.toList.drop (index + 1) = upper :: rest) :
    nodes[index + 1]? = some upper ∧ nodes.toList.drop ((index + 1) + 1) = rest := by
  constructor
  · have hHead := congrArg List.head? hRest
    simpa only [List.head?_drop, Array.getElem?_toList, List.head?_cons] using hHead
  · simpa only [List.tail_drop, List.tail_cons] using congrArg List.tail hRest

/-- Actual contour execution on its actual finite source suffix. Every
copyEdge success is derived from the local mountain certificate and bounds. -/
theorem contour_total {mountain : Mountain} (hValid : MountainValid mountain)
    {sourceColumn shift rootColumn : Nat} {nodes : Column}
    (hColumn : mountain[sourceColumn]? = some nodes) (hSourcePositive : 0 < sourceColumn)
    (hDestination : sourceColumn + shift ≤ mountain.size) (hTop : TopOne nodes)
    (markerIndices : List Nat) {index : Nat} {current : Cell} (target : Row)
    (hCurrent : nodes[index]? = some current) {rest : List Cell}
    (hRest : nodes.toList.drop (index + 1) = rest) :
    ∃ result,
      contour mountain sourceColumn markerIndices shift rootColumn index target current rest = .ok result ∧
      result.map Cell.row = bumpTrace target (contourExponents markerIndices index current rest) ∧
      ContourParents mountain (sourceColumn + shift) result := by
  have hSourceBound := (Array.getElem?_eq_some_iff.mp hColumn).1
  have hNodesEq := (Array.getElem?_eq_some_iff.mp hColumn).2
  have hNodesValid : ColumnValid mountain sourceColumn nodes := by
    rw [← hNodesEq]
    exact hValid sourceColumn hSourceBound
  induction rest generalizing index current target with
  | nil =>
    have hOne := contour_suffix_end hCurrent hRest hTop
    refine ⟨[], ?_, rfl, ?_⟩
    · simp [contour, hOne]
    · simp [ContourParents]
  | cons upper rest ih =>
    by_cases hStop : current.value = 1 ∨ index + 1 ∈ markerIndices
    · refine ⟨[], ?_, ?_, ?_⟩
      · simp [contour, hStop]
      · simp [contourExponents, hStop, bumpTrace]
      · simp [ContourParents]
    · obtain ⟨hUpper, hTail⟩ := contour_suffix_cons hRest
      have hRows := hNodesValid.rows_strict index (index + 1) current upper hCurrent hUpper
        (Nat.lt_succ_self index)
      let nextTarget := Row.bump target (Row.jump current.row upper.row - 1)
      have hNextPositive : 0 < nextTarget := (Row.zero_le target).trans_lt (Row.lt_bump target _)
      have hUpperNonzero : upper.row ≠ 0 := ne_of_gt ((Row.zero_le current.row).trans_lt hRows)
      have hUpperRead : lookup mountain ⟨sourceColumn, index + 1⟩ = .ok upper :=
        lookup_ok_iff.mpr ⟨nodes, hColumn, hUpper⟩
      obtain ⟨copied, parent, parentCell, hCopied, hCopiedRow, hZero, hLeft, hParent, hParentLeft, _⟩ :=
        copyEdge_nonphantom_total hValid hUpperRead hSourcePositive hDestination
          hUpperNonzero hNextPositive (rootColumn := rootColumn)
      obtain ⟨remaining, hRemaining, hTrace, hParents⟩ := ih nextTarget hUpper hTail
      refine ⟨copied :: remaining, ?_, ?_, ?_⟩
      · dsimp only [nextTarget] at hCopied hRemaining
        simp [contour, hStop, hRows, hCopied, hRemaining]
      · simp only [List.map_cons, hCopiedRow, hTrace, contourExponents, hStop, ↓reduceIte, bumpTrace]
        rfl
      · intro cell hCell
        rcases List.mem_cons.mp hCell with rfl | hCell
        · exact ⟨hZero, parent, parentCell, hLeft, hParent, hParentLeft⟩
        · exact hParents cell hCell

theorem contour_total_strict {mountain : Mountain} (hValid : MountainValid mountain)
    {sourceColumn shift rootColumn : Nat} {nodes : Column}
    (hColumn : mountain[sourceColumn]? = some nodes) (hSourcePositive : 0 < sourceColumn)
    (hDestination : sourceColumn + shift ≤ mountain.size) (hTop : TopOne nodes)
    (markerIndices : List Nat) {index : Nat} {current : Cell} (target : Row)
    (hCurrent : nodes[index]? = some current) {rest : List Cell}
    (hRest : nodes.toList.drop (index + 1) = rest) :
    ∃ result,
      contour mountain sourceColumn markerIndices shift rootColumn index target current rest = .ok result ∧
      (target :: result.map Cell.row).Pairwise (· < ·) ∧
      ContourParents mountain (sourceColumn + shift) result := by
  obtain ⟨result, hRun, hRows, hParents⟩ := contour_total hValid hColumn hSourcePositive
    hDestination hTop markerIndices target hCurrent hRest (rootColumn := rootColumn)
  exact ⟨result, hRun, by rw [hRows]; exact bumpTrace_strict target _, hParents⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.contour_total
#print axioms OmegaY.Expansion.contour_total_strict
