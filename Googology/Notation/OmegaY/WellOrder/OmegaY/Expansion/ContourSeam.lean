/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ContourSeam.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/ContourSeam.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.SourceStopping
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ContourPowerSteps

set_option backward.do.legacy false

/-! The exact power-step seam between a copied contour and the next marked
source row. Strict upper bounds alone are insufficient: the proof transports
the last genuine source step by the exact interval lift and resets its high
endpoint at the root cap. -/

namespace OmegaY.Expansion

open Canonical

private theorem seam_suffix_cons {nodes : Column} {index : Nat} {upper : Cell}
    {rest : List Cell} (hRest : nodes.toList.drop (index + 1) = upper :: rest) :
    nodes[index + 1]? = some upper ∧ nodes.toList.drop ((index + 1) + 1) = rest := by
  constructor
  · simpa only [List.head?_drop, Array.getElem?_toList, List.head?_cons]
      using congrArg List.head? hRest
  · simpa only [List.tail_drop, List.tail_cons] using congrArg List.tail hRest

theorem RowPowerStep.lift {root target lower upper : Row} (hLower : root ≤ lower)
    (hStep : RowPowerStep lower upper) :
    RowPowerStep (Row.lift root target lower) (Row.lift root target upper) := by
  change upper = Row.bump lower (Row.jump lower upper - 1) at hStep
  have hLift := congrArg (Row.lift root target) hStep
  rw [Row.lift_bump hLower] at hLift
  rw [hLift]
  exact RowPowerStep.bump _ _

/-- Absence of intervening markers and premature value-one cells makes the
source contour stop precisely before the specified next actual marker. -/
theorem contour_source_seam {nodes : Column} (hPower : ColumnPowerSteps nodes)
    (hNoPremature : NoPrematureOne nodes) (markerIndices : List Nat)
    {index nextIndex : Nat} {current nextMarker : Cell}
    (hCurrent : nodes[index]? = some current) (hNext : nodes[nextIndex]? = some nextMarker)
    (hMarked : nextIndex ∈ markerIndices) (hIndex : index < nextIndex)
    (hNoBetween : ∀ middle, index < middle → middle < nextIndex → middle ∉ markerIndices)
    {rest : List Cell} (hRest : nodes.toList.drop (index + 1) = rest) :
    RowPowerStep (Row.run current.row (contourExponents markerIndices index current rest))
      nextMarker.row := by
  induction rest generalizing index current with
  | nil =>
    have hSize : nodes.size ≤ index + 1 := by
      simpa only [Array.length_toList] using List.drop_eq_nil_iff.mp hRest
    have hNextBound := (Array.getElem?_eq_some_iff.mp hNext).1
    omega
  | cons upper rest ih =>
    obtain ⟨hUpper, hTail⟩ := seam_suffix_cons hRest
    by_cases hAdjacent : index + 1 = nextIndex
    · have hSame : upper = nextMarker := Option.some.inj
        (hUpper.symm.trans (by simpa only [hAdjacent] using hNext))
      have hStop : current.value = 1 ∨ index + 1 ∈ markerIndices :=
        Or.inr (hAdjacent ▸ hMarked)
      simp only [contourExponents, hStop, ↓reduceIte, Row.run_nil]
      change nextMarker.row = Row.bump current.row (Row.jump current.row nextMarker.row - 1)
      simpa only [hSame] using hPower index current upper hCurrent hUpper
    · have hStrict : index + 1 < nextIndex := by omega
      have hNotMarked := hNoBetween (index + 1) (by omega) hStrict
      have hNotOne := hNoPremature index current upper hCurrent hUpper
      have hStop : ¬ (current.value = 1 ∨ index + 1 ∈ markerIndices) := by
        simpa only [not_or] using And.intro hNotOne hNotMarked
      simp only [contourExponents, hStop, ↓reduceIte, Row.run_cons]
      rw [← hPower index current upper hCurrent hUpper]
      exact ih hUpper hStrict (fun middle hlo hhi => hNoBetween middle (by omega) hhi) hTail

/-- The last genuine source step is lifted too. The next marker lies at or
above the cap and hence is fixed by the lift, closing an exact power seam. -/
theorem contour_lifted_seam {nodes : Column} (hPower : ColumnPowerSteps nodes)
    (hNoPremature : NoPrematureOne nodes) (markerIndices : List Nat)
    {index nextIndex : Nat} {current nextMarker : Cell}
    (hCurrent : nodes[index]? = some current) (hNext : nodes[nextIndex]? = some nextMarker)
    (hMarked : nextIndex ∈ markerIndices) (hIndex : index < nextIndex)
    (hNoBetween : ∀ middle, index < middle → middle < nextIndex → middle ∉ markerIndices)
    {rest : List Cell} (hRest : nodes.toList.drop (index + 1) = rest)
    {target : Row} {scale : Nat} (hLower : current.row ≤ target)
    (hUpper : target < Row.bump current.row scale)
    (hCap : Row.bump current.row scale ≤ nextMarker.row) :
    RowPowerStep (Row.run target (contourExponents markerIndices index current rest))
      nextMarker.row := by
  have hSource := contour_source_seam hPower hNoPremature markerIndices hCurrent hNext
    hMarked hIndex hNoBetween hRest
  have hLift := RowPowerStep.lift (target := target) (Row.le_run current.row _) hSource
  rw [← Row.run_eq_lift, Row.lift_eq_of_ge_cap hLower hUpper hCap] at hLift
  exact hLift

section Actual

variable {mountain : Mountain} (hValid : MountainValid mountain)
  {sourceColumn shift rootColumn : Nat} {nodes : Column}
  (hColumn : mountain[sourceColumn]? = some nodes) (hSourcePositive : 0 < sourceColumn)
  (hDestination : sourceColumn + shift ≤ mountain.size) (hTop : TopOne nodes)
  (hPower : ColumnPowerSteps nodes) (hNoPremature : NoPrematureOne nodes)
  (markerIndices : List Nat) {index nextIndex : Nat} {current nextMarker : Cell} (target : Row)
  (hCurrent : nodes[index]? = some current) (hNext : nodes[nextIndex]? = some nextMarker)
  (hMarked : nextIndex ∈ markerIndices) (hIndex : index < nextIndex)
  (hNoBetween : ∀ middle, index < middle → middle < nextIndex → middle ∉ markerIndices)
  {rest : List Cell} (hRest : nodes.toList.drop (index + 1) = rest) {scale : Nat}
  (hLower : current.row ≤ target) (hUpper : target < Row.bump current.row scale)
  (hCap : Row.bump current.row scale ≤ nextMarker.row) {result : List Cell}
  (hRun : contour mountain sourceColumn markerIndices shift rootColumn index target current rest =
    .ok result)

include hValid hColumn hSourcePositive hDestination hTop hPower hNoPremature hCurrent hNext
  hMarked hIndex hNoBetween hRest hLower hUpper hCap hRun

/-- This includes the empty-contour case, whose last row is the initial
target. In every case the witness is the last actual output row. -/
theorem contour_seam_of_success :
    ∀ last ∈ (target :: result.map Cell.row).getLast?, RowPowerStep last nextMarker.row := by
  obtain ⟨output, hOutput, hTrace, _⟩ := contour_total hValid hColumn hSourcePositive
    hDestination hTop markerIndices target hCurrent hRest (rootColumn := rootColumn)
  have he : output = result := Except.ok.inj (hOutput.symm.trans hRun)
  subst output
  have hLast : (target :: result.map Cell.row).getLast? =
      some (Row.run target (contourExponents markerIndices index current rest)) := by
    rw [hTrace]
    exact bumpTrace_last target _
  intro last hMember
  have hLastEq : Row.run target (contourExponents markerIndices index current rest) = last := by
    simpa only [hLast, Option.mem_some_iff] using hMember
  rw [← hLastEq]
  exact contour_lifted_seam hPower hNoPremature markerIndices hCurrent hNext hMarked hIndex
    hNoBetween hRest hLower hUpper hCap

/-- The actual contour and its next unshifted marker form one complete
adjacent-power path, not merely a strictly increasing list of rows. -/
theorem contour_with_next_marker_power_steps :
    RowsPowerSteps ((target :: result.map Cell.row) ++ [nextMarker.row]) := by
  apply RowsPowerSteps.append
    (contour_power_steps_of_success hValid hColumn hSourcePositive hDestination hTop
      markerIndices target hCurrent hRest hRun) (.singleton _) ?_
  intro lower hLast upper hHead
  have he : nextMarker.row = upper := by
    simpa only [List.head?_cons, Option.mem_some_iff] using hHead
  rw [← he]
  exact contour_seam_of_success hValid hColumn hSourcePositive hDestination hTop hPower
    hNoPremature markerIndices target hCurrent hNext hMarked hIndex hNoBetween hRest
    hLower hUpper hCap hRun lower hLast

end Actual

end OmegaY.Expansion

#print axioms OmegaY.Expansion.contour_source_seam
#print axioms OmegaY.Expansion.contour_lifted_seam
#print axioms OmegaY.Expansion.contour_seam_of_success
#print axioms OmegaY.Expansion.contour_with_next_marker_power_steps
