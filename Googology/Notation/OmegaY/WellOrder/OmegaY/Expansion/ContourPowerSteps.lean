/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ContourPowerSteps.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/ContourPowerSteps.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ContourTransport
import Googology.Notation.OmegaY.WellOrder.OmegaY.Rows.Lift
import Mathlib.Data.List.Chain

set_option backward.do.legacy false

/-!
# Adjacent power steps on the actual copied contour

Every executed contour step is a bump, so its copied rows satisfy the same
adjacent-row power-step equation as a canonical source column. This conclusion
does not assume normality of the copied column. The initial target is included:
it is a reference row, and need not be the copied marker's row. Joining this
path to marker and fill rows remains a separate boundary obligation.
-/

namespace OmegaY.Expansion

open Canonical

def RowPowerStep (lower upper : Row) : Prop :=
  upper = Row.bump lower (Row.jump lower upper - 1)

def RowsPowerSteps (rows : List Row) : Prop :=
  rows.IsChain RowPowerStep

theorem RowPowerStep.bump (lower : Row) (exponent : Nat) :
    RowPowerStep lower (Row.bump lower exponent) := by
  simp [RowPowerStep, Row.jump_bump]

theorem RowsPowerSteps.append {before after : List Row}
    (hBefore : RowsPowerSteps before) (hAfter : RowsPowerSteps after)
    (hJoin : ∀ lower ∈ before.getLast?, ∀ upper ∈ after.head?, RowPowerStep lower upper) :
    RowsPowerSteps (before ++ after) :=
  List.IsChain.append hBefore hAfter hJoin

theorem columnPowerSteps_iff_rowsPowerSteps (column : Column) :
    ColumnPowerSteps column ↔ RowsPowerSteps (column.toList.map Cell.row) := by
  simp only [RowsPowerSteps, List.isChain_iff_getElem]
  constructor
  · intro h i hi
    have hi' : i + 1 < column.size := by simpa using hi
    have hs := h i column[i] column[i+1]
      (Array.getElem?_eq_getElem (by omega)) (Array.getElem?_eq_getElem hi')
    simpa only [List.getElem_map, Array.getElem_toList, RowPowerStep] using hs
  · intro h i lower upper hLower hUpper
    obtain ⟨hl, el⟩ := Array.getElem?_eq_some_iff.mp hLower
    obtain ⟨hu, eu⟩ := Array.getElem?_eq_some_iff.mp hUpper
    have hs := h i (by simpa using hu)
    simpa only [List.getElem_map, Array.getElem_toList, el, eu, RowPowerStep] using hs

theorem bumpTrace_power_steps (target : Row) (exponents : List Nat) :
    RowsPowerSteps (target :: bumpTrace target exponents) := by
  induction exponents generalizing target with
  | nil => exact .singleton _
  | cons exponent rest ih =>
    exact (ih (Row.bump target exponent)).cons_cons (RowPowerStep.bump target exponent)

/-- A pointwise form of lift_run, including every intermediate row. -/
theorem bumpTrace_map_lift {root source target : Row} (hSource : root ≤ source)
    (exponents : List Nat) :
    (bumpTrace source exponents).map (Row.lift root target) =
      bumpTrace (Row.lift root target source) exponents := by
  induction exponents generalizing source with
  | nil => rfl
  | cons exponent rest ih =>
    simp only [bumpTrace, List.map_cons]
    rw [ih (hSource.trans (Row.lt_bump source exponent).le), Row.lift_bump hSource]

theorem bumpTrace_eq_lift (source target : Row) (exponents : List Nat) :
    bumpTrace target exponents =
      (bumpTrace source exponents).map (Row.lift source target) := by
  rw [bumpTrace_map_lift (le_refl source), Row.lift_at_root]

/-- Success is supplied by contour_total; neither copied-column normality nor
source power steps are needed for this local adjacent-row conclusion. -/
theorem contour_total_power_steps {mountain : Mountain} (hValid : MountainValid mountain)
    {sourceColumn shift rootColumn : Nat} {nodes : Column}
    (hColumn : mountain[sourceColumn]? = some nodes) (hSourcePositive : 0 < sourceColumn)
    (hDestination : sourceColumn + shift ≤ mountain.size) (hTop : TopOne nodes)
    (markerIndices : List Nat) {index : Nat} {current : Cell} (target : Row)
    (hCurrent : nodes[index]? = some current) {rest : List Cell}
    (hRest : nodes.toList.drop (index + 1) = rest) :
    ∃ result,
      contour mountain sourceColumn markerIndices shift rootColumn index target current rest = .ok result ∧
      RowsPowerSteps (target :: result.map Cell.row) ∧
      ContourParents mountain (sourceColumn + shift) result := by
  obtain ⟨result, hRun, hTrace, hParents⟩ := contour_total hValid hColumn hSourcePositive
    hDestination hTop markerIndices target hCurrent hRest (rootColumn := rootColumn)
  refine ⟨result, hRun, ?_, hParents⟩
  rw [hTrace]
  exact bumpTrace_power_steps target _

theorem contour_power_steps_of_success {mountain : Mountain} (hValid : MountainValid mountain)
    {sourceColumn shift rootColumn : Nat} {nodes : Column}
    (hColumn : mountain[sourceColumn]? = some nodes) (hSourcePositive : 0 < sourceColumn)
    (hDestination : sourceColumn + shift ≤ mountain.size) (hTop : TopOne nodes)
    (markerIndices : List Nat) {index : Nat} {current : Cell} (target : Row)
    (hCurrent : nodes[index]? = some current) {rest : List Cell}
    (hRest : nodes.toList.drop (index + 1) = rest) {result : List Cell}
    (hRun : contour mountain sourceColumn markerIndices shift rootColumn index target current rest =
      .ok result) : RowsPowerSteps (target :: result.map Cell.row) := by
  obtain ⟨output, hOutput, hPower, _⟩ := contour_total_power_steps hValid hColumn hSourcePositive
    hDestination hTop markerIndices target hCurrent hRest (rootColumn := rootColumn)
  have he : output = result := Except.ok.inj (hOutput.symm.trans hRun)
  exact he ▸ hPower

/-- A successful actual output is exactly the interval lift of each visited
source row. Only the frozen source column is required to have power steps. -/
theorem contour_rows_eq_lift_of_success {mountain : Mountain} (hValid : MountainValid mountain)
    {sourceColumn shift rootColumn : Nat} {nodes : Column}
    (hColumn : mountain[sourceColumn]? = some nodes) (hSourcePositive : 0 < sourceColumn)
    (hDestination : sourceColumn + shift ≤ mountain.size) (hTop : TopOne nodes)
    (hPower : ColumnPowerSteps nodes) (markerIndices : List Nat)
    {index : Nat} {current : Cell} (target : Row)
    (hCurrent : nodes[index]? = some current) {rest : List Cell}
    (hRest : nodes.toList.drop (index + 1) = rest) {result : List Cell}
    (hRun : contour mountain sourceColumn markerIndices shift rootColumn index target current rest =
      .ok result) :
    result.map Cell.row = (contourSourceCells markerIndices index current rest).map
      (fun source => Row.lift current.row target source.row) := by
  obtain ⟨output, hOutput, hTrace, _⟩ := contour_total hValid hColumn hSourcePositive
    hDestination hTop markerIndices target hCurrent hRest (rootColumn := rootColumn)
  have he : output = result := Except.ok.inj (hOutput.symm.trans hRun)
  subst output
  rw [hTrace, bumpTrace_eq_lift current.row target,
    contour_source_trace hPower markerIndices hCurrent hRest, List.map_map]
  rfl

end OmegaY.Expansion

#print axioms OmegaY.Expansion.columnPowerSteps_iff_rowsPowerSteps
#print axioms OmegaY.Expansion.contour_total_power_steps
#print axioms OmegaY.Expansion.contour_rows_eq_lift_of_success
