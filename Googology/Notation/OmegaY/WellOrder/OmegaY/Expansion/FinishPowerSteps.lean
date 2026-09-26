/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/FinishPowerSteps.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/FinishPowerSteps.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.FillPowerSteps
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.FinishSupport

set_option backward.do.legacy false

/-! An ascending power-step presentation of the actual candidates survives
the real sorting and value backfill. No power-step property of the output
column is a premise. -/

namespace OmegaY.Expansion

open Canonical

theorem finishSort_rows_eq_of_power_perm {cells : List Cell} {rows : List Row}
    (hPerm : rows.Perm (cells.map Cell.row)) (hPower : RowsPowerSteps rows) :
    (finishSort cells).map Cell.row = rows := by
  have hNodup : (cells.map Cell.row).Nodup :=
    hPerm.nodup_iff.mp (hPower.strict.imp (fun h => ne_of_lt h))
  have hSorted : ((finishSort cells).map Cell.row).Pairwise (· < ·) := by
    simpa only [List.pairwise_map] using finishSort_strict hNodup
  exact (((finishSort_perm cells).map Cell.row).trans hPerm.symm).eq_of_pairwise'
    hSorted hPower.strict

theorem finish_power_steps {mountain : Mountain} {cells : List Cell} {column : Column}
    (hRun : finish mountain cells = .ok column) {rows : List Row}
    (hPerm : rows.Perm (cells.map Cell.row)) (hPower : RowsPowerSteps rows) :
    ColumnPowerSteps column := by
  have hShape := (finish_success_spec hRun).1
  have hRows : column.toList.map Cell.row = rows :=
    hShape.1.symm.trans (finishSort_rows_eq_of_power_perm hPerm hPower)
  apply (columnPowerSteps_iff_rowsPowerSteps column).mpr
  rw [hRows]
  exact hPower

end OmegaY.Expansion

#print axioms OmegaY.Expansion.finishSort_rows_eq_of_power_perm
#print axioms OmegaY.Expansion.finish_power_steps
