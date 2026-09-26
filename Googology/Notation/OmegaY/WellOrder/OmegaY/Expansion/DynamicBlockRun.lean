/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/DynamicBlockRun.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/DynamicBlockRun.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.DynamicBlockStep
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ColumnPower
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ColumnRootRows

set_option backward.do.legacy false

/-! An actual column step in any block, including the boundary-row support
needed to start the next block when this is the final source column. -/

namespace OmegaY.Expansion

open Canonical

theorem DynamicBlockState.copy_next {front : List Nat} {last : Nat}
    {p : Preparation front last} {block : Nat} {start : Mountain} {references : List Ref}
    {next : Nat} {ambient : Mountain} (s : DynamicBlockState p block start references next ambient)
    (hLast : 1 < last) (hNext : next < p.reduced.size) :
    ∃ column,
      copyColumn ambient p.marked references next
        (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column ∧
      ColumnValid ambient ambient.size column ∧ TopOne column ∧ ColumnPowerSteps column ∧
      DynamicCopiedMarkerRows p start references next column ∧
      DynamicBlockState p block start references (next + 1) (ambient.push column) ∧
      (next = p.reduced.size - 1 → RootRowsInColumn p (ambient.push column) ambient.size) := by
  obtain ⟨d, hNoPremature, hParentPower, hParentLow⟩ := s.column_data hLast hNext
  obtain ⟨column, hRun, _, hValid, hTop, hPower, _, hSupport⟩ :=
    d.copyColumn_valid_power hParentPower hParentLow hNoPremature
  have hRows : DynamicCopiedMarkerRows p start references next column := by
    intro marker hm current hCurrent target hTarget
    let md := d.marker_data marker hm
    have hCurrentAmbient : Canonical.cellAt ambient marker = .ok current :=
      p.cell_read_preserved s.base_ambient hCurrent
    have hDataRead : Canonical.cellAt ambient marker = .ok md.current :=
      cellAt_ok_iff.mpr ⟨d.sources, by simpa only [d.marker_columns marker hm] using d.source_column,
        md.current_at⟩
    have hCurrentEq : current = md.current := Except.ok.inj (hCurrentAmbient.symm.trans hDataRead)
    subst current
    have hTargetAmbient : referenceAt ambient references md.current.row = .ok target :=
      (s.referenceAt_preserved md.current.row).trans hTarget
    have hTargetEq : target = md.targetCell.row := Except.ok.inj (hTargetAmbient.symm.trans md.reference)
    subst target
    exact hSupport marker hm
  refine ⟨column, hRun, hValid, hTop, hPower, hRows, s.push hNext hValid hPower hRows, ?_⟩
  intro hFinalSource
  have hBaseSource : p.reduced[next]? = some d.sources :=
    (s.base_ambient next hNext).symm.trans d.source_column
  have hSourceRows : RootRowsInColumn p ambient next := by
    rw [hFinalSource]
    exact RootRowsInColumn.preserve (p.reduced_root_rows hLast) s.base_ambient
  have hBoundaryRows : RootRowsInColumn p ambient (start.size - 1) :=
    RootRowsInColumn.preserve s.boundary_rows s.start_preserved
  have hMap : p.boundaries.mapM (below ambient (start.size - 1)) = .ok references := by
    have hBelow : below ambient (start.size - 1) = below start (start.size - 1) :=
      funext (s.start_preserved.below (RootRowsInColumn.column_lt s.boundary_rows))
    rw [hBelow]
    exact s.reference_map
  intro nodes index source hNodes hSource hIndex
  exact d.copyColumn_root_rows hLast hNoPremature hBaseSource hSourceRows hBoundaryRows hMap hRun
    hNodes hSource hIndex

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.copy_next
