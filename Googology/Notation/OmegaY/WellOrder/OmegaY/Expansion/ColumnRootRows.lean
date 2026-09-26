/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ColumnRootRows.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/ColumnRootRows.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.SourcePartition
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ContourPowerSteps
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.FinishSupport
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.BoundaryReferences

set_option backward.do.legacy false

/-!
# Distinguished source rows survive a whole column copy

Every source node belongs to a physical marker or its actual source contour.
If every lower marker's target remains below a power cap at or below the
distinguished source row, the contour lift fixes that row. Actual sorting
and backfill therefore return it at a fresh array index. The parent-column
power-step and low-support facts are unnecessary for this preservation
argument; the successful copy itself has already generated the candidates.
-/

namespace OmegaY.Expansion

open Canonical

namespace ColumnCopyData

variable {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
  {sourceColumn shift rootColumn : Nat}
  (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)

/-- An actual source contour node above the reference cap contributes its
unchanged row to the actual segment output. Its numerical value may change. -/
theorem segment_source_row_mem_of_cap {marker : Ref} (hm : marker ∈ d.bucket)
    {sourceCell : Cell}
    (hSource : sourceCell ∈ contourSourceCells (d.bucket.map Ref.index) marker.index
      (d.marker_data marker hm).current (d.sources.toList.drop (marker.index + 1)))
    {scale : Nat}
    (hTarget : (d.marker_data marker hm).targetCell.row <
      Row.bump (d.marker_data marker hm).current.row scale)
    (hCap : Row.bump (d.marker_data marker hm).current.row scale ≤ sourceCell.row) :
    sourceCell.row ∈ (d.segment marker).map Cell.row := by
  let s := d.marker_data marker hm
  obtain ⟨copied, path, gap, hResult, _, _, _, hContour, _, _, _, _⟩ :=
    copySegment_result_decomposition d.ambient_valid d.source_column d.source_nonzero d.destination.le
      d.source_top references (d.bucket.map Ref.index) s.current_at s.upper_at s.upper_left
      s.parent_nodes s.target_at s.reference s.target_lower (d.segment_run hm)
  have hLiftRows := contour_rows_eq_lift_of_success d.ambient_valid d.source_column
    d.source_nonzero d.destination.le d.source_top d.source_power (d.bucket.map Ref.index)
    s.targetCell.row s.current_at rfl hContour
  have hLift : Row.lift s.current.row s.targetCell.row sourceCell.row = sourceCell.row :=
    Row.lift_eq_of_ge_cap s.target_lower hTarget hCap
  have hPath : sourceCell.row ∈ path.map Cell.row := by
    rw [hLiftRows]
    exact List.mem_map.mpr ⟨sourceCell, hSource, hLift⟩
  obtain ⟨cell, hCell, hCellRow⟩ := List.mem_map.mp hPath
  rw [hResult]
  exact List.mem_map.mpr ⟨cell, by simp [hCell], hCellRow⟩

/-- A row can be distinguished independently of preparation. The only new
condition is an input cap for each marker genuinely below that row. -/
theorem source_row_mem_candidates_of_caps (hNoPremature : NoPrematureOne d.sources)
    {sourceIndex : Nat} {sourceCell : Cell}
    (hSource : d.sources[sourceIndex]? = some sourceCell)
    (hCaps : ∀ marker (hm : marker ∈ d.bucket),
      (d.marker_data marker hm).current.row < sourceCell.row →
      ∃ scale, (d.marker_data marker hm).targetCell.row <
          Row.bump (d.marker_data marker hm).current.row scale ∧
        Row.bump (d.marker_data marker hm).current.row scale ≤ sourceCell.row) :
    sourceCell.row ∈ d.candidates.map Cell.row := by
  obtain ⟨marker, hm, _, _, _, hMarker | hContour⟩ := d.source_partition hNoPremature hSource
  · have hMem := (d.segment_bounds hm).2.1
    have hRow : sourceCell.row ∈ (d.segment marker).map Cell.row := by
      simpa only [hMarker.2] using hMem
    obtain ⟨cell, hCell, hCellRow⟩ := List.mem_map.mp hRow
    exact List.mem_map.mpr ⟨cell, List.mem_flatMap.mpr ⟨marker, hm, hCell⟩, hCellRow⟩
  · have hStrict : (d.marker_data marker hm).current.row < sourceCell.row :=
      d.source_valid.rows_strict _ _ _ _ (d.marker_data marker hm).current_at hSource hContour.1
    obtain ⟨scale, hTarget, hCap⟩ := hCaps marker hm hStrict
    have hRow := d.segment_source_row_mem_of_cap hm hContour.2 hTarget hCap
    obtain ⟨cell, hCell, hCellRow⟩ := List.mem_map.mp hRow
    exact List.mem_map.mpr ⟨cell, List.mem_flatMap.mpr ⟨marker, hm, hCell⟩, hCellRow⟩

/-- The returned node is read from the real copied array at a new witnessed
index. Neither source index nor source numerical value is reused. -/
theorem copyColumn_source_row_read_of_caps (hNoPremature : NoPrematureOne d.sources)
    {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {sourceIndex : Nat} {sourceCell : Cell}
    (hSource : d.sources[sourceIndex]? = some sourceCell)
    (hCaps : ∀ marker (hm : marker ∈ d.bucket),
      (d.marker_data marker hm).current.row < sourceCell.row →
      ∃ scale, (d.marker_data marker hm).targetCell.row <
          Row.bump (d.marker_data marker hm).current.row scale ∧
        Row.bump (d.marker_data marker hm).current.row scale ≤ sourceCell.row) :
    ∃ (index : Nat) (cell : Cell), column[index]? = some cell ∧ cell.row = sourceCell.row :=
  finish_row_read (d.copyColumn_eq_finish.symm.trans hRun)
    (d.source_row_mem_candidates_of_caps hNoPremature hSource hCaps)

end ColumnCopyData

/-- When the copied source contains all original root-prefix rows, the
current boundary's actual reference intervals ensure that those same rows
survive the copy. References may be freshly chosen for any later block. -/
theorem ColumnCopyData.copyColumn_root_rows {front : List Nat} {last : Nat}
    {p : Preparation front last} {mountain : Mountain} {references : List Ref}
    {sourceColumn shift rootColumn boundaryColumn : Nat}
    (d : ColumnCopyData mountain p.marked references sourceColumn shift rootColumn)
    (hLast : 1 < last) (hNoPremature : NoPrematureOne d.sources)
    (hBaseSource : p.reduced[sourceColumn]? = some d.sources)
    (hSourceRows : RootRowsInColumn p mountain sourceColumn)
    (hBoundaryRows : RootRowsInColumn p mountain boundaryColumn)
    (hMap : p.boundaries.mapM (below mountain boundaryColumn) = .ok references)
    {column : Column}
    (hRun : copyColumn mountain p.marked references sourceColumn shift rootColumn = .ok column) :
    RootRowsInColumn p (mountain.push column) mountain.size := by
  intro rootNodes rootIndex rootCell hRootColumn hRootRead hRootIndex
  obtain ⟨sourceRef, sourceCell, hSourceAt, hSourceColumn, hSourceRow⟩ :=
    hSourceRows hRootColumn hRootRead hRootIndex
  obtain ⟨sourceNodes, hSourceNodes, hSourceRead⟩ := cellAt_ok_iff.mp hSourceAt
  have hSourcesEq : sourceNodes = d.sources := Option.some.inj
    (hSourceNodes.symm.trans (by simpa only [hSourceColumn] using d.source_column))
  have hRead : d.sources[sourceRef.index]? = some sourceCell := by
    simpa only [hSourcesEq] using hSourceRead
  have hCaps : ∀ marker (hm : marker ∈ d.bucket),
      (d.marker_data marker hm).current.row < sourceCell.row →
      ∃ scale, (d.marker_data marker hm).targetCell.row <
          Row.bump (d.marker_data marker hm).current.row scale ∧
        Row.bump (d.marker_data marker hm).current.row scale ≤ sourceCell.row := by
    intro marker hm hStrict
    let s := d.marker_data marker hm
    have hBaseRead : Canonical.cellAt p.reduced marker = .ok s.current :=
      cellAt_ok_iff.mpr ⟨d.sources,
        by simpa only [d.marker_columns marker hm] using hBaseSource, s.current_at⟩
    have hRootStrict : s.current.row < rootCell.row := by
      simpa only [hSourceRow] using hStrict
    obtain ⟨target, ceiling, scale, hReference, _, hHigh, hPower, hCap⟩ :=
      hBoundaryRows.marker_below_root_row d.ambient_valid hLast hMap hm hBaseRead
        hRootColumn hRootRead hRootIndex hRootStrict
    have hTargetEq : target = s.targetCell.row := Except.ok.inj (hReference.symm.trans s.reference)
    exact ⟨scale, by simpa only [hTargetEq, hPower] using hHigh,
      by simpa only [hPower, hSourceRow] using hCap⟩
  obtain ⟨index, cell, hCell, hRow⟩ :=
    d.copyColumn_source_row_read_of_caps hNoPremature hRun hRead hCaps
  exact ⟨⟨mountain.size, index⟩, cell,
    cellAt_ok_iff.mpr ⟨column, by simp, hCell⟩, rfl, hRow.trans hSourceRow⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ColumnCopyData.source_row_mem_candidates_of_caps
#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_source_row_read_of_caps
#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_root_rows
