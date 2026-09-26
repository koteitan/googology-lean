/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/PreparedBlockStep.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/PreparedBlockStep.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.PreparedBlockState
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.SourceStopping

set_option backward.do.legacy false

/-! Input data for any column of the first block. The actual weak-parent
closure selects either the original boundary column or an already copied
earlier column. Both endpoint reads and parent power steps come from that
specific available column, with no whole-block-success premise. -/

namespace OmegaY.Expansion

open Canonical

structure PreparedMarkerData (mountain : Mountain) (sources : Column) (references : List Ref)
    (shift index : Nat) extends MarkerCopyData mountain sources references shift index where
  lowIndex : Nat
  lowCell : Cell
  low_at : parentNodes[lowIndex]? = some lowCell
  low_row : lowCell.row = current.row
  parent_power : ColumnPowerSteps parentNodes

theorem PreparedBlockState.marker_data {front : List Nat} {last : Nat}
    {p : Preparation front last} {references : List Ref} {next : Nat} {ambient : Mountain}
    (s : PreparedBlockState p references next ambient) (hLast : 1 < last)
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
    {sources : Column} (hSources : p.reduced[next]? = some sources)
    {marker : Ref} (hMarker : BucketMem p.marked next marker) :
    Nonempty (PreparedMarkerData ambient sources references
      (p.reduced.size - 1 - p.root.column) marker.index) := by
  obtain ⟨rootIndex, parent, current, upper, parentCell, _, hCurrent, hUpper,
    hLeft, hParentLeft, hParent, hParentRow, hParentCase⟩ :=
    markers_upper_parent
      (weakLocal_of_ordered p.reduced_valid.toOrdered p.reduced_valid.left_sources)
      p.root_valid p.markers_built hMarker
  have hMarkerColumn : marker.column = next := (p.marker_iff.mp hMarker).1
  obtain ⟨currentSources, hCurrentSources, hCurrentIndex⟩ := hCurrent
  have hCurrentSourcesEq : currentSources = sources := Option.some.inj
    (hCurrentSources.symm.trans (by simpa only [hMarkerColumn] using hSources))
  subst currentSources
  obtain ⟨upperSources, hUpperSources, hUpperIndex⟩ := hUpper
  have hUpperSourcesEq : upperSources = sources := Option.some.inj
    (hUpperSources.symm.trans (by simpa only [hMarkerColumn] using hSources))
  subst upperSources
  have hCurrentRead : Canonical.cellAt p.reduced marker = .ok current :=
    cellAt_ok_iff.mpr ⟨sources, hCurrentSources, hCurrentIndex⟩
  have hParentRead : Canonical.cellAt p.reduced parent = .ok parentCell := cellAt_ok_iff.mpr hParent
  obtain ⟨rootNodes, rootRowIndex, lower, hRootColumn, hRootLower, hRootIndex, hRootRow⟩ :=
    p.marker_root_prefix_read hMarker hCurrentRead
  obtain ⟨_, _, targetRef, boundaryTarget, _, _, hBelow, hTargetRead, hReference, hLow, _, _⟩ :=
    p.initial_referenceAt_root_interval hLast hRootColumn hRootLower hRootIndex hMap
  have hBaseReference : referenceAt p.reduced references current.row = .ok boundaryTarget.row := by
    simpa only [hRootRow] using hReference
  have hTargetLower : current.row ≤ boundaryTarget.row := by
    simpa only [hRootRow] using hLow
  have hSize := build_size p.reduced_build
  simp only [List.length_append, List.length_singleton] at hSize
  have hRootLeft := p.root_before_last
  have hWitness : ∃ (nodes : Column) (targetIndex : Nat) (targetCell : Cell)
      (lowIndex : Nat) (lowCell : Cell),
      ambient[parent.column + (p.reduced.size - 1 - p.root.column)]? = some nodes ∧
      nodes[targetIndex]? = some targetCell ∧ targetCell.row = boundaryTarget.row ∧
      nodes[lowIndex]? = some lowCell ∧ lowCell.row = current.row ∧ ColumnPowerSteps nodes := by
    rcases hParentCase with hRoot | hEarlier
    · have hParentColumn : parent.column = p.root.column := by
        simpa only using congrArg Ref.column hRoot
      have hShift : parent.column + (p.reduced.size - 1 - p.root.column) =
          p.reduced.size - 1 := by omega
      have hTargetColumn : targetRef.column = p.reduced.size - 1 :=
        (below_result (Array.getElem?_eq_getElem p.reduced_last_exists) hBelow).1
      obtain ⟨nodes, hNodes, hTargetIndex⟩ := cellAt_ok_iff.mp hTargetRead
      obtain ⟨lowRef, lowCell, hLowRead, hLowColumn, hLowRow⟩ :=
        p.reduced_root_prefix_read hLast hRootColumn hRootLower hRootIndex
      obtain ⟨lowNodes, hLowNodes, hLowIndex⟩ := cellAt_ok_iff.mp hLowRead
      have hNodesEq : lowNodes = nodes := Option.some.inj
        (hLowNodes.symm.trans (by simpa only [hLowColumn, hTargetColumn] using hNodes))
      subst lowNodes
      exact ⟨nodes, targetRef.index, boundaryTarget, lowRef.index, lowCell,
        by simpa only [hShift, hTargetColumn] using s.base_preserved.column_read hNodes,
        hTargetIndex, rfl, hLowIndex, hLowRow.trans hRootRow,
        build_column_power_steps_of_read p.reduced_build hNodes⟩
    · have hParentRight := (p.marker_iff.mp hEarlier).2.1
      have hParentEarlier : parent.column < next := by simpa only [hMarkerColumn] using hParentLeft
      obtain ⟨nodes, hNodes, hPower, hRows⟩ :=
        s.copied_columns parent.column hParentRight hParentEarlier
      have hParentReference : referenceAt p.reduced references parentCell.row = .ok boundaryTarget.row := by
        simpa only [hParentRow] using hBaseReference
      obtain ⟨⟨lowIndex, lowCell, hLowIndex, hLowRow⟩, ⟨targetIndex, targetCell, hTargetIndex, hTargetRow⟩⟩ :=
        hRows parent hEarlier parentCell hParentRead boundaryTarget.row hParentReference
      exact ⟨nodes, targetIndex, targetCell, lowIndex, lowCell, hNodes, hTargetIndex,
        hTargetRow, hLowIndex, hLowRow.trans hParentRow, hPower⟩
  obtain ⟨parentNodes, targetIndex, targetCell, lowIndex, lowCell, hParentNodes,
    hTargetAt, hTargetRow, hLowAt, hLowRow, hPower⟩ := hWitness
  exact ⟨{
    current := current
    upper := upper
    sourceParent := parent
    parentNodes := parentNodes
    targetIndex := targetIndex
    targetCell := targetCell
    current_at := hCurrentIndex
    upper_at := hUpperIndex
    upper_left := hLeft
    parent_nodes := hParentNodes
    target_at := hTargetAt
    reference := by
      simpa only [hTargetRow] using
        (p.initial_referenceAt_preserved s.base_preserved hMap current.row).trans hBaseReference
    target_lower := by simpa only [hTargetRow] using hTargetLower
    lowIndex := lowIndex
    lowCell := lowCell
    low_at := hLowAt
    low_row := hLowRow
    parent_power := hPower }⟩

/-- The state supplies all generic copy input and power-step input for its
next actual source column. All marker data is chosen once, so the returned
low endpoints and parent power steps concern exactly those same nodes. -/
theorem PreparedBlockState.column_data {front : List Nat} {last : Nat}
    {p : Preparation front last} {references : List Ref} {next : Nat} {ambient : Mountain}
    (s : PreparedBlockState p references next ambient) (hLast : 1 < last)
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
    (hNext : next < p.reduced.size) :
    ∃ d : ColumnCopyData ambient p.marked references next
        (p.reduced.size - 1 - p.root.column) p.root.column,
      NoPrematureOne d.sources ∧
      (∀ marker (hm : marker ∈ d.bucket), ColumnPowerSteps (d.marker_data marker hm).parentNodes) ∧
      (∀ marker (hm : marker ∈ d.bucket),
        ∃ (index : Nat) (cell : Cell), (d.marker_data marker hm).parentNodes[index]? = some cell ∧
          cell.row = (d.marker_data marker hm).current.row) := by
  classical
  let sources := p.reduced[next]
  have hSources : p.reduced[next]? = some sources := Array.getElem?_eq_getElem hNext
  obtain ⟨hAmbientSources, hTop, hPower, hPositive⟩ :=
    frozen_source_facts p.reduced_build s.base_preserved hSources
  let data : ∀ marker, BucketMem p.marked next marker →
      PreparedMarkerData ambient sources references (p.reduced.size - 1 - p.root.column) marker.index :=
    fun marker hm => Classical.choice (s.marker_data hLast hMap hSources hm)
  have hSourceValid : ColumnValid ambient next sources := by
    obtain ⟨hc, hNodes⟩ := Array.getElem?_eq_some_iff.mp hAmbientSources
    exact hNodes ▸ s.ambient_valid _ hc
  have hRead : ∀ marker (hm : BucketMem p.marked next marker),
      Canonical.cellAt ambient marker = .ok (data marker hm).current := by
    intro marker hm
    have hColumn := (p.marker_iff.mp hm).1
    exact cellAt_ok_iff.mpr ⟨sources, by simpa only [hColumn] using hAmbientSources,
      (data marker hm).current_at⟩
  let d : ColumnCopyData ambient p.marked references next
      (p.reduced.size - 1 - p.root.column) p.root.column := {
    sources := sources
    ambient_valid := s.ambient_valid
    source_column := hAmbientSources
    source_nonzero := by have := s.next_lower; omega
    destination := s.size_eq.symm
    source_top := hTop
    source_power := hPower
    source_positive := hPositive
    marker_columns := fun _ hm => (p.marker_iff.mp hm).1
    marker_order := (p.markers_ordered next).1
    phantom_marker := p.phantom_marker s.next_lower hNext
    marker_data := fun marker hm => (data marker hm).toMarkerCopyData
    reference_zero := p.initial_referenceAt_zero_extended hLast s.base_preserved hMap
    reference_caps := by
      intro lower hl higher hh hIndex
      have hStrict := hSourceValid.rows_strict lower.index higher.index
        (data lower hl).current (data higher hh).current
        (data lower hl).current_at (data higher hh).current_at hIndex
      obtain ⟨target, ceiling, degree, hReference, _hLow, hHigh, hBump, hCap⟩ :=
        p.initial_marker_reference_below_extended hLast s.base_preserved hMap hl (hRead lower hl)
          hh (hRead higher hh) hStrict
      have hTargetEq : target = (data lower hl).targetCell.row :=
        Except.ok.inj (hReference.symm.trans (data lower hl).reference)
      exact ⟨degree, by simpa only [hTargetEq, hBump] using hHigh,
        by simpa only [hBump] using hCap⟩ }
  refine ⟨d, build_source_no_premature_one p.reduced_build hSources, ?_, ?_⟩
  · intro marker hm
    exact (data marker hm).parent_power
  · intro marker hm
    exact ⟨(data marker hm).lowIndex, (data marker hm).lowCell,
      (data marker hm).low_at, (data marker hm).low_row⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.PreparedBlockState.marker_data
#print axioms OmegaY.Expansion.PreparedBlockState.column_data
