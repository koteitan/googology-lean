/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ColumnCopyData.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/ColumnCopyData.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.SegmentPositive
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.SegmentLegs
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ColumnSegments
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.InitialBaseRows
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.FinishPreservation

set_option backward.do.legacy false

/-!
# Generic actual column-copy completion from local input geometry

The records contain source reads, selected target reads, and finite input
geometry. They contain no successful segment/column/finish execution and no
candidate-list invariant. The theorem derives those conclusions for the
unchanged executable `copyColumn`.

A block-width induction must still supply the target's actual occurrence
in each shifted parent column and the reference caps. This module neither
constructs that induction nor assumes copied-column canonicality.
-/

namespace OmegaY.Expansion

open Canonical

/-- Actual local reads needed for one marker. The selected target belongs
to the particular shifted parent column used by the real fill loop. -/
structure MarkerCopyData (mountain : Mountain) (sources : Column) (references : List Ref)
    (shift index : Nat) where
  current : Cell
  upper : Cell
  sourceParent : Ref
  parentNodes : Column
  targetIndex : Nat
  targetCell : Cell
  current_at : sources[index]? = some current
  upper_at : sources[index + 1]? = some upper
  upper_left : upper.left = some sourceParent
  parent_nodes : mountain[sourceParent.column + shift]? = some parentNodes
  target_at : parentNodes[targetIndex]? = some targetCell
  reference : referenceAt mountain references current.row = .ok targetCell.row
  target_lower : current.row ≤ targetCell.row

/-- Input-only conditions for one actual source column and marker bucket.
The cap conditions concern selected target rows and source marker rows,
never the as-yet unconstructed output segments. -/
structure ColumnCopyData (mountain : Mountain) (marked : Array (List Ref))
    (references : List Ref) (sourceColumn shift rootColumn : Nat) where
  sources : Column
  ambient_valid : MountainValid mountain
  source_column : mountain[sourceColumn]? = some sources
  source_nonzero : 0 < sourceColumn
  destination : sourceColumn + shift = mountain.size
  source_top : TopOne sources
  source_power : ColumnPowerSteps sources
  source_positive : SourceAboveBottomPositive mountain sources
  marker_columns : ∀ marker ∈ marked[sourceColumn]?.getD [], marker.column = sourceColumn
  marker_order : (marked[sourceColumn]?.getD []).Pairwise (fun higher lower => lower.index < higher.index)
  phantom_marker : (⟨sourceColumn, 0⟩ : Ref) ∈ marked[sourceColumn]?.getD []
  marker_data : ∀ marker ∈ marked[sourceColumn]?.getD [],
    MarkerCopyData mountain sources references shift marker.index
  reference_zero : referenceAt mountain references 0 = .ok 0
  reference_caps : ∀ lower (hLower : lower ∈ marked[sourceColumn]?.getD [])
      higher (hHigher : higher ∈ marked[sourceColumn]?.getD []), lower.index < higher.index →
    ∃ scale, (marker_data lower hLower).targetCell.row <
        Row.bump (marker_data lower hLower).current.row scale ∧
      Row.bump (marker_data lower hLower).current.row scale ≤ (marker_data higher hHigher).current.row

namespace ColumnCopyData

variable {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
  {sourceColumn shift rootColumn : Nat}
  (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)

abbrev bucket (_data : ColumnCopyData mountain marked references sourceColumn shift rootColumn) :
    List Ref := marked[sourceColumn]?.getD []

def segment (marker : Ref) : List Cell :=
  (copySegment mountain d.sources references sourceColumn (d.bucket.map Ref.index)
    shift rootColumn marker.index).toOption.getD []

def candidates : List Cell := d.bucket.flatMap d.segment

include d

theorem source_valid : ColumnValid mountain sourceColumn d.sources := by
  obtain ⟨hc, hSources⟩ := Array.getElem?_eq_some_iff.mp d.source_column
  exact hSources ▸ d.ambient_valid _ hc

theorem target_zero {marker : Ref} (hm : marker ∈ d.bucket)
    (hZero : (d.marker_data marker hm).current.row = 0) :
    (d.marker_data marker hm).targetCell.row = 0 := by
  have hRef := (d.marker_data marker hm).reference
  rw [hZero] at hRef
  exact Except.ok.inj (hRef.symm.trans d.reference_zero)

/-- The default in `segment` is harmless because actual success is derived
here from source and target reads, before any output property is used. -/
theorem segment_run {marker : Ref} (hm : marker ∈ d.bucket) :
    copySegment mountain d.sources references sourceColumn (d.bucket.map Ref.index)
      shift rootColumn marker.index = .ok (d.segment marker) := by
  let s := d.marker_data marker hm
  obtain ⟨copied, path, gap, _, _, _, _, _, hRun, _, _⟩ :=
    copySegment_total_nodup d.ambient_valid d.source_column d.source_nonzero d.destination.le d.source_top
      references (d.bucket.map Ref.index) s.current_at s.upper_at s.upper_left s.parent_nodes s.target_at
      s.reference s.target_lower
      (rootColumn := rootColumn)
  have hValue : d.segment marker = [copied] ++ path ++ gap := by
    simp only [segment, hRun, Except.toOption, Option.getD_some]
  simpa only [hValue] using hRun

theorem segment_bounds {marker : Ref} (hm : marker ∈ d.bucket) :
    ((d.segment marker).map Cell.row).Nodup ∧
      (d.marker_data marker hm).current.row ∈ (d.segment marker).map Cell.row ∧
      ∀ cell ∈ d.segment marker, (d.marker_data marker hm).current.row ≤ cell.row := by
  let s := d.marker_data marker hm
  exact copySegment_result_bounds d.ambient_valid d.source_column d.source_nonzero d.destination.le
    d.source_top references _ s.current_at s.upper_at s.upper_left s.parent_nodes s.target_at
    s.reference s.target_lower (d.segment_run hm)

theorem segment_positive {marker : Ref} (hm : marker ∈ d.bucket) :
    ∀ cell ∈ d.segment marker, (1 : Row) < cell.row →
      ∃ parent parentCell, cell.left = some parent ∧ lookup mountain parent = .ok parentCell ∧
        0 < parentCell.value := by
  let s := d.marker_data marker hm
  exact copySegment_positive_of_source d.ambient_valid d.source_column d.source_nonzero d.destination.le
    d.source_top d.source_power d.source_positive references _ s.current_at s.upper_at s.upper_left
    s.parent_nodes s.target_at s.reference s.target_lower (d.target_zero hm) (d.segment_run hm)

theorem segment_legs {marker : Ref} (hm : marker ∈ d.bucket) :
    ∀ cell ∈ d.segment marker, CellLegs mountain mountain.size cell := by
  let s := d.marker_data marker hm
  have hLegs := copySegment_legs_of_source d.ambient_valid d.source_column d.source_nonzero
    d.destination.le d.source_top d.source_power references _ s.current_at s.upper_at s.upper_left
    s.parent_nodes s.target_at s.reference s.target_lower (d.segment_run hm)
  simpa only [d.destination] using hLegs

theorem segment_lt_marker {lower higher : Ref} (hl : lower ∈ d.bucket) (hh : higher ∈ d.bucket)
    (hIndex : lower.index < higher.index) :
    ∀ cell ∈ d.segment lower, cell.row < (d.marker_data higher hh).current.row := by
  let lo := d.marker_data lower hl
  let hi := d.marker_data higher hh
  obtain ⟨scale, hTarget, hCap⟩ := d.reference_caps lower hl higher hh hIndex
  exact copySegment_result_lt_next_marker d.ambient_valid d.source_column d.source_nonzero
    d.destination.le d.source_top references _ lo.current_at lo.upper_at lo.upper_left lo.parent_nodes
    lo.target_at lo.reference lo.target_lower (d.segment_run hl) d.source_power hi.current_at
    (List.mem_map.mpr ⟨higher, hh, rfl⟩) hIndex hTarget hCap

theorem candidates_nodup : (d.candidates.map Cell.row).Nodup := by
  rw [candidates, List.map_flatMap]
  apply List.nodup_flatMap.mpr
  constructor
  · intro marker hm
    exact (d.segment_bounds hm).1
  · apply d.marker_order.imp_of_mem
    intro higher lower hh hl hIndex
    apply List.disjoint_left.mpr
    intro row hHigher hLower
    obtain ⟨higherCell, hHigherMem, hHigherRow⟩ := List.mem_map.mp hHigher
    obtain ⟨lowerCell, hLowerMem, hLowerRow⟩ := List.mem_map.mp hLower
    have hFloor := (d.segment_bounds hh).2.2 higherCell hHigherMem
    have hCeiling := d.segment_lt_marker hl hh hIndex lowerCell hLowerMem
    rw [hHigherRow] at hFloor
    rw [hLowerRow] at hCeiling
    exact (not_lt_of_ge hFloor) hCeiling

theorem candidates_positive :
    ∀ cell ∈ d.candidates, (1 : Row) < cell.row →
      ∃ parent parentCell, cell.left = some parent ∧ lookup mountain parent = .ok parentCell ∧
        0 < parentCell.value := by
  intro cell hCell hAbove
  obtain ⟨marker, hm, hCell⟩ := List.mem_flatMap.mp hCell
  exact d.segment_positive hm cell hCell hAbove

theorem candidates_legs : ∀ cell ∈ d.candidates, CellLegs mountain mountain.size cell := by
  intro cell hCell
  obtain ⟨marker, hm, hCell⟩ := List.mem_flatMap.mp hCell
  exact d.segment_legs hm cell hCell

theorem candidates_phantom : phantom ∈ d.candidates := by
  let marker : Ref := ⟨sourceColumn, 0⟩
  have hm : marker ∈ d.bucket := d.phantom_marker
  let s := d.marker_data marker hm
  have hCurrent : s.current = phantom := Option.some.inj (s.current_at.symm.trans d.source_valid.phantom)
  obtain ⟨copied, path, gap, hResult, hCopy, _, _, _, _, _, _, _⟩ :=
    copySegment_result_decomposition d.ambient_valid d.source_column d.source_nonzero d.destination.le
      d.source_top references _ s.current_at s.upper_at s.upper_left s.parent_nodes s.target_at
      s.reference s.target_lower (d.segment_run hm)
  have hPhantomRead : lookup mountain ⟨sourceColumn, 0⟩ = .ok phantom :=
    lookup_ok_iff.mpr ⟨d.sources, d.source_column, d.source_valid.phantom⟩
  have hCopied : copied = phantom := by
    rw [hCurrent] at hCopy
    exact Except.ok.inj (hCopy.symm.trans (copyEdge_phantom hPhantomRead rfl _ _ 0))
  exact List.mem_flatMap.mpr ⟨marker, hm, by rw [hResult, hCopied]; simp⟩

theorem candidates_one : (1 : Row) ∈ d.candidates.map Cell.row := by
  have hCV := d.source_valid
  have hSize := hCV.size_ge_two
  have hb : 1 < d.sources.size := by omega
  let bottom := d.sources[1]
  let bottomRef : Ref := ⟨sourceColumn, 1⟩
  have hBottom : d.sources[1]? = some bottom := Array.getElem?_eq_getElem hb
  have hBottomRow := hCV.bottom_row bottom hBottom
  by_cases hBottomMarker : bottomRef ∈ d.bucket
  · let s := d.marker_data bottomRef hBottomMarker
    have hCurrent : s.current = bottom := Option.some.inj (s.current_at.symm.trans hBottom)
    have hMem := (d.segment_bounds hBottomMarker).2.1
    obtain ⟨cell, hCell, hRow⟩ := List.mem_map.mp hMem
    exact List.mem_map.mpr ⟨cell, List.mem_flatMap.mpr ⟨bottomRef, hBottomMarker, hCell⟩,
      hRow.trans ((congrArg Cell.row hCurrent).trans hBottomRow)⟩
  · have hNotMarked : 1 ∉ d.bucket.map Ref.index := by
      intro h
      obtain ⟨entry, hm, hIndex⟩ := List.mem_map.mp h
      have hColumn := d.marker_columns entry hm
      have he : entry = bottomRef := by
        cases entry
        simp_all only [bottomRef]
      exact hBottomMarker (he ▸ hm)
    let marker : Ref := ⟨sourceColumn, 0⟩
    have hm : marker ∈ d.bucket := d.phantom_marker
    let s := d.marker_data marker hm
    have hCurrent : s.current = phantom := Option.some.inj (s.current_at.symm.trans hCV.phantom)
    have hZero : s.targetCell.row = 0 := d.target_zero hm (congrArg Cell.row hCurrent)
    obtain ⟨copied, path, gap, hResult, _, _, _, hContour, _, _, _, _⟩ :=
      copySegment_result_decomposition d.ambient_valid d.source_column d.source_nonzero d.destination.le
        d.source_top references _ s.current_at s.upper_at s.upper_left s.parent_nodes s.target_at
        s.reference s.target_lower (d.segment_run hm)
    rw [hCurrent, hZero] at hContour
    have hOne := contour_phantom_contains_one d.ambient_valid d.source_column d.source_nonzero
      d.destination.le d.source_top _ hNotMarked hContour
    obtain ⟨cell, hCell, hRow⟩ := List.mem_map.mp hOne
    exact List.mem_map.mpr ⟨cell, List.mem_flatMap.mpr
      ⟨marker, hm, by rw [hResult]; simp [hCell]⟩, hRow⟩

theorem finish_input : FinishInput mountain d.candidates := {
  rows_nodup := d.candidates_nodup
  phantom_mem := d.candidates_phantom
  bottom_mem := List.mem_map.mp d.candidates_one
  parents_above_one := d.candidates_positive }

theorem copyColumn_eq_finish :
    copyColumn mountain marked references sourceColumn shift rootColumn = finish mountain d.candidates :=
  copyColumn_eq_finish_segments d.source_column d.segment d.marker_columns (fun _ hm => d.segment_run hm)

/-- Full success of the frozen executable column copier, including local
validity and appendability. All hypotheses are the preceding input record;
none asserts successful execution or an output invariant. -/
theorem copyColumn_valid :
    ∃ column, copyColumn mountain marked references sourceColumn shift rootColumn = .ok column ∧
      FinishedColumn mountain column ∧ ColumnValid mountain mountain.size column ∧
      TopOne column ∧ MountainValid (mountain.push column) := by
  have hSize : 0 < mountain.size := by
    have hPositive := d.source_nonzero
    have hDestination := d.destination
    omega
  obtain ⟨column, hFinish, _, hFinished, hValid, hTop⟩ := d.finish_input.finish_valid hSize
    (fun cell hCell => (d.candidates_legs cell hCell).1)
    (fun cell hCell => (d.candidates_legs cell hCell).2)
  exact ⟨column, d.copyColumn_eq_finish.trans hFinish, hFinished, hValid, hTop,
    d.ambient_valid.push hValid⟩

end ColumnCopyData

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ColumnCopyData.segment_run
#print axioms OmegaY.Expansion.ColumnCopyData.candidates_nodup
#print axioms OmegaY.Expansion.ColumnCopyData.finish_input
#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_valid
