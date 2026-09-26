/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/BoundaryReferences.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/BoundaryReferences.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.RootReferenceAt
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.PreparedExtension

set_option backward.do.legacy false

/-! Reference selection in an arbitrary currently available boundary
column. Canonical root geometry is fixed by the original preparation; the
current mountain need only be valid and contain all original root-prefix
rows in the chosen boundary column. Every map below is freshly selected in
that current mountain, rather than identified with an earlier block's map. -/

namespace OmegaY.Expansion

open Canonical Geometry

def RootRowsInColumn {front : List Nat} {last : Nat} (p : Preparation front last)
    (mountain : Mountain) (column : Nat) : Prop :=
  ∀ {nodes : Column} {index : Nat} {source : Cell},
    p.initial[p.root.column]? = some nodes → nodes[index]? = some source → index ≤ p.root.index →
    ∃ ref cell, Canonical.cellAt mountain ref = .ok cell ∧ ref.column = column ∧ cell.row = source.row

theorem Preparation.reduced_root_rows {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) :
    RootRowsInColumn p p.reduced (p.reduced.size - 1) := by
  intro nodes index source hNodes hSource hIndex
  exact p.reduced_root_prefix_read hLast hNodes hSource hIndex

theorem RootRowsInColumn.column_lt {front : List Nat} {last : Nat}
    {p : Preparation front last} {mountain : Mountain} {column : Nat}
    (hRows : RootRowsInColumn p mountain column) : column < mountain.size := by
  obtain ⟨nodes, hNodes, _⟩ := cellAt_ok_iff.mp p.initial_root
  obtain ⟨hc, hNodesEq⟩ := Array.getElem?_eq_some_iff.mp hNodes
  have hValid : ColumnValid p.initial p.root.column nodes := hNodesEq ▸ p.initial_valid _ hc
  obtain ⟨ref, cell, hRead, hColumn, _⟩ := hRows hNodes hValid.phantom (Nat.zero_le _)
  obtain ⟨actualNodes, hActual, _⟩ := cellAt_ok_iff.mp hRead
  have hBound := (Array.getElem?_eq_some_iff.mp hActual).1
  simpa only [hColumn] using hBound

theorem RootRowsInColumn.preserve {front : List Nat} {last : Nat}
    {p : Preparation front last} {before after : Mountain} {column : Nat}
    (hRows : RootRowsInColumn p before column) (hPreserve : PreservesColumns before after) :
    RootRowsInColumn p after column := by
  intro nodes index source hNodes hSource hIndex
  obtain ⟨ref, cell, hRead, hColumn, hRow⟩ := hRows hNodes hSource hIndex
  obtain ⟨actualNodes, hActual, hCell⟩ := cellAt_ok_iff.mp hRead
  exact ⟨ref, cell, cellAt_ok_iff.mpr ⟨actualNodes, hPreserve.column_read hActual, hCell⟩,
    hColumn, hRow⟩

theorem RootRowsInColumn.references {front : List Nat} {last : Nat}
    {p : Preparation front last} {mountain : Mountain} {column : Nat}
    (hRows : RootRowsInColumn p mountain column) (hValid : MountainValid mountain)
    (hLast : 1 < last) :
    ∃ references, p.boundaries.mapM (below mountain column) = .ok references ∧
      List.Forall₂ (fun ceiling ref => below mountain column ceiling = .ok ref)
        p.boundaries references :=
  boundary_references_total hValid hRows.column_lt p.boundaries (p.boundaries_positive hLast)

theorem RootRowsInColumn.references_valid {front : List Nat} {last : Nat}
    {p : Preparation front last} {mountain : Mountain} {column : Nat}
    (hRows : RootRowsInColumn p mountain column) {references : List Ref}
    (hMap : p.boundaries.mapM (below mountain column) = .ok references) :
    ∀ ref ∈ references, ValidRef mountain ref :=
  below_references_valid (Array.getElem?_eq_getElem hRows.column_lt) (below_mapM_pairing hMap)

/-- The exact interval and all higher-root-row caps are independent of the
boundary column's construction. Its actual floor read is the only support
used by the strict-below selector. -/
theorem RootRowsInColumn.root_interval {front : List Nat} {last : Nat}
    {p : Preparation front last} {mountain : Mountain} {column : Nat}
    (hRows : RootRowsInColumn p mountain column) (hValid : MountainValid mountain)
    (hLast : 1 < last) {nodes : Column}
    (hColumn : p.initial[p.root.column]? = some nodes)
    {index : Nat} {lower : Cell} (hLower : nodes[index]? = some lower)
    (hIndex : index ≤ p.root.index) {references : List Ref}
    (hMap : p.boundaries.mapM (below mountain column) = .ok references) :
    ∃ ceiling degree ref cell,
      ceiling = Row.bump lower.row degree ∧ ceiling ≤ p.lastTop.row ∧
      below mountain column ceiling = .ok ref ∧ Canonical.cellAt mountain ref = .ok cell ∧
      ref.column = column ∧ referenceAt mountain references lower.row = .ok cell.row ∧
      lower.row ≤ cell.row ∧ cell.row < ceiling ∧
      ∀ higherIndex higherCell, index < higherIndex → higherIndex ≤ p.root.index →
        nodes[higherIndex]? = some higherCell → ceiling ≤ higherCell.row := by
  obtain ⟨earlier, ceiling, later, degree, hPartition, hPower, hTop, hLater, hHigher⟩ :=
    p.root_boundary_partition hLast hColumn hLower hIndex
  obtain ⟨floorRef, floorCell, hFloor, hFloorColumn, hFloorRow⟩ := hRows hColumn hLower hIndex
  have hBelow : floorCell.row < ceiling := by
    rw [hFloorRow, hPower]
    exact Row.lt_bump _ _
  obtain ⟨ref, cell, hSelected, hRead, hRefColumn, hAbove, hUpper⟩ :=
    below_between hValid hFloor hBelow
  rw [hFloorColumn] at hSelected hRefColumn
  rw [hFloorRow] at hAbove
  have hReference := referenceAt_of_boundary_partition
    (Array.getElem?_eq_getElem hRows.column_lt) hPartition hMap hSelected
    (lookup_ok_iff.mpr (cellAt_ok_iff.mp hRead)) hAbove hLater
  exact ⟨ceiling, degree, ref, cell, hPower, hTop, hSelected, hRead, hRefColumn,
    hReference, hAbove, hUpper, hHigher⟩

/-- Every original prepared marker queries the new boundary map inside the
same original root power interval. The marker is read from its frozen source. -/
theorem RootRowsInColumn.marker_interval {front : List Nat} {last : Nat}
    {p : Preparation front last} {mountain : Mountain} {column : Nat}
    (hRows : RootRowsInColumn p mountain column) (hValid : MountainValid mountain)
    (hLast : 1 < last) {references : List Ref}
    (hMap : p.boundaries.mapM (below mountain column) = .ok references)
    {bucket : Nat} {marker : Ref} {source : Cell}
    (hMarker : BucketMem p.marked bucket marker)
    (hSource : Canonical.cellAt p.reduced marker = .ok source) :
    ∃ target ceiling degree,
      referenceAt mountain references source.row = .ok target ∧
      source.row ≤ target ∧ target < ceiling ∧
      ceiling = Row.bump source.row degree ∧ ceiling ≤ p.lastTop.row := by
  obtain ⟨nodes, index, lower, hColumn, hLower, hIndex, hRow⟩ :=
    p.marker_root_prefix_read hMarker hSource
  obtain ⟨ceiling, degree, _, cell, hPower, hTop, _, _, _, hReference, hLow, hHigh, _⟩ :=
    hRows.root_interval hValid hLast hColumn hLower hIndex hMap
  exact ⟨cell.row, ceiling, degree, by simpa only [hRow] using hReference,
    by simpa only [hRow] using hLow, hHigh, by simpa only [hRow] using hPower, hTop⟩

/-- The higher row need not be a marker anywhere. Any actual higher row
of the original root prefix supplies the upper cap for this marker's lift. -/
theorem RootRowsInColumn.marker_below_root_row {front : List Nat} {last : Nat}
    {p : Preparation front last} {mountain : Mountain} {column : Nat}
    (hRows : RootRowsInColumn p mountain column) (hValid : MountainValid mountain)
    (hLast : 1 < last) {references : List Ref}
    (hMap : p.boundaries.mapM (below mountain column) = .ok references)
    {bucket : Nat} {marker : Ref} {source : Cell}
    (hMarker : BucketMem p.marked bucket marker)
    (hSource : Canonical.cellAt p.reduced marker = .ok source)
    {higherNodes : Column} {higherIndex : Nat} {higherCell : Cell}
    (hHigherColumn : p.initial[p.root.column]? = some higherNodes)
    (hHigherRead : higherNodes[higherIndex]? = some higherCell)
    (hHigherIndex : higherIndex ≤ p.root.index) (hStrict : source.row < higherCell.row) :
    ∃ target ceiling degree,
      referenceAt mountain references source.row = .ok target ∧
      source.row ≤ target ∧ target < ceiling ∧
      ceiling = Row.bump source.row degree ∧ ceiling ≤ higherCell.row := by
  obtain ⟨nodes, index, lower, hColumn, hLower, hIndex, hRow⟩ :=
    p.marker_root_prefix_read hMarker hSource
  have he : higherNodes = nodes := Option.some.inj (hHigherColumn.symm.trans hColumn)
  subst higherNodes
  have hRootStrict : lower.row < higherCell.row := by simpa only [hRow] using hStrict
  have hIndexLt : index < higherIndex :=
    (cellAt_row_lt_iff p.initial_valid.toOrdered
      (show CellAt p.initial ⟨p.root.column, index⟩ lower from ⟨nodes, hColumn, hLower⟩)
      (show CellAt p.initial ⟨p.root.column, higherIndex⟩ higherCell from ⟨nodes, hColumn, hHigherRead⟩)
      rfl).mp hRootStrict
  obtain ⟨ceiling, degree, _, cell, hPower, _, _, _, _, hReference, hLow, hHigh, hHigher⟩ :=
    hRows.root_interval hValid hLast hColumn hLower hIndex hMap
  exact ⟨cell.row, ceiling, degree, by simpa only [hRow] using hReference,
    by simpa only [hRow] using hLow, hHigh, by simpa only [hRow] using hPower,
    hHigher higherIndex higherCell hIndexLt hHigherIndex hHigherRead⟩

theorem RootRowsInColumn.marker_below_marker {front : List Nat} {last : Nat}
    {p : Preparation front last} {mountain : Mountain} {column : Nat}
    (hRows : RootRowsInColumn p mountain column) (hValid : MountainValid mountain)
    (hLast : 1 < last) {references : List Ref}
    (hMap : p.boundaries.mapM (below mountain column) = .ok references)
    {bucket nextBucket : Nat} {marker nextMarker : Ref} {source nextCell : Cell}
    (hMarker : BucketMem p.marked bucket marker)
    (hSource : Canonical.cellAt p.reduced marker = .ok source)
    (hNextMarker : BucketMem p.marked nextBucket nextMarker)
    (hNext : Canonical.cellAt p.reduced nextMarker = .ok nextCell)
    (hStrict : source.row < nextCell.row) :
    ∃ target ceiling degree,
      referenceAt mountain references source.row = .ok target ∧
      source.row ≤ target ∧ target < ceiling ∧
      ceiling = Row.bump source.row degree ∧ ceiling ≤ nextCell.row := by
  obtain ⟨nodes, index, lower, hColumn, hLower, hIndex, hRow⟩ :=
    p.marker_root_prefix_read hNextMarker hNext
  obtain ⟨target, ceiling, degree, hReference, hLow, hHigh, hPower, hCap⟩ :=
    hRows.marker_below_root_row hValid hLast hMap hMarker hSource hColumn hLower hIndex
      (by simpa only [hRow] using hStrict)
  exact ⟨target, ceiling, degree, hReference, hLow, hHigh, hPower, by simpa only [hRow] using hCap⟩

theorem RootRowsInColumn.references_end_phantom {front : List Nat} {last : Nat}
    {p : Preparation front last} {mountain : Mountain} {column : Nat}
    (hRows : RootRowsInColumn p mountain column) (hValid : MountainValid mountain)
    (hLast : 1 < last) {references : List Ref}
    (hMap : p.boundaries.mapM (below mountain column) = .ok references) :
    ∃ earlier, references = earlier ++ [⟨column, 0⟩] := by
  obtain ⟨higher, hBoundaries⟩ := p.boundaries_end_one hLast
  have hPhantom := below_one hValid hRows.column_lt
  rw [hBoundaries, List.mapM_append] at hMap
  cases hEarlier : higher.mapM (below mountain column) with
  | error error => simp [hEarlier] at hMap
  | ok earlier => exact ⟨earlier, by simpa [hEarlier, hPhantom] using hMap.symm⟩

/-- A newly selected boundary map still fixes zero exactly. The proof uses
its actual final phantom reference, not a bound inherited from an old map. -/
theorem RootRowsInColumn.referenceAt_zero {front : List Nat} {last : Nat}
    {p : Preparation front last} {mountain : Mountain} {column : Nat}
    (hRows : RootRowsInColumn p mountain column) (hValid : MountainValid mountain)
    (hLast : 1 < last) {references : List Ref}
    (hMap : p.boundaries.mapM (below mountain column) = .ok references) :
    referenceAt mountain references 0 = .ok 0 := by
  obtain ⟨earlier, hReferences⟩ := hRows.references_end_phantom hValid hLast hMap
  have hRefsValid := hRows.references_valid hMap
  rw [hReferences] at hRefsValid ⊢
  have hc : column < mountain.size := hRows.column_lt
  have hPhantom : lookup mountain ⟨column, 0⟩ = .ok phantom :=
    lookup_ok_iff.mpr ⟨mountain[column], Array.getElem?_eq_getElem hc,
      (hValid _ hc).phantom⟩
  exact referenceAt_last hRefsValid hPhantom le_rfl

end OmegaY.Expansion

#print axioms OmegaY.Expansion.RootRowsInColumn.references
#print axioms OmegaY.Expansion.RootRowsInColumn.root_interval
#print axioms OmegaY.Expansion.RootRowsInColumn.marker_below_root_row
#print axioms OmegaY.Expansion.RootRowsInColumn.referenceAt_zero
