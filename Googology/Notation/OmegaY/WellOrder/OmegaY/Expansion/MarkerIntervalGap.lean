/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/MarkerIntervalGap.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/MarkerIntervalGap.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.WeakParentPaths
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ContourAdjacent

set_option backward.do.legacy false

/-!
# Actual marker-free root intervals

The upper barrier is conditional on an actual successor. It therefore also
handles a root-column top, without inserting nonexistent intermediate rows.
Both interval endpoints are strict. The auxiliary phantom is not omitted:
the proofs apply to every actual stored root-prefix and marker node.
-/

namespace OmegaY.Geometry.Frame

/-- Every stored node of this column strictly below the upper barrier is
at or below the given node. If that node is a top, a hypothetical higher
node itself supplies the missing upper neighbour and a contradiction. -/
theorem height_le_of_upper_barrier {F : Frame} (hF : F.Ordered)
    {root node : F.Node} {cap : Row}
    (hBarrier : ∀ upper, F.upper root = some upper → cap ≤ F.height upper)
    (hColumn : node.1 = root.1) (hBelow : F.height node < cap) :
    F.height node ≤ F.height root := by
  rcases node with ⟨c, i⟩
  dsimp only at hColumn
  subst c
  apply (hF.rows_strict root.1).monotone
  by_contra hn
  have hIndex : root.2.val + 1 ≤ i.val := by change ¬ i.val ≤ root.2.val at hn; omega
  have hBound : root.2.val + 1 < F.length root.1 := lt_of_le_of_lt hIndex i.isLt
  let upper : F.Node := ⟨root.1, ⟨root.2.val + 1, hBound⟩⟩
  have hUpper : F.upper root = some upper := by simp only [Frame.upper, hBound, ↓reduceDIte, upper]
  have hUpperBelow : F.height upper ≤ F.height ⟨root.1, i⟩ :=
    (hF.rows_strict root.1).monotone hIndex
  exact not_lt_of_ge ((hBarrier upper hUpper).trans hUpperBelow) hBelow

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry

/-- Actual marker enumeration cannot put any marker in this open root-row
interval. This includes row-zero markers, without a separate realness
assumption, and does not assert absence at the cap itself. -/
theorem marker_not_in_open_interval {mountain : Mountain}
    (hOrdered : (Frame.ofMountain mountain).Ordered) (hLocal : WeakLocal mountain)
    {badRoot : Ref} (hRootValid : ValidRef mountain badRoot)
    {marked : Array (List Ref)} (hMarkers : markers mountain badRoot = .ok marked)
    {root : (Frame.ofMountain mountain).Node} {cap : Row}
    (hRootColumn : root.1.val = badRoot.column)
    (hBarrier : ∀ upper, (Frame.ofMountain mountain).upper root = some upper →
      cap ≤ (Frame.ofMountain mountain).height upper)
    {bucket : Nat} {marker : Ref} (hMarker : BucketMem marked bucket marker)
    {cell : Cell} (hCell : Canonical.cellAt mountain marker = .ok cell) :
    ¬ ((Frame.ofMountain mountain).height root < cell.row ∧ cell.row < cap) := by
  rintro ⟨hLower, hUpper⟩
  obtain ⟨_, _, _, index, hIndex, path⟩ := (markers_member_iff hLocal hRootValid hMarkers).mp hMarker
  obtain ⟨rootCell, hRootCell⟩ := hRootValid.lookup_below_index hIndex
  obtain ⟨low, hLowRef, hLowCell⟩ := frame_node_of_cellAt (lookup_ok_iff.mp hRootCell)
  have hLowColumn : low.1 = root.1 := by
    apply Fin.ext
    have hRefColumn := congrArg Ref.column hLowRef
    change low.1.val = badRoot.column at hRefColumn
    exact hRefColumn.trans hRootColumn.symm
  have hSameRow : cell.row = (Frame.ofMountain mountain).height low := by
    have hRow := path.row_eq (lookup_ok_iff.mp hRootCell) (cellAt_ok_iff.mp hCell)
    simpa only [Frame.height, hLowCell] using hRow
  have hBelow : (Frame.ofMountain mountain).height low < cap := by
    simpa only [hSameRow] using hUpper
  have hBound := Frame.height_le_of_upper_barrier hOrdered hBarrier hLowColumn hBelow
  exact not_lt_of_ge hBound (by simpa only [hSameRow] using hLower)

namespace ColumnCopyData

variable {mountain base : Mountain} {marked : Array (List Ref)} {references : List Ref}
  {sourceColumn shift rootColumn : Nat}
  (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)

include d

/-- A root-column gap gives the exact inclusive index upper bound needed
by the actual contour traversal. The source endpoint row remains strictly
below `cap`; a marker on `cap` is deliberately not excluded. -/
theorem no_markers_through_source_index
    (hOrdered : (Frame.ofMountain base).Ordered) (hLocal : WeakLocal base)
    {badRoot : Ref} (hRootValid : ValidRef base badRoot)
    (hMarkers : markers base badRoot = .ok marked)
    (hSource : base[sourceColumn]? = some d.sources)
    {root : (Frame.ofMountain base).Node} {cap : Row}
    (hRootColumn : root.1.val = badRoot.column)
    (hBarrier : ∀ upper, (Frame.ofMountain base).upper root = some upper →
      cap ≤ (Frame.ofMountain base).height upper)
    {marker : Ref} (hm : marker ∈ d.bucket)
    (hMarkerRow : (d.marker_data marker hm).current.row = (Frame.ofMountain base).height root)
    {upperIndex : Nat} {upperCell : Cell} (hUpper : d.sources[upperIndex]? = some upperCell)
    (hBelow : upperCell.row < cap) :
    ∀ middle, marker.index < middle → middle ≤ upperIndex → middle ∉ d.bucket.map Ref.index := by
  intro middle hAfter hBefore hMember
  obtain ⟨entry, hEntry, hIndex⟩ := List.mem_map.mp hMember
  let md := d.marker_data entry hEntry
  have hEntryRead : Canonical.cellAt base entry = .ok md.current :=
    cellAt_ok_iff.mpr ⟨d.sources, by simpa only [d.marker_columns entry hEntry] using hSource, md.current_at⟩
  have hLower : (Frame.ofMountain base).height root < md.current.row := by
    rw [← hMarkerRow]
    exact d.source_valid.rows_strict _ _ _ _ (d.marker_data marker hm).current_at md.current_at
      (by omega)
  have hUpperBound : md.current.row ≤ upperCell.row := by
    rcases eq_or_lt_of_le (show entry.index ≤ upperIndex by omega) with he | hl
    · have hCell : md.current = upperCell := Option.some.inj
        (md.current_at.symm.trans (by simpa only [he] using hUpper))
      exact le_of_eq (congrArg Cell.row hCell)
    · exact le_of_lt (d.source_valid.rows_strict _ _ _ _ md.current_at hUpper hl)
  exact marker_not_in_open_interval hOrdered hLocal hRootValid hMarkers hRootColumn hBarrier
    hEntry hEntryRead ⟨hLower, hUpperBound.trans_lt hBelow⟩

end ColumnCopyData

/-- The prepared construction supplies the ordered root graph and weak
marker validity; only actual frozen source reads and the root barrier are
needed to produce the traversal's no-interruption condition. -/
theorem ColumnCopyData.prepared_no_markers_through_source_index
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {mountain : Mountain} {references : List Ref} {sourceColumn shift : Nat}
    (d : ColumnCopyData mountain p.marked references sourceColumn shift p.root.column)
    (hSource : p.reduced[sourceColumn]? = some d.sources)
    {root : (Frame.ofMountain p.reduced).Node} {cap : Row}
    (hRootColumn : root.1.val = p.root.column)
    (hBarrier : ∀ upper, (Frame.ofMountain p.reduced).upper root = some upper →
      cap ≤ (Frame.ofMountain p.reduced).height upper)
    {marker : Ref} (hm : marker ∈ d.bucket)
    (hMarkerRow : (d.marker_data marker hm).current.row = (Frame.ofMountain p.reduced).height root)
    {upperIndex : Nat} {upperCell : Cell} (hUpper : d.sources[upperIndex]? = some upperCell)
    (hBelow : upperCell.row < cap) :
    ∀ middle, marker.index < middle → middle ≤ upperIndex → middle ∉ d.bucket.map Ref.index :=
  d.no_markers_through_source_index p.reduced_valid.toOrdered
    (weakLocal_of_ordered p.reduced_valid.toOrdered p.reduced_valid.left_sources)
    p.root_valid p.markers_built hSource hRootColumn hBarrier hm hMarkerRow hUpper hBelow

/-- A real source pair strictly inside the root-row gap is visited by the
actual contour and remains adjacent after the complete column finish.
No marker-absence or output-adjacency condition is assumed. -/
theorem ColumnCopyData.prepared_source_adjacent_below_cap
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {mountain : Mountain} {references : List Ref} {sourceColumn shift : Nat}
    (d : ColumnCopyData mountain p.marked references sourceColumn shift p.root.column)
    (hSource : p.reduced[sourceColumn]? = some d.sources)
    (hParentPower : ∀ marker (hm : marker ∈ d.bucket),
      ColumnPowerSteps (d.marker_data marker hm).parentNodes)
    (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (index : Nat) (cell : Cell),
      (d.marker_data marker hm).parentNodes[index]? = some cell ∧
        cell.row = (d.marker_data marker hm).current.row)
    (hNoPremature : NoPrematureOne d.sources)
    {root : (Frame.ofMountain p.reduced).Node} {cap : Row}
    (hRootColumn : root.1.val = p.root.column)
    (hBarrier : ∀ upper, (Frame.ofMountain p.reduced).upper root = some upper →
      cap ≤ (Frame.ofMountain p.reduced).height upper)
    {column : Column}
    (hRun : copyColumn mountain p.marked references sourceColumn shift p.root.column = .ok column)
    {marker : Ref} (hm : marker ∈ d.bucket)
    (hMarkerRow : (d.marker_data marker hm).current.row = (Frame.ofMountain p.reduced).height root)
    {sourceIndex : Nat} {oldLower oldUpper : Cell}
    (hLower : d.sources[sourceIndex]? = some oldLower)
    (hUpper : d.sources[sourceIndex + 1]? = some oldUpper)
    (hAfter : marker.index < sourceIndex) (hBelow : oldUpper.row < cap) :
    ∃ (position : Nat) (lower upper : Cell),
      column[position]? = some lower ∧ column[position + 1]? = some upper ∧
      lower.row = Row.lift (d.marker_data marker hm).current.row
        (d.marker_data marker hm).targetCell.row oldLower.row ∧
      upper.row = Row.lift (d.marker_data marker hm).current.row
        (d.marker_data marker hm).targetCell.row oldUpper.row := by
  have hNoBetween := d.prepared_no_markers_through_source_index hSource hRootColumn hBarrier hm
    hMarkerRow hUpper hBelow
  exact d.copyColumn_source_adjacent_of_no_between hParentPower hParentLow hNoPremature hRun hm
    hLower hUpper hAfter hNoBetween

end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.height_le_of_upper_barrier
#print axioms OmegaY.Expansion.marker_not_in_open_interval
#print axioms OmegaY.Expansion.ColumnCopyData.no_markers_through_source_index
#print axioms OmegaY.Expansion.ColumnCopyData.prepared_no_markers_through_source_index
#print axioms OmegaY.Expansion.ColumnCopyData.prepared_source_adjacent_below_cap
