/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ContourCapBarrier.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/ContourCapBarrier.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.MarkerIntervalGap
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.BoundarySelection

set_option backward.do.legacy false

/-!
# The actual copied barrier at a crossed root cap

An unmarked upper source node remains the adjacent contour node. When it
is marked, the current contour ends at its predecessor, lower marker
segments stay below the starting marker, and higher segments start at or
above the cap. Both cases give a barrier on actual finished column reads.
-/

namespace OmegaY.Expansion

open Canonical Geometry

private theorem cap_suffix_cons {nodes : Column} {index : Nat} {upper : Cell}
    {rest : List Cell} (hRest : nodes.toList.drop (index + 1) = upper :: rest) :
    nodes[index + 1]? = some upper ∧ nodes.toList.drop ((index + 1) + 1) = rest := by
  constructor
  · simpa only [List.head?_drop, Array.getElem?_toList, List.head?_cons]
      using congrArg List.head? hRest
  · simpa only [List.tail_drop, List.tail_cons] using congrArg List.tail hRest

/-- If the actual upper index is the next marker, the source contour ends
at its actual predecessor, not at a synthetic cap node. -/
theorem contourSourceCells_ends_before_marker {nodes : Column}
    (hNoPremature : NoPrematureOne nodes) (markerIndices : List Nat)
    {index sourceIndex : Nat} {current sourceCell : Cell}
    (hCurrent : nodes[index]? = some current) (hSource : nodes[sourceIndex]? = some sourceCell)
    (hAfter : index < sourceIndex)
    (hNoBetween : ∀ middle, index < middle → middle ≤ sourceIndex → middle ∉ markerIndices)
    (hMarked : sourceIndex + 1 ∈ markerIndices)
    {rest : List Cell} (hRest : nodes.toList.drop (index + 1) = rest) :
    ∃ before, contourSourceCells markerIndices index current rest = before ++ [sourceCell] := by
  induction rest generalizing index current with
  | nil =>
    have hSize : nodes.size ≤ index + 1 := by
      simpa only [Array.length_toList] using List.drop_eq_nil_iff.mp hRest
    have hBound := (Array.getElem?_eq_some_iff.mp hSource).1
    omega
  | cons upper rest ih =>
    obtain ⟨hUpper, hTail⟩ := cap_suffix_cons hRest
    have hNoStop : ¬ (current.value = 1 ∨ index + 1 ∈ markerIndices) := not_or.mpr
      ⟨hNoPremature index current upper hCurrent hUpper,
        hNoBetween (index + 1) (by omega) (by omega)⟩
    rw [contourSourceCells, if_neg hNoStop]
    by_cases he : index + 1 = sourceIndex
    · have hSame : upper = sourceCell := Option.some.inj
        (hUpper.symm.trans (by simpa only [he] using hSource))
      have hStop : upper.value = 1 ∨ (index + 1) + 1 ∈ markerIndices :=
        Or.inr (by simpa only [he] using hMarked)
      refine ⟨[], ?_⟩
      cases rest with
      | nil => simp only [contourSourceCells, hSame, List.nil_append]
      | cons first rest =>
        rw [contourSourceCells, if_pos hStop]
        simp only [hSame, List.nil_append]
    · obtain ⟨before, hBefore⟩ := ih hUpper (by omega)
        (fun middle hlo hhi => hNoBetween middle (by omega) hhi) hTail
      exact ⟨upper :: before, by simp only [hBefore, List.cons_append]⟩

private theorem le_last_of_pairwise_append {before : List Row} {last row : Row}
    (hStrict : (before ++ [last]).Pairwise (· < ·))
    (hMem : row ∈ before ++ [last]) : row ≤ last := by
  rcases List.mem_append.mp hMem with hBefore | hLast
  · exact ((List.pairwise_append.mp hStrict).2.2 row hBefore last (by simp)).le
  · exact le_of_eq (List.mem_singleton.mp hLast)

private theorem row_barrier_of_adjacent {mountain : Mountain} {column : Column} {c index : Nat}
    (hValid : ColumnValid mountain c column) {lower upper : Cell}
    (hLower : column[index]? = some lower) (hUpper : column[index + 1]? = some upper)
    {cap : Row} (hCap : cap ≤ upper.row) :
    ∀ (otherIndex : Nat) (other : Cell), column[otherIndex]? = some other → lower.row < other.row → cap ≤ other.row := by
  intro otherIndex other hOther hAbove
  have hIndex : index + 1 ≤ otherIndex := by
    by_contra hn
    rcases eq_or_lt_of_le (show otherIndex ≤ index by omega) with he | hl
    · have hSame : other = lower := Option.some.inj
        (hOther.symm.trans (by simpa only [he] using hLower))
      exact (ne_of_lt hAbove) (congrArg Cell.row hSame).symm
    · exact (lt_asymm hAbove) (hValid.rows_strict _ _ _ _ hOther hLower hl)
  rcases eq_or_lt_of_le hIndex with he | hl
  · have hSame : upper = other := Option.some.inj
      (hUpper.symm.trans (by simpa only [he] using hOther))
    simpa only [hSame] using hCap
  · exact hCap.trans (hValid.rows_strict _ _ _ _ hUpper hOther hl).le

/-- A barrier on actual stored rows determines the executable strict-below
selection throughout the whole nonempty ceiling interval. -/
theorem below_eq_of_row_barrier {mountain : Mountain} {column : Nat} {nodes : Column}
    (hNodes : mountain[column]? = some nodes) (hValid : ColumnValid mountain column nodes)
    {index : Nat} {cell : Cell} (hCell : nodes[index]? = some cell) {cap ceiling : Row}
    (hBarrier : ∀ (otherIndex : Nat) (other : Cell), nodes[otherIndex]? = some other →
      cell.row < other.row → cap ≤ other.row)
    (hLow : cell.row < ceiling) (hHigh : ceiling ≤ cap) :
    below mountain column ceiling = .ok ⟨column, index⟩ := by
  obtain ⟨found, hFound⟩ := (below_succeeds_iff hNodes ceiling).mpr ⟨index, cell, hCell, hLow⟩
  obtain ⟨hColumn, actual, hActual, hActualBelow⟩ := below_result hNodes hFound
  have hAtLeast := below_max_index hNodes hFound hCell hLow
  have hAtMost : found.index ≤ index := by
    by_contra hn
    have hAbove := hValid.rows_strict _ _ _ _ hCell hActual (by omega)
    exact (not_lt_of_ge (hHigh.trans (hBarrier found.index actual hActual hAbove))) hActualBelow
  have hIndex : found.index = index := by omega
  have hRef : found = ⟨column, index⟩ := by cases found; simp_all only
  simpa only [hRef] using hFound

namespace ColumnCopyData

variable {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
  {sourceColumn shift rootColumn : Nat}
  (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)

include d

/-- When the next source node is marked, the actual present segment ends
at the lifted source node and every segment cell is at or below that row. -/
theorem segment_max_before_marker (hNoPremature : NoPrematureOne d.sources)
    {marker : Ref} (hm : marker ∈ d.bucket) {sourceIndex : Nat} {sourceCell : Cell}
    (hSource : d.sources[sourceIndex]? = some sourceCell) (hAfter : marker.index < sourceIndex)
    (hNoBetween : ∀ middle, marker.index < middle → middle ≤ sourceIndex →
      middle ∉ d.bucket.map Ref.index)
    (hMarked : sourceIndex + 1 ∈ d.bucket.map Ref.index) :
    Row.lift (d.marker_data marker hm).current.row (d.marker_data marker hm).targetCell.row sourceCell.row ∈
        (d.segment marker).map Cell.row ∧
      ∀ cell ∈ d.segment marker, cell.row ≤ Row.lift (d.marker_data marker hm).current.row
        (d.marker_data marker hm).targetCell.row sourceCell.row := by
  let s := d.marker_data marker hm
  obtain ⟨sourceBefore, hSourcePath⟩ := contourSourceCells_ends_before_marker hNoPremature
    (d.bucket.map Ref.index) s.current_at hSource hAfter hNoBetween hMarked rfl
  obtain ⟨copied, path, gap, hResult, _, hCopiedRow, _, hContour, _, _, hStrict, hGap⟩ :=
    copySegment_result_decomposition d.ambient_valid d.source_column d.source_nonzero d.destination.le
      d.source_top references (d.bucket.map Ref.index) s.current_at s.upper_at s.upper_left
      s.parent_nodes s.target_at s.reference s.target_lower (d.segment_run hm)
  have hRows := contour_rows_eq_lift_of_success d.ambient_valid d.source_column d.source_nonzero
    d.destination.le d.source_top d.source_power (d.bucket.map Ref.index) s.targetCell.row s.current_at rfl hContour
  rw [hSourcePath, List.map_append, List.map_singleton] at hRows
  have hPathMem : Row.lift s.current.row s.targetCell.row sourceCell.row ∈ path.map Cell.row := by
    rw [hRows]
    simp
  have hTargetBound : s.targetCell.row ≤ Row.lift s.current.row s.targetCell.row sourceCell.row :=
    Row.lift_ge_target _ _ _
  have hPathBound : ∀ cell ∈ path, cell.row ≤ Row.lift s.current.row s.targetCell.row sourceCell.row := by
    intro cell hCell
    apply le_last_of_pairwise_append (by simpa only [hRows, List.tail_cons] using hStrict.tail)
    simpa only [hRows] using (List.mem_map.mpr ⟨cell, hCell, rfl⟩ : cell.row ∈ path.map Cell.row)
  constructor
  · rw [hResult]
    simp only [List.map_append, List.mem_append]
    exact Or.inl (Or.inr hPathMem)
  · intro cell hCell
    rw [hResult] at hCell
    rcases List.mem_append.mp hCell with hFirst | hGapCell
    · rcases List.mem_append.mp hFirst with hCopied | hPathCell
      · have he := List.mem_singleton.mp hCopied
        simpa only [he, hCopiedRow] using s.target_lower.trans hTargetBound
      · exact hPathBound cell hPathCell
    · exact (hGap cell hGapCell).2.trans hTargetBound

/-- The marked-upper case gives a whole-candidate barrier. Lower source
segments cannot intrude, and every higher segment starts above the cap. -/
theorem candidates_barrier_before_marker (hNoPremature : NoPrematureOne d.sources)
    {marker : Ref} (hm : marker ∈ d.bucket) {sourceIndex : Nat} {sourceCell sourceUpper : Cell}
    (hSource : d.sources[sourceIndex]? = some sourceCell)
    (hUpper : d.sources[sourceIndex + 1]? = some sourceUpper) (hAfter : marker.index < sourceIndex)
    (hNoBetween : ∀ middle, marker.index < middle → middle ≤ sourceIndex →
      middle ∉ d.bucket.map Ref.index)
    (hMarked : sourceIndex + 1 ∈ d.bucket.map Ref.index) {cap : Row} (hCap : cap ≤ sourceUpper.row) :
    Row.lift (d.marker_data marker hm).current.row (d.marker_data marker hm).targetCell.row sourceCell.row ∈
        d.candidates.map Cell.row ∧
      ∀ cell ∈ d.candidates, cell.row ≤ Row.lift (d.marker_data marker hm).current.row
        (d.marker_data marker hm).targetCell.row sourceCell.row ∨ cap ≤ cell.row := by
  obtain ⟨hOwnMem, hOwnBound⟩ := d.segment_max_before_marker hNoPremature hm hSource hAfter hNoBetween hMarked
  refine ⟨d.segment_row_mem_candidates hm hOwnMem, ?_⟩
  intro cell hCell
  obtain ⟨other, hOther, hCell⟩ := List.mem_flatMap.mp hCell
  rcases lt_trichotomy other.index marker.index with hBelow | hEqual | hAbove
  · apply Or.inl
    have hCellBelow := d.segment_lt_marker hOther hm hBelow cell hCell
    exact hCellBelow.le.trans ((d.marker_data marker hm).target_lower.trans (Row.lift_ge_target _ _ _))
  · have hSame : other = marker := by
      cases other with | mk c i =>
        cases marker with | mk c' i' =>
          have hc := d.marker_columns ⟨c, i⟩ hOther
          have hc' := d.marker_columns ⟨c', i'⟩ hm
          simp_all only
    subst other
    exact Or.inl (hOwnBound cell hCell)
  · have hIndex : sourceIndex + 1 ≤ other.index := by
      by_contra hn
      exact hNoBetween other.index hAbove (by omega) (List.mem_map.mpr ⟨other, hOther, rfl⟩)
    have hSourceBound : sourceUpper.row ≤ (d.marker_data other hOther).current.row := by
      rcases eq_or_lt_of_le hIndex with he | hl
      · have hSame : sourceUpper = (d.marker_data other hOther).current := Option.some.inj
          (hUpper.symm.trans (by simpa only [he] using (d.marker_data other hOther).current_at))
        exact le_of_eq (congrArg Cell.row hSame)
      · exact (d.source_valid.rows_strict _ _ _ _ hUpper (d.marker_data other hOther).current_at hl).le
    exact Or.inr (hCap.trans (hSourceBound.trans ((d.segment_bounds hOther).2.2 cell hCell)))

section ParentInputs

variable
  (hParentPower : ∀ marker (hm : marker ∈ d.bucket),
    ColumnPowerSteps (d.marker_data marker hm).parentNodes)
  (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (index : Nat) (cell : Cell),
    (d.marker_data marker hm).parentNodes[index]? = some cell ∧
      cell.row = (d.marker_data marker hm).current.row)
  (hNoPremature : NoPrematureOne d.sources)

include hParentPower hParentLow hNoPremature

/-- A crossed cap is a barrier on the actual copied column, whether the
source upper is marked or is itself copied by this contour. -/
theorem copyColumn_crossed_cap_barrier {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {marker : Ref} (hm : marker ∈ d.bucket) {sourceIndex : Nat} {sourceCell sourceUpper : Cell}
    (hSource : d.sources[sourceIndex]? = some sourceCell)
    (hUpper : d.sources[sourceIndex + 1]? = some sourceUpper) (hAfter : marker.index < sourceIndex)
    (hNoBetween : ∀ middle, marker.index < middle → middle ≤ sourceIndex →
      middle ∉ d.bucket.map Ref.index) {cap : Row} (hCap : cap ≤ sourceUpper.row) :
    ∃ (index : Nat) (cell : Cell), column[index]? = some cell ∧
      cell.row = Row.lift (d.marker_data marker hm).current.row
        (d.marker_data marker hm).targetCell.row sourceCell.row ∧
      ∀ (otherIndex : Nat) (other : Cell), column[otherIndex]? = some other → cell.row < other.row → cap ≤ other.row := by
  let s := d.marker_data marker hm
  have hFinish := d.copyColumn_eq_finish.symm.trans hRun
  obtain ⟨otherColumn, hOther, _, hValid, _, _⟩ := d.copyColumn_valid
  have he : otherColumn = column := Except.ok.inj (hOther.symm.trans hRun)
  subst otherColumn
  by_cases hMarked : sourceIndex + 1 ∈ d.bucket.map Ref.index
  · obtain ⟨hMem, hBarrier⟩ := d.candidates_barrier_before_marker hNoPremature hm hSource hUpper hAfter
      hNoBetween hMarked hCap
    obtain ⟨index, cell, hCell, hCellRow⟩ := finish_row_read hFinish hMem
    refine ⟨index, cell, hCell, hCellRow, ?_⟩
    intro otherIndex other hOther hAbove
    have hRowMem : other.row ∈ column.toList.map Cell.row := List.mem_map.mpr
      ⟨other, List.mem_iff_getElem?.mpr ⟨otherIndex, by simpa only [Array.getElem?_toList] using hOther⟩, rfl⟩
    obtain ⟨candidate, hCandidate, hCandidateRow⟩ := List.mem_map.mp
      ((finish_rows_mem_iff hFinish other.row).mp hRowMem)
    rcases hBarrier candidate hCandidate with hBelow | hCapOther
    · have hNoAbove : other.row ≤ cell.row := by simpa only [hCandidateRow, ← hCellRow] using hBelow
      exact False.elim ((not_lt_of_ge hNoAbove) hAbove)
    · simpa only [hCandidateRow] using hCapOther
  · have hNoBetweenUpper : ∀ middle, marker.index < middle → middle ≤ sourceIndex + 1 →
        middle ∉ d.bucket.map Ref.index := by
      intro middle hlo hhi
      by_cases he : middle = sourceIndex + 1
      · simpa only [he] using hMarked
      · exact hNoBetween middle hlo (by omega)
    obtain ⟨index, lower, upper, hLower, hUpperOut, hLowerRow, hUpperRow⟩ :=
      d.copyColumn_source_adjacent_of_no_between hParentPower hParentLow hNoPremature hRun hm hSource hUpper
        hAfter hNoBetweenUpper
    have hSourceUpper : s.current.row ≤ sourceUpper.row :=
      (d.source_valid.rows_strict _ _ _ _ s.current_at hUpper (by omega)).le
    have hUpperCap : cap ≤ upper.row := by
      rw [hUpperRow]
      exact hCap.trans (Row.lift_ge_source s.target_lower hSourceUpper)
    exact ⟨index, lower, hLower, hLowerRow, row_barrier_of_adjacent hValid hLower hUpperOut hUpperCap⟩

/-- At a power cap, both source and target lie strictly below the cap, so
the returned lifted node does too. Every ceiling up to and including that
cap selects this exact actual node. -/
theorem copyColumn_crossed_cap_below {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {marker : Ref} (hm : marker ∈ d.bucket) {sourceIndex : Nat} {sourceCell sourceUpper : Cell}
    (hSource : d.sources[sourceIndex]? = some sourceCell)
    (hUpper : d.sources[sourceIndex + 1]? = some sourceUpper) (hAfter : marker.index < sourceIndex)
    (hNoBetween : ∀ middle, marker.index < middle → middle ≤ sourceIndex →
      middle ∉ d.bucket.map Ref.index) {degree : Nat}
    (hTarget : (d.marker_data marker hm).targetCell.row < Row.bump (d.marker_data marker hm).current.row degree)
    (hSourceCap : sourceCell.row < Row.bump (d.marker_data marker hm).current.row degree)
    (hUpperCap : Row.bump (d.marker_data marker hm).current.row degree ≤ sourceUpper.row) :
    ∃ (index : Nat) (cell : Cell), column[index]? = some cell ∧
      cell.row = Row.lift (d.marker_data marker hm).current.row (d.marker_data marker hm).targetCell.row sourceCell.row ∧
      cell.row < Row.bump (d.marker_data marker hm).current.row degree ∧
      ∀ ceiling, cell.row < ceiling → ceiling ≤ Row.bump (d.marker_data marker hm).current.row degree →
        below (mountain.push column) mountain.size ceiling = .ok ⟨mountain.size, index⟩ := by
  let s := d.marker_data marker hm
  obtain ⟨index, cell, hCell, hRow, hBarrier⟩ := d.copyColumn_crossed_cap_barrier hParentPower hParentLow
    hNoPremature hRun hm hSource hUpper hAfter hNoBetween hUpperCap
  obtain ⟨otherColumn, hOther, _, hValid, _, hMountain⟩ := d.copyColumn_valid
  have he : otherColumn = column := Except.ok.inj (hOther.symm.trans hRun)
  subst otherColumn
  have hSourceLower : s.current.row ≤ sourceCell.row :=
    (d.source_valid.rows_strict _ _ _ _ s.current_at hSource hAfter).le
  have hLiftBelow := (Row.lift_mem_interval s.target_lower hTarget hSourceLower hSourceCap).2
  refine ⟨index, cell, hCell, hRow, by simpa only [hRow] using hLiftBelow, ?_⟩
  intro ceiling hlo hhi
  have hColumn : (mountain.push column)[mountain.size]? = some column := by simp
  have hCV : ColumnValid (mountain.push column) mountain.size column := by
    have h := hMountain mountain.size (by simp)
    simpa only [Array.getElem_push_eq] using h
  exact below_eq_of_row_barrier hColumn hCV hCell hBarrier hlo hhi

end ParentInputs

end ColumnCopyData

/-- Prepared root gaps remove the generic marker-exclusion premise. The
strict source interior and the actual reference target below the power cap
ensure that the selector interval is nonempty, not a vacuous condition. -/
theorem ColumnCopyData.prepared_crossed_cap_below
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {mountain : Mountain} {references : List Ref} {sourceColumn shift : Nat}
    (d : ColumnCopyData mountain p.marked references sourceColumn shift p.root.column)
    (hBaseSource : p.reduced[sourceColumn]? = some d.sources)
    (hParentPower : ∀ marker (hm : marker ∈ d.bucket),
      ColumnPowerSteps (d.marker_data marker hm).parentNodes)
    (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (index : Nat) (cell : Cell),
      (d.marker_data marker hm).parentNodes[index]? = some cell ∧
        cell.row = (d.marker_data marker hm).current.row)
    (hNoPremature : NoPrematureOne d.sources)
    {root : (Frame.ofMountain p.reduced).Node} {degree : Nat}
    (hRootColumn : root.1.val = p.root.column)
    (hBarrier : ∀ upper, (Frame.ofMountain p.reduced).upper root = some upper →
      Row.bump ((Frame.ofMountain p.reduced).height root) degree ≤ (Frame.ofMountain p.reduced).height upper)
    {column : Column}
    (hRun : copyColumn mountain p.marked references sourceColumn shift p.root.column = .ok column)
    {marker : Ref} (hm : marker ∈ d.bucket)
    (hMarkerRow : (d.marker_data marker hm).current.row = (Frame.ofMountain p.reduced).height root)
    {sourceIndex : Nat} {sourceCell sourceUpper : Cell}
    (hSource : d.sources[sourceIndex]? = some sourceCell)
    (hUpper : d.sources[sourceIndex + 1]? = some sourceUpper)
    (hSourceAbove : (Frame.ofMountain p.reduced).height root < sourceCell.row)
    (hSourceCap : sourceCell.row < Row.bump ((Frame.ofMountain p.reduced).height root) degree)
    (hUpperCap : Row.bump ((Frame.ofMountain p.reduced).height root) degree ≤ sourceUpper.row)
    (hTarget : (d.marker_data marker hm).targetCell.row < Row.bump ((Frame.ofMountain p.reduced).height root) degree) :
    ∃ (index : Nat) (cell : Cell), column[index]? = some cell ∧
      cell.row = Row.lift ((Frame.ofMountain p.reduced).height root)
        (d.marker_data marker hm).targetCell.row sourceCell.row ∧
      cell.row < Row.bump ((Frame.ofMountain p.reduced).height root) degree ∧
      ∀ ceiling, cell.row < ceiling → ceiling ≤ Row.bump ((Frame.ofMountain p.reduced).height root) degree →
        below (mountain.push column) mountain.size ceiling = .ok ⟨mountain.size, index⟩ := by
  have hAfter : marker.index < sourceIndex := by
    by_contra hn
    rcases eq_or_lt_of_le (show sourceIndex ≤ marker.index by omega) with he | hl
    · have hSame : sourceCell = (d.marker_data marker hm).current := Option.some.inj
        (hSource.symm.trans (by simpa only [he] using (d.marker_data marker hm).current_at))
      have hEqual := (congrArg Cell.row hSame).trans hMarkerRow
      exact (ne_of_lt hSourceAbove) hEqual.symm
    · have hLower := d.source_valid.rows_strict _ _ _ _ hSource (d.marker_data marker hm).current_at hl
      exact (lt_asymm hSourceAbove) (by simpa only [hMarkerRow] using hLower)
  have hNoBetween := d.prepared_no_markers_through_source_index hBaseSource hRootColumn hBarrier hm
    hMarkerRow hSource hSourceCap
  have hResult := d.copyColumn_crossed_cap_below hParentPower hParentLow hNoPremature hRun hm
    hSource hUpper hAfter hNoBetween (by simpa only [hMarkerRow] using hTarget)
    (by simpa only [hMarkerRow] using hSourceCap) (by simpa only [hMarkerRow] using hUpperCap)
  simpa only [hMarkerRow] using hResult

end OmegaY.Expansion

#print axioms OmegaY.Expansion.contourSourceCells_ends_before_marker
#print axioms OmegaY.Expansion.ColumnCopyData.segment_max_before_marker
#print axioms OmegaY.Expansion.ColumnCopyData.candidates_barrier_before_marker
#print axioms OmegaY.Expansion.below_eq_of_row_barrier
#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_crossed_cap_barrier
#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_crossed_cap_below
#print axioms OmegaY.Expansion.ColumnCopyData.prepared_crossed_cap_below
