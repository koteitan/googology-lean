/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualRootInterval.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/ActualRootInterval.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.PreparedBoundaryParent
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.IntervalLegTransport

set_option backward.do.legacy false

/-!
# Source root barriers for the actual reference partition

The cap below is selected by the real boundary-reference partition. Higher
root-prefix rows supply its interior barriers. At the final prefix node,
the original last-top edge and the father upper bound supply the remaining
barrier; the entire root column is unchanged by decrementing the last value.
-/

namespace OmegaY.Expansion

open Canonical Geometry

private theorem frame_upper_of_refs {F : Frame} {before after : F.Node} {column index : Nat}
    (hBefore : Frame.ref before = ⟨column, index⟩)
    (hAfter : Frame.ref after = ⟨column, index + 1⟩) : F.upper before = some after := by
  rcases before with ⟨c, i⟩
  rcases after with ⟨d, j⟩
  simp only [Frame.ref, Ref.mk.injEq] at hBefore hAfter
  have hc : d = c := Fin.ext (hAfter.1.trans hBefore.1.symm)
  subst d
  have hBound : i.val + 1 < F.length c := by have := j.isLt; omega
  simp only [Frame.upper, hBound, ↓reduceDIte, Option.some.injEq]
  apply Executable.ref_injective F
  simp only [Frame.ref, Ref.mk.injEq]
  exact ⟨trivial, by omega⟩

private theorem upper_ref_of_root_ref {F : Frame} {root upper : F.Node} {column index : Nat}
    (hRoot : Frame.ref root = ⟨column, index⟩) (hUpper : F.upper root = some upper) :
    Frame.ref upper = ⟨column, index + 1⟩ := by
  have hc := congrArg Ref.column hRoot
  have hi := congrArg Ref.index hRoot
  obtain ⟨hUpperColumn, hUpperIndex⟩ := Frame.upper_spec hUpper
  simp only [Frame.ref, Ref.mk.injEq]
  exact ⟨(congrArg Fin.val hUpperColumn).trans hc, by dsimp only [Frame.ref] at hi; omega⟩

/-- At the top of the source root prefix, an actual upper is at least the
old last top. This is transported through the unchanged entire root column. -/
theorem Preparation.reduced_badRoot_upper_bound {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last)
    {root upper : (Frame.ofMountain p.reduced).Node}
    (hRoot : Frame.ref root = p.root)
    (hUpper : (Frame.ofMountain p.reduced).upper root = some upper) :
    p.lastTop.row ≤ (Frame.ofMountain p.reduced).height upper := by
  have hUpperRef : Frame.ref upper = ⟨p.root.column, p.root.index + 1⟩ :=
    upper_ref_of_root_ref hRoot hUpper
  have hReducedRead := cellAt_of_frame_node p.reduced upper
  rw [hUpperRef] at hReducedRead
  have hInitialRead : Canonical.cellAt p.initial ⟨p.root.column, p.root.index + 1⟩ =
      .ok ((Frame.ofMountain p.reduced).cell upper) :=
    (build_changed_last_preserves_ref (ref := ⟨p.root.column, p.root.index + 1⟩)
      p.initial_build p.reduced_build p.root_before_last).trans hReducedRead
  obtain ⟨oldUpper, hOldRef, hOldCell⟩ := frame_node_of_cellAt (cellAt_ok_iff.mp hInitialRead)
  obtain ⟨g⟩ := p.root_geometry hLast
  have hOldUpper : (Frame.ofMountain p.initial).upper g.rootNode = some oldUpper :=
    frame_upper_of_refs g.root_ref hOldRef
  have hNormal := build_normal_of_success p.initial_build
  have hBound := Frame.father_upper_bound_nodes hNormal g.lower_parent g.lower_upper hOldUpper
  simpa only [Frame.height, g.top_cell, hOldCell] using hBound

/-- A cap bounded by the actual partition's higher prefix rows and last
top is below every upper of the corresponding source root-prefix node. -/
theorem Preparation.root_prefix_upper_barrier {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {nodes : Column}
    (hColumn : p.initial[p.root.column]? = some nodes) {index : Nat}
    (hIndex : index ≤ p.root.index) {cap : Row} (hTop : cap ≤ p.lastTop.row)
    (hHigher : ∀ higherIndex higherCell, index < higherIndex → higherIndex ≤ p.root.index →
      nodes[higherIndex]? = some higherCell → cap ≤ higherCell.row)
    {root : (Frame.ofMountain p.reduced).Node}
    (hRoot : Frame.ref root = ⟨p.root.column, index⟩) :
    ∀ upper, (Frame.ofMountain p.reduced).upper root = some upper →
      cap ≤ (Frame.ofMountain p.reduced).height upper := by
  intro upper hUpper
  rcases lt_or_eq_of_le hIndex with hBefore | hAtEnd
  · have hUpperRef := upper_ref_of_root_ref hRoot hUpper
    have hReducedRead := cellAt_of_frame_node p.reduced upper
    rw [hUpperRef] at hReducedRead
    have hInitialRead : Canonical.cellAt p.initial ⟨p.root.column, index + 1⟩ =
        .ok ((Frame.ofMountain p.reduced).cell upper) :=
      (build_changed_last_preserves_ref (ref := ⟨p.root.column, index + 1⟩)
        p.initial_build p.reduced_build p.root_before_last).trans hReducedRead
    obtain ⟨actualNodes, hActualColumn, hRead⟩ := cellAt_ok_iff.mp hInitialRead
    have he : actualNodes = nodes := Option.some.inj (hActualColumn.symm.trans hColumn)
    subst actualNodes
    exact hHigher (index + 1) ((Frame.ofMountain p.reduced).cell upper)
      (Nat.lt_succ_self _) (by omega) hRead
  · have hRootExact : Frame.ref root = p.root := by simpa only [hAtEnd] using hRoot
    exact hTop.trans (p.reduced_badRoot_upper_bound hLast hRootExact hUpper)

/-- All data refer to the source node and target cell selected in a real
block. In particular, root_upper_barrier is proved by actual partition
construction and is not an external condition on an arbitrary cap. -/
structure ActualRootInterval {front : List Nat} {last : Nat} (p : Preparation front last)
    (start ambient : Mountain) (references : List Ref) (sourceIndex : Nat) (sourceRow : Row) where
  root : (Frame.ofMountain p.reduced).Node
  degree : Nat
  reference : Ref
  target : Cell
  root_ref : Frame.ref root = ⟨p.root.column, sourceIndex⟩
  root_row : (Frame.ofMountain p.reduced).height root = sourceRow
  root_real : Frame.Real root
  root_prefix : sourceIndex ≤ p.root.index
  reference_column : reference.column = start.size - 1
  target_start_read : Canonical.cellAt start reference = .ok target
  target_ambient_read : Canonical.cellAt ambient reference = .ok target
  start_query : referenceAt start references sourceRow = .ok target.row
  ambient_query : referenceAt ambient references sourceRow = .ok target.row
  start_below : below start (start.size - 1) (Row.bump sourceRow degree) = .ok reference
  ambient_below : below ambient (start.size - 1) (Row.bump sourceRow degree) = .ok reference
  target_lower : sourceRow ≤ target.row
  target_below : target.row < Row.bump sourceRow degree
  cap_top : Row.bump sourceRow degree ≤ p.lastTop.row
  higher_prefix_barrier : ∀ nodes higherIndex higherCell,
    p.initial[p.root.column]? = some nodes → sourceIndex < higherIndex →
    higherIndex ≤ p.root.index → nodes[higherIndex]? = some higherCell →
      Row.bump sourceRow degree ≤ higherCell.row
  root_upper_barrier : ∀ upper, (Frame.ofMountain p.reduced).upper root = some upper →
    Row.bump sourceRow degree ≤ (Frame.ofMountain p.reduced).height upper
  raised_degree : sourceRow < target.row → 0 < degree

/-- A positive actual root-prefix row produces all source geometry and
reference data. The degree and cap are taken from the boundary partition. -/
theorem DynamicBlockState.actual_root_interval {front : List Nat} {last : Nat}
    {p : Preparation front last} {block : Nat} {start ambient : Mountain}
    {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (hLast : 1 < last) {nodes : Column}
    (hColumn : p.initial[p.root.column]? = some nodes)
    {index : Nat} {source : Cell} (hSource : nodes[index]? = some source)
    (hIndex : index ≤ p.root.index) (hPositive : 0 < source.row) :
    Nonempty (ActualRootInterval p start ambient references index source.row) := by
  obtain ⟨ceiling, degree, ref, target, hPower, hTop, hBelow, hRead, hRefColumn,
      hQuery, hLow, hHigh, hHigher⟩ :=
    RootRowsInColumn.root_interval s.boundary_rows s.start_valid hLast hColumn hSource hIndex s.reference_map
  have hInitialRead : Canonical.cellAt p.initial ⟨p.root.column, index⟩ = .ok source :=
    cellAt_ok_iff.mpr ⟨nodes, hColumn, hSource⟩
  have hReducedRead : Canonical.cellAt p.reduced ⟨p.root.column, index⟩ = .ok source :=
    (build_changed_last_preserves_ref (ref := ⟨p.root.column, index⟩)
      p.initial_build p.reduced_build p.root_before_last).symm.trans hInitialRead
  obtain ⟨root, hRootRef, hRootCell⟩ := frame_node_of_cellAt (cellAt_ok_iff.mp hReducedRead)
  have hRootRow : (Frame.ofMountain p.reduced).height root = source.row := congrArg Cell.row hRootCell
  have hIndexPositive : 0 < index := by
    by_contra hn
    have hi : index = 0 := by omega
    obtain ⟨hc, hNodes⟩ := Array.getElem?_eq_some_iff.mp hColumn
    have hPhantom : nodes[0]? = some phantom := hNodes ▸ (p.initial_valid _ hc).phantom
    have hSourceEq : source = phantom := Option.some.inj
      (hSource.symm.trans (by simpa only [hi] using hPhantom))
    simp [hSourceEq, phantom] at hPositive
  have hRootReal : Frame.Real root := by
    have hi := congrArg Ref.index hRootRef
    change root.2.val = index at hi
    change 0 < root.2.val
    rw [hi]
    exact hIndexPositive
  obtain ⟨targetNodes, hTargetNodes, hTargetIndex⟩ := cellAt_ok_iff.mp hRead
  have hAmbientRead : Canonical.cellAt ambient ref = .ok target :=
    cellAt_ok_iff.mpr ⟨targetNodes, s.start_preserved.column_read hTargetNodes, hTargetIndex⟩
  have hBarrier := p.root_prefix_upper_barrier hLast hColumn hIndex hTop hHigher hRootRef
  have hRaised : source.row < target.row → 0 < degree := by
    intro hStrict
    by_contra hn
    have hd : degree = 0 := by omega
    have hHighZero : target.row < Row.bump source.row 0 := by simpa only [hPower, hd] using hHigh
    have hEq : source.row = target.row := Row.jump_eq_zero.mp
      (Nat.eq_zero_of_le_zero (Row.jump_le_of_lt_bump hLow hHighZero))
    exact (ne_of_lt hStrict) hEq
  refine ⟨{
    root := root
    degree := degree
    reference := ref
    target := target
    root_ref := hRootRef
    root_row := hRootRow
    root_real := hRootReal
    root_prefix := hIndex
    reference_column := hRefColumn
    target_start_read := hRead
    target_ambient_read := hAmbientRead
    start_query := hQuery
    ambient_query := (s.referenceAt_preserved source.row).trans hQuery
    start_below := by simpa only [hPower] using hBelow
    ambient_below := ?_
    target_lower := hLow
    target_below := by simpa only [hPower] using hHigh
    cap_top := by simpa only [hPower] using hTop
    higher_prefix_barrier := ?_
    root_upper_barrier := by simpa only [hPower] using hBarrier
    raised_degree := hRaised }⟩
  · simpa only [hPower] using
      (s.start_preserved.below (RootRowsInColumn.column_lt s.boundary_rows) ceiling).trans hBelow
  · intro otherNodes higherIndex higherCell hOtherColumn hBefore hPrefix hHigherRead
    have he : otherNodes = nodes := Option.some.inj (hOtherColumn.symm.trans hColumn)
    subst otherNodes
    simpa only [hPower] using hHigher higherIndex higherCell hBefore hPrefix hHigherRead

/-- Actual prepared markers supply the original root-prefix read used by
the construction above; callers need not independently identify that read. -/
theorem DynamicBlockState.actual_marker_root_interval {front : List Nat} {last : Nat}
    {p : Preparation front last} {block : Nat} {start ambient : Mountain}
    {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (hLast : 1 < last) {bucket : Nat} {marker : Ref} {source : Cell}
    (hMarker : BucketMem p.marked bucket marker)
    (hSource : Canonical.cellAt p.reduced marker = .ok source)
    (hPositive : 0 < source.row) :
    ∃ index, Nonempty (ActualRootInterval p start ambient references index source.row) := by
  obtain ⟨nodes, index, lower, hColumn, hLower, hIndex, hRow⟩ :=
    p.marker_root_prefix_read hMarker hSource
  exact ⟨index, by simpa only [hRow] using
    s.actual_root_interval hLast hColumn hLower hIndex (by rw [hRow]; exact hPositive)⟩

/-- A genuinely raised actual marker cannot be phantom, because the actual
reference map fixes zero. Thus its real root and positive degree are both
derived, together with agreement with the already queried target. -/
theorem DynamicBlockState.raised_marker_root_interval {front : List Nat} {last : Nat}
    {p : Preparation front last} {block : Nat} {start ambient : Mountain}
    {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (hLast : 1 < last) {bucket : Nat} {marker : Ref} {source : Cell}
    (hMarker : BucketMem p.marked bucket marker)
    (hSource : Canonical.cellAt p.reduced marker = .ok source)
    {target : Row} (hTarget : referenceAt ambient references source.row = .ok target)
    (hRaised : source.row < target) :
    ∃ index, ∃ a : ActualRootInterval p start ambient references index source.row,
      a.target.row = target ∧ 0 < a.degree := by
  have hPositive : 0 < source.row := by
    by_contra hn
    have hZero : source.row = 0 := le_antisymm (le_of_not_gt hn) (Row.zero_le _)
    have hZeroQuery : referenceAt ambient references 0 = .ok 0 :=
      (s.referenceAt_preserved 0).trans
        (RootRowsInColumn.referenceAt_zero s.boundary_rows s.start_valid hLast s.reference_map)
    have hTargetZero : target = 0 := Except.ok.inj
      (hTarget.symm.trans (by simpa only [hZero] using hZeroQuery))
    rw [hZero, hTargetZero] at hRaised
    exact (lt_irrefl _) hRaised
  obtain ⟨index, ⟨a⟩⟩ := s.actual_marker_root_interval hLast hMarker hSource hPositive
  have hEq : a.target.row = target := Except.ok.inj (a.ambient_query.symm.trans hTarget)
  exact ⟨index, a, hEq, a.raised_degree (by rw [hEq]; exact hRaised)⟩

/-- The full single-interval source-edge transport now consumes the actual
reference certificate; source normality, root reality and the upper barrier
are all supplied internally rather than assumed anew by the caller. -/
theorem ActualRootInterval.leg_B_transport {front : List Nat} {last : Nat}
    {p : Preparation front last} {start ambient : Mountain} {references : List Ref}
    {index : Nat} {sourceRow : Row}
    (a : ActualRootInterval p start ambient references index sourceRow)
    (hRaised : sourceRow < a.target.row)
    {child parent upper : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hUpper : (Frame.ofMountain p.reduced).upper child = some upper) :
    (Frame.ofMountain p.reduced).incomingRow a.root (Row.bump sourceRow a.degree) a.target.row upper =
      Row.B ((Frame.ofMountain p.reduced).effectiveRow a.root
        (Row.bump sourceRow a.degree) a.target.row child)
        ((Frame.ofMountain p.reduced).effectiveRow a.root
          (Row.bump sourceRow a.degree) a.target.row parent) := by
  have hNormal := build_normal_of_success p.reduced_build
  have hBarrier : ∀ rootUpper, (Frame.ofMountain p.reduced).upper a.root = some rootUpper →
      Row.bump ((Frame.ofMountain p.reduced).height a.root) a.degree ≤
        (Frame.ofMountain p.reduced).height rootUpper := by
    simpa only [a.root_row] using a.root_upper_barrier
  have hTarget : (Frame.ofMountain p.reduced).height a.root ≤ a.target.row :=
    a.root_row.trans_le a.target_lower
  have hCap : a.target.row < Row.bump ((Frame.ofMountain p.reduced).height a.root) a.degree := by
    simpa only [a.root_row] using a.target_below
  simpa only [a.root_row] using Frame.interval_leg_B_transport hNormal a.root_real
    (a.raised_degree hRaised) hBarrier hTarget hCap hParent hUpper

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.reduced_badRoot_upper_bound
#print axioms OmegaY.Expansion.Preparation.root_prefix_upper_barrier
#print axioms OmegaY.Expansion.DynamicBlockState.actual_root_interval
#print axioms OmegaY.Expansion.DynamicBlockState.actual_marker_root_interval
#print axioms OmegaY.Expansion.DynamicBlockState.raised_marker_root_interval
#print axioms OmegaY.Expansion.ActualRootInterval.leg_B_transport
