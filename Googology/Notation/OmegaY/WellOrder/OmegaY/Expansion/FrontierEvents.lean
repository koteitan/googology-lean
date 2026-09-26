/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/FrontierEvents.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/FrontierEvents.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.RawParent
import Googology.Notation.OmegaY.WellOrder.OmegaY.Forests.DepthValues

set_option backward.do.legacy false

/-!
# Synchronous finite frontier events from actual stored-parent geometry

Each event chooses one actual real node in each active column. Consecutive
events either reuse that same node or move to its actual immediate upper
node at the next common cut. The parent closure and exact raw B row rule
are explicit geometric inputs, not assertions of numerical canonicality.

The common-parent synchrony field of SynchronousBackfill is derived below:
two frontier nodes with the same actual raw parent have equal upper rows,
by B_eq_of_between, and therefore move in the same cut event. NumericSuffix
is deliberately not a conclusion; it additionally requires recovery by the
candidate forest's first-smaller search.
-/

namespace OmegaY.Geometry.Frame

def frontierIndices (F : Frame) (cut : Row) (column : Fin F.width) : Finset (Fin (F.length column)) :=
  Finset.univ.filter fun i => F.height ⟨column, i⟩ ≤ cut

theorem frontierIndices_nonempty {F : Frame} (hF : F.Ordered) {cut : Row}
    (hCut : (1 : Row) ≤ cut) (column : Fin F.width) :
    (F.frontierIndices cut column).Nonempty := by
  have hLength : 1 < F.length column := by have := hF.length_ge_two column; omega
  refine ⟨⟨1, hLength⟩, ?_⟩
  simp only [frontierIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  simpa only [height, cell, hF.bottom_row column hLength] using hCut

/-- Actual finite maximum at a cut; no candidate or numerical-parent search. -/
noncomputable def frontierAt {F : Frame} (hF : F.Ordered) (cut : Row)
    (hCut : (1 : Row) ≤ cut) (column : Fin F.width) : F.Node :=
  ⟨column, (F.frontierIndices cut column).max' (frontierIndices_nonempty hF hCut column)⟩

theorem frontierAt_spec {F : Frame} (hF : F.Ordered) {cut : Row}
    (hCut : (1 : Row) ≤ cut) (column : Fin F.width) :
    let node := frontierAt hF cut hCut column
    node.1 = column ∧ Real node ∧ F.height node ≤ cut ∧
      (∀ i : Fin (F.length column), F.height ⟨column, i⟩ ≤ cut → i ≤ node.2) ∧
      ∀ upper, F.upper node = some upper → cut < F.height upper := by
  let eligible := F.frontierIndices cut column
  have hNonempty := frontierIndices_nonempty hF hCut column
  have hMem := Finset.max'_mem eligible hNonempty
  have hHeight : F.height (frontierAt hF cut hCut column) ≤ cut := by
    simpa only [eligible, frontierIndices, Finset.mem_filter, Finset.mem_univ, true_and,
      frontierAt] using hMem
  have hMaximum : ∀ i : Fin (F.length column), F.height ⟨column, i⟩ ≤ cut →
      i ≤ (frontierAt hF cut hCut column).2 := by
    intro i hi
    exact Finset.le_max' eligible i (by simp only [eligible, frontierIndices,
      Finset.mem_filter, Finset.mem_univ, true_and]; exact hi)
  have hLength : 1 < F.length column := by have := hF.length_ge_two column; omega
  have hReal : Real (frontierAt hF cut hCut column) := by
    have hBottom : F.height ⟨column, ⟨1, hLength⟩⟩ ≤ cut := by
      simpa only [height, cell, hF.bottom_row column hLength] using hCut
    exact Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) (hMaximum ⟨1, hLength⟩ hBottom)
  refine ⟨rfl, hReal, hHeight, hMaximum, ?_⟩
  intro upper hUpper
  obtain ⟨hColumn, hIndex⟩ := upper_spec hUpper
  cases upper with
  | mk c i =>
    change c = column at hColumn
    subst c
    by_contra hNot
    have hLe := hMaximum i (le_of_not_gt hNot)
    change i.val ≤ (frontierAt hF cut hCut column).2.val at hLe
    change i.val = (frontierAt hF cut hCut column).2.val + 1 at hIndex
    omega

/-- A real parent interval can identify the actual frontier without any
numerical-parent search or raw B hypothesis. -/
theorem frontierAt_eq_of_upper_barrier {F : Frame} (hF : F.Ordered) {cut : Row}
    (hCut : (1 : Row) ≤ cut) {node : F.Node}
    (hBelow : F.height node ≤ cut)
    (hBarrier : ∀ upper, F.upper node = some upper → cut < F.height upper) :
    frontierAt hF cut hCut node.1 = node := by
  rcases node with ⟨column, index⟩
  let chosen := frontierAt hF cut hCut column
  have hChosen := frontierAt_spec hF hCut column
  have hLe : index ≤ chosen.2 := hChosen.2.2.2.1 index hBelow
  have hIndices : chosen.2 = index := by
    apply le_antisymm _ hLe
    by_contra hNot
    have hLt : index.val < chosen.2.val := lt_of_not_ge hNot
    have hLength : index.val + 1 < F.length column :=
      lt_of_le_of_lt (Nat.succ_le_of_lt hLt) chosen.2.isLt
    let upper : F.Node := ⟨column, ⟨index.val + 1, hLength⟩⟩
    have hUpper : F.upper ⟨column, index⟩ = some upper := by
      change (if h : index.val + 1 < F.length column then
        some (⟨column, ⟨index.val + 1, h⟩⟩ : F.Node) else none) = some upper
      rw [dif_pos hLength]
    have hUpperLe : F.height upper ≤ F.height chosen :=
      (hF.rows_strict column).monotone (Nat.succ_le_of_lt hLt)
    exact (not_lt_of_ge (hUpperLe.trans hChosen.2.2.1)) (hBarrier upper hUpper)
  exact congrArg (fun i : Fin (F.length column) => (⟨column, i⟩ : F.Node)) hIndices

/-- Consecutive cuts in the finite union of actual rows cause exactly one
physical upper step in every changing column, all ending at the same cut. -/
theorem frontierAt_advance {F : Frame} (hF : F.Ordered) {cut nextCut : Row}
    (hCut : (1 : Row) ≤ cut) (hNextCut : (1 : Row) ≤ nextCut)
    (hOrder : cut ≤ nextCut)
    (hNoBetween : ∀ node : F.Node, cut < F.height node → F.height node < nextCut → False)
    (column : Fin F.width)
    (hChanged : frontierAt hF nextCut hNextCut column ≠ frontierAt hF cut hCut column) :
    F.upper (frontierAt hF cut hCut column) = some (frontierAt hF nextCut hNextCut column) ∧
      F.height (frontierAt hF nextCut hNextCut column) = nextCut := by
  let before := frontierAt hF cut hCut column
  let after := frontierAt hF nextCut hNextCut column
  have hBefore := frontierAt_spec hF hCut column
  have hAfter := frontierAt_spec hF hNextCut column
  have hIndexLe : before.2 ≤ after.2 := hAfter.2.2.2.1 before.2 (hBefore.2.2.1.trans hOrder)
  have hIndexNe : before.2 ≠ after.2 := by
    intro hEq
    apply hChanged
    exact (congrArg (fun i : Fin (F.length column) => (⟨column, i⟩ : F.Node)) hEq).symm
  have hIndexLt : before.2.val < after.2.val :=
    lt_of_le_of_ne hIndexLe (fun hEq => hIndexNe (Fin.ext hEq))
  have hLength : before.2.val + 1 < F.length column :=
    lt_of_le_of_lt (Nat.succ_le_of_lt hIndexLt) after.2.isLt
  let middle : F.Node := ⟨column, ⟨before.2.val + 1, hLength⟩⟩
  have hUpper : F.upper before = some middle := by
    change (if h : before.2.val + 1 < F.length column then
      some (⟨column, ⟨before.2.val + 1, h⟩⟩ : F.Node) else none) = some middle
    rw [dif_pos hLength]
  have hMiddleLe : F.height middle ≤ F.height after :=
    (hF.rows_strict column).monotone (Nat.succ_le_of_lt hIndexLt)
  have hMiddleCut : cut < F.height middle := hBefore.2.2.2.2 middle hUpper
  have hMiddleNext : F.height middle = nextCut := by
    apply le_antisymm (hMiddleLe.trans hAfter.2.2.1)
    exact le_of_not_gt (hNoBetween middle hMiddleCut)
  have hAfterNext : F.height after = nextCut :=
    le_antisymm hAfter.2.2.1 (hMiddleNext ▸ hMiddleLe)
  have hRows : F.height middle = F.height after := hMiddleNext.trans hAfterNext.symm
  have hIndices : (⟨before.2.val + 1, hLength⟩ : Fin (F.length column)) = after.2 :=
    (hF.rows_strict column).injective hRows
  have hNodes : middle = after := congrArg
    (fun i : Fin (F.length column) => (⟨column, i⟩ : F.Node)) hIndices
  exact ⟨hUpper.trans (congrArg some hNodes), hAfterNext⟩

noncomputable def frontierParent (F : Frame) (front : Nat → Nat → F.Node)
    (bound event : Nat) : ZeroY.ParentMap := fun column =>
  if column ≤ bound then (F.rawParent (front event column)).map (fun p => p.1.val) else none

noncomputable def frontierForests (F : Frame) (initial : ZeroY.ParentMap)
    (front : Nat → Nat → F.Node) (bound : Nat) : Nat → ZeroY.ParentMap
  | 0 => initial
  | event + 1 => F.frontierParent front bound event

def frontierValue (F : Frame) (front : Nat → Nat → F.Node) (event column : Nat) : Nat :=
  F.value (front event column)

def frontierMoves {F : Frame} (front : Nat → Nat → F.Node) (event column : Nat) : Prop :=
  front (event + 1) column ≠ front event column

/-- Local conditions on actual finite-row frontiers. The intended front is
the highest real node at or below a cut from the finite union of actual rows.
The advance field expresses a consecutive such cut, rather than an arbitrary
jump or serial movement of one member of a simultaneous event. -/
structure FrontierGeometry (F : Frame) (front : Nat → Nat → F.Node)
    (cut : Nat → Row) (bound start finish : Nat) : Prop where
  at_column : ∀ r, start ≤ r → r ≤ finish → ∀ c, c ≤ bound → (front r c).1.val = c
  real : ∀ r, start ≤ r → r ≤ finish → ∀ c, c ≤ bound → Real (front r c)
  below_cut : ∀ r, start ≤ r → r ≤ finish → ∀ c, c ≤ bound → F.height (front r c) ≤ cut r
  upper_above_cut : ∀ r, start ≤ r → r ≤ finish → ∀ c, c ≤ bound →
    ∀ upper, F.upper (front r c) = some upper → cut r < F.height upper
  advance : ∀ r, start ≤ r → r < finish → ∀ c, c ≤ bound → frontierMoves front r c →
    F.upper (front r c) = some (front (r + 1) c) ∧ F.height (front (r + 1) c) = cut (r + 1)
  parent_frontier : ∀ r, start ≤ r → r < finish → ∀ c, c ≤ bound →
    ∀ parent, F.rawParent (front r c) = some parent → front r parent.1.val = parent
  raw_B : ∀ r, start ≤ r → r < finish → ∀ c, c ≤ bound → ∀ upper parent,
    F.upper (front r c) = some upper → F.rawParent (front r c) = some parent →
      F.height parent ≤ F.height (front r c) ∧
      F.height upper = Row.B (F.height (front r c)) (F.height parent)

theorem frontierParent_leftward {F : Frame} (hF : F.Ordered)
    {front : Nat → Nat → F.Node} {bound event : Nat}
    (hColumn : ∀ c, c ≤ bound → (front event c).1.val = c) :
    ZeroY.Forest.Leftward (F.frontierParent front bound event) := by
  intro c p hParent
  by_cases hc : c ≤ bound
  · cases hRaw : F.rawParent (front event c) with
    | none => simp [frontierParent, hc, hRaw] at hParent
    | some parent =>
      have hCode : parent.1.val = p := by simpa [frontierParent, hc, hRaw] using hParent
      simpa only [hCode, hColumn c hc] using rawParent_column_lt hF hRaw
  · simp [frontierParent, hc] at hParent

theorem frontierForests_leftward {F : Frame} (hF : F.Ordered)
    {front : Nat → Nat → F.Node} {bound : Nat} {initial : ZeroY.ParentMap}
    (hInitial : ZeroY.Forest.Leftward initial)
    (hColumn : ∀ r c, c ≤ bound → (front r c).1.val = c) (event : Nat) :
    ZeroY.Forest.Leftward (F.frontierForests initial front bound event) := by
  cases event with
  | zero => exact hInitial
  | succ r => exact frontierParent_leftward hF (hColumn r)

/-- Being an actual highest node at the next cut forces a move whenever the
old upper is at that cut; no common-parent synchrony is assumed. -/
theorem FrontierGeometry.moves_iff_upper_at_cut {F : Frame}
    {front : Nat → Nat → F.Node} {cut : Nat → Row} {bound start finish r c : Nat}
    (h : FrontierGeometry F front cut bound start finish)
    (hr : start ≤ r) (hrf : r < finish) (hc : c ≤ bound) {upper : F.Node}
    (hUpper : F.upper (front r c) = some upper) :
    frontierMoves front r c ↔ F.height upper = cut (r + 1) := by
  constructor
  · intro hMove
    obtain ⟨hNext, hRow⟩ := h.advance r hr hrf c hc hMove
    have hEq : upper = front (r + 1) c := Option.some.inj (hUpper.symm.trans hNext)
    exact hEq ▸ hRow
  · intro hRow hSame
    have hNextUpper : F.upper (front (r + 1) c) = some upper := by rw [hSame]; exact hUpper
    have hAbove := h.upper_above_cut (r + 1) (by omega) (by omega) c hc upper hNextUpper
    rw [hRow] at hAbove
    exact (lt_irrefl _) hAbove

/-- The same cut below both B uppers forces those upper rows to coincide. -/
theorem B_equal_at_common_frontier {a b parent cut : Row}
    (hParentA : parent ≤ a) (hParentB : parent ≤ b)
    (hA : a ≤ cut) (hB : b ≤ cut)
    (hUpperA : cut < Row.B a parent) (hUpperB : cut < Row.B b parent) :
    Row.B a parent = Row.B b parent := by
  rcases le_total a b with hab | hba
  · exact (Row.B_eq_of_between hab hParentA (hB.trans_lt hUpperA)).symm
  · exact Row.B_eq_of_between hba hParentB (hA.trans_lt hUpperB)

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry

/-- The numerical minimum needed to read the parent's summand at a frontier.
Equality of the actual parent node and that frontier is sufficient, but
the additive equation itself requires only equality of their values. -/
theorem parent_sum_iff_frontier_value {F : Frame} {u upper parent atFrontier : F.Node}
    (hSum : F.value u = F.value upper + F.value parent) :
    F.value u = F.value upper + F.value atFrontier ↔ F.value parent = F.value atFrontier := by
  omega

/-- General actual-geometry-to-backfill bridge. All three synchronization
fields are proved from reads, sums, cut bracketing and the independent raw
B law. No NumericSuffix, P=rawParent, or Normal assumption is used. -/
theorem synchronousBackfill_of_frontier_geometry {mountain : Mountain}
    (hValid : MountainValid mountain) (hSums : MountainSums mountain)
    {front : Nat → Nat → (Frame.ofMountain mountain).Node} {cut : Nat → Row}
    {bound start finish : Nat}
    (hGeometry : Frame.FrontierGeometry (Frame.ofMountain mountain) front cut bound start finish)
    (initial : ZeroY.ParentMap) :
    Forests.SynchronousBackfill
      ((Frame.ofMountain mountain).frontierForests initial front bound)
      ((Frame.ofMountain mountain).frontierValue front)
      (Frame.frontierMoves front) bound start finish := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr hrf c hc hStationary
    have hSame : front (r + 1) c = front r c := Classical.not_not.mp hStationary
    simp only [Frame.frontierValue, hSame]
  · intro r hr hrf c hc hMove
    obtain ⟨hUpper, _⟩ := hGeometry.advance r hr hrf c hc hMove
    obtain ⟨parent, hParent, _, _, _, hValue, _⟩ := hSums.rawParent_upper hValid
      (hGeometry.real r hr hrf.le c hc) hUpper
    refine ⟨parent.1.val, ?_, ?_⟩
    · simp [Frame.frontierForests, Frame.frontierParent, hc, hParent]
    · simpa only [Frame.frontierValue, hGeometry.parent_frontier r hr hrf c hc parent hParent]
        using hValue
  · intro r hr hrf c z hc hz hCommon
    have hCommonRaw :
        ((Frame.ofMountain mountain).rawParent (front r c)).map (fun p => p.1.val) =
        ((Frame.ofMountain mountain).rawParent (front r z)).map (fun p => p.1.val) := by
      simpa only [Frame.frontierForests, Frame.frontierParent, if_pos hc, if_pos hz] using hCommon
    cases hC : (Frame.ofMountain mountain).rawParent (front r c) with
    | none =>
      have hZ : (Frame.ofMountain mountain).rawParent (front r z) = none := by
        cases hZ : (Frame.ofMountain mountain).rawParent (front r z) with
        | none => rfl
        | some p => simp [hC, hZ] at hCommonRaw
      have hCNoUpper := (hSums.rawParent_none_iff_upper_none hValid
        (hGeometry.real r hr hrf.le c hc)).mp hC
      have hZNoUpper := (hSums.rawParent_none_iff_upper_none hValid
        (hGeometry.real r hr hrf.le z hz)).mp hZ
      have hCNoMove : ¬ Frame.frontierMoves front r c := by
        intro hMove
        have hUpper := (hGeometry.advance r hr hrf c hc hMove).1
        rw [hCNoUpper] at hUpper
        cases hUpper
      have hZNoMove : ¬ Frame.frontierMoves front r z := by
        intro hMove
        have hUpper := (hGeometry.advance r hr hrf z hz hMove).1
        rw [hZNoUpper] at hUpper
        cases hUpper
      exact ⟨fun h => False.elim (hCNoMove h), fun h => False.elim (hZNoMove h)⟩
    | some parent =>
      cases hZ : (Frame.ofMountain mountain).rawParent (front r z) with
      | none => simp [hC, hZ] at hCommonRaw
      | some otherParent =>
        have hColumns : parent.1.val = otherParent.1.val := by
          simpa only [hC, hZ, Option.map_some, Option.some.injEq] using hCommonRaw
        have hParents : parent = otherParent := by
          rw [← hGeometry.parent_frontier r hr hrf c hc parent hC,
            ← hGeometry.parent_frontier r hr hrf z hz otherParent hZ, hColumns]
        subst otherParent
        obtain ⟨cUpper, hCUpper, _⟩ := Frame.rawParent_spec hC
        obtain ⟨zUpper, hZUpper, _⟩ := Frame.rawParent_spec hZ
        obtain ⟨hParentC, hCB⟩ := hGeometry.raw_B r hr hrf c hc cUpper parent hCUpper hC
        obtain ⟨hParentZ, hZB⟩ := hGeometry.raw_B r hr hrf z hz zUpper parent hZUpper hZ
        have hUpperRows : (Frame.ofMountain mountain).height cUpper =
            (Frame.ofMountain mountain).height zUpper := by
          rw [hCB, hZB]
          exact Frame.B_equal_at_common_frontier hParentC hParentZ
            (hGeometry.below_cut r hr hrf.le c hc) (hGeometry.below_cut r hr hrf.le z hz)
            (by rw [← hCB]; exact hGeometry.upper_above_cut r hr hrf.le c hc cUpper hCUpper)
            (by rw [← hZB]; exact hGeometry.upper_above_cut r hr hrf.le z hz zUpper hZUpper)
        rw [hGeometry.moves_iff_upper_at_cut hr hrf hc hCUpper,
          hGeometry.moves_iff_upper_at_cut hr hrf hz hZUpper, hUpperRows]

/-- The numerical sums required by the generic interface are supplied by
the actual expansion. Parent-frontier closure and raw B geometry are still
explicit obligations, not consequences asserted by this wrapper. -/
theorem expandDiagram_synchronousBackfill {values : List Nat} (hLegal : Legal values)
    {copies : Nat} {mountain : Mountain} (hRun : expandDiagram values copies = .ok mountain)
    {front : Nat → Nat → (Frame.ofMountain mountain).Node} {cut : Nat → Row}
    {bound start finish : Nat}
    (hGeometry : Frame.FrontierGeometry (Frame.ofMountain mountain) front cut bound start finish)
    (initial : ZeroY.ParentMap) :
    Forests.SynchronousBackfill
      ((Frame.ofMountain mountain).frontierForests initial front bound)
      ((Frame.ofMountain mountain).frontierValue front)
      (Frame.frontierMoves front) bound start finish := by
  obtain ⟨actual, hActual, hValid, hSums, _⟩ := expandDiagram_total_with_equations hLegal copies
  have hEq : actual = mountain := Except.ok.inj (hActual.symm.trans hRun)
  subst actual
  exact synchronousBackfill_of_frontier_geometry hValid hSums hGeometry initial

end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.frontierAt_spec
#print axioms OmegaY.Geometry.Frame.frontierAt_eq_of_upper_barrier
#print axioms OmegaY.Geometry.Frame.frontierAt_advance
#print axioms OmegaY.Geometry.Frame.frontierParent_leftward
#print axioms OmegaY.Geometry.Frame.frontierForests_leftward
#print axioms OmegaY.Geometry.Frame.FrontierGeometry.moves_iff_upper_at_cut
#print axioms OmegaY.Geometry.Frame.B_equal_at_common_frontier
#print axioms OmegaY.Expansion.parent_sum_iff_frontier_value
#print axioms OmegaY.Expansion.synchronousBackfill_of_frontier_geometry
#print axioms OmegaY.Expansion.expandDiagram_synchronousBackfill
