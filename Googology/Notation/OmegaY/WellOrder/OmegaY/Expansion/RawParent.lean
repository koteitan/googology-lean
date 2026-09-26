/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/RawParent.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/RawParent.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.TotalEquations

set_option backward.do.legacy false

/-!
# The actual stored-parent relation before numerical canonicality

The raw parent of a node is the left endpoint stored on its vertical upper
neighbour. This definition neither calls `Q` nor searches with `P`. Basic
ordered geometry makes raw parent edges strictly leftward. The independently
proved sums and tops of the actual expanded graph give the numerical laws.

Well-foundedness below concerns parent traversal inside one finite mountain,
not the relation between successive expanded sequences. Identifying raw
parents with numerical first-smaller parents, and synchronizing frontier
event forests, remain separate obligations.
-/

namespace OmegaY.Geometry.Frame

def rawParent (F : Frame) (u : F.Node) : Option F.Node := do
  let upper ← F.upper u
  let stored ← (F.cell upper).left
  F.lookup stored

def RawParentRel (F : Frame) (parent child : F.Node) : Prop :=
  F.rawParent child = some parent

theorem rawParent_eq_of_upper_left {F : Frame} {u upper parent : F.Node}
    (hUpper : F.upper u = some upper) (hLeft : (F.cell upper).left = some (ref parent)) :
    F.rawParent u = some parent := by
  simp [rawParent, hUpper, hLeft]

theorem rawParent_none_of_upper_none {F : Frame} {u : F.Node}
    (hUpper : F.upper u = none) : F.rawParent u = none := by
  simp [rawParent, hUpper]

theorem rawParent_spec {F : Frame} {u parent : F.Node}
    (h : F.rawParent u = some parent) :
    ∃ upper, F.upper u = some upper ∧ (F.cell upper).left = some (ref parent) := by
  cases hUpper : F.upper u with
  | none => simp [rawParent, hUpper] at h
  | some upper =>
    cases hLeft : (F.cell upper).left with
    | none => simp [rawParent, hUpper, hLeft] at h
    | some stored =>
      have hLookup : F.lookup stored = some parent := by
        simpa [rawParent, hUpper, hLeft] using h
      exact ⟨upper, rfl, by simpa only [lookup_spec hLookup] using hLeft⟩

/-- Raw parent edges decrease the column even for phantom nodes. No
numerical equations or canonical search rules are needed. -/
theorem rawParent_column_lt {F : Frame} (hF : F.Ordered) {u parent : F.Node}
    (h : F.rawParent u = some parent) : parent.1.val < u.1.val := by
  obtain ⟨upper, hUpper, hLeft⟩ := rawParent_spec h
  obtain ⟨found, hFound, hColumn, _⟩ := hF.stored_valid upper (ref parent) hLeft
  have hEq : found = parent := Option.some.inj
    (hFound.symm.trans (F.lookup_ref parent))
  subst found
  simpa only [(upper_spec hUpper).1] using hColumn

theorem rawParent_wellFounded {F : Frame} (hF : F.Ordered) :
    WellFounded F.RawParentRel := by
  have hAcc : ∀ column, ∀ u : F.Node, u.1.val = column → Acc F.RawParentRel u := by
    intro column
    induction column using Nat.strongRecOn with
    | ind column ih =>
      intro u hu
      apply Acc.intro u
      intro parent hParent
      have hLt : parent.1.val < column := by
        simpa only [hu] using rawParent_column_lt hF hParent
      exact ih parent.1.val hLt parent rfl
  exact ⟨fun u => hAcc u.1.val u rfl⟩

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry

/-- Every real adjacent pair in an actual mountain with backfill sums has
an actual raw parent. Positivity of both summands gives strict value descent.
No B row equation or numerical-parent identity is assumed. -/
theorem MountainSums.rawParent_upper {mountain : Mountain}
    (hSums : MountainSums mountain) (hValid : MountainValid mountain)
    {u upper : (Frame.ofMountain mountain).Node} (hReal : Frame.Real u)
    (hUpper : (Frame.ofMountain mountain).upper u = some upper) :
    ∃ parent, (Frame.ofMountain mountain).rawParent u = some parent ∧
      parent.1.val < u.1.val ∧ 0 < (Frame.ofMountain mountain).value parent ∧
      (Frame.ofMountain mountain).value parent < (Frame.ofMountain mountain).value u ∧
      (Frame.ofMountain mountain).value u =
        (Frame.ofMountain mountain).value upper + (Frame.ofMountain mountain).value parent ∧
      1 < (Frame.ofMountain mountain).value u := by
  rcases u with ⟨c, i⟩
  unfold Frame.upper at hUpper
  split at hUpper
  · obtain rfl := Option.some.inj hUpper
    rename_i hNext
    have hi : i.val < mountain[c.val].size := i.isLt
    have hj : i.val + 1 < mountain[c.val].size := hNext
    have hRow : mountain[c.val][i.val].row ≠ 0 := by
      have hStrict := (hValid c.val c.isLt).rows_strict 0 i.val phantom
        mountain[c.val][i.val] (hValid c.val c.isLt).phantom
        (Array.getElem?_eq_getElem hi) hReal
      exact ne_of_gt hStrict
    have hChain : mountain[c.val].toList.IsChain (AdjacentSum mountain) := hSums c.val c.isLt
    have hSum := (List.isChain_iff_getElem.mp hChain) i.val
      (by change i.val + 1 < mountain[c.val].size; exact hj)
    simp only [Array.getElem_toList] at hSum
    obtain ⟨parentRef, parentCell, hLeft, hRead, hPositive, hValue⟩ := hSum hRow
    obtain ⟨parent, hRef, hCell⟩ := frame_node_of_cellAt (lookup_ok_iff.mp hRead)
    have hRaw : (Frame.ofMountain mountain).rawParent ⟨c, i⟩ = some parent := by
      apply Frame.rawParent_eq_of_upper_left (upper := ⟨c, ⟨i.val + 1, hNext⟩⟩)
      · simp [Frame.upper, hNext]
      · rw [hRef]
        exact hLeft
    have hUpperPositive := (hValid c.val c.isLt).real_positive (i.val + 1)
      mountain[c.val][i.val + 1] (Array.getElem?_eq_getElem hj) (by omega)
    refine ⟨parent, hRaw, Frame.rawParent_column_lt hValid.toOrdered hRaw, ?_, ?_, ?_, ?_⟩
    · simpa only [Frame.value, hCell] using hPositive
    · change (Frame.ofMountain mountain).value parent < mountain[c.val][i.val].value
      simp only [Frame.value, hCell]
      omega
    · change mountain[c.val][i.val].value = mountain[c.val][i.val + 1].value +
        (Frame.ofMountain mountain).value parent
      simpa only [Frame.value, hCell] using hValue
    · change 1 < mountain[c.val][i.val].value
      omega
  · cases hUpper

theorem MountainSums.rawParent_none_iff_upper_none {mountain : Mountain}
    (hSums : MountainSums mountain) (hValid : MountainValid mountain)
    {u : (Frame.ofMountain mountain).Node} (hReal : Frame.Real u) :
    (Frame.ofMountain mountain).rawParent u = none ↔
      (Frame.ofMountain mountain).upper u = none := by
  constructor
  · intro hNone
    cases hUpper : (Frame.ofMountain mountain).upper u with
    | none => rfl
    | some upper =>
      obtain ⟨parent, hParent, _⟩ := hSums.rawParent_upper hValid hReal hUpper
      rw [hNone] at hParent
      cases hParent
  · exact Frame.rawParent_none_of_upper_none

/-- A top is value one by MountainTops, independently of all parent rules. -/
theorem MountainTops.value_one_of_upper_none {mountain : Mountain}
    (hTops : MountainTops mountain) {u : (Frame.ofMountain mountain).Node}
    (hUpper : (Frame.ofMountain mountain).upper u = none) :
    (Frame.ofMountain mountain).value u = 1 := by
  rcases u with ⟨c, i⟩
  have hi : i.val < mountain[c.val].size := i.isLt
  have hNoNext : ¬ i.val + 1 < mountain[c.val].size := by
    intro hNext
    unfold Frame.upper at hUpper
    split at hUpper
    · cases hUpper
    · rename_i hNo
      exact hNo (by simpa only [Frame.ofMountain] using hNext)
  have hLast : i.val = mountain[c.val].size - 1 := by omega
  obtain ⟨topCell, hTop, hOne⟩ := hTops c.val c.isLt
  change mountain[c.val].back? = some topCell at hTop
  have hTopRead : mountain[c.val][i.val]? = some topCell := by
    rw [hLast]
    rw [Array.back?_eq_getElem?] at hTop
    exact hTop
  have hCell : mountain[c.val][i.val] = topCell :=
    Option.some.inj ((Array.getElem?_eq_getElem hi).symm.trans hTopRead)
  change mountain[c.val][i.val].value = 1
  exact hCell ▸ hOne

/-- On real nodes of the actual graph, raw roots are exactly value-one tops.
Phantom nodes are intentionally excluded from this numerical equivalence. -/
theorem MountainSums.rawParent_none_iff_value_one {mountain : Mountain}
    (hSums : MountainSums mountain) (hValid : MountainValid mountain)
    (hTops : MountainTops mountain) {u : (Frame.ofMountain mountain).Node}
    (hReal : Frame.Real u) :
    (Frame.ofMountain mountain).rawParent u = none ↔ (Frame.ofMountain mountain).value u = 1 := by
  rw [hSums.rawParent_none_iff_upper_none hValid hReal]
  constructor
  · exact MountainTops.value_one_of_upper_none hTops
  · intro hOne
    cases hUpper : (Frame.ofMountain mountain).upper u with
    | none => rfl
    | some upper =>
      obtain ⟨_, _, _, _, _, _, hLarge⟩ := hSums.rawParent_upper hValid hReal hUpper
      omega

/-- All laws are supplied for every actual expanded mountain. The only
well-founded relation here is its internal raw-parent relation. -/
theorem expandDiagram_rawParent {values : List Nat} (hLegal : Legal values)
    {copies : Nat} {mountain : Mountain} (hRun : expandDiagram values copies = .ok mountain) :
    WellFounded (Frame.ofMountain mountain).RawParentRel ∧
    (∀ u upper, Frame.Real u → (Frame.ofMountain mountain).upper u = some upper →
      ∃ parent, (Frame.ofMountain mountain).rawParent u = some parent ∧
        parent.1.val < u.1.val ∧ 0 < (Frame.ofMountain mountain).value parent ∧
        (Frame.ofMountain mountain).value parent < (Frame.ofMountain mountain).value u ∧
        (Frame.ofMountain mountain).value u =
          (Frame.ofMountain mountain).value upper + (Frame.ofMountain mountain).value parent ∧
        1 < (Frame.ofMountain mountain).value u) ∧
    ∀ u, Frame.Real u → ((Frame.ofMountain mountain).rawParent u = none ↔
      (Frame.ofMountain mountain).value u = 1) := by
  obtain ⟨actual, hActual, hValid, hSums, hTops⟩ := expandDiagram_total_with_equations hLegal copies
  have hEq : actual = mountain := Except.ok.inj (hActual.symm.trans hRun)
  subst actual
  exact ⟨Frame.rawParent_wellFounded hValid.toOrdered,
    fun _ _ hReal hUpper => hSums.rawParent_upper hValid hReal hUpper,
    fun _ hReal => hSums.rawParent_none_iff_value_one hValid hTops hReal⟩

end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.rawParent_eq_of_upper_left
#print axioms OmegaY.Geometry.Frame.rawParent_none_of_upper_none
#print axioms OmegaY.Geometry.Frame.rawParent_spec
#print axioms OmegaY.Geometry.Frame.rawParent_column_lt
#print axioms OmegaY.Geometry.Frame.rawParent_wellFounded
#print axioms OmegaY.Expansion.MountainSums.rawParent_upper
#print axioms OmegaY.Expansion.MountainSums.rawParent_none_iff_upper_none
#print axioms OmegaY.Expansion.MountainTops.value_one_of_upper_none
#print axioms OmegaY.Expansion.MountainSums.rawParent_none_iff_value_one
#print axioms OmegaY.Expansion.expandDiagram_rawParent
