/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Canonical/BuildSplit.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Canonical/BuildSplit.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Domain
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Values

set_option backward.do.legacy false

/-!
# Splitting actual builds at their last input

Successful validation of the full input also validates its possibly empty
front. The left mountain below is the actual validated build of that front,
not an independently assumed successful object.
-/

namespace OmegaY.Canonical

open Geometry

theorem Legal.front {front suffix : List Nat} (h : Legal (front ++ suffix)) : Legal front := by
  cases front with
  | nil => exact Or.inl rfl
  | cons first rest =>
    rcases h with he | ⟨tail, he, hpositive⟩
    · simp at he
    · have hparts : first = 1 ∧ rest ++ suffix = tail := by simpa using he
      obtain ⟨rfl, rfl⟩ := hparts
      exact Or.inr ⟨rest, rfl, fun value hv => hpositive value (List.mem_append_left _ hv)⟩

theorem build_eq_buildFrom_of_legal {values : List Nat} (h : Legal values) :
    build values = buildFrom #[] values := by
  rcases h with rfl | ⟨rest, rfl, hpositive⟩
  · rfl
  · have hAll : rest.all (fun n => 0 < n) = true := by
      simpa only [List.all_eq_true, decide_eq_true_eq] using hpositive
    simp [build, hAll]

/-- Decompose a successful whole build into its actual front and final
column, including the exact size and old-column preservation equations. -/
theorem build_split_last {front : List Nat} {last : Nat} {old : Mountain}
    (hBuild : build (front ++ [last]) = .ok old) :
    ∃ (left : Mountain) (column : Column),
      build front = .ok left ∧ buildColumn left last = .ok column ∧
      old = left.push column ∧ left.size = front.length ∧
      ∀ c, c < left.size → old[c]? = left[c]? := by
  obtain ⟨left, hFront, hLast⟩ :=
    buildFrom_append_success_iff.mp (buildFrom_of_build hBuild)
  have hFrontLegal : Legal front := (build_success_legal hBuild).front
  have hFrontBuild : build front = .ok left :=
    (build_eq_buildFrom_of_legal hFrontLegal).trans hFront
  cases hColumn : buildColumn left last with
  | error e => simp [buildFrom, hColumn] at hLast
  | ok column =>
    have hShape : old = left.push column := by
      simpa only [buildFrom, hColumn, except_bind_ok, Except.ok.injEq] using hLast.symm
    refine ⟨left, column, hFrontBuild, hColumn, hShape, build_size hFrontBuild, ?_⟩
    intro c hc
    rw [hShape]
    simp [Array.getElem?_push, Nat.ne_of_lt hc]

/-- Different final input values share one and the same actual front build. -/
theorem build_split_common_front {front : List Nat} {oldLast newLast : Nat}
    {before after : Mountain}
    (hBefore : build (front ++ [oldLast]) = .ok before)
    (hAfter : build (front ++ [newLast]) = .ok after) :
    ∃ (left : Mountain) (oldColumn newColumn : Column),
      build front = .ok left ∧
      buildColumn left oldLast = .ok oldColumn ∧ before = left.push oldColumn ∧
      buildColumn left newLast = .ok newColumn ∧ after = left.push newColumn ∧
      left.size = front.length ∧
      ∀ c, c < left.size → before[c]? = left[c]? ∧ after[c]? = left[c]? := by
  obtain ⟨left, oldColumn, hLeft, hOld, hBeforeShape, hSize, hBeforePrefix⟩ := build_split_last hBefore
  obtain ⟨other, newColumn, hOther, hNew, hAfterShape, _, hAfterPrefix⟩ := build_split_last hAfter
  have he : other = left := Except.ok.inj (hOther.symm.trans hLeft)
  subst other
  exact ⟨left, oldColumn, newColumn, hLeft, hOld, hBeforeShape, hNew, hAfterShape,
    hSize, fun c hc => ⟨hBeforePrefix c hc, hAfterPrefix c hc⟩⟩

/-- The final bottom cell has its exact input value and actual initial leg.
This holds even for the value-one case. -/
theorem build_last_bottom_read {front : List Nat} {last : Nat} {old : Mountain}
    (hBuild : build (front ++ [last]) = .ok old) :
    cellAt old ⟨front.length, 1⟩ = .ok (initialBottom front.length last) := by
  obtain ⟨left, column, _, hColumn, hShape, hSize, _⟩ := build_split_last hBuild
  rw [hShape, ← hSize]
  simp [cellAt, Array.getElem?_push, buildColumn_bottom hColumn]

/-- A typed node for the old last bottom, supplied by the actual read. -/
theorem build_last_bottom_node {front : List Nat} {last : Nat} {old : Mountain}
    (hBuild : build (front ++ [last]) = .ok old) :
    ∃ u : (Frame.ofMountain old).Node,
      Frame.ref u = ⟨front.length, 1⟩ ∧ Frame.Real u ∧
      (Frame.ofMountain old).cell u = initialBottom front.length last ∧
      (Frame.ofMountain old).height u = 1 ∧ (Frame.ofMountain old).value u = last := by
  obtain ⟨u, hRef, hCell⟩ := frame_node_of_cellAt (build_last_bottom_read hBuild)
  have hIndex : u.2.val = 1 := congrArg Ref.index hRef
  refine ⟨u, hRef, by unfold Frame.Real; omega, hCell, ?_, ?_⟩
  · exact congrArg Cell.row hCell
  · exact congrArg Cell.value hCell

#print axioms build_split_last
#print axioms build_split_common_front
#print axioms build_last_bottom_node

end OmegaY.Canonical
