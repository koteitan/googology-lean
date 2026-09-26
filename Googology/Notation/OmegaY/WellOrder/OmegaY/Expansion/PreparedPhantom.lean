/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/PreparedPhantom.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/PreparedPhantom.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.PreparedReferenceAt

set_option backward.do.legacy false

/-! The zero-row marker is not lifted. The actual boundary list ends in
one, strict-below selection at one returns the real stored phantom, and
referenceAt takes that last qualifying reference when asked for zero. -/

namespace OmegaY.Expansion

open Canonical

theorem below_one {mountain : Mountain} (hValid : MountainValid mountain)
    {column : Nat} (hc : column < mountain.size) :
    below mountain column 1 = .ok ⟨column, 0⟩ := by
  obtain ⟨found, hFound⟩ := below_positive_total hValid hc Row.zero_lt_one
  have hColumn := Array.getElem?_eq_getElem hc
  obtain ⟨hSame, cell, hCell, hRow⟩ := below_result hColumn hFound
  have hZero : found.index = 0 := by
    by_contra hn
    have hSize := (hValid column hc).size_ge_two
    have hb : 1 < mountain[column].size := by omega
    let bottom := mountain[column][1]
    have hBottom : mountain[column][1]? = some bottom := Array.getElem?_eq_getElem hb
    have hBottomRow := (hValid column hc).bottom_row bottom hBottom
    by_cases hi : found.index = 1
    · rw [hi] at hCell
      have he := Option.some.inj (hCell.symm.trans hBottom)
      exact (not_lt_of_ge ((congrArg Cell.row he).trans hBottomRow).ge) hRow
    · have hStrict := (hValid column hc).rows_strict 1 found.index bottom cell hBottom hCell (by omega)
      rw [hBottomRow] at hStrict
      exact (not_lt_of_ge hStrict.le) hRow
  have he : found = ⟨column, 0⟩ := by
    cases found
    simp_all only
  exact he ▸ hFound

private theorem list_first_two {α : Type} {xs : List α} {a b : α}
    (hZero : xs[0]? = some a) (hOne : xs[1]? = some b) :
    ∃ tail, xs = a :: b :: tail := by
  cases xs with
  | nil => simp at hZero
  | cons first rest =>
    have he : first = a := by simpa using hZero
    subst first
    cases rest with
    | nil => simp at hOne
    | cons second tail =>
      have he : second = b := by simpa using hOne
      subst second
      exact ⟨tail, rfl⟩

theorem Preparation.boundaries_end_one {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) :
    ∃ higher, p.boundaries = higher ++ [1] := by
  obtain ⟨nodes, hColumn, _⟩ := cellAt_ok_iff.mp p.initial_root
  obtain ⟨hc, hNodes⟩ := Array.getElem?_eq_some_iff.mp hColumn
  have hValid : ColumnValid p.initial p.root.column nodes :=
    hNodes ▸ p.initial_valid p.root.column hc
  have hSize := hValid.size_ge_two
  have hb : 1 < nodes.size := by omega
  let bottom := nodes[1]
  have hBottom : nodes[1]? = some bottom := Array.getElem?_eq_getElem hb
  have hBottomRow := hValid.bottom_row bottom hBottom
  obtain ⟨tail, hList⟩ := list_first_two
    (show nodes.toList[0]? = some phantom by simpa only [Array.getElem?_toList] using hValid.phantom)
    (show nodes.toList[1]? = some bottom by simpa only [Array.getElem?_toList] using hBottom)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (p.root_index_pos hLast))
  refine ⟨p.lastTop.row :: ((tail.take k).reverse.filterMap
    fun cell => if cell.row = 0 then none else some cell.row), ?_⟩
  rw [p.boundaries_of_column hColumn, hList, hk]
  simp [List.reverse_cons, List.filterMap_append, hBottomRow, phantom,
    ne_of_gt Row.zero_lt_one]

theorem referenceAt_last {mountain : Mountain} {earlier : List Ref}
    {ref : Ref} {cell : Cell} {row : Row}
    (hValid : ∀ entry ∈ earlier ++ [ref], ValidRef mountain entry)
    (hRead : lookup mountain ref = .ok cell) (hRow : row ≤ cell.row) :
    referenceAt mountain (earlier ++ [ref]) row = .ok cell.row := by
  apply (referenceAt_iff_getLast hValid).mpr
  simp [referenceCandidates, List.filterMap_append, hRead, Except.toOption, hRow]

/-- The phantom is the actual last element of the complete mapM output. -/
theorem Preparation.initial_references_end_phantom {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {references : List Ref}
    (hRun : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references) :
    ∃ earlier, references = earlier ++ [⟨p.reduced.size - 1, 0⟩] := by
  obtain ⟨higher, hBoundaries⟩ := p.boundaries_end_one hLast
  have hPhantom := below_one p.reduced_valid p.reduced_last_exists
  rw [hBoundaries, List.mapM_append] at hRun
  cases hEarlier : higher.mapM (below p.reduced (p.reduced.size - 1)) with
  | error error => simp [hEarlier] at hRun
  | ok earlier =>
    exact ⟨earlier, by simpa [hEarlier, hPhantom] using hRun.symm⟩

/-- This exact zero is needed when stitching the phantom contour to the
real bottom: a mere nonnegative lower bound would allow a false lift. -/
theorem Preparation.initial_referenceAt_zero {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {references : List Ref}
    (hRun : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references) :
    referenceAt p.reduced references 0 = .ok 0 := by
  obtain ⟨earlier, hReferences⟩ := p.initial_references_end_phantom hLast hRun
  have hValid := p.initial_references_valid hRun
  rw [hReferences] at hValid ⊢
  have hc := p.reduced_last_exists
  have hPhantom : lookup p.reduced ⟨p.reduced.size - 1, 0⟩ = .ok phantom :=
    lookup_ok_iff.mpr ⟨p.reduced[p.reduced.size - 1],
      Array.getElem?_eq_getElem p.reduced_last_exists,
      (p.reduced_valid _ p.reduced_last_exists).phantom⟩
  exact referenceAt_last hValid hPhantom le_rfl

end OmegaY.Expansion

#print axioms OmegaY.Expansion.below_one
#print axioms OmegaY.Expansion.Preparation.initial_referenceAt_zero
