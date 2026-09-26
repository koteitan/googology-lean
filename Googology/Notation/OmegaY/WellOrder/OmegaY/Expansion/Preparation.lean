/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/Preparation.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/Preparation.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Totality
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.Markers

set_option backward.do.legacy false

/-!
# Total preparation of a nontrivial expansion

The original and decremented mountains, the actual last-top left endpoint,
the unchanged root cell, and the actual marker array are all constructed.
There is no hypothesis that either build or marker enumeration succeeds.
The block-copy stage itself remains a separate obligation.
-/

namespace OmegaY.Expansion

open Canonical

structure Preparation (front : List Nat) (last : Nat) where
  initial : Mountain
  reduced : Mountain
  root : Ref
  lastTop : Cell
  rootCell : Cell
  marked : Array (List Ref)
  initial_build : Canonical.build (front ++ [last]) = .ok initial
  reduced_build : Canonical.build (front ++ [last - 1]) = .ok reduced
  initial_valid : MountainValid initial
  reduced_valid : MountainValid reduced
  initial_top : (initial[front.length]?).bind Array.back? = some lastTop
  top_left : lastTop.left = some root
  root_before_last : root.column < front.length
  initial_root : Canonical.cellAt initial root = .ok rootCell
  restored_root : Canonical.cellAt reduced root = .ok rootCell
  markers_built : markers reduced root = .ok marked

/-- Every legal nontrivial input has actual finite preparation data.
`1 :: middle ++ [last]` covers all legal inputs with final value greater than 1. -/
theorem preparation_total (middle : List Nat) (last : Nat)
    (hmiddle : ∀ value ∈ middle, 0 < value) (hlast : 1 < last) :
    Nonempty (Preparation (1 :: middle) last) := by
  let front := 1 :: middle
  have hlegal : Legal (front ++ [last]) := by
    refine Or.inr ⟨middle ++ [last], rfl, ?_⟩
    intro value hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hmiddle value hv
    · have he : value = last := List.mem_singleton.mp hv
      subst value; omega
  have hdecreased : Legal (front ++ [last - 1]) := by
    refine Or.inr ⟨middle ++ [last - 1], rfl, ?_⟩
    intro value hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hmiddle value hv
    · have he : value = last - 1 := List.mem_singleton.mp hv
      subst value; omega
  obtain ⟨initial, hi, hiv, hit, his⟩ := build_total_with_size hlegal
  obtain ⟨reduced, hd, hdv, _hdt⟩ := build_total hdecreased
  have hc : front.length < initial.size := by
    simp only [List.length_append, List.length_singleton] at his
    omega
  have hcpos : 0 < front.length := by simp [front]
  let column := initial[front.length]
  have hcolumn : ColumnValid initial front.length column := hiv front.length hc
  obtain ⟨lastTop, htop, _htopvalue⟩ := hit front.length hc
  have hread : column[column.size - 1]? = some lastTop := by
    simpa only [Array.back?_eq_getElem?] using htop
  have hindex : 0 < column.size - 1 := by have := hcolumn.size_ge_two; omega
  obtain ⟨root, hleft⟩ := hcolumn.stored_exists _ _ hread hindex hcpos
  obtain ⟨hrootleft, rootCell, hrootread, _hrootrow⟩ :=
    hcolumn.stored_valid _ _ _ hread hleft
  have hrestore : Canonical.cellAt reduced root = .ok rootCell :=
    (build_changed_last_preserves_ref hi hd hrootleft).symm.trans hrootread
  have hvalidroot : ValidRef reduced root :=
    ⟨rootCell, cellAt_ok_iff.mp hrestore⟩
  obtain ⟨marked, hmarked⟩ := markers_total
    (weakLocal_of_ordered hdv.toOrdered hdv.left_sources) hvalidroot
  refine ⟨{
    initial := initial
    reduced := reduced
    root := root
    lastTop := lastTop
    rootCell := rootCell
    marked := marked
    initial_build := hi
    reduced_build := hd
    initial_valid := hiv
    reduced_valid := hdv
    initial_top := ?_
    top_left := hleft
    root_before_last := hrootleft
    initial_root := hrootread
    restored_root := hrestore
    markers_built := hmarked }⟩
  change (initial[front.length]?).bind Array.back? = some lastTop
  rw [Array.getElem?_eq_getElem hc]
  exact htop

end OmegaY.Expansion

#print axioms OmegaY.Expansion.preparation_total
