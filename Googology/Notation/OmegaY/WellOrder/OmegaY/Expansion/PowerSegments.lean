/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/PowerSegments.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/PowerSegments.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.FinishPowerSteps

set_option backward.do.legacy false

/-! Ascending marker order supplies actual consecutive-marker gaps.
Power-step paths concatenate using only their real adjacent seams; the
power relation is not incorrectly treated as transitive. -/

namespace OmegaY.Expansion

open Canonical

theorem ordered_markers_adjacent {markers : List Ref}
    (hOrder : markers.Pairwise (fun a b => a.index < b.index)) :
    markers.IsChain (fun a b => a.index < b.index ∧
      ∀ entry ∈ markers, ¬(a.index < entry.index ∧ entry.index < b.index)) := by
  apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
  intro a b before after hSplit
  have hParts := hOrder
  rw [hSplit, List.pairwise_append] at hParts
  have hTail := List.pairwise_cons.mp hParts.2.1
  refine ⟨hTail.1 b (by simp), ?_⟩
  intro entry hEntry hBetween
  rw [hSplit] at hEntry
  rcases List.mem_append.mp hEntry with hBefore | hRest
  · have hBelow := hParts.2.2 entry hBefore a (by simp)
    omega
  · rcases List.mem_cons.mp hRest with he | hRest
    · subst entry
      omega
    · rcases List.mem_cons.mp hRest with he | hAfter
      · subst entry
        omega
      · have hAbove := (List.pairwise_cons.mp hTail.2).1 entry hAfter
        omega

theorem RowsPowerSteps.flatMap_of_adjacent {α : Type} {items : List α}
    (pieces : α → List Row)
    (hNonempty : ∀ item ∈ items, pieces item ≠ [])
    (hPower : ∀ item ∈ items, RowsPowerSteps (pieces item))
    (hSeams : items.IsChain (fun a b =>
      ∀ lower ∈ (pieces a).getLast?, ∀ upper ∈ (pieces b).head?, RowPowerStep lower upper)) :
    RowsPowerSteps (items.flatMap pieces) := by
  induction items with
  | nil => exact .nil
  | cons first rest ih =>
    cases rest with
    | nil => simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        using hPower first (by simp)
    | cons next rest =>
      have hTailPower := ih
        (fun item hm => hNonempty item (List.mem_cons_of_mem first hm))
        (fun item hm => hPower item (List.mem_cons_of_mem first hm)) hSeams.tail
      have hHead : ((next :: rest).flatMap pieces).head? = (pieces next).head? := by
        cases hNext : pieces next with
        | nil => exact False.elim (hNonempty next (by simp) hNext)
        | cons head tail => simp only [List.flatMap_cons, hNext, List.cons_append, List.head?_cons]
      apply RowsPowerSteps.append (hPower first (by simp)) hTailPower
      intro lower hLower upper hUpper
      rw [hHead] at hUpper
      exact hSeams.rel lower hLower upper hUpper

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ordered_markers_adjacent
#print axioms OmegaY.Expansion.RowsPowerSteps.flatMap_of_adjacent
