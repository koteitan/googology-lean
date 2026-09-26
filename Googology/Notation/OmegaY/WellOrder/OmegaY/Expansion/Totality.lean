/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/Totality.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/Totality.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.BlocksTotal
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.TruncateValues

set_option backward.do.legacy false

/-! Totality of the unchanged weak-magma expansion on its entire syntactic
domain, for every finite copy count. This does not assert well-foundedness
of the relation obtained by repeatedly expanding the returned sequences. -/

namespace OmegaY.Expansion

open Canonical

theorem expandDiagram_total {values : List Nat} (hLegal : Legal values) (copies : Nat) :
    ∃ mountain, expandDiagram values copies = .ok mountain ∧ MountainValid mountain := by
  by_cases hTrivial : values.isEmpty ∨ values.getLast? = some 1 ∨ copies = 0
  · obtain ⟨initial, hBuild, hValid, _⟩ := build_total hLegal
    refine ⟨initial.pop, ?_, hValid.pop⟩
    simp only [List.isEmpty_iff] at hTrivial
    simp [expandDiagram, hBuild, Except.mapError, hTrivial]
  · rcases hLegal with rfl | ⟨rest, rfl, hPositive⟩
    · simp at hTrivial
    · rcases List.eq_nil_or_concat' rest with rfl | ⟨middle, last, rfl⟩
      · simp at hTrivial
      · have hLastPositive : 0 < last := hPositive last (by simp)
        have hLastNe : last ≠ 1 := by
          intro hLast
          apply hTrivial
          right; left
          change ((1 :: middle) ++ [last]).getLast? = some 1
          rw [List.getLast?_append]
          simp [hLast]
        have hLast : 1 < last := by omega
        have hCopies : 0 < copies := by
          by_contra h
          apply hTrivial
          right; right
          omega
        obtain ⟨p⟩ := preparation_total middle last
          (fun value hv => hPositive value (by simp [hv])) hLast
        obtain ⟨result, hRun, hReady⟩ := p.expandDiagram_total hLast hCopies
        exact ⟨result.pop, hRun, hReady.valid.pop⟩

theorem expand_total {values : List Nat} (hLegal : Legal values) (copies : Nat) :
    ∃ result, expand values copies = .ok result ∧ Legal result := by
  obtain ⟨mountain, hDiagram, hValid⟩ := expandDiagram_total hLegal copies
  obtain ⟨result, hValues, hResultLegal, _⟩ := valuesOf_total_legal hValid
  refine ⟨result, ?_, hResultLegal⟩
  simp only [expand, hDiagram]
  exact hValues

theorem expand_legal_of_success {values result : List Nat} {copies : Nat}
    (hLegal : Legal values) (hRun : expand values copies = .ok result) : Legal result := by
  obtain ⟨actual, hActual, hActualLegal⟩ := expand_total hLegal copies
  have he : actual = result := Except.ok.inj (hActual.symm.trans hRun)
  exact he ▸ hActualLegal

end OmegaY.Expansion

#print axioms OmegaY.Expansion.expandDiagram_total
#print axioms OmegaY.Expansion.expand_total
#print axioms OmegaY.Expansion.expand_legal_of_success
