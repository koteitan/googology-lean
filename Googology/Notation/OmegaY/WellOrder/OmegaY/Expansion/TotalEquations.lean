/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/TotalEquations.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/TotalEquations.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.Totality
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.BlockEquations

set_option backward.do.legacy false

/-! Every actual expanded graph has the proved numerical equations and
value-one tops. These are necessary reconstruction certificates; they do
not assert that its stored parent is the canonical numerical parent. -/

namespace OmegaY.Expansion

open Canonical

theorem expandDiagram_equations {values : List Nat} (hLegal : Legal values)
    {copies : Nat} {result : Mountain} (hRun : expandDiagram values copies = .ok result) :
    MountainSums result ∧ MountainTops result := by
  by_cases hTrivial : values.isEmpty ∨ values.getLast? = some 1 ∨ copies = 0
  · obtain ⟨initial, hBuild, hValid, hTops⟩ := build_total hLegal
    have hActual : expandDiagram values copies = .ok initial.pop := by
      simp only [List.isEmpty_iff] at hTrivial
      simp [expandDiagram, hBuild, Except.mapError, hTrivial]
    have he : initial.pop = result := Except.ok.inj (hActual.symm.trans hRun)
    subst result
    exact ⟨(build_mountain_sums hBuild).pop hValid, MountainTops.pop hTops⟩
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
        exact p.expandDiagram_equations hLast hCopies hRun

theorem expandDiagram_total_with_equations {values : List Nat}
    (hLegal : Legal values) (copies : Nat) :
    ∃ result, expandDiagram values copies = .ok result ∧ MountainValid result ∧
      MountainSums result ∧ MountainTops result := by
  obtain ⟨result, hRun, hValid⟩ := expandDiagram_total hLegal copies
  exact ⟨result, hRun, hValid, expandDiagram_equations hLegal hRun⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.expandDiagram_equations
#print axioms OmegaY.Expansion.expandDiagram_total_with_equations
