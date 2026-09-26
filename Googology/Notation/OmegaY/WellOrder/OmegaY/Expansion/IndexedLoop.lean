/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/IndexedLoop.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/IndexedLoop.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.LoopInvariant
import Mathlib.Data.List.Range

set_option backward.do.legacy false

/-! Indexed state invariants for the actual finite Except/forIn loop.
The index is exactly the next list entry, and every successful body yields
the next state. There is no extra fuel or alternate execution function. -/

namespace OmegaY.Expansion

theorem forIn_range'_indexed {State : Type} (start count : Nat) (initial : State)
    (body : Nat → State → Result (ForInStep State)) (P : Nat → State → Prop)
    (hInit : P start initial)
    (hStep : ∀ i, start ≤ i → i < start + count → ∀ state, P i state →
      ∃ next, body i state = .ok (.yield next) ∧ P (i + 1) next) :
    ∃ final, (forIn (List.range' start count) initial body : Result State) = .ok final ∧
      P (start + count) final := by
  induction count generalizing start initial with
  | zero => exact ⟨initial, rfl, by simpa only [Nat.add_zero] using hInit⟩
  | succ count ih =>
    obtain ⟨next, hNext, hNextP⟩ := hStep start le_rfl (by omega) initial hInit
    have hTailStep : ∀ i, start + 1 ≤ i → i < (start + 1) + count →
        ∀ state, P i state → ∃ next, body i state = .ok (.yield next) ∧ P (i + 1) next := by
      intro i hLower hUpper state hState
      exact hStep i (by omega) (by omega) state hState
    obtain ⟨final, hRun, hFinal⟩ := ih (start + 1) next hNextP hTailStep
    refine ⟨final, ?_, ?_⟩
    · rw [List.range'_succ, List.forIn_cons, hNext]
      exact hRun
    · have hEnd : (start + 1) + count = start + (count + 1) := by omega
      simpa only [hEnd] using hFinal

/-- The range used by copyBlock, starting at offset zero. -/
theorem forIn_range_indexed {State : Type} (count : Nat) (initial : State)
    (body : Nat → State → Result (ForInStep State)) (P : Nat → State → Prop)
    (hInit : P 0 initial)
    (hStep : ∀ i, i < count → ∀ state, P i state →
      ∃ next, body i state = .ok (.yield next) ∧ P (i + 1) next) :
    ∃ final, (forIn (List.range count) initial body : Result State) = .ok final ∧ P count final := by
  have h := forIn_range'_indexed 0 count initial body P hInit
    (fun i _ hi state hs => hStep i (by simpa only [Nat.zero_add] using hi) state hs)
  simpa only [← List.range_eq_range', Nat.zero_add] using h

end OmegaY.Expansion

#print axioms OmegaY.Expansion.forIn_range'_indexed
#print axioms OmegaY.Expansion.forIn_range_indexed
