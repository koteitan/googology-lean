/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/SuccessInvariant.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/SuccessInvariant.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.LoopInvariant

set_option backward.do.legacy false

/-! Soundness invariants for actual successful loops. A failing body is
allowed; no success premise is manufactured for an unreachable state. -/

namespace OmegaY.Expansion

theorem bind_success_witness {α β : Type} {action : Result α} {next : α → Result β} {result : β}
    (h : (action >>= next) = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error e => cases h
  | ok value => exact ⟨value, rfl, h⟩

theorem forIn_invariant_of_success {α β : Type} (xs : List α) (initial : β)
    (body : α → β → Result (ForInStep β)) (post : β → Prop) (hInit : post initial)
    (hBody : ∀ item ∈ xs, ∀ state, post state → ∀ step,
      body item state = .ok step → StepInvariant post step)
    {result : β} (hRun : (forIn xs initial body : Result β) = .ok result) : post result := by
  induction xs generalizing initial with
  | nil =>
    have he : initial = result := Except.ok.inj hRun
    exact he ▸ hInit
  | cons item rest ih =>
    rw [List.forIn_cons] at hRun
    obtain ⟨step, hStep, hAfter⟩ := bind_success_witness hRun
    have hPost := hBody item (by simp) initial hInit step hStep
    cases step with
    | done state =>
      have he : state = result := Except.ok.inj hAfter
      exact he ▸ hPost
    | yield state =>
      exact ih state hPost (fun item hi => hBody item (by simp [hi])) hAfter

end OmegaY.Expansion

#print axioms OmegaY.Expansion.forIn_invariant_of_success
