/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/LoopCoverage.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/LoopCoverage.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.LoopInvariant

set_option backward.do.legacy false

/-! Visiting a designated item in an actual, non-breaking finite loop. -/

namespace OmegaY.Expansion

theorem forIn_yield_coverage {α β : Type} (xs : List α) (initial : β)
    (body : α → β → Result (ForInStep β))
    (invariant present : β → Prop) (event : α → Prop) (hinit : invariant initial)
    (hbody : ∀ item ∈ xs, ∀ state, invariant state →
      ∃ next, body item state = .ok (.yield next) ∧ invariant next ∧
        (present state → present next) ∧ (event item → present next)) :
    ∃ result, (forIn xs initial body : Result β) = .ok result ∧ invariant result ∧
      (present initial → present result) ∧ ((∃ item ∈ xs, event item) → present result) := by
  induction xs generalizing initial with
  | nil => exact ⟨initial, rfl, hinit, id, by simp⟩
  | cons item rest ih =>
    obtain ⟨next, hn, hi, hp, he⟩ := hbody item (by simp) initial hinit
    obtain ⟨result, hr, hinv, hkeep, hhit⟩ := ih next hi
      (fun a ha state hs => hbody a (by simp [ha]) state hs)
    refine ⟨result, ?_, hinv, fun h => hkeep (hp h), ?_⟩
    · rw [List.forIn_cons, hn]
      exact hr
    · rintro ⟨a, ha, hea⟩
      rcases List.mem_cons.mp ha with heq | hrest
      · subst a
        exact hkeep (he hea)
      · exact hhit ⟨a, hrest, hea⟩

theorem returns_forIn_hit {α β : Type} (xs : List α) (initial : β)
    (body : α → β → Result (ForInStep β))
    (invariant present : β → Prop) (event : α → Prop) (hinit : invariant initial)
    (hhit : ∃ item ∈ xs, event item)
    (hbody : ∀ item ∈ xs, ∀ state, invariant state →
      ∃ next, body item state = .ok (.yield next) ∧ invariant next ∧
        (present state → present next) ∧ (event item → present next)) :
    Returns (forIn xs initial body : Result β) (fun result => invariant result ∧ present result) := by
  obtain ⟨result, hr, hi, _, hh⟩ :=
    forIn_yield_coverage xs initial body invariant present event hinit hbody
  exact ⟨result, hr, hi, hh hhit⟩

/-- Nest a complete non-breaking loop inside a surrounding loop body. -/
theorem forIn_yield_cover {α β : Type} (xs : List α) (initial : β)
    (body : α → β → Result (ForInStep β))
    (invariant present : β → Prop) (event : α → Prop) (obligation : Prop)
    (hinit : invariant initial) (hcover : obligation → ∃ item ∈ xs, event item)
    (hbody : ∀ item ∈ xs, ∀ state, invariant state →
      ∃ next, body item state = .ok (.yield next) ∧ invariant next ∧
        (present state → present next) ∧ (event item → present next)) :
    ∃ result,
      (do let output ← forIn xs initial body; pure (.yield output) : Result (ForInStep β)) =
        .ok (.yield result) ∧ invariant result ∧
      (present initial → present result) ∧ (obligation → present result) := by
  obtain ⟨result, hr, hi, hp, hh⟩ :=
    forIn_yield_coverage xs initial body invariant present event hinit hbody
  refine ⟨result, ?_, hi, hp, fun ho => hh (hcover ho)⟩
  rw [hr]
  rfl

end OmegaY.Expansion

#print axioms OmegaY.Expansion.forIn_yield_coverage
