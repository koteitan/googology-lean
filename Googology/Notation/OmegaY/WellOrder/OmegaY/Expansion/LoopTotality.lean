/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/LoopTotality.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/LoopTotality.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.Build

set_option backward.do.legacy false

/-! Totality lemmas for the actual finite `Except` loops emitted by Lean's
`for` syntax.  No loop is replaced by a separate selection oracle. -/

namespace OmegaY.Expansion

def Succeeds {α : Type} (action : Result α) : Prop := ∃ value, action = .ok value

@[simp] theorem succeeds_ok {α : Type} (value : α) : Succeeds (.ok value : Result α) :=
  ⟨value, rfl⟩

theorem succeeds_pure {α : Type} (value : α) : Succeeds (pure value : Result α) :=
  ⟨value, rfl⟩

theorem succeeds_bind {α β : Type} {action : Result α} {next : α → Result β}
    (h : Succeeds action) (hn : ∀ value, Succeeds (next value)) :
    Succeeds (action >>= next) := by
  obtain ⟨value, hv⟩ := h
  rw [hv]
  exact hn value

theorem succeeds_forIn {α β : Type} (xs : List α) (initial : β)
    (body : α → β → Result (ForInStep β))
    (hbody : ∀ item ∈ xs, ∀ state, Succeeds (body item state)) :
    Succeeds (forIn xs initial body : Result β) := by
  induction xs generalizing initial with
  | nil => exact ⟨initial, rfl⟩
  | cons item rest ih =>
    obtain ⟨step, hs⟩ := hbody item (by simp) initial
    rw [List.forIn_cons, hs]
    cases step with
    | done state => exact ⟨state, rfl⟩
    | yield state =>
      exact ih state (fun item hi state => hbody item (by simp [hi]) state)

end OmegaY.Expansion

#print axioms OmegaY.Expansion.succeeds_forIn
