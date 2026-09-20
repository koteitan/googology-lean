/-!
# Well-foundedness, in general

Facts about `WellFounded` that do not mention expansion systems.  They are
stated here so that a notation system can use them without importing
`Googology.Core.Rewrite`.
-/

namespace Googology

variable {α : Type u} {r : α → α → Prop}

/-- A well-founded relation admits no infinite descending sequence. -/
theorem not_descending (h : WellFounded r) (f : Nat → α)
    (hf : ∀ n, r (f (n + 1)) (f n)) : False := by
  have key : ∀ a, Acc r a → ∀ n, f n ≠ a := by
    intro a ha
    induction ha with
    | intro x _ ih => intro n hn; exact ih (f (n + 1)) (hn ▸ hf n) (n + 1) rfl
  exact key (f 0) (h.apply (f 0)) 0 rfl

/-- An infinite descending sequence refutes well-foundedness. -/
theorem not_wellFounded_of_descending (f : Nat → α)
    (hf : ∀ n, r (f (n + 1)) (f n)) : ¬ WellFounded r :=
  fun h => not_descending h f hf

end Googology
