import Googology.Notation.ExBuchholz.Sum

/-!
# Fundamental sequences

Following p進大好きbot's article, the system carries two total recursive maps

```
dom : T → T          the shape of the limit a term is
[ ] : T × T → T      the fundamental sequence
```

`dom X` is `0` for zero, `X` itself when the sequence is indexed by the terms
below `X`, `1` for a successor, `ω` for an `ω`-limit, and otherwise the term
whose values index the sequence.

`dom` never calls `[ ]`, so it is an ordinary structural recursion and comes
first.  `[ ]` is the harder half: its recursion is not structural.
-/

namespace Googology.Notation.ExBuchholz.Term

/-- `dom X` names the shape of the limit `X` is: `0` for a zero, `X` itself for
a successor-like collapse, `1` for a successor, `ω` for an `ω`-limit, and
otherwise the term whose values index the fundamental sequence.

It does not call `[ ]`, so it is an ordinary structural recursion. -/
def dom : Term → Term
  | nil => nil
  | cons a b nil =>
      match dom b with
      | nil =>
          match dom a with
          | nil => cons a b nil
          | cons nil nil nil => cons a b nil
          | da => da
      | cons nil nil nil => tw
      | cons nil (cons nil nil nil) nil => tw
      | db => if db < cons a b nil then db else tw
  | cons _ _ t => dom t

@[simp] theorem dom_nil : dom nil = nil := rfl

@[simp] theorem size_tw : size tw = 2 := rfl

set_option linter.unusedSimpArgs false in
/-- `dom` never grows a term. -/
theorem size_dom_le : ∀ X : Term, size (dom X) ≤ size X := by
  intro X
  induction X with
  | nil => simp [dom]
  | cons a b t iha ihb iht =>
    cases t with
    | cons c d u =>
      have h : dom (cons a b (cons c d u)) = dom (cons c d u) := rfl
      rw [h]; simp only [size_cons] at iht ⊢; omega
    | nil =>
      cases b with
      | nil =>
        rw [dom]
        simp only [dom]
        split <;> simp only [size_cons] <;> omega
      | cons p q r =>
        simp only [size_cons] at ihb
        rw [dom]
        split
        · split <;> simp only [size_cons] <;> omega
        · simp only [size_tw, size_cons, size_nil]; omega
        · simp only [size_tw, size_cons, size_nil]; omega
        · split <;> simp only [size_tw, size_cons, size_nil] <;> omega

/-! ### Sanity checks against the reference -/

#guard dom t0 = t0                    -- 0
#guard dom t1 = t1                    -- 1 is a successor
#guard dom t2 = t1                    -- so is 2
#guard dom tw = tw                    -- ω is its own index
#guard dom tW = tW                    -- Ω is indexed by the terms below it
#guard dom (psi nil tW) = tw          -- ε₀ has cofinality ω
#guard dom (psi nil (psi nil tW)) = tw

end Googology.Notation.ExBuchholz.Term
