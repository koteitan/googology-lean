import Googology.Core
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
first.

`[ ]` is the harder half: its recursion is not structural.  Three of its calls
shrink the term, one shrinks the index, and one reads the subscript out of
`dom X₂` — which `size_dom_le` keeps inside `X`.  The measure is therefore the
pair `(size X, size Y)`, ordered lexicographically.  The call that keeps `X`
fixed is guarded by `Y` being a numeral, and a numeral's predecessor is
structurally smaller, so that one decreases in the index.
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

/-! ## The fundamental sequence -/

/-- The subscript of a principal term; `0` for `0`. -/
def subOf : Term → Term
  | nil => nil
  | cons Z _ _ => Z

theorem size_subOf_le (X : Term) : size (subOf X) ≤ size X := by
  cases X <;> simp [subOf, size_cons] <;> omega

/-- Is the term a numeral `1 + ⋯ + 1`? -/
def isNum : Term → Bool
  | nil => true
  | cons nil nil t => isNum t
  | _ => false

/-- The value of a numeral. -/
def numVal : Term → Nat
  | nil => 0
  | cons nil nil t => numVal t + 1
  | _ => 0

/-- One less, for a numeral. -/
def numPred : Term → Term
  | cons nil nil t => t
  | _ => nil

theorem size_numPred_lt {X : Term} (h : X ≠ nil) : size (numPred X) < size X := by
  cases X with
  | nil => exact absurd rfl h
  | cons a b t =>
    cases a with
    | nil =>
      cases b with
      | nil => simp [numPred, size_cons]
      | cons _ _ _ => simp [numPred, size_cons]
    | cons _ _ _ => simp [numPred, size_cons]

/-- `n` copies of the principal term `ψ_A(B)`, as a sum. -/
def repeatPrin (A B : Term) : Nat → Term
  | 0 => nil
  | n + 1 => cons A B (repeatPrin A B n)

set_option linter.unusedVariables false in
/-- The fundamental sequence `X[Y]`, following the reference. -/
def fs : Term → Term → Term
  | nil, _ => nil
  | cons X₁ X₂ (cons c d u), Y => cons X₁ X₂ (fs (cons c d u) Y)
  | cons X₁ X₂ nil, Y =>
      if dom X₂ = nil then
        (if dom X₁ = nil then nil
         else if dom X₁ = t1 then Y
         else cons (fs X₁ Y) nil nil)
      else if dom X₂ = t1 then
        (if isNum Y then repeatPrin X₁ (fs X₂ nil) (numVal Y) else nil)
      else if dom X₂ = tw then
        cons X₁ (fs X₂ Y) nil
      else if dom X₂ < cons X₁ X₂ nil then
        cons X₁ (fs X₂ Y) nil
      else
        if h : Y ≠ nil ∧ isNum Y = true then
          (match fs (cons X₁ X₂ nil) (numPred Y) with
           | cons x₁' Γ nil =>
               if x₁' = X₁ then
                 cons X₁ (fs X₂ (cons (fs (subOf (dom X₂)) nil) Γ nil)) nil
               else cons X₁ (fs X₂ (cons (fs (subOf (dom X₂)) nil) nil nil)) nil
           | _ => cons X₁ (fs X₂ (cons (fs (subOf (dom X₂)) nil) nil nil)) nil)
        else cons X₁ (fs X₂ (cons (fs (subOf (dom X₂)) nil) nil nil)) nil
termination_by X Y => (size X, size Y)
decreasing_by
  all_goals first
    | exact Prod.Lex.left _ _ (by simp only [size_cons]; omega)
    | exact Prod.Lex.left _ _ (by
        have h1 := size_subOf_le (dom X₂)
        have h2 := size_dom_le X₂
        simp only [size_cons]
        omega)
    | exact Prod.Lex.right _ (size_numPred_lt h.1)

#guard numVal t2 = 2
#guard isNum t2
#guard !isNum tw
#guard numPred t2 = t1
#guard repeatPrin nil nil 2 = t2

/-! ### Fundamental sequences, checked against known values -/

/-- `3` as a term. -/
abbrev t3 : Term := cons nil nil t2
/-- `ε₀ = ψ_0(Ω)`. -/
abbrev te : Term := psi nil tW
/-- `ω^ω = ψ_0(ω)`. -/
abbrev tww : Term := psi nil tw

#guard fs t0 t3 = t0            -- 0[n] = 0
#guard fs t1 t0 = t0            -- 1[0] = 0
#guard fs t2 t0 = t1            -- 2[0] = 1
#guard fs t3 t0 = t2            -- 3[0] = 2
#guard fs tw t0 = t0            -- ω[0] = 0
#guard fs tw t1 = t1            -- ω[1] = 1
#guard fs tw t2 = t2            -- ω[2] = 2
#guard fs tw t3 = t3            -- ω[3] = 3
#guard fs tW t2 = t2            -- Ω[Y] = Y
#guard fs tW tw = tw
#guard fs tww t2 = psi nil t2   -- (ω^ω)[2] = ω^2
#guard fs te t0 = tw            -- ε₀[0] = ω
#guard fs te t1 = tww           -- ε₀[1] = ω^ω
#guard fs te t2 = psi nil tww   -- ε₀[2] = ω^(ω^ω)

/-! ### Sanity checks against the reference -/

#guard dom t0 = t0                    -- 0
#guard dom t1 = t1                    -- 1 is a successor
#guard dom t2 = t1                    -- so is 2
#guard dom tw = tw                    -- ω is its own index
#guard dom tW = tW                    -- Ω is indexed by the terms below it
#guard dom (psi nil tW) = tw          -- ε₀ has cofinality ω
#guard dom (psi nil (psi nil tW)) = tw

/-! ## As an expansion system -/

/-- The numeral `n`, as a term. -/
def numeral (n : Nat) : Term := repeatPrin nil nil n

#guard numeral 0 = t0
#guard numeral 3 = t3

/-- Extended Buchholz terms as an expansion system: one step is the
fundamental sequence at the numeral `n`.

Well-foundedness is **not** proved.  It needs two theorems that are not here
yet: that `OT` is closed under `[ ]`, and that `X[n̲] < X` for a standard `X`
other than `0`.  Granting those, restricting the state to `OT` and composing
`valHom` with `OrdHom.wf` gives it.  The `#guard` lines above are the only
evidence so far. -/
def exb : Rewrite where
  State := Term
  step := fun X n => fs X (numeral n)
  halted := fun X => X = nil

example : Prop := exb.Terminates

end Googology.Notation.ExBuchholz.Term
