import Googology.Notation.InaccPsi.Facts

/-!
# Terms, their values, the comparison, and normal forms

```
t ::= 0 | I_n | I_ω | t + t | φ(t, t) | Ω_t | ψ^S_s(t) | ψ^I_n(t)
```

`ψ^S_s(a)` denotes `ψ_{Ω_{s+1}}(a)` and `ψ^I_n(a)` denotes `ψ_{I_n}(a)`.

* `Term.val S t` is the ordinal a term denotes, relative to an `InaccSeq S`.
* `Term.cmp` compares two terms by recursion on the sum of their sizes (section 4 of the
  README). It does not look at `S`: it is a syntactic procedure.
* `Term.KLt μ t α` says that every member of the finite set `K_μ(t)` is below `α`
  (Pohlers's Definition 3.4.4.2, in the weaker form "below `μ`, or checked").
* `Term.NF` is the normal form.
-/

namespace Googology.Notation.InaccPsi

open Ordinal

universe u

/-- Terms of the notation system. -/
inductive Term : Type
  | zero
  | inacc (n : ℕ)
  | inaccW
  | add (a b : Term)
  | phi (a b : Term)
  | om (a : Term)
  /-- `ψ^S_s(a) = ψ_{Ω_{s+1}}(a)` -/
  | psiS (s a : Term)
  /-- `ψ^I_n(a) = ψ_{I_n}(a)` -/
  | psiI (n : ℕ) (a : Term)
  deriving DecidableEq, Repr

namespace Term

/-- The number of constructors. -/
def size : Term → ℕ
  | zero => 1
  | inacc _ => 1
  | inaccW => 1
  | add a b => a.size + b.size + 1
  | phi a b => a.size + b.size + 1
  | om a => a.size + 1
  | psiS s a => s.size + a.size + 1
  | psiI _ a => a.size + 1

theorem size_pos (t : Term) : 0 < t.size := by
  cases t <;> simp [size]

/-- The value of a term. -/
noncomputable def val (S : InaccSeq.{u}) : Term → Ordinal.{u}
  | zero => 0
  | inacc n => S.I n
  | inaccW => S.Iw
  | add a b => val S a + val S b
  | phi a b => veblen (val S a) (val S b)
  | om a => Om (val S a)
  | psiS s a => S.psi (val S a) (Om (val S s + 1))
  | psiI n a => S.psi (val S a) (S.I n)

/-! ## Kinds -/

/-- Fixed-point terms `F`: `I_n`, `I_ω`, `ψ^I_n(a)`. -/
def isF : Term → Bool
  | inacc _ => true
  | inaccW => true
  | psiI _ _ => true
  | _ => false

/-- Strongly critical terms: `I_n`, `I_ω`, `Ω_a`, `ψ^S_s(a)`, `ψ^I_n(a)`. -/
def isSC : Term → Bool
  | inacc _ => true
  | inaccW => true
  | om _ => true
  | psiS _ _ => true
  | psiI _ _ => true
  | _ => false

/-- Principal terms: strongly critical terms and `φ(a, b)`. -/
def isPrin : Term → Bool
  | phi _ _ => true
  | t => t.isSC

/-- Cardinal terms `K`: `F` and `Ω_a`. -/
def isK : Term → Bool
  | om _ => true
  | t => t.isF

/-- The term for `Ω_s`: `0` if `s = 0`, `s` if `s ∈ F`, and `Ω_s` otherwise. -/
def cardT (s : Term) : Term :=
  if s = zero then zero else if s.isF then s else om s

theorem size_cardT_le (s : Term) : (cardT s).size ≤ s.size + 1 := by
  unfold cardT
  split_ifs <;> simp [size]

/-- The first summand. -/
def head : Term → Term
  | add a _ => a
  | t => t

/-! ## The comparison -/

/-- The comparison of terms. It is exact on values wherever that needs no normal form;
the remaining clauses assume normal forms (see `Correct.lean`). -/
def cmp : Term → Term → Ordering
  -- zero
  | zero, zero => .eq
  | zero, _ => .lt
  | _, zero => .gt
  -- sums
  | add a b, add c d =>
      match cmp a c with
      | .eq => cmp b d
      | o => o
  | add a _, t =>
      match cmp a t with
      | .lt => .lt
      | _ => .gt
  | t, add c _ =>
      match cmp t c with
      | .gt => .gt
      | _ => .lt
  -- Veblen terms
  | phi a b, phi c d =>
      match cmp a c with
      | .lt => cmp b (phi c d)
      | .eq => cmp b d
      | .gt => cmp (phi a b) d
  -- against a strongly critical `γ`: `φ(a, b) < γ` iff `a, b < γ`; `φ(a, γ) = γ` for
  -- `a < γ`; `φ(γ, 0) = γ`; `φ(γ, b) > γ` for `b > 0`
  | phi a b, t =>
      match cmp a t with
      | .lt => cmp b t
      | .eq => cmp b zero
      | .gt => .gt
  | t, phi c d =>
      match cmp t c with
      | .gt => cmp t d
      | .eq => cmp zero d
      | .lt => .lt
  -- inaccessibles
  | inacc n, inacc m => compare n m
  | inacc _, inaccW => .lt
  | inaccW, inacc _ => .gt
  | inaccW, inaccW => .eq
  | psiI n a, psiI m b =>
      match compare n m with
      | .eq => cmp a b
      | o => o
  | psiI n _, inacc m => if n ≤ m then .lt else .gt
  | inacc m, psiI n _ => if n ≤ m then .gt else .lt
  | psiI _ _, inaccW => .lt
  | inaccW, psiI _ _ => .gt
  -- `Ω_a` against `Ω_c` and against fixed points
  | om a, om c => cmp a c
  | om a, inacc m => cmp a (inacc m)
  | om a, inaccW => cmp a inaccW
  | om a, psiI m b => cmp a (psiI m b)
  | inacc m, om c => cmp (inacc m) c
  | inaccW, om c => cmp inaccW c
  | psiI m b, om c => cmp (psiI m b) c
  -- `ψ^S`
  | psiS s a, psiS t b =>
      match cmp s t with
      | .eq => cmp a b
      | o => o
  | psiS s a', k =>
      match cmp (cardT s) k with
      | .lt => .lt
      | _ => .gt
  | k, psiS s a' =>
      match cmp k (cardT s) with
      | .gt => .gt
      | _ => .lt
termination_by a b => a.size + b.size
decreasing_by
  all_goals simp_wf
  all_goals first
    | (simp only [size]; omega)
    | (simp only [size]; grind [size_cardT_le, size_pos])

/-! ## `K`-sets and normal forms -/

/-- `KLt μ t α`: every member of `K_μ(t)` is `< α`. A strongly critical subterm below `μ`
contributes nothing; a collapse `ψ_π(b)` not below `μ` contributes `b` and the sets of
its parts. -/
def KLt (μ : Term) : Term → Term → Prop
  | zero, _ => True
  | inacc _, _ => True
  | inaccW, _ => True
  | add a b, α => KLt μ a α ∧ KLt μ b α
  | phi a b, α => KLt μ a α ∧ KLt μ b α
  | om b, α => cmp (om b) μ = .lt ∨ KLt μ b α
  | psiS s b, α => cmp (psiS s b) μ = .lt ∨ (cmp b α = .lt ∧ KLt μ s α ∧ KLt μ b α)
  | psiI n b, α => cmp (psiI n b) μ = .lt ∨ (cmp b α = .lt ∧ KLt μ b α)

/-- Normal forms. -/
def NF : Term → Prop
  | zero => True
  | inacc _ => True
  | inaccW => True
  | add a b => NF a ∧ NF b ∧ a.isPrin ∧ b ≠ zero ∧ cmp (head b) a ≠ .gt
  | phi a b => NF a ∧ NF b ∧ cmp a (phi a b) = .lt ∧ cmp b (phi a b) = .lt
  | om a => NF a ∧ a ≠ zero ∧ a.isF = false
  | psiS s a => NF s ∧ NF a ∧ KLt (cardT s) a a
  | psiI n a => NF a ∧ KLt (psiI n a) a a

end Term

end Googology.Notation.InaccPsi
