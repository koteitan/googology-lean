import Googology.Core.WF
import Googology.Notation.ExBuchholz.Std

/-!
# Well-foundedness

The order on *all* terms is **not** well founded.  Collapsing repeatedly,

```
Ω > ψ_0(Ω) > ψ_0(ψ_0(Ω)) > ψ_0(ψ_0(ψ_0(Ω))) > ⋯
```

descends forever, because `cmp` compares the subscripts first and `0 < ψ_0(0)`.
That is exactly what the standard-form condition rules out: the chain leaves
`OT` at its third term, since `Ω` is not below `ψ_0(Ω)`.

So the statement to aim at is well-foundedness of `OTLt`, the order restricted
to standard forms.
-/

namespace Googology.Notation.ExBuchholz.Term

/-! ## `0` is the least term -/

theorem not_lt_nil (x : Term) : ¬ x < nil := by
  cases x <;> simp [lt_def, cmp]

theorem nil_le (x : Term) : nil ≤ x := by
  cases x <;> simp [le_def, cmp]

/-! ## The unrestricted order is not well founded -/

/-- `collapse n` is `ψ_0` applied `n` times to `Ω`. -/
def collapse : Nat → Term
  | 0 => tW
  | n + 1 => psi nil (collapse n)

theorem collapse_lt (n : Nat) : collapse (n + 1) < collapse n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show cmp (psi nil (collapse (n + 1))) (psi nil (collapse n)) = .lt
    show (cmp nil nil).then ((cmp (collapse (n + 1)) (collapse n)).then
      (cmp nil nil)) = .lt
    rw [cmp_self, ih]
    rfl

/-- The order on all terms is not well founded.  This is why standard forms
are needed at all. -/
theorem not_wellFounded_lt : ¬ WellFounded (· < · : Term → Term → Prop) :=
  Googology.not_wellFounded_of_descending collapse collapse_lt

-- The descending chain leaves `OT` immediately: `ψ_0(Ω)` is standard,
-- `ψ_0(ψ_0(Ω))` is not.
#guard isOT (collapse 1)
#guard !isOT (collapse 2)

/-! ## The term order is a lexicographic product -/

/-- The term order is the lexicographic product of the order on the leading
principal term and the order on the tail.  Every later step reads the order
through this. -/
theorem cmp_cons_cons' (a b t c d u : Term) :
    cmp (cons a b t) (cons c d u) = (cmp (psi a b) (psi c d)).then (cmp t u) := by
  show (cmp a c).then ((cmp b d).then (cmp t u)) =
    ((cmp a c).then ((cmp b d).then (cmp nil nil))).then (cmp t u)
  rw [cmp_self]
  generalize cmp a c = x
  generalize cmp b d = y
  generalize cmp t u = z
  cases x <;> cases y <;> cases z <;> rfl

/-! ## Standard form is inherited by the parts -/

/-- Standard form is inherited by the leading principal term. -/
theorem OT_head {a b t : Term} (h : OT (cons a b t)) : OT (psi a b) := by
  simp only [OT, isOT, descHead, head?, Bool.and_eq_true] at h ⊢
  exact ⟨⟨h.1.1, trivial⟩, trivial⟩

/-- Standard form is inherited by the tail. -/
theorem OT_tail {a b t : Term} (h : OT (cons a b t)) : OT t := by
  simp only [OT, isOT, Bool.and_eq_true] at h
  exact h.1.2

/-- In a standard form the principal terms do not increase. -/
theorem OT_tail_head_le {a b c d u : Term} (h : OT (cons a b (cons c d u))) :
    psi c d ≤ psi a b := by
  simp only [OT, isOT, descHead, head?, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-! ## The order restricted to standard forms -/

/-- The order restricted to standard forms.  Well-foundedness of this is the
goal; it is not proved yet. -/
def OTLt (x y : Term) : Prop := OT x ∧ OT y ∧ x < y

theorem OTLt_lt {x y : Term} (h : OTLt x y) : x < y := h.2.2

/-- `0` is accessible, vacuously. -/
theorem acc_nil : Acc OTLt nil :=
  ⟨nil, fun _ h => absurd h.2.2 (not_lt_nil _)⟩

/-! ## What remains

`WellFounded OTLt` splits in two, along `cmp_cons_cons'`.

**(1) Principal terms.**  `∀ a b, OT (ψ_a(b)) → Acc OTLt (ψ_a(b))`.  This is
the collapsing argument and carries all the content.  Buchholz proves the
unextended case syntactically through the sets `W_u` and the Bachmann
property, which first needs fundamental sequences; the alternative is to
evaluate into the ordinals and pull well-foundedness back along an `OrdHom`.

**(2) Sums.**  Granting (1), every standard form is accessible.  Structural
induction on the term reduces this to

```
Acc OTLt (ψ_a(b)) → Acc OTLt r → OT (cons a b r) → Acc OTLt (cons a b r)
```

which is accessibility for a lexicographic product.  The nested induction does
not close directly, because a term below `cons a b r` with a *smaller* head
carries an unrelated tail.  `OT_tail_head_le` is what repairs it: in a
standard form every principal term is at most the leading one, so writing a
standard form as `q ^ k` followed by a term whose head is strictly below `q`
presents the order as the lexicographic product of `Nat` with the terms below
`q`.  The leading-block count is monotone — more copies of `q` in front makes
a term larger — so the induction runs on that count.
-/

end Googology.Notation.ExBuchholz.Term
