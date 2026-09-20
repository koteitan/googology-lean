/-!
# Extended Buchholz's psi: terms and their order

Maksudov's extension of Buchholz's collapsing function lets the subscript of
`ψ` be any ordinal the system itself names, instead of a numeral at most `ω`:

```
C_v^0(a)     = {b | b < Ω_v}
C_v^(n+1)(a) = {b + c, ψ_u(e) | u, b, c, e ∈ C_v^n(a) ∧ e < a}
C_v(a)       = ⋃_{n<ω} C_v^n(a)
ψ_v(a)       = min {g | g ∉ C_v(a)}
```

On the term side that means the subscript of `ψ` is itself a term.  A term is
a finite, weakly decreasing sum of principal terms `ψ_a(b)`, so it is
represented as a snoc-free list:

* `nil` is `0`;
* `cons a b t` is `ψ_a(b) + t`.

One inductive type, three recursive arguments — no mutual or nested induction,
so every recursion below is structural.
-/

namespace Googology.Notation.ExBuchholz

/-- A term of the extended Buchholz notation system.  `nil` is `0`, and
`cons a b t` is `ψ_a(b) + t`. -/
inductive Term where
  /-- The term `0`. -/
  | nil : Term
  /-- `cons a b t` is the term `ψ_a(b) + t`. -/
  | cons : Term → Term → Term → Term
  deriving DecidableEq, Repr

namespace Term

/-- The principal term `ψ_a(b)`, standing alone. -/
abbrev psi (a b : Term) : Term := cons a b nil

/-- Comparison of terms: the dictionary order on the list of principal terms,
with a proper prefix counting as smaller, and principal terms compared by
`(subscript, argument)` lexicographically.  This is Buchholz's `(<1)`–`(<3)`
with the subscript generalised from a numeral to a term. -/
def cmp : Term → Term → Ordering
  | nil, nil => .eq
  | nil, cons _ _ _ => .lt
  | cons _ _ _, nil => .gt
  | cons a b t, cons c d u => (cmp a c).then ((cmp b d).then (cmp t u))

/-- Strict order on terms. -/
def lt (x y : Term) : Prop := cmp x y = .lt

/-- Non-strict order on terms. -/
def le (x y : Term) : Prop := cmp x y ≠ .gt

instance : LT Term := ⟨lt⟩
instance : LE Term := ⟨le⟩

instance (x y : Term) : Decidable (x < y) := by
  show Decidable (cmp x y = .lt); infer_instance

instance (x y : Term) : Decidable (x ≤ y) := by
  show Decidable (cmp x y ≠ .gt); infer_instance

@[simp] theorem lt_def (x y : Term) : (x < y) = (cmp x y = .lt) := rfl
@[simp] theorem le_def (x y : Term) : (x ≤ y) = (cmp x y ≠ .gt) := rfl

/-! ### Basic facts about `cmp` -/

@[simp] theorem cmp_self (x : Term) : cmp x x = .eq := by
  induction x with
  | nil => rfl
  | cons a b t ha hb ht => simp [cmp, ha, hb, ht, Ordering.then]

theorem cmp_swap (x y : Term) : (cmp x y).swap = cmp y x := by
  induction x generalizing y with
  | nil => cases y <;> rfl
  | cons a b t ha hb ht =>
    cases y with
    | nil => rfl
    | cons c d u =>
      simp only [cmp]
      rw [← ha c, ← hb d, ← ht u]
      cases cmp a c <;> cases cmp b d <;> cases cmp t u <;> rfl

/-- `cmp` splits a `cons`/`cons` comparison into its three components. -/
theorem cmp_cons_eq_eq {a b t c d u : Term}
    (h : cmp (cons a b t) (cons c d u) = .eq) :
    cmp a c = .eq ∧ cmp b d = .eq ∧ cmp t u = .eq := by
  revert h
  simp only [cmp]
  generalize cmp a c = x
  generalize cmp b d = y
  generalize cmp t u = z
  cases x <;> cases y <;> cases z <;> simp

theorem cmp_eq_iff {x y : Term} : cmp x y = .eq ↔ x = y := by
  constructor
  · induction x generalizing y with
    | nil =>
      cases y with
      | nil => intro _; rfl
      | cons _ _ _ => intro h; cases h
    | cons a b t ha hb ht =>
      cases y with
      | nil => intro h; cases h
      | cons c d u =>
        intro h
        obtain ⟨h1, h2, h3⟩ := cmp_cons_eq_eq h
        have e1 := ha h1
        have e2 := hb h2
        have e3 := ht h3
        subst e1; subst e2; subst e3; rfl
  · rintro rfl; exact cmp_self x

end Term
end Googology.Notation.ExBuchholz
