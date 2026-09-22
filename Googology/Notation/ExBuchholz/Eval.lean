import Googology.Notation.ExBuchholz.Ord
import Googology.Notation.ExBuchholz.Sum

/-!
# The evaluation of a term into the ordinals

A term denotes an ordinal in the obvious way: `ψ_a(b)` denotes
`ψ_{val a}(val b)` and a sum denotes the ordinal sum.  Terms are evaluated in
`Ordinal.{0}`; the notation system names countable ordinals and the
uncountables that bound them, all of which live there.

The theorem this file is aimed at is

```
x < y → OT x → OT y → val x < val y
```

which is the correctness of the notation system, and which — pulled back along
`OrdHom.wf` — discharges the hypothesis of `wellFounded_OTLt`.

It is not proved yet, and the reason is worth recording. Weak monotonicity of
`ψ_v` in the argument (`Ord.psi_mono`) is not enough: `ψ_v(a) = ψ_v(a+1)` does
happen, exactly when `a` is not itself reachable inside `C_v(a)`. Strictness is
what the standard-form condition buys, and turning it into a theorem needs, in
order:

1. `x ∈ C_v(a)` with `x` small enough implies `x < ψ_v(a)` — the closure is
   downward closed below the next uncountable;
2. hence `ψ_v(a)` is additively principal;
3. the standard-form condition `G_a(b) < b` gives `val b ∈ C_{val a}(val b)`,
   so `ψ_{val a}` is *strictly* increasing at the arguments that standard forms
   actually use;
4. the comparison of terms then transfers to the comparison of values, by the
   lexicographic decomposition `cmp_cons_cons'` and step 2 for the sums.
-/

namespace Googology.Notation.ExBuchholz

open Ordinal

/-- The ordinal denoted by a term: `0` for `nil`, and `ψ_{val a}(val b) + val t`
for `ψ_a(b) + t`. -/
noncomputable def Term.val : Term → Ordinal.{0}
  | .nil => 0
  | .cons a b t => Ord.psi (Term.val b) (Term.val a) + Term.val t

namespace Term

@[simp] theorem val_nil : val nil = 0 := rfl

@[simp] theorem val_cons (a b t : Term) :
    val (cons a b t) = Ord.psi (val b) (val a) + val t := rfl

theorem val_psi (a b : Term) : val (psi a b) = Ord.psi (val b) (val a) := by
  simp [psi]

/-- A nonzero term has a nonzero value. -/
theorem val_pos {x : Term} (h : x ≠ nil) : 0 < val x := by
  cases x with
  | nil => exact absurd rfl h
  | cons a b t =>
    rw [val_cons]
    exact lt_of_lt_of_le (Ord.psi_pos _ _) (le_self_add)

theorem val_eq_zero_iff {x : Term} : val x = 0 ↔ x = nil := by
  constructor
  · intro h
    by_contra hx
    exact absurd h (val_pos hx).ne'
  · rintro rfl; rfl

end Term
end Googology.Notation.ExBuchholz
