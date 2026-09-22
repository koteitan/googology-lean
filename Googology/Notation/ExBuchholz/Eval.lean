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
   actually use.  Half of this is below: `Term.val_mem_CSet` says the
   *subscript* is always available, because a term never names a fixed point of
   `v ↦ ω_v`.  What is left is the *argument*, which is where `G` is read;
4. the comparison of terms then transfers to the comparison of values, by the
   lexicographic decomposition `cmp_cons_cons'` and step 2 for the sums.
-/

namespace Googology.Notation.ExBuchholz

open Ordinal Cardinal

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

/-! ## Term values are never omega fixed points -/

/-- The first fixed point of `v ↦ ω_v`.  Every term names an ordinal below it,
which is what keeps `Ω_{val a}` strictly above `val a`. -/
noncomputable def Lam : Ordinal.{0} := nfp omega 0

theorem omega_Lam : ω_ Lam = Lam := nfp_fp isNormal_omega 0

theorem omega0_le_Lam : ω ≤ Lam := by
  rw [← omega_Lam]; exact omega0_le_omega Lam

theorem Lam_pos : 0 < Lam := lt_of_lt_of_le omega0_pos omega0_le_Lam

theorem omega_lt_Lam {x : Ordinal} (h : x < Lam) : ω_ x < Lam := by
  conv_rhs => rw [← omega_Lam]
  exact omega_lt_omega.2 h

theorem lt_Lam_iff_card {x : Ordinal} : x < Lam ↔ x.card < ℵ_ Lam := by
  conv_lhs => rw [← omega_Lam]
  rw [← Ordinal.card_omega Lam]
  exact ((isInitial_omega Lam).card_lt_card).symm

theorem add_lt_Lam {x y : Ordinal} (hx : x < Lam) (hy : y < Lam) : x + y < Lam := by
  rw [lt_Lam_iff_card] at hx hy ⊢
  rw [Ordinal.card_add]
  exact Cardinal.add_lt_of_lt (aleph0_le_aleph Lam) hx hy

theorem isSuccLimit_Lam : Order.IsSuccLimit Lam := omega_Lam ▸ isSuccLimit_omega Lam

/-- Every term names an ordinal below the first omega fixed point. -/
theorem Term.val_lt_Lam (t : Term) : t.val < Lam := by
  induction t with
  | nil => exact Lam_pos
  | cons c d r ihc _ ihr =>
    rw [Term.val_cons]
    refine add_lt_Lam ?_ ihr
    have h1 : c.val + 1 < Lam := by
      rw [← Order.succ_eq_add_one]
      exact isSuccLimit_Lam.succ_lt ihc
    have h2 : ω_ (c.val + 1) < Lam := omega_lt_Lam h1
    have h3 : Ord.Omega (c.val + 1) = ω_ (c.val + 1) :=
      Ord.Omega_of_ne_zero (Ord.add_one_ne_zero_ord c.val)
    have h4 : Ord.psi d.val c.val < Ord.Omega (c.val + 1) :=
      Ord.psi_lt_Omega_succ d.val c.val
    rw [h3] at h4
    exact h4.trans h2

/-- Hence `val a` is strictly below `Ω_{val a}`, so it sits in every closure at
subscript `val a`. -/
theorem Term.val_lt_Omega_val (t : Term) : t.val < Ord.Omega t.val := by
  by_cases h : t.val = 0
  · rw [h, Ord.Omega_zero]; exact zero_lt_one
  · rw [Ord.Omega_of_ne_zero h]
    by_contra hcon
    have hfp : ω_ t.val ≤ t.val := not_lt.mp hcon
    have : Lam ≤ t.val := nfp_le_fp (Ordinal.omega.monotone) bot_le hfp
    exact absurd (t.val_lt_Lam) (not_lt.mpr this)

theorem Term.val_mem_CSet (t : Term) (b : Ordinal) : t.val ∈ Ord.CSet t.val b :=
  Ord.Clos.small t.val_lt_Omega_val

end Googology.Notation.ExBuchholz
