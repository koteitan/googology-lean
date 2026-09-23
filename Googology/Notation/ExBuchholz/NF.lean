import Googology.Notation.ExBuchholz.Eval
import Googology.Notation.ExBuchholz.Opow

/-!
# The normal form theorem, on the ordinal side

`Onto.lean` proves that every member of `C_0(Λ)` is the value of a standard
form.  The obstacle is the collapse clause: `ψ_u(e)` is in the closure for
every `e` in it, but the standard form of `ψ_u(e)` needs an argument that lies
in its own closure `C_u(·)`, and that argument is in general **larger** than
`e` — `ψ_0(ε₀) = ψ_0(Ω)`, and the standard form uses `Ω`.  So the argument has
to be moved up, and the question is whether the new argument is still named by
the system.

The argument that works is the least member of `C_u(e)` at or above `e`:

```
M_R(x) = min (R ∩ [x, ∞))      where R = C_c(a)
```

`CSet_M_subset` says `C_u(M(e)) ⊆ C_u(e)`, so `ψ_u(M(e)) = ψ_u(e)`, and
`M_mem_self` says `M(e)` lies in its own closure.  What is left is to show that
`M` does not leave a set `S` the argument started in, and this file does it
for any `S` closed under `+`, `Ω_·` and the collapses below `a`.

The proof reads `x` through its Cantor normal form.  `Comp g x` says `ω^g` is
one of its principal summands.  `M_mem_of_comp` reduces `M(x)` to `M` of the
principal summands: the leading one `p` is kept when it is in `R`, and `M(x)`
is then `p + M(rest)`; otherwise `M(x) = M(p)`.  `M_psi_mem` does a principal
summand `ψ_t(η)`: the next member of `R` above it is `ψ_t(M(η))`, `Ω_{t+1}` or
`Ω_{M(t)}`, according to what `R` contains.  Neither needs the argument `η` to
be in its own closure, and neither needs `S` to be anything in particular.

`M_mem_CSet` is the case `S = C_v(β)`, and `arg_mem_of_psi_mem` is what it is
for: if `ψ_w(d)` is in `C_v(β)` with `v ≤ w` and `d` in its own closure, then
`d` itself is in `C_v(β)` and below `β`.  That is Buchholz's reading of the
closure through `G`, and `Onto.lean` turns it into the syntactic statement.
-/

namespace Googology.Notation.ExBuchholz.Ord

open Ordinal Set

/-! ### The leading principal summand -/

/-- The leading principal summand `ω^(log x)` of `x`. -/
noncomputable def lead (x : Ordinal) : Ordinal := ω ^ Ordinal.log ω x

/-- What is left of `x` after its leading principal summand. -/
noncomputable def tail (x : Ordinal) : Ordinal := x - lead x

theorem lead_le {x : Ordinal} (hx : x ≠ 0) : lead x ≤ x := Ordinal.opow_log_le_self ω hx

theorem lt_opow_log_add_one (x : Ordinal) : x < ω ^ (Ordinal.log ω x + 1) := by
  have h := Ordinal.lt_opow_succ_log_self Ordinal.one_lt_omega0 x
  rwa [Order.succ_eq_add_one] at h

theorem lead_add_tail {x : Ordinal} (hx : x ≠ 0) : lead x + tail x = x :=
  Ordinal.add_sub_cancel_of_le (lead_le hx)

theorem tail_le (x : Ordinal) : tail x ≤ x := Ordinal.sub_le_self _ _

theorem tail_lt_opow (x : Ordinal) : tail x < ω ^ (Ordinal.log ω x + 1) :=
  lt_of_le_of_lt (tail_le x) (lt_opow_log_add_one x)

theorem opow_lt_opow_add_one (g : Ordinal) : (ω : Ordinal) ^ g < ω ^ (g + 1) :=
  (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2 (lt_add_one g)

theorem opow_ne_zero' (g : Ordinal) : (ω : Ordinal) ^ g ≠ 0 :=
  ne_of_gt (Ordinal.opow_pos g omega0_pos)

theorem opow_add_one_eq (g : Ordinal) : (ω : Ordinal) ^ (g + 1) = ω ^ g * ω :=
  Ordinal.opow_add_one _ _

/-- `ω^g + y` with `y < ω^(g+1)` has `ω^g` as leading summand and `y` as rest. -/
theorem log_opow_add {g y : Ordinal} (hy : y < ω ^ (g + 1)) :
    Ordinal.log ω (ω ^ g + y) = g := by
  refine (Ordinal.log_eq_iff Ordinal.one_lt_omega0 ?_ g).2 ⟨self_le_add_right _ _, ?_⟩
  · exact ne_of_gt (lt_of_lt_of_le (Ordinal.opow_pos g omega0_pos) (self_le_add_right _ _))
  · exact Ordinal.isPrincipal_add_omega0_opow (g + 1) (opow_lt_opow_add_one g) hy

theorem lead_opow_add {g y : Ordinal} (hy : y < ω ^ (g + 1)) : lead (ω ^ g + y) = ω ^ g := by
  rw [lead, log_opow_add hy]

theorem tail_opow_add {g y : Ordinal} (hy : y < ω ^ (g + 1)) : tail (ω ^ g + y) = y := by
  rw [tail, lead_opow_add hy, Ordinal.add_sub_cancel]

/-- A nonzero additively principal ordinal is a power of `ω`. -/
theorem exists_opow_of_principal {x : Ordinal} (h : Ordinal.IsPrincipal (· + ·) x)
    (h0 : x ≠ 0) : ∃ g : Ordinal, x = ω ^ g := by
  rcases Ordinal.isPrincipal_add_iff_zero_or_omega0_opow.1 h with h1 | ⟨g, hg⟩
  · exact absurd h1 h0
  · exact ⟨g, hg.symm⟩

theorem lead_opow (g : Ordinal) : lead (ω ^ g) = ω ^ g := by
  rw [lead, Ordinal.log_opow Ordinal.one_lt_omega0]

theorem tail_opow (g : Ordinal) : tail (ω ^ g) = 0 := by
  rw [tail, lead_opow, Ordinal.sub_self]

theorem log_add_of_le {x y : Ordinal} (hx : x ≠ 0)
    (h : Ordinal.log ω y ≤ Ordinal.log ω x) : Ordinal.log ω (x + y) = Ordinal.log ω x := by
  refine (Ordinal.log_eq_iff Ordinal.one_lt_omega0 ?_ _).2 ⟨?_, ?_⟩
  · exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.2 hx) (self_le_add_right _ _))
  · exact le_trans (Ordinal.opow_log_le_self ω hx) (self_le_add_right _ _)
  · refine Ordinal.isPrincipal_add_omega0_opow _ (lt_opow_log_add_one x) ?_
    refine lt_of_lt_of_le (lt_opow_log_add_one y) ?_
    exact Ordinal.opow_le_opow_right omega0_pos (add_le_add_left h 1)

/-- **The leading summand and the rest of a member of the closure are in the
closure.** -/
theorem lead_tail_mem {v a x : Ordinal} (hx : x ∈ CSet v a) (h0 : x ≠ 0) :
    lead x ∈ CSet v a ∧ tail x ∈ CSet v a := by
  revert h0
  induction hx with
  | @small y h =>
    intro h0
    exact ⟨Clos.small (lt_of_le_of_lt (lead_le h0) h), Clos.small (lt_of_le_of_lt (tail_le y) h)⟩
  | @add p q hp hq ihp ihq =>
    intro h0
    by_cases hq0 : q = 0
    · subst hq0
      rw [add_zero] at h0 ⊢
      exact ihp h0
    by_cases hp0 : p = 0
    · subst hp0
      rw [zero_add] at h0 ⊢
      exact ihq hq0
    rcases lt_or_ge (Ordinal.log ω p) (Ordinal.log ω q) with hl | hl
    · have habs : p + q = q := by
        refine Ordinal.add_of_omega0_opow_le (lt_of_lt_of_le (lt_opow_log_add_one p) ?_)
          (lead_le hq0)
        exact Ordinal.opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hl)
      rw [habs]
      exact ihq hq0
    · have hlog := log_add_of_le hp0 hl
      have hlead : lead (p + q) = lead p := by rw [lead, lead, hlog]
      have htail : tail (p + q) = tail p + q := by
        calc tail (p + q) = (p + q) - lead p := by rw [tail, hlead]
          _ = (lead p + (tail p + q)) - lead p := by rw [← add_assoc, lead_add_tail hp0]
          _ = tail p + q := Ordinal.add_sub_cancel _ _
      rw [hlead, htail]
      exact ⟨(ihp hp0).1, Clos.add (ihp hp0).2 hq⟩
  | @coll u e hu he _ _ =>
    intro h0
    obtain ⟨g, hg⟩ := exists_opow_of_principal (isPrincipal_add_psi e.1 u) h0
    have hmem : psi e.1 u ∈ CSet v a := Clos.coll hu he
    rw [hg, lead_opow, tail_opow]
    exact ⟨hg ▸ hmem, CSet.zero_mem v a⟩

/-! ### Principal summands -/

/-- `ω^g` is one of the principal summands of `x` in Cantor normal form. -/
def Comp (g x : Ordinal) : Prop :=
  ∃ A B : Ordinal, B < ω ^ (g + 1) ∧ x = A + ω ^ g + B

theorem Comp.opow_le {g x : Ordinal} (h : Comp g x) : ω ^ g ≤ x := by
  obtain ⟨A, B, _, rfl⟩ := h
  exact le_trans (self_le_add_left _ _) (self_le_add_right _ _)

theorem not_comp_zero (g : Ordinal) : ¬ Comp g 0 := by
  intro h
  exact absurd (le_antisymm h.opow_le zero_le) (opow_ne_zero' g)

/-- **A principal summand of a sum is a principal summand of one of the two.** -/
theorem Comp.add {g x y : Ordinal} (h : Comp g (x + y)) : Comp g x ∨ Comp g y := by
  obtain ⟨A, B, hB, he⟩ := h
  rcases le_or_gt x A with h1 | h1
  · right
    refine ⟨A - x, B, hB, ?_⟩
    have h2 : x + y = x + (A - x + ω ^ g + B) := by
      rw [he, ← add_assoc, ← add_assoc, Ordinal.add_sub_cancel_of_le h1]
    exact add_left_cancel h2
  · rcases le_or_gt x (A + ω ^ g) with h2 | h2
    · have hxF : A + (x - A) = x := Ordinal.add_sub_cancel_of_le h1.le
      have hFle : x - A ≤ ω ^ g := Ordinal.sub_le.2 h2
      rcases eq_or_lt_of_le hFle with hFe | hFl
      · left
        refine ⟨A, 0, Ordinal.opow_pos _ omega0_pos, ?_⟩
        rw [add_zero, ← hFe, hxF]
      · right
        refine ⟨0, B, hB, ?_⟩
        rw [zero_add]
        have h3 : A + ((x - A) + y) = A + (ω ^ g + B) := by
          rw [← add_assoc, hxF, he, add_assoc]
        have h4 : (x - A) + y = ω ^ g + B := add_left_cancel h3
        have h5 : (x - A) + (ω ^ g + B) = ω ^ g + B := by
          rw [← add_assoc, Ordinal.add_omega0_opow hFl]
        exact add_left_cancel (h4.trans h5.symm)
    · left
      refine ⟨A, x - (A + ω ^ g), ?_, (Ordinal.add_sub_cancel_of_le h2.le).symm⟩
      have h3 : A + ω ^ g + ((x - (A + ω ^ g)) + y) = A + ω ^ g + B := by
        rw [← add_assoc, Ordinal.add_sub_cancel_of_le h2.le, he]
      have hD : x - (A + ω ^ g) + y = B := add_left_cancel h3
      exact lt_of_le_of_lt (hD ▸ self_le_add_right _ _) hB

/-- The only principal summand of `ω^h` is `ω^h`. -/
theorem Comp.eq_of_opow {g h : Ordinal} (hc : Comp g (ω ^ h)) : g = h := by
  obtain ⟨A, B, hB, he⟩ := hc
  have hle : (ω : Ordinal) ^ g ≤ ω ^ h := he ▸ le_trans (self_le_add_left _ _) (self_le_add_right _ _)
  have hgh : g ≤ h := (Ordinal.opow_le_opow_iff_right Ordinal.one_lt_omega0).1 hle
  rcases eq_or_lt_of_le hgh with h1 | h1
  · exact h1
  · exfalso
    have hprin := Ordinal.isPrincipal_add_omega0_opow h
    have hA : A < ω ^ h := by
      refine lt_of_lt_of_le ?_ (he ▸ self_le_add_right (A + ω ^ g) B)
      conv_lhs => rw [← add_zero A]
      exact (add_lt_add_iff_left A).2 (Ordinal.opow_pos g omega0_pos)
    have hg : (ω : Ordinal) ^ g < ω ^ h := (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2 h1
    have hB' : B < ω ^ h := lt_of_lt_of_le hB
      (Ordinal.opow_le_opow_right omega0_pos (Order.add_one_le_of_lt h1))
    have hsum : A + ω ^ g + B < ω ^ h := hprin (hprin hA hg) hB'
    rw [← he] at hsum
    exact lt_irrefl _ hsum

theorem comp_lead {x : Ordinal} (hx : x ≠ 0) : Comp (Ordinal.log ω x) x :=
  ⟨0, tail x, tail_lt_opow x, by rw [zero_add]; exact (lead_add_tail hx).symm⟩

theorem Comp.of_tail {g x : Ordinal} (hx : x ≠ 0) (h : Comp g (tail x)) : Comp g x := by
  obtain ⟨A, B, hB, he⟩ := h
  refine ⟨lead x + A, B, hB, ?_⟩
  conv_lhs => rw [← lead_add_tail hx, he]
  simp only [add_assoc]

theorem tail_lt {x : Ordinal} (hx : x ≠ 0) : tail x < x := by
  refine lt_of_le_of_ne (le_trans (tail_le x) le_rfl) ?_
  intro heq
  have h1 : lead x + tail x = tail x := by rw [lead_add_tail hx]; exact heq.symm
  have h2 := Ordinal.add_eq_right_iff_mul_omega0_le.1 h1
  rw [lead, ← opow_add_one_eq] at h2
  exact absurd (tail_lt_opow x) (not_lt.2 h2)

/-! ### The least member of `R` above `x` -/

/-- `M c a x` is the least member of `C_c(a)` at or above `x`. -/
noncomputable def M (c a x : Ordinal) : Ordinal := sInf (CSet c a ∩ Ici x)

theorem M_spec {c a x : Ordinal} (h : ∃ z ∈ CSet c a, x ≤ z) :
    M c a x ∈ CSet c a ∧ x ≤ M c a x := by
  obtain ⟨z, hz, hxz⟩ := h
  exact csInf_mem (⟨z, hz, hxz⟩ : (CSet c a ∩ Ici x).Nonempty)

theorem M_le {c a x z : Ordinal} (hz : z ∈ CSet c a) (hxz : x ≤ z) : M c a x ≤ z :=
  csInf_le' ⟨hz, hxz⟩

theorem M_eq_self {c a x : Ordinal} (hx : x ∈ CSet c a) : M c a x = x :=
  le_antisymm (M_le hx le_rfl) (M_spec ⟨x, hx, le_rfl⟩).2

theorem Omega_mem {c a w : Ordinal} (ha : 0 < a) (hw : w ∈ CSet c a) : Ω_ w ∈ CSet c a := by
  rw [← psi_zero_arg w]
  exact CSet.psi_mem ha hw (CSet.zero_mem c a)

theorem one_mem {c a : Ordinal} (ha : 0 < a) : (1 : Ordinal) ∈ CSet c a := by
  have h := Omega_mem ha (CSet.zero_mem c a)
  rwa [Omega_zero] at h

theorem mul_nat_mem {c a p : Ordinal} (hp : p ∈ CSet c a) : ∀ n : ℕ, p * n ∈ CSet c a := by
  intro n
  induction n with
  | zero => rw [Nat.cast_zero, mul_zero]; exact CSet.zero_mem c a
  | succ k ih => rw [Nat.cast_succ, mul_add_one]; exact Clos.add ih hp

/-- The tower `0, Ω_0, Ω_{Ω_0}, …` climbs to `Λ`. -/
theorem omega_iterate_le_Omega_iterate : ∀ n : ℕ,
    (Ordinal.omega)^[n] 0 ≤ (fun v => Ω_ v)^[n + 1] (0 : Ordinal.{0}) := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply' _ (k + 1)]
    have hne : (fun v => Ω_ v)^[k + 1] (0 : Ordinal.{0}) ≠ 0 := by
      rw [Function.iterate_succ_apply']
      exact ne_of_gt (Omega_pos _)
    show ω_ _ ≤ Ω_ _
    rw [Omega_of_ne_zero hne]
    exact Ordinal.omega_le_omega.2 ih

theorem Omega_iterate_mem {c a : Ordinal.{0}} (ha : 0 < a) :
    ∀ n : ℕ, (fun v => Ω_ v)^[n] (0 : Ordinal.{0}) ∈ CSet c a := by
  intro n
  induction n with
  | zero => exact CSet.zero_mem c a
  | succ k ih => rw [Function.iterate_succ_apply']; exact Omega_mem ha ih

/-- Below `Λ` there is always a member of the closure above. -/
theorem bounded_of_lt_Lam {c a x : Ordinal.{0}} (ha : 0 < a) (hx : x < Lam) :
    ∃ z ∈ CSet c a, x ≤ z := by
  obtain ⟨n, hn⟩ := Ordinal.lt_nfp_iff.1 hx
  exact ⟨_, Omega_iterate_mem ha (n + 1), le_trans hn.le (omega_iterate_le_Omega_iterate n)⟩

theorem M_spec' {c a x : Ordinal.{0}} (ha : 0 < a) (hx : x < Lam) :
    M c a x ∈ CSet c a ∧ x ≤ M c a x :=
  M_spec (bounded_of_lt_Lam ha hx)

/-- A member of `C_c(a)` at or above a principal `ω^g` outside it is at least
`ω^(g+1)`: its leading summand cannot be `ω^g`. -/
theorem opow_add_one_le_of_notMem {c a g z : Ordinal} (hp : (ω : Ordinal) ^ g ∉ CSet c a)
    (hz : z ∈ CSet c a) (hle : ω ^ g ≤ z) : ω ^ (g + 1) ≤ z := by
  have hz0 : z ≠ 0 := ne_of_gt (lt_of_lt_of_le (Ordinal.opow_pos g omega0_pos) hle)
  have hlog : g ≤ Ordinal.log ω z := Ordinal.le_log_of_opow_le Ordinal.one_lt_omega0 hle
  rcases eq_or_lt_of_le hlog with h | h
  · exact absurd (h ▸ (lead_tail_mem hz hz0).1) hp
  · exact le_trans (Ordinal.opow_le_opow_right omega0_pos (Order.add_one_le_of_lt h))
      (lead_le hz0)

/-- **The least member above a principal outside `R`**, read off the principal
members of `R` above it. -/
theorem M_eq_of_principal {c a g X : Ordinal} (hp : (ω : Ordinal) ^ g ∉ CSet c a)
    (hX : X ∈ CSet c a) (hpX : ω ^ g ≤ X)
    (hmin : ∀ q, q ∈ CSet c a → Ordinal.IsPrincipal (· + ·) q → 0 < q → ω ^ g < q → X ≤ q) :
    M c a (ω ^ g) = X := by
  refine le_antisymm (M_le hX hpX) ?_
  obtain ⟨hm, hpm⟩ := M_spec ⟨X, hX, hpX⟩
  have hbig := opow_add_one_le_of_notMem hp hm hpm
  have hm0 : M c a (ω ^ g) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (Ordinal.opow_pos _ omega0_pos) hbig)
  have hlog : g + 1 ≤ Ordinal.log ω (M c a (ω ^ g)) :=
    Ordinal.le_log_of_opow_le Ordinal.one_lt_omega0 hbig
  refine le_trans (hmin _ (lead_tail_mem hm hm0).1 (Ordinal.isPrincipal_add_omega0_opow _)
    (Ordinal.opow_pos _ omega0_pos) ?_) (lead_le hm0)
  exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2
    (lt_of_lt_of_le (lt_add_one g) hlog)

/-! ### From the principal summands to the whole -/

/-- **`M` of `x` is in `S` when `M` of its principal summands is.**  The
leading summand `p` stays when it is in `R`, and then `M(x) = p + M(rest)`;
otherwise `M(x) = M(p)`. -/
theorem M_mem_of_comp {c a : Ordinal.{0}} {S : Set Ordinal.{0}} (ha : 0 < a)
    (hS0 : (0 : Ordinal) ∈ S) (hSadd : ∀ x y, x ∈ S → y ∈ S → x + y ∈ S) :
    ∀ x : Ordinal.{0}, x < Lam →
      (∀ g, Comp g x → (ω : Ordinal) ^ g ∈ S ∧ M c a (ω ^ g) ∈ S) → M c a x ∈ S := by
  intro x
  induction x using WellFoundedLT.induction with
  | _ x IH =>
    intro hx hcomp
    by_cases hx0 : x = 0
    · subst hx0
      rw [M_eq_self (CSet.zero_mem c a)]
      exact hS0
    set g := Ordinal.log ω x with hg
    have hpS := hcomp g (comp_lead hx0)
    have hr : tail x < x := tail_lt hx0
    have hMr : M c a (tail x) ∈ S :=
      IH _ hr (lt_trans hr hx) (fun h hc => hcomp h (Comp.of_tail hx0 hc))
    obtain ⟨hMxR, hxMx⟩ := M_spec' (c := c) ha hx
    by_cases hpR : (ω : Ordinal) ^ g ∈ CSet c a
    · -- `M(x) = p + M(rest)`
      obtain ⟨hMrR, hrMr⟩ := M_spec' (c := c) ha (lt_trans hr hx)
      have hsum : M c a x = ω ^ g + M c a (tail x) := by
        refine le_antisymm (M_le (Clos.add hpR hMrR) ?_) ?_
        · conv_lhs => rw [← lead_add_tail hx0]
          exact (add_le_add_iff_left _).2 hrMr
        · have hpm : (ω : Ordinal) ^ g ≤ M c a x := le_trans (lead_le hx0) hxMx
          have hm0 : M c a x ≠ 0 :=
            ne_of_gt (lt_of_lt_of_le (Ordinal.opow_pos _ omega0_pos) hpm)
          have hlog : g ≤ Ordinal.log ω (M c a x) :=
            Ordinal.le_log_of_opow_le Ordinal.one_lt_omega0 hpm
          rcases eq_or_lt_of_le hlog with hl | hl
          · -- the leading summand of `M(x)` is `p`
            have hlead : lead (M c a x) = ω ^ g := by rw [lead, ← hl]
            have htR := (lead_tail_mem hMxR hm0).2
            have hdec := lead_add_tail hm0
            rw [hlead] at hdec
            have hrt : tail x ≤ tail (M c a x) := by
              have h1 : ω ^ g + tail x ≤ ω ^ g + tail (M c a x) := by
                rw [hdec]
                conv_lhs => rw [show (ω : Ordinal) ^ g = lead x from rfl, lead_add_tail hx0]
                exact hxMx
              exact (add_le_add_iff_left _).1 h1
            conv_rhs => rw [← hdec]
            exact (add_le_add_iff_left _).2 (M_le htR hrt)
          · -- `M(x)` is past `ω^(g+1)`, and `p + M(rest)` is below it
            have hbig : (ω : Ordinal) ^ (g + 1) ≤ M c a x :=
              le_trans (Ordinal.opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hl))
                (lead_le hm0)
            refine le_trans (le_of_lt ?_) hbig
            have hne : g + 1 ≠ 0 := add_one_ne_zero_ord g
            obtain ⟨e, he, n, hn⟩ := (Ordinal.lt_omega0_opow hne).1 (tail_lt_opow x)
            have hle : (ω : Ordinal) ^ e * n ≤ ω ^ g * n :=
              mul_le_mul_left (Ordinal.opow_le_opow_right omega0_pos (Order.lt_add_one_iff.1 he)) _
            have hMrle : M c a (tail x) ≤ ω ^ g * n :=
              M_le (mul_nat_mem hpR n) (le_of_lt (lt_of_lt_of_le hn hle))
            refine Ordinal.isPrincipal_add_omega0_opow (g + 1) (opow_lt_opow_add_one g) ?_
            exact lt_of_le_of_lt hMrle (Ordinal.omega0_opow_mul_nat_lt (lt_add_one g) n)
      rw [hsum]
      exact hSadd _ _ hpS.1 hMr
    · -- `M(x) = M(p)`
      obtain ⟨hMpR, hpMp⟩ := M_spec' (c := c) ha
        (lt_of_le_of_lt (lead_le hx0) hx : (ω : Ordinal) ^ g < Lam)
      have heq : M c a x = M c a (ω ^ g) := by
        refine le_antisymm (M_le hMpR ?_) (M_le hMxR (le_trans (lead_le hx0) hxMx))
        exact le_trans (le_of_lt (lt_opow_log_add_one x))
          (opow_add_one_le_of_notMem hpR hMpR hpMp)
      rw [heq]
      exact hpS.2

/-! ### A principal summand `ψ_t(η)` -/

theorem psi_lt_Omega_of_lt {ξ w t : Ordinal} (h : w < t) : psi ξ w < Ω_ t :=
  lt_of_lt_of_le (psi_lt_Omega_succ ξ w) (Omega_mono (Order.add_one_le_of_lt h))

/-- **The next member of `R` above `ψ_t(η)`.**  It is `ψ_t(M(η))` when `R` has
a collapse at subscript `t` above `ψ_t(η)`, `Ω_{t+1}` when `t ∈ R` but it has
none, and `Ω_{M(t)}` when `t ∉ R`.  All three are in `S` as soon as `M(t)` and
`M(η)` are. -/
theorem M_psi_mem {c a : Ordinal.{0}} {S : Set Ordinal.{0}} (ha : 0 < a)
    (hSadd : ∀ x y, x ∈ S → y ∈ S → x + y ∈ S) (hS1 : (1 : Ordinal) ∈ S)
    (hSO : ∀ w, w ∈ S → Ω_ w ∈ S)
    (hScoll : ∀ t y, t ∈ S → y ∈ S → y < a → psi y t ∈ S)
    {t η : Ordinal.{0}} (ht : t < Lam) (hη : η < Lam)
    (hpS : psi η t ∈ S) (htS : t ∈ S) (hMt : M c a t ∈ S) (hMη : M c a η ∈ S) :
    M c a (psi η t) ∈ S := by
  obtain ⟨g, hg⟩ := exists_opow_of_principal (isPrincipal_add_psi η t) (ne_of_gt (psi_pos η t))
  by_cases hpR : psi η t ∈ CSet c a
  · rw [M_eq_self hpR]; exact hpS
  have hpR' : (ω : Ordinal) ^ g ∉ CSet c a := hg ▸ hpR
  have hpΩ : Ω_ c ≤ psi η t := by
    by_contra hcon
    exact hpR (Clos.small (not_le.1 hcon))
  -- the principal members of `R` above `ψ_t(η)` are collapses at subscript `≥ t`
  have hshape : ∀ q, q ∈ CSet c a → Ordinal.IsPrincipal (· + ·) q → 0 < q → psi η t < q →
      ∃ w ξ, w ∈ CSet c a ∧ ξ ∈ CSet c a ∧ ξ < a ∧ q = psi ξ w ∧ t ≤ w := by
    intro q hq hprin hq0 hpq
    rcases principal_mem_CSet q hq hprin hq0 with hs | ⟨w, ξ, hw, hξ, hξa, rfl⟩
    · exact absurd (lt_of_lt_of_le hs (le_trans hpΩ hpq.le)) (lt_irrefl _)
    · refine ⟨w, ξ, hw, hξ, hξa, rfl, ?_⟩
      by_contra hwt
      have h1 := psi_lt_Omega_of_lt (ξ := ξ) (not_le.1 hwt)
      exact absurd (lt_trans hpq (lt_of_lt_of_le h1 (Omega_le_psi η t))) (lt_irrefl _)
  have hpt1 : psi η t < Ω_ (t + 1) := psi_lt_Omega_succ η t
  by_cases htR : t ∈ CSet c a
  · by_cases hA : ∃ ξ, ξ ∈ CSet c a ∧ ξ < a ∧ psi η t < psi ξ t
    · obtain ⟨ξ, hξR, hξa, hpξ⟩ := hA
      have hηξ : η ≤ ξ := by
        by_contra hcon
        exact absurd (psi_mono t (not_le.1 hcon).le) (not_le.2 hpξ)
      obtain ⟨hMηR, hηMη⟩ := M_spec' (c := c) ha hη
      have hMξ : M c a η ≤ ξ := M_le hξR hηξ
      have hMa : M c a η < a := lt_of_le_of_lt hMξ hξa
      have hXR : psi (M c a η) t ∈ CSet c a := CSet.psi_mem hMa htR hMηR
      have heq : M c a (psi η t) = psi (M c a η) t := by
        rw [hg]
        refine M_eq_of_principal hpR' hXR (by rw [← hg]; exact psi_mono t hηMη) ?_
        intro q hq hprin hq0 hpq
        rw [← hg] at hpq
        obtain ⟨w, ξ', hw, hξ', hξ'a, rfl, htw⟩ := hshape q hq hprin hq0 hpq
        rcases eq_or_lt_of_le htw with rfl | hlt
        · have hηξ' : η ≤ ξ' := by
            by_contra hcon
            exact absurd (psi_mono t (not_le.1 hcon).le) (not_le.2 hpq)
          exact psi_mono t (M_le hξ' hηξ')
        · exact le_trans (psi_lt_Omega_succ _ t).le
            (le_trans (Omega_mono (Order.add_one_le_of_lt hlt)) (Omega_le_psi ξ' w))
      rw [heq]
      exact hScoll t _ htS hMη hMa
    · have ht1R : t + 1 ∈ CSet c a := Clos.add htR (one_mem ha)
      have heq : M c a (psi η t) = Ω_ (t + 1) := by
        rw [hg]
        refine M_eq_of_principal hpR' (Omega_mem ha ht1R) (by rw [← hg]; exact hpt1.le) ?_
        intro q hq hprin hq0 hpq
        rw [← hg] at hpq
        obtain ⟨w, ξ', hw, hξ', hξ'a, rfl, htw⟩ := hshape q hq hprin hq0 hpq
        rcases eq_or_lt_of_le htw with rfl | hlt
        · exact absurd ⟨ξ', hξ', hξ'a, hpq⟩ hA
        · exact le_trans (Omega_mono (Order.add_one_le_of_lt hlt)) (Omega_le_psi ξ' w)
      rw [heq]
      exact hSO _ (hSadd _ _ htS hS1)
  · obtain ⟨hMtR, htMt⟩ := M_spec' (c := c) ha ht
    have htlt : t < M c a t := lt_of_le_of_ne htMt (fun h => htR (h ▸ hMtR))
    have heq : M c a (psi η t) = Ω_ (M c a t) := by
      rw [hg]
      refine M_eq_of_principal hpR' (Omega_mem ha hMtR)
        (by rw [← hg]; exact le_trans hpt1.le (Omega_mono (Order.add_one_le_of_lt htlt))) ?_
      intro q hq hprin hq0 hpq
      rw [← hg] at hpq
      obtain ⟨w, ξ', hw, hξ', hξ'a, rfl, htw⟩ := hshape q hq hprin hq0 hpq
      rcases eq_or_lt_of_le htw with rfl | hlt
      · exact absurd hw htR
      · exact le_trans (Omega_mono (M_le hw hlt.le)) (Omega_le_psi ξ' w)
    rw [heq]
    exact hSO _ hMt

/-! ### The case `S = C_v(β)` -/

theorem Omega_lt_Lam' {v : Ordinal.{0}} (hv : v < Lam) : Ω_ v < Lam := by
  by_cases h : v = 0
  · rw [h, Omega_zero]
    exact lt_of_lt_of_le Ordinal.one_lt_omega0 omega0_le_Lam
  · rw [Omega_of_ne_zero h]
    exact omega_lt_Lam hv

theorem psi_lt_Lam {e u : Ordinal.{0}} (hu : u < Lam) : psi e u < Lam := by
  refine lt_trans (psi_lt_Omega_succ e u) (Omega_lt_Lam' ?_)
  rw [← Order.succ_eq_add_one]
  exact isSuccLimit_Lam.succ_lt hu

/-- Below `Λ`, the closure stays below `Λ`. -/
theorem lt_Lam_of_mem {v β x : Ordinal.{0}} (hv : v < Lam) (hx : x ∈ CSet v β) : x < Lam := by
  induction hx with
  | small h => exact lt_trans h (Omega_lt_Lam' hv)
  | add _ _ ihx ihy => exact add_lt_Lam ihx ihy
  | coll _ _ ihu _ => exact psi_lt_Lam ihu

/-- **`M` does not leave `C_v(β)`**, for the principal summands of its members. -/
theorem comp_M_mem_CSet {v β c a : Ordinal.{0}} (hv : v < Lam) (hvc : v ≤ c) (ha : 0 < a)
    (haβ : a ≤ β) : ∀ ℓ, ℓ ∈ CSet v β →
      ∀ g, Comp g ℓ → (ω : Ordinal) ^ g ∈ CSet v β ∧ M c a (ω ^ g) ∈ CSet v β := by
  have hβ : 0 < β := lt_of_lt_of_le ha haβ
  have hSadd : ∀ x y, x ∈ CSet v β → y ∈ CSet v β → x + y ∈ CSet v β :=
    fun _ _ hx hy => Clos.add hx hy
  intro ℓ hℓ
  induction hℓ with
  | @small y h =>
    intro g hc
    have hlt : (ω : Ordinal) ^ g < Ω_ v := lt_of_le_of_lt hc.opow_le h
    have hR : (ω : Ordinal) ^ g ∈ CSet c a := Clos.small (lt_of_lt_of_le hlt (Omega_mono hvc))
    rw [M_eq_self hR]
    exact ⟨Clos.small hlt, Clos.small hlt⟩
  | add _ _ ihx ihy =>
    intro g hc
    rcases hc.add with h | h
    · exact ihx g h
    · exact ihy g h
  | @coll u e hu he ihu ihe =>
    intro g hc
    have hmem : psi e.1 u ∈ CSet v β := Clos.coll hu he
    obtain ⟨h, hh⟩ := exists_opow_of_principal (isPrincipal_add_psi e.1 u)
      (ne_of_gt (psi_pos e.1 u))
    rw [hh] at hc
    rw [hc.eq_of_opow, ← hh]
    refine ⟨hmem, ?_⟩
    have huL : u < Lam := lt_Lam_of_mem hv hu
    have heL : e.1 < Lam := lt_Lam_of_mem hv he
    refine M_psi_mem ha hSadd (one_mem hβ) (fun w hw => Omega_mem hβ hw)
      (fun t y ht hy hya => CSet.psi_mem (lt_of_lt_of_le hya haβ) ht hy) huL heL hmem hu ?_ ?_
    · exact M_mem_of_comp ha (CSet.zero_mem v β) hSadd u huL ihu
    · exact M_mem_of_comp ha (CSet.zero_mem v β) hSadd e.1 heL ihe

theorem M_mem_CSet {v β c a ℓ : Ordinal.{0}} (hv : v < Lam) (hvc : v ≤ c) (ha : 0 < a)
    (haβ : a ≤ β) (hℓ : ℓ ∈ CSet v β) : M c a ℓ ∈ CSet v β :=
  M_mem_of_comp ha (CSet.zero_mem v β) (fun _ _ hx hy => Clos.add hx hy) ℓ
    (lt_Lam_of_mem hv hℓ) (comp_M_mem_CSet hv hvc ha haβ ℓ hℓ)

/-! ### The argument `M(e)` -/

/-- **Moving the argument up to `M(e)` does not change the closure.** -/
theorem CSet_M_subset {w e : Ordinal.{0}} (he : 0 < e) (hlt : e < Lam) :
    CSet w (M w e e) ⊆ CSet w e := by
  obtain ⟨hmR, hem⟩ := M_spec' (c := w) he hlt
  intro x hx
  induction hx with
  | small h => exact Clos.small h
  | add _ _ ihx ihy => exact Clos.add ihx ihy
  | @coll u y hu hy ihu ihy =>
    by_cases hye : y.1 < e
    · exact CSet.psi_mem hye ihu ihy
    · exact absurd (M_le ihy (not_lt.1 hye)) (not_le.2 y.2)

theorem psi_M_eq {w e : Ordinal.{0}} (he : 0 < e) (hlt : e < Lam) :
    psi (M w e e) w = psi e w := by
  refine le_antisymm ?_ (psi_mono w (M_spec' (c := w) he hlt).2)
  refine psi_le_of_notMem ?_
  intro h
  exact psi_notMem e w (CSet_M_subset he hlt h)

/-- `M(e)` lies in its own closure. -/
theorem M_mem_self {w e : Ordinal.{0}} (he : 0 < e) (hlt : e < Lam) :
    M w e e ∈ CSet w (M w e e) := by
  obtain ⟨hmR, hem⟩ := M_spec' (c := w) he hlt
  exact CSet_mono w hem hmR

/-! ### Reading an argument out of the closure -/

theorem lt_Omega_self {w : Ordinal.{0}} (hw : w < Lam) : w < Ω_ w := by
  by_cases h : w = 0
  · rw [h, Omega_zero]; exact zero_lt_one
  · rw [Omega_of_ne_zero h]
    by_contra hcon
    have hfp : ω_ w ≤ w := not_lt.1 hcon
    exact absurd (lt_of_lt_of_le hw (nfp_le_fp Ordinal.omega.monotone bot_le hfp))
      (lt_irrefl _)

theorem CSet_subset_of_le {v w a : Ordinal} (h : v ≤ w) : CSet v a ⊆ CSet w a := by
  intro x hx
  induction hx with
  | small h' => exact Clos.small (lt_of_lt_of_le h' (Omega_mono h))
  | add _ _ ihx ihy => exact Clos.add ihx ihy
  | coll _ _ ihu ihe => exact Clos.coll ihu ihe

/-- The subscript of a collapse is determined by its value. -/
theorem sub_eq_of_psi_eq {e w e' w' : Ordinal} (h : psi e w = psi e' w') : w = w' := by
  rcases lt_trichotomy w w' with hlt | heq | hlt
  · exfalso
    have h1 := psi_lt_Omega_of_lt (ξ := e) hlt
    rw [h] at h1
    exact absurd (Omega_le_psi e' w') (not_le.2 h1)
  · exact heq
  · exfalso
    have h1 := psi_lt_Omega_of_lt (ξ := e') hlt
    rw [← h] at h1
    exact absurd (Omega_le_psi e w) (not_le.2 h1)

/-- **If `ψ_w(d)` is in `C_v(β)`, `v ≤ w`, and `d` is in its own closure, then
`d` is in `C_v(β)` and below `β`, and so is the subscript.**  The closure put
`ψ_w(d)` in as some `ψ_w(e)` with `e ∈ C_v(β)`, and `d` is `M(e)`, which
`M_mem_CSet` keeps inside. -/
theorem arg_mem_of_psi_mem {v β w d : Ordinal.{0}} (hv : v < Lam) (hw : w < Lam)
    (hvw : v ≤ w) (hmem : psi d w ∈ CSet v β) (hstd : d ∈ CSet w d) :
    d ∈ CSet v β ∧ d < β ∧ w ∈ CSet v β := by
  have hdβ : d < β := by
    by_contra hcon
    exact psi_notMem d w (CSet_mono w (not_lt.1 hcon) (CSet_subset_of_le hvw hmem))
  have hwself : ∀ x, w ∈ CSet w x := fun x => Clos.small (lt_Omega_self hw)
  rcases principal_mem_CSet _ hmem (isPrincipal_add_psi d w) (psi_pos d w) with
    hs | ⟨u, e, hu, he, heβ, heq⟩
  · exact absurd (lt_of_lt_of_le hs (le_trans (Omega_mono hvw) (Omega_le_psi d w)))
      (lt_irrefl _)
  have huw : u = w := (sub_eq_of_psi_eq heq).symm
  subst huw
  refine ⟨?_, hdβ, hu⟩
  rcases eq_or_ne e 0 with rfl | he0
  · rcases eq_or_ne d 0 with rfl | hd0
    · exact CSet.zero_mem v β
    · exfalso
      have h1 := Term.psi_lt_of_arg_lt (CSet.zero_mem u 0) (pos_iff_ne_zero.2 hd0) (hwself d)
      rw [heq] at h1
      exact lt_irrefl _ h1
  · have hepos : 0 < e := pos_iff_ne_zero.2 he0
    have heL : e < Lam := lt_Lam_of_mem hv he
    have hmS : M u e e ∈ CSet v β := M_mem_CSet hv hvw hepos heβ.le he
    have hmd : M u e e = d := by
      have hpsi : psi (M u e e) u = psi d u := by rw [psi_M_eq hepos heL, heq]
      rcases lt_trichotomy (M u e e) d with hlt | h | hlt
      · exact absurd hpsi (ne_of_lt (Term.psi_lt_of_arg_lt (M_mem_self hepos heL) hlt (hwself d)))
      · exact h
      · exact absurd hpsi.symm (ne_of_lt (Term.psi_lt_of_arg_lt hstd hlt (hwself _)))
    rw [← hmd]
    exact hmS

end Googology.Notation.ExBuchholz.Ord
