import Googology.Notation.ExBuchholz.Ord

/-!
# `ψ_0` and `ω ^ ·`

`ψ_0(a) = ω^a` is the first thing one wants to know about the collapse, and it
is **not** true for every `a`: `ε₀ ∉ C_0(ε₀ + 1)`, so `ψ_0(ε₀ + 1) = ψ_0(ε₀) =
ε₀` while `ω^(ε₀+1) = ε₀·ω`.  One half holds with no condition, and that is
what this file proves.

`lt_opow_of_mem_CSet_zero` says every countable member of `C_0(a)` is below
`ω^a`, by transfinite recursion on `a` with an induction on the derivation
inside it.  The three clauses are the three ways into the closure: below
`Ω_0 = 1` is `0`; a sum stays below because `ω^a` is additively principal; and
a collapse `ψ_u(e)` that is countable has `u = 0`, because `Ω_u ≤ ψ_u(e)`, so
the recursion at `e < a` bounds it by `ω^e < ω^a`.

`psi_zero_le_opow` is the corollary: `ψ_0(a) ≤ ω^a` for every `a`.  Above the
first uncountable it is not close — `ψ_0(a) < Ω_1` always — and the content is
below it.

Above `ε₀` the arguments carry `Ω` in front, and the same proof gives
`ψ_0(Ω + a) = ε₀ · ω^a` up to the first fixed point of `x ↦ ε₀ · ω^x`, which
is `ε₁`.  `psi_Omega_add_one` is the first value it names: `ψ_0(Ω + 1)` is
`ε₀·ω`.
-/

namespace Googology.Notation.ExBuchholz.Ord

open Ordinal Cardinal Set

/-- An uncountable ordinal is at least `Ω_1`. -/
theorem Omega_one_le_of_not_card_le {x : Ordinal.{u}} (h : ¬ x.card ≤ ℵ_ 0) : Ω_ 1 ≤ x := by
  rw [Omega_of_ne_zero one_ne_zero]
  have h1 : ℵ_ 1 ≤ x.card := by
    rw [show (1 : Ordinal) = 0 + 1 from (zero_add 1).symm, ← Cardinal.succ_aleph]
    exact Order.succ_le_of_lt (not_le.mp h)
  rw [← Cardinal.ord_aleph]
  exact Cardinal.ord_le.mpr h1

/-- `ψ_0(a)` is countable. -/
theorem psi_zero_lt_Omega_one (a : Ordinal.{u}) : psi a 0 < Ω_ 1 := by
  have := psi_lt_Omega_succ a 0
  rwa [zero_add] at this

/-- **Every countable member of `C_0(a)` is below `ω^a`.** -/
theorem lt_opow_of_mem_CSet_zero : ∀ a : Ordinal.{u}, ∀ x : Ordinal.{u}, x ∈ CSet 0 a →
    x.card ≤ ℵ_ 0 → x < ω ^ a := by
  intro a
  induction a using WellFoundedLT.induction with
  | _ a IH =>
    have key : ∀ e : Ordinal.{u}, e < a → psi e 0 ≤ ω ^ e := by
      intro e he
      by_cases hc : (ω ^ e : Ordinal.{u}).card ≤ ℵ_ 0
      · refine psi_le_of_notMem (fun hmem => ?_)
        exact absurd (IH e he _ hmem hc) (lt_irrefl _)
      · exact le_trans (psi_zero_lt_Omega_one e).le (Omega_one_le_of_not_card_le hc)
    intro x hx
    induction hx with
    | @small y h =>
      intro _
      rw [Omega_zero, Order.lt_one_iff] at h
      rw [h]
      exact Ordinal.opow_pos a omega0_pos
    | @add p q _ _ ihp ihq =>
      intro hcard
      rw [Ordinal.card_add] at hcard
      exact Ordinal.isPrincipal_add_omega0_opow a
        (ihp (le_trans (self_le_add_right _ _) hcard))
        (ihq (le_trans (self_le_add_left _ _) hcard))
    | @coll u e hu he _ _ =>
      intro hcard
      have hu0 : u = 0 := by
        have hOu : (Ω_ u).card ≤ ℵ_ 0 :=
          le_trans (Ordinal.card_le_card (Omega_le_psi e.1 u)) hcard
        exact nonpos_iff_eq_zero.mp (le_of_card_Omega_le hOu)
      rw [hu0]
      refine lt_of_le_of_lt (key e.1 e.2) ?_
      exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr e.2

/-- **`ψ_0(a) ≤ ω^a`**, with no condition on `a`. -/
theorem psi_zero_le_opow (a : Ordinal.{u}) : psi a 0 ≤ ω ^ a := by
  by_cases hc : (ω ^ a : Ordinal.{u}).card ≤ ℵ_ 0
  · refine psi_le_of_notMem (fun hmem => ?_)
    exact absurd (lt_opow_of_mem_CSet_zero a _ hmem hc) (lt_irrefl _)
  · exact le_trans (psi_zero_lt_Omega_one a).le (Omega_one_le_of_not_card_le hc)

/-! ### `ε₀` -/

/-- `ε₀`, the least fixed point of `ω ^ ·`. -/
noncomputable def eps0 : Ordinal.{u} := Ordinal.nfp (fun x => (ω : Ordinal.{u}) ^ x) 0

theorem opow_monotone : Monotone (fun x : Ordinal.{u} => (ω : Ordinal.{u}) ^ x) := by
  intro x y h
  exact Ordinal.opow_le_opow_right omega0_pos h

/-- **Below `ε₀` nothing is a fixed point of `ω ^ ·`.** -/
theorem lt_opow_self_of_lt_eps0 {b : Ordinal.{u}} (h : b < eps0) : b < ω ^ b := by
  rcases lt_or_ge b (ω ^ b) with hb | hb
  · exact hb
  · exact absurd h (not_lt.mpr (Ordinal.nfp_le_fp opow_monotone (by simp : (0 : Ordinal.{u}) ≤ b) hb))

/-- **`ε₀` is closed under `ω ^ ·`.** -/
theorem opow_lt_eps0 {b : Ordinal.{u}} (h : b < eps0) : ω ^ b < eps0 := by
  obtain ⟨n, hn⟩ := Ordinal.lt_nfp_iff.mp h
  refine lt_of_lt_of_le ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr hn) ?_
  have : (fun x => (ω : Ordinal.{u}) ^ x)^[n + 1] 0
      = (ω : Ordinal.{u}) ^ (fun x => (ω : Ordinal.{u}) ^ x)^[n] 0 :=
    Function.iterate_succ_apply' _ n 0
  rw [← this]
  exact Ordinal.iterate_le_nfp _ _ _

/-! ### The other half -/

/-- Everything below `M · ω^a` is `M` times a finite sum of powers `ω^b` with
`b < a`, plus a remainder below `M`.  So a set that has everything below `M`,
has each `M · ω^b`, and is closed under `+`, has all of it. -/
theorem mem_of_lt_mul_opow {S : Set Ordinal.{u}} (M : Ordinal.{u}) (hM : 0 < M)
    (hsmall : ∀ z : Ordinal.{u}, z < M → z ∈ S)
    (hadd : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) {a : Ordinal.{u}}
    (hpow : ∀ b : Ordinal.{u}, b < a → M * (ω : Ordinal.{u}) ^ b ∈ S) :
    ∀ x : Ordinal.{u}, x < M * ω ^ a → x ∈ S := by
  have hmul : ∀ (b : Ordinal.{u}), b < a → ∀ n : ℕ, M * (ω : Ordinal.{u}) ^ b * n ∈ S := by
    intro b hb n
    induction n with
    | zero => rw [Nat.cast_zero, mul_zero]; exact hsmall 0 hM
    | succ m ih =>
      rw [Nat.cast_succ, mul_add_one]
      exact hadd _ ih _ (hpow b hb)
  have key : ∀ y : Ordinal.{u}, y < (ω : Ordinal.{u}) ^ a → M * y ∈ S := by
    intro y
    induction y using WellFoundedLT.induction with
    | _ y IH =>
      intro hy
      rcases eq_or_ne y 0 with rfl | hy0
      · rw [mul_zero]
        exact hsmall 0 hM
      · have hle : (ω : Ordinal.{u}) ^ Ordinal.log ω y ≤ y := Ordinal.opow_log_le_self ω hy0
        have hlt : Ordinal.log ω y < a :=
          (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mp (lt_of_le_of_lt hle hy)
        have hne : (ω : Ordinal.{u}) ^ Ordinal.log ω y ≠ 0 :=
          ne_of_gt (Ordinal.opow_pos _ omega0_pos)
        have hr : y % (ω : Ordinal.{u}) ^ Ordinal.log ω y < y :=
          lt_of_lt_of_le (Ordinal.mod_lt y hne) hle
        obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp (Ordinal.div_opow_log_lt y Ordinal.one_lt_omega0)
        have hsum := Ordinal.div_add_mod y ((ω : Ordinal.{u}) ^ Ordinal.log ω y)
        rw [hn] at hsum
        rw [← hsum, mul_add, ← mul_assoc]
        exact hadd _ (hmul _ hlt n) _ (IH _ hr (lt_trans hr hy))
  intro x hx
  have hy : x / M < (ω : Ordinal.{u}) ^ a := (Ordinal.lt_mul_iff_div_lt (ne_of_gt hM)).mp hx
  have hz : x % M < M := Ordinal.mod_lt x (ne_of_gt hM)
  have hdm : M * (x / M) + x % M = x := Ordinal.div_add_mod x M
  rw [← hdm]
  exact hadd _ (key _ hy) _ (hsmall _ hz)

/-- The same with no multiplier. -/
theorem mem_of_lt_opow {S : Set Ordinal.{u}} (hzero : (0 : Ordinal.{u}) ∈ S)
    (hadd : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) {a : Ordinal.{u}}
    (hpow : ∀ b, b < a → (ω : Ordinal.{u}) ^ b ∈ S) :
    ∀ x : Ordinal.{u}, x < ω ^ a → x ∈ S := by
  intro x hx
  refine mem_of_lt_mul_opow (S := S) (a := a) 1 zero_lt_one (fun z hz => ?_) hadd
    (fun b hb => ?_) x ?_
  · rw [Order.lt_one_iff.mp hz]
    exact hzero
  · rw [one_mul]
    exact hpow b hb
  · rw [one_mul]
    exact hx

/-- **`ψ_0(a) = ω^a` below `ε₀`.** -/
theorem psi_zero_eq_opow : ∀ a : Ordinal.{u}, a < eps0 → psi a 0 = ω ^ a := by
  intro a
  induction a using WellFoundedLT.induction with
  | _ a IH =>
    intro ha
    have hG : a ≤ psi a 0 := by
      by_contra hc
      have hb : psi a 0 < a := not_le.mp hc
      have h1 := IH (psi a 0) hb (lt_trans hb ha)
      have h2 : psi (psi a 0) 0 ≤ psi a 0 := psi_mono 0 hb.le
      rw [h1] at h2
      exact absurd h2 (not_le.mpr (lt_opow_self_of_lt_eps0 (lt_trans hb ha)))
    have hpow : ∀ b, b < a → (ω : Ordinal.{u}) ^ b ∈ CSet 0 a := by
      intro b hb
      have hmem : b ∈ CSet 0 a := mem_CSet_of_lt_psi (lt_of_lt_of_le hb hG)
      have := CSet.psi_mem hb (CSet.zero_mem 0 a) hmem
      rwa [IH b hb (lt_trans hb ha)] at this
    refine le_antisymm (psi_zero_le_opow a) ?_
    by_contra hc
    exact psi_notMem a 0 (mem_of_lt_opow (CSet.zero_mem 0 a)
      (fun _ hx _ hy => CSet.add_mem hx hy) hpow _ (not_le.mp hc))

/-! ### `ψ_0(Ω) = ε₀` -/

theorem card_le_of_lt_Omega_one {x : Ordinal.{u}} (h : x < Ω_ 1) : x.card ≤ ℵ_ 0 := by
  rw [Omega_of_ne_zero one_ne_zero, ← Cardinal.ord_aleph] at h
  have := Cardinal.lt_ord.mp h
  rw [show (1 : Ordinal) = 0 + 1 from (zero_add 1).symm, ← Cardinal.succ_aleph] at this
  exact Order.le_of_lt_succ this

theorem lt_Omega_one_of_card_le {x : Ordinal.{u}} (h : x.card ≤ ℵ_ 0) : x < Ω_ 1 := by
  rw [Omega_of_ne_zero one_ne_zero, ← Cardinal.ord_aleph]
  refine Cardinal.lt_ord.mpr (lt_of_le_of_lt h ?_)
  rw [show (1 : Ordinal) = 0 + 1 from (zero_add 1).symm, ← Cardinal.succ_aleph]
  exact Order.lt_succ _

theorem iterate_lt_Omega_one : ∀ n : ℕ,
    (fun x : Ordinal.{u} => (ω : Ordinal.{u}) ^ x)^[n] 0 < Ω_ 1 := by
  intro n
  induction n with
  | zero => rw [Function.iterate_zero_apply]; exact Omega_pos 1
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    refine lt_Omega_one_of_card_le ?_
    rcases eq_or_ne ((fun x : Ordinal.{u} => (ω : Ordinal.{u}) ^ x)^[m] 0) 0 with h0 | h0
    · rw [h0, Ordinal.opow_zero, Ordinal.card_one]
      exact le_trans Cardinal.one_le_aleph0 (le_of_eq Cardinal.aleph_zero.symm)
    · rw [Ordinal.card_omega0_opow h0, Cardinal.aleph_zero]
      exact max_le (le_refl _) (by rw [← Cardinal.aleph_zero]; exact card_le_of_lt_Omega_one ih)

theorem eps0_le_Omega_one : eps0.{u} ≤ Ω_ 1 :=
  Ordinal.nfp_le (fun n => (iterate_lt_Omega_one n).le)

theorem opow_eps0 : (ω : Ordinal.{u}) ^ eps0.{u} = eps0.{u} :=
  Ordinal.nfp_fp (Ordinal.isNormal_opow Ordinal.one_lt_omega0) 0

theorem eps0_pos : 0 < eps0.{u} := by
  refine Ordinal.lt_nfp_iff.mpr ⟨1, ?_⟩
  rw [Function.iterate_one]
  exact Ordinal.opow_pos 0 omega0_pos

theorem isPrincipal_add_eps0 : Ordinal.IsPrincipal (· + ·) eps0.{u} := by
  have := Ordinal.isPrincipal_add_omega0_opow eps0.{u}
  rwa [opow_eps0] at this

/-- Every countable member of `C_0(Ω)` is below `ε₀`. -/
theorem lt_eps0_of_mem_CSet_Omega_one : ∀ x : Ordinal.{u}, x ∈ CSet 0 (Ω_ 1) →
    x.card ≤ ℵ_ 0 → x < eps0 := by
  intro x hx
  induction hx with
  | @small y h =>
    intro _
    rw [Omega_zero, Order.lt_one_iff] at h
    rw [h]
    exact eps0_pos
  | @add p q _ _ ihp ihq =>
    intro hcard
    rw [Ordinal.card_add] at hcard
    exact isPrincipal_add_eps0 (ihp (le_trans (self_le_add_right _ _) hcard))
      (ihq (le_trans (self_le_add_left _ _) hcard))
  | @coll u e _ _ _ ihe =>
    intro hcard
    have hu0 : u = 0 := by
      have hOu : (Ω_ u).card ≤ ℵ_ 0 :=
        le_trans (Ordinal.card_le_card (Omega_le_psi e.1 u)) hcard
      exact nonpos_iff_eq_zero.mp (le_of_card_Omega_le hOu)
    rw [hu0]
    exact lt_of_le_of_lt (psi_zero_le_opow e.1)
      (opow_lt_eps0 (ihe (card_le_of_lt_Omega_one e.2)))

/-- **`ψ_0(Ω) = ε₀`.** -/
theorem psi_Omega_one : psi (Ω_ 1) 0 = eps0.{u} := by
  refine le_antisymm ?_ ?_
  · by_contra hc
    have h : eps0.{u} < psi (Ω_ 1) 0 := not_le.mp hc
    exact absurd (lt_eps0_of_mem_CSet_Omega_one eps0 (mem_CSet_of_lt_psi h)
      (card_le_of_lt_Omega_one (lt_trans h (psi_zero_lt_Omega_one _)))) (lt_irrefl _)
  · have key : ∀ x : Ordinal.{u}, x < eps0 → x ∈ CSet 0 (Ω_ 1) := by
      intro x
      induction x using WellFoundedLT.induction with
      | _ x IH =>
        intro hx
        refine mem_of_lt_opow (CSet.zero_mem 0 (Ω_ 1)) (fun _ h1 _ h2 => CSet.add_mem h1 h2)
          (a := x) (fun b hb => ?_) x (lt_opow_self_of_lt_eps0 hx)
        have hb0 : b < eps0 := lt_trans hb hx
        have := CSet.psi_mem (lt_of_lt_of_le hb0 eps0_le_Omega_one)
          (CSet.zero_mem 0 (Ω_ 1)) (IH b hb hb0)
        rwa [psi_zero_eq_opow b hb0] at this
    by_contra hc
    have h : psi (Ω_ 1) 0 < eps0.{u} := not_le.mp hc
    exact psi_notMem (Ω_ 1) 0 (key _ h)

/-! ### `ψ_0` just above `Ω`

`ψ_0(Ω) = ε₀`, and above that the arguments carry `Ω` in front: `ψ_0(Ω + a)`
is `ε₀ · ω^a`, again up to the first fixed point.  The proof is the one for
`ψ_0(a) = ω^a` with `ε₀` in front of every power. -/

theorem isPrincipal_add_eps0_mul_opow (a : Ordinal.{u}) :
    Ordinal.IsPrincipal (· + ·) (eps0.{u} * ω ^ a) := by
  have h : eps0.{u} * (ω : Ordinal.{u}) ^ a = (ω : Ordinal.{u}) ^ (eps0.{u} + a) := by
    rw [Ordinal.opow_add, opow_eps0]
  rw [h]
  exact Ordinal.isPrincipal_add_omega0_opow _

theorem eps0_le_eps0_mul_opow (a : Ordinal.{u}) : eps0.{u} ≤ eps0.{u} * ω ^ a := by
  conv_lhs => rw [← mul_one eps0.{u}]
  refine mul_le_mul_right ?_ _
  rw [← Ordinal.opow_zero (ω : Ordinal.{u})]
  exact Ordinal.opow_le_opow_right omega0_pos (by simp)

theorem eps0_lt_eps0_mul_opow {a : Ordinal.{u}} (ha : a ≠ 0) : eps0.{u} < eps0.{u} * ω ^ a := by
  conv_lhs => rw [← mul_one eps0.{u}]
  refine (mul_lt_mul_iff_of_pos_left eps0_pos).mpr ?_
  rw [← Ordinal.opow_zero (ω : Ordinal.{u})]
  exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr
    (by
      rcases eq_or_lt_of_le (show (0 : Ordinal.{u}) ≤ a by simp) with h | h
      · exact absurd h.symm ha
      · exact h)

/-- **Every countable member of `C_0(Ω + a)` is below `ε₀ · ω^a`.** -/
theorem lt_eps0_mul_opow_of_mem_CSet : ∀ a : Ordinal.{u}, ∀ x : Ordinal.{u},
    x ∈ CSet 0 (Ω_ 1 + a) → x.card ≤ ℵ_ 0 → x < eps0 * ω ^ a := by
  intro a
  induction a using WellFoundedLT.induction with
  | _ a IH =>
    rcases eq_or_ne a 0 with rfl | ha
    · intro x hx hc
      rw [add_zero] at hx
      rw [Ordinal.opow_zero, mul_one]
      exact lt_eps0_of_mem_CSet_Omega_one x hx hc
    · have key : ∀ b : Ordinal.{u}, b < a → psi (Ω_ 1 + b) 0 ≤ eps0 * ω ^ b := by
        intro b hb
        by_cases hc : (eps0.{u} * (ω : Ordinal.{u}) ^ b).card ≤ ℵ_ 0
        · refine psi_le_of_notMem (fun hmem => ?_)
          exact absurd (IH b hb _ hmem hc) (lt_irrefl _)
        · exact le_trans (psi_zero_lt_Omega_one _).le (Omega_one_le_of_not_card_le hc)
      intro x hx
      induction hx with
      | @small y h =>
        intro _
        rw [Omega_zero, Order.lt_one_iff] at h
        rw [h]
        exact lt_of_lt_of_le eps0_pos (eps0_le_eps0_mul_opow a)
      | @add p q _ _ ihp ihq =>
        intro hcard
        rw [Ordinal.card_add] at hcard
        exact isPrincipal_add_eps0_mul_opow a
          (ihp (le_trans (self_le_add_right _ _) hcard))
          (ihq (le_trans (self_le_add_left _ _) hcard))
      | @coll u e _ _ _ _ =>
        intro hcard
        have hu0 : u = 0 := by
          have hOu : (Ω_ u).card ≤ ℵ_ 0 :=
            le_trans (Ordinal.card_le_card (Omega_le_psi e.1 u)) hcard
          exact nonpos_iff_eq_zero.mp (le_of_card_Omega_le hOu)
        rw [hu0]
        rcases lt_or_ge e.1 (Ω_ 1) with hlt | hge
        · refine lt_of_le_of_lt ?_ (eps0_lt_eps0_mul_opow ha)
          rw [← psi_Omega_one]
          exact psi_mono 0 hlt.le
        · have hb : e.1 - Ω_ 1 < a := (Ordinal.sub_lt_of_le hge).mpr e.2
          have heq : Ω_ 1 + (e.1 - Ω_ 1) = e.1 := Ordinal.add_sub_cancel_of_le hge
          refine lt_of_le_of_lt (le_trans (le_of_eq (congrArg (fun z => psi z 0) heq.symm))
            (key (e.1 - Ω_ 1) hb)) ?_
          exact (mul_lt_mul_iff_of_pos_left eps0_pos).mpr
            ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr hb)

/-- **`ψ_0(Ω + a) ≤ ε₀ · ω^a`**, with no condition on `a`. -/
theorem psi_Omega_add_le (a : Ordinal.{u}) : psi (Ω_ 1 + a) 0 ≤ eps0.{u} * ω ^ a := by
  by_cases hc : (eps0.{u} * (ω : Ordinal.{u}) ^ a).card ≤ ℵ_ 0
  · refine psi_le_of_notMem (fun hmem => ?_)
    exact absurd (lt_eps0_mul_opow_of_mem_CSet a _ hmem hc) (lt_irrefl _)
  · exact le_trans (psi_zero_lt_Omega_one _).le (Omega_one_le_of_not_card_le hc)

/-! ### `ψ_v(0) = Ω_v` -/

theorem isPrincipal_add_Omega (v : Ordinal.{u}) : Ordinal.IsPrincipal (· + ·) (Ω_ v) := by
  by_cases h : v = 0
  · rw [h, Omega_zero]
    intro x y hx hy
    rw [Order.lt_one_iff] at hx hy
    subst hx
    subst hy
    show (0 : Ordinal.{u}) + 0 < 1
    rw [add_zero]
    exact zero_lt_one
  · rw [Omega_of_ne_zero h, ← Cardinal.ord_aleph]
    exact Ordinal.isPrincipal_add_ord (Cardinal.aleph0_le_aleph v)

/-- **`ψ_v(0) = Ω_v`**: with no argument below `0` to collapse, the closure is
everything below `Ω_v`. -/
theorem psi_zero_arg (v : Ordinal.{u}) : psi 0 v = Ω_ v := by
  refine le_antisymm (psi_le_of_notMem (fun hmem => ?_)) (Omega_le_psi 0 v)
  have key : ∀ x : Ordinal.{u}, x ∈ CSet v 0 → x < Ω_ v := by
    intro x hx
    induction hx with
    | @small y h => exact h
    | @add p q _ _ ihp ihq => exact isPrincipal_add_Omega v ihp ihq
    | @coll _ e _ _ _ _ => exact absurd e.2 (by simp)
  exact absurd (key _ hmem) (lt_irrefl _)

/-! ### The equality above `Ω` -/

/-- The least fixed point of `x ↦ ε₀ · ω^x`, which is `ε₁`. -/
noncomputable def eps1 : Ordinal.{u} :=
  Ordinal.nfp (fun x => eps0.{u} * (ω : Ordinal.{u}) ^ x) 0

theorem eps0_mul_opow_monotone :
    Monotone (fun x : Ordinal.{u} => eps0.{u} * (ω : Ordinal.{u}) ^ x) := by
  intro x y h
  exact mul_le_mul_right (Ordinal.opow_le_opow_right omega0_pos h) _

theorem lt_eps0_mul_opow_self {b : Ordinal.{u}} (h : b < eps1) : b < eps0.{u} * ω ^ b := by
  rcases lt_or_ge b (eps0.{u} * (ω : Ordinal.{u}) ^ b) with hb | hb
  · exact hb
  · exact absurd h (not_lt.mpr
      (Ordinal.nfp_le_fp eps0_mul_opow_monotone (by simp : (0 : Ordinal.{u}) ≤ b) hb))

theorem eps0_mul_opow_lt_eps1 {b : Ordinal.{u}} (h : b < eps1) : eps0.{u} * ω ^ b < eps1 := by
  obtain ⟨n, hn⟩ := Ordinal.lt_nfp_iff.mp h
  refine lt_of_lt_of_le ?_ (Ordinal.iterate_le_nfp
    (fun x => eps0.{u} * (ω : Ordinal.{u}) ^ x) 0 (n + 1))
  rw [Function.iterate_succ_apply']
  exact (mul_lt_mul_iff_of_pos_left eps0_pos).mpr
    ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr hn)

/-- **`ψ_0(Ω + a) = ε₀ · ω^a` below `ε₁`.**  At `a = 0` that is
`ψ_0(Ω) = ε₀`, and each step up multiplies by `ω`. -/
theorem psi_Omega_add_eq : ∀ a : Ordinal.{u}, a < eps1 → psi (Ω_ 1 + a) 0 = eps0.{u} * ω ^ a := by
  intro a
  induction a using WellFoundedLT.induction with
  | _ a IH =>
    intro ha
    have hG : a ≤ psi (Ω_ 1 + a) 0 := by
      by_contra hc
      have hb : psi (Ω_ 1 + a) 0 < a := not_le.mp hc
      have h1 := IH (psi (Ω_ 1 + a) 0) hb (lt_trans hb ha)
      have h2 : psi (Ω_ 1 + psi (Ω_ 1 + a) 0) 0 ≤ psi (Ω_ 1 + a) 0 :=
        psi_mono 0 ((add_le_add_iff_left _).mpr hb.le)
      rw [h1] at h2
      exact absurd h2 (not_le.mpr (lt_eps0_mul_opow_self (lt_trans hb ha)))
    have hOmega : (Ω_ 1 : Ordinal.{u}) ∈ CSet 0 (Ω_ 1 + a) := by
      have h1 : (1 : Ordinal.{u}) ∈ CSet 0 (Ω_ 1 + a) := by
        have := CSet.psi_mem (v := 0) (a := Ω_ 1 + a) (u := 0) (e := 0)
          (by exact lt_of_lt_of_le (Omega_pos 1) (self_le_add_right _ _))
          (CSet.zero_mem 0 _) (CSet.zero_mem 0 _)
        rwa [psi_zero_arg, Omega_zero] at this
      have := CSet.psi_mem (v := 0) (a := Ω_ 1 + a) (u := 1) (e := 0)
        (by exact lt_of_lt_of_le (Omega_pos 1) (self_le_add_right _ _)) h1 (CSet.zero_mem 0 _)
      rwa [psi_zero_arg] at this
    have hpow : ∀ b : Ordinal.{u}, b < a → eps0.{u} * (ω : Ordinal.{u}) ^ b ∈ CSet 0 (Ω_ 1 + a) := by
      intro b hb
      have hbmem : b ∈ CSet 0 (Ω_ 1 + a) := mem_CSet_of_lt_psi (lt_of_lt_of_le hb hG)
      have := CSet.psi_mem (v := 0) (a := Ω_ 1 + a) (u := 0) (e := Ω_ 1 + b)
        ((add_lt_add_iff_left _).mpr hb) (CSet.zero_mem 0 _) (CSet.add_mem hOmega hbmem)
      rwa [IH b hb (lt_trans hb ha)] at this
    refine le_antisymm (psi_Omega_add_le a) ?_
    by_contra hc
    refine psi_notMem (Ω_ 1 + a) 0 ?_
    refine mem_of_lt_mul_opow eps0.{u} eps0_pos (fun z hz => ?_)
      (fun _ hx _ hy => CSet.add_mem hx hy) hpow _ (not_le.mp hc)
    exact mem_CSet_of_lt_psi (lt_of_lt_of_le hz (le_trans (le_of_eq psi_Omega_one.symm)
      (psi_mono 0 (self_le_add_right _ _))))

theorem omega0_le_eps0 : (ω : Ordinal.{u}) ≤ eps0.{u} := by
  refine le_trans (le_of_eq ?_) (Ordinal.iterate_le_nfp (fun x => (ω : Ordinal.{u}) ^ x) 0 2)
  rw [Function.iterate_succ_apply', Function.iterate_one, Ordinal.opow_zero, Ordinal.opow_one]

theorem one_lt_eps0 : 1 < eps0.{u} := lt_of_lt_of_le Ordinal.one_lt_omega0 omega0_le_eps0

theorem eps0_le_eps1 : eps0.{u} ≤ eps1.{u} := by
  refine le_trans (le_of_eq ?_) (Ordinal.iterate_le_nfp
    (fun x => eps0.{u} * (ω : Ordinal.{u}) ^ x) 0 1)
  rw [Function.iterate_one, Ordinal.opow_zero, mul_one]

theorem one_lt_eps1 : 1 < eps1.{u} := lt_of_lt_of_le one_lt_eps0 eps0_le_eps1

/-- **`ψ_0(Ω + 1) = ε₀·ω`** — the first value above `ε₀`. -/
theorem psi_Omega_add_one : psi (Ω_ 1 + 1) 0 = eps0.{u} * ω := by
  rw [psi_Omega_add_eq 1 one_lt_eps1, Ordinal.opow_one]

end Googology.Notation.ExBuchholz.Ord
