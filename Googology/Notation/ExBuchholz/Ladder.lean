import Googology.Notation.ExBuchholz.Eps

/-!
# `ψ_0(Ω·(1+γ)) = ε_γ` at every `γ`

`Eps.lean` climbs the ladder `ψ_0(Ω·(n+1)) = ε_n` one finite rung at a time,
and stops at `Ω·ω`.  This file replaces the ladder by the ε function itself:
`eps γ` is `Ordinal.deriv (ω ^ ·) γ`, the `γ`-th fixed point of `ω ^ ·`, and
the theorem is `ψ_0(Ω·(1+γ)) = eps γ` with no restriction on `γ`.

What makes the transfinite step go through, where the finite ladder needed a
decomposition of the closure, is ordinal division by `Ω`.  Every member of
`C_0(Ω·(1+γ))` has its remainder `x % Ω` below `eps γ` — that single statement
is what the induction on the derivation proves, and the collapse clause reads
the argument `e` as `Ω·δ + β` with `β = e % Ω`, so the recursion at `δ` and
the bound on `β` are both in hand.  A collapse with a nonzero subscript is
additively principal and at least `Ω`, so its remainder is `0`; nothing has to
be known about which ordinals `ψ_1` reaches.
-/

namespace Googology.Notation.ExBuchholz.Ord

open Ordinal Cardinal Set

/-! ### The ε function -/

/-- `ε_γ`, the `γ`-th fixed point of `ω ^ ·`. -/
noncomputable def eps (γ : Ordinal.{u}) : Ordinal.{u} :=
  Ordinal.deriv (fun x : Ordinal.{u} => (ω : Ordinal.{u}) ^ x) γ

theorem opow_eps (γ : Ordinal.{u}) : (ω : Ordinal.{u}) ^ eps.{u} γ = eps.{u} γ :=
  Ordinal.deriv_fp (Ordinal.isNormal_opow Ordinal.one_lt_omega0) γ

theorem eps_zero : eps.{u} 0 = eps0.{u} :=
  Ordinal.deriv_zero_right _

theorem eps_strictMono : StrictMono (eps.{u}) := Ordinal.deriv_strictMono _

theorem eps_mono {a b : Ordinal.{u}} (h : a ≤ b) : eps.{u} a ≤ eps.{u} b :=
  eps_strictMono.monotone h

theorem eps_pos (γ : Ordinal.{u}) : 0 < eps.{u} γ := by
  refine lt_of_lt_of_le eps0_pos ?_
  rw [← eps_zero]
  exact eps_mono (by simp)

theorem isPrincipal_add_eps (γ : Ordinal.{u}) : Ordinal.IsPrincipal (· + ·) (eps.{u} γ) := by
  conv_rhs => rw [← opow_eps γ]
  exact Ordinal.isPrincipal_add_omega0_opow _

theorem isPrincipal_mul_eps (γ : Ordinal.{u}) : Ordinal.IsPrincipal (· * ·) (eps.{u} γ) := by
  have := Ordinal.isPrincipal_mul_omega0_opow_opow (eps.{u} γ)
  rwa [opow_eps γ, opow_eps γ] at this

/-- **`ε_γ` is closed under `ω ^ ·`.** -/
theorem opow_lt_eps {γ b : Ordinal.{u}} (h : b < eps.{u} γ) : (ω : Ordinal.{u}) ^ b < eps.{u} γ := by
  conv_rhs => rw [← opow_eps γ]
  exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr h

/-- **`ε_γ` is closed under multiplication.** -/
theorem mul_lt_eps {γ a b : Ordinal.{u}} (ha : a < eps.{u} γ) (hb : b < eps.{u} γ) :
    a * b < eps.{u} γ := isPrincipal_mul_eps γ ha hb

theorem self_le_eps (γ : Ordinal.{u}) : γ ≤ eps.{u} γ := eps_strictMono.le_apply

/-- **The next level is the tower of `ε_γ · ω^·`**, which is how `Eps.lean`
builds it. -/
theorem eps_add_one (γ : Ordinal.{u}) :
    eps.{u} (γ + 1) = Ordinal.nfp (fun x => eps.{u} γ * (ω : Ordinal.{u}) ^ x) 0 := by
  have hlt : eps.{u} γ < eps.{u} (γ + 1) := eps_strictMono (by simp)
  have hfp : eps.{u} γ * (ω : Ordinal.{u}) ^ eps.{u} (γ + 1) = eps.{u} (γ + 1) := by
    conv_lhs => rw [← opow_eps γ, opow_eps (γ + 1), ← opow_eps (γ + 1), ← Ordinal.opow_add,
      Ordinal.IsPrincipal.add_eq_right (isPrincipal_add_eps (γ + 1)) hlt]
    exact opow_eps (γ + 1)
  refine le_antisymm ?_ (Ordinal.nfp_le_fp (mul_opow_monotone _) (by simp) (le_of_eq hfp))
  rw [eps, Ordinal.deriv_add_one]
  refine Ordinal.nfp_le_fp opow_monotone ?_ ?_
  · rw [← Order.succ_eq_add_one, Order.succ_le_iff, ← eps]
    refine lt_of_lt_of_le ?_ (Ordinal.iterate_le_nfp
      (fun x => eps.{u} γ * (ω : Ordinal.{u}) ^ x) 0 2)
    rw [Function.iterate_succ_apply', Function.iterate_one, Ordinal.opow_zero, mul_one]
    exact lt_mul_opow_self (eps_pos γ) (ne_of_gt (eps_pos γ))
  · have hfp2 : eps.{u} γ * (ω : Ordinal.{u}) ^
        Ordinal.nfp (fun x => eps.{u} γ * (ω : Ordinal.{u}) ^ x) 0
          = Ordinal.nfp (fun x => eps.{u} γ * (ω : Ordinal.{u}) ^ x) 0 :=
      Ordinal.nfp_fp (isNormal_mul_opow (eps_pos γ)) 0
    exact le_trans (Ordinal.le_mul_right _ (eps_pos γ)) (le_of_eq hfp2)

/-! ### Division by `Ω` -/

theorem opow_Omega_one : (ω : Ordinal.{u}) ^ (Ω_ 1 : Ordinal.{u}) = Ω_ 1 := by
  refine le_antisymm ?_ (Ordinal.right_le_opow _ Ordinal.one_lt_omega0)
  have hlim : Order.IsSuccLimit (Ω_ 1 : Ordinal.{u}) := by
    refine Ordinal.isSuccLimit_of_isPrincipal_add ?_ (isPrincipal_add_Omega 1)
    rw [Omega_of_ne_zero one_ne_zero]
    exact lt_of_lt_of_le Ordinal.one_lt_omega0 (omega0_le_omega 1)
  rw [Ordinal.opow_le_of_isSuccLimit (ne_of_gt omega0_pos) hlim]
  intro b hb
  refine le_of_lt (lt_Omega_one_of_card_le ?_)
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [Ordinal.opow_zero, Ordinal.card_one]
    exact le_trans Cardinal.one_le_aleph0 (le_of_eq Cardinal.aleph_zero.symm)
  · rw [Ordinal.card_omega0_opow hb0, Cardinal.aleph_zero]
    exact max_le (le_refl _) (by
      rw [← Cardinal.aleph_zero]
      exact card_le_of_lt_Omega_one hb)

/-- An additively principal ordinal at least `Ω` is a multiple of `Ω`. -/
theorem principal_mod_Omega {x : Ordinal.{u}} (hx : Ordinal.IsPrincipal (· + ·) x)
    (h : Ω_ 1 ≤ x) : x % Ω_ 1 = 0 := by
  obtain (hz | ⟨c, hc⟩) := Ordinal.isPrincipal_add_iff_zero_or_omega0_opow.mp hx
  · exact absurd (hz ▸ h) (not_le.mpr (Omega_pos 1))
  · have hc' : (ω : Ordinal.{u}) ^ c = x := hc
    have hΩc : (Ω_ 1 : Ordinal.{u}) ≤ c := by
      by_contra hcon
      have hlt : c < Ω_ 1 := not_le.mp hcon
      refine absurd h (not_le.mpr ?_)
      rw [← hc']
      conv_rhs => rw [← opow_Omega_one]
      exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr hlt
    have hsplit : (ω : Ordinal.{u}) ^ c = Ω_ 1 * (ω : Ordinal.{u}) ^ (c - Ω_ 1) := by
      conv_lhs => rw [← Ordinal.add_sub_cancel_of_le hΩc, Ordinal.opow_add, opow_Omega_one]
    rw [← hc', hsplit, Ordinal.mul_mod]

theorem add_mod_Omega_of_lt {p q : Ordinal.{u}} (h : q < Ω_ 1) :
    (p + q) % Ω_ 1 = p % Ω_ 1 + q := by
  have hsum : p + q = Ω_ 1 * (p / Ω_ 1) + (p % Ω_ 1 + q) := by
    conv_lhs => rw [← Ordinal.div_add_mod p (Ω_ 1)]
    rw [add_assoc]
  rw [hsum, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt]
  exact isPrincipal_add_Omega 1 (Ordinal.mod_lt p (ne_of_gt (Omega_pos 1))) h

theorem add_mod_Omega_of_le {p q : Ordinal.{u}} (h : Ω_ 1 ≤ q) :
    (p + q) % Ω_ 1 = q % Ω_ 1 := by
  have hc : 1 ≤ q / Ω_ 1 := by
    refine (Ordinal.mul_le_iff_le_div (ne_of_gt (Omega_pos 1))).mp ?_
    rw [mul_one]
    exact h
  have hpΩ : p + Ω_ 1 = Ω_ 1 * (p / Ω_ 1 + 1) := by
    conv_lhs => rw [← Ordinal.div_add_mod p (Ω_ 1)]
    rw [add_assoc, add_Omega_one (Ordinal.mod_lt p (ne_of_gt (Omega_pos 1))), mul_add, mul_one]
  have hsum : p + q = Ω_ 1 * (p / Ω_ 1 + 1 + (q / Ω_ 1 - 1)) + q % Ω_ 1 := by
    conv_lhs => rw [← Ordinal.div_add_mod q (Ω_ 1)]
    rw [← add_assoc]
    congr 1
    conv_lhs => rw [← Ordinal.add_sub_cancel_of_le hc, mul_add, mul_one, ← add_assoc, hpΩ]
    exact (mul_add _ _ _).symm
  rw [hsum, Ordinal.mul_add_mod_self, Ordinal.mod_mod]

/-! ### The bound -/

/-- **Every member of `C_0(Ω·(1+γ))` has remainder below `ε_γ`.**  For a
countable member that says the member itself is below `ε_γ`; for an
uncountable one it says nothing new appears below `Ω` on top of it.  The
collapse clause reads its argument as `Ω·δ + β` by division, so the recursion
at `δ` and the bound on `β` are both to hand, and a collapse with a nonzero
subscript has remainder `0`. -/
theorem mod_Omega_lt_eps : ∀ γ : Ordinal.{u}, ∀ x : Ordinal.{u},
    x ∈ CSet 0 (Ω_ 1 * (1 + γ)) → x % Ω_ 1 < eps.{u} γ := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | _ γ IH =>
    have hbase : ∀ δ : Ordinal.{u}, δ < γ → ∀ x : Ordinal.{u},
        x ∈ CSet 0 (Ω_ 1 * (1 + δ)) → x.card ≤ ℵ_ 0 → x < eps.{u} δ := by
      intro δ hδ x hx hcard
      have h := IH δ hδ x hx
      rwa [Ordinal.mod_eq_of_lt (lt_Omega_one_of_card_le hcard)] at h
    have hle : ∀ δ : Ordinal.{u}, δ < γ → ∀ β : Ordinal.{u},
        psi (Ω_ 1 * (1 + δ) + β) 0 ≤ eps.{u} δ * ω ^ β := fun δ hδ =>
      psi_add_le (psi_le_of_bound (hbase δ hδ)) (opow_eps δ) (eps_pos δ) (hbase δ hδ)
    intro x hx
    induction hx with
    | @small y h =>
      rw [Omega_zero, Order.lt_one_iff] at h
      rw [h]
      simpa using eps_pos γ
    | @add p q _ _ ihp ihq =>
      rcases lt_or_ge q (Ω_ 1) with hq | hq
      · rw [add_mod_Omega_of_lt hq]
        refine isPrincipal_add_eps γ ihp ?_
        rwa [Ordinal.mod_eq_of_lt hq] at ihq
      · rw [add_mod_Omega_of_le hq]
        exact ihq
    | @coll u e _ _ _ ihe =>
      rcases eq_or_ne u 0 with rfl | hu
      · rw [Ordinal.mod_eq_of_lt (psi_zero_lt_Omega_one e.1)]
        have hdm : Ω_ 1 * (e.1 / Ω_ 1) + e.1 % Ω_ 1 = e.1 := Ordinal.div_add_mod e.1 (Ω_ 1)
        have hdlt : e.1 / Ω_ 1 < 1 + γ :=
          (Ordinal.lt_mul_iff_div_lt (ne_of_gt (Omega_pos 1))).mp e.2
        rcases eq_or_ne (e.1 / Ω_ 1) 0 with hd0 | hd0
        · have hsmall : e.1 < Ω_ 1 := by
            rw [hd0, mul_zero, zero_add] at hdm
            rw [← hdm]
            exact Ordinal.mod_lt _ (ne_of_gt (Omega_pos 1))
          have he : e.1 < eps.{u} γ := by
            have h := ihe
            rwa [Ordinal.mod_eq_of_lt hsmall] at h
          exact lt_of_le_of_lt (psi_zero_le_opow e.1) (opow_lt_eps he)
        · obtain ⟨δ, hδ⟩ : ∃ δ : Ordinal.{u}, e.1 / Ω_ 1 = 1 + δ :=
            ⟨e.1 / Ω_ 1 - 1, (Ordinal.add_sub_cancel_of_le
              (Order.one_le_iff_ne_zero.mpr hd0)).symm⟩
          have hδγ : δ < γ := by
            rw [hδ] at hdlt
            exact (add_lt_add_iff_left 1).mp hdlt
          have heq : Ω_ 1 * (1 + δ) + e.1 % Ω_ 1 = e.1 := by rw [← hδ, hdm]
          rw [← heq]
          refine lt_of_le_of_lt (hle δ hδγ _) ?_
          exact mul_lt_eps (eps_strictMono hδγ) (opow_lt_eps ihe)
      · have hΩle : (Ω_ 1 : Ordinal.{u}) ≤ psi e.1 u :=
          le_trans (Omega_mono (Order.one_le_iff_ne_zero.mpr hu)) (Omega_le_psi e.1 u)
        rw [principal_mod_Omega (isPrincipal_add_psi e.1 u) hΩle]
        exact eps_pos γ

/-- **Every countable member of `C_0(Ω·(1+γ))` is below `ε_γ`.** -/
theorem lt_eps_of_mem_CSet (γ : Ordinal.{u}) {x : Ordinal.{u}}
    (hx : x ∈ CSet 0 (Ω_ 1 * (1 + γ))) (hc : x.card ≤ ℵ_ 0) : x < eps.{u} γ := by
  have h := mod_Omega_lt_eps γ x hx
  rwa [Ordinal.mod_eq_of_lt (lt_Omega_one_of_card_le hc)] at h

/-- **`ψ_0(Ω·(1+γ)) ≤ ε_γ`**, with no condition on `γ`. -/
theorem psi_Omega_mul_le (γ : Ordinal.{u}) : psi (Ω_ 1 * (1 + γ)) 0 ≤ eps.{u} γ :=
  psi_le_of_bound (fun _ hx hc => lt_eps_of_mem_CSet γ hx hc)

/-- **`ψ_0(Ω·(1+γ) + β) ≤ ε_γ · ω^β`**, with no condition on either. -/
theorem psi_Omega_mul_add_le (γ β : Ordinal.{u}) :
    psi (Ω_ 1 * (1 + γ) + β) 0 ≤ eps.{u} γ * ω ^ β :=
  psi_add_le (psi_Omega_mul_le γ) (opow_eps γ) (eps_pos γ)
    (fun _ hx hc => lt_eps_of_mem_CSet γ hx hc) β

/-! ### `Ω·μ` inside the closure -/

theorem mul_natCast_mem_CSet {b y : Ordinal.{u}} (hy : y ∈ CSet 0 b) :
    ∀ n : ℕ, y * (n : Ordinal.{u}) ∈ CSet 0 b := by
  intro n
  induction n with
  | zero => rw [Nat.cast_zero, mul_zero]; exact CSet.zero_mem 0 b
  | succ m ih => rw [Nat.cast_succ, mul_add_one]; exact CSet.add_mem ih hy

theorem one_mem_CSet {b : Ordinal.{u}} (hb : 0 < b) : (1 : Ordinal.{u}) ∈ CSet 0 b := by
  have := CSet.psi_mem (v := 0) (a := b) (u := 0) (e := 0) hb
    (CSet.zero_mem 0 b) (CSet.zero_mem 0 b)
  rwa [psi_zero_arg, Omega_zero] at this

/-- **`Ω·μ` is in the closure** whenever every ordinal up to `μ` is, and `μ`
is countable.  Cantor normal form: `Ω·ω^e` is `ψ_1(e)`, and the rest is a
finite sum. -/
theorem Omega_mul_mem_CSet {b : Ordinal.{u}} (hb : 0 < b) : ∀ μ : Ordinal.{u}, μ < fpOmega 1 →
    (∀ e : Ordinal.{u}, e ≤ μ → e ∈ CSet 0 b) → (∀ e : Ordinal.{u}, e ≤ μ → e < b) →
      (Ω_ 1 : Ordinal.{u}) * μ ∈ CSet 0 b := by
  intro μ
  induction μ using WellFoundedLT.induction with
  | _ μ IH =>
    intro hμΩ hall hlt
    rcases eq_or_ne μ 0 with rfl | h0
    · rw [mul_zero]
      exact CSet.zero_mem 0 b
    · have hL : Ordinal.log (ω : Ordinal.{u}) μ ≤ μ := Ordinal.log_le_self _ _
      obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp (Ordinal.div_opow_log_lt μ Ordinal.one_lt_omega0)
      have hdm := Ordinal.div_add_mod μ ((ω : Ordinal.{u}) ^ Ordinal.log ω μ)
      rw [hn] at hdm
      have hrlt : μ % (ω : Ordinal.{u}) ^ Ordinal.log ω μ < μ :=
        lt_of_lt_of_le (Ordinal.mod_lt μ (ne_of_gt (Ordinal.opow_pos _ omega0_pos)))
          (Ordinal.opow_log_le_self _ h0)
      have hpsi : (Ω_ 1 : Ordinal.{u}) * (ω : Ordinal.{u}) ^ Ordinal.log ω μ
          = psi (Ordinal.log (ω : Ordinal.{u}) μ) 1 :=
        (psi_one_eq (lt_of_le_of_lt hL hμΩ)).symm
      have hpmem : psi (Ordinal.log (ω : Ordinal.{u}) μ) 1 ∈ CSet 0 b :=
        CSet.psi_mem (hlt _ hL) (one_mem_CSet hb) (hall _ hL)
      have hfirst : (Ω_ 1 : Ordinal.{u}) * (ω : Ordinal.{u}) ^ Ordinal.log ω μ
          * (n : Ordinal.{u}) ∈ CSet 0 b := by
        rw [hpsi]
        exact mul_natCast_mem_CSet hpmem n
      have hrest : (Ω_ 1 : Ordinal.{u}) * (μ % (ω : Ordinal.{u}) ^ Ordinal.log ω μ)
          ∈ CSet 0 b :=
        IH _ hrlt (lt_trans hrlt hμΩ) (fun e he => hall e (le_trans he hrlt.le))
          (fun e he => hlt e (le_trans he hrlt.le))
      have hsplit : (Ω_ 1 : Ordinal.{u}) * μ
          = Ω_ 1 * (ω : Ordinal.{u}) ^ Ordinal.log ω μ * (n : Ordinal.{u})
            + Ω_ 1 * (μ % (ω : Ordinal.{u}) ^ Ordinal.log ω μ) := by
        conv_lhs => rw [← hdm]
        rw [mul_add, mul_assoc]
      rw [hsplit]
      exact CSet.add_mem hfirst hrest

/-! ### The equality -/

/-- `ζ₀`, the first fixed point of the ε function. -/
noncomputable def zeta0 : Ordinal.{u} := Ordinal.nfp eps.{u} 0

theorem lt_eps_self {γ : Ordinal.{u}} (h : γ < zeta0.{u}) : γ < eps.{u} γ := by
  rcases lt_or_ge γ (eps.{u} γ) with hb | hb
  · exact hb
  · exact absurd h (not_lt.mpr (Ordinal.nfp_le_fp eps_strictMono.monotone (by simp) hb))

theorem one_lt_eps (γ : Ordinal.{u}) : 1 < eps.{u} γ := by
  refine lt_of_lt_of_le one_lt_eps0 ?_
  rw [← eps_zero]
  exact eps_mono (by simp)

theorem one_add_lt_eps {γ : Ordinal.{u}} (h : γ < eps.{u} γ) : 1 + γ < eps.{u} γ :=
  isPrincipal_add_eps γ (one_lt_eps γ) h

theorem eps_limit {γ : Ordinal.{u}} (h : Order.IsSuccLimit γ) :
    eps.{u} γ = ⨆ a : {a : Ordinal.{u} // a < γ}, eps.{u} a.1 :=
  Ordinal.deriv_limit _ h

theorem Omega_le_Omega_mul (μ : Ordinal.{u}) (h : 1 ≤ μ) : (Ω_ 1 : Ordinal.{u}) ≤ Ω_ 1 * μ := by
  conv_lhs => rw [← mul_one (Ω_ 1 : Ordinal.{u})]
  exact mul_le_mul_right h _

/-- **`ψ_0(Ω·(1+γ)) = ε_γ`**, for every `γ` below the first fixed point of the
ε function and with `ε_γ` countable.  Both conditions are needed: at a fixed
point the argument `Ω·(1+γ)` is no longer inside its own closure, and above
`Ω` the collapse cannot reach `ε_γ` at all. -/
theorem psi_Omega_mul_eq : ∀ γ : Ordinal.{u}, γ < zeta0.{u} → eps.{u} γ < Ω_ 1 →
    psi (Ω_ 1 * (1 + γ)) 0 = eps.{u} γ := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | _ γ IH =>
    intro hz hc
    refine le_antisymm (psi_Omega_mul_le γ) ?_
    have key : ∀ x : Ordinal.{u}, x < eps.{u} γ → x ∈ CSet 0 (Ω_ 1 * (1 + γ)) := by
      rcases Ordinal.zero_or_succ_or_isSuccLimit γ with rfl | ⟨δ, hδeq⟩ | hlim
      · intro x hx
        rw [add_zero, mul_one]
        refine mem_CSet_of_lt_psi ?_
        rw [psi_Omega_one, ← eps_zero]
        exact hx
      · subst hδeq
        rw [Order.succ_eq_add_one] at *
        have hδlt : δ < δ + 1 := by simp
        have hδz : δ < zeta0.{u} := lt_trans hδlt hz
        have hδc : eps.{u} δ < Ω_ 1 := lt_trans (eps_strictMono hδlt) hc
        have hIH : psi (Ω_ 1 * (1 + δ)) 0 = eps.{u} δ := IH δ hδlt hδz hδc
        have h1δ : 1 + δ < eps.{u} δ := one_add_lt_eps (lt_eps_self hδz)
        have hΩ1δ : 1 + δ < Ω_ 1 := lt_trans h1δ hδc
        have hbound : Ω_ 1 * (1 + (δ + 1)) = Ω_ 1 * (1 + δ) + Ω_ 1 := by
          rw [show (1 : Ordinal.{u}) + (δ + 1) = (1 + δ) + 1 from (add_assoc 1 δ 1).symm,
            mul_add_one]
        have hmono : Ω_ 1 * (1 + δ) ≤ Ω_ 1 * (1 + (δ + 1)) :=
          mul_le_mul_right ((add_le_add_iff_left 1).mpr (by simp)) _
        have hsmall : ∀ z : Ordinal.{u}, z < eps.{u} δ →
            z ∈ CSet 0 (Ω_ 1 * (1 + (δ + 1))) := fun z hz' =>
          CSet_mono 0 hmono (mem_CSet_of_lt_psi (by rw [hIH]; exact hz'))
        have hAmem : ∀ a : Ordinal.{u},
            (Ω_ 1 : Ordinal.{u}) * (1 + δ) ∈ CSet 0 (Ω_ 1 * (1 + δ) + a) := by
          intro a
          have hpos : (0 : Ordinal.{u}) < Ω_ 1 * (1 + δ) + a :=
            lt_of_lt_of_le (Omega_pos 1) (le_trans (Omega_le_Omega_mul _ (by simp))
              (self_le_add_right _ _))
          refine Omega_mul_mem_CSet hpos (1 + δ)
            (lt_of_lt_of_le hΩ1δ (Omega_le_fpOmega 1)) (fun e he => ?_) (fun e he => ?_)
          · refine mem_CSet_of_lt_psi (lt_of_le_of_lt he (lt_of_lt_of_le h1δ ?_))
            rw [← hIH]
            exact psi_mono 0 (self_le_add_right _ _)
          · exact lt_of_le_of_lt he (lt_of_lt_of_le hΩ1δ
              (le_trans (Omega_le_Omega_mul _ (by simp)) (self_le_add_right _ _)))
        have hEq : ∀ b : Ordinal.{u}, b < eps.{u} (δ + 1) →
            psi (Ω_ 1 * (1 + δ) + b) 0 = eps.{u} δ * ω ^ b := by
          intro b hb
          rw [eps_add_one] at hb
          exact psi_add_eq (le_of_eq hIH.symm) (eps_pos δ)
            (fun c => psi_Omega_mul_add_le δ c) hAmem b hb
        have hiter : ∀ m : ℕ, ∀ b : Ordinal.{u},
            b < (fun x => eps.{u} δ * (ω : Ordinal.{u}) ^ x)^[m] 0 →
              b ∈ CSet 0 (Ω_ 1 * (1 + (δ + 1))) := by
          intro m
          induction m with
          | zero =>
            intro b hb
            rw [Function.iterate_zero_apply] at hb
            exact absurd hb (by simp)
          | succ k ihk =>
            intro b hb
            rw [Function.iterate_succ_apply'] at hb
            refine mem_of_lt_mul_opow (eps.{u} δ) (eps_pos δ) hsmall
              (fun _ h1 _ h2 => CSet.add_mem h1 h2) (fun c hc' => ?_) b hb
            have hcmem : c ∈ CSet 0 (Ω_ 1 * (1 + (δ + 1))) := ihk c hc'
            have hclt : c < eps.{u} (δ + 1) := by
              rw [eps_add_one]
              exact lt_of_lt_of_le hc' (Ordinal.iterate_le_nfp _ 0 k)
            have hcΩ : c < Ω_ 1 := lt_trans hclt hc
            have hargs : Ω_ 1 * (1 + δ) + c < Ω_ 1 * (1 + (δ + 1)) := by
              rw [hbound, add_lt_add_iff_left]
              exact hcΩ
            have hamem : Ω_ 1 * (1 + δ) + c ∈ CSet 0 (Ω_ 1 * (1 + (δ + 1))) := by
              refine CSet.add_mem ?_ hcmem
              have := hAmem (Ω_ 1 : Ordinal.{u})
              rwa [← hbound] at this
            have hmem := CSet.psi_mem (v := 0) (a := Ω_ 1 * (1 + (δ + 1))) (u := 0)
              (e := Ω_ 1 * (1 + δ) + c) hargs (CSet.zero_mem _ _) hamem
            rwa [hEq c hclt] at hmem
        intro x hx
        rw [eps_add_one] at hx
        obtain ⟨m, hm⟩ := Ordinal.lt_nfp_iff.mp hx
        exact hiter m x hm
      · intro x hx
        haveI : Small.{u} {a : Ordinal.{u} // a < γ} := Ordinal.small_Iio γ
        rw [eps_limit hlim] at hx
        obtain ⟨⟨δ, hδ⟩, hxδ⟩ := Ordinal.lt_iSup_iff.mp hx
        have hIH := IH δ hδ (lt_trans hδ hz) (lt_trans (eps_strictMono hδ) hc)
        refine CSet_mono 0 ?_ (mem_CSet_of_lt_psi (by rw [hIH]; exact hxδ))
        exact mul_le_mul_right ((add_le_add_iff_left 1).mpr hδ.le) _
    by_contra hcon
    exact psi_notMem _ 0 (key _ (not_le.mp hcon))

/-! ### `ζ₀` is countable

Everything above needs `ε_γ` to be countable, and that is a fact about the ε
function, not a condition: `Cardinal.deriv_lt_ord` says a normal function's
derivative stays below a regular cardinal when the function does, and `ℵ₁` is
regular.  So `ε` maps the countable ordinals into themselves, `ε_{Ω} = Ω`, and
`ζ₀`, the first fixed point, is countable as well. -/

theorem isSuccLimit_Omega_one : Order.IsSuccLimit (Ω_ 1 : Ordinal.{u}) := by
  refine Ordinal.isSuccLimit_of_isPrincipal_add ?_ (isPrincipal_add_Omega 1)
  rw [Omega_of_ne_zero one_ne_zero]
  exact lt_of_lt_of_le Ordinal.one_lt_omega0 (omega0_le_omega 1)

theorem opow_lt_Omega_one {i : Ordinal.{u}} (h : i < Ω_ 1) :
    (ω : Ordinal.{u}) ^ i < Ω_ 1 := by
  refine lt_Omega_one_of_card_le ?_
  rcases eq_or_ne i 0 with rfl | h0
  · rw [Ordinal.opow_zero, Ordinal.card_one]
    exact le_trans Cardinal.one_le_aleph0 (le_of_eq Cardinal.aleph_zero.symm)
  · rw [Ordinal.card_omega0_opow h0, Cardinal.aleph_zero]
    exact max_le (le_refl _) (by
      rw [← Cardinal.aleph_zero]
      exact card_le_of_lt_Omega_one h)

theorem Omega_one_eq_ord : (Ω_ 1 : Ordinal.{u}) = (ℵ_ 1 : Cardinal.{u}).ord := by
  rw [Omega_of_ne_zero one_ne_zero, ← Cardinal.ord_aleph]

/-- **`ε` takes countable ordinals to countable ordinals.** -/
theorem eps_lt_Omega_one {γ : Ordinal.{u}} (h : γ < Ω_ 1) : eps.{u} γ < Ω_ 1 := by
  have hf : ∀ i : Ordinal.{u}, i < (ℵ_ 1 : Cardinal.{u}).ord →
      (ω : Ordinal.{u}) ^ i < (ℵ_ 1 : Cardinal.{u}).ord := by
    intro i hi
    rw [← Omega_one_eq_ord] at hi ⊢
    exact opow_lt_Omega_one hi
  rw [eps, Omega_one_eq_ord]
  refine Cardinal.deriv_lt_ord Cardinal.isRegular_aleph_one ?_ hf ?_
  · exact ne_of_gt Cardinal.aleph0_lt_aleph_one
  · rw [← Omega_one_eq_ord]
    exact h

/-- **`ε_Ω = Ω`**: the countable ε-numbers are exactly `Ω` many. -/
theorem eps_Omega_one : eps.{u} (Ω_ 1) = Ω_ 1 := by
  refine le_antisymm ?_ (self_le_eps _)
  rw [eps_limit isSuccLimit_Omega_one]
  exact Ordinal.iSup_le (fun a => (eps_lt_Omega_one a.2).le)

theorem zeta0_le_Omega_one : zeta0.{u} ≤ Ω_ 1 :=
  Ordinal.nfp_le_fp eps_strictMono.monotone (by simp) (le_of_eq eps_Omega_one)

theorem eps_lt_Omega_one_of_lt_zeta0 {γ : Ordinal.{u}} (h : γ < zeta0.{u}) :
    eps.{u} γ < Ω_ 1 :=
  eps_lt_Omega_one (lt_of_lt_of_le h zeta0_le_Omega_one)

/-- **`ψ_0(Ω·(1+γ)) = ε_γ` for every `γ` below `ζ₀`.**  Below the first fixed
point of the ε function, and no further: at `ζ₀` itself the argument
`Ω·(1+ζ₀)` is no longer inside its own closure. -/
theorem psi_Omega_mul_eps {γ : Ordinal.{u}} (h : γ < zeta0.{u}) :
    psi (Ω_ 1 * (1 + γ)) 0 = eps.{u} γ :=
  psi_Omega_mul_eq γ h (eps_lt_Omega_one_of_lt_zeta0 h)

/-- **`ψ_0(Ω·(1+γ) + β) = ε_γ · ω^β` below `ε_{γ+1}`.** -/
theorem psi_Omega_mul_add_eps {γ : Ordinal.{u}} (h : γ < zeta0.{u}) {β : Ordinal.{u}}
    (hβ : β < eps.{u} (γ + 1)) :
    psi (Ω_ 1 * (1 + γ) + β) 0 = eps.{u} γ * ω ^ β := by
  rw [eps_add_one] at hβ
  refine psi_add_eq (le_of_eq (psi_Omega_mul_eps h).symm) (eps_pos γ)
    (fun c => psi_Omega_mul_add_le γ c) (fun a => ?_) β hβ
  have hpos : (0 : Ordinal.{u}) < Ω_ 1 * (1 + γ) + a :=
    lt_of_lt_of_le (Omega_pos 1) (le_trans (Omega_le_Omega_mul _ (by simp))
      (self_le_add_right _ _))
  have h1γ : 1 + γ < eps.{u} γ := one_add_lt_eps (lt_eps_self h)
  refine Omega_mul_mem_CSet hpos (1 + γ)
    (lt_trans h1γ (lt_of_lt_of_le (eps_lt_Omega_one_of_lt_zeta0 h) (Omega_le_fpOmega 1)))
    (fun e he => ?_) (fun e he => ?_)
  · refine mem_CSet_of_lt_psi (lt_of_le_of_lt he (lt_of_lt_of_le h1γ ?_))
    rw [← psi_Omega_mul_eps h]
    exact psi_mono 0 (self_le_add_right _ _)
  · exact lt_of_le_of_lt he (lt_of_lt_of_le (lt_trans h1γ (eps_lt_Omega_one_of_lt_zeta0 h))
      (le_trans (Omega_le_Omega_mul _ (by simp)) (self_le_add_right _ _)))

/-! ### Agreement with the finite ladder -/

theorem eps_natCast : ∀ n : ℕ, eps.{u} (n : Ordinal.{u}) = epsN.{u} n := by
  intro n
  induction n with
  | zero => rw [Nat.cast_zero, eps_zero, epsN_zero]
  | succ m ih => rw [Nat.cast_succ, eps_add_one, ih, epsN_succ]

theorem OmegaMul_succ_eq (n : ℕ) :
    OmegaMul.{u} (n + 1) = Ω_ 1 * (1 + (n : Ordinal.{u})) := by
  rw [OmegaMul, show ((n + 1 : ℕ) : Ordinal.{u}) = ((1 + n : ℕ) : Ordinal.{u}) from by
    rw [Nat.add_comm], Nat.cast_add, Nat.cast_one]

/-- The two developments agree: `Eps.lean`'s `ψ_0(Ω·(n+1)) = ε_n` is this
file's theorem at a finite `γ`. -/
theorem psi_OmegaMul_eq_eps (n : ℕ) :
    psi (OmegaMul.{u} (n + 1)) 0 = eps.{u} (n : Ordinal.{u}) := by
  rw [eps_natCast, psi_OmegaMul]

theorem eps_lt_zeta0 {γ : Ordinal.{u}} (h : γ < zeta0.{u}) : eps.{u} γ < zeta0.{u} := by
  obtain ⟨n, hn⟩ := Ordinal.lt_nfp_iff.mp h
  refine lt_of_lt_of_le ?_ (Ordinal.iterate_le_nfp eps.{u} 0 (n + 1))
  rw [Function.iterate_succ_apply']
  exact eps_strictMono hn

/-- `ε_ω` is the limit of the finite levels, so `Eps.lean`'s `epsW` is this
file's `eps ω`. -/
theorem eps_omega0 : eps.{u} (ω : Ordinal.{u}) = epsW.{u} := by
  refine le_antisymm ?_ (Ordinal.iSup_le (fun n => ?_))
  · rw [eps_limit Ordinal.isSuccLimit_omega0]
    refine Ordinal.iSup_le (fun a => ?_)
    obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp a.2
    rw [show a.1 = (n : Ordinal.{u}) from hn, eps_natCast]
    exact epsN_le_epsW n
  · rw [← eps_natCast n]
    exact eps_mono (le_of_lt (Ordinal.natCast_lt_omega0 n))

/-- And `ψ_0(Ω·ω) = ε_ω` is the ladder at `γ = ω`. -/
theorem psi_Omega_omega_eq_eps : psi ((Ω_ 1 : Ordinal.{u}) * ω) 0 = eps.{u} (ω : Ordinal.{u}) := by
  rw [eps_omega0, psi_Omega_omega]

/-- **Every fixed point of `ω ^ ·` is an `ε_γ`.**  So the level of an ordinal
is available without constructing it: a term-building recursion that meets an
ε-number can ask for its index. -/
theorem exists_eps_index {α : Ordinal.{u}} (h : (ω : Ordinal.{u}) ^ α = α) :
    ∃ γ : Ordinal.{u}, eps.{u} γ = α :=
  (Ordinal.le_iff_deriv (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mp (le_of_eq h)

/-- And below `ζ₀` that index is smaller than the ordinal itself. -/
theorem eps_index_lt {γ : Ordinal.{u}} (h : eps.{u} γ < zeta0.{u}) : γ < eps.{u} γ :=
  lt_eps_self (lt_of_le_of_lt (self_le_eps γ) h)

theorem eps0_le_zeta0 : eps0.{u} ≤ zeta0.{u} := by
  rw [← eps_zero]
  refine le_trans (le_of_eq ?_) (Ordinal.iterate_le_nfp eps.{u} 0 1)
  rw [Function.iterate_one]

/-- A fixed point of `ω ^ ·` above `ε_γ` is at least `ε_{γ+1}`. -/
theorem eps_succ_le_of_opow_fp {γ a : Ordinal.{u}} (hfp : (ω : Ordinal.{u}) ^ a = a)
    (h0 : eps.{u} γ < a) : eps.{u} (γ + 1) ≤ a := by
  obtain ⟨δ, hδ⟩ := exists_eps_index hfp
  rw [← hδ] at h0 ⊢
  exact eps_mono (Order.succ_le_of_lt (eps_strictMono.lt_iff_lt.mp h0))

/-- **Between `ε_γ` and `ε_{γ+1}` the logarithm is strictly smaller.** -/
theorem log_lt_self_of_lt_eps_succ {γ a : Ordinal.{u}} (h0 : eps.{u} γ < a)
    (h1 : a < eps.{u} (γ + 1)) : Ordinal.log (ω : Ordinal.{u}) a < a := by
  rcases lt_or_ge (Ordinal.log (ω : Ordinal.{u}) a) a with h | h
  · exact h
  · exfalso
    have heq : Ordinal.log (ω : Ordinal.{u}) a = a := le_antisymm (Ordinal.log_le_self _ _) h
    have hne : a ≠ 0 := ne_of_gt (lt_trans (eps_pos γ) h0)
    have hle : (ω : Ordinal.{u}) ^ a ≤ a := by
      conv_lhs => rw [← heq]
      exact Ordinal.opow_log_le_self _ hne
    exact absurd h1 (not_lt.mpr (eps_succ_le_of_opow_fp
      (le_antisymm hle (Ordinal.right_le_opow _ Ordinal.one_lt_omega0)) h0))

theorem isSuccLimit_eps0 : Order.IsSuccLimit eps0.{u} :=
  Ordinal.isSuccLimit_of_isPrincipal_add one_lt_eps0 isPrincipal_add_eps0

theorem eps0_lt_zeta0 : eps0.{u} < zeta0.{u} := by
  refine lt_of_lt_of_le ?_ (Ordinal.iterate_le_nfp eps.{u} 0 2)
  rw [Function.iterate_succ_apply', Function.iterate_one, ← eps_zero]
  exact eps_strictMono (by rw [eps_zero]; exact eps0_pos)

theorem one_add_eps0 : 1 + eps0.{u} = eps0.{u} :=
  Ordinal.IsPrincipal.add_eq_right isPrincipal_add_eps0 one_lt_eps0

theorem iterate_eps_lt_succ : ∀ n : ℕ, eps.{u}^[n] 0 < eps.{u}^[n + 1] 0 := by
  intro n
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply, Function.iterate_one]
    exact eps_pos 0
  | succ m ih =>
    have h := eps_strictMono ih
    rwa [← Function.iterate_succ_apply' eps.{u} m 0,
      ← Function.iterate_succ_apply' eps.{u} (m + 1) 0] at h

/-- **`ζ₀` is a limit.** -/
theorem succ_lt_zeta0 {δ : Ordinal.{u}} (h : δ < zeta0.{u}) : δ + 1 < zeta0.{u} := by
  obtain ⟨n, hn⟩ := Ordinal.lt_nfp_iff.mp h
  rw [← Order.succ_eq_add_one]
  refine lt_of_le_of_lt (Order.succ_le_of_lt hn) ?_
  exact lt_of_lt_of_le (iterate_eps_lt_succ n) (Ordinal.iterate_le_nfp eps.{u} 0 (n + 1))

/-! ### The ceiling of the two levels -/

theorem eps_zeta0 : eps.{u} zeta0.{u} = zeta0.{u} :=
  Ordinal.nfp_fp (Ordinal.isNormal_deriv _) 0

theorem omega0_le_zeta0 : (ω : Ordinal.{u}) ≤ zeta0.{u} :=
  le_trans omega0_le_eps0 (le_of_lt eps0_lt_zeta0)

theorem one_add_zeta0 : 1 + zeta0.{u} = zeta0.{u} :=
  Ordinal.one_add_of_omega0_le omega0_le_zeta0

/-- **`ψ_0(Ω·ζ₀) = ζ₀`.**  It is the first ordinal `ψ_0` and `ψ_1` together do
not name: every `ε_γ` below it is `ψ_0(Ω·(1+γ))`, and nothing gets past. -/
theorem psi_Omega_mul_zeta0 : psi ((Ω_ 1 : Ordinal.{u}) * zeta0.{u}) 0 = zeta0.{u} := by
  refine le_antisymm ?_ ?_
  · have h := psi_Omega_mul_le zeta0.{u}
    rw [one_add_zeta0, eps_zeta0] at h
    exact h
  · refine le_of_forall_lt (fun x hx => ?_)
    have hxe : x < eps.{u} x := lt_eps_self hx
    rw [← psi_Omega_mul_eps hx] at hxe
    refine lt_of_lt_of_le hxe (psi_mono 0 ?_)
    refine mul_le_mul_right ?_ _
    rw [← one_add_zeta0]
    exact (add_le_add_iff_left 1).mpr hx.le

end Googology.Notation.ExBuchholz.Ord
