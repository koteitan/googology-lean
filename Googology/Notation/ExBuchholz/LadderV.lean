import Googology.Notation.ExBuchholz.Ladder

/-!
# The ladder at every subscript

`Ladder.lean` proves `ψ_0(Ω·(1+γ)) = ε_γ` by dividing the argument by `Ω`.
Nothing in that argument is about the subscript `0`: at subscript `v` the
same proof divides by `Ω_{v+1}` and gives `ψ_v(Ω_{v+1}·(1+γ)) = ε^v_γ`, where
`ε^v` is the derivative of `x ↦ Ω_v · ω^x` — the function `Level.lean` already
shows `ψ_v` follows below its first fixed point.

`epsV v` is that derivative, so `epsV 0` is the ε function and `epsV v 0` is
`fpOmega v`.  The three clauses of the closure behave as they do at `0`: a
sum adds the `Ω_{v+1}` parts, a collapse below `v` is already below `Ω_v`, a
collapse at `v` is the recursion, and a collapse above `v` is additively
principal and at least `Ω_{v+1}`, so its remainder is `0`.
-/

namespace Googology.Notation.ExBuchholz.Ord

open Ordinal Cardinal Set

/-! ### The ε function at subscript `v` -/

/-- `ε^v_γ`: the `γ`-th fixed point of `x ↦ Ω_v · ω^x`.  At `v = 0` it is the
ε function, and at `γ = 0` it is `fpOmega v`. -/
noncomputable def epsV (v γ : Ordinal.{u}) : Ordinal.{u} :=
  Ordinal.deriv (fun x => Ω_ v * (ω : Ordinal.{u}) ^ x) γ

theorem epsV_fp (v γ : Ordinal.{u}) : Ω_ v * (ω : Ordinal.{u}) ^ epsV.{u} v γ = epsV.{u} v γ :=
  Ordinal.deriv_fp (isNormal_mul_opow (Omega_pos v)) γ

theorem epsV_zero (v : Ordinal.{u}) : epsV.{u} v 0 = fpOmega.{u} v :=
  Ordinal.deriv_zero_right _

theorem epsV_strictMono (v : Ordinal.{u}) : StrictMono (epsV.{u} v) :=
  Ordinal.deriv_strictMono _

theorem epsV_mono {v a b : Ordinal.{u}} (h : a ≤ b) : epsV.{u} v a ≤ epsV.{u} v b :=
  (epsV_strictMono v).monotone h

theorem self_le_epsV (v γ : Ordinal.{u}) : γ ≤ epsV.{u} v γ := (epsV_strictMono v).le_apply

theorem Omega_le_epsV (v γ : Ordinal.{u}) : Ω_ v ≤ epsV.{u} v γ := by
  conv_rhs => rw [← epsV_fp v γ]
  exact le_mul_opow_self _ _

theorem epsV_pos (v γ : Ordinal.{u}) : 0 < epsV.{u} v γ :=
  lt_of_lt_of_le (Omega_pos v) (Omega_le_epsV v γ)

/-- **`ε^v_γ` is a fixed point of `ω ^ ·` as well.** -/
theorem opow_epsV (v γ : Ordinal.{u}) : (ω : Ordinal.{u}) ^ epsV.{u} v γ = epsV.{u} v γ := by
  refine le_antisymm ?_ (Ordinal.right_le_opow _ Ordinal.one_lt_omega0)
  conv_rhs => rw [← epsV_fp v γ]
  exact Ordinal.le_mul_right _ (Omega_pos v)

theorem isPrincipal_add_epsV (v γ : Ordinal.{u}) :
    Ordinal.IsPrincipal (· + ·) (epsV.{u} v γ) := by
  conv_rhs => rw [← opow_epsV v γ]
  exact Ordinal.isPrincipal_add_omega0_opow _

theorem isPrincipal_mul_epsV (v γ : Ordinal.{u}) :
    Ordinal.IsPrincipal (· * ·) (epsV.{u} v γ) := by
  have := Ordinal.isPrincipal_mul_omega0_opow_opow (epsV.{u} v γ)
  rwa [opow_epsV v γ, opow_epsV v γ] at this

theorem opow_lt_epsV {v γ b : Ordinal.{u}} (h : b < epsV.{u} v γ) :
    (ω : Ordinal.{u}) ^ b < epsV.{u} v γ := by
  conv_rhs => rw [← opow_epsV v γ]
  exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr h

theorem mul_lt_epsV {v γ a b : Ordinal.{u}} (ha : a < epsV.{u} v γ) (hb : b < epsV.{u} v γ) :
    a * b < epsV.{u} v γ := isPrincipal_mul_epsV v γ ha hb

theorem Omega_lt_epsV (v γ : Ordinal.{u}) : Ω_ v < epsV.{u} v γ := by
  conv_rhs => rw [← epsV_fp v γ]
  conv_lhs => rw [← mul_one (Ω_ v : Ordinal.{u})]
  refine (mul_lt_mul_iff_of_pos_left (Omega_pos v)).mpr ?_
  rw [← Ordinal.opow_zero (ω : Ordinal.{u})]
  exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (epsV_pos v γ)

theorem Omega_mul_opow_lt_epsV {v γ b : Ordinal.{u}} (h : b < epsV.{u} v γ) :
    Ω_ v * (ω : Ordinal.{u}) ^ b < epsV.{u} v γ :=
  mul_lt_epsV (Omega_lt_epsV v γ) (opow_lt_epsV h)

/-! ### The bound -/

theorem Omega_le_Omega_succ (v : Ordinal.{u}) : (Ω_ v : Ordinal.{u}) ≤ Ω_ (v + 1) :=
  Omega_mono (le_of_lt (lt_add_one_ord v))

/-- **Every member of `C_v(Ω_{v+1}·(1+γ))` has remainder below `ε^v_γ`.**  The
proof is `Ladder.lean`'s, with the subscript left free: the collapse clause
divides its argument by `Ω_{v+1}`, a collapse below `v` is already below
`Ω_v`, and one above `v` is additively principal and at least `Ω_{v+1}`, so
its remainder is `0`. -/
theorem mod_Omega_lt_epsV (v : Ordinal.{u}) : ∀ γ : Ordinal.{u},
    ∀ x : Ordinal.{u}, x ∈ CSet v (Ω_ (v + 1) * (1 + γ)) →
      x % Ω_ (v + 1) < epsV.{u} v γ := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | _ γ IH =>
    have hbase : ∀ δ : Ordinal.{u}, δ < γ → ∀ x : Ordinal.{u},
        x ∈ CSet v (Ω_ (v + 1) * (1 + δ)) → x.card ≤ ℵ_ v → x < epsV.{u} v δ := by
      intro δ hδ x hx hcard
      have h := IH δ hδ x hx
      rwa [Ordinal.mod_eq_of_lt (lt_Omega_succ_of_card_le hcard)] at h
    have hle : ∀ δ : Ordinal.{u}, δ < γ → ∀ β : Ordinal.{u},
        psi (Ω_ (v + 1) * (1 + δ) + β) v ≤ epsV.{u} v δ * ω ^ β := fun δ hδ =>
      psi_add_le (psi_le_of_bound (hbase δ hδ)) (opow_epsV v δ) (Omega_le_epsV v δ)
        (hbase δ hδ)
    intro x hx
    induction hx with
    | @small y h =>
      rw [Ordinal.mod_eq_of_lt (lt_of_lt_of_le h (Omega_le_Omega_succ v))]
      exact lt_of_lt_of_le h (Omega_le_epsV v γ)
    | @add p q _ _ ihp ihq =>
      rcases lt_or_ge q (Ω_ (v + 1)) with hq | hq
      · rw [add_mod_Omega_of_lt hq]
        refine isPrincipal_add_epsV v γ ihp ?_
        rwa [Ordinal.mod_eq_of_lt hq] at ihq
      · rw [add_mod_Omega_of_le hq]
        exact ihq
    | @coll u e _ _ _ ihe =>
      rcases lt_or_ge u (v + 1) with hu | hu
      · have huv : u ≤ v := by
          rw [← Order.succ_eq_add_one, Order.lt_succ_iff] at hu
          exact hu
        have hsmall : psi e.1 u < Ω_ (v + 1) :=
          lt_of_lt_of_le (psi_lt_Omega_succ e.1 u) (Omega_mono (add_le_add huv (le_refl 1)))
        rw [Ordinal.mod_eq_of_lt hsmall]
        rcases eq_or_lt_of_le huv with heq | hlt
        · rw [heq]
          have hdm : Ω_ (v + 1) * (e.1 / Ω_ (v + 1)) + e.1 % Ω_ (v + 1) = e.1 :=
            Ordinal.div_add_mod e.1 (Ω_ (v + 1))
          have hdlt : e.1 / Ω_ (v + 1) < 1 + γ :=
            (Ordinal.lt_mul_iff_div_lt (ne_of_gt (Omega_pos (v + 1)))).mp e.2
          rcases eq_or_ne (e.1 / Ω_ (v + 1)) 0 with hd0 | hd0
          · have hsm : e.1 < Ω_ (v + 1) := by
              rw [hd0, mul_zero, zero_add] at hdm
              rw [← hdm]
              exact Ordinal.mod_lt _ (ne_of_gt (Omega_pos (v + 1)))
            have he : e.1 < epsV.{u} v γ := by
              have h := ihe
              rwa [Ordinal.mod_eq_of_lt hsm] at h
            exact lt_of_le_of_lt (psi_le_Omega_mul_opow e.1 v) (Omega_mul_opow_lt_epsV he)
          · obtain ⟨δ, hδ⟩ : ∃ δ : Ordinal.{u}, e.1 / Ω_ (v + 1) = 1 + δ :=
              ⟨e.1 / Ω_ (v + 1) - 1, (Ordinal.add_sub_cancel_of_le
                (Order.one_le_iff_ne_zero.mpr hd0)).symm⟩
            have hδγ : δ < γ := by
              rw [hδ] at hdlt
              exact (add_lt_add_iff_left 1).mp hdlt
            have heq2 : Ω_ (v + 1) * (1 + δ) + e.1 % Ω_ (v + 1) = e.1 := by rw [← hδ, hdm]
            rw [← heq2]
            refine lt_of_le_of_lt (hle δ hδγ _) ?_
            exact mul_lt_epsV (epsV_strictMono v hδγ) (opow_lt_epsV ihe)
        · refine lt_of_lt_of_le (psi_lt_Omega_succ e.1 u) ?_
          refine le_trans (Omega_mono ?_) (Omega_le_epsV v γ)
          rw [← Order.succ_eq_add_one]
          exact Order.succ_le_of_lt hlt
      · have hΩle : (Ω_ (v + 1) : Ordinal.{u}) ≤ psi e.1 u :=
          le_trans (Omega_mono hu) (Omega_le_psi e.1 u)
        rw [principal_mod_Omega (add_one_ne_zero_ord v) (isPrincipal_add_psi e.1 u) hΩle]
        exact epsV_pos v γ

/-- **Every member of `C_v(Ω_{v+1}·(1+γ))` of cardinality at most `ℵ_v` is
below `ε^v_γ`.** -/
theorem lt_epsV_of_mem_CSet (v γ : Ordinal.{u}) {x : Ordinal.{u}}
    (hx : x ∈ CSet v (Ω_ (v + 1) * (1 + γ))) (hc : x.card ≤ ℵ_ v) : x < epsV.{u} v γ := by
  have h := mod_Omega_lt_epsV v γ x hx
  rwa [Ordinal.mod_eq_of_lt (lt_Omega_succ_of_card_le hc)] at h

/-- **`ψ_v(Ω_{v+1}·(1+γ)) ≤ ε^v_γ`**, with no condition on `γ`. -/
theorem psi_OmegaV_mul_le (v γ : Ordinal.{u}) :
    psi (Ω_ (v + 1) * (1 + γ)) v ≤ epsV.{u} v γ :=
  psi_le_of_bound (fun _ hx hc => lt_epsV_of_mem_CSet v γ hx hc)

/-- **`ψ_v(Ω_{v+1}·(1+γ) + β) ≤ ε^v_γ · ω^β`**, with no condition. -/
theorem psi_OmegaV_mul_add_le (v γ β : Ordinal.{u}) :
    psi (Ω_ (v + 1) * (1 + γ) + β) v ≤ epsV.{u} v γ * ω ^ β :=
  psi_add_le (psi_OmegaV_mul_le v γ) (opow_epsV v γ) (Omega_le_epsV v γ)
    (fun _ hx hc => lt_epsV_of_mem_CSet v γ hx hc) β

/-! ### `Ω_{v+1}·μ` inside the closure -/

theorem succ_mem_CSet {v b : Ordinal.{u}} (hv : v < Ω_ v) (hb : 0 < b) :
    v + 1 ∈ CSet v b := by
  rcases eq_or_ne v 0 with rfl | hv0
  · have := CSet.psi_mem (v := 0) (a := b) (u := 0) (e := 0) hb
      (CSet.zero_mem 0 b) (CSet.zero_mem 0 b)
    rw [psi_zero_arg, Omega_zero] at this
    rw [zero_add]
    exact this
  · refine mem_CSet_of_lt_Omega ?_
    rw [← Order.succ_eq_add_one]
    exact (isSuccLimit_Omega hv0).succ_lt hv

theorem Omega_succ_mul_mem_CSet {v b : Ordinal.{u}} (hv : v < Ω_ v) (hv1 : v + 1 < Ω_ (v + 1))
    (hb : 0 < b) : ∀ μ : Ordinal.{u}, μ < fpOmega (v + 1) →
    (∀ e : Ordinal.{u}, e ≤ μ → e ∈ CSet v b) → (∀ e : Ordinal.{u}, e ≤ μ → e < b) →
      (Ω_ (v + 1) : Ordinal.{u}) * μ ∈ CSet v b := by
  intro μ
  induction μ using WellFoundedLT.induction with
  | _ μ IH =>
    intro hμ hall hlt
    rcases eq_or_ne μ 0 with rfl | h0
    · rw [mul_zero]
      exact CSet.zero_mem v b
    · have hL : Ordinal.log (ω : Ordinal.{u}) μ ≤ μ := Ordinal.log_le_self _ _
      obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp (Ordinal.div_opow_log_lt μ Ordinal.one_lt_omega0)
      have hdm := Ordinal.div_add_mod μ ((ω : Ordinal.{u}) ^ Ordinal.log ω μ)
      rw [hn] at hdm
      have hrlt : μ % (ω : Ordinal.{u}) ^ Ordinal.log ω μ < μ :=
        lt_of_lt_of_le (Ordinal.mod_lt μ (ne_of_gt (Ordinal.opow_pos _ omega0_pos)))
          (Ordinal.opow_log_le_self _ h0)
      have hpsi : (Ω_ (v + 1) : Ordinal.{u}) * (ω : Ordinal.{u}) ^ Ordinal.log ω μ
          = psi (Ordinal.log (ω : Ordinal.{u}) μ) (v + 1) :=
        (psi_eq_Omega_mul_opow hv1 _ (lt_of_le_of_lt hL hμ)).symm
      have hpmem : psi (Ordinal.log (ω : Ordinal.{u}) μ) (v + 1) ∈ CSet v b :=
        CSet.psi_mem (hlt _ hL) (succ_mem_CSet hv hb) (hall _ hL)
      have hfirst : (Ω_ (v + 1) : Ordinal.{u}) * (ω : Ordinal.{u}) ^ Ordinal.log ω μ
          * (n : Ordinal.{u}) ∈ CSet v b := by
        rw [hpsi]
        exact mul_natCast_mem_CSet hpmem n
      have hrest : (Ω_ (v + 1) : Ordinal.{u}) * (μ % (ω : Ordinal.{u}) ^ Ordinal.log ω μ)
          ∈ CSet v b :=
        IH _ hrlt (lt_trans hrlt hμ) (fun e he => hall e (le_trans he hrlt.le))
          (fun e he => hlt e (le_trans he hrlt.le))
      have hsplit : (Ω_ (v + 1) : Ordinal.{u}) * μ
          = Ω_ (v + 1) * (ω : Ordinal.{u}) ^ Ordinal.log ω μ * (n : Ordinal.{u})
            + Ω_ (v + 1) * (μ % (ω : Ordinal.{u}) ^ Ordinal.log ω μ) := by
        conv_lhs => rw [← hdm]
        rw [mul_add, mul_assoc]
      rw [hsplit]
      exact CSet.add_mem hfirst hrest

/-! ### Countability and the next level -/

theorem Omega_succ_eq_ord (v : Ordinal.{u}) :
    (Ω_ (v + 1) : Ordinal.{u}) = (ℵ_ (v + 1) : Cardinal.{u}).ord := by
  rw [Omega_of_ne_zero (add_one_ne_zero_ord v), ← Cardinal.ord_aleph]

theorem isRegular_aleph_succ (v : Ordinal.{u}) :
    Cardinal.IsRegular (ℵ_ (v + 1) : Cardinal.{u}) := by
  rw [← Cardinal.succ_aleph]
  exact Cardinal.isRegular_succ (Cardinal.aleph0_le_aleph v)

theorem aleph_succ_ne_aleph0 (v : Ordinal.{u}) : (ℵ_ (v + 1) : Cardinal.{u}) ≠ ℵ₀ := by
  refine ne_of_gt ?_
  rw [← Cardinal.aleph_zero]
  exact Cardinal.aleph_lt_aleph.mpr (lt_of_le_of_lt (by simp : (0:Ordinal.{u}) ≤ v)
    (lt_add_one_ord v))

theorem Omega_mul_opow_lt_Omega_succ {v i : Ordinal.{u}} (h : i < Ω_ (v + 1)) :
    Ω_ v * (ω : Ordinal.{u}) ^ i < Ω_ (v + 1) := by
  refine lt_Omega_succ_of_card_le ?_
  rw [Ordinal.card_mul]
  have h2 : ((ω : Ordinal.{u}) ^ i).card ≤ ℵ_ v := by
    rcases eq_or_ne i 0 with rfl | hi
    · rw [Ordinal.opow_zero, Ordinal.card_one]
      exact le_trans Cardinal.one_le_aleph0 (Cardinal.aleph0_le_aleph v)
    · rw [Ordinal.card_omega0_opow hi]
      exact max_le (Cardinal.aleph0_le_aleph v) (card_le_of_lt_Omega_succ h)
  exact le_trans (mul_le_mul' (card_Omega_le v) h2)
    (le_of_eq (Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph v)))

/-- **`ε^v` takes the ordinals below `Ω_{v+1}` into themselves.** -/
theorem epsV_lt_Omega_succ {v γ : Ordinal.{u}} (h : γ < Ω_ (v + 1)) :
    epsV.{u} v γ < Ω_ (v + 1) := by
  have hf : ∀ i : Ordinal.{u}, i < (ℵ_ (v + 1) : Cardinal.{u}).ord →
      Ω_ v * (ω : Ordinal.{u}) ^ i < (ℵ_ (v + 1) : Cardinal.{u}).ord := by
    intro i hi
    rw [← Omega_succ_eq_ord] at hi ⊢
    exact Omega_mul_opow_lt_Omega_succ hi
  rw [epsV, Omega_succ_eq_ord]
  refine Cardinal.deriv_lt_ord (isRegular_aleph_succ v) (aleph_succ_ne_aleph0 v) hf ?_
  rw [← Omega_succ_eq_ord]
  exact h

theorem epsV_limit {v γ : Ordinal.{u}} (h : Order.IsSuccLimit γ) :
    epsV.{u} v γ = ⨆ a : {a : Ordinal.{u} // a < γ}, epsV.{u} v a.1 :=
  Ordinal.deriv_limit _ h

theorem epsV_Omega_succ (v : Ordinal.{u}) : epsV.{u} v (Ω_ (v + 1)) = Ω_ (v + 1) := by
  refine le_antisymm ?_ (self_le_epsV v _)
  rw [epsV_limit (isSuccLimit_Omega (add_one_ne_zero_ord v))]
  exact Ordinal.iSup_le (fun a => (epsV_lt_Omega_succ a.2).le)

/-- `ζ^v`, the first fixed point of `ε^v`. -/
noncomputable def zetaV (v : Ordinal.{u}) : Ordinal.{u} := Ordinal.nfp (epsV.{u} v) 0

theorem zetaV_le_Omega_succ (v : Ordinal.{u}) : zetaV.{u} v ≤ Ω_ (v + 1) :=
  Ordinal.nfp_le_fp (epsV_strictMono v).monotone (by simp) (le_of_eq (epsV_Omega_succ v))

theorem lt_epsV_self {v γ : Ordinal.{u}} (h : γ < zetaV.{u} v) : γ < epsV.{u} v γ := by
  rcases lt_or_ge γ (epsV.{u} v γ) with hb | hb
  · exact hb
  · exact absurd h (not_lt.mpr
      (Ordinal.nfp_le_fp (epsV_strictMono v).monotone (by simp) hb))

theorem epsV_lt_Omega_succ_of_lt_zetaV {v γ : Ordinal.{u}} (h : γ < zetaV.{u} v) :
    epsV.{u} v γ < Ω_ (v + 1) :=
  epsV_lt_Omega_succ (lt_of_lt_of_le h (zetaV_le_Omega_succ v))

/-- **The next level is the tower of `ε^v_γ · ω^·`.** -/
theorem epsV_add_one (v γ : Ordinal.{u}) :
    epsV.{u} v (γ + 1) = Ordinal.nfp (fun x => epsV.{u} v γ * (ω : Ordinal.{u}) ^ x) 0 := by
  have hNfp : epsV.{u} v γ * (ω : Ordinal.{u}) ^
      Ordinal.nfp (fun x => epsV.{u} v γ * (ω : Ordinal.{u}) ^ x) 0
        = Ordinal.nfp (fun x => epsV.{u} v γ * (ω : Ordinal.{u}) ^ x) 0 :=
    Ordinal.nfp_fp (isNormal_mul_opow (epsV_pos v γ)) 0
  have hElt : epsV.{u} v γ < Ordinal.nfp (fun x => epsV.{u} v γ * (ω : Ordinal.{u}) ^ x) 0 := by
    refine lt_of_lt_of_le ?_ (Ordinal.iterate_le_nfp
      (fun x => epsV.{u} v γ * (ω : Ordinal.{u}) ^ x) 0 2)
    rw [Function.iterate_succ_apply', Function.iterate_one, Ordinal.opow_zero, mul_one]
    exact lt_mul_opow_self (epsV_pos v γ) (ne_of_gt (epsV_pos v γ))
  have hNprin : Ordinal.IsPrincipal (· + ·)
      (Ordinal.nfp (fun x => epsV.{u} v γ * (ω : Ordinal.{u}) ^ x) 0) := by
    conv_rhs => rw [← hNfp]
    exact isPrincipal_add_mul_opow (opow_epsV v γ) _
  have hEN : epsV.{u} v γ + Ordinal.nfp (fun x => epsV.{u} v γ * (ω : Ordinal.{u}) ^ x) 0
      = Ordinal.nfp (fun x => epsV.{u} v γ * (ω : Ordinal.{u}) ^ x) 0 :=
    Ordinal.IsPrincipal.add_eq_right hNprin hElt
  refine le_antisymm ?_ ?_
  · rw [epsV, Ordinal.deriv_add_one]
    refine Ordinal.nfp_le_fp (mul_opow_monotone (Ω_ v)) ?_ (le_of_eq ?_)
    · rw [← Order.succ_eq_add_one, Order.succ_le_iff, ← epsV]
      exact hElt
    · conv_rhs => rw [← hNfp]
      conv_rhs => rw [← epsV_fp v γ]
      rw [mul_assoc, ← Ordinal.opow_add, epsV_fp v γ, hEN]
  · refine Ordinal.nfp_le_fp (mul_opow_monotone (epsV.{u} v γ)) (by simp) (le_of_eq ?_)
    have hFprin : epsV.{u} v γ + epsV.{u} v (γ + 1) = epsV.{u} v (γ + 1) :=
      Ordinal.IsPrincipal.add_eq_right (isPrincipal_add_epsV v (γ + 1))
        (epsV_strictMono v (by simp))
    conv_rhs => rw [← epsV_fp v (γ + 1)]
    conv_lhs => rw [← epsV_fp v γ]
    rw [mul_assoc, ← Ordinal.opow_add, hFprin]

/-! ### The equality -/

theorem one_lt_epsV (v γ : Ordinal.{u}) : 1 < epsV.{u} v γ :=
  lt_of_le_of_lt (Order.one_le_iff_ne_zero.mpr (ne_of_gt (Omega_pos v))) (Omega_lt_epsV v γ)

theorem one_add_lt_epsV {v γ : Ordinal.{u}} (h : γ < epsV.{u} v γ) : 1 + γ < epsV.{u} v γ :=
  isPrincipal_add_epsV v γ (one_lt_epsV v γ) h

/-- **`ψ_v(Ω_{v+1}·(1+γ)) = ε^v_γ` for every `γ` below `ζ^v`.** -/
theorem psi_OmegaV_mul_eq {v : Ordinal.{u}} (hv : v < Ω_ v) (hv1 : v + 1 < Ω_ (v + 1)) :
    ∀ γ : Ordinal.{u}, γ < zetaV.{u} v → psi (Ω_ (v + 1) * (1 + γ)) v = epsV.{u} v γ := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | _ γ IH =>
    intro hz
    refine le_antisymm (psi_OmegaV_mul_le v γ) ?_
    have key : ∀ x : Ordinal.{u}, x < epsV.{u} v γ → x ∈ CSet v (Ω_ (v + 1) * (1 + γ)) := by
      rcases Ordinal.zero_or_succ_or_isSuccLimit γ with rfl | ⟨δ, hδeq⟩ | hlim
      · intro x hx
        rw [add_zero, mul_one]
        refine mem_CSet_of_lt_psi ?_
        rw [psi_Omega_succ hv, ← epsV_zero v]
        exact hx
      · subst hδeq
        rw [Order.succ_eq_add_one] at *
        have hδlt : δ < δ + 1 := by simp
        have hδz : δ < zetaV.{u} v := lt_trans hδlt hz
        have hIH : psi (Ω_ (v + 1) * (1 + δ)) v = epsV.{u} v δ := IH δ hδlt hδz
        have h1δ : 1 + δ < epsV.{u} v δ := one_add_lt_epsV (lt_epsV_self hδz)
        have hΩ1δ : 1 + δ < Ω_ (v + 1) :=
          lt_trans h1δ (epsV_lt_Omega_succ_of_lt_zetaV hδz)
        have hbound : Ω_ (v + 1) * (1 + (δ + 1)) = Ω_ (v + 1) * (1 + δ) + Ω_ (v + 1) := by
          rw [show (1 : Ordinal.{u}) + (δ + 1) = (1 + δ) + 1 from (add_assoc 1 δ 1).symm,
            mul_add_one]
        have hmono : Ω_ (v + 1) * (1 + δ) ≤ Ω_ (v + 1) * (1 + (δ + 1)) :=
          mul_le_mul_right ((add_le_add_iff_left 1).mpr (by simp)) _
        have hsmall : ∀ z : Ordinal.{u}, z < epsV.{u} v δ →
            z ∈ CSet v (Ω_ (v + 1) * (1 + (δ + 1))) := fun z hz' =>
          CSet_mono v hmono (mem_CSet_of_lt_psi (by rw [hIH]; exact hz'))
        have hAmem : ∀ a : Ordinal.{u},
            (Ω_ (v + 1) : Ordinal.{u}) * (1 + δ) ∈ CSet v (Ω_ (v + 1) * (1 + δ) + a) := by
          intro a
          have hpos : (0 : Ordinal.{u}) < Ω_ (v + 1) * (1 + δ) + a :=
            lt_of_lt_of_le (Omega_pos (v + 1)) (le_trans (by
              conv_lhs => rw [← mul_one (Ω_ (v + 1) : Ordinal.{u})]
              exact mul_le_mul_right (by simp) _) (self_le_add_right _ _))
          refine Omega_succ_mul_mem_CSet hv hv1 hpos (1 + δ)
            (lt_of_lt_of_le hΩ1δ (Omega_le_fpOmega (v + 1))) (fun e he => ?_) (fun e he => ?_)
          · refine mem_CSet_of_lt_psi (lt_of_le_of_lt he (lt_of_lt_of_le h1δ ?_))
            rw [← hIH]
            exact psi_mono v (self_le_add_right _ _)
          · refine lt_of_le_of_lt he (lt_of_lt_of_le hΩ1δ (le_trans ?_ (self_le_add_right _ _)))
            conv_lhs => rw [← mul_one (Ω_ (v + 1) : Ordinal.{u})]
            exact mul_le_mul_right (by simp) _
        have hEq : ∀ b : Ordinal.{u}, b < epsV.{u} v (δ + 1) →
            psi (Ω_ (v + 1) * (1 + δ) + b) v = epsV.{u} v δ * ω ^ b := by
          intro b hb
          rw [epsV_add_one] at hb
          exact psi_add_eq hv (le_of_eq hIH.symm) (epsV_pos v δ)
            (fun c => psi_OmegaV_mul_add_le v δ c) hAmem b hb
        have hiter : ∀ m : ℕ, ∀ b : Ordinal.{u},
            b < (fun x => epsV.{u} v δ * (ω : Ordinal.{u}) ^ x)^[m] 0 →
              b ∈ CSet v (Ω_ (v + 1) * (1 + (δ + 1))) := by
          intro m
          induction m with
          | zero =>
            intro b hb
            rw [Function.iterate_zero_apply] at hb
            exact absurd hb (by simp)
          | succ k ihk =>
            intro b hb
            rw [Function.iterate_succ_apply'] at hb
            refine mem_of_lt_mul_opow (epsV.{u} v δ) (epsV_pos v δ) hsmall
              (fun _ h1 _ h2 => CSet.add_mem h1 h2) (fun c hc' => ?_) b hb
            have hcmem : c ∈ CSet v (Ω_ (v + 1) * (1 + (δ + 1))) := ihk c hc'
            have hclt : c < epsV.{u} v (δ + 1) := by
              rw [epsV_add_one]
              exact lt_of_lt_of_le hc' (Ordinal.iterate_le_nfp _ 0 k)
            have hcΩ : c < Ω_ (v + 1) :=
              lt_trans hclt (epsV_lt_Omega_succ_of_lt_zetaV hz)
            have hargs : Ω_ (v + 1) * (1 + δ) + c < Ω_ (v + 1) * (1 + (δ + 1)) := by
              rw [hbound, add_lt_add_iff_left]
              exact hcΩ
            have hamem : Ω_ (v + 1) * (1 + δ) + c ∈ CSet v (Ω_ (v + 1) * (1 + (δ + 1))) := by
              refine CSet.add_mem ?_ hcmem
              have := hAmem (Ω_ (v + 1) : Ordinal.{u})
              rwa [← hbound] at this
            have hmem := CSet.psi_mem (v := v) (a := Ω_ (v + 1) * (1 + (δ + 1))) (u := v)
              (e := Ω_ (v + 1) * (1 + δ) + c) hargs (mem_CSet_of_lt_Omega hv) hamem
            rwa [hEq c hclt] at hmem
        intro x hx
        rw [epsV_add_one] at hx
        obtain ⟨m, hm⟩ := Ordinal.lt_nfp_iff.mp hx
        exact hiter m x hm
      · intro x hx
        haveI : Small.{u} {a : Ordinal.{u} // a < γ} := Ordinal.small_Iio γ
        rw [epsV_limit hlim] at hx
        obtain ⟨⟨δ, hδ⟩, hxδ⟩ := Ordinal.lt_iSup_iff.mp hx
        have hIH := IH δ hδ (lt_trans hδ hz)
        refine CSet_mono v ?_ (mem_CSet_of_lt_psi (by rw [hIH]; exact hxδ))
        exact mul_le_mul_right ((add_le_add_iff_left 1).mpr hδ.le) _
    by_contra hcon
    exact psi_notMem _ v (key _ (not_le.mp hcon))

/-! ### The instances -/

/-- At `v = 0` the ε function of this file is the one of `Ladder.lean`. -/
theorem epsV_zero_eq (γ : Ordinal.{u}) : epsV.{u} 0 γ = eps.{u} γ := by
  rw [epsV, eps]
  congr 1
  funext x
  rw [Omega_zero, one_mul]

/-- Every finite subscript satisfies the condition the ladder asks for. -/
theorem natCast_lt_Omega (n : ℕ) : (n : Ordinal.{u}) < Ω_ (n : Ordinal.{u}) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, Omega_zero]
    exact zero_lt_one
  · have hne : ((n : Ordinal.{u})) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    rw [Omega_of_ne_zero hne]
    exact lt_of_lt_of_le (Ordinal.natCast_lt_omega0 n) (omega0_le_omega _)

/-- **`ψ_n(Ω_{n+1}·(1+γ)) = ε^n_γ` at every finite subscript.**  That is what
a reading of the Bashicu matrices at two rows and up would need: the collapse
at every finite level, not only at `0`. -/
theorem psi_OmegaV_mul_eq_nat (n : ℕ) {γ : Ordinal.{u}} (hz : γ < zetaV.{u} (n : Ordinal.{u})) :
    psi (Ω_ ((n : Ordinal.{u}) + 1) * (1 + γ)) (n : Ordinal.{u}) = epsV.{u} (n : Ordinal.{u}) γ := by
  refine psi_OmegaV_mul_eq (natCast_lt_Omega n) ?_ γ hz
  have h := natCast_lt_Omega (n + 1)
  rwa [Nat.cast_succ] at h

/-! ### Where the subscript stops -/

theorem epsV_zetaV (v : Ordinal.{u}) : epsV.{u} v (zetaV.{u} v) = zetaV.{u} v :=
  Ordinal.nfp_fp (Ordinal.isNormal_deriv _) 0

theorem Omega_le_zetaV (v : Ordinal.{u}) : Ω_ v ≤ zetaV.{u} v := by
  refine le_trans (Omega_le_epsV v 0) ?_
  refine le_trans (le_of_eq ?_) (Ordinal.iterate_le_nfp (epsV.{u} v) 0 1)
  rw [Function.iterate_one]

theorem omega0_le_fpOmega (v : Ordinal.{u}) : (ω : Ordinal.{u}) ≤ fpOmega.{u} v := by
  refine le_trans ?_ (Ordinal.iterate_le_nfp (fun x => Ω_ v * (ω : Ordinal.{u}) ^ x) 0 2)
  rw [Function.iterate_succ_apply', Function.iterate_one, Ordinal.opow_zero, mul_one]
  refine le_trans ?_ (Ordinal.le_mul_right _ (Omega_pos v))
  conv_lhs => rw [← Ordinal.opow_one (ω : Ordinal.{u})]
  exact Ordinal.opow_le_opow_right omega0_pos
    (Order.one_le_iff_ne_zero.mpr (ne_of_gt (Omega_pos v)))

theorem omega0_le_zetaV (v : Ordinal.{u}) : (ω : Ordinal.{u}) ≤ zetaV.{u} v := by
  refine le_trans (omega0_le_fpOmega v) ?_
  rw [← epsV_zero v]
  refine le_trans (le_of_eq ?_) (Ordinal.iterate_le_nfp (epsV.{u} v) 0 1)
  rw [Function.iterate_one]

theorem one_add_zetaV (v : Ordinal.{u}) : 1 + zetaV.{u} v = zetaV.{u} v :=
  Ordinal.one_add_of_omega0_le (omega0_le_zetaV v)

/-- **`ψ_v(Ω_{v+1}·ζ^v) = ζ^v`**: where the ladder at subscript `v` stops.
As at `v = 0`, that is a statement about the arguments of this shape, not
about what the terms of the notation system reach. -/
theorem psi_OmegaV_mul_zetaV {v : Ordinal.{u}} (hv : v < Ω_ v) (hv1 : v + 1 < Ω_ (v + 1)) :
    psi ((Ω_ (v + 1) : Ordinal.{u}) * zetaV.{u} v) v = zetaV.{u} v := by
  refine le_antisymm ?_ ?_
  · have h := psi_OmegaV_mul_le v (zetaV.{u} v)
    rw [one_add_zetaV v, epsV_zetaV] at h
    exact h
  · refine le_of_forall_lt (fun x hx => ?_)
    have hxe : x < epsV.{u} v x := lt_epsV_self hx
    rw [← psi_OmegaV_mul_eq hv hv1 x hx] at hxe
    refine lt_of_lt_of_le hxe (psi_mono v ?_)
    refine mul_le_mul_right ?_ _
    rw [← one_add_zetaV v]
    exact (add_le_add_iff_left 1).mpr hx.le

end Googology.Notation.ExBuchholz.Ord
