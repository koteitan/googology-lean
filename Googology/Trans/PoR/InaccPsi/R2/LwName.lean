import Googology.Trans.PoR.InaccPsi.R2.LwFix
import Googology.Trans.PoR.InaccPsi.R2.NcGG

/-!
# `L(ω)` and `L(ω+1)`: their GEN names, goodness, `υ`-indices, and `L(ω)` is not a `τ`-point

`θ = ψ_{Ω₂}(Ω_ω)`, `P(η) = ψ_{Ω₁}(Ω_ω + θ·η)`, `P' = ψ_{Ω₂}(Ω_ω·2)` (`ncPp`),
`L(ξ) = ψ_{Ω₁}(Ω_ω·2 + P'·ξ)` (`ncL`), `W = Ω₁^{Ω₁}`, `ι` the index of Theorem GEN (`υ_{ι(η)} = P(η)`).

* `lw_A_L`, `lw_L_eq` (**the GEN name**): `Ω_ω + θ·(Ω_ω + P'·ξ) = Ω_ω·2 + P'·ξ`, so `L(ξ) = P(Ω_ω + P'·ξ)`;
* `lw_good_L` (**goodness**): `Ω_ω + P'·ξ` is good whenever `ξ < L(ξ)`; in particular at `ξ = ω, ω+1`
  (`lw_good_L_omega`, `lw_good_L_omega_succ`), with `ι(Ω_ω + P'·ξ + 1) = L(ξ) + 1` there;
* `lw_Pp_cof`: `P' = sup_n ψ_{Ω₂}(Ω_ω + Ω_n)` (Lemma CONT for `ψ_{Ω₂}` and `Ω_ω = sup_n Ω_n`);
* `lw_GP_L_limit`, `lw_GP_L_succ`, `lw_GP_L` (**`L(ξ)` is a `Γ`-point**) for every `ξ ≠ 0` with
  `β < L(β)` for all `β < ξ`: the points `P(η₁ + W)` (Theorem START at `W`) are cofinal below `L(ξ)`, with
  `η₁ = Ω_ω + P'·β` (`ξ` a limit) or `η₁ = Ω_ω + P'·β + ψ_{Ω₂}(Ω_ω + Ω_n)` (`ξ = β + 1`);
* `lw_iota_L_omega`, `lw_iota_L_omega_succ` (**the `υ`-indices**): `ι(Ω_ω + P'·ω) = L(ω)` and
  `ι(Ω_ω + P'·(ω+1)) = L(ω+1)`; both are restart indices with `ρ = υ_ι = L(·)` (`lw_restart_L_omega`, ..);
* `lw_not_tau_L_omega` (**the third hypothesis of `ncUpper_L`**): `L(ω)` is not a `τ`-point; also
  `L(ω+1)` is not (`lw_not_tau_L_omega_succ`);
* `lw_upper_L`, `lw_bounds_L`: `ncUpper_L` and `ncBounds_L_PhiG` with that hypothesis discharged: (P) and
  (Q) at `(L(ω), L(ω+1))` give `ψ_{Ω₁}(Ω_ω + θ·Ω₁^{Ω₁+1}) < ν_C ≤ L(ω+1) = ψ_{Ω₁}(Ω_ω·2 + ω^{P'+1} + P')`;
* `lw_PhiG_lt_L_omega`: `Φ_Γ ≤ ψ_{Ω₁}(Ω_ω·2) < L(ω)`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lw

open Googology.Trans.PoR.InaccPsi.R2.Br Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Nc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq

variable {S : InaccSeq.{0}}

/-! ## The GEN name of `L(ξ)` -/

theorem lw_A_L (S : InaccSeq.{0}) (ξ : Ordinal.{0}) :
    ConjT.Aη S (Om ω + ncPp S * ξ) = Om ω + Om ω + ncPp S * ξ := by
  unfold ConjT.Aη
  rw [mul_add, th_mul_Om_omega, ← mul_assoc, ncTh_mul_Pp, add_assoc]

/-- `L(ξ) = P(Ω_ω + P'·ξ)`. -/
theorem lw_L_eq (S : InaccSeq.{0}) (ξ : Ordinal.{0}) : ncL S ξ = Pv S (Om ω + ncPp S * ξ) :=
  ncL_eq_A S ξ

theorem lw_L_SC (S : InaccSeq.{0}) (ξ : Ordinal.{0}) : SC (ncL S ξ) := SC_psi Low.InR_Om_one _

/-! ## Small facts -/

theorem lw_omega_lt_SC {γ : Ordinal.{0}} (h : SC γ) : ω < γ := by
  have := h.2 0 h.1 1 (one_lt_SC h); rwa [veblen_zero_apply, opow_one] at this

theorem lw_omega_mem (a b : Ordinal.{0}) : (ω : Ordinal.{0}) ∈ S.CSet a b := by
  have := CSet.phi_mem (S := S) (CSet.zero_mem a b) (CSet.one_mem a b)
  rwa [veblen_zero_apply, opow_one] at this

theorem lw_nat_mem (a b : Ordinal.{0}) (n : ℕ) : ((n : ℕ) : Ordinal.{0}) ∈ S.CSet a b := by
  induction n with
  | zero => simpa using CSet.zero_mem (S := S) a b
  | succ n ih => rw [Nat.cast_succ]; exact CSet.succ_mem ih

theorem lw_Pp_opow (S : InaccSeq.{0}) : ω ^ ncPp S = ncPp S := Low.opow_eq_self_of_SC (ncPp_SC S)

theorem lw_Om1_lt_Pp (S : InaccSeq.{0}) : Om (1 : Ordinal.{0}) < ncPp S := (psiS_bounds (S := S) _ 1).1

theorem lw_W_dvd_opow {c : Ordinal.{0}} (h : Om 1 * Om 1 ≤ c) : W ∣ ω ^ c := by
  rw [show W = ω ^ (Om 1 * Om 1) from Om1_pow _, opow_split h]
  exact dvd_mul_right _ _

theorem lw_W_dvd_SC {x : Ordinal.{0}} (hx : SC x) (h1 : Om 1 < x) : W ∣ x := by
  have e := Low.opow_eq_self_of_SC hx
  rw [← e]; exact lw_W_dvd_opow (Om1_mul_lt_eps e h1 h1).le

theorem lw_W_dvd_eta (S : InaccSeq.{0}) (ξ : Ordinal.{0}) : W ∣ Om ω + ncPp S * ξ :=
  dvd_add (lw_W_dvd_SC (SC_Om omega0_ne_zero) (Om_lt_Om.2 one_lt_omega0))
    (dvd_mul_of_dvd_left (lw_W_dvd_SC (ncPp_SC S) (lw_Om1_lt_Pp S)) _)

theorem lw_W_lt_SC {x : Ordinal.{0}} (hx : SC x) (h1 : Om 1 < x) : W < x := by
  have e := Low.opow_eq_self_of_SC hx
  rw [show W = ω ^ (Om 1 * Om 1) from Om1_pow _]
  conv_rhs => rw [← e]
  exact (opow_lt_opow_iff_right one_lt_omega0).2 (Om1_mul_lt_eps e h1 h1)

theorem lw_Pp_mem {a b : Ordinal.{0}} (ha : Om ω + Om ω < a) : ncPp S ∈ S.CSet a b :=
  CSet.psi_mem ha (InR_Om_succ 1) (CSet.Om_mem (CSet.succ_mem (CSet.one_mem a b)))
    (CSet.add_mem (CSet.Om_mem (lw_omega_mem a b)) (CSet.Om_mem (lw_omega_mem a b)))

/-! ## Goodness -/

/-- **Goodness**: `Ω_ω + P'·ξ` is good whenever `ξ < L(ξ)`. -/
theorem lw_good_L {ξ : Ordinal.{0}} (hξ : ξ < ncL S ξ) : Bt.Good S (Om ω + ncPp S * ξ) := by
  unfold Bt.Good
  rw [lw_A_L]
  have hb : ξ < S.psi (Om ω + Om ω + ncPp S * ξ) (Om 1) := hξ
  refine CSet.add_mem (CSet.Om_mem (lw_omega_mem _ _)) ?_
  have hP := lw_Pp_mem (S := S) (a := Om ω + Om ω + ncPp S * ξ + 1)
    (b := S.psi (Om ω + Om ω + ncPp S * ξ) (Om 1)) (lt_of_le_of_lt le_self_add (lt_add_one _))
  have := mem_opow_mul hP hb
  rwa [lw_Pp_opow] at this

theorem lw_lt_L_of_le {ξ : Ordinal.{0}} (h : ξ ≤ ω + 1) : ξ < ncL S ξ :=
  h.trans_lt ((lw_L_SC S ξ).add_one_lt (lw_omega_lt_SC (lw_L_SC S ξ)))

theorem lw_good_L_omega (S : InaccSeq.{0}) : Bt.Good S (Om ω + ncPp S * ω) :=
  lw_good_L (lw_lt_L_of_le le_self_add)

theorem lw_good_L_omega_succ (S : InaccSeq.{0}) : Bt.Good S (Om ω + ncPp S * (ω + 1)) :=
  lw_good_L (lw_lt_L_of_le le_rfl)

/-! ## `P' = sup_n ψ_{Ω₂}(Ω_ω + Ω_n)` -/

theorem lw_le_OmOm {e : Ordinal.{0}} (he : e < Om ω + Om ω) :
    ∃ n : ℕ, e ≤ Om ω + Om ((n : ℕ) : Ordinal.{0}) := by
  rcases lt_or_ge e (Om ω) with h1 | h1
  · exact ⟨0, h1.le.trans le_self_add⟩
  · obtain ⟨d, rfl⟩ := exists_add_of_le h1
    have hd : d < Om ω := (add_lt_add_iff_left _).1 he
    rw [Om_of_ne_zero omega0_ne_zero] at hd
    obtain ⟨c, hc, hdc⟩ := (isNormal_omega.lt_iff_exists_lt isSuccLimit_omega0).1 hd
    obtain ⟨n, rfl⟩ := lt_omega0.1 hc
    refine ⟨n + 1, (add_le_add_iff_left _).2 ?_⟩
    rw [Om_of_ne_zero (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n))]
    exact hdc.le.trans (omega_le_omega.2 (Nat.cast_le.2 (Nat.le_succ n)))

theorem lw_Q_mem_self (n : ℕ) (a b : Ordinal.{0}) :
    Om ω + Om ((n : ℕ) : Ordinal.{0}) ∈ S.CSet a b :=
  CSet.add_mem (CSet.Om_mem (lw_omega_mem a b)) (CSet.Om_mem (lw_nat_mem a b n))

theorem lw_Q_lt_Pp (S : InaccSeq.{0}) (n : ℕ) :
    S.psi (Om ω + Om ((n : ℕ) : Ordinal.{0})) (Om (1 + 1)) < ncPp S :=
  psi_lt_psi (InR_Om_succ 1)
    ((add_lt_add_iff_left _).2 (Om_lt_Om.2 (natCast_lt_omega0 n))) (lw_Q_mem_self n _ _)

/-- **`P' = sup_n q_n`**: every `c < P'` is below some `q_n`. -/
theorem lw_Pp_cof {c : Ordinal.{0}} (hc : c < ncPp S) :
    ∃ n : ℕ, c < S.psi (Om ω + Om ((n : ℕ) : Ordinal.{0})) (Om (1 + 1)) := by
  have hlim : IsSuccLimit (Om ω + Om (ω : Ordinal.{0})) :=
    isSuccLimit_add _ (Om_isSuccLimit omega0_ne_zero)
  have e := lw_psi_limit S (InR_Om_succ 1) hlim
  by_contra h
  have h' : ∀ n : ℕ, S.psi (Om ω + Om ((n : ℕ) : Ordinal.{0})) (Om (1 + 1)) ≤ c :=
    fun n => not_lt.1 fun h'' => h ⟨n, h''⟩
  have hle : S.psi (Om ω + Om ω) (Om (1 + 1)) ≤ c := by
    rw [e]
    haveI : Nonempty (Iio (Om ω + Om (ω : Ordinal.{0}))) := ⟨⟨0, hlim.bot_lt⟩⟩
    refine ciSup_le fun e' => ?_
    obtain ⟨n, hn⟩ := lw_le_OmOm e'.2
    exact (psi_mono (InR_Om_succ 1) hn).1.trans (h' n)
  exact absurd hc (not_lt.2 hle)

/-! ## `L(ξ)` is a `Γ`-point -/

/-- `L(ξ)` is a `Γ`-point for a limit `ξ` with `β < L(β)` for every `β < ξ`. -/
theorem lw_GP_L_limit {ξ : Ordinal.{0}} (hl : IsSuccLimit ξ) (h : ∀ β < ξ, β < ncL S β) :
    IsGP (ncL S ξ) := by
  rw [lw_L_eq]
  refine lw_GP_Pv (isSuccLimit_mul_right (ncPp_SC S).1 hl) fun c hc => ?_
  obtain ⟨β, hβ, hcβ⟩ := (lt_mul_iff_of_isSuccLimit hl).1 hc
  refine ⟨Om ω + ncPp S * β + W, ?_, ?_, lw_GP_step (lw_good_L (h β hβ)) (lw_W_dvd_eta S β)⟩
  · rw [add_assoc]; exact (add_le_add_iff_left _).2 (hcβ.le.trans le_self_add)
  · rw [add_assoc]; refine (add_le_add_iff_left _).2 ?_
    calc ncPp S * β + W ≤ ncPp S * β + ncPp S :=
          (add_le_add_iff_left _).2 (lw_W_lt_SC (ncPp_SC S) (lw_Om1_lt_Pp S)).le
      _ = ncPp S * (β + 1) := (mul_add_one _ _).symm
      _ ≤ ncPp S * ξ := mul_le_mul_right (Order.add_one_le_of_lt hβ) _

/-- `L(β + 1)` is a `Γ`-point when `β < L(β)`. -/
theorem lw_GP_L_succ {β : Ordinal.{0}} (hβ : β < ncL S β) : IsGP (ncL S (β + 1)) := by
  have e : ncL S (β + 1) = Pv S ((Om ω + ncPp S * β) + ncPp S) := by
    rw [lw_L_eq, mul_add_one, add_assoc]
  rw [e]
  set η0 := Om ω + ncPp S * β with hη0
  refine lw_GP_Pv (ncPp_SC S).isSuccLimit fun c hc => ?_
  obtain ⟨n, hcq⟩ := lw_Pp_cof hc
  set q := S.psi (Om ω + Om ((n : ℕ) : Ordinal.{0})) (Om (1 + 1)) with hq
  have hqSC : SC (q) := SC_psi (InR_Om_succ 1) _
  have hq1 : Om (1 : Ordinal.{0}) < q := (psiS_bounds (S := S) _ 1).1
  have hgood : Bt.Good S (η0 + q) := by
    refine good_add (lw_good_L hβ) ?_
    have hA : Om ω + Om ω ≤ ConjT.Aη S (η0 + q) := by
      rw [← A_Om_omega]
      exact ConjT.A_mono S ((le_self_add).trans le_self_add)
    have hlt : Om ω + Om ((n : ℕ) : Ordinal.{0}) < ConjT.Aη S (η0 + q) + 1 :=
      lt_of_lt_of_le ((add_lt_add_iff_left _).2 (Om_lt_Om.2 (natCast_lt_omega0 n)))
        (hA.trans le_self_add)
    exact CSet.psi_mem hlt (InR_Om_succ 1) (CSet.Om_mem (CSet.succ_mem (CSet.one_mem _ _)))
      (lw_Q_mem_self n _ _)
  have hdvd : W ∣ η0 + q := dvd_add (lw_W_dvd_eta S β) (lw_W_dvd_SC hqSC hq1)
  refine ⟨η0 + q + W, ?_, ?_, lw_GP_step hgood hdvd⟩
  · rw [add_assoc η0 (q) W]; exact (add_le_add_iff_left _).2 (hcq.le.trans le_self_add)
  · rw [add_assoc η0 (q) W]
    exact (add_le_add_iff_left _).2 ((ncPp_SC S).isPrincipal (lw_Q_lt_Pp S n)
      (lw_W_lt_SC (ncPp_SC S) (lw_Om1_lt_Pp S))).le

/-- **`L(ξ)` is a `Γ`-point** for every `ξ ≠ 0` with `β < L(β)` for all `β < ξ`. -/
theorem lw_GP_L {ξ : Ordinal.{0}} (hξ : ξ ≠ 0) (h : ∀ β < ξ, β < ncL S β) : IsGP (ncL S ξ) := by
  rcases zero_or_succ_or_isSuccLimit ξ with h0 | ⟨β, rfl⟩ | hl
  · exact absurd h0 hξ
  · rw [Order.succ_eq_add_one]
    exact lw_GP_L_succ (h β (Order.lt_succ β))
  · exact lw_GP_L_limit hl h

theorem lw_GP_L_omega (S : InaccSeq.{0}) : IsGP (ncL S ω) :=
  lw_GP_L_limit isSuccLimit_omega0 fun β hβ => hβ.trans (lw_omega_lt_SC (lw_L_SC S β))

theorem lw_GP_L_omega_succ (S : InaccSeq.{0}) : IsGP (ncL S (ω + 1)) :=
  lw_GP_L_succ (lw_omega_lt_SC (lw_L_SC S ω))

/-! ## The `υ`-indices, restarts, and not a `τ`-point -/

theorem lw_iota_L {ξ : Ordinal.{0}} (h : IsGP (ncL S ξ)) : iota S (Om ω + ncPp S * ξ) = ncL S ξ := by
  rw [lw_L_eq] at h ⊢; exact lw_iota_of_GP h

/-- **`ι(Ω_ω + P'·ω) = L(ω)`**. -/
theorem lw_iota_L_omega (S : InaccSeq.{0}) : iota S (Om ω + ncPp S * ω) = ncL S ω :=
  lw_iota_L (lw_GP_L_omega S)

/-- **`ι(Ω_ω + P'·(ω+1)) = L(ω+1)`**. -/
theorem lw_iota_L_omega_succ (S : InaccSeq.{0}) :
    iota S (Om ω + ncPp S * (ω + 1)) = ncL S (ω + 1) :=
  lw_iota_L (lw_GP_L_omega_succ S)

/-- `ι(Ω_ω + P'·ξ + 1) = L(ξ) + 1` at `ξ = ω`. -/
theorem lw_iota_L_omega_add_one (S : InaccSeq.{0}) :
    iota S (Om ω + ncPp S * ω + 1) = ncL S ω + 1 := by
  rw [iota_good (lw_good_L_omega S), lw_iota_L_omega]

/-- `ι(Ω_ω + P'·(ω+1) + 1) = L(ω+1) + 1`. -/
theorem lw_iota_L_omega_succ_add_one (S : InaccSeq.{0}) :
    iota S (Om ω + ncPp S * (ω + 1) + 1) = ncL S (ω + 1) + 1 := by
  rw [iota_good (lw_good_L_omega_succ S), lw_iota_L_omega_succ]

theorem lw_restart_L {ξ : Ordinal.{0}} (h : IsGP (ncL S ξ)) :
    IsRestartIdx (iota S (Om ω + ncPp S * ξ)) ∧ ncL S ξ = upsilon (iota S (Om ω + ncPp S * ξ)) := by
  rw [lw_L_eq] at h ⊢; exact lw_restart_of_GP h

/-- `L(ω) = ρ_λ` with `λ = ι(Ω_ω + P'·ω) = L(ω)` a restart index. -/
theorem lw_restart_L_omega (S : InaccSeq.{0}) :
    IsRestartIdx (iota S (Om ω + ncPp S * ω)) ∧ ncL S ω = upsilon (iota S (Om ω + ncPp S * ω)) :=
  lw_restart_L (lw_GP_L_omega S)

theorem lw_restart_L_omega_succ (S : InaccSeq.{0}) :
    IsRestartIdx (iota S (Om ω + ncPp S * (ω + 1))) ∧
      ncL S (ω + 1) = upsilon (iota S (Om ω + ncPp S * (ω + 1))) :=
  lw_restart_L (lw_GP_L_omega_succ S)

theorem lw_not_tau_L {ξ : Ordinal.{0}} (h : IsGP (ncL S ξ)) : ¬ NcTauPt (ncL S ξ) := by
  rw [lw_L_eq] at h ⊢; exact lw_not_tau_of_GP h

/-- **`L(ω)` is not a `τ`-point** (the third hypothesis of `ncUpper_L`). -/
theorem lw_not_tau_L_omega (S : InaccSeq.{0}) : ¬ NcTauPt (ncL S ω) := lw_not_tau_L (lw_GP_L_omega S)

theorem lw_not_tau_L_omega_succ (S : InaccSeq.{0}) : ¬ NcTauPt (ncL S (ω + 1)) :=
  lw_not_tau_L (lw_GP_L_omega_succ S)

/-! ## The upper bound with the third hypothesis discharged -/

/-- **`ncUpper_L` without the `τ` hypothesis**: (P), (Q) at `(L(ω), L(ω+1))` give
`ν_C ≤ L(ω+1) = ψ_{Ω₁}(Ω_ω·2 + ω^{P'+1} + P')` and `ν_C = ψ_{Ω₁}(Ω_ω + θ·η)`, `η ≤ Ω_ω + P'·(ω+1)`. -/
theorem lw_upper_L (S : InaccSeq.{0})
    (hP : NcCofPred (ncL S ω) (ncL S (ω + 1))) (hQ : ¬ le1 (ncL S ω) (ncL S (ω + 1) + 1)) :
    nuC ≤ S.psi (Om ω + Om ω + ω ^ (ncPp S + 1) + ncPp S) (Om 1) ∧
      ∃ η ≤ Om ω + ncPp S * (ω + 1), nuC = S.psi (Om ω + ConjT.th S * η) (Om 1) :=
  ncUpper_L S (lw_not_tau_L_omega S) hP hQ

/-- **Both bounds**, given (P) and (Q) at `(L(ω), L(ω+1))` only. -/
theorem lw_bounds_L (S : InaccSeq.{0})
    (hP : NcCofPred (ncL S ω) (ncL S (ω + 1))) (hQ : ¬ le1 (ncL S ω) (ncL S (ω + 1) + 1)) :
    S.psi (Om ω + ConjT.th S * Om 1 ^ (Om 1 + 1)) (Om 1) < nuC ∧
      nuC ≤ S.psi (Om ω + Om ω + ω ^ (ncPp S + 1) + ncPp S) (Om 1) :=
  ncBounds_L_PhiG S (lw_not_tau_L_omega S) hP hQ

/-! ## Order -/

/-- `Φ_Γ ≤ ψ_{Ω₁}(Ω_ω·2) < L(ω)`. -/
theorem lw_PhiG_lt_L_omega (S : InaccSeq.{0}) :
    PhiG ≤ S.psi (Om ω + Om ω) (Om 1) ∧ S.psi (Om ω + Om ω) (Om 1) < ncL S ω := by
  have hg0 : Bt.Good S (Om ω) := by
    have := lw_good_L (S := S) (ξ := 0) (lw_lt_L_of_le zero_le)
    rwa [mul_zero, add_zero] at this
  have h0 : Pv S (Om ω) = S.psi (Om ω + Om ω) (Om 1) := by
    show S.psi (ConjT.Aη S (Om ω)) (Om 1) = _; rw [A_Om_omega]
  have hOm := Low.opow_eq_self_of_SC (SC_Om (omega0_ne_zero : (ω : Ordinal.{0}) ≠ 0))
  have h1ω : Om (1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 one_lt_omega0
  have hle : Om (1 : Ordinal.{0}) ^ (Om 1 + 1) ≤ Om ω := by
    rw [Om1_pow]
    conv_rhs => rw [← hOm]
    exact opow_le_opow_right omega0_pos
      (Om1_mul_lt_eps hOm h1ω ((SC_Om omega0_ne_zero).add_one_lt h1ω)).le
  refine ⟨?_, ?_⟩
  · rw [PhiG_eq S, ← h0]
    exact Pv_mono hle
  · rw [← h0, lw_L_eq]
    exact (Pv_lt_succ hg0).trans_le (Pv_mono (Order.add_one_le_of_lt
      (lt_add_of_pos_right _ (mul_pos (ncPp_SC S).1 omega0_pos))))

end Googology.Trans.PoR.InaccPsi.R2.Lw
