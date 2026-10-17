import Googology.Trans.PoR.InaccPsi.R2.LwName
import Googology.Trans.PoR.InaccPsi.R2.LwLev

/-!
# `L(ω)` and `L(ω+1)` are fixed points of `GG`

`P(η) = ψ_{Ω₁}(Ω_ω + θ·η)`, `P' = ψ_{Ω₂}(Ω_ω·2)`, `L(ξ) = ψ_{Ω₁}(Ω_ω·2 + P'·ξ)`, `U = Ω₁^{Ω₁+1}`,
`D = deriv GG` (the enumeration of the fixed points of `GG`).

* `lw_fixGG_Pv` (the cofinality criterion for `GG`): if for every `c < X` some `e` with
  `η₀ + c ≤ e ≤ η₀ + X` has `GG(P(e)) = P(e)`, then `GG(P(η₀ + X)) = P(η₀ + X)`;
* `lw_fixGG_step`: for a good multiple `η₁` of `U`, `P(η₁ + U)` is a fixed point of `GG`
  (Theorem START at `U`, `lw_start_U`);
* `lw_fixGG_L_limit`, `lw_fixGG_L_succ`; `lw_fixGG_L_omega`, `lw_fixGG_L_omega_succ`:
  `GG(L(ω)) = L(ω)` and `GG(L(ω+1)) = L(ω+1)`, so both are values of `D`;
* `lw_nfpD_lt_L_omega`: `nfp D 1 = ψ_{Ω₁}(Ω_ω + θ·Ω₁^{Ω₁+1}·nfp D 1) < L(ω)`.

No new axiom, no new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lw

open Googology.Trans.PoR.InaccPsi.R2.Br Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Nc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq

variable {S : InaccSeq.{0}}

theorem lw_U_le_opow {x : Ordinal.{0}} (hx : SC x) (h1 : Om 1 < x) :
    Om 1 * (Om 1 + 1) ≤ x :=
  (Om1_mul_lt_eps (Low.opow_eq_self_of_SC hx) h1 (hx.add_one_lt h1)).le

theorem lw_U_dvd_SC {x : Ordinal.{0}} (hx : SC x) (h1 : Om 1 < x) :
    Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) ∣ x := by
  have e := Low.opow_eq_self_of_SC hx
  rw [Om1_pow, ← e, opow_split (lw_U_le_opow hx h1)]
  exact dvd_mul_right _ _

theorem lw_U_lt_SC {x : Ordinal.{0}} (hx : SC x) (h1 : Om 1 < x) :
    Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) < x := by
  have e := Low.opow_eq_self_of_SC hx
  rw [Om1_pow]
  conv_rhs => rw [← e]
  exact (opow_lt_opow_iff_right one_lt_omega0).2
    (Om1_mul_lt_eps e h1 (hx.add_one_lt h1))

theorem lw_U_dvd_eta (S : InaccSeq.{0}) (ξ : Ordinal.{0}) :
    Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) ∣ Om ω + ncPp S * ξ :=
  dvd_add (lw_U_dvd_SC (SC_Om omega0_ne_zero) (Om_lt_Om.2 one_lt_omega0))
    (dvd_mul_of_dvd_left (lw_U_dvd_SC (ncPp_SC S) (lw_Om1_lt_Pp S)) _)

/-- The cofinality criterion for fixed points of `GG`. -/
theorem lw_fixGG_Pv {η0 X : Ordinal.{0}} (hX : IsSuccLimit X)
    (h : ∀ c < X, ∃ e, η0 + c ≤ e ∧ e ≤ η0 + X ∧ GG (Pv S e) = Pv S e) :
    GG (Pv S (η0 + X)) = Pv S (η0 + X) := by
  refine lw_fix_of_cof GG_normal (Pv_SC S _).isSuccLimit fun b hb => ?_
  obtain ⟨c, hc, hbc⟩ := lw_cof hX hb
  obtain ⟨e, he1, he2, he3⟩ := h c hc
  exact ⟨Pv S e, hbc.trans_le (Pv_mono he1), Pv_mono he2, he3⟩

/-- For a good multiple `η₁` of `U`, `P(η₁ + U)` is a fixed point of `GG`. -/
theorem lw_fixGG_step {η1 : Ordinal.{0}} (hg : Bt.Good S η1)
    (hdvd : Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) ∣ η1) :
    GG (Pv S (η1 + Om 1 ^ (Om 1 + 1))) = Pv S (η1 + Om 1 ^ (Om 1 + 1)) := by
  rw [lw_start_U hg hdvd]
  exact (mem_range_deriv GG_normal).1 (nxt_mem _ _)

theorem lw_fixGG_L_limit {ξ : Ordinal.{0}} (hl : IsSuccLimit ξ) (h : ∀ β < ξ, β < ncL S β) :
    GG (ncL S ξ) = ncL S ξ := by
  rw [lw_L_eq]
  refine lw_fixGG_Pv (isSuccLimit_mul_right (ncPp_SC S).1 hl) fun c hc => ?_
  obtain ⟨β, hβ, hcβ⟩ := (lt_mul_iff_of_isSuccLimit hl).1 hc
  refine ⟨Om ω + ncPp S * β + Om 1 ^ (Om 1 + 1), ?_, ?_,
    lw_fixGG_step (lw_good_L (h β hβ)) (lw_U_dvd_eta S β)⟩
  · rw [add_assoc]; exact (add_le_add_iff_left _).2 (hcβ.le.trans le_self_add)
  · rw [add_assoc]; refine (add_le_add_iff_left _).2 ?_
    calc ncPp S * β + Om 1 ^ (Om 1 + 1) ≤ ncPp S * β + ncPp S :=
          (add_le_add_iff_left _).2 (lw_U_lt_SC (ncPp_SC S) (lw_Om1_lt_Pp S)).le
      _ = ncPp S * (β + 1) := (mul_add_one _ _).symm
      _ ≤ ncPp S * ξ := mul_le_mul_right (Order.add_one_le_of_lt hβ) _

theorem lw_fixGG_L_succ {β : Ordinal.{0}} (hβ : β < ncL S β) :
    GG (ncL S (β + 1)) = ncL S (β + 1) := by
  have e : ncL S (β + 1) = Pv S ((Om ω + ncPp S * β) + ncPp S) := by
    rw [lw_L_eq, mul_add_one, add_assoc]
  rw [e]
  set η0 := Om ω + ncPp S * β with hη0
  refine lw_fixGG_Pv (ncPp_SC S).isSuccLimit fun c hc => ?_
  obtain ⟨n, hcq⟩ := lw_Pp_cof hc
  set q := S.psi (Om ω + Om ((n : ℕ) : Ordinal.{0})) (Om (1 + 1)) with hq
  have hqSC : SC q := SC_psi (InR_Om_succ 1) _
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
  have hdvd : Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) ∣ η0 + q :=
    dvd_add (lw_U_dvd_eta S β) (lw_U_dvd_SC hqSC hq1)
  refine ⟨η0 + q + Om 1 ^ (Om 1 + 1), ?_, ?_, lw_fixGG_step hgood hdvd⟩
  · rw [add_assoc η0 q]; exact (add_le_add_iff_left _).2 (hcq.le.trans le_self_add)
  · rw [add_assoc η0 q]
    exact (add_le_add_iff_left _).2 ((ncPp_SC S).isPrincipal (lw_Q_lt_Pp S n)
      (lw_U_lt_SC (ncPp_SC S) (lw_Om1_lt_Pp S))).le

/-- `GG(L(ω)) = L(ω)`: `L(ω)` is a value of `D = deriv GG`. -/
theorem lw_fixGG_L_omega (S : InaccSeq.{0}) : GG (ncL S ω) = ncL S ω :=
  lw_fixGG_L_limit isSuccLimit_omega0 fun β hβ => hβ.trans (lw_omega_lt_SC (lw_L_SC S β))

/-- `GG(L(ω+1)) = L(ω+1)`. -/
theorem lw_fixGG_L_omega_succ (S : InaccSeq.{0}) : GG (ncL S (ω + 1)) = ncL S (ω + 1) :=
  lw_fixGG_L_succ (lw_omega_lt_SC (lw_L_SC S ω))

theorem lw_L_omega_mem_D (S : InaccSeq.{0}) :
    ncL S ω ∈ range (deriv GG) ∧ ncL S (ω + 1) ∈ range (deriv GG) :=
  ⟨(mem_range_deriv GG_normal).2 (lw_fixGG_L_omega S),
    (mem_range_deriv GG_normal).2 (lw_fixGG_L_omega_succ S)⟩

/-- `nfp D 1 = ψ_{Ω₁}(Ω_ω + θ·Ω₁^{Ω₁+1}·nfp D 1) < ψ_{Ω₁}(Ω_ω·2) < L(ω)`. -/
theorem lw_nfpD_lt_L_omega (S : InaccSeq.{0}) :
    nfp (deriv GG) 1 =
        S.psi (Om ω + ConjT.th S * (Om 1 ^ (Om (1 : Ordinal.{0}) + 1) * nfp (deriv GG) 1)) (Om 1) ∧
      nfp (deriv GG) 1 < ncL S ω := by
  have hN1 : 1 ≤ nfp (deriv GG) 1 := le_nfp _ _
  have e := lw_D_eq S hN1 le_rfl
  rw [nfp_fp lw_D_normal 1] at e
  refine ⟨e, ?_⟩
  rw [e]
  have hOm := Low.opow_eq_self_of_SC (SC_Om (omega0_ne_zero : (ω : Ordinal.{0}) ≠ 0))
  have h1ω : Om (1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 one_lt_omega0
  have hNlt : nfp (deriv GG) 1 < Om 1 := lt_of_eq_of_lt e (Pv_lt_Om1 S _)
  have hle : Om (1 : Ordinal.{0}) ^ (Om 1 + 1) * nfp (deriv GG) 1 ≤ Om ω := by
    calc Om (1 : Ordinal.{0}) ^ (Om 1 + 1) * nfp (deriv GG) 1
        ≤ Om (1 : Ordinal.{0}) ^ (Om 1 + 1) * Om 1 := by gcongr
      _ = Om (1 : Ordinal.{0}) ^ (Om 1 + 1 + 1) := (opow_add_one _ _).symm
      _ ≤ Om ω := by
        rw [Om1_pow]
        conv_rhs => rw [← hOm]
        exact opow_le_opow_right omega0_pos (Om1_mul_lt_eps hOm h1ω
          ((SC_Om omega0_ne_zero).add_one_lt ((SC_Om omega0_ne_zero).add_one_lt h1ω))).le
  calc S.psi (Om ω + ConjT.th S * (Om 1 ^ (Om 1 + 1) * nfp (deriv GG) 1)) (Om 1)
      = Pv S (Om 1 ^ (Om 1 + 1) * nfp (deriv GG) 1) := rfl
    _ ≤ Pv S (Om ω) := Pv_mono hle
    _ = S.psi (Om ω + Om ω) (Om 1) := by
        show S.psi (ConjT.Aη S (Om ω)) (Om 1) = _; rw [A_Om_omega]
    _ < ncL S ω := (lw_PhiG_lt_L_omega S).2
