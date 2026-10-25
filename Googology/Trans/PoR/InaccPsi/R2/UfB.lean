import Googology.Trans.PoR.InaccPsi.R2.UfCL
import Googology.Trans.PoR.InaccPsi.R2.UfMove
import Googology.Trans.PoR.InaccPsi.R2.TzB

/-!
# The `ψ_{Ω₁}`-side of the move at every level `μ < B₂`: `B_n` maps the runs of `Φ_μ` to runs of `Φ_{B_n μ}`

`B_n = Bc.bcB S n`, `c_n = L(n+1) = Bc.bcC S n`, `Φ_μ = Uc.ucP μ` (data `Uc.ucDatL μ`), `u_μ = Ω₁^μ`, `μ' = B_n μ`,
`B = α_{n+1} + |r|`, `B' = α_ω + |σ r|` (the argument maps of `Bc`), `B₂ = Uc.ucB = ψ_{Ω₂}(E₂)`, `E₂ = ε_{Ω₂+1}`, codes
`Uc.UcCl` (atoms `H_λ(y)`, moved by `B_n` as `Uf.ufB_atom`).  The proofs of `R2.TzB` (levels `< X`) at the levels
`< B₂`.  Every argument in the window `[c_n, c_{n+1})` is `≥ α_{n+1} > E₂`, and every atom below `B₂` has its own
argument below `E₂`, so the hypothesis `TwArgs` of `Uf.uf_eqP` and `Uf.ufFwdAll` holds there (`uf_args_E`,
`uf_E_le_of_lo`):

* `uf_E_lt_Omw`, `uf_E_le_alpha`, `uf_E_le_alphaW`, `uf_B_le_Omw`, `uf_B_le_th`, `uf_B_le_Pp`;
* `uf_args_E` (**`TwArgs S a μ` for `a ≥ E₂`, `μ < B₂`**), `uf_E_le_of_lo` (**every `K` with `c_n ≤ ψ_{Ω₁}(K)` is
  `≥ E₂`**);
* `ufB_Om1mul`, `ufB_Oe` (**`B_n(u_μ) = u_{B_n μ}`**), `ufB_Oe_mul`, `ufB_psi`, `uf_dvd_sig`, `ufB_dvd`, for every
  code `μ` over `c_{n+1}`; `uf_dvd_alpha`, `uf_dvd_alphaW`, `uf_B_lvl`, `uf_B_datL` (**`ucDatL(B_n μ) =
  B_n(ucDatL μ)`**), `uf_B_dvd`, `uf_dvd_of_rangeP`;
* `uf_B_val`, `uf_B_fix` (**`B_n` maps values and fixed points `∈ [c_n, c_{n+1})` of `Φ_μ` to values and fixed
  points of `Φ_{μ'}`**), `uf_B_run` (**the run**: `B_n(Φ_μ(c₀ + 1 + δ)) = Φ_{μ'}(c₁ + 1 + B_n δ)`), at every code
  `μ < B₂`.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Lq
  Googology.Trans.PoR.InaccPsi.R2.Rb Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Trans.PoR.InaccPsi.R2.Rh
  Googology.Trans.PoR.InaccPsi.R2.Ri Googology.Trans.PoR.InaccPsi.R2.Rk
  Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Tw
  Googology.Trans.PoR.InaccPsi.R2.Ti Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ts

variable {S : InaccSeq.{0}}

/-! ## The arguments in the window are `≥ E₂` -/

theorem uf_E_lt_Omw : ucE < Om (ω : Ordinal.{0}) := by
  have h3 : SC (Om (3 : Ordinal.{0})) := SC_Om (by norm_num)
  have h23 : (OmTwo : Ordinal.{0}) < Om 3 := by
    rw [uf_Om2]; exact Om_lt_Om.2 (by norm_num)
  have hlt : ucE < Om (3 : Ordinal.{0}) := by
    rw [uc_E_eq_veblen]
    exact h3.2 1 (uc_one_lt_SC h3) _ (h3.add_one_lt h23)
  exact hlt.trans_le (Om_le_Om.2 (natCast_lt_omega0 3).le)

theorem uf_E_le_alpha (j : ℕ) : ucE ≤ bcAlpha S j := by
  unfold bcAlpha; exact uf_E_lt_Omw.le.trans (le_self_add.trans le_self_add)

theorem uf_E_le_alphaW : ucE ≤ bcAlphaW S := by
  unfold bcAlphaW; exact uf_E_lt_Omw.le.trans (le_self_add.trans le_self_add)

/-- `B₂ ≤ Ω_ω`. -/
theorem uf_B_le_Omw : (ucB : Ordinal.{0}) ≤ Om ω :=
  (ucB_lt_Om2.trans (ucE_gt.trans uf_E_lt_Omw)).le

/-- `B₂ ≤ θ = ψ_{Ω₂}(Ω_ω)`. -/
theorem uf_B_le_th (S : InaccSeq.{0}) : (ucB : Ordinal.{0}) ≤ ConjT.th S := by
  unfold ConjT.th
  rw [← uc_psiE_eq_B (S := S)]
  exact (psi_mono (S := S) (InR_Om_succ 1) uf_E_lt_Omw.le).1

/-- `B₂ ≤ P′`. -/
theorem uf_B_le_Pp (S : InaccSeq.{0}) : (ucB : Ordinal.{0}) ≤ Nc.ncPp S :=
  (uf_B_le_th S).trans (Nc.ncTh_lt_Pp S).le

/-- **`TwArgs S a μ` for `a ≥ E₂` and `μ < B₂`**: the own argument of an atom below `B₂ = ψ_{Ω₂}(E₂)` is below
`E₂`. -/
theorem uf_args_E {a μ : Ordinal.{0}} (hE : ucE ≤ a) (hμ : μ < ucB) : TwArgs S a μ := by
  intro s e _ _ hsμ hown hψ
  exact (uf_own_lt_E hown (by rw [hψ]; exact hsμ.trans_lt hμ)).trans_le hE

/-- **Every `K` with `c_n ≤ ψ_{Ω₁}(K)` is `≥ E₂`.** -/
theorem uf_E_le_of_lo {n : ℕ} {K : Ordinal.{0}} (hlo : Bc.bcC S n ≤ S.psi K (Om 1)) : ucE ≤ K := by
  by_contra h
  push Not at h
  have h1 : S.psi K (Om 1) ≤ S.psi ucE (Om 1) := (psi_mono Low.InR_Om_one h.le).1
  have h2 : S.psi ucE (Om 1) < S.psi (bcAlpha S (n + 1)) (Om 1) :=
    psi_lt_psi_of_mem Low.InR_Om_one (uf_E_lt_Omw.trans_le (by unfold bcAlpha; exact le_self_add.trans le_self_add))
      (uc_E_mem _ _)
  have hc : Bc.bcC S n = S.psi (bcAlpha S (n + 1)) (Om 1) := Bc.ncL_nat_eq S (n + 1)
  exact absurd hlo (not_le.2 (h1.trans_lt (hc ▸ h2)))


/-- **`B_n(Ω₁·μ) = Ω₁·B_n μ`** for a code `μ` over a strongly critical `c < L(ω)`. -/
theorem ufB_Om1mul {n : ℕ} {c : Ordinal.{0}} (hc : SC c) (hcL : c < Nc.ncL S ω) (hBc : Bc.bcB S n c ≤ Om 1) :
    ∀ μ, UcCl c μ → MvD S (Om 1 * μ) ∧ Bc.bcB S n (Om 1 * μ) = Om 1 * Bc.bcB S n μ := by
  have hc1 : c ≤ Om1 := by rw [Rj.rj_Om1]; exact (hcL.trans (InaccSeq.psi_lt Low.InR_Om_one _)).le
  intro μ
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμ
  rcases eq_or_ne μ 0 with rfl | hμ0
  · rw [mul_zero, Bc.bcB_zero, mul_zero]; exact ⟨mvD_of_lt ((Lw.lw_L_SC S ω).1), rfl⟩
  obtain ⟨hsub, hlog⟩ := ucDec hc hc1 μ hμ
  set g := log ω μ with hg
  have hwg : ω ^ g ≤ μ := opow_log_le_self ω hμ0
  have ht : UcCl c (μ - ω ^ g) := hsub _ (UcCl.opow hc.1 hlog) hwg
  have htlt : μ - ω ^ g < μ := Ph.ph_sub_log_lt hμ0
  have hdec : ω ^ g + (μ - ω ^ g) = μ := Ordinal.add_sub_cancel_of_le hwg
  have hDg := (ufB_code (n := n) hc hcL hBc g hlog).1
  have hDt := (ufB_code (n := n) hc hcL hBc _ ht).1
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  obtain ⟨hDOg, hBOg⟩ := mvB_add (k := n) hDO hDg
  obtain ⟨hDe, hBe⟩ := Ld.ldB_opow (n := n) hDOg
  obtain ⟨hDw, hBw⟩ := Ld.ldB_opow (n := n) hDg
  obtain ⟨hDt2, hBt2⟩ := IH _ htlt ht
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDe hDt2
  obtain ⟨-, hBμ⟩ := mvB_add (k := n) hDw hDt
  rw [hdec] at hBμ
  have hO : ω ^ (Om 1 : Ordinal.{0}) = Om 1 := Bt.Om1_opow
  have e : Om 1 * μ = ω ^ (Om 1 + g) + Om 1 * (μ - ω ^ g) := by
    conv_lhs => rw [← hdec]
    rw [mul_add, opow_add, hO]
  rw [e]
  refine ⟨hDs, ?_⟩
  rw [hBs, hBe, hBOg, hBO, hBt2, hBμ, hBw, opow_add, hO, mul_add]

/-- **`B_n(u_μ) = u_{B_n μ}`** for a code `μ` over a strongly critical `c < L(ω)`. -/
theorem ufB_Oe {n : ℕ} {c μ : Ordinal.{0}} (hc : SC c) (hcL : c < Nc.ncL S ω) (hBc : Bc.bcB S n c ≤ Om 1)
    (hμ : UcCl c μ) :
    MvD S (Le.leOe μ) ∧ Bc.bcB S n (Le.leOe μ) = Le.leOe (Bc.bcB S n μ) := by
  obtain ⟨hDK, hBK⟩ := ufB_Om1mul (n := n) hc hcL hBc μ hμ
  obtain ⟨hD, hB⟩ := Ld.ldB_opow (n := n) hDK
  unfold Le.leOe; rw [hB, hBK]; exact ⟨hD, rfl⟩

/-- **`B_n(u_μ·D) = u_{B_n μ}·B_n D`** for a code `μ` over `c_{n+1}` and a countable `D < c_{n+1}`. -/
theorem ufB_Oe_mul {n : ℕ} {μ D : Ordinal.{0}} (hμ : UcCl (Bc.bcC S (n + 1)) μ) (hD1 : D < Om 1)
    (hDc : D < Bc.bcC S (n + 1)) :
    MvD S (Le.leOe μ * D) ∧ Bc.bcB S n (Le.leOe μ * D) = Le.leOe (Bc.bcB S n μ) * Bc.bcB S n D := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hcS : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  rcases eq_or_ne μ 0 with rfl | hμ0
  · rw [Le.leOe_zero, one_mul, Bc.bcB_zero, Le.leOe_zero, one_mul]
    exact ⟨mvD_of_lt (hDc.trans hLw), rfl⟩
  obtain ⟨hDK, hBK⟩ := ufB_Om1mul (n := n) hcS hLw (Tc.tcB_c_le n) μ hμ
  have h := Le.leB_mulOp2 (n := n) hDK (fun z => z < Om 1 ∧ z < Bc.bcC S (n + 1))
    (fun z hz => mvD_of_lt (hz.2.trans hLw))
    (fun z hz _ => ⟨⟨(log_le_self ω z).trans_lt hz.1, (log_le_self ω z).trans_lt hz.2⟩,
      ⟨(Ordinal.sub_le_self _ _).trans_lt hz.1, (Ordinal.sub_le_self _ _).trans_lt hz.2⟩⟩)
    (fun z hz => hz.1.trans_le (le_mul_left _ (pos_iff_ne_zero.2 hμ0))) D ⟨hD1, hDc⟩
  rw [hBK] at h
  exact h

/-- **`B_n(ψ_{Ω₁}(B + u_μ·D)) = ψ_{Ω₁}(B' + u_{B_n μ}·B_n D)`** for a code `μ` over `c_{n+1}`, an own `B` in the
window and an own `B + u_μ·D` with a countable `D < c_{n+1}`, with `B = α_{n+1} + |r|`, `B' = α_ω + |σ r|` own and
`B_n(ψ_{Ω₁}(B)) = ψ_{Ω₁}(B')`. -/
theorem ufB_psi {n : ℕ} {μ : Ordinal.{0}} (hμ : UcCl (Bc.bcC S (n + 1)) μ)
    {B D : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1)))
    (hlo : Bc.bcC S n ≤ S.psi B (Om 1))
    (hown1 : B + Le.leOe μ * D ∈ S.CSet (B + Le.leOe μ * D) (S.psi (B + Le.leOe μ * D) (Om 1)))
    (hhi : S.psi (B + Le.leOe μ * D) (Om 1) < Bc.bcC S (n + 1)) (hD1 : D < Om 1)
    (hDc : D < Bc.bcC S (n + 1)) :
    ∃ r : Term, bcD S r ∧ B = bcAlpha S (n + 1) + val S r ∧
      bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) ∈
        S.CSet (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r))
          (S.psi (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r)) (Om 1)) ∧
      Bc.bcB S n (S.psi B (Om 1)) = S.psi (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r)) (Om 1) ∧
      Bc.bcB S n (S.psi (B + Le.leOe μ * D) (Om 1)) =
        S.psi (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) + Le.leOe (Bc.bcB S n μ) *
          Bc.bcB S n D) (Om 1) := by
  obtain ⟨hDm, hBm⟩ := ufB_Oe_mul hμ hD1 hDc
  obtain ⟨r, h1, h2, h3, h4, h5⟩ := rdB_psi_baseD hown hlo hown1 hhi hDm
  exact ⟨r, h1, h2, h3, h4, by rw [h5, hBm]⟩

/-- **`σ` maps `u_μ ∣ |r|` to `u_{B_n μ} ∣ |σ r|`** on its domain. -/
theorem uf_dvd_sig {n : ℕ} {μ : Ordinal.{0}} (hμ : UcCl (Bc.bcC S (n + 1)) μ) {r : Term}
    (hr : bcD S r) (h : Le.leOe μ ∣ val S r) :
    Le.leOe (Bc.bcB S n μ) ∣ val S (bcSig (bcPre (n + 1)) bcPreW r) := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  obtain ⟨hDu, hBu⟩ := ufB_Oe (n := n) (Lw.lw_L_SC S _) hLw (Tc.tcB_c_le n) hμ
  have hle : ∀ v : Term, bcD S v → Le.leOe μ ≤ val S v →
      Le.leOe (Bc.bcB S n μ) ≤ val S (bcSig (bcPre (n + 1)) bcPreW v) := fun v hv hlv => by
    have hDv := mvD_of_term hv
    rw [← mvB_term (k := n) hv, ← hBu]
    exact not_lt.1 fun hlt => absurd ((mvB_lt_iff hDv hDu).1 hlt) (not_lt.2 hlv)
  by_cases h0 : r = Term.zero
  · subst h0; rw [bcSig_zero]; exact dvd_zero _
  have hN' := bc_NF (k := n) hr
  have h0' : bcSig (bcPre (n + 1)) bcPreW r ≠ Term.zero := bcSig_ne_zero h0
  rw [rd_dvd_iff_last (rhU_indec _) hN' h0', rbLast_sig]
  exact hle _ (rbLast_D hr) ((rd_dvd_iff_last (rhU_indec μ) hr.1 h0).1 h)


/-- **`u_μ ∣ B` gives `u_{B_n μ} ∣ B'`** under `B_n`. -/
theorem ufB_dvd {n : ℕ} {μ : Ordinal.{0}} (hμ : UcCl (Bc.bcC S (n + 1)) μ)
    (hα : Le.leOe μ ∣ bcAlpha S (n + 1)) (hαW : Le.leOe (Bc.bcB S n μ) ∣ bcAlphaW S)
    {B : Ordinal.{0}} {r : Term} (hr : bcD S r)
    (hB : B = bcAlpha S (n + 1) + val S r) (h : Le.leOe μ ∣ B) :
    Le.leOe (Bc.bcB S n μ) ∣ bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) := by
  rw [hB, rd_dvd_add_left hα] at h
  rw [rd_dvd_add_left hαW]
  exact uf_dvd_sig hμ hr h




/-- **`u_μ ∣ α_j`** for `μ ≤ Γ_{Ω₁+1}`. -/
theorem uf_dvd_alpha {μ : Ordinal.{0}} (hμ : μ ≤ ucB) (j : ℕ) : Le.leOe μ ∣ bcAlpha S j := by
  have h1 : Le.leOe μ ∣ Om (ω : Ordinal.{0}) :=
    uf_dvd_eps hμ (Low.opow_eq_self_of_SC (SC_Om omega0_pos.ne'))
      uf_B_le_Omw
  have h2 : Le.leOe μ ∣ Nc.ncPp S :=
    uf_dvd_eps hμ (Low.opow_eq_self_of_SC (Nc.ncPp_SC S))
      (uf_B_le_Pp S)
  exact dvd_add (dvd_add h1 h1) (dvd_mul_of_dvd_left h2 _)

/-- **`u_μ ∣ α_ω`** for `μ ≤ Γ_{Ω₁+1}`. -/
theorem uf_dvd_alphaW {μ : Ordinal.{0}} (hμ : μ ≤ ucB) : Le.leOe μ ∣ bcAlphaW S := by
  have h1 : Le.leOe μ ∣ Om (ω : Ordinal.{0}) :=
    uf_dvd_eps hμ (Low.opow_eq_self_of_SC (SC_Om omega0_pos.ne'))
      uf_B_le_Omw
  refine dvd_add (dvd_add h1 h1) ?_
  have hE : ω ^ Nc.ncPp S = Nc.ncPp S := Low.opow_eq_self_of_SC (Nc.ncPp_SC S)
  have h2 : Le.leOe μ ∣ Nc.ncPp S :=
    uf_dvd_eps hμ hE (uf_B_le_Pp S)
  have hI : Indec (ω ^ (Nc.ncPp S + 1)) :=
    indec_iff.2 ⟨(opow_pos _ omega0_pos).ne', isPrincipal_add_omega0_opow _⟩
  refine rh_dvd_of_indec μ hI ((Ordinal.le_of_dvd (inE_indec hE).ne_zero h2).trans ?_)
  conv_lhs => rw [← hE]
  exact opow_le_opow_right omega0_pos le_self_add

/-- **The level moves**: for a code `μ` over `c_{n+1}`: `μ` is in the domain of `B_n`, `μ < Γ_{Ω₁+1}`, `B_n μ <
Γ_{Ω₁+1}`, `B_n μ` is a code over `B_n c_{n+1}`, and `B_n(μ + 1) = B_n μ + 1`. -/
theorem uf_B_lvl {n : ℕ} {μ : Ordinal.{0}} (hμ : UcCl (Bc.bcC S (n + 1)) μ) (hμΓ : μ < ucB) :
    MvD S μ ∧ μ < ucB ∧ Bc.bcB S n μ < ucB ∧ Bc.bcB S n (μ + 1) = Bc.bcB S n μ + 1 := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hc1 : Bc.bcC S (n + 1) ≤ Om1 := by
    rw [Rj.rj_Om1]; exact (hLw.trans (InaccSeq.psi_lt Low.InR_Om_one _)).le
  have hD := (ufB_cl (n := n) hμ).1
  exact ⟨hD, hμΓ, ufB_lt_B hμ, rkB_succ hD⟩

/-- **`ucDatL (B_n μ) = B_n (ucDatL μ)`** for a code `μ` over `c_{n+1}`. -/
theorem uf_B_datL {n : ℕ} {μ : Ordinal.{0}} (hμ : UcCl (Bc.bcC S (n + 1)) μ) (hμΓ : μ < ucB) :
    ucDatL (Bc.bcB S n μ) = Bc.bcB S n (ucDatL μ) := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hD := (ufB_cl (n := n) hμ).1
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  have e : Bc.bcB S n (Om1 + μ) = Om1 + Bc.bcB S n μ := by
    rw [Rj.rj_Om1, (mvB_add (k := n) hDO hD).2, hBO]
  unfold ucDatL
  rw [← e]
  exact ufB_dat (UcCl.add UcCl.om hμ)

/-- **`u_μ ∣ B` gives `u_{B_n μ} ∣ B'`** for `B = α_{n+1} + |r|`, `B' = α_ω + |σ r|`, a code `μ` over `c_{n+1}`. -/
theorem uf_B_dvd {n : ℕ} {μ : Ordinal.{0}} (hμ : UcCl (Bc.bcC S (n + 1)) μ) (hμΓ : μ < ucB)
    {B : Ordinal.{0}} {r : Term} (hr : bcD S r)
    (hB : B = bcAlpha S (n + 1) + val S r) (h : Le.leOe μ ∣ B) :
    Le.leOe (Bc.bcB S n μ) ∣ bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) :=
  ufB_dvd hμ (uf_dvd_alpha (uf_B_lvl hμ hμΓ).2.1.le _) (uf_dvd_alphaW (uf_B_lvl hμ hμΓ).2.2.1.le) hr hB h

/-- **`u_μ ∣ B`** for an own `B` whose collapse is a fixed point of every `Φ_j`, `j < μ`, `ucDatL j < ψ_{Ω₁}(B)`
(`μ ≤ Γ_{Ω₁+1}`). -/
theorem uf_dvd_of_rangeP {μ B : Ordinal.{0}} (hμΩ : μ ≤ ucB) (hown : B ∈ S.CSet B (S.psi B (Om 1)))
    (hfix : ∀ j < μ, ucDatL j < S.psi B (Om 1) → ucP j (S.psi B (Om 1)) = S.psi B (Om 1)) :
    Le.leOe μ ∣ B := by
  set p := S.psi B (Om 1) with hpdef
  have hpSC : SC p := SC_psi Low.InR_Om_one B
  have hcoll : ∀ e, e < B → e ∈ S.CSet B p → RiDg p e → UfLev p e → S.psi e (Om 1) < p :=
    fun e he heC _ _ => lt_psi_of_mem Low.InR_Om_one
      (CSet.psi_mem he Low.InR_Om_one (mem_CSet_psi Low.InR_Om_one B) heC) (psi_lt Low.InR_Om_one _)
  have hdl := uf_diglev (S := S) hpSC (psi_lt Low.InR_Om_one B).le hcoll B hown
  refine Ri.ri_dvd_of_dig μ fun j hj => ?_
  have hjΩ : j < ucB := hj.trans_le hμΩ
  by_cases hd : ucDatL j < p
  · exact Ri.ri_dig_zero_of_dvd (uf_conv hjΩ hown (hfix j hj hd))
  · by_contra hd0
    exact hd (hdl.2.1 j hjΩ hd0)

/-- **`B_n` maps a value `v = ψ_{Ω₁}(B) ∈ [c_n, c_{n+1})` of `Φ_μ` (`B` own) to a value of `Φ_{B_n μ}`**, for a code
`μ` over `c_{n+1}`; the image is `ψ_{Ω₁}(B')` with `B'` own and `u_{B_n μ} ∣ B'`. -/
theorem uf_B_val {n : ℕ} {μ B : Ordinal.{0}} (hμ : UcCl (Bc.bcC S (n + 1)) μ) (hμΓ : μ < ucB)
    (hown : B ∈ S.CSet B (S.psi B (Om 1))) (hlo : Bc.bcC S n ≤ S.psi B (Om 1))
    (hhi : S.psi B (Om 1) < Bc.bcC S (n + 1)) (hv : S.psi B (Om 1) ∈ range (ucP μ)) :
    ∃ r : Term, bcD S r ∧ B = bcAlpha S (n + 1) + val S r ∧
      bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) ∈
        S.CSet (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r))
          (S.psi (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r)) (Om 1)) ∧
      Le.leOe (Bc.bcB S n μ) ∣ bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) ∧
      Bc.bcB S n (S.psi B (Om 1)) = S.psi (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r)) (Om 1) ∧
      Bc.bcB S n (S.psi B (Om 1)) ∈ range (ucP (Bc.bcB S n μ)) := by
  obtain ⟨hDμ, hμG, hμ'G, -⟩ := uf_B_lvl hμ hμΓ
  have hcS : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  set v := S.psi B (Om 1) with hvdef
  have hvSC : SC v := SC_psi Low.InR_Om_one B
  obtain ⟨hvL, hv1, hBv1⟩ := Tz.ti_win (n := n) hhi
  have hvd : ucDatL μ < v := by obtain ⟨o, ho⟩ := hv; rw [← ho]; exact ucDatL_lt_ucP μ o
  have hdvd : Le.leOe μ ∣ B := uf_dvd_of_rangeP hμG.le hown fun j hj hd => ucP_fix_lower hj hv hd
  obtain ⟨r, hDr, hBr, hownB', hBv, -⟩ := ufB_psi (n := n) (D := 0) hμ hown hlo
    (by rw [mul_zero, add_zero]; exact hown) (by rw [mul_zero, add_zero]; exact hhi)
    (lt_of_le_of_lt zero_le (by rw [← Rj.rj_Om1]; exact Rj.rj_Om1_pos.trans_le (by rw [Rj.rj_Om1])))
    (lt_of_le_of_lt zero_le hcS.1)
  set B' := bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) with hB'def
  have hdvd' : Le.leOe (Bc.bcB S n μ) ∣ B' := uf_B_dvd hμ hμΓ hDr hBr hdvd
  refine ⟨r, hDr, hBr, hownB', hdvd', hBv, ?_⟩
  -- the image is a value of `Φ_{μ'}`
  have hB'0 : B' ≠ 0 := by
    rw [hB'def]
    exact (lt_of_lt_of_le (lt_of_le_of_lt zero_le (Bc.bcAlpha_lt_W S 0)) le_self_add).ne'
  have hdμ : ucDatL μ < Bc.bcC S (n + 1) := by
    have h := (uc_cl_iff hcS (lt_of_le_of_lt le_rfl
      (uc_B_indec.add_lt ucB_gt hμG))).1 (UcCl.add UcCl.om hμ)
    exact h
  have hdv' : ucDatL (Bc.bcB S n μ) < S.psi B' (Om 1) := by
    rw [uf_B_datL hμ hμΓ, ← hBv]
    exact (Bc.bcB_lt_iff (hdμ.trans (Bc.bcC_lt S (n + 1))) hvL).2 hvd
  rw [hBv]
  refine ucP_range (SC_psi Low.InR_Om_one _) hdv' fun j hj hdj => ?_
  exact ufFwdAll j (hj.trans hμ'G) B' hownB' ((rhU_dvd_succ hj).trans hdvd') hB'0 hdj
    (uf_args_E (uf_E_le_alphaW.trans le_self_add) (hj.trans hμ'G))

/-- **`B_n` maps a fixed point `p = ψ_{Ω₁}(B) ∈ [c_n, c_{n+1})` of `Φ_μ` (`B` own) to a fixed point of
`Φ_{B_n μ}`**, for a code `μ` over `c_{n+1}`. -/
theorem uf_B_fix {n : ℕ} {μ B : Ordinal.{0}} (hμ : UcCl (Bc.bcC S (n + 1)) μ) (hμΓ : μ < ucB)
    (hown : B ∈ S.CSet B (S.psi B (Om 1))) (hlo : Bc.bcC S n ≤ S.psi B (Om 1))
    (hhi : S.psi B (Om 1) < Bc.bcC S (n + 1)) (hp : ucP μ (S.psi B (Om 1)) = S.psi B (Om 1)) :
    ucP (Bc.bcB S n μ) (Bc.bcB S n (S.psi B (Om 1))) = Bc.bcB S n (S.psi B (Om 1)) := by
  obtain ⟨hDμ, hμG, hμ'G, hBsucc⟩ := uf_B_lvl hμ hμΓ
  have hcS : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  have hcl1 : UcCl (Bc.bcC S (n + 1)) (μ + 1) := UcCl.add hμ (UcCl.small (gg_one_lt_of_SC hcS))
  obtain ⟨r, hDr, hBr, hownB', -, hBv, -⟩ := uf_B_val hμ hμΓ hown hlo hhi ⟨_, hp⟩
  have hdvd1 : Le.leOe (μ + 1) ∣ B := uf_conv hμG hown hp
  have hdvd1' := uf_B_dvd hcl1 (ucB_SC.add_one_lt hμΓ) hDr hBr hdvd1
  rw [hBsucc] at hdvd1'
  have hB'0 : bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) ≠ 0 :=
    (lt_of_lt_of_le (lt_of_le_of_lt zero_le (Bc.bcAlpha_lt_W S 0)) le_self_add).ne'
  obtain ⟨hvL, -, -⟩ := Tz.ti_win (n := n) hhi
  have hdμ : ucDatL μ < S.psi B (Om 1) := (by rw [← hp]; exact ucDatL_lt_ucP μ _)
  have hdμL : ucDatL μ < Nc.ncL S ω := hdμ.trans hvL
  have hdv' : ucDatL (Bc.bcB S n μ) < Bc.bcB S n (S.psi B (Om 1)) := by
    rw [uf_B_datL hμ hμΓ]; exact (Bc.bcB_lt_iff hdμL hvL).2 hdμ
  rw [hBv] at hdv' ⊢
  exact ufFwdAll _ hμ'G _ hownB' hdvd1' hB'0 hdv' (uf_args_E (uf_E_le_alphaW.trans le_self_add) hμ'G)

/-- **The run of `Φ_μ` from an own base point moves to a run of `Φ_{B_n μ}`.** -/
theorem uf_B_run {n : ℕ} {μ B0 c0 δ : Ordinal.{0}} (hμ : UcCl (Bc.bcC S (n + 1)) μ) (hμΓ : μ < ucB)
    (hown0 : B0 ∈ S.CSet B0 (S.psi B0 (Om 1))) (hdvd0 : Le.leOe μ ∣ B0)
    (hc0 : ucP μ c0 = S.psi B0 (Om 1)) (hlo : Bc.bcC S n ≤ S.psi B0 (Om 1))
    (hd0 : ucDatL μ < S.psi B0 (Om 1))
    (hx : ucP μ (c0 + 1 + δ) < Bc.bcC S (n + 1))
    (hcond : ∀ σ, σ ≤ δ → c0 + 1 + σ < ucP μ (c0 + 1 + σ)) :
    ∃ B', B' ∈ S.CSet B' (S.psi B' (Om 1)) ∧ Le.leOe (Bc.bcB S n μ) ∣ B' ∧
      Bc.bcB S n (S.psi B0 (Om 1)) = S.psi B' (Om 1) ∧
      ∀ c1, ucP (Bc.bcB S n μ) c1 = S.psi B' (Om 1) →
        Bc.bcB S n (ucP μ (c0 + 1 + δ)) = ucP (Bc.bcB S n μ) (c1 + 1 + Bc.bcB S n δ) ∧
        ∀ σ, σ ≤ Bc.bcB S n δ → c1 + 1 + σ < ucP (Bc.bcB S n μ) (c1 + 1 + σ) := by
  obtain ⟨hDμ, hμG, hμ'G, -⟩ := uf_B_lvl hμ hμΓ
  set x := ucP μ (c0 + 1 + δ) with hxdef
  obtain ⟨hxL, hx1, hBx1⟩ := Tz.ti_win (n := n) hx
  have h1L : (1 : Ordinal.{0}) < Nc.ncL S ω := Ri.ri_one_lt_L S
  set D := 1 + δ with hDdef
  have hcD : c0 + D = c0 + 1 + δ := (add_assoc c0 1 δ).symm
  have hDx : D < x := by
    rw [hxdef, ← hcD]
    have h := hcond δ le_rfl
    rw [← hcD] at h
    exact le_add_self.trans_lt h
  have hDL : D < Nc.ncL S ω := hDx.trans hxL
  have hδL : δ < Nc.ncL S ω := (le_add_self.trans_lt hDx).trans hxL
  have hcondD : ∀ d, d ≤ D → d < ucP μ (c0 + d) := by
    intro d hd
    rcases eq_or_ne d 0 with rfl | hd0
    · exact (ucP_SC μ _).1
    have hσ : 1 + (d - 1) = d := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hd0)
    have hσδ : d - 1 ≤ δ := by
      rw [← hσ] at hd; exact (add_le_add_iff_left 1).1 hd
    have h := hcond _ hσδ
    rw [add_assoc, hσ] at h
    exact le_add_self.trans_lt h
  have hW0 := uf_E_le_of_lo hlo
  obtain ⟨hval, hψ⟩ := uf_eqP hμG hown0 hdvd0 hc0 hd0 (uf_args_E hW0 hμG) D (hDx.trans hx1) hcondD
  have hψx : S.psi (B0 + Le.leOe μ * D) (Om 1) = x := by rw [hψ, hcD]
  have hown1 : B0 + Le.leOe μ * D ∈ S.CSet (B0 + Le.leOe μ * D) (S.psi (B0 + Le.leOe μ * D) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add : B0 ≤ B0 + Le.leOe μ * D)).2 hown0)
      (uf_U_mul_mem (SC_psi Low.InR_Om_one _) (psi_lt Low.InR_Om_one _).le hμG
        (hd0.trans_le (psi_mono (S := S) Low.InR_Om_one le_self_add).1) hval (uf_args_E (hW0.trans le_self_add) hμG))
  obtain ⟨r, hDr, hBr, hownB', hB0', hBx⟩ := ufB_psi (n := n) hμ hown0 hlo hown1
    (by rw [hψx]; exact hx) (hDx.trans hx1) (hDx.trans hx)
  set B' := bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) with hB'def
  have hdvd' : Le.leOe (Bc.bcB S n μ) ∣ B' := uf_B_dvd hμ hμΓ hDr hBr hdvd0
  rw [hψx] at hBx
  have hBDx : Bc.bcB S n D < Bc.bcB S n x := (Bc.bcB_lt_iff hDL hxL).2 hDx
  have hval' : Bc.bcB S n D < S.psi (B' + Le.leOe (Bc.bcB S n μ) * Bc.bcB S n D) (Om 1) := by
    rw [← hBx]; exact hBDx
  have hBD : Bc.bcB S n D = 1 + Bc.bcB S n δ := by rw [hDdef, Bc.bcB_add h1L hδL, Mw.mwB_one]
  refine ⟨B', hownB', hdvd', hB0', fun c1 hc1 => ?_⟩
  have hcondD' := uf_validP hμ'G.le hdvd' hc1 hval'
  have hd1 : ucDatL (Bc.bcB S n μ) < S.psi B' (Om 1) := by
    rw [uf_B_datL hμ hμΓ, ← hB0']
    have hvL : S.psi B0 (Om 1) < Nc.ncL S ω := by
      rw [← hc0]; exact ((ucP_le_iff μ).2 (le_self_add.trans le_self_add)).trans_lt hxL
    exact (Bc.bcB_lt_iff (hd0.trans hvL) hvL).2 hd0
  have hBxF : Bc.bcB S n x = ucP (Bc.bcB S n μ) (c1 + Bc.bcB S n D) := by
    rw [hBx]
    exact (uf_eqP hμ'G hownB' hdvd' hc1 hd1 (uf_args_E (uf_E_le_alphaW.trans le_self_add) hμ'G)
      (Bc.bcB S n D) (hBDx.trans hBx1) hcondD').2
  refine ⟨by rw [hBxF, hBD, add_assoc], fun σ hσ => ?_⟩
  have h1 := hcondD' (1 + σ) (by rw [hBD]; exact (add_le_add_iff_left 1).2 hσ)
  have h2 : c1 < ucP (Bc.bcB S n μ) (c1 + (1 + σ)) :=
    (ucP_le_self _ c1).trans_lt
      ((ucP_lt_iff _).2 (lt_add_of_pos_right _ (lt_of_lt_of_le zero_lt_one le_self_add)))
  rw [add_assoc]
  exact (lq_SC_indec (ucP_SC _ _)).add_lt h2 h1

end Googology.Trans.PoR.InaccPsi.R2.Uf
