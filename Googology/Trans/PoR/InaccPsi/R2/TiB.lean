import Googology.Trans.PoR.InaccPsi.R2.TiCode

/-!
# The `ψ_{Ω₁}`-side of the move at every level `μ < B_Γ`: `B_n` maps the runs of `Φ_μ` to runs of `Φ_{B_n μ}`

`B_n = Bc.bcB S n`, `c_n = L(n+1) = Bc.bcC S n`, `Φ_μ = Tf.tfP μ` (data `Tf.tfDatL μ`), `u_μ = Ω₁^μ`, `μ' = B_n μ`,
`B = α_{n+1} + |r|`, `B' = α_ω + |σ r|` (the argument maps of `Bc`), `B_Γ = Tf.tfBG` (the least fixed point of `Γ` above
`Ω₁`), codes `Tf.TfCl` (atoms `Γ_ν = ψ_{Ω₂}(ν − (Ω₁ + 1))`, moved by `B_n` as `Ti.tiB_gamma`).  The proofs of `R2.TcB`
(codes `LgCl`, levels `< Γ'`) with the codes `TfCl` and the levels `< B_Γ`:

* `tiB_Om1mul`, `tiB_Oe` (**`B_n(u_μ) = u_{B_n μ}`**), `tiB_Oe_mul`, `tiB_psi` (**`B_n(ψ_{Ω₁}(B + u_μ·D)) =
  ψ_{Ω₁}(B' + u_{B_n μ}·B_n D)`**), `ti_dvd_sig`, `tiB_dvd`, for every code `μ` over `c_{n+1}`;
* `ti_dvd_alpha`, `ti_dvd_alphaW` (`u_μ ∣ α_j`, `u_μ ∣ α_ω` for `μ ≤ B_Γ`), `ti_B_lvl`, `ti_B_datL` (**`tfDatL μ' =
  B_n(tfDatL μ)`**), `ti_B_dvd`, `ti_dvd_of_range`, `ti_win`;
* `ti_B_val`, `ti_B_fix` (**`B_n` maps values and fixed points `∈ [c_n, c_{n+1})` of `Φ_μ` to values and fixed points
  of `Φ_{μ'}`**), `ti_B_run` (**the run**: `B_n(Φ_μ(c₀ + 1 + δ)) = Φ_{μ'}(c₁ + 1 + B_n δ)`), at every code `μ < B_Γ`.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ti

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Lq
  Googology.Trans.PoR.InaccPsi.R2.Rb Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Trans.PoR.InaccPsi.R2.Rh
  Googology.Trans.PoR.InaccPsi.R2.Ri Googology.Trans.PoR.InaccPsi.R2.Rk
  Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Tf

variable {S : InaccSeq.{0}}

theorem ti_Gam_lt_Omw : ggGam < Om (ω : Ordinal.{0}) :=
  ggGam_le_Om2.trans_lt (Om_lt_Om.2 (by rw [one_add_one_eq_two]; exact natCast_lt_omega0 2))

/-- **`B_n(Ω₁·μ) = Ω₁·B_n μ`** for a code `μ` over a strongly critical `c < L(ω)`. -/
theorem tiB_Om1mul {n : ℕ} {c : Ordinal.{0}} (hc : SC c) (hcL : c < Nc.ncL S ω) (hBc : Bc.bcB S n c ≤ Om 1) :
    ∀ μ, TfCl c μ → MvD S (Om 1 * μ) ∧ Bc.bcB S n (Om 1 * μ) = Om 1 * Bc.bcB S n μ := by
  intro μ
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμ
  rcases eq_or_ne μ 0 with rfl | hμ0
  · rw [mul_zero, Bc.bcB_zero, mul_zero]; exact ⟨mvD_of_lt ((Lw.lw_L_SC S ω).1), rfl⟩
  obtain ⟨hsub, hlog⟩ := tfDec hc μ hμ
  set g := log ω μ with hg
  have hwg : ω ^ g ≤ μ := opow_log_le_self ω hμ0
  have ht : TfCl c (μ - ω ^ g) := hsub _ (TfCl.opow hc.1 hlog) hwg
  have htlt : μ - ω ^ g < μ := Ph.ph_sub_log_lt hμ0
  have hdec : ω ^ g + (μ - ω ^ g) = μ := Ordinal.add_sub_cancel_of_le hwg
  have hDg := (tiB_code (n := n) hc hcL hBc g hlog).1
  have hDt := (tiB_code (n := n) hc hcL hBc _ ht).1
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
theorem tiB_Oe {n : ℕ} {c μ : Ordinal.{0}} (hc : SC c) (hcL : c < Nc.ncL S ω) (hBc : Bc.bcB S n c ≤ Om 1)
    (hμ : TfCl c μ) :
    MvD S (Le.leOe μ) ∧ Bc.bcB S n (Le.leOe μ) = Le.leOe (Bc.bcB S n μ) := by
  obtain ⟨hDK, hBK⟩ := tiB_Om1mul (n := n) hc hcL hBc μ hμ
  obtain ⟨hD, hB⟩ := Ld.ldB_opow (n := n) hDK
  unfold Le.leOe; rw [hB, hBK]; exact ⟨hD, rfl⟩

/-- **`B_n(u_μ·D) = u_{B_n μ}·B_n D`** for a code `μ` over `c_{n+1}` and a countable `D < c_{n+1}`. -/
theorem tiB_Oe_mul {n : ℕ} {μ D : Ordinal.{0}} (hμ : TfCl (Bc.bcC S (n + 1)) μ) (hD1 : D < Om 1)
    (hDc : D < Bc.bcC S (n + 1)) :
    MvD S (Le.leOe μ * D) ∧ Bc.bcB S n (Le.leOe μ * D) = Le.leOe (Bc.bcB S n μ) * Bc.bcB S n D := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hcS : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  rcases eq_or_ne μ 0 with rfl | hμ0
  · rw [Le.leOe_zero, one_mul, Bc.bcB_zero, Le.leOe_zero, one_mul]
    exact ⟨mvD_of_lt (hDc.trans hLw), rfl⟩
  obtain ⟨hDK, hBK⟩ := tiB_Om1mul (n := n) hcS hLw (Tc.tcB_c_le n) μ hμ
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
theorem tiB_psi {n : ℕ} {μ : Ordinal.{0}} (hμ : TfCl (Bc.bcC S (n + 1)) μ)
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
  obtain ⟨hDm, hBm⟩ := tiB_Oe_mul hμ hD1 hDc
  obtain ⟨r, h1, h2, h3, h4, h5⟩ := rdB_psi_baseD hown hlo hown1 hhi hDm
  exact ⟨r, h1, h2, h3, h4, by rw [h5, hBm]⟩

/-- **`σ` maps `u_μ ∣ |r|` to `u_{B_n μ} ∣ |σ r|`** on its domain. -/
theorem ti_dvd_sig {n : ℕ} {μ : Ordinal.{0}} (hμ : TfCl (Bc.bcC S (n + 1)) μ) {r : Term}
    (hr : bcD S r) (h : Le.leOe μ ∣ val S r) :
    Le.leOe (Bc.bcB S n μ) ∣ val S (bcSig (bcPre (n + 1)) bcPreW r) := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  obtain ⟨hDu, hBu⟩ := tiB_Oe (n := n) (Lw.lw_L_SC S _) hLw (Tc.tcB_c_le n) hμ
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
theorem tiB_dvd {n : ℕ} {μ : Ordinal.{0}} (hμ : TfCl (Bc.bcC S (n + 1)) μ)
    (hα : Le.leOe μ ∣ bcAlpha S (n + 1)) (hαW : Le.leOe (Bc.bcB S n μ) ∣ bcAlphaW S)
    {B : Ordinal.{0}} {r : Term} (hr : bcD S r)
    (hB : B = bcAlpha S (n + 1) + val S r) (h : Le.leOe μ ∣ B) :
    Le.leOe (Bc.bcB S n μ) ∣ bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) := by
  rw [hB, rd_dvd_add_left hα] at h
  rw [rd_dvd_add_left hαW]
  exact ti_dvd_sig hμ hr h




/-- **`u_μ ∣ α_j`** for `μ ≤ Γ_{Ω₁+1}`. -/
theorem ti_dvd_alpha {μ : Ordinal.{0}} (hμ : μ ≤ tfBG) (j : ℕ) : Le.leOe μ ∣ bcAlpha S j := by
  have h1 : Le.leOe μ ∣ Om (ω : Ordinal.{0}) :=
    tf_dvd_eps hμ (Low.opow_eq_self_of_SC (SC_Om omega0_pos.ne'))
      ti_BG_le_Omw
  have h2 : Le.leOe μ ∣ Nc.ncPp S :=
    tf_dvd_eps hμ (Low.opow_eq_self_of_SC (Nc.ncPp_SC S))
      (ti_BG_le_Pp S)
  exact dvd_add (dvd_add h1 h1) (dvd_mul_of_dvd_left h2 _)

/-- **`u_μ ∣ α_ω`** for `μ ≤ Γ_{Ω₁+1}`. -/
theorem ti_dvd_alphaW {μ : Ordinal.{0}} (hμ : μ ≤ tfBG) : Le.leOe μ ∣ bcAlphaW S := by
  have h1 : Le.leOe μ ∣ Om (ω : Ordinal.{0}) :=
    tf_dvd_eps hμ (Low.opow_eq_self_of_SC (SC_Om omega0_pos.ne'))
      ti_BG_le_Omw
  refine dvd_add (dvd_add h1 h1) ?_
  have hE : ω ^ Nc.ncPp S = Nc.ncPp S := Low.opow_eq_self_of_SC (Nc.ncPp_SC S)
  have h2 : Le.leOe μ ∣ Nc.ncPp S :=
    tf_dvd_eps hμ hE (ti_BG_le_Pp S)
  have hI : Indec (ω ^ (Nc.ncPp S + 1)) :=
    indec_iff.2 ⟨(opow_pos _ omega0_pos).ne', isPrincipal_add_omega0_opow _⟩
  refine rh_dvd_of_indec μ hI ((Ordinal.le_of_dvd (inE_indec hE).ne_zero h2).trans ?_)
  conv_lhs => rw [← hE]
  exact opow_le_opow_right omega0_pos le_self_add

/-- **The level moves**: for a code `μ` over `c_{n+1}`: `μ` is in the domain of `B_n`, `μ < Γ_{Ω₁+1}`, `B_n μ <
Γ_{Ω₁+1}`, `B_n μ` is a code over `B_n c_{n+1}`, and `B_n(μ + 1) = B_n μ + 1`. -/
theorem ti_B_lvl {n : ℕ} {μ : Ordinal.{0}} (hμ : TfCl (Bc.bcC S (n + 1)) μ) (hμΓ : μ < tfBG) :
    MvD S μ ∧ μ < tfBG ∧ Bc.bcB S n μ < tfBG ∧ Bc.bcB S n (μ + 1) = Bc.bcB S n μ + 1 := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hc1 : Bc.bcC S (n + 1) ≤ Om1 := by
    rw [Rj.rj_Om1]; exact (hLw.trans (InaccSeq.psi_lt Low.InR_Om_one _)).le
  have hD := (tiB_cl (n := n) hμ).1
  exact ⟨hD, hμΓ, tiB_lt_BG hμ, rkB_succ hD⟩

/-- **`tfDatL (B_n μ) = B_n (tfDatL μ)`** for a code `μ` over `c_{n+1}`. -/
theorem ti_B_datL {n : ℕ} {μ : Ordinal.{0}} (hμ : TfCl (Bc.bcC S (n + 1)) μ) (hμΓ : μ < tfBG) :
    tfDatL (Bc.bcB S n μ) = Bc.bcB S n (tfDatL μ) := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hD := (tiB_cl (n := n) hμ).1
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  have e : Bc.bcB S n (Om1 + μ) = Om1 + Bc.bcB S n μ := by
    rw [Rj.rj_Om1, (mvB_add (k := n) hDO hD).2, hBO]
  unfold tfDatL
  rw [← e]
  exact tiB_dat (TfCl.add TfCl.om hμ)

/-- **`u_μ ∣ B` gives `u_{B_n μ} ∣ B'`** for `B = α_{n+1} + |r|`, `B' = α_ω + |σ r|`, a code `μ` over `c_{n+1}`. -/
theorem ti_B_dvd {n : ℕ} {μ : Ordinal.{0}} (hμ : TfCl (Bc.bcC S (n + 1)) μ) (hμΓ : μ < tfBG)
    {B : Ordinal.{0}} {r : Term} (hr : bcD S r)
    (hB : B = bcAlpha S (n + 1) + val S r) (h : Le.leOe μ ∣ B) :
    Le.leOe (Bc.bcB S n μ) ∣ bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) :=
  tiB_dvd hμ (ti_dvd_alpha (ti_B_lvl hμ hμΓ).2.1.le _) (ti_dvd_alphaW (ti_B_lvl hμ hμΓ).2.2.1.le) hr hB h

/-- **`u_μ ∣ B`** for an own `B` whose collapse is a fixed point of every `Φ_j`, `j < μ`, `tfDatL j < ψ_{Ω₁}(B)`
(`μ ≤ Γ_{Ω₁+1}`). -/
theorem ti_dvd_of_range {μ B : Ordinal.{0}} (hμΩ : μ ≤ tfBG) (hown : B ∈ S.CSet B (S.psi B (Om 1)))
    (hfix : ∀ j < μ, tfDatL j < S.psi B (Om 1) → tfP j (S.psi B (Om 1)) = S.psi B (Om 1)) :
    Le.leOe μ ∣ B := by
  set p := S.psi B (Om 1) with hpdef
  have hpSC : SC p := SC_psi Low.InR_Om_one B
  have hcoll : ∀ e, e < B → e ∈ S.CSet B p → RiDg p e → TfLev p e → S.psi e (Om 1) < p :=
    fun e he heC _ _ => lt_psi_of_mem Low.InR_Om_one
      (CSet.psi_mem he Low.InR_Om_one (mem_CSet_psi Low.InR_Om_one B) heC) (psi_lt Low.InR_Om_one _)
  have hdl := tf_diglev (S := S) hpSC hcoll B hown
  refine Ri.ri_dvd_of_dig μ fun j hj => ?_
  have hjΩ : j < tfBG := hj.trans_le hμΩ
  by_cases hd : tfDatL j < p
  · exact Ri.ri_dig_zero_of_dvd (tf_conv hjΩ hown (hfix j hj hd))
  · by_contra hd0
    exact hd (hdl.2.1 j hjΩ hd0)

/-- The window facts for `x < c_{n+1}`: `x` and `B_n x` are countable and in the domain. -/
theorem ti_win {n : ℕ} {x : Ordinal.{0}} (hx : x < Bc.bcC S (n + 1)) :
    x < Nc.ncL S ω ∧ x < Om 1 ∧ Bc.bcB S n x < Om 1 := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  obtain ⟨h1, h2⟩ := Rt.rt_lt_Om1 hx
  rw [Rj.rj_Om1] at h1 h2
  exact ⟨hx.trans hLw, h1, h2⟩

/-- **`B_n` maps a value `v = ψ_{Ω₁}(B) ∈ [c_n, c_{n+1})` of `Φ_μ` (`B` own) to a value of `Φ_{B_n μ}`**, for a code
`μ` over `c_{n+1}`; the image is `ψ_{Ω₁}(B')` with `B'` own and `u_{B_n μ} ∣ B'`. -/
theorem ti_B_val {n : ℕ} {μ B : Ordinal.{0}} (hμ : TfCl (Bc.bcC S (n + 1)) μ) (hμΓ : μ < tfBG)
    (hown : B ∈ S.CSet B (S.psi B (Om 1))) (hlo : Bc.bcC S n ≤ S.psi B (Om 1))
    (hhi : S.psi B (Om 1) < Bc.bcC S (n + 1)) (hv : S.psi B (Om 1) ∈ range (tfP μ)) :
    ∃ r : Term, bcD S r ∧ B = bcAlpha S (n + 1) + val S r ∧
      bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) ∈
        S.CSet (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r))
          (S.psi (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r)) (Om 1)) ∧
      Le.leOe (Bc.bcB S n μ) ∣ bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) ∧
      Bc.bcB S n (S.psi B (Om 1)) = S.psi (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r)) (Om 1) ∧
      Bc.bcB S n (S.psi B (Om 1)) ∈ range (tfP (Bc.bcB S n μ)) := by
  obtain ⟨hDμ, hμG, hμ'G, -⟩ := ti_B_lvl hμ hμΓ
  have hcS : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  set v := S.psi B (Om 1) with hvdef
  have hvSC : SC v := SC_psi Low.InR_Om_one B
  obtain ⟨hvL, hv1, hBv1⟩ := ti_win (n := n) hhi
  rw [tfP_range_eq] at hv
  have hdvd : Le.leOe μ ∣ B := ti_dvd_of_range hμG.le hown fun j hj hd => hv.2.2 j hj hd
  obtain ⟨r, hDr, hBr, hownB', hBv, -⟩ := tiB_psi (n := n) (D := 0) hμ hown hlo
    (by rw [mul_zero, add_zero]; exact hown) (by rw [mul_zero, add_zero]; exact hhi)
    (lt_of_le_of_lt zero_le (by rw [← Rj.rj_Om1]; exact Rj.rj_Om1_pos.trans_le (by rw [Rj.rj_Om1])))
    (lt_of_le_of_lt zero_le hcS.1)
  set B' := bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) with hB'def
  have hdvd' : Le.leOe (Bc.bcB S n μ) ∣ B' := ti_B_dvd hμ hμΓ hDr hBr hdvd
  refine ⟨r, hDr, hBr, hownB', hdvd', hBv, ?_⟩
  -- the image is a value of `Φ_{μ'}`
  have hB'0 : B' ≠ 0 := by
    rw [hB'def]
    exact (lt_of_lt_of_le (lt_of_le_of_lt zero_le (Bc.bcAlpha_lt_W S 0)) le_self_add).ne'
  have hdμ : tfDatL μ < Bc.bcC S (n + 1) := by
    have h := (tf_cl_iff hcS (lt_of_le_of_lt le_rfl
      (tf_BG_indec.add_lt tfBG_gt hμG))).1 (TfCl.add TfCl.om hμ)
    exact h
  have hdv' : tfDatL (Bc.bcB S n μ) < S.psi B' (Om 1) := by
    rw [ti_B_datL hμ hμΓ, ← hBv]
    exact (Bc.bcB_lt_iff (hdμ.trans (Bc.bcC_lt S (n + 1))) hvL).2 hv.2.1
  rw [hBv, tfP_range_eq]
  refine ⟨SC_psi Low.InR_Om_one _, hdv', fun j hj hdj => ?_⟩
  exact tfFwdAll j (hj.trans hμ'G) B' hownB' ((rhU_dvd_succ hj).trans hdvd') hB'0 hdj

/-- **`B_n` maps a fixed point `p = ψ_{Ω₁}(B) ∈ [c_n, c_{n+1})` of `Φ_μ` (`B` own) to a fixed point of
`Φ_{B_n μ}`**, for a code `μ` over `c_{n+1}`. -/
theorem ti_B_fix {n : ℕ} {μ B : Ordinal.{0}} (hμ : TfCl (Bc.bcC S (n + 1)) μ) (hμΓ : μ < tfBG)
    (hown : B ∈ S.CSet B (S.psi B (Om 1))) (hlo : Bc.bcC S n ≤ S.psi B (Om 1))
    (hhi : S.psi B (Om 1) < Bc.bcC S (n + 1)) (hp : tfP μ (S.psi B (Om 1)) = S.psi B (Om 1)) :
    tfP (Bc.bcB S n μ) (Bc.bcB S n (S.psi B (Om 1))) = Bc.bcB S n (S.psi B (Om 1)) := by
  obtain ⟨hDμ, hμG, hμ'G, hBsucc⟩ := ti_B_lvl hμ hμΓ
  have hcS : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  have hcl1 : TfCl (Bc.bcC S (n + 1)) (μ + 1) := TfCl.add hμ (TfCl.small (gg_one_lt_of_SC hcS))
  obtain ⟨r, hDr, hBr, hownB', -, hBv, -⟩ := ti_B_val hμ hμΓ hown hlo hhi ⟨_, hp⟩
  have hdvd1 : Le.leOe (μ + 1) ∣ B := tf_conv hμG hown hp
  have hdvd1' := ti_B_dvd hcl1 (tfBG_SC.add_one_lt hμΓ) hDr hBr hdvd1
  rw [hBsucc] at hdvd1'
  have hB'0 : bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) ≠ 0 :=
    (lt_of_lt_of_le (lt_of_le_of_lt zero_le (Bc.bcAlpha_lt_W S 0)) le_self_add).ne'
  obtain ⟨hvL, -, -⟩ := ti_win (n := n) hhi
  have hdμ : tfDatL μ < S.psi B (Om 1) := tfDatL_lt_fix hp
  have hdμL : tfDatL μ < Nc.ncL S ω := hdμ.trans hvL
  have hdv' : tfDatL (Bc.bcB S n μ) < Bc.bcB S n (S.psi B (Om 1)) := by
    rw [ti_B_datL hμ hμΓ]; exact (Bc.bcB_lt_iff hdμL hvL).2 hdμ
  rw [hBv] at hdv' ⊢
  exact tfFwdAll _ hμ'G _ hownB' hdvd1' hB'0 hdv'

/-- **The run of `Φ_μ` from an own base point moves to a run of `Φ_{B_n μ}`.** -/
theorem ti_B_run {n : ℕ} {μ B0 c0 δ : Ordinal.{0}} (hμ : TfCl (Bc.bcC S (n + 1)) μ) (hμΓ : μ < tfBG)
    (hown0 : B0 ∈ S.CSet B0 (S.psi B0 (Om 1))) (hdvd0 : Le.leOe μ ∣ B0)
    (hc0 : tfP μ c0 = S.psi B0 (Om 1)) (hlo : Bc.bcC S n ≤ S.psi B0 (Om 1))
    (hd0 : tfDatL μ < S.psi B0 (Om 1))
    (hx : tfP μ (c0 + 1 + δ) < Bc.bcC S (n + 1))
    (hcond : ∀ σ, σ ≤ δ → c0 + 1 + σ < tfP μ (c0 + 1 + σ)) :
    ∃ B', B' ∈ S.CSet B' (S.psi B' (Om 1)) ∧ Le.leOe (Bc.bcB S n μ) ∣ B' ∧
      Bc.bcB S n (S.psi B0 (Om 1)) = S.psi B' (Om 1) ∧
      ∀ c1, tfP (Bc.bcB S n μ) c1 = S.psi B' (Om 1) →
        Bc.bcB S n (tfP μ (c0 + 1 + δ)) = tfP (Bc.bcB S n μ) (c1 + 1 + Bc.bcB S n δ) ∧
        ∀ σ, σ ≤ Bc.bcB S n δ → c1 + 1 + σ < tfP (Bc.bcB S n μ) (c1 + 1 + σ) := by
  obtain ⟨hDμ, hμG, hμ'G, -⟩ := ti_B_lvl hμ hμΓ
  set x := tfP μ (c0 + 1 + δ) with hxdef
  obtain ⟨hxL, hx1, hBx1⟩ := ti_win (n := n) hx
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
  have hcondD : ∀ d, d ≤ D → d < tfP μ (c0 + d) := by
    intro d hd
    rcases eq_or_ne d 0 with rfl | hd0
    · exact (tfP_SC μ _).1
    have hσ : 1 + (d - 1) = d := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hd0)
    have hσδ : d - 1 ≤ δ := by
      rw [← hσ] at hd; exact (add_le_add_iff_left 1).1 hd
    have h := hcond _ hσδ
    rw [add_assoc, hσ] at h
    exact le_add_self.trans_lt h
  obtain ⟨hval, hψ⟩ := tf_eq hμG hown0 hdvd0 hc0 hd0 D (hDx.trans hx1) hcondD
  have hψx : S.psi (B0 + Le.leOe μ * D) (Om 1) = x := by rw [hψ, hcD]
  have hown1 : B0 + Le.leOe μ * D ∈ S.CSet (B0 + Le.leOe μ * D) (S.psi (B0 + Le.leOe μ * D) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add : B0 ≤ B0 + Le.leOe μ * D)).2 hown0)
      (tf_U_mul_mem (SC_psi Low.InR_Om_one _) (by rw [Rj.rj_Om1]; exact (psi_lt Low.InR_Om_one _).le) hμG
        (hd0.trans_le (psi_mono (S := S) Low.InR_Om_one le_self_add).1) hval le_add_self)
  obtain ⟨r, hDr, hBr, hownB', hB0', hBx⟩ := tiB_psi (n := n) hμ hown0 hlo hown1
    (by rw [hψx]; exact hx) (hDx.trans hx1) (hDx.trans hx)
  set B' := bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) with hB'def
  have hdvd' : Le.leOe (Bc.bcB S n μ) ∣ B' := ti_B_dvd hμ hμΓ hDr hBr hdvd0
  rw [hψx] at hBx
  have hBDx : Bc.bcB S n D < Bc.bcB S n x := (Bc.bcB_lt_iff hDL hxL).2 hDx
  have hval' : Bc.bcB S n D < S.psi (B' + Le.leOe (Bc.bcB S n μ) * Bc.bcB S n D) (Om 1) := by
    rw [← hBx]; exact hBDx
  have hBD : Bc.bcB S n D = 1 + Bc.bcB S n δ := by rw [hDdef, Bc.bcB_add h1L hδL, Mw.mwB_one]
  refine ⟨B', hownB', hdvd', hB0', fun c1 hc1 => ?_⟩
  have hcondD' := tf_valid hμ'G.le hdvd' hc1 hval'
  have hd1 : tfDatL (Bc.bcB S n μ) < S.psi B' (Om 1) := by
    rw [ti_B_datL hμ hμΓ, ← hB0']
    have hvL : S.psi B0 (Om 1) < Nc.ncL S ω := by
      rw [← hc0]; exact ((tfP_le_iff μ).2 (le_self_add.trans le_self_add)).trans_lt hxL
    exact (Bc.bcB_lt_iff (hd0.trans hvL) hvL).2 hd0
  have hBxF : Bc.bcB S n x = tfP (Bc.bcB S n μ) (c1 + Bc.bcB S n D) := by
    rw [hBx]
    exact (tf_eq hμ'G hownB' hdvd' hc1 hd1 (Bc.bcB S n D) (hBDx.trans hBx1) hcondD').2
  refine ⟨by rw [hBxF, hBD, add_assoc], fun σ hσ => ?_⟩
  have h1 := hcondD' (1 + σ) (by rw [hBD]; exact (add_le_add_iff_left 1).2 hσ)
  have h2 : c1 < tfP (Bc.bcB S n μ) (c1 + (1 + σ)) :=
    (tfP_le_self _ c1).trans_lt
      ((tfP_lt_iff _).2 (lt_add_of_pos_right _ (lt_of_lt_of_le zero_lt_one le_self_add)))
  rw [add_assoc]
  exact (lq_SC_indec (tfP_SC _ _)).add_lt h2 h1

end Googology.Trans.PoR.InaccPsi.R2.Ti
