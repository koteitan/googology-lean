import Googology.Trans.PoR.InaccPsi.R2.SvPsi

/-!
# The `ψ_{Ω₁}`-side of the move at every level `μ < Γ_{Ω₁+1}`: `B_n` maps the runs of `Φ_μ` to runs of `Φ_{B_n μ}`

`B_n = Bc.bcB S n`, `c_n = L(n+1) = Bc.bcC S n`, `Φ_μ = Ss.ssP μ` (data `ssDatL μ = ssDat(Ω₁ + μ)`), `u_μ = Ω₁^μ`,
`μ' = B_n μ`, `B = α_{n+1} + |r|`, `B' = α_ω + |σ r|` (the argument maps of `Bc`).  `R2.SsMove` does this at the one
level `E₁ = ε_{Ω₁+1}` (where `B_n E₁ = E₁`); here every Veblen level `μ < Γ_{Ω₁+1}` that is a code over `c_{n+1}` is
moved, with `μ' = B_n μ` in general different from `μ`:

* `sv_dvd_alpha`, `sv_dvd_alphaW` (**`u_μ ∣ α_j`, `u_μ ∣ α_ω`** for `μ ≤ Γ_{Ω₁+1}`), `sv_B_dvd` (**`u_μ ∣ B` gives
  `u_{μ'} ∣ B'`**), `sv_B_datL` (**`ssDatL μ' = B_n(ssDatL μ)`**), `sv_B_lvl` (`μ' < Γ_{Ω₁+1}`, `B_n(μ + 1) = μ' +
  1`);
* `sv_dvd_of_range` (**`u_μ ∣ B`** for an own `B` whose collapse is a fixed point of every `Φ_j`, `j < μ`, `ssDatL j`
  below it);
* `sv_B_fix` (**`B_n` maps a fixed point `p ∈ [c_n, c_{n+1})` of `Φ_μ` to a fixed point of `Φ_{μ'}`**), `sv_B_val`
  (**`B_n` maps a value `v ∈ [c_n, c_{n+1})` of `Φ_μ` to a value of `Φ_{μ'}`**);
* `sv_B_run` (**the run**: for an own `B₀` with `u_μ ∣ B₀`, `Φ_μ(c₀) = ψ_{Ω₁}(B₀) ≥ c_n`, `ssDatL μ < ψ_{Ω₁}(B₀)`,
  and `x = Φ_μ(c₀ + 1 + δ) < c_{n+1}` with no fixed point of `Φ_μ` at the indices `c₀ + 1 + σ`, `σ ≤ δ`:
  `B_n(ψ_{Ω₁}(B₀)) = ψ_{Ω₁}(B')` with `B'` own, `u_{μ'} ∣ B'`, and for every index `c₁` of `ψ_{Ω₁}(B')` in `Φ_{μ'}`:
  **`B_n x = Φ_{μ'}(c₁ + 1 + B_n δ)`**, with no fixed point of `Φ_{μ'}` at the indices `c₁ + 1 + σ`, `σ ≤ B_n δ`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Sv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rb
  Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Ri
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rk Googology.Trans.PoR.InaccPsi.R2.Ss
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2.Bc

variable {S : InaccSeq.{0}}

/-- **`u_μ ∣ α_j`** for `μ ≤ Γ_{Ω₁+1}`. -/
theorem sv_dvd_alpha {μ : Ordinal.{0}} (hμ : μ ≤ ggGam) (j : ℕ) : Le.leOe μ ∣ bcAlpha S j := by
  have h1 : Le.leOe μ ∣ Om (ω : Ordinal.{0}) :=
    sv_dvd_eps hμ (Low.opow_eq_self_of_SC (SC_Om omega0_pos.ne'))
      (ggGam_le (SC_Om omega0_pos.ne') (Om_lt_Om.2 one_lt_omega0))
  have h2 : Le.leOe μ ∣ Nc.ncPp S :=
    sv_dvd_eps hμ (Low.opow_eq_self_of_SC (Nc.ncPp_SC S)) (ggGam_le (Nc.ncPp_SC S) rb_Om1_lt_Pp)
  exact dvd_add (dvd_add h1 h1) (dvd_mul_of_dvd_left h2 _)

/-- **`u_μ ∣ α_ω`** for `μ ≤ Γ_{Ω₁+1}`. -/
theorem sv_dvd_alphaW {μ : Ordinal.{0}} (hμ : μ ≤ ggGam) : Le.leOe μ ∣ bcAlphaW S := by
  have h1 : Le.leOe μ ∣ Om (ω : Ordinal.{0}) :=
    sv_dvd_eps hμ (Low.opow_eq_self_of_SC (SC_Om omega0_pos.ne'))
      (ggGam_le (SC_Om omega0_pos.ne') (Om_lt_Om.2 one_lt_omega0))
  refine dvd_add (dvd_add h1 h1) ?_
  have hE : ω ^ Nc.ncPp S = Nc.ncPp S := Low.opow_eq_self_of_SC (Nc.ncPp_SC S)
  have h2 : Le.leOe μ ∣ Nc.ncPp S := sv_dvd_eps hμ hE (ggGam_le (Nc.ncPp_SC S) rb_Om1_lt_Pp)
  have hI : Indec (ω ^ (Nc.ncPp S + 1)) :=
    indec_iff.2 ⟨(opow_pos _ omega0_pos).ne', isPrincipal_add_omega0_opow _⟩
  refine rh_dvd_of_indec μ hI ((Ordinal.le_of_dvd (inE_indec hE).ne_zero h2).trans ?_)
  conv_lhs => rw [← hE]
  exact opow_le_opow_right omega0_pos le_self_add

/-- **The level moves**: for a code `μ` over `c_{n+1}`: `μ` is in the domain of `B_n`, `μ < Γ_{Ω₁+1}`, `B_n μ <
Γ_{Ω₁+1}`, `B_n μ` is a code over `B_n c_{n+1}`, and `B_n(μ + 1) = B_n μ + 1`. -/
theorem sv_B_lvl {n : ℕ} {μ : Ordinal.{0}} (hμ : GgCl (Bc.bcC S (n + 1)) μ) :
    MvD S μ ∧ μ < ggGam ∧ Bc.bcB S n μ < ggGam ∧ Bc.bcB S n (μ + 1) = Bc.bcB S n μ + 1 := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hc1 : Bc.bcC S (n + 1) ≤ Om1 := by
    rw [Rj.rj_Om1]; exact (hLw.trans (InaccSeq.psi_lt Low.InR_Om_one _)).le
  have hD := (rkB_cl (n := n) hLw μ hμ).1
  exact ⟨hD, ss_cl_lt_Gam (hc1.trans ss_Om1_lt_Gam.le) hμ, ssB_lt_Gam hμ, rkB_succ hD⟩

/-- **`ssDatL (B_n μ) = B_n (ssDatL μ)`** for a code `μ` over `c_{n+1}`. -/
theorem sv_B_datL {n : ℕ} {μ : Ordinal.{0}} (hμ : GgCl (Bc.bcC S (n + 1)) μ) :
    ssDatL (Bc.bcB S n μ) = Bc.bcB S n (ssDatL μ) := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hD := (rkB_cl (n := n) hLw μ hμ).1
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  have e : Bc.bcB S n (Om1 + μ) = Om1 + Bc.bcB S n μ := by
    rw [Rj.rj_Om1, (mvB_add (k := n) hDO hD).2, hBO]
  unfold ssDatL
  rw [← e]
  exact ssB_dat _ (by rw [Rj.rj_Om1]; exact GgCl.add GgCl.om hμ)

/-- **`u_μ ∣ B` gives `u_{B_n μ} ∣ B'`** for `B = α_{n+1} + |r|`, `B' = α_ω + |σ r|`, a code `μ` over `c_{n+1}`. -/
theorem sv_B_dvd {n : ℕ} {μ : Ordinal.{0}} (hμ : GgCl (Bc.bcC S (n + 1)) μ)
    {B : Ordinal.{0}} {r : Term} (hr : bcD S r)
    (hB : B = bcAlpha S (n + 1) + val S r) (h : Le.leOe μ ∣ B) :
    Le.leOe (Bc.bcB S n μ) ∣ bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) :=
  ssB_dvd hμ (sv_dvd_alpha (sv_B_lvl hμ).2.1.le _) (sv_dvd_alphaW (sv_B_lvl hμ).2.2.1.le) hr hB h

/-- **`u_μ ∣ B`** for an own `B` whose collapse is a fixed point of every `Φ_j`, `j < μ`, `ssDatL j < ψ_{Ω₁}(B)`
(`μ ≤ Γ_{Ω₁+1}`). -/
theorem sv_dvd_of_range {μ B : Ordinal.{0}} (hμΩ : μ ≤ ggGam) (hown : B ∈ S.CSet B (S.psi B (Om 1)))
    (hfix : ∀ j < μ, ssDatL j < S.psi B (Om 1) → ssP j (S.psi B (Om 1)) = S.psi B (Om 1)) :
    Le.leOe μ ∣ B := by
  set p := S.psi B (Om 1) with hpdef
  have hpSC : SC p := SC_psi Low.InR_Om_one B
  have hcoll : ∀ e, e < B → e ∈ S.CSet B p → RiDg p e → SvLev p e → S.psi e (Om 1) < p :=
    fun e he heC _ _ => lt_psi_of_mem Low.InR_Om_one
      (CSet.psi_mem he Low.InR_Om_one (mem_CSet_psi Low.InR_Om_one B) heC) (psi_lt Low.InR_Om_one _)
  have hdl := sv_diglev (S := S) hpSC hcoll B hown
  refine Ri.ri_dvd_of_dig μ fun j hj => ?_
  have hjΩ : j < ggGam := hj.trans_le hμΩ
  by_cases hd : ssDatL j < p
  · exact Ri.ri_dig_zero_of_dvd (sv_conv hjΩ hown (hfix j hj hd))
  · by_contra hd0
    exact hd (hdl.2.1 j hjΩ hd0)

/-- The window facts for `x < c_{n+1}`: `x` and `B_n x` are countable and in the domain. -/
theorem sv_win {n : ℕ} {x : Ordinal.{0}} (hx : x < Bc.bcC S (n + 1)) :
    x < Nc.ncL S ω ∧ x < Om 1 ∧ Bc.bcB S n x < Om 1 := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  obtain ⟨h1, h2⟩ := Rt.rt_lt_Om1 hx
  rw [Rj.rj_Om1] at h1 h2
  exact ⟨hx.trans hLw, h1, h2⟩

/-- **`B_n` maps a value `v = ψ_{Ω₁}(B) ∈ [c_n, c_{n+1})` of `Φ_μ` (`B` own) to a value of `Φ_{B_n μ}`**, for a code
`μ` over `c_{n+1}`; the image is `ψ_{Ω₁}(B')` with `B'` own and `u_{B_n μ} ∣ B'`. -/
theorem sv_B_val {n : ℕ} {μ B : Ordinal.{0}} (hμ : GgCl (Bc.bcC S (n + 1)) μ)
    (hown : B ∈ S.CSet B (S.psi B (Om 1))) (hlo : Bc.bcC S n ≤ S.psi B (Om 1))
    (hhi : S.psi B (Om 1) < Bc.bcC S (n + 1)) (hv : S.psi B (Om 1) ∈ range (ssP μ)) :
    ∃ r : Term, bcD S r ∧ B = bcAlpha S (n + 1) + val S r ∧
      bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) ∈
        S.CSet (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r))
          (S.psi (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r)) (Om 1)) ∧
      Le.leOe (Bc.bcB S n μ) ∣ bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) ∧
      Bc.bcB S n (S.psi B (Om 1)) = S.psi (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r)) (Om 1) ∧
      Bc.bcB S n (S.psi B (Om 1)) ∈ range (ssP (Bc.bcB S n μ)) := by
  obtain ⟨hDμ, hμG, hμ'G, -⟩ := sv_B_lvl hμ
  have hcS : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  set v := S.psi B (Om 1) with hvdef
  have hvSC : SC v := SC_psi Low.InR_Om_one B
  obtain ⟨hvL, hv1, hBv1⟩ := sv_win (n := n) hhi
  rw [ssP_range_eq] at hv
  have hdvd : Le.leOe μ ∣ B := sv_dvd_of_range hμG.le hown fun j hj hd => hv.2.2 j hj hd
  obtain ⟨r, hDr, hBr, hownB', hBv, -⟩ := rkB_psi (n := n) (D := 0) hμ hown hlo
    (by rw [mul_zero, add_zero]; exact hown) (by rw [mul_zero, add_zero]; exact hhi)
    (lt_of_le_of_lt zero_le (by rw [← Rj.rj_Om1]; exact Rj.rj_Om1_pos.trans_le (by rw [Rj.rj_Om1])))
    (lt_of_le_of_lt zero_le hcS.1)
  set B' := bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) with hB'def
  have hdvd' : Le.leOe (Bc.bcB S n μ) ∣ B' := sv_B_dvd hμ hDr hBr hdvd
  refine ⟨r, hDr, hBr, hownB', hdvd', hBv, ?_⟩
  -- the image is a value of `Φ_{μ'}`
  have hB'0 : B' ≠ 0 := by
    rw [hB'def]
    exact (lt_of_lt_of_le (lt_of_le_of_lt zero_le (Bc.bcAlpha_lt_W S 0)) le_self_add).ne'
  have hdμ : ssDatL μ < Bc.bcC S (n + 1) := by
    have h := (ss_cl_iff hcS (lt_of_le_of_lt le_rfl
      ((lq_SC_indec ggGam_spec.1).add_lt ss_Om1_lt_Gam hμG))).1 (by rw [Rj.rj_Om1]; exact GgCl.add GgCl.om hμ)
    exact h
  have hdv' : ssDatL (Bc.bcB S n μ) < S.psi B' (Om 1) := by
    rw [sv_B_datL hμ, ← hBv]
    exact (Bc.bcB_lt_iff (hdμ.trans (Bc.bcC_lt S (n + 1))) hvL).2 hv.2.1
  rw [hBv, ssP_range_eq]
  refine ⟨SC_psi Low.InR_Om_one _, hdv', fun j hj hdj => ?_⟩
  exact ssFwdAll j (hj.trans hμ'G) B' hownB' ((rhU_dvd_succ hj).trans hdvd') hB'0 hdj

/-- **`B_n` maps a fixed point `p = ψ_{Ω₁}(B) ∈ [c_n, c_{n+1})` of `Φ_μ` (`B` own) to a fixed point of
`Φ_{B_n μ}`**, for a code `μ` over `c_{n+1}`. -/
theorem sv_B_fix {n : ℕ} {μ B : Ordinal.{0}} (hμ : GgCl (Bc.bcC S (n + 1)) μ)
    (hown : B ∈ S.CSet B (S.psi B (Om 1))) (hlo : Bc.bcC S n ≤ S.psi B (Om 1))
    (hhi : S.psi B (Om 1) < Bc.bcC S (n + 1)) (hp : ssP μ (S.psi B (Om 1)) = S.psi B (Om 1)) :
    ssP (Bc.bcB S n μ) (Bc.bcB S n (S.psi B (Om 1))) = Bc.bcB S n (S.psi B (Om 1)) := by
  obtain ⟨hDμ, hμG, hμ'G, hBsucc⟩ := sv_B_lvl hμ
  have hcS : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  have hcl1 : GgCl (Bc.bcC S (n + 1)) (μ + 1) := GgCl.add hμ (GgCl.small (gg_one_lt_of_SC hcS))
  obtain ⟨r, hDr, hBr, hownB', -, hBv, -⟩ := sv_B_val hμ hown hlo hhi ⟨_, hp⟩
  have hdvd1 : Le.leOe (μ + 1) ∣ B := sv_conv hμG hown hp
  have hdvd1' := sv_B_dvd hcl1 hDr hBr hdvd1
  rw [hBsucc] at hdvd1'
  have hB'0 : bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) ≠ 0 :=
    (lt_of_lt_of_le (lt_of_le_of_lt zero_le (Bc.bcAlpha_lt_W S 0)) le_self_add).ne'
  obtain ⟨hvL, -, -⟩ := sv_win (n := n) hhi
  have hdμ : ssDatL μ < S.psi B (Om 1) := ssDatL_lt_fix hp
  have hdμL : ssDatL μ < Nc.ncL S ω := hdμ.trans hvL
  have hdv' : ssDatL (Bc.bcB S n μ) < Bc.bcB S n (S.psi B (Om 1)) := by
    rw [sv_B_datL hμ]; exact (Bc.bcB_lt_iff hdμL hvL).2 hdμ
  rw [hBv] at hdv' ⊢
  exact ssFwdAll _ hμ'G _ hownB' hdvd1' hB'0 hdv'

/-- **The run of `Φ_μ` from an own base point moves to a run of `Φ_{B_n μ}`.** -/
theorem sv_B_run {n : ℕ} {μ B0 c0 δ : Ordinal.{0}} (hμ : GgCl (Bc.bcC S (n + 1)) μ)
    (hown0 : B0 ∈ S.CSet B0 (S.psi B0 (Om 1))) (hdvd0 : Le.leOe μ ∣ B0)
    (hc0 : ssP μ c0 = S.psi B0 (Om 1)) (hlo : Bc.bcC S n ≤ S.psi B0 (Om 1))
    (hd0 : ssDatL μ < S.psi B0 (Om 1))
    (hx : ssP μ (c0 + 1 + δ) < Bc.bcC S (n + 1))
    (hcond : ∀ σ, σ ≤ δ → c0 + 1 + σ < ssP μ (c0 + 1 + σ)) :
    ∃ B', B' ∈ S.CSet B' (S.psi B' (Om 1)) ∧ Le.leOe (Bc.bcB S n μ) ∣ B' ∧
      Bc.bcB S n (S.psi B0 (Om 1)) = S.psi B' (Om 1) ∧
      ∀ c1, ssP (Bc.bcB S n μ) c1 = S.psi B' (Om 1) →
        Bc.bcB S n (ssP μ (c0 + 1 + δ)) = ssP (Bc.bcB S n μ) (c1 + 1 + Bc.bcB S n δ) ∧
        ∀ σ, σ ≤ Bc.bcB S n δ → c1 + 1 + σ < ssP (Bc.bcB S n μ) (c1 + 1 + σ) := by
  obtain ⟨hDμ, hμG, hμ'G, -⟩ := sv_B_lvl hμ
  set x := ssP μ (c0 + 1 + δ) with hxdef
  obtain ⟨hxL, hx1, hBx1⟩ := sv_win (n := n) hx
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
  have hcondD : ∀ d, d ≤ D → d < ssP μ (c0 + d) := by
    intro d hd
    rcases eq_or_ne d 0 with rfl | hd0
    · exact (ssP_SC μ _).1
    have hσ : 1 + (d - 1) = d := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hd0)
    have hσδ : d - 1 ≤ δ := by
      rw [← hσ] at hd; exact (add_le_add_iff_left 1).1 hd
    have h := hcond _ hσδ
    rw [add_assoc, hσ] at h
    exact le_add_self.trans_lt h
  obtain ⟨hval, hψ⟩ := sv_eq hμG hown0 hdvd0 hc0 hd0 D (hDx.trans hx1) hcondD
  have hψx : S.psi (B0 + Le.leOe μ * D) (Om 1) = x := by rw [hψ, hcD]
  have hown1 : B0 + Le.leOe μ * D ∈ S.CSet (B0 + Le.leOe μ * D) (S.psi (B0 + Le.leOe μ * D) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add : B0 ≤ B0 + Le.leOe μ * D)).2 hown0)
      (sv_U_mul_mem (SC_psi Low.InR_Om_one _) hμG
        (hd0.trans_le (psi_mono (S := S) Low.InR_Om_one le_self_add).1) hval)
  obtain ⟨r, hDr, hBr, hownB', hB0', hBx⟩ := rkB_psi (n := n) hμ hown0 hlo hown1
    (by rw [hψx]; exact hx) (hDx.trans hx1) (hDx.trans hx)
  set B' := bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) with hB'def
  have hdvd' : Le.leOe (Bc.bcB S n μ) ∣ B' := sv_B_dvd hμ hDr hBr hdvd0
  rw [hψx] at hBx
  have hBDx : Bc.bcB S n D < Bc.bcB S n x := (Bc.bcB_lt_iff hDL hxL).2 hDx
  have hval' : Bc.bcB S n D < S.psi (B' + Le.leOe (Bc.bcB S n μ) * Bc.bcB S n D) (Om 1) := by
    rw [← hBx]; exact hBDx
  have hBD : Bc.bcB S n D = 1 + Bc.bcB S n δ := by rw [hDdef, Bc.bcB_add h1L hδL, Mw.mwB_one]
  refine ⟨B', hownB', hdvd', hB0', fun c1 hc1 => ?_⟩
  have hcondD' := sv_valid hμ'G.le hdvd' hc1 hval'
  have hd1 : ssDatL (Bc.bcB S n μ) < S.psi B' (Om 1) := by
    rw [sv_B_datL hμ, ← hB0']
    have hvL : S.psi B0 (Om 1) < Nc.ncL S ω := by
      rw [← hc0]; exact ((ssP_le_iff μ).2 (le_self_add.trans le_self_add)).trans_lt hxL
    exact (Bc.bcB_lt_iff (hd0.trans hvL) hvL).2 hd0
  have hBxF : Bc.bcB S n x = ssP (Bc.bcB S n μ) (c1 + Bc.bcB S n D) := by
    rw [hBx]
    exact (sv_eq hμ'G hownB' hdvd' hc1 hd1 (Bc.bcB S n D) (hBDx.trans hBx1) hcondD').2
  refine ⟨by rw [hBxF, hBD, add_assoc], fun σ hσ => ?_⟩
  have h1 := hcondD' (1 + σ) (by rw [hBD]; exact (add_le_add_iff_left 1).2 hσ)
  have h2 : c1 < ssP (Bc.bcB S n μ) (c1 + (1 + σ)) :=
    (ssP_le_self _ c1).trans_lt
      ((ssP_lt_iff _).2 (lt_add_of_pos_right _ (lt_of_lt_of_le zero_lt_one le_self_add)))
  rw [add_assoc]
  exact (lq_SC_indec (ssP_SC _ _)).add_lt h2 h1

end Googology.Trans.PoR.InaccPsi.R2.Sv
