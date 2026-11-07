import Googology.Trans.PoR.InaccPsi.R2.QfK
import Googology.Trans.PoR.InaccPsi.R2.QfZeta
import Googology.Trans.PoR.InaccPsi.R2.QcLh
import Googology.Trans.PoR.InaccPsi.R2.HcLImg
import Googology.Trans.PoR.InaccPsi.R2.PhUni

/-!
# QfLh: THE REACH OF A POINT OF A VEBLEN LEVEL, AS THE READING OF A CODE

For a strongly critical base `y < Ω₁`, the readings `Θ_y` of the codes below `Γ_{Ω₁+1}` lie below `Γ_{y+1}`
(`qf_th_lt_G`); an `ε`-code `p = φ(a, b)` reads as the Veblen point `φ(Θ_y a, Θ_y b)` over `y`, whose reach is
`luL(·, Θ_y a) + logend(Θ_y b)` (`Qf.qf_lh`), the reading of the code `qfRe p = p·(1+a) + e_a + logend(b)`
(`qf_re`); a power `ω^x` (`x < ω^x`) has the reach `ω^x + logend(x)` (`Lu.lu_lh_opow`, `qf_pow`).  With the cited
`R2.qfLhT`:

* `qfLam M` (**the reach code of the level `M`**: `qfRe(c) + Ω₁·M` if `QfCr M`; `qfRe(l) + (Ω₁·M − ω^l)` if
  `ω^l = l`; `ω^l + logend(l) + (Ω₁·M − ω^l)` otherwise; `l = qfL M`, `c = qfC M`);
* `qf_lh_lvl` (**`lh(ϑᵖ(Ω₁·M + σ)) = Θ_E(qfLam M) + ζ`**, `E = ϑᵖ(Ω₁·M + σ)`, `ζ = lqZeta ρ (Ω₁·M) σ`, for every
  Veblen level `ε_{Ω₁+1} ≤ M < Γ_{Ω₁+1}` with `tfDat M ∈ Tᵖ`).

No new axiom beyond `R2.CitedQf`.  New definitions: `qfRe`, `qfLam`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Hc

/-- **The reach code of an `ε`-code `p = φ(a, b)`**: `p·(1+a) + e_a + logend(b)`. -/
noncomputable def qfRe (p : Ordinal.{0}) : Ordinal.{0} :=
  p * (1 + invVeblen₁ p) + hcE (invVeblen₁ p) + lg (invVeblen₂ p)

open Classical in
/-- **The reach code of the Veblen level `M`.** -/
noncomputable def qfLam (M : Ordinal.{0}) : Ordinal.{0} :=
  if QfCr M then qfRe (qfC M) + Om1 * M
  else if ω ^ qfL M = qfL M then qfRe (qfL M) + (Om1 * M - ω ^ qfL M)
  else ω ^ qfL M + lg (qfL M) + (Om1 * M - ω ^ qfL M)

/-- A fixed point of `x ↦ φ(x, 0)` is strongly critical. -/
theorem qf_SC_of_fix {p : Ordinal.{0}} (hp0 : 0 < p) (h : veblen p 0 = p) : SC p := by
  refine ⟨hp0, fun a ha b hb => ?_⟩
  have h1 : veblen a b < veblen a p := (veblen_lt_veblen_iff_right).2 hb
  have h2 : veblen a p = p := by
    have := veblen_veblen_of_lt ha (0 : Ordinal.{0}); rwa [h] at this
  rwa [h2] at h1

section Base

variable {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om1)
include hy hy1

omit hy in
theorem qf_y1 : y < Om 1 := by rw [← rj_Om1]; exact hy1

/-- **The readings of the codes lie below `Γ_{y+1}`.** -/
theorem qf_th_lt_G : ∀ z, GgCl y z → ggTh y z < lgG y := by
  intro z hz
  have hG := Lp.lpG_facts hy (qf_y1 hy1)
  have hGS : SC (lgG y) := Lp.lpG_SC hy (qf_y1 hy1)
  induction hz with
  | small h => rw [ggTh_small h.le]; exact h.trans hG.1
  | om => rw [ggTh_Om1 hy (qf_y1 hy1)]; exact hG.1
  | @add x w hx _ ihx ihw =>
    rw [ggTh_add hy hx]; exact (Lq.lq_SC_indec hGS).add_lt ihx ihw
  | @phi x w hx hw ihx ihw =>
    rw [Ph.phTh_phi hy x hx w hw]; exact hGS.2 _ ihx _ ihw

omit hy1 in
/-- `e_a` is a code. -/
theorem qf_hcE_code {a : Ordinal.{0}} (ha : GgCl y a) : GgCl y (hcE a) := by
  unfold hcE
  split_ifs
  · exact Qc.qc_lg_code hy (ggDec hy a ha).2
  · exact GgCl.small hy.1

omit hy1 in
/-- **`Θ_y(e_a) = e_{Θ_y a}`.** -/
theorem qf_th_hcE {a : Ordinal.{0}} (ha : GgCl y a) : ggTh y (hcE a) = hcE (ggTh y a) := by
  classical
  have hωy : ω < y := Lw.lw_omega_lt_SC hy
  have hTω : ggTh y ω = ω := ggTh_small hωy.le
  have hlogC : GgCl y (log ω a) := (ggDec hy a ha).2
  have hwC : GgCl y (ω ^ log ω a) := GgCl.opow hy.1 hlogC
  have hc1 : ω ≤ a ↔ ω ≤ ggTh y a := by
    constructor
    · intro h; rw [← hTω]; exact ggTh_mono h
    · intro h; by_contra hc; push Not at hc
      rw [ggTh_small (hc.trans hωy).le] at h; exact absurd hc (not_lt.2 h)
  have hc2 : a = ω ^ log ω a ↔ ggTh y a = ω ^ log ω (ggTh y a) := by
    have e : ggTh y (ω ^ log ω a) = ω ^ log ω (ggTh y a) := by rw [ggTh_opow hy hlogC, Qc.qc_th_log hy ha]
    constructor
    · intro h; conv_lhs => rw [h]
      exact e
    · intro h; exact Ph.phTh_inj ha hwC (h.trans e.symm)
  unfold hcE
  by_cases hcond : ω ≤ a ∧ a = ω ^ log ω a
  · rw [if_pos hcond, if_pos ⟨hc1.1 hcond.1, hc2.1 hcond.2⟩]
    rcases eq_or_ne (log ω a) 0 with h0 | h0
    · rw [h0, Qc.qc_lg_zero, ggTh_small zero_le, ← Qc.qc_th_log hy ha, h0, ggTh_small zero_le, Qc.qc_lg_zero]
    · rw [Qc.qc_th_lg hy hlogC h0, Qc.qc_th_log hy ha]
  · rw [if_neg hcond, if_neg (fun h => hcond ⟨hc1.2 h.1, hc2.2 h.2⟩), ggTh_small zero_le]

/-- **An `ε`-code `p ∈ (Ω₁, Γ_{Ω₁+1})` is `φ(a, b)` with codes `1 ≤ a < p`, `b < p`.** -/
theorem qf_eps_dec {p : Ordinal.{0}} (hp : GgCl y p) (hp1 : Om 1 < p) (hpE : ω ^ p = p) :
    veblen (invVeblen₁ p) (invVeblen₂ p) = p ∧ invVeblen₂ p < p ∧ GgCl y (invVeblen₁ p) ∧
      GgCl y (invVeblen₂ p) ∧ 1 ≤ invVeblen₁ p ∧ invVeblen₁ p < p := by
  have hdec : veblen (invVeblen₁ p) (invVeblen₂ p) = p := by rw [veblen_invVeblen₁_invVeblen₂, hpE]
  have hb1 : invVeblen₂ p < p := by have := invVeblen₂_lt p; rwa [hpE] at this
  obtain ⟨ha, hb⟩ := Ph.phDec hy.1 hp _ _ hdec hb1
  have ha1 : 1 ≤ invVeblen₁ p := by
    refine one_le_iff_ne_zero.2 fun h0 => ?_
    rw [h0, veblen_zero_apply] at hdec
    have e : ω ^ invVeblen₂ p = ω ^ p := hdec.trans hpE.symm
    rw [(opow_right_inj one_lt_omega0).1 e] at hb1
    exact lt_irrefl _ hb1
  have hap : invVeblen₁ p < p := by
    refine lt_of_le_of_ne ((left_le_veblen (invVeblen₁ p) (invVeblen₂ p)).trans_eq hdec) fun e => ?_
    have hfix : veblen p 0 = p := by
      refine le_antisymm ?_ (left_le_veblen p 0)
      calc veblen p 0 ≤ veblen p (invVeblen₂ p) := (veblen_le_veblen_iff_right).2 zero_le
        _ = veblen (invVeblen₁ p) (invVeblen₂ p) := by rw [e]
        _ = p := hdec
    have hS := qf_SC_of_fix ((Om_pos one_ne_zero).trans hp1) hfix
    have hpG : p < ggGam := Ph.ph_lt_Gam (hp.mono (qf_y1 hy1).le)
    exact absurd (ggGam_le hS hp1) (not_le.2 hpG)
  exact ⟨hdec, hb1, ha, hb, ha1, hap⟩

/-- **The reach of the reading of an `ε`-code** `p ∈ (Ω₁, Γ_{Ω₁+1})`: `lh(Θ_y p) = Θ_y(qfRe p)`. -/
theorem qf_re {p : Ordinal.{0}} (hp : GgCl y p) (hp1 : Om 1 < p) (hpE : ω ^ p = p) :
    GgCl y (qfRe p) ∧ IsLh1 (ggTh y p) (ggTh y (qfRe p)) := by
  obtain ⟨hdec, hb1, ha, hb, ha1, hap⟩ := qf_eps_dec hy hy1 hp hp1 hpE
  set a := invVeblen₁ p with hadef
  set b := invVeblen₂ p with hbdef
  have h1C : GgCl y (1 : Ordinal.{0}) := GgCl.small (gg_one_lt_of_SC hy)
  have h1a : GgCl y (1 + a) := GgCl.add h1C ha
  have hpa : GgCl y (p * (1 + a)) := by
    have := Ph.ph_cl_opow_mul hy hp (1 + a) h1a
    rwa [hpE] at this
  have hlgb : GgCl y (lg b) := Qc.qc_lg_code hy hb
  have hReC : GgCl y (qfRe p) := GgCl.add (GgCl.add hpa (qf_hcE_code hy ha)) hlgb
  refine ⟨hReC, ?_⟩
  set A := ggTh y a with hA
  set B := ggTh y b with hB
  have hX : ggTh y p = veblen A B := by
    conv_lhs => rw [← hdec]
    exact Ph.phTh_phi hy a ha b hb
  have hA1 : 1 ≤ A := by
    have := ggTh_mono (y := y) ha1; rwa [ggTh_small (gg_one_lt_of_SC hy).le] at this
  have hBX : B < veblen A B := by rw [← hX]; exact ggTh_lt hb hb1
  have hAX : A < veblen A B := by rw [← hX]; exact ggTh_lt ha hap
  have hyX : y < veblen A B := by
    rw [← hX]; exact (ggTh_Om1 hy (qf_y1 hy1)).symm.trans_lt (ggTh_lt GgCl.om hp1)
  have hXG : veblen A B < lgG y := by rw [← hX]; exact qf_th_lt_G hy hy1 p hp
  have hL := qf_lh hy hy1 hA1 hyX hXG hBX
  have hXE : InE (veblen A B) := luP_E hA1 (luP_veblen A B)
  rw [hc_luL_dec hXE hA1 hAX] at hL
  rw [hX]
  convert hL using 1
  unfold qfRe
  rw [← hadef, ← hbdef]
  have e1 : ggTh y (p * (1 + a)) = veblen A B * (1 + A) := by
    have := Ph.phTh_opow_mul hy hp (1 + a) h1a
    rw [hpE, ggTh_add hy h1C, ggTh_small (gg_one_lt_of_SC hy).le] at this
    rw [this, ← hX, ← ggTh_opow hy hp, hpE]
  rw [ggTh_add hy (GgCl.add hpa (qf_hcE_code hy ha)), ggTh_add hy hpa, e1, qf_th_hcE hy ha]
  rcases eq_or_ne b 0 with h0 | h0
  · rw [h0, Qc.qc_lg_zero, ggTh_small zero_le, show B = 0 by rw [hB, h0, ggTh_small zero_le], Qc.qc_lg_zero]
  · rw [Qc.qc_th_lg hy hb h0]

omit hy1 in
/-- **The reach of the reading of a power** `ω^x`, `x ≠ 0`, `x < ω^x`: `lh(Θ_y(ω^x)) = Θ_y(ω^x + logend(x))`. -/
theorem qf_pow {x : Ordinal.{0}} (hx : GgCl y x) (hx0 : x ≠ 0) (hxw : x < ω ^ x) :
    GgCl y (ω ^ x + lg x) ∧ IsLh1 (ggTh y (ω ^ x)) (ggTh y (ω ^ x + lg x)) := by
  have hwC : GgCl y (ω ^ x) := GgCl.opow hy.1 hx
  refine ⟨GgCl.add hwC (Qc.qc_lg_code hy hx), ?_⟩
  have hX0 : ggTh y x ≠ 0 := Ph.phTh_ne_zero hy hx0
  have hXw : ggTh y x < ω ^ ggTh y x := by rw [← ggTh_opow hy hx]; exact ggTh_lt hx hxw
  rw [ggTh_add hy hwC, ggTh_opow hy hx, Qc.qc_th_lg hy hx hx0]
  exact lu_lh_opow hX0 hXw

end Base


/-! ## The reach at a point of a Veblen level -/

section Lvl

variable {ρ : Ordinal.{0}} (hρ : SC ρ) (hρ1 : ρ < Om1)
include hρ hρ1

/-- **Every ordinal below `Γ_{E+1}` lies in `Tᵖ ∩ Ω₁`** for a strongly critical `E ∈ Tᵖ ∩ (ρ, Ω₁)`. -/
theorem qf_T_lgG {E : Ordinal.{0}} (hET : E ∈ Tset ρ) (hE1 : E < Om1) (hES : SC E) :
    ∀ X, X < lgG E → X ∈ Tset ρ ∧ X < Om1 := by
  have hρE : InE ρ := gg_SC_eps hρ
  obtain ⟨m, hρm, hmI, -, hTm, hm1⟩ := T_next (Or.inr hρE) hρ1
  have hEm : E < m := (hTm E hE1).1 hET
  have hmE : InE m := by
    have hm0 : 0 < m := lt_of_le_of_lt zero_le hρm
    exact (le1R_two_iff hm0).1 (hmI _ (le_mul_of_one_le_right' (by norm_num)))
  have hmS : SC m := Qc.qc_m_SC hρE hρ1 hρm hTm hm1 hmE
  have hGm : lgG E ≤ m := by
    by_contra hc; push Not at hc
    exact qf_noSC hES (hE1) hEm hc hmS.veblen_zero
  intro X hX
  have hXm : X < m := hX.trans_le hGm
  exact ⟨(hTm X (hXm.trans hm1)).2 hXm, hXm.trans hm1⟩

/-- **`lhᵖ` at the reading of a code above `Ω₁`** over a strongly critical `E ∈ Tᵖ ∩ (ρ, Ω₁)`: any reach `r` of
`Θ_E(x)` is `lhT ρ (Θ_E x)`. -/
theorem qf_lhT_eq {E x r : Ordinal.{0}} (hET : E ∈ Tset ρ) (hρE : ρ < E) (hE1 : E < Om1) (hES : SC E)
    (hx : GgCl E x) (hx1 : Om 1 < x) (hI : Indec (ggTh E x)) (hR : IsLh1 (ggTh E x) r) : lhT ρ (ggTh E x) = r := by
  have hρE' : InE ρ := gg_SC_eps hρ
  obtain ⟨hXT, hX1⟩ := qf_T_lgG hρ hρ1 hET hE1 hES _ (qf_th_lt_G hES hE1 x hx)
  have hEX : E < ggTh E x := (ggTh_Om1 hES (qf_y1 hE1)).symm.trans_lt (ggTh_lt GgCl.om hx1)
  exact lu_isLh1_unique (lh_eq_lhT (Or.inr hρE') hρ1 hXT (hρE.trans hEX) hX1 hI) hR

/-- **THE REACH AT A POINT OF A VEBLEN LEVEL**: for `ε_{Ω₁+1} ≤ M < Γ_{Ω₁+1}` with `tfDat M ∈ Tᵖ` and `σ ∈ Tᵖ ∩ Ω₁`,
`E := ϑᵖ(Ω₁·M + σ)` has `lh(E) = Θ_E(qfLam M) + lqZeta ρ (Ω₁·M) σ`, and `qfLam M` is a code over `E`. -/
theorem qf_lh_lvl {M σ : Ordinal.{0}} (hM1 : ggE ≤ M) (hMG : M < ggGam) (hMT : Tf.tfDat M ∈ Tset ρ)
    (hσ : σ ∈ Tset ρ) (hσΩ : σ < Om1) :
    GgCl (vt ρ (Om1 * M + σ)) (qfLam M) ∧
      IsLh1 (vt ρ (Om1 * M + σ)) (ggTh (vt ρ (Om1 * M + σ)) (qfLam M) + lqZeta ρ (Om1 * M) σ) := by
  classical
  have hρE : InE ρ := gg_SC_eps hρ
  have hM1' : Om1 ≤ M := rj_Om1_lt_E.le.trans hM1
  obtain ⟨-, -, hvT, hρv, hv1, -, hvP, -, -⟩ := qfK_facts hρ hρ1 hM1' hMG hMT hσ hσΩ
  have hES := qfK_SC hρ hρ1 hM1' hMG hMT hσ hσΩ
  set E := vt ρ (Om1 * M + σ) with hEdef
  have hE1' : E < Om 1 := qf_y1 hv1
  have hMC : GgCl E M := qf_code_of hρ hρ1 hM1' hMG hMT hσ hσΩ
  have hLC : GgCl E (Om1 * M) := by rw [rj_Om1]; exact Rk.rk_cl_Om1_mul hES hMC
  have hO0 : (0 : Ordinal.{0}) < Om1 := rj_Om1_pos
  have hL0 : Om1 * M ≠ 0 := (mul_pos hO0 (hO0.trans_le hM1')).ne'
  obtain ⟨hsubL, hlC⟩ := ggDec hES _ hLC
  set l := qfL M with hldef
  have hlC' : GgCl E l := hlC
  have hDC : GgCl E (ω ^ l) := GgCl.opow hES.1 hlC'
  have hDL : ω ^ l ≤ Om1 * M := opow_log_le_self ω hL0
  have hrC : GgCl E (Om1 * M - ω ^ l) := hsubL _ hDC hDL
  -- `l ≥ ε_{Ω₁+1} > Ω₁`
  have hEl : ggE ≤ l := by
    have h1 : ggE ≤ Om1 * M := hM1.trans (Ordinal.le_mul_right M hO0)
    have h2 := log_mono_right ω h1
    rwa [show log ω ggE = ggE from by
      have : ω ^ ggE = ggE := ggE_spec.1
      conv_lhs => rw [← this]
      exact log_opow one_lt_omega0 _] at h2
  have hl1 : Om 1 < l := by rw [← rj_Om1]; exact rj_Om1_lt_E.trans_le hEl
  have hlh := lh_eq_lhT (Or.inr hρE) hρ1 hvT hρv hv1 hvP
  obtain ⟨hcr, hncr⟩ := qfLhT hρE hρ1 hM1 hMG hMT hσ hσΩ hES
  have hTL := ggTh_add hES hDC (Om1 * M - ω ^ l)
  rw [Ordinal.add_sub_cancel_of_le hDL] at hTL
  by_cases hC : QfCr M
  · -- `cr < m`: `lh(E) = lh(Θ_E c) + λ`
    obtain ⟨-, hcE, -, -⟩ := id hC
    set c := qfC M with hcdef
    have hcC : GgCl E c := GgCl.opow hES.1 (ggDec hES l hlC').2
    have hcl : c ≤ l := opow_log_le_self ω (lt_of_lt_of_le (Om_pos one_ne_zero) hl1.le).ne'
    have hc1 : Om 1 < c := by
      by_contra hle; push Not at hle
      have hl' : l < ω ^ (log ω l + 1) := lt_opow_succ_log_self one_lt_omega0 l
      have h3 : ω ^ (log ω l + 1) ≤ Om 1 * ω := by
        rw [opow_add, opow_one]; exact mul_le_mul_left hle ω
      have h4 : Om 1 * ω < ggE := by
        have hgE : InE ggE := ggE_spec.1
        rw [← rj_Om1]
        exact hgE.mul_lt rj_Om1_lt_E (omega0_lt_inE hgE)
      exact absurd hEl (not_le.2 ((hl'.trans_le h3).trans h4))
    obtain ⟨hReC, hRe⟩ := qf_re hES hv1 hcC hc1 hcE
    have hI : Indec (ggTh E c) := by rw [← hcE, ggTh_opow hES hcC]; exact indec_opow _
    have heq := qf_lhT_eq hρ hρ1 hvT hρv hv1 hES hcC hc1 hI hRe
    have hlam : qfLam M = qfRe c + Om1 * M := by unfold qfLam; rw [if_pos hC]
    rw [hcr hC, heq] at hlh
    refine ⟨by rw [hlam]; exact GgCl.add hReC hLC, ?_⟩
    rw [hlam, ggTh_add hES hReC, add_assoc]
    exact hlh
  · rw [hncr hC] at hlh
    by_cases hlE : ω ^ l = l
    · -- `D = ω^l` an `ε`-code
      have hRe := qf_re hES hv1 hlC' hl1 hlE
      have hI : Indec (ggTh E l) := by
        rw [← hlE, ggTh_opow hES hlC']; exact indec_opow _
      have heq := qf_lhT_eq hρ hρ1 hvT hρv hv1 hES hlC' hl1 hI hRe.2
      have hlam : qfLam M = qfRe l + (Om1 * M - ω ^ l) := by unfold qfLam; rw [if_neg hC, if_pos hlE]
      rw [show ggTh E (ω ^ l) = ggTh E l by rw [hlE], heq] at hlh
      refine ⟨by rw [hlam]; exact GgCl.add hRe.1 hrC, ?_⟩
      rw [hlam, ggTh_add hES hRe.1, add_assoc]
      exact hlh
    · -- `D = ω^l` a power
      have hl0 : l ≠ 0 := (lt_of_le_of_lt zero_le hl1).ne'
      have hlw : l < ω ^ l := lt_of_le_of_ne (right_le_opow l one_lt_omega0) (Ne.symm hlE)
      obtain ⟨hPC, hP⟩ := qf_pow hES hlC' hl0 hlw
      have hD1 : Om 1 < ω ^ l := hl1.trans hlw
      have hI : Indec (ggTh E (ω ^ l)) := by rw [ggTh_opow hES hlC']; exact indec_opow _
      have heq := qf_lhT_eq hρ hρ1 hvT hρv hv1 hES hDC hD1 hI hP
      have hlam : qfLam M = ω ^ l + lg l + (Om1 * M - ω ^ l) := by unfold qfLam; rw [if_neg hC, if_neg hlE]
      rw [heq] at hlh
      refine ⟨by rw [hlam]; exact GgCl.add hPC hrC, ?_⟩
      rw [hlam, ggTh_add hES hPC, add_assoc]
      exact hlh

end Lvl

end Googology.Trans.PoR.InaccPsi.R2.Qf
