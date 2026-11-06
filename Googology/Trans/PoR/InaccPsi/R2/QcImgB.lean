import Googology.Trans.PoR.InaccPsi.R2.QcSep
import Googology.Trans.PoR.InaccPsi.R2.YwImg

/-!
# QcImgB: LEMMA IMG BELOW `ϑᵖ(Ω₁·N)` FOR EVERY LEVEL `Ω₁ ≤ N < ε_{Ω₁+1}` WITH ITS DATA BELOW `ρ`

`Yw.ywImg` gives Lemma IMG below `X^ρ = ϑᵖ(Ω₁·Ω₁·2)`; it uses the bound `X^ρ` only to find the levels of the
`ε`-numbers below a Veblen point (`Yw.ywVeb_rep`) and to decompose the arguments into `Ω₁·(Ω₁ + j) + σ`.  Here:

* `qcVeb_rep` (**every `ε`-number of `(max(x, q, t), ϑˣ(Ω₁·q + t))` is of Veblen level**, with no bound: [W07a]
  Lemma 3.30 through `luLt_of_vt_lt` (`q < x`) and `lvLt_of_vt_lt` (`x ≤ q`));
* `qc_img_veb` (**LEMMA IMG AT EVERY VEBLEN POINT `ϑᵖ(Ω₁·q + t)`**, given it below: the proof of `Yw.ywI_veb`
  with `qcVeb_rep`);
* `qc_img` (**LEMMA IMG BELOW `ϑᵖ(Ω₁·N)`** for every level `Ω₁ ≤ N < ε_{Ω₁+1}` with `rjDat N < ρ`, `ρ` strongly
  critical: an `ε`-number `e ∈ [Γ_{ρ+2}, ϑᵖ(Ω₁·N))` is `ϑᵖ(ξ)` with `ξ < Ω₁·N` (`rjLt_of_vt_lt`), a Veblen point or a
  point of a level `Ω₁ ≤ M < N` (`Qc.qc_img_lvl`); below `Γ_{ρ+2}` it is `He.he_img_G1`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.He
  Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Gq Googology.Trans.PoR.InaccPsi.R2.Hb
  Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gj Googology.Trans.PoR.InaccPsi.R2.Gw Googology.Trans.PoR.InaccPsi.R2.Xk
  Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rk Googology.Trans.PoR.InaccPsi.R2.Yr
  Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Rj
  Googology.Trans.PoR.InaccPsi.R2.Gg
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gb

section Rep

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **Every `ε`-number of `(max(x, q, t), ϑˣ(Ω₁·q + t))` is of Veblen level** (no bound). -/
theorem qcVeb_rep {q t u : Ordinal.{0}} (hq1 : 1 ≤ q) (hqT : q ∈ Tset x) (hqΩ : q < Om1) (htT : t ∈ Tset x)
    (ht1 : t < Om1) (huE : InE u) (hxu : x < u) (hqu : q < u) (htu : t < u)
    (hue : u < vt x (Om1 * q + t)) :
    ∃ q' t', 1 ≤ q' ∧ q' ∈ Tset x ∧ q' < Om1 ∧ t' ∈ Tset x ∧ t' < Om1 ∧ glA q' t' x = u := by
  obtain ⟨hvT, -, hv1, -, -, -⟩ := glA_facts hx hx1 hq1 hqT hqΩ htT ht1
  have hu1 : u < Om1 := hue.trans hv1
  have huT : u ∈ Tset x := vz_T_down hx hx1 hvT hv1 hue.le
  obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 huT hxu.le hu1 (inE_indec huE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxu, by rw [hξv]; exact huE⟩
  have hξlt : ξ < Om1 * q + t := by
    rcases lt_or_ge q x with hqx | hxq
    · exact luLt_of_vt_lt hx hx1 hξT hξ2 hqx htT ht1 (by rw [hξv]; exact htu) (by rw [hξv]; exact hue)
    · exact lvLt_of_vt_lt hx hx1 hξT hξ2 hqT hxq hqΩ htT ht1 (by rw [hξv]; exact htu) (by rw [hξv]; exact hqu)
        (by rw [hξv]; exact hue)
  have hξs : ξ < Om1 * Om1 :=
    calc ξ < Om1 * q + t := hξlt
      _ < Om1 * q + Om1 := (add_lt_add_iff_left _).2 ht1
      _ = Om1 * (q + 1) := (mul_add_one _ _).symm
      _ ≤ Om1 * Om1 := mul_le_mul_right (Order.add_one_le_of_lt hqΩ) _
  obtain ⟨hq'1, hrT, hr1, hdec⟩ := lu_split hx hx1 hξT hξ2 hΩξ
  have hq'T : ξ / Om1 ∈ Tset x := lgQuot_mem hx hx1 hξT hξs
  have hq'Ω : ξ / Om1 < Om1 := (Ordinal.lt_mul_iff_div_lt (Ordinal.omega_pos 1).ne').1 hξs
  refine ⟨ξ / Om1, ξ % Om1, hq'1, hq'T, hq'Ω, hrT, hr1, ?_⟩
  show vt x (Om1 * (ξ / Om1) + ξ % Om1) = u
  rw [hdec, hξv]

end Rep

section Img

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **LEMMA IMG AT EVERY VEBLEN POINT `e = ϑᵖ(Ω₁·q + t)`**, given it below `e` (`Yw.ywI_veb` without the bound
`X^ρ`). -/
theorem qc_img_veb {q t : Ordinal.{0}} (hq1 : 1 ≤ q) (hqT : q ∈ Tset ρ) (hqΩ : q < Om1) (htT : t ∈ Tset ρ)
    (ht1 : t < Om1) (IHe : ∀ u, u < glA q t ρ → GnI ρ δ u) : GnI ρ δ (glA q t ρ) := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  obtain ⟨-, hρe, -, hE, hqe, hte⟩ := glA_facts hρE hρ1 hq1 hqT hqΩ htT ht1
  -- the fixed points of `φ(q, ·)` below `e`
  have hPq : ∃ P0, P0 < glA q t ρ ∧ ∀ u, LuP (q + 1) u → u < glA q t ρ → u ≤ P0 := by
    by_cases hz : veblen (q + 1) 0 ≤ glA q t ρ
    · obtain ⟨a, ha1, ha2⟩ := hb_floor (q + 1) (j0 := 0) hz
      refine ⟨veblen (q + 1) a, lt_of_le_of_ne ha1 (fun e' =>
        glA_notP hρE hρ1 hq1 hqT hqΩ htT ht1 (by rw [← e']; exact ⟨a, rfl⟩)), fun u hu hue => ?_⟩
      obtain ⟨j, rfl⟩ := hu
      have hj : j < a + 1 := (veblen_lt_veblen_iff_right).1 (hue.trans ha2)
      exact (isNormal_veblen _).monotone (Order.lt_add_one_iff.1 hj)
    · push Not at hz
      refine ⟨0, hE.pos, fun u hu hue => ?_⟩
      exfalso
      obtain ⟨j, rfl⟩ := hu
      exact absurd (hue.trans hz) (not_lt.2 ((isNormal_veblen _).monotone zero_le))
  -- the earlier points of level `q`
  have hRq : ∃ R0, R0 < glA q t ρ ∧ ∀ t', t' ∈ Tset ρ → t' < Om1 → t' < t → R0 < glA q t' ρ →
      luZeta ρ q t' < luZeta ρ q t := by
    rcases zero_or_succ_or_isSuccLimit t with ht0 | ⟨s, hs⟩ | hlim
    · refine ⟨0, hE.pos, fun t' _ _ ht' _ => ?_⟩
      exact absurd ht' (by rw [ht0]; exact not_lt.2 zero_le)
    · have hts : t = s + 1 := by rw [← hs, succ_eq_add_one]
      have hst : s < t := by rw [hts]; exact lt_add_one s
      obtain ⟨hsT, hs1⟩ : s ∈ Tset ρ ∧ s < Om1 := ⟨vz_T_down hρE hρ1 htT ht1 hst.le, hst.trans ht1⟩
      refine ⟨glA q s ρ, glA_lt_of hρE hρ1 hq1 hqT hqΩ hsT htT ht1 hst, fun t' ht'T ht'1 ht' hR => ?_⟩
      exfalso
      have hst' : t' ≤ s := by rw [hts] at ht'; exact Order.lt_add_one_iff.1 ht'
      have := (glA_le_iff hρE hρ1 hq1 hqT hqΩ ht'T ht'1 hsT hs1).2 hst'
      exact absurd hR (not_lt.2 this)
    · by_cases hcl : ∃ σ, σ < t ∧ t < vt ρ (Om1 * q + σ)
      · have hz : luZeta ρ q t = lg t := by unfold luZeta; rw [if_pos hcl]
        have ht0 : t ≠ 0 := hlim.bot_lt.ne'
        obtain ⟨c', hcs, -, hc't⟩ := lg_split ht0
        obtain ⟨hc'T, hc'1⟩ : c' ∈ Tset ρ ∧ c' < Om1 := ⟨vz_T_down hρE hρ1 htT ht1 hc't.le, hc't.trans ht1⟩
        refine ⟨glA q c' ρ, glA_lt_of hρE hρ1 hq1 hqT hqΩ hc'T htT ht1 hc't, fun t' ht'T ht'1 ht' hR => ?_⟩
        have hc't' : c' < t' := (glA_lt_iff hρE hρ1 hq1 hqT hqΩ hc'T hc'1 ht'T ht'1).1 hR
        rw [hz]
        set z := lg t with hzdef
        obtain ⟨δ', hδ'⟩ : ∃ δ', t' = c' + δ' := ⟨t' - c', (Ordinal.add_sub_cancel_of_le hc't'.le).symm⟩
        have hδ0 : δ' ≠ 0 := by rintro rfl; rw [add_zero] at hδ'; exact absurd hδ' hc't'.ne'
        have hδlt : δ' < ω ^ z := by
          have : c' + δ' < c' + ω ^ z := by rw [← hδ', ← hcs]; exact ht'
          exact (add_lt_add_iff_left _).1 this
        have hlgd : lg t' < z := by
          rw [hδ', gz_lg_add _ hδ0]
          by_contra hge; push Not at hge
          obtain ⟨δ'', hδs, -, -⟩ := lg_split hδ0
          have h1 : ω ^ z ≤ ω ^ lg δ' := opow_le_opow_right omega0_pos hge
          have h2 : ω ^ lg δ' ≤ δ' := (le_add_self (a := ω ^ lg δ') (b := δ'')).trans_eq hδs.symm
          exact absurd hδlt (not_lt.2 (h1.trans h2))
        exact lu_zeta_le_lg.trans_lt hlgd
      · push Not at hcl
        refine ⟨t, hte, fun t' _ _ ht' hR => ?_⟩
        exact absurd (hcl t' ht') (not_le.2 hR)
  obtain ⟨P0, hP0e, hP0⟩ := hPq
  obtain ⟨R0, hR0e, hR0⟩ := hRq
  set M0 := max (ρ + 1) (max q t) with hM0
  set E' := max (max M0 (q + 1)) (max P0 R0) with hE'def
  have hM0E' : M0 ≤ E' := (le_max_left _ _).trans (le_max_left _ _)
  have hρE' : ρ < E' := (lt_add_one ρ).trans_le ((le_max_left _ _).trans hM0E')
  have hqE' : q < E' := (lt_add_one q).trans_le ((le_max_right _ _).trans (le_max_left _ _))
  have hPE' : P0 ≤ E' := (le_max_left _ _).trans (le_max_right _ _)
  have hRE' : R0 ≤ E' := (le_max_right _ _).trans (le_max_right _ _)
  have hqM : q ≤ M0 := (le_max_left _ _).trans (le_max_right _ _)
  have htM : t ≤ M0 := (le_max_right _ _).trans (le_max_right _ _)
  have hlim := ev_isSuccLimit_of_inE hE
  have hE'e : E' < glA q t ρ :=
    max_lt (max_lt (max_lt (hlim.add_one_lt hρe) (max_lt hqe hte)) (hlim.add_one_lt hqe)) (max_lt hP0e hR0e)
  refine he_img_down h hq1 hqT hqΩ htT ht1 hρE' hqE' hE'e (fun u hu hE'u hue => ?_) IHe
  have hM0u : M0 < u := hM0E'.trans_lt hE'u
  obtain ⟨q', t', hq'1, hq'T, hq'Ω, ht'T, ht'1, hu'⟩ := qcVeb_rep hρE hρ1 hq1 hqT hqΩ htT ht1 hu
    ((lt_add_one ρ).trans ((le_max_left _ _).trans_lt hM0u)) (hqM.trans_lt hM0u) (htM.trans_lt hM0u) hue
  have hq'q : q' ≤ q := by
    by_contra hlt
    push Not at hlt
    have hP : LuP (q + 1) u := by
      rw [← hu']
      exact (gq_veb_level hρE hρ1 hq'1 hq'T hq'Ω ht'T ht'1 le_add_self).2 (Order.add_one_le_of_lt hlt)
    exact absurd (hE'u.trans_le' (hP0 u hP hue |>.trans hPE')) (lt_irrefl _)
  obtain ⟨H1', H2', -⟩ := he_lhq hρE hρ1 hq'1 hq'T hq'Ω ht'T ht'1
  rw [hu'] at H1' H2'
  refine ⟨q', _, hq'q, H1', H2', fun e' => ?_⟩
  subst e'
  have ht't : t' < t := by
    rw [← hu'] at hue
    exact (glA_lt_iff hρE hρ1 hq1 hqT hqΩ ht'T ht'1 htT ht1).1 hue
  exact hR0 t' ht'T ht'1 ht't (hRE'.trans_lt (hu' ▸ hE'u))

/-- **LEMMA IMG BELOW `ϑᵖ(Ω₁·N)`** for every level `Ω₁ ≤ N < ε_{Ω₁+1}` with its data below `ρ` (`ρ` strongly
critical). -/
theorem qc_img (hρS : SC ρ) {N : Ordinal.{0}} (hN1 : Om1 ≤ N) (hNE : N < ggE) (hNρ : rjDat N < ρ) :
    ∀ v, v < vt ρ (Om1 * N) → GnI ρ δ v := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have h0T : (0 : Ordinal.{0}) ∈ Tset ρ := mem_T_of_le hρE hρ1 zero_le
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hρE.pos.trans hρ1
  have hNT : rjDat N ∈ Tset ρ := mem_T_of_le hρE hρ1 hNρ.le
  have hargT := rjArg_mem hρE hρ1 hN1 hNE hNT h0T h0Ω
  rw [add_zero] at hargT
  obtain ⟨hBT, -, hB1, -, -⟩ := vt_memTwo hρE hρ1 hargT (by simpa using qc_arg_lt hNE h0Ω)
  refine gnImg_of_eps h (fun v hv => ⟨vz_T_down hρE hρ1 hBT hB1 hv.le, hv.trans hB1⟩)
    (fun e he _ heB IHe => ?_)
  rcases lt_or_ge e (gq 1 ρ) with hlt | hge
  · exact he_img_G1 h e hlt
  have h1T : (1 : Ordinal.{0}) ∈ Tset ρ := (yw_one hρE hρ1).1
  have h1Ω : (1 : Ordinal.{0}) < Om1 := (yw_one hρE hρ1).2
  have hρG1 : ρ < gq 1 ρ := (geq_facts hρE hρ1 h1T h1Ω).2.1
  have hρe : ρ < e := hρG1.trans_le hge
  have he1 : e < Om1 := heB.trans hB1
  have heT : e ∈ Tset ρ := vz_T_down hρE hρ1 hBT hB1 heB.le
  obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hρE hρ1 heT hρe.le he1 (inE_indec he)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hρE hρ1 hξT hξ2).1 ⟨by rw [hξv]; exact hρe, by rw [hξv]; exact he⟩
  have hξN : ξ < Om1 * N := by
    have := rjLt_of_vt_lt hρE hρ1 hξT hξ2 hN1 hNE hNT h0T h0Ω (by rw [hξv]; exact hNρ.trans hρe)
      (by rw [hξv]; exact he.pos) (by rw [hξv, add_zero]; exact heB)
    rwa [add_zero] at this
  obtain ⟨hq1, hrT, hr1, hdec⟩ := lu_split hρE hρ1 hξT hξ2 hΩξ
  rcases lt_or_ge (ξ / Om1) Om1 with hqΩ | hqΩ
  · have hξs : ξ < Om1 * Om1 := by
      rw [← hdec]
      calc Om1 * (ξ / Om1) + ξ % Om1 < Om1 * (ξ / Om1) + Om1 := (add_lt_add_iff_left _).2 hr1
        _ = Om1 * (ξ / Om1 + 1) := (mul_add_one _ _).symm
        _ ≤ Om1 * Om1 := mul_le_mul_right (Order.add_one_le_of_lt hqΩ) _
    have hqT : ξ / Om1 ∈ Tset ρ := lgQuot_mem hρE hρ1 hξT hξs
    have hev : glA (ξ / Om1) (ξ % Om1) ρ = e := by
      show vt ρ (Om1 * (ξ / Om1) + ξ % Om1) = e
      rw [hdec, hξv]
    rw [← hev] at IHe ⊢
    exact qc_img_veb h hq1 hqT hqΩ hrT hr1 IHe
  · have hMN : ξ / Om1 < N := by
      have h1 : Om1 * (ξ / Om1) ≤ ξ := Ordinal.mul_div_le ξ Om1
      exact (mul_lt_mul_iff_right₀ rj_Om1_pos).1 (h1.trans_lt hξN)
    have hME : ξ / Om1 < ggE := hMN.trans hNE
    have hMT : rjDat (ξ / Om1) ∈ Tset ρ := rkArg_dat hρE hρ1 hqΩ hME hr1 (by rw [hdec]; exact hξT)
    have hev : vt ρ (Om1 * (ξ / Om1) + ξ % Om1) = e := by rw [hdec, hξv]
    rw [← hev] at IHe ⊢
    exact qc_img_lvl h hρS hqΩ hME hMT hrT hr1 IHe

end Img

end Googology.Trans.PoR.InaccPsi.R2.Qc
