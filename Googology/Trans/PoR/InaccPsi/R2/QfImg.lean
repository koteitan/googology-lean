import Googology.Trans.PoR.InaccPsi.R2.QfCopy
import Googology.Trans.PoR.InaccPsi.R2.QfRep
import Googology.Trans.PoR.InaccPsi.R2.QcImgB

/-!
# QfImg: LEMMA IMG AT THE POINTS OF THE VEBLEN LEVELS, AND `Qd.QdImgH` FROM `Qf.QfTBphi`

The proof of `Qc.qc_img_atom`, `Qc.qc_img_lvl`, `Qc.qc_img` with the reach code `qfLam M` (`Qf.qf_lh_lvl`), the copy
lemma for every code (`Qf.qf_copy`) and the separation at the Veblen levels (`Qf.qf_sep`):

* `qf_img_atom` (**LEMMA IMG AT `E = ϑᵖ(Ω₁·M + σ)`, `ε_{Ω₁+1} ≤ M < Γ_{Ω₁+1}`, FROM THE SEPARATION**);
* `qf_img_lvl` (**LEMMA IMG AT EVERY POINT OF A VEBLEN LEVEL**, given it below);
* `qf_img` (**LEMMA IMG BELOW `ϑᵖ(Ω₁·N)`** for every level `Ω₁ ≤ N < Γ_{Ω₁+1}` with `tfDat N < ρ`);
* `qf_imgH` (**`Qd.QdImgH`**, given `Qf.QfTBphi`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.He Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gw
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Qc
  Googology.Trans.PoR.InaccPsi.R2.Gb

section Img

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **LEMMA IMG AT A POINT `E = ϑᵖ(Ω₁·M + σ)` OF A VEBLEN LEVEL `ε_{Ω₁+1} ≤ M < Γ_{Ω₁+1}`, FROM THE SEPARATION**
(`QfTBphi` given). -/
theorem qf_img_atom (hTB : QfTBphi) (hρS : SC ρ) {M σ E' : Ordinal.{0}} (hM1 : ggE ≤ M) (hMG : M < ggGam)
    (hMT : Tf.tfDat M ∈ Tset ρ) (hσT : σ ∈ Tset ρ) (hσΩ : σ < Om1) (hρE' : ρ < E')
    (hE'E : E' < vt ρ (Om1 * M + σ)) (hdE' : Tf.tfDat M < E')
    (hsep : ∀ a, InE a → E' < a → a < vt ρ (Om1 * M + σ) →
      (SC a → ¬ le1R a (ggTh a (qfLam M) + lqZeta ρ (Om1 * M) σ)) ∧ (¬ SC a → ¬ le1R a (a * a)))
    (IH : ∀ u, u < vt ρ (Om1 * M + σ) → GnI ρ δ u) : GnI ρ δ (vt ρ (Om1 * M + σ)) := by
  classical
  have hρ1 := h.ρ1
  have hM1' : Om1 ≤ M := rj_Om1_lt_E.le.trans hM1
  obtain ⟨-, -, hET0, hρEE, hE1, hE, hEI, -, hσE⟩ := qfK_facts hρS hρ1 hM1' hMG hMT hσT hσΩ
  have hES := qfK_SC hρS hρ1 hM1' hMG hMT hσT hσΩ
  obtain ⟨hΛC, hLE⟩ := qf_lh_lvl hρS hρ1 hM1 hMG hMT hσT hσΩ
  set E := vt ρ (Om1 * M + σ) with hEdef
  set z := lqZeta ρ (Om1 * M) σ with hzdef
  set Λ := qfLam M with hΛdef
  have hE1' : E < Om 1 := by rw [← rj_Om1]; exact hE1
  have hzE : z < E := (rj_zeta_le ρ (Om1 * M) σ).trans_lt hσE
  have hMC : GgCl E M := qf_code_of hρS hρ1 hM1' hMG hMT hσT hσΩ
  have hΛL : Om1 * M ≤ Λ := (qf_lam_code hES hE1 hM1 hMC).2
  have hET : E ∈ Tset ρ ∧ E < Om1 := ⟨hET0, hE1⟩
  have hEδ : E < δ := gn_lt_δ h hET.1 hET.2
  have hδI := inE_indec h.δE
  have hE0 : 0 < E := hE.pos
  have hEEδ : E + E < δ := hδI.add_lt hEδ hEδ
  have hPδ : E * E < δ := h.δE.mul_lt hEδ hEδ
  have hPEδ : E * E + E < δ := hδI.add_lt hPδ hEδ
  have hΛδ : ggTh E Λ < δ := by
    obtain ⟨hT, h1⟩ := qf_T_lgG hρS hρ1 hET0 hE1 hES _ (qf_th_lt_G hES hE1 Λ hΛC)
    exact gn_lt_δ h hT h1
  have hTopδ : ggTh E Λ + z < δ := hδI.add_lt hΛδ (hzE.trans hEδ)
  have hEP : E < E * E := lt_mul_of_one_lt_right hE0 (lu_one_lt_E hE)
  have hPe : E * E = ω ^ (E + E) := by
    conv_lhs => rw [← show ω ^ E = E from hE]
    rw [← opow_add]
  have hρP : ρ ≤ E * E := hρEE.le.trans hEP.le
  have hPΛ : E * E ≤ ggTh E Λ := by
    have h1 : ggTh E (Om1 * Om1) = E * E := by
      rw [rj_Th_mul hES hE1 (by rw [rj_Om1]; exact GgCl.om), rj_Om1, ggTh_Om1 hES hE1']
    rw [← h1]
    exact ggTh_mono ((mul_le_mul_right hM1' _).trans hΛL)
  have hEΛ : E ≤ ggTh E Λ := hEP.le.trans hPΛ
  have hsrc : le1 E (ggTh E Λ + z) := (h.lowδ _ _ hρEE hTopδ.le).2 hLE.1
  -- witness sets
  obtain ⟨W1, Z1, w1, m1, -, -, b1⟩ := gnI_use h (IH E' hE'E)
  obtain ⟨W2, Z2, w2, m2, -, -, b2⟩ := gnI_use h (IH z hzE)
  set W3 := insert E (W1 ∪ W2) with hW3
  set Z3 := Z1 ∪ Z2 with hZ3
  have w3 : WZ ρ δ W3 Z3 := (w1.union w2).insW hρEE.le hEδ (Or.inl hEI)
  have hE3 : E ∈ W3 := Finset.mem_insert_self _ _
  set W4 := insert (E + E) W3 with hW4
  have w4 : WZ ρ δ W4 Z3 := w3.insW (hρEE.le.trans le_self_add) hEEδ
    (Or.inr ⟨E, Finset.mem_union_left _ hE3, E, Finset.mem_union_left _ hE3, lt_add_of_pos_right _ hE0,
      lt_add_of_pos_right _ hE0, rfl⟩)
  have h34 : W3 ⊆ W4 := Finset.subset_insert _ _
  set W5 := insert (E * E) W4 with hW5
  have w5 : WZ ρ δ W5 Z3 := w4.insW hρP hPδ (Or.inl (by rw [hPe]; exact indec_opow _))
  have h45 : W4 ⊆ W5 := Finset.subset_insert _ _
  set W6 := insert (E * E + E) W5 with hW6
  have w6 : WZ ρ δ W6 Z3 := w5.insW (hρP.trans le_self_add) hPEδ
    (Or.inr ⟨E * E, Finset.mem_union_left _ (Finset.mem_insert_self _ _), E,
      Finset.mem_union_left _ (h45 (h34 hE3)), lt_add_of_pos_right _ hE0, hEP.trans_le le_self_add, rfl⟩)
  have h56 : W5 ⊆ W6 := Finset.subset_insert _ _
  have hE6 : E ∈ W6 := h56 (h45 (h34 hE3))
  obtain ⟨W7, Z7, w7, h67, hZ37, m7, b7⟩ := qf_copy h hTB w6 hE6 hρEE hES hE1' hET0 hEδ IH Λ hΛC
  have hzW7 : z ∈ W7 ∪ Z7 := by
    rcases Finset.mem_union.1 m2 with hm | hm
    · exact Finset.mem_union_left _ (h67 (h56 (h45 (h34 (Finset.mem_insert_of_mem
        (Finset.mem_union_right _ hm))))))
    · exact Finset.mem_union_right _ (hZ37 (Finset.mem_union_right _ hm))
  obtain ⟨W8, w8, h78, hTop⟩ : ∃ W8 : Finset Ordinal.{0}, WZ ρ δ W8 Z7 ∧ W7 ⊆ W8 ∧
      ggTh E Λ + z ∈ W8 ∪ Z7 := by
    rcases eq_or_ne z 0 with hz0 | hz0
    · exact ⟨W7, w7, subset_refl _, by rw [hz0, add_zero]; exact m7⟩
    · refine ⟨insert (ggTh E Λ + z) W7, w7.insW ((hρEE.le.trans hEΛ).trans le_self_add) hTopδ
        (Or.inr ⟨_, m7, z, hzW7, lt_add_of_pos_right _ (pos_iff_ne_zero.2 hz0),
          hzE.trans_le (hEΛ.trans le_self_add), rfl⟩), Finset.subset_insert _ _,
        Finset.mem_union_left _ (Finset.mem_insert_self _ _)⟩
  have hsub : ∀ a, a ∈ W6 → a ∈ W8 := fun a ha => h78 (h67 ha)
  refine gnI_mk h w8 (Finset.mem_union_left _ (hsub _ hE6)) hET.1 hET.2 (fun A f hW hZ C => ?_)
  have hZ7 : ↑Z7 ⊆ A := fun a ha => hZ (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 ha)))
  have hWA : ∀ a, a ∈ W6 → a ∈ A := fun a ha => hW (Finset.mem_coe.2 (hsub a ha))
  have hW7A : ↑W7 ⊆ A := fun a ha => hW (Finset.mem_coe.2 (h78 (Finset.mem_coe.1 ha)))
  have hW1 : ↑W1 ⊆ A := fun a ha => hWA a (h56 (h45 (h34 (Finset.mem_insert_of_mem
    (Finset.mem_union_left _ (Finset.mem_coe.1 ha))))))
  have hW2 : ↑W2 ⊆ A := fun a ha => hWA a (h56 (h45 (h34 (Finset.mem_insert_of_mem
    (Finset.mem_union_right _ (Finset.mem_coe.1 ha))))))
  have hZ1 : ↑Z1 ⊆ A := fun a ha => hZ7 (Finset.mem_coe.2 (hZ37 (Finset.mem_union_left _ (Finset.mem_coe.1 ha))))
  have hZ2 : ↑Z2 ⊆ A := fun a ha => hZ7 (Finset.mem_coe.2 (hZ37 (Finset.mem_union_right _ (Finset.mem_coe.1 ha))))
  obtain ⟨hE'A, hE'TB, pE'⟩ := b1 A f hW1 hZ1 C
  obtain ⟨hzA, -, pz⟩ := b2 A f hW2 hZ2 C
  have hEA : E ∈ A := hWA _ hE6
  have hEEA : E + E ∈ A := hWA _ (h56 (h45 (Finset.mem_insert_self _ _)))
  have hPA : E * E ∈ A := hWA _ (h56 (Finset.mem_insert_self _ _))
  have hPEA : E * E + E ∈ A := hWA _ (Finset.mem_insert_self _ _)
  have hΛA : ggTh E Λ ∈ A := mem_A m7 hW7A hZ7
  have hTopA : ggTh E Λ + z ∈ A := mem_A hTop (fun a ha => hW ha) hZ7
  have hETB : E ∈ TB ρ (f ρ) := gnI_TB h C hET.1 (fun p hp => hZ (by simp [hp]))
  have hB := h.img_bases C
  by_contra hlt
  push Not at hlt
  by_cases hU : UpsPt (f E)
  · exact absurd (gw_pbig h hET hρEE A f C hEA hETB hU) (not_lt.2 hlt.le)
  have hfTop : f (ggTh E Λ + z) = f (ggTh E Λ) + f z := (C.add _ hΛA _ hzA _ hTopA rfl).symm
  have himg : le1 (f E) (f (ggTh E Λ + z)) := C.cov1 _ hEA _ hTopA hsrc
  have hR := (C.sk _ (C.low _ hEA) hU _).1 himg
  obtain ⟨u, huTB, hpu, hE'u, huE, huI⟩ :=
    gw_key h hE hET hρEE hEEδ A f C hEA hEEA hETB E' hE'E hE'A hE'TB pE' hlt
  have hu1 : u < Om1 := huE.trans hET.2
  have hρu : ρ < u := hρE'.trans hE'u
  obtain ⟨l, hl, hlTB, hpl⟩ := lh_pi hB huTB hρu hu1
  have hle0 : f (ggTh E Λ + z) ≤ pi (f ρ) ρ l := hpl.2 _ (by rw [hpu]; exact hR)
  obtain ⟨hzTB, -⟩ : z ∈ TB ρ (f ρ) ∧ True := ⟨(b2 A f hW2 hZ2 C).2.1, trivial⟩
  by_cases huS : SC u
  · -- the copy lemma at `u`
    have hu1' : u < Om 1 := by rw [← rj_Om1]; exact hu1
    have huM : GgCl u M := Ss.ss_code huS.1 M hMG (by rw [← Tf.tfDat_eq_ss M hMG]; exact hdE'.trans hE'u)
    obtain ⟨hΛu, hΛuL⟩ := qf_lam_code huS hu1 hM1 huM
    obtain ⟨hΛuTB, hΛuπ⟩ := b7 A f hW7A hZ7 C u huS huTB hu1' hΛu hpu
    obtain ⟨hsTB, hsπ⟩ := pi_add hB hΛuTB hzTB
    have hle1 : pi (f ρ) ρ (ggTh u Λ + z) ≤ pi (f ρ) ρ l := by
      rw [hsπ]
      exact (add_le_add hΛuπ pz).trans (hfTop ▸ hle0)
    have hle2 : ggTh u Λ + z ≤ l := ((pi_bijOn hB).2.le_iff_le hsTB hlTB).1 hle1
    have huΛ : u ≤ ggTh u Λ + z := by
      have hΩΛ : Om 1 ≤ Λ := by
        rw [← rj_Om1]
        exact (le_mul_of_one_le_right' (rj_Om1_pos.trans_le hM1' |> Order.one_le_iff_pos.2)).trans hΛL
      have := ggTh_mono (y := u) hΩΛ
      rw [ggTh_Om1 huS hu1'] at this
      exact this.trans le_self_add
    exact (hsep u huI hE'u huE).1 huS (le1R_of_le huΛ hle2 hl.1)
  · -- the square
    obtain ⟨-, hPge⟩ := Gb.GbK.gbImg h hE hρEE hEδ C hEA hEEA hPA hPEA
    have hPTop : f (E * E) ≤ f (ggTh E Λ + z) := by
      rcases (hPΛ.trans le_self_add).lt_or_eq with hlt' | heq
      · exact (C.mono hPA hTopA hlt').le
      · rw [heq]
    obtain ⟨huuTB, huuπ⟩ := he_pi_mul C.ups h.ρU hB huTB hu1 huI u huTB hu1
    have hle1 : pi (f ρ) ρ (u * u) ≤ pi (f ρ) ρ l := by
      rw [huuπ, hpu]; exact (hPge.trans hPTop).trans hle0
    have hle2 : u * u ≤ l := ((pi_bijOn hB).2.le_iff_le huuTB hlTB).1 hle1
    have huu : u ≤ u * u := le_mul_of_one_le_right' (lu_one_lt_E huI).le
    exact (hsep u huI hE'u huE).2 huS (le1R_of_le huu hle2 hl.1)


/-- **LEMMA IMG AT A POINT `ϑᵖ(Ω₁·M + σ)` OF A VEBLEN LEVEL `ε_{Ω₁+1} ≤ M < Γ_{Ω₁+1}`**, given it below (`QfTBphi`
given, `ρ` strongly critical). -/
theorem qf_img_lvl (hTB : QfTBphi) (hρS : SC ρ) {M σ : Ordinal.{0}} (hM1 : ggE ≤ M) (hMG : M < ggGam)
    (hMT : Tf.tfDat M ∈ Tset ρ) (hσT : σ ∈ Tset ρ) (hσΩ : σ < Om1)
    (IH : ∀ u, u < vt ρ (Om1 * M + σ) → GnI ρ δ u) : GnI ρ δ (vt ρ (Om1 * M + σ)) := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hM1' : Om1 ≤ M := rj_Om1_lt_E.le.trans hM1
  obtain ⟨-, -, -, hρv, -, hvE, -, hje, -⟩ := qfK_facts hρS hρ1 hM1' hMG hMT hσT hσΩ
  have hL : max (ρ + 1) (Tf.tfDat M + 1) < vt ρ (Om1 * M + σ) := by
    have hlim := ev_isSuccLimit_of_inE hvE
    exact max_lt (hlim.add_one_lt hρv) (hlim.add_one_lt hje)
  obtain ⟨E', hLE', hdE', hσE', hE'E, hJ⟩ := qf_LB hρE hρ1 hM1' hMG hMT hσT hσΩ hL
  have hρE' : ρ < E' := (lt_add_one ρ).trans_le ((le_max_left _ _).trans hLE')
  have hdE'' : Tf.tfDat M < E' := (lt_add_one _).trans_le ((le_max_right _ _).trans hLE')
  exact qf_img_atom h hTB hρS hM1 hMG hMT hσT hσΩ hρE' hE'E hdE''
    (qf_sep_lvl hρE hρ1 hρS hM1 hMG hMT hσT hσΩ hρE'.le hdE' hσE' hJ) IH

/-- **LEMMA IMG BELOW `ϑᵖ(Ω₁·N)`** in a restart context, for every level `Ω₁ ≤ N < Γ_{Ω₁+1}` with `tfDat N < ρ`
(`QfTBphi` given, `ρ` strongly critical). -/
theorem qf_img (hTB : QfTBphi) (hρS : SC ρ) {N : Ordinal.{0}} (hN1 : Om1 ≤ N) (hNG : N < ggGam)
    (hNρ : Tf.tfDat N < ρ) : ∀ v, v < vt ρ (Om1 * N) → GnI ρ δ v := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have h0T : (0 : Ordinal.{0}) ∈ Tset ρ := mem_T_of_le hρE hρ1 zero_le
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hρE.pos.trans hρ1
  have hNT : Tf.tfDat N ∈ Tset ρ := mem_T_of_le hρE hρ1 hNρ.le
  obtain ⟨-, -, hBT, -, hB1, -, -, -, -⟩ := qfK_facts hρS hρ1 hN1 hNG hNT h0T h0Ω
  rw [add_zero] at hBT hB1
  refine gnImg_of_eps h (fun v hv => ⟨vz_T_down hρE hρ1 hBT hB1 hv.le, hv.trans hB1⟩)
    (fun e he _ heB IHe => ?_)
  rcases lt_or_ge e (gq 1 ρ) with hlt | hge
  · exact he_img_G1 h e hlt
  have h1T : (1 : Ordinal.{0}) ∈ Tset ρ := (Yw.yw_one hρE hρ1).1
  have h1Ω : (1 : Ordinal.{0}) < Om1 := (Yw.yw_one hρE hρ1).2
  have hρG1 : ρ < gq 1 ρ := (Ge.geq_facts hρE hρ1 h1T h1Ω).2.1
  have hρe : ρ < e := hρG1.trans_le hge
  have he1 : e < Om1 := heB.trans hB1
  have heT : e ∈ Tset ρ := vz_T_down hρE hρ1 hBT hB1 heB.le
  obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hρE hρ1 heT hρe.le he1 (inE_indec he)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hρE hρ1 hξT hξ2).1 ⟨by rw [hξv]; exact hρe, by rw [hξv]; exact he⟩
  have hξN : ξ < Om1 * N := by
    have := tfLt_of_vt_lt hρE hρ1 hN1 (hNG.trans qf_gg_lt_BG) hξT hξ2 hNT h0T h0Ω
      (by rw [hξv]; exact hNρ.trans hρe) (by rw [hξv]; exact he.pos) (by rw [hξv, add_zero]; exact heB)
    rwa [add_zero] at this
  obtain ⟨hq1, hrT, hr1, hdec⟩ := lu_split hρE hρ1 hξT hξ2 hΩξ
  rcases lt_or_ge (ξ / Om1) Om1 with hqΩ | hqΩ
  · have hξs : ξ < Om1 * Om1 := by
      rw [← hdec]
      calc Om1 * (ξ / Om1) + ξ % Om1 < Om1 * (ξ / Om1) + Om1 := (add_lt_add_iff_left _).2 hr1
        _ = Om1 * (ξ / Om1 + 1) := (mul_add_one _ _).symm
        _ ≤ Om1 * Om1 := mul_le_mul_right (Order.add_one_le_of_lt hqΩ) _
    have hqT : ξ / Om1 ∈ Tset ρ := lgQuot_mem hρE hρ1 hξT hξs
    have hev : Gl.glA (ξ / Om1) (ξ % Om1) ρ = e := by
      show vt ρ (Om1 * (ξ / Om1) + ξ % Om1) = e
      rw [hdec, hξv]
    rw [← hev] at IHe ⊢
    exact qc_img_veb h hq1 hqT hqΩ hrT hr1 IHe
  · have hMN : ξ / Om1 < N := by
      have h1 : Om1 * (ξ / Om1) ≤ ξ := Ordinal.mul_div_le ξ Om1
      exact (mul_lt_mul_iff_right₀ rj_Om1_pos).1 (h1.trans_lt hξN)
    have hMG : ξ / Om1 < ggGam := hMN.trans hNG
    have hMT : Tf.tfDat (ξ / Om1) ∈ Tset ρ :=
      tfArg_dat hρE hρ1 hqΩ (hMG.trans qf_gg_lt_BG) hr1 (by rw [hdec]; exact hξT)
    have hev : vt ρ (Om1 * (ξ / Om1) + ξ % Om1) = e := by rw [hdec, hξv]
    rw [← hev] at IHe ⊢
    rcases lt_or_ge (ξ / Om1) ggE with hME | hME
    · have hMTr : rjDat (ξ / Om1) ∈ Tset ρ := by rw [← Tf.tfDat_eq_rj _ hME]; exact hMT
      exact qc_img_lvl h hρS hqΩ hME hMTr hrT hr1 IHe
    · exact qf_img_lvl h hTB hρS hME hMG hMT hrT hr1 IHe

end Img

/-- **`Qd.QdImgH`: LEMMA IMG BELOW EVERY POINT OF A VEBLEN LEVEL**, in every restart context, given `QfTBphi`. -/
theorem qf_imgH (hTB : QfTBphi) : Qd.QdImgH := by
  intro ρ τ δ v h hb
  obtain ⟨N, hN1, hNG, hNx, hv⟩ := hb
  exact qf_img h hTB (qc_rstK_SC h) hN1 hNG hNx v hv

end Googology.Trans.PoR.InaccPsi.R2.Qf
