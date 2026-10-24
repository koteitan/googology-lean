import Googology.Trans.PoR.InaccPsi.R2.GnIw

/-!
# LEMMA IMG BELOW THE NEXT `ε`-FIXED POINT ABOVE `Γ_{ρ+1}`: every value below `ζ_{Γ_{ρ+1}+1} = evZ(Γ_{ρ+1})`

The `ε`-numbers in `(Γ_{ρ+1}, evZ(Γ_{ρ+1}))` are `ε_{Γ_{ρ+1}+c}` (`0 < c < evZ(Γ_{ρ+1})`); their `R₁⁺`-reach is
`ε_{Γ+c}·2 + logend(c)` (`Gk.gk_lh_evA` at the pseudo-base `Γ_{ρ+1}`; the reach is a property of ordinals only).
Lemma IMG in `π`-form is proved for them WITHOUT a formula for `π(ε_{Γ+c})`: if a copy had `f(E) < π(E)`, then
`f(E) = π(u)` for some `u ∈ Tᵖ[f(ρ)]` (`π` is onto `T^{f(ρ)}`, an initial segment), `u` is an `ε`-number (the
test `u ≤₁ u·2` goes down, `down_le1R`), it lies strictly between the previous `ε`-number and `E`, and for a limit
index `c = c' + ω^z` its reach `π(lh(u)) = lh(f(E)) ≥ f(E)·2 + f(z) ≥ f(E)·2 + π(z)` ([W07b] Cor 5.7, `lh_pi`) forces
`ω^z ∣ d` for the index `d ∈ (c', c)` of `u`, which is impossible.  With the generic step `gnImg_of_eps`:

* `gn_evZG_lt1` (`evZ(Γ_{x+1}) < Γ_{x+2}`, through `ϑˣ(Ω₁·2 + Γ_{x+1})`), `gn_pi_inv` (the inverse image),
  `gn_eps_down` (the `ε`-test goes down), `gnI_epsG` (**Lemma IMG for every `ε`-number in
  `(Γ_{ρ+1}, evZ(Γ_{ρ+1}))`**, given Lemma IMG below it);
* `gnImg_Z` (**LEMMA IMG FOR EVERY VALUE BELOW `ζ_{Γ_{ρ+1}+1}`**), `gnPkg_of_exZ` (**Lemma IMG (gated) for a specified
  function with Lemma EXACT and value below `ζ_{Γ_{ρ+1}+1}`**).

No new axiom, no new definition.

[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gn

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **`evZ(Γ_{x+1}) < Γ_{x+2}`**: `ϑˣ(Ω₁·2 + Γ_{x+1})` is an `ε`-fixed point above `Γ_{x+1}` below `Γ_{x+2}`. -/
theorem gn_evZG_lt1 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : evZ (lgG x) < gq 1 x := by
  obtain ⟨hGT, -, hG1, -, -⟩ := lgG_facts hx hx1
  have hq := (gm1_facts hx hx1).2.2.2
  have h2q : (2 : Ordinal.{0}) < gq 1 x :=
    ((show (2 : Ordinal.{0}) < ω from nat_lt_omega0 2)).trans (omega0_lt_inE hq)
  obtain ⟨h2T, h21⟩ := gm1_T hx hx1 h2q
  have h12 : (1 : Ordinal.{0}) ≤ 2 := one_le_two
  obtain ⟨-, -, -, -, -, hta⟩ := glA_facts hx hx1 h12 h2T h21 hGT hG1
  obtain ⟨i, hi⟩ := glA_P hx hx1 h12 h2T h21 hGT hG1
  have hfix : Ordinal.epsilon (glA 2 (lgG x) x) = glA 2 (lgG x) x := by
    rw [← hi]; exact veblen_veblen_of_lt one_lt_two i
  refine (evZ_le hta hfix).trans_lt ?_
  exact lgVt_lt_low hx hx1 h2T h21 hGT hG1 (gm1_one_T hx hx1).1 (gm1_one_T hx hx1).2 h2q
    (mg_lgG_lt_G1 hx hx1)

/-- The inverse image under `π` of an ordinal below a value of `π`. -/
theorem gn_pi_inv {σ ρ v w : Ordinal.{0}} (hB : Bases σ ρ) (hv : v ∈ TB ρ σ) (hv1 : v < Om1)
    (hw : w < pi σ ρ v) : ∃ u, u ∈ TB ρ σ ∧ pi σ ρ u = w ∧ u < v := by
  have hσ1 : σ < Om1 := hB.2.2.1.trans hB.2.2.2
  obtain ⟨m, -, -, -, hTm, -⟩ := T_next (Or.inr hB.1) hσ1
  have hpv1 := vz_pi_lt_Om1 hB hv hv1
  have hpvT : pi σ ρ v ∈ Tset σ := (pi_bijOn hB).1.mapsTo hv
  have hwT : w ∈ Tset σ := (hTm w (hw.trans hpv1)).2 (hw.trans ((hTm _ hpv1).1 hpvT))
  obtain ⟨u, huTB, hu⟩ := (pi_bijOn hB).1.surjOn hwT
  refine ⟨u, huTB, hu, ?_⟩
  by_contra hge
  push Not at hge
  have := ((pi_bijOn hB).2.le_iff_le hv huTB).2 hge
  rw [hu] at this
  exact absurd hw (not_lt.2 this)

/-- **The `ε`-test goes down**: if `π(u)` is an `ε`-number then so is `u` (`υ`-points `σ < ρ`). -/
theorem gn_eps_down {σ ρ u : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) (hu : u ∈ TB ρ σ)
    (hu1 : u < Om1) (hpu : InE (pi σ ρ u)) (hu0 : 0 < u) : InE u := by
  obtain ⟨huu, hpuu⟩ := pi_add hB hu hu
  have h1 : le1R (pi σ ρ u) (pi σ ρ (u + u)) := by
    rw [hpuu, ← mul_two_eq]; exact (le1R_two_iff hpu.pos).2 hpu
  have h2 := (down_le1R hσ hρ hB hu huu hu1).2 h1
  rw [← mul_two_eq] at h2
  exact (le1R_two_iff hu0).1 h2

section Img

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **Lemma IMG in `π`-form for every `ε`-number `E ∈ (Γ_{ρ+1}, evZ(Γ_{ρ+1}))`**, given Lemma IMG for every value below
`E`. -/
theorem gnI_epsG {E : Ordinal.{0}} (hE : InE E) (hGE : lgG ρ < E) (hEZ : E < evZ (lgG ρ))
    (IH : ∀ u, u < E → GnI ρ δ u) : GnI ρ δ E := by
  classical
  have hρE := h.ρE
  obtain ⟨-, hρG, hG1, hGI, -⟩ := lgG_facts hρE h.ρ1
  set G := lgG ρ with hGdef
  have hET : E ∈ Tset ρ ∧ E < Om1 := gm1_T hρE h.ρ1 (hEZ.trans (gn_evZG_lt1 hρE h.ρ1))
  have hEδ : E < δ := gn_lt_δ h hET.1 hET.2
  have hδI := inE_indec h.δE
  have hEEδ : E + E < δ := hδI.add_lt hEδ hEδ
  have hρE' : ρ < E := hρG.trans hGE
  obtain ⟨c, hc⟩ := evA_surj hGI hE hGE.le
  have hc0 : c ≠ 0 := by rintro rfl; rw [evA_zero hGI] at hc; exact absurd hc hGE.ne
  have hcZ : c < evZ G := by
    by_contra hge; push Not at hge
    exact absurd (hge.trans ((le_evA_idx G c).trans hc.le)) (not_le.2 hEZ)
  -- the inverse image of a copy below `π(E)`
  have key : ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ImgCtx ρ A f → E ∈ A → E + E ∈ A →
      E ∈ TB ρ (f ρ) → ∀ E', E' < E → E' ∈ A → E' ∈ TB ρ (f ρ) → pi (f ρ) ρ E' ≤ f E' →
      f E < pi (f ρ) ρ E → ∃ u, u ∈ TB ρ (f ρ) ∧ pi (f ρ) ρ u = f E ∧ E' < u ∧ u < E ∧ InE u := by
    intro A f C hEA hEEA hETB E' hE'E hE'A hE'TB pE' hlt
    have hB := h.img_bases C
    obtain ⟨u, huTB, hpu, huE⟩ := gn_pi_inv hB hETB hET.2 hlt
    have hfE : InE (f E) := gk_img_inE C hEA hEEA (gk_src2 h hE hρE' hEEδ.le)
      (lt_of_le_of_lt zero_le (C.mono C.rho hEA hρE'))
    have hfE'E : f E' < f E := C.mono hE'A hEA hE'E
    have hE'u : E' < u := by
      refine ((pi_bijOn hB).2.lt_iff_lt hE'TB huTB).1 ?_
      rw [hpu]; exact lt_of_le_of_lt pE' hfE'E
    have hu1 : u < Om1 := huE.trans hET.2
    have huE' : InE u := gn_eps_down C.ups h.ρU hB huTB hu1 (by rw [hpu]; exact hfE)
      (lt_of_le_of_lt zero_le hE'u)
    exact ⟨u, huTB, hpu, hE'u, huE, huE'⟩
  have hpEbig : ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ImgCtx ρ A f → E ∈ A →
      E ∈ TB ρ (f ρ) → UpsPt (f E) → pi (f ρ) ρ E < f E := by
    intro A f C hEA hETB hU
    have hB := h.img_bases C
    have hfρ : InE (f ρ) := upsPt_inE C.ups
    have hfρ1 : f ρ < Om1 := (C.low ρ C.rho).trans h.ρ1
    exact gn_lt_ups hfρ hfρ1 ((pi_bijOn hB).1.mapsTo hETB) (vz_pi_lt_Om1 hB hETB hET.2) hU
      (C.mono C.rho hEA hρE')
  rcases zero_or_succ_or_isSuccLimit c with h0 | ⟨c', hc'⟩ | hlim
  · exact absurd h0 hc0
  · -- `c = c' + 1`: `E = ε_{E'+1}`
    have hcs : c = c' + 1 := by rw [← hc', succ_eq_add_one]
    set E' := evA G c' with hE'def
    have hE'E : E' < E := by rw [← hc, hcs]; exact evA_lt_iff.2 (lt_add_one c')
    have hEeq : E = eN E' := by rw [← hc, hcs, evA_add_one]
    obtain ⟨W1, Z1, w1, m1, -, -, b1⟩ := gnI_use h (IH E' hE'E)
    have w2 := w1.insW hρE'.le hEδ (Or.inl (inE_indec hE))
    have w3 := w2.insW (hρE'.le.trans le_self_add) hEEδ
      (Or.inr ⟨E, by simp, E, by simp, lt_add_of_pos_right _ hE.pos, lt_add_of_pos_right _ hE.pos, rfl⟩)
    refine gnI_mk h w3 (by simp) hET.1 hET.2 (fun A f hW hZ C => ?_)
    have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    obtain ⟨hE'A, hE'TB, pE'⟩ := b1 A f hW1 hZ1 C
    have hEA : E ∈ A := hW (by simp)
    have hEEA : E + E ∈ A := hW (by simp)
    have hETB : E ∈ TB ρ (f ρ) := gnI_TB h C hET.1 (fun p hp => hZ (by simp [hp]))
    by_contra hlt
    push Not at hlt
    obtain ⟨u, -, -, hE'u, huE, huI⟩ := key A f C hEA hEEA hETB E' hE'E hE'A hE'TB pE' hlt
    rw [hEeq] at huE
    exact absurd (eN_le hE'u huI) (not_le.2 huE)
  · -- a limit `c = c' + ω^z`
    have hωc : ω ≤ c := omega0_le_of_isSuccLimit hlim
    obtain ⟨c', hcs, hdvd, hc'c⟩ := lg_split hc0
    set z := lg c with hzdef
    have hz0 : z ≠ 0 := by
      intro hz
      rw [hz, opow_zero] at hcs
      exact not_isSuccLimit_succ c' (by rw [succ_eq_add_one, ← hcs]; exact hlim)
    set E' := evA G c' with hE'def
    have hE'E : E' < E := by rw [← hc]; exact evA_lt_iff.2 hc'c
    have hzE : z < E := (lg_le hc0).trans_lt (by rw [← hc]; exact lt_evA_self hGI hcZ)
    have hlh : IsLh1 E (E * 2 + z) := by rw [← hc]; exact gk_lh_evA hGI hG1 hc0 hcZ
    have hEEz : E + E < E + E + z := lt_add_of_pos_right _ (pos_iff_ne_zero.2 hz0)
    have hzEEz : z < E + E + z := hzE.trans ((lt_add_of_pos_right _ hE.pos).trans hEEz)
    have hEEzδ : E + E + z < δ := hδI.add_lt hEEδ (hzE.trans hEδ)
    have hsrc : le1 E (E + E + z) := by
      refine (h.lowδ _ _ hρE' hEEzδ.le).2 ?_
      have := hlh.1
      rwa [mul_two_eq] at this
    obtain ⟨W1, Z1, w1, m1, -, -, b1⟩ := gnI_use h (IH E' hE'E)
    obtain ⟨W2, Z2, w2, m2, -, -, b2⟩ := gnI_use h (IH z hzE)
    have w3 := (w1.union w2).insW hρE'.le hEδ (Or.inl (inE_indec hE))
    have w4 := w3.insW (hρE'.le.trans le_self_add) hEEδ
      (Or.inr ⟨E, by simp, E, by simp, lt_add_of_pos_right _ hE.pos, lt_add_of_pos_right _ hE.pos, rfl⟩)
    have w5 := w4.insW ((hρE'.le.trans le_self_add).trans le_self_add) hEEzδ
      (Or.inr ⟨E + E, by simp, z, by rcases Finset.mem_union.1 m2 with hm | hm <;> simp [hm], hEEz, hzEEz, rfl⟩)
    refine gnI_mk h w5 (by simp) hET.1 hET.2 (fun A f hW hZ C => ?_)
    have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    have hW2 : ↑W2 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hZ2 : ↑Z2 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    obtain ⟨hE'A, hE'TB, pE'⟩ := b1 A f hW1 hZ1 C
    obtain ⟨hzA, hzTB, pz⟩ := b2 A f hW2 hZ2 C
    have hEA : E ∈ A := hW (by simp)
    have hEEA : E + E ∈ A := hW (by simp)
    have hEEzA : E + E + z ∈ A := hW (by simp)
    have hETB : E ∈ TB ρ (f ρ) := gnI_TB h C hET.1 (fun p hp => hZ (by simp [hp]))
    have hB := h.img_bases C
    by_contra hlt
    push Not at hlt
    by_cases hU : UpsPt (f E)
    · exact absurd (hpEbig A f C hEA hETB hU) (not_lt.2 hlt.le)
    have himg : le1 (f E) (f E + f E + f z) := by
      have := C.cov1 _ hEA _ hEEzA hsrc
      rwa [← C.add _ hEEA _ hzA _ hEEzA rfl, ← C.add _ hEA _ hEA _ hEEA rfl] at this
    have hR := (C.sk _ (C.low _ hEA) hU _).1 himg
    obtain ⟨u, huTB, hpu, hE'u, huE, huI⟩ := key A f C hEA hEEA hETB E' hE'E hE'A hE'TB pE' hlt
    have hGu : G ≤ u := (le_evA hGI c').trans hE'u.le
    obtain ⟨d, hd⟩ := evA_surj hGI huI hGu
    have hd0 : d ≠ 0 := by
      rintro rfl
      rw [evA_zero hGI] at hd
      exact absurd (lt_of_lt_of_eq hE'u hd.symm) (not_lt.2 (le_evA hGI c'))
    have hu1 : u < Om1 := huE.trans hET.2
    have hdZ : d < evZ G := by
      by_contra hge; push Not at hge
      exact absurd (hge.trans ((le_evA_idx G d).trans hd.le)) (not_le.2 (huE.trans hEZ))
    have hc'd : c' < d := (evA_lt_iff (x := G)).1 (lt_of_lt_of_eq hE'u hd.symm)
    have hdc : d < c := (evA_lt_iff (x := G)).1 (by rw [hd, hc]; exact huE)
    have hlhu : IsLh1 u (u * 2 + lg d) := by rw [← hd]; exact gk_lh_evA hGI hG1 hd0 hdZ
    have hρu : ρ < u := hρG.trans_le hGu
    obtain ⟨l, hl, hlTB, hpl⟩ := lh_pi hB huTB hρu hu1
    have hl' : l = u + u + lg d := by rw [lkcIsLh1_unique hl hlhu, mul_two_eq]
    rw [hl'] at hlTB hpl
    obtain ⟨huu1, huu2⟩ := pi_add hB huTB huTB
    have hlg1 : u + u + lg d < Om1 := by
      have hld : lg d < u := (lg_le hd0).trans_lt (by rw [← hd]; exact lt_evA_self hGI hdZ)
      exact (inE_indec gl_Om1_E).add_lt ((inE_indec gl_Om1_E).add_lt hu1 hu1) (hld.trans hu1)
    obtain ⟨hdTB, -⟩ := TB_sub hB huu1 hlTB le_self_add hlg1
    rw [Ordinal.add_sub_cancel] at hdTB
    obtain ⟨-, hps⟩ := pi_add hB huu1 hdTB
    have hle := hpl.2 _ (by rw [hpu]; exact hR)
    rw [hps, huu2, hpu] at hle
    have hfz : f z ≤ pi (f ρ) ρ (lg d) := (add_le_add_iff_left _).1 hle
    have hzd : z ≤ lg d := ((pi_bijOn hB).2.le_iff_le hzTB hdTB).1 (pz.trans hfz)
    have hdiv : ω ^ z ∣ d := (le_lg_iff hd0 z).1 hzd
    obtain ⟨δ', hδ'⟩ : ∃ δ', d = c' + δ' := ⟨d - c', (Ordinal.add_sub_cancel_of_le hc'd.le).symm⟩
    have hδ0 : δ' ≠ 0 := by rintro rfl; rw [add_zero] at hδ'; exact absurd hδ' hc'd.ne'
    have hδlt : δ' < ω ^ z := by
      have : c' + δ' < c' + ω ^ z := by rw [← hδ', ← hcs]; exact hdc
      exact (add_lt_add_iff_left _).1 this
    have hdivδ : ω ^ z ∣ δ' := (dvd_add_iff hdvd).1 (by rw [← hδ']; exact hdiv)
    exact absurd (Ordinal.le_of_dvd hδ0 hdivδ) (not_le.2 hδlt)

/-- **LEMMA IMG FOR EVERY VALUE BELOW `ζ_{Γ_{ρ+1}+1} = evZ(Γ_{ρ+1})`** (the next `ε`-fixed point above `Γ_{ρ+1}`). -/
theorem gnImg_Z : ∀ v, v < evZ (lgG ρ) → GnI ρ δ v := by
  have hρE := h.ρE
  refine gnImg_of_eps h (fun v hv => gm1_T hρE h.ρ1 (hv.trans (gn_evZG_lt1 hρE h.ρ1)))
    (fun e he _ heB IHe => ?_)
  rcases lt_trichotomy e (lgG ρ) with hlt | rfl | hgt
  · exact gnI_lowG h hlt
  · exact gnI_G h
  · exact gnI_epsG h he hgt heB IHe

/-- **LEMMA IMG (gated) FOR A SPECIFIED FUNCTION BELOW `ζ_{Γ_{ρ+1}+1}`**: Lemma EXACT above the gate `g < ρ` with
constants `C < ρ` and `T(ρ) < evZ(Γ_{ρ+1})` give `T(f ρ) ≤ f(T ρ)` for every covering copy `f` that keeps `g`. -/
theorem gnPkg_of_exZ {g : Ordinal.{0}} {C : Finset Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}} (hgρ : g < ρ)
    (hC : ∀ c ∈ C, c < ρ) (hT : T ρ < evZ (lgG ρ)) (hex : GjEx g C T) : GhPkg g ρ δ T :=
  gnPkg_of_GnI h hgρ hC (gnImg_Z h _ hT) hex

end Img

end Googology.Trans.PoR.InaccPsi.R2.Gn
