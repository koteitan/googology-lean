import Googology.Trans.PoR.InaccPsi.R2.GwEx

/-!
# LEMMA IMG AT VEBLEN LEVEL 2: the `ε`-fixed points `ζ_{Γ_{ρ+1}+n}` and every value below `ζ_{Γ_{ρ+1}+ω}`

`Gn.gnImg_Z` gives Lemma IMG (in `π`-form, `Gn.GnI`) for every value below `ζ_{Γ_{ρ+1}+1} = evZ(Γ_{ρ+1})`, the wall
of the gated digit systems (`Gs.GsD.R_lt_Z`).  Here:

* `gw_evZ_lt1` (**`evZ(P) < Γ_{x+2}` for every `P < Γ_{x+2}`**, through `ϑˣ(Ω₁·2 + P)`);
* `gw_key`, `gw_pbig` (the inverse image of a copy below `π(E)` and the `υ`-point case, as in `Gn.gnI_epsG`);
* `gwI_epsP` (**Lemma IMG for every `ε`-number `E ∈ (P, evZ(P))` over ANY `ε`-number pseudo-base `ρ < P < Γ_{ρ+2}`**,
  given Lemma IMG below `E`: `Gn.gnI_epsG` with `Γ_{ρ+1}` replaced by `P`);
* `gwI_fixZ` (**Lemma IMG for the `ε`-fixed point `E = evZ(P)` itself**, given Lemma IMG below it: a copy `f` with
  `f(E) < π(E)` gives `π(u) = f(E)` for an `ε`-number `u ∈ (P, E)`, `u = ε_{P+d}`, `0 < d < evZ(P)`; the source
  `E ≤₁ E·3` (`EvV.vz_lh_evZ`) is copied to `f(E) ≤₁ f(E)·3` in `R₁⁺`, and `π(lh(u)) = lh(π(u))` ([W07b] Cor 5.7,
  `lh_pi`) with `lh(u) = u·2 + lg(d)` (`Gk.gk_lh_evA`) forces `u ≤ lg(d) ≤ d < u`, impossible);
* `gwZn` (`Z₀ = Γ_{ρ+1}`, `Z_{n+1} = evZ(Z_n)`: `Z_n = ζ_{Γ_{ρ+1}+n}`), `gwZn_E`, `gwZn_gt`, `gwZn_lt`;
* `gwImg_Zn` (**LEMMA IMG FOR EVERY VALUE BELOW `ζ_{Γ_{ρ+1}+n+1}`, EVERY `n`**), `gwImg_Zw` (**below
  `ζ_{Γ_{ρ+1}+ω}`**), `gwPkg_of_exZn` (**Lemma IMG (gated) for a specified function with Lemma EXACT and value below
  `ζ_{Γ_{ρ+1}+n}`**).

No new axiom.  New definition: `gwZn`.

[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gw

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **`evZ(P) < Γ_{x+2}` for every `P < Γ_{x+2}`**: `ϑˣ(Ω₁·2 + P)` is an `ε`-fixed point above `P` below `Γ_{x+2}`. -/
theorem gw_evZ_lt1 {x P : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hP : P < gq 1 x) : evZ P < gq 1 x := by
  obtain ⟨hPT, hP1⟩ := gm1_T hx hx1 hP
  have hq := (gm1_facts hx hx1).2.2.2
  have h2q : (2 : Ordinal.{0}) < gq 1 x :=
    ((show (2 : Ordinal.{0}) < ω from nat_lt_omega0 2)).trans (omega0_lt_inE hq)
  obtain ⟨h2T, h21⟩ := gm1_T hx hx1 h2q
  have h12 : (1 : Ordinal.{0}) ≤ 2 := one_le_two
  obtain ⟨-, -, -, -, -, hta⟩ := glA_facts hx hx1 h12 h2T h21 hPT hP1
  obtain ⟨i, hi⟩ := glA_P hx hx1 h12 h2T h21 hPT hP1
  have hfix : Ordinal.epsilon (glA 2 P x) = glA 2 P x := by
    rw [← hi]; exact veblen_veblen_of_lt one_lt_two i
  refine (evZ_le hta hfix).trans_lt ?_
  exact lgVt_lt_low hx hx1 h2T h21 hPT hP1 (gm1_one_T hx hx1).1 (gm1_one_T hx hx1).2 h2q hP

section Img

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **The inverse image of a copy below `π(E)`**: an `ε`-number `u ∈ (E', E)` with `π(u) = f(E)`. -/
theorem gw_key {E : Ordinal.{0}} (hE : InE E) (hET : E ∈ Tset ρ ∧ E < Om1) (hρE' : ρ < E) (hEEδ : E + E < δ)
    (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) (C : ImgCtx ρ A f) (hEA : E ∈ A) (hEEA : E + E ∈ A)
    (hETB : E ∈ TB ρ (f ρ)) (E' : Ordinal.{0}) (hE'E : E' < E) (hE'A : E' ∈ A) (hE'TB : E' ∈ TB ρ (f ρ))
    (pE' : pi (f ρ) ρ E' ≤ f E') (hlt : f E < pi (f ρ) ρ E) :
    ∃ u, u ∈ TB ρ (f ρ) ∧ pi (f ρ) ρ u = f E ∧ E' < u ∧ u < E ∧ InE u := by
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

/-- A copy whose value at `E` is a `υ`-point lies above `π(E)`. -/
theorem gw_pbig {E : Ordinal.{0}} (hET : E ∈ Tset ρ ∧ E < Om1) (hρE' : ρ < E) (A : Set Ordinal.{0})
    (f : Ordinal.{0} → Ordinal.{0}) (C : ImgCtx ρ A f) (hEA : E ∈ A) (hETB : E ∈ TB ρ (f ρ))
    (hU : UpsPt (f E)) : pi (f ρ) ρ E < f E := by
  have hB := h.img_bases C
  have hfρ : InE (f ρ) := upsPt_inE C.ups
  have hfρ1 : f ρ < Om1 := (C.low ρ C.rho).trans h.ρ1
  exact gn_lt_ups hfρ hfρ1 ((pi_bijOn hB).1.mapsTo hETB) (vz_pi_lt_Om1 hB hETB hET.2) hU
    (C.mono C.rho hEA hρE')

/-- **Lemma IMG for every `ε`-number `E ∈ (P, evZ(P))` over an `ε`-number pseudo-base `P`** (`ρ < P < Γ_{ρ+2}`),
given Lemma IMG for every value below `E`. -/
theorem gwI_epsP {P E : Ordinal.{0}} (hPI : InE P) (hρP : ρ < P) (hPq : P < gq 1 ρ) (hE : InE E) (hPE : P < E)
    (hEZ : E < evZ P) (IH : ∀ u, u < E → GnI ρ δ u) : GnI ρ δ E := by
  classical
  have hρE := h.ρE
  have hP1 : P < Om1 := hPq.trans (gm1_facts hρE h.ρ1).2.2.1
  have hET : E ∈ Tset ρ ∧ E < Om1 := gm1_T hρE h.ρ1 (hEZ.trans (gw_evZ_lt1 hρE h.ρ1 hPq))
  have hEδ : E < δ := gn_lt_δ h hET.1 hET.2
  have hδI := inE_indec h.δE
  have hEEδ : E + E < δ := hδI.add_lt hEδ hEδ
  have hρE' : ρ < E := hρP.trans hPE
  obtain ⟨c, hc⟩ := evA_surj hPI hE hPE.le
  have hc0 : c ≠ 0 := by rintro rfl; rw [evA_zero hPI] at hc; exact absurd hc hPE.ne
  have hcZ : c < evZ P := by
    by_contra hge; push Not at hge
    exact absurd (hge.trans ((le_evA_idx P c).trans hc.le)) (not_le.2 hEZ)
  rcases zero_or_succ_or_isSuccLimit c with h0 | ⟨c', hc'⟩ | hlim
  · exact absurd h0 hc0
  · -- `c = c' + 1`: `E = ε_{E'+1}`
    have hcs : c = c' + 1 := by rw [← hc', succ_eq_add_one]
    set E' := evA P c' with hE'def
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
    obtain ⟨u, -, -, hE'u, huE, huI⟩ := gw_key h hE hET hρE' hEEδ A f C hEA hEEA hETB E' hE'E hE'A hE'TB pE' hlt
    rw [hEeq] at huE
    exact absurd (eN_le hE'u huI) (not_le.2 huE)
  · -- a limit `c = c' + ω^z`
    obtain ⟨c', hcs, hdvd, hc'c⟩ := lg_split hc0
    set z := lg c with hzdef
    have hz0 : z ≠ 0 := by
      intro hz
      rw [hz, opow_zero] at hcs
      exact not_isSuccLimit_succ c' (by rw [succ_eq_add_one, ← hcs]; exact hlim)
    set E' := evA P c' with hE'def
    have hE'E : E' < E := by rw [← hc]; exact evA_lt_iff.2 hc'c
    have hzE : z < E := (lg_le hc0).trans_lt (by rw [← hc]; exact lt_evA_self hPI hcZ)
    have hlh : IsLh1 E (E * 2 + z) := by rw [← hc]; exact gk_lh_evA hPI hP1 hc0 hcZ
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
    · exact absurd (gw_pbig h hET hρE' A f C hEA hETB hU) (not_lt.2 hlt.le)
    have himg : le1 (f E) (f E + f E + f z) := by
      have := C.cov1 _ hEA _ hEEzA hsrc
      rwa [← C.add _ hEEA _ hzA _ hEEzA rfl, ← C.add _ hEA _ hEA _ hEEA rfl] at this
    have hR := (C.sk _ (C.low _ hEA) hU _).1 himg
    obtain ⟨u, huTB, hpu, hE'u, huE, huI⟩ :=
      gw_key h hE hET hρE' hEEδ A f C hEA hEEA hETB E' hE'E hE'A hE'TB pE' hlt
    have hGu : P ≤ u := (le_evA hPI c').trans hE'u.le
    obtain ⟨d, hd⟩ := evA_surj hPI huI hGu
    have hd0 : d ≠ 0 := by
      rintro rfl
      rw [evA_zero hPI] at hd
      exact absurd (lt_of_lt_of_eq hE'u hd.symm) (not_lt.2 (le_evA hPI c'))
    have hu1 : u < Om1 := huE.trans hET.2
    have hdZ : d < evZ P := by
      by_contra hge; push Not at hge
      exact absurd (hge.trans ((le_evA_idx P d).trans hd.le)) (not_le.2 (huE.trans hEZ))
    have hc'd : c' < d := (evA_lt_iff (x := P)).1 (lt_of_lt_of_eq hE'u hd.symm)
    have hdc : d < c := (evA_lt_iff (x := P)).1 (by rw [hd, hc]; exact huE)
    have hlhu : IsLh1 u (u * 2 + lg d) := by rw [← hd]; exact gk_lh_evA hPI hP1 hd0 hdZ
    have hρu : ρ < u := hρP.trans_le hGu
    obtain ⟨l, hl, hlTB, hpl⟩ := lh_pi hB huTB hρu hu1
    have hl' : l = u + u + lg d := by rw [lkcIsLh1_unique hl hlhu, mul_two_eq]
    rw [hl'] at hlTB hpl
    obtain ⟨huu1, huu2⟩ := pi_add hB huTB huTB
    have hlg1 : u + u + lg d < Om1 := by
      have hld : lg d < u := (lg_le hd0).trans_lt (by rw [← hd]; exact lt_evA_self hPI hdZ)
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

/-- **LEMMA IMG FOR THE `ε`-FIXED POINT `evZ(P)`** (`ρ < P < Γ_{ρ+2}`, `P` an `ε`-number), given Lemma IMG for every
value below it. -/
theorem gwI_fixZ {P : Ordinal.{0}} (hPI : InE P) (hρP : ρ < P) (hPq : P < gq 1 ρ)
    (IH : ∀ u, u < evZ P → GnI ρ δ u) : GnI ρ δ (evZ P) := by
  classical
  have hρE := h.ρE
  set E := evZ P with hEdef
  have hP1 : P < Om1 := hPq.trans (gm1_facts hρE h.ρ1).2.2.1
  have hE : InE E := evZ_E P
  have hPE : P < E := lt_evZ P
  have hET : E ∈ Tset ρ ∧ E < Om1 := gm1_T hρE h.ρ1 (gw_evZ_lt1 hρE h.ρ1 hPq)
  have hEδ : E < δ := gn_lt_δ h hET.1 hET.2
  have hδI := inE_indec h.δE
  have hEEδ : E + E < δ := hδI.add_lt hEδ hEδ
  have hρE' : ρ < E := hρP.trans hPE
  have hEEE : E + E < E + E + E := lt_add_of_pos_right _ hE.pos
  have hEEEδ : E + E + E < δ := hδI.add_lt hEEδ hEδ
  have hlh : IsLh1 E (E * 2 + E) := vz_lh_evZ hPI hP1
  have hsrc : le1 E (E + E + E) := by
    refine (h.lowδ _ _ hρE' hEEEδ.le).2 ?_
    have := hlh.1
    rwa [mul_two_eq] at this
  obtain ⟨W1, Z1, w1, m1, -, -, b1⟩ := gnI_use h (IH P hPE)
  have w3 := w1.insW hρE'.le hEδ (Or.inl (inE_indec hE))
  have w4 := w3.insW (hρE'.le.trans le_self_add) hEEδ
    (Or.inr ⟨E, by simp, E, by simp, lt_add_of_pos_right _ hE.pos, lt_add_of_pos_right _ hE.pos, rfl⟩)
  have w5 := w4.insW ((hρE'.le.trans le_self_add).trans le_self_add) hEEEδ
    (Or.inr ⟨E + E, by simp, E, by simp, hEEE, (lt_add_of_pos_right _ hE.pos).trans hEEE, rfl⟩)
  refine gnI_mk h w5 (by simp) hET.1 hET.2 (fun A f hW hZ C => ?_)
  have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  obtain ⟨hPA, hPTB, pP⟩ := b1 A f hW1 hZ1 C
  have hEA : E ∈ A := hW (by simp)
  have hEEA : E + E ∈ A := hW (by simp)
  have hEEEA : E + E + E ∈ A := hW (by simp)
  have hETB : E ∈ TB ρ (f ρ) := gnI_TB h C hET.1 (fun p hp => hZ (by simp [hp]))
  have hB := h.img_bases C
  by_contra hlt
  push Not at hlt
  by_cases hU : UpsPt (f E)
  · exact absurd (gw_pbig h hET hρE' A f C hEA hETB hU) (not_lt.2 hlt.le)
  have himg : le1 (f E) (f E + f E + f E) := by
    have := C.cov1 _ hEA _ hEEEA hsrc
    rwa [← C.add _ hEEA _ hEA _ hEEEA rfl, ← C.add _ hEA _ hEA _ hEEA rfl] at this
  have hR := (C.sk _ (C.low _ hEA) hU _).1 himg
  obtain ⟨u, huTB, hpu, hPu, huE, huI⟩ := gw_key h hE hET hρE' hEEδ A f C hEA hEEA hETB P hPE hPA hPTB pP hlt
  obtain ⟨d, hd⟩ := evA_surj hPI huI hPu.le
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [evA_zero hPI] at hd
    exact absurd hd hPu.ne
  have hu1 : u < Om1 := huE.trans hET.2
  have hdZ : d < evZ P := by
    by_contra hge; push Not at hge
    exact absurd (hge.trans ((le_evA_idx P d).trans hd.le)) (not_le.2 huE)
  have hlhu : IsLh1 u (u * 2 + lg d) := by rw [← hd]; exact gk_lh_evA hPI hP1 hd0 hdZ
  have hρu : ρ < u := hρP.trans hPu
  obtain ⟨l, hl, hlTB, hpl⟩ := lh_pi hB huTB hρu hu1
  have hl' : l = u + u + lg d := by rw [lkcIsLh1_unique hl hlhu, mul_two_eq]
  rw [hl'] at hlTB hpl
  obtain ⟨huu1, huu2⟩ := pi_add hB huTB huTB
  have hld : lg d < u := (lg_le hd0).trans_lt (by rw [← hd]; exact lt_evA_self hPI hdZ)
  have hlg1 : u + u + lg d < Om1 :=
    (inE_indec gl_Om1_E).add_lt ((inE_indec gl_Om1_E).add_lt hu1 hu1) (hld.trans hu1)
  obtain ⟨hdTB, -⟩ := TB_sub hB huu1 hlTB le_self_add hlg1
  rw [Ordinal.add_sub_cancel] at hdTB
  obtain ⟨-, hps⟩ := pi_add hB huu1 hdTB
  have hle := hpl.2 _ (by rw [hpu]; exact hR)
  rw [hps, huu2, hpu] at hle
  have hfz : f E ≤ pi (f ρ) ρ (lg d) := (add_le_add_iff_left _).1 hle
  have hud : u ≤ lg d := ((pi_bijOn hB).2.le_iff_le huTB hdTB).1 (by rw [hpu]; exact hfz)
  exact absurd hud (not_le.2 hld)

end Img

/-! ## The `ζ`-numbers `ζ_{Γ_{ρ+1}+n}` -/

/-- **`Z₀ = Γ_{ρ+1}`, `Z_{n+1} = evZ(Z_n)`**: `Z_n = ζ_{Γ_{ρ+1}+n}`. -/
noncomputable def gwZn (x : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => lgG x
  | n + 1 => evZ (gwZn x n)

section Zn

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem gwZn_facts : ∀ n : ℕ, InE (gwZn x n) ∧ x < gwZn x n ∧ gwZn x n < gq 1 x
  | 0 => ⟨(lgG_facts hx hx1).2.2.2.1, (lgG_facts hx hx1).2.1, mg_lgG_lt_G1 hx hx1⟩
  | n + 1 => by
    obtain ⟨-, h2, h3⟩ := gwZn_facts n
    exact ⟨evZ_E _, h2.trans (lt_evZ _), gw_evZ_lt1 hx hx1 h3⟩

theorem gwZn_E (n : ℕ) : InE (gwZn x n) := (gwZn_facts hx hx1 n).1

theorem gwZn_gt (n : ℕ) : x < gwZn x n := (gwZn_facts hx hx1 n).2.1

theorem gwZn_lt (n : ℕ) : gwZn x n < gq 1 x := (gwZn_facts hx hx1 n).2.2

end Zn

section ImgZ

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **LEMMA IMG FOR EVERY VALUE BELOW `ζ_{Γ_{ρ+1}+n+1} = evZ(Z_n)`, EVERY `n`.** -/
theorem gwImg_Zn : ∀ (n : ℕ) (v : Ordinal.{0}), v < evZ (gwZn ρ n) → GnI ρ δ v
  | 0 => fun v hv => gnImg_Z h v hv
  | n + 1 => by
    have hρE := h.ρE
    obtain ⟨hPI, hρP, hPq⟩ := gwZn_facts hρE h.ρ1 (n + 1)
    have IHn := gwImg_Zn n
    refine gnImg_of_eps h (fun v hv => gm1_T hρE h.ρ1 (hv.trans (gw_evZ_lt1 hρE h.ρ1 hPq)))
      (fun e he _ heB IHe => ?_)
    rcases lt_trichotomy e (gwZn ρ (n + 1)) with hlt | heq | hgt
    · exact IHn e hlt
    · obtain ⟨hQI, hρQ, hQq⟩ := gwZn_facts hρE h.ρ1 n
      rw [heq]
      exact gwI_fixZ h hQI hρQ hQq IHn
    · exact gwI_epsP h hPI hρP hPq he hgt heB IHe

/-- **LEMMA IMG FOR EVERY VALUE BELOW `ζ_{Γ_{ρ+1}+ω}`.** -/
theorem gwImg_Zw {v : Ordinal.{0}} (hv : ∃ n : ℕ, v < gwZn ρ n) : GnI ρ δ v := by
  obtain ⟨n, hn⟩ := hv
  exact gwImg_Zn h n v (hn.trans (lt_evZ _))

/-- **LEMMA IMG (gated) FOR A SPECIFIED FUNCTION BELOW `ζ_{Γ_{ρ+1}+ω}`**: Lemma EXACT above the gate `g < ρ` with
constants `C < ρ` and `T(ρ) < ζ_{Γ_{ρ+1}+n}` give `T(f ρ) ≤ f(T ρ)` for every covering copy `f` that keeps `g`. -/
theorem gwPkg_of_exZn {g : Ordinal.{0}} {C : Finset Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}} (hgρ : g < ρ)
    (hC : ∀ c ∈ C, c < ρ) (n : ℕ) (hT : T ρ < gwZn ρ n) (hex : GjEx g C T) : GhPkg g ρ δ T :=
  gnPkg_of_GnI h hgρ hC (gwImg_Zw h ⟨n, hT⟩) hex

end ImgZ

end Googology.Trans.PoR.InaccPsi.R2.Gw
