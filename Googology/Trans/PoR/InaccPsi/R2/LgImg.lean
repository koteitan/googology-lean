import Googology.Trans.PoR.InaccPsi.R2.LgTh

/-!
# Lemma IMG for the limit top `Γ(ρ) = lgG ρ = ϑᵖ(Ω₁·Ω₁)`: the IMG package of the top of `lgUSys`

At a restart `ρ` with first block top `δ` (`RstK ρ τ δ`), `G := lgG ρ`, `P := G·G = ω^{G+G}`.  The witness set is
`W = {G, G+G, P, P+G}` with the sources

* `G ≤₁ P` (`lgG_le1R`, through `lowδ`), `G ≤₁ G + G` (`G ∈ E`), and `P ≤₁ P + G` (`P = ω^{G+G}` is not an
  `ε`-number, its `R₁⁺`-reach is `P + logend(G+G) = P + G`, `Lu.lu_lh_opow`).

For a covering copy `f`: `f(G) ∈ E` (`Lu.LuK.luFE`), `f(P) ≥ f(G)·f(G)` (from `f(P) ≤₁ f(P) + f(G)` and the reach of
`ω^d`), so `f(G) ≤₁ f(G)·f(G)` in `R₁⁺`, and by `lg_not_le1R_sq` at the base `f(ρ)`, `f(G) ≥ lgG(f ρ)`.

* `LgK.lgImgP` (`f(P) ≥ f(G)·f(G)`), `LgK.lgTopPkg` (**`ImgPkg ρ δ lgG`**), `lgUSys_topPkg` (**`XtTopPkg lgUSys`**).

Cited axioms: those of `R2.CitedLg` (through `R2.LgTh`).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order Lu

namespace LgK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

theorem lgG_lt_δ : lgG ρ < δ :=
  (lgG_le fun n => (LvGT.lvg_top_lt_next (upsPt_inE h.ρU) h.ρ1 n h.ρτ h.τU.2).le).trans_lt h.τδ

omit h in
/-- `ω^d ≥ g·g` when `ω^d ≤₁ ω^d + g` in `R₁⁺`, `g ∈ E` and `g < ω^d`. -/
theorem lg_sq_le_of_reach {d g : Ordinal.{0}} (hgE : InE g) (hgd : g < ω ^ d)
    (hR : le1R (ω ^ d) (ω ^ d + g)) : g * g ≤ ω ^ d := by
  have hgg : g * g = ω ^ (g + g) := by
    conv_lhs => rw [← show ω ^ g = g from hgE]
    rw [← opow_add]
  have hgd' : g < d := by
    have : ω ^ g < ω ^ d := by rw [show ω ^ g = g from hgE]; exact hgd
    exact (opow_lt_opow_iff_right one_lt_omega0).1 this
  by_cases hdE : InE (ω ^ d)
  · exact (hdE.mul_lt hgd hgd).le
  have hd0 : d ≠ 0 := (lt_of_le_of_lt zero_le hgd').ne'
  have hdlt : d < ω ^ d := lt_of_le_of_ne (right_le_opow _ one_lt_omega0) (fun e => hdE (by
    unfold InE; rw [← e]; exact e.symm))
  have hL := lu_lh_opow hd0 hdlt
  have hglg : g ≤ lg d := (add_le_add_iff_left _).1 (hL.2 _ hR)
  rw [hgg]
  refine (opow_le_opow_iff_right one_lt_omega0).2 ?_
  obtain ⟨d', hds, hdvd, hd'd⟩ := lg_split hd0
  have hgω : g ≤ ω ^ lg d := by
    calc g = ω ^ g := (show ω ^ g = g from hgE).symm
      _ ≤ ω ^ lg d := opow_le_opow_right omega0_pos hglg
  rcases lt_or_ge d' g with hd'g | hgd''
  · -- `d' < g ≤ ω^{lg d}` and `ω^{lg d} ∣ d'`: `d' = 0`, `d = ω^{lg d}` is additive principal above `g`
    have hd'0 : d' = 0 := by
      by_contra hne
      exact absurd (le_of_dvd hne hdvd) (not_le.2 (hd'g.trans_le hgω))
    have hdp : d = ω ^ lg d := by have := hds; rwa [hd'0, zero_add] at this
    have hI : IsPrincipal (· + ·) d := by rw [hdp]; exact isPrincipal_add_omega0_opow _
    exact (hI hgd' hgd').le
  · rw [hds]
    exact add_le_add hgd'' hgω

/-- **The block witness of the top**: `f(G·G) ≥ f(G)·f(G)` and `f(G) ∈ E`. -/
theorem lgImgP {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (C : ImgCtx ρ A f)
    (hGA : lgG ρ ∈ A) (hGGA : lgG ρ + lgG ρ ∈ A) (hPA : lgG ρ * lgG ρ ∈ A)
    (hPGA : lgG ρ * lgG ρ + lgG ρ ∈ A) :
    InE (f (lgG ρ)) ∧ (¬ UpsPt (f (lgG ρ)) → le1R (f (lgG ρ)) (f (lgG ρ) * f (lgG ρ))) := by
  have hρE := upsPt_inE h.ρU
  obtain ⟨-, hρG, -, hGE, -⟩ := lgG_facts hρE h.ρ1
  set G := lgG ρ with hG
  set P := G * G with hP
  have hGδ : G < δ := lgG_lt_δ h
  have hPδ : P < δ := h.δE.mul_lt hGδ hGδ
  have hPGδ : P + G < δ := (inE_indec h.δE).add_lt hPδ hGδ
  have hfE : InE (f G) := LuK.luFE h C hGE hρG.le hGδ hGA hGGA
  refine ⟨hfE, fun hU => ?_⟩
  have hGP : G < P := lt_mul_of_one_lt_right hGE.pos (lu_one_lt_E hGE)
  -- `G ≤₁ P`
  have hsrc1 : le1 G P := (h.lowδ _ _ hρG hPδ.le).2 (lgG_le1R hρE h.ρ1)
  have hR1 : le1R (f G) (f P) := (C.sk _ (C.low _ hGA) hU _).1 (C.cov1 G hGA P hPA hsrc1)
  have hfGP : f G < f P := C.mono hGA hPA hGP
  -- `f(P) ≥ f(G)·f(G)`
  have hPge : f G * f G ≤ f P := by
    by_cases hUP : UpsPt (f P)
    · exact ((upsPt_inE hUP).mul_lt hfGP hfGP).le
    -- `P ≤₁ P + G`
    have hPe : P = ω ^ (G + G) := by
      rw [hP]; conv_lhs => rw [← show ω ^ G = G from hGE]
      rw [← opow_add]
    have hc0 : G + G ≠ 0 := (lt_of_lt_of_le hGE.pos le_self_add).ne'
    have hclt : G + G < ω ^ (G + G) := by
      rw [← hPe, hP, ← mul_two_eq G]
      have h2ω : (2 : Ordinal.{0}) < ω := by simpa using natCast_lt_omega0 2
      exact (mul_lt_mul_iff_right₀ hGE.pos).2 (h2ω.trans_le (lu_omega_lt_E hGE).le)
    have hGlg : G ≤ lg (G + G) := le_lg hc0 ⟨2, by rw [show ω ^ G = G from hGE]; exact (mul_two_eq G).symm⟩
    have hLP := lu_lh_opow hc0 hclt
    have hsrcR : le1R P (P + G) := by
      rw [hPe]
      exact le1R_of_le le_self_add ((add_le_add_iff_left _).2 hGlg) hLP.1
    have hρP : ρ < P := hρG.trans hGP
    have hsrc2 : le1 P (P + G) := (h.lowδ _ _ hρP hPGδ.le).2 hsrcR
    have himg : le1 (f P) (f P + f G) := by
      have := C.cov1 P hPA _ hPGA hsrc2
      rwa [← C.add P hPA G hGA _ hPGA rfl] at this
    have hR2 := (C.sk _ (C.low _ hPA) hUP _).1 himg
    obtain ⟨d, hd⟩ := indec_eq_opow (C.indec P hPA (by rw [hPe]; exact indec_opow _))
    rw [hd] at hR2 hfGP ⊢
    exact lg_sq_le_of_reach hfE hfGP hR2
  exact le1R_of_le (le_mul_left _ hfE.pos) hPge hR1

/-- **The IMG package of the limit top**: `ImgPkg ρ δ lgG`. -/
theorem lgTopPkg : ImgPkg ρ δ lgG := by
  classical
  have hρE := upsPt_inE h.ρU
  obtain ⟨-, hρG, -, hGE, hGI⟩ := lgG_facts hρE h.ρ1
  set G := lgG ρ with hG
  set P := G * G with hP
  have hGδ : G < δ := lgG_lt_δ h
  have hPδ : P < δ := h.δE.mul_lt hGδ hGδ
  have hGGδ : G + G < δ := (inE_indec h.δE).add_lt hGδ hGδ
  have hPGδ : P + G < δ := (inE_indec h.δE).add_lt hPδ hGδ
  have hG0 : 0 < G := hGE.pos
  have hGP : G < P := lt_mul_of_one_lt_right hG0 (lu_one_lt_E hGE)
  have hPe : P = ω ^ (G + G) := by
    rw [hP]; conv_lhs => rw [← show ω ^ G = G from hGE]
    rw [← opow_add]
  have w1 : WZ ρ δ {G} ∅ := by
    have := (WZ.empty (ρ := ρ) (δ := δ)).insW hρG.le hGδ (Or.inl hGI)
    simpa using this
  have w2 : WZ ρ δ {G + G, G} ∅ := by
    have := w1.insW (hρG.le.trans le_self_add) hGGδ
      (Or.inr ⟨G, by simp, G, by simp, lt_add_of_pos_right _ hG0, lt_add_of_pos_right _ hG0, rfl⟩)
    simpa using this
  have w3 : WZ ρ δ {P, G + G, G} ∅ := by
    have := w2.insW (hρG.le.trans hGP.le) hPδ (Or.inl (by rw [hPe]; exact indec_opow _))
    simpa using this
  have w4 : WZ ρ δ {P + G, P, G + G, G} ∅ := by
    have := w3.insW ((hρG.le.trans hGP.le).trans le_self_add) hPGδ
      (Or.inr ⟨P, by simp, G, by simp, lt_add_of_pos_right _ hG0, hGP.trans_le le_self_add, rfl⟩)
    simpa using this
  refine ⟨one_le_iff_pos.2 hG0, hGδ, {P + G, P, G + G, G}, ∅, w4, by rw [← hG]; simp, ?_⟩
  intro A f hW _ C
  have hGA : G ∈ A := hW (by simp)
  have hGGA : G + G ∈ A := hW (by simp)
  have hPA : P ∈ A := hW (by simp)
  have hPGA : P + G ∈ A := hW (by simp)
  obtain ⟨hyE, hy1, -⟩ := h.vz_img_base C
  have hyG : f ρ < f G := C.mono C.rho hGA hρG
  obtain ⟨hfE, hsq⟩ := lgImgP h C hGA hGGA hPA hPGA
  by_cases hU : UpsPt (f G)
  · exact lgG_le fun n => (LvGT.lvg_top_lt_next hyE hy1 n hyG hU.2).le
  · by_contra hlt
    push Not at hlt
    exact lg_not_le1R_sq hyE hy1 hfE hyG hlt (hsq hU)

end LgK

/-- **The top `lgG` of `lgUSys` has an IMG package.** -/
theorem lgUSys_topPkg : Xt.XtTopPkg lgUSys := fun _ _ _ R => LgK.lgTopPkg R

end Googology.Trans.PoR.InaccPsi.R2
