import Googology.Trans.PoR.InaccPsi.R2.GcLim

/-!
# The diagonal top `Γ_{x+x} = ϑˣ(Ω₁·Ω₁ + x)`: its reach, its decomposition, EXACT and its top witness

The first term-indexed base: the offset is the base `x` itself (not a constant).  Here everything about the top
`D(x) = ϑˣ(Ω₁·Ω₁ + x)` that a layer with this top needs, proved once:

* `gcq_facts` (`ϑˣ(Ω₁·Ω₁ + η)` for every `η ≤ x`, not only constants), `gcq_lt_next`, `gc_lg_eps` (`logend(x) = x`);
* `gcD_lh` (**`lh(D) = D·D + D + x`** in `R₁⁺`, from `Lq.lq_lh_sq` at `η = x`, `ζ = logend(x) = x`), `gcD_lt_iff`
  (**`v < D(x)` iff `v < ϑˣ(Ω₁·Ω₁ + ν)` for some `ν < x`**), `gc_not_le1R_diag` (**no `ε`-number `a ∈ (x, D(x))` has
  `a ≤₁ a·a + a + x`**: there `lh(a) = a·a + a + logend(ν)` with `logend(ν) ≤ ν < x`);
* `gcD_pi` (**EXACT: `π_{σ,ρ}(D(ρ)) = D(σ)`**, from `pi_base`), `GcDK.gcDiagWit` (**THE TOP WITNESS of `Γ_{x+x}`**:
  `f(D(ρ)) ∈ E` and `D(fρ) ≤ f(D(ρ))`, from the copy of `D ≤₁ D·D + D + ρ`; no layer below is needed).

No new axiom.  New definition: none.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Lp Lu
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gb

/-- **`logend(x) = x`** for an `ε`-number `x`. -/
theorem gc_lg_eps {x : Ordinal.{0}} (hx : InE x) : lg x = x :=
  le_antisymm (lg_le hx.pos.ne') (le_lg hx.pos.ne' (by rw [show ω ^ x = x from hx]))

section D

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- The facts on `ϑˣ(Ω₁·Ω₁ + η)` for every `η ≤ x`. -/
theorem gcq_facts {η : Ordinal.{0}} (hηx : η ≤ x) :
    gq η x ∈ Tset x ∧ x < gq η x ∧ gq η x < Om1 ∧ InE (gq η x) ∧ Indec (gq η x) := by
  have hT : η ∈ Tset x := mem_T_of_le hx hx1 hηx
  have h1 : η < Om1 := hηx.trans_lt hx1
  have hA : Om1 * Om1 + η ∈ Tset x := lgArg_mem hx hx1 hT h1
  have h2 : Om1 * Om1 + η < OmTwo := lg_OmOm_lt h1
  obtain ⟨hvT, -, hv1, hvP, -⟩ := vt_memTwo hx hx1 hA h2
  have hE := (vt_E_iff hx hx1 hA h2).2 (lg_Om1_le_OmOm.trans le_self_add)
  exact ⟨hvT, hE.1, hv1, hE.2, hvP⟩

theorem gcq_lt_next {η : Ordinal.{0}} (hηx : η ≤ x) {u : Ordinal.{0}} (hxu : x < u) (hu : LtInf1 u) :
    gq η x < u := by
  obtain ⟨m, -, -, hmin, hTm, -⟩ := T_next (Or.inr hx) hx1
  obtain ⟨hT, -, h1, -, -⟩ := gcq_facts hx hx1 hηx
  exact ((hTm _ h1).1 hT).trans_le (hmin u hxu hu)

/-- **`lh(Γ_{x+x}) = D·D + D + x`** in `R₁⁺` (`D = ϑˣ(Ω₁·Ω₁ + x)`). -/
theorem gcD_lh : IsLh1 (gq x x) (gq x x * gq x x + gq x x + x) := by
  have hT : x ∈ Tset x := mem_T_of_le hx hx1 le_rfl
  have h := (Lq.lq_lh_sq hx hx1 hT hx1).1
  have hz : lqZeta x (Om1 * Om1) x = x := by
    unfold lqZeta
    rw [if_pos ⟨0, hx.pos, (gcq_facts hx hx1 hx.pos.le).2.1⟩, gc_lg_eps hx]
  rw [hz] at h
  exact h

/-- **`v < Γ_{x+x}` iff `v < ϑˣ(Ω₁·Ω₁ + ν)` for some `ν < x`.** -/
theorem gcD_lt_iff : ∀ v, v < gq x x → ∃ ν < x, v < gq ν x := by
  obtain ⟨hGT, -, hG1, -, -⟩ := gcq_facts hx hx1 le_rfl
  have hxT : x ∈ Tset x := mem_T_of_le hx hx1 le_rfl
  have hxl : IsSuccLimit x := by
    have h := Ph.ph_opow_lim hx.pos.ne'
    rwa [show ω ^ x = x from hx] at h
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  rcases le_or_gt v x with hvx | hxv
  · exact ⟨0, hx.pos, hvx.trans_lt (gq_facts hx hx1 hx.pos).2.1⟩
  have hv1 : v < Om1 := hv.trans hG1
  have hvT : v ∈ Tset x := vz_T_down hx hx1 hGT hG1 hv.le
  by_cases hI : Indec v
  · by_cases hvE' : InE v
    · obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 hvT hxv.le hv1 hI
      have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxv, by rw [hξv]; exact hvE'⟩
      have hξk : ξ < Om1 * Om1 + x :=
        lgLt_of_vt_lt hx hx1 hξT hξ2 hxT hx1 (by rw [hξv]; exact hxv) (by rw [hξv]; exact hv)
      rcases lt_or_ge ξ (Om1 * Om1) with hξs | hξs
      · obtain ⟨hq1, hrT, hr1, hdec⟩ := lu_split hx hx1 hξT hξ2 hΩξ
        have hqT : ξ / Om1 ∈ Tset x := lgQuot_mem hx hx1 hξT hξs
        have hqΩ : ξ / Om1 < Om1 := (Ordinal.lt_mul_iff_div_lt (Ordinal.omega_pos 1).ne').1 hξs
        have hqr : ξ / Om1 < v ∧ ξ % Om1 < v := by
          rcases lt_or_ge (ξ / Om1) x with hqx | hxq
          · have h := luLt_vt_self hx hx1 hq1 hqx hrT hr1
            rw [hdec, hξv] at h
            exact ⟨hqx.trans hxv, h⟩
          · have h := lvLevel_lt_vt hx hx1 hqT hxq hqΩ hrT hr1
            rw [hdec, hξv] at h
            exact h
        obtain ⟨n1, hn1l, hn1⟩ := IH _ hqr.1 (hqr.1.trans hv)
        obtain ⟨n2, hn2l, hn2⟩ := IH _ hqr.2 (hqr.2.trans hv)
        have hml : max n1 n2 < x := max_lt hn1l hn2l
        refine ⟨max n1 n2, hml, ?_⟩
        have hq' : ξ / Om1 < gq (max n1 n2) x := hn1.trans_le (gq_mono hx hx1 hml (le_max_left _ _))
        have hr' : ξ % Om1 < gq (max n1 n2) x := hn2.trans_le (gq_mono hx hx1 hml (le_max_right _ _))
        obtain ⟨hmT, hm1⟩ := gq_cst hx hx1 hml
        have h := lgVt_lt_low hx hx1 hqT hqΩ hrT hr1 hmT hm1 hq' hr'
        rw [hdec, hξv] at h
        exact h
      · have hje : Om1 * Om1 + (ξ - Om1 * Om1) = ξ := Ordinal.add_sub_cancel_of_le hξs
        obtain ⟨j, hj⟩ : ∃ j, ξ - Om1 * Om1 = j := ⟨_, rfl⟩
        rw [hj] at hje
        have hjk : j < x := (add_lt_add_iff_left _).1 (by rw [hje]; exact hξk)
        refine ⟨j + 1, hxl.add_one_lt hjk, ?_⟩
        have hvj : v = gq j x := by rw [← hξv, ← hje]; rfl
        rw [hvj]
        exact gq_lt hx hx1 (hxl.add_one_lt hjk) (lt_add_one _)
    · obtain ⟨L, rfl⟩ := indec_eq_opow hI
      have hL : L < ω ^ L := lt_of_le_of_ne (right_le_opow _ one_lt_omega0)
        (fun h => hvE' (by unfold InE; rw [← h]; exact h.symm))
      obtain ⟨n, hnl, hn⟩ := IH L hL (hL.trans hv)
      exact ⟨n, hnl, (gq_facts hx hx1 hnl).2.2.2.1.opow_lt hn⟩
  · have hD : DecompR0 v := not_not.1 hI
    rcases hD with h0 | ⟨u1, u2, hu1, hu2, hsum⟩
    · exact absurd h0 (lt_of_le_of_lt zero_le hxv).ne'
    obtain ⟨n1, hn1l, h1⟩ := IH u1 hu1 (hu1.trans hv)
    obtain ⟨n2, hn2l, h2⟩ := IH u2 hu2 (hu2.trans hv)
    have hml : max n1 n2 < x := max_lt hn1l hn2l
    refine ⟨max n1 n2, hml, ?_⟩
    rw [← hsum]
    exact (inE_indec (gq_facts hx hx1 hml).2.2.2.1).add_lt
      (h1.trans_le (gq_mono hx hx1 hml (le_max_left _ _)))
      (h2.trans_le (gq_mono hx hx1 hml (le_max_right _ _)))

/-- **No `ε`-number `a ∈ (x, Γ_{x+x})` has `a ≤₁ a·a + a + x` in `R₁⁺`.** -/
theorem gc_not_le1R_diag {a : Ordinal.{0}} (haE : InE a) (hxa : x < a) (h2 : a < gq x x) :
    ¬ le1R a (a * a + a + x) := by
  intro hR
  obtain ⟨hGT, -, hG1, -, -⟩ := gcq_facts hx hx1 le_rfl
  have hxT : x ∈ Tset x := mem_T_of_le hx hx1 le_rfl
  have ha1 : a < Om1 := h2.trans hG1
  have haT : a ∈ Tset x := vz_T_down hx hx1 hGT hG1 h2.le
  obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 haT hxa.le ha1 (inE_indec haE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxa, by rw [hξv]; exact haE⟩
  have hξk : ξ < Om1 * Om1 + x :=
    lgLt_of_vt_lt hx hx1 hξT hξ2 hxT hx1 (by rw [hξv]; exact hxa) (by rw [hξv]; exact h2)
  have haa : a * a ≤ a * a + a + x := le_self_add.trans le_self_add
  rcases lt_or_ge ξ (Om1 * Om1) with hξs | hξs
  · obtain ⟨hq1, hrT, hr1, hdec'⟩ := lu_split hx hx1 hξT hξ2 hΩξ
    have hqT : ξ / Om1 ∈ Tset x := lgQuot_mem hx hx1 hξT hξs
    have hqΩ : ξ / Om1 < Om1 := (Ordinal.lt_mul_iff_div_lt (Ordinal.omega_pos 1).ne').1 hξs
    set q := ξ / Om1 with hq
    set r := ξ % Om1 with hr
    have hv : vt x (Om1 * q + r) = a := by rw [hdec', hξv]
    have hζr : luZeta x q r < a := by
      refine lu_zeta_le.trans_lt ?_
      rcases lt_or_ge q x with hqx | hxq
      · have := (lu_th_facts hx hx1 hq1 hqx hrT hr1).2.2.2.2.2.2.2
        rwa [hv] at this
      · have := (Lv.gen_facts hx hx1 hqT hxq hqΩ hrT hr1).2.2.2.2.2.2.2.2
        rwa [hv] at this
    have hL : IsLh1 a (luL a q + luZeta x q r) ∧ q < a := by
      rcases lt_or_ge q x with hqx | hxq
      · have h := lu_lh_th hx hx1 hq1 hqx hrT hr1
        rw [hv] at h
        exact ⟨h, hqx.trans hxa⟩
      · have h := Lv.lv_lh_gen hx hx1 hqT hxq hqΩ hrT hr1
        have hqv := (Lv.gen_facts hx hx1 hqT hxq hqΩ hrT hr1).2.2.2.2.2.2.2.1
        rw [hv] at h hqv
        exact ⟨h, hqv⟩
    have hle := hL.1.2 _ hR
    exact absurd ((haa.trans hle).trans_lt (lg_luL_lt_sq haE hL.2 hζr)) (lt_irrefl _)
  · have hje : Om1 * Om1 + (ξ - Om1 * Om1) = ξ := Ordinal.add_sub_cancel_of_le hξs
    obtain ⟨ν, hν⟩ : ∃ ν, ξ - Om1 * Om1 = ν := ⟨_, rfl⟩
    rw [hν] at hje
    have hνx : ν < x := (add_lt_add_iff_left _).1 (by rw [hje]; exact hξk)
    have hva : a = gq ν x := by rw [← hξv, ← hje]; rfl
    rcases eq_or_ne ν 0 with rfl | hν0
    · obtain ⟨h0T, h01⟩ := gq_cst hx hx1 hx.pos
      have hL := (Lq.lq_lh_sq hx hx1 h0T h01).1
      have hz : lqZeta x (Om1 * Om1) 0 = 0 := by
        unfold lqZeta
        rw [if_neg]
        rintro ⟨σ, hσ, -⟩
        exact absurd hσ (not_lt.2 zero_le)
      have hva' : a = vt x (Om1 * Om1 + 0) := hva
      rw [hz, ← hva'] at hL
      have hle := (add_le_add_iff_left (a * a + a)).1 (hL.2 _ hR)
      exact absurd hle (not_le.2 hx.pos)
    · have hL := gc_lh hx hx1 hνx (pos_iff_ne_zero.2 hν0)
      rw [← hva] at hL
      have hle := (add_le_add_iff_left (a * a + a)).1 (hL.2 _ hR)
      exact absurd hle (not_le.2 ((lg_le hν0).trans_lt hνx))

end D

/-- **EXACT for the diagonal top**: `π_{σ,ρ}(ϑ^ρ(Ω₁·Ω₁ + ρ)) = ϑ^σ(Ω₁·Ω₁ + σ)`. -/
theorem gcD_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) : gq ρ ρ ∈ TB ρ σ ∧ pi σ ρ (gq ρ ρ) = gq σ σ := by
  obtain ⟨hσE, hρE, hσρ, hρ1⟩ := hB
  have hB' : Bases σ ρ := ⟨hσE, hρE, hσρ, hρ1⟩
  obtain ⟨hTB0, hpi0⟩ := lgPi_OmOm hB'
  obtain ⟨hTBs, hpis⟩ := pi_add hB' hTB0 (pi_base hB').1
  rw [hpi0, (pi_base hB').2] at hpis
  have h2 : Om1 * Om1 + ρ < OmTwo := lg_OmOm_lt hρ1
  obtain ⟨hvT, -, -, -, hPar⟩ := vt_memTwo hρE hρ1 hTBs.1 h2
  refine ⟨⟨hvT, ?_⟩, ?_⟩
  · show ↑(Par ρ (vt ρ (Om1 * Om1 + ρ))) ⊆ Set.Iio σ
    rw [hPar]; exact hTBs.2
  · show pi σ ρ (vt ρ (Om1 * Om1 + ρ)) = vt σ (Om1 * Om1 + σ)
    rw [pi_vt_two hB' hTBs h2, hpis]

namespace GcDK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **THE TOP WITNESS of `Γ_{x+x}`**: `f(D(ρ)) ∈ E` and `D(fρ) ≤ f(D(ρ))` (`D(x) = ϑˣ(Ω₁·Ω₁ + x)`), from the copy
`f(D) ≤₁ f(D)·f(D) + f(D) + fρ` of `D ≤₁ D·D + D + ρ` (`gcD_lh`) and `gc_not_le1R_diag`. -/
theorem gcDiagWit : ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ gq ρ ρ ∈ W ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      (∃ e', f (gq ρ ρ) = ω ^ e' ∧ ω ^ f ρ ∣ e') ∧ gq (f ρ) (f ρ) ≤ f (gq ρ ρ) := by
  classical
  have hρE := upsPt_inE h.ρU
  obtain ⟨-, hρG, -, hGE, hGI⟩ := gcq_facts hρE h.ρ1 le_rfl
  have hLG := gcD_lh hρE h.ρ1
  set G := gq ρ ρ with hG
  have hGδ : G < δ := (gcq_lt_next hρE h.ρ1 le_rfl h.ρτ h.τU.2).trans h.τδ
  have hρδ : ρ < δ := hρG.trans hGδ
  have hPδ : G * G < δ := h.δE.mul_lt hGδ hGδ
  have hGGδ : G + G < δ := (inE_indec h.δE).add_lt hGδ hGδ
  have hPGδ : G * G + G < δ := (inE_indec h.δE).add_lt hPδ hGδ
  have hPGρδ : G * G + G + ρ < δ := (inE_indec h.δE).add_lt hPGδ hρδ
  have hG0 : 0 < G := hGE.pos
  have hGP : G < G * G := lt_mul_of_one_lt_right hG0 (lu_one_lt_E hGE)
  have hPe : G * G = ω ^ (G + G) := by
    conv_lhs => rw [← show ω ^ G = G from hGE]
    rw [← opow_add]
  have hρPG : ρ ≤ G * G + G := (hρG.le.trans hGP.le).trans le_self_add
  have w0 : WZ ρ δ {ρ} ∅ := by
    have := (WZ.empty (ρ := ρ) (δ := δ)).insW le_rfl hρδ (Or.inl (inE_indec hρE))
    simpa using this
  have w1 : WZ ρ δ {G, ρ} ∅ := by
    have := w0.insW hρG.le hGδ (Or.inl hGI)
    simpa using this
  have w2 : WZ ρ δ {G + G, G, ρ} ∅ := by
    have := w1.insW (hρG.le.trans le_self_add) hGGδ
      (Or.inr ⟨G, by simp, G, by simp, lt_add_of_pos_right _ hG0, lt_add_of_pos_right _ hG0, rfl⟩)
    simpa using this
  have w3 : WZ ρ δ {G * G, G + G, G, ρ} ∅ := by
    have := w2.insW (hρG.le.trans hGP.le) hPδ (Or.inl (by rw [hPe]; exact indec_opow _))
    simpa using this
  have w4 : WZ ρ δ {G * G + G, G * G, G + G, G, ρ} ∅ := by
    have := w3.insW hρPG hPGδ
      (Or.inr ⟨G * G, by simp, G, by simp, lt_add_of_pos_right _ hG0, hGP.trans_le le_self_add, rfl⟩)
    simpa using this
  have w5 : WZ ρ δ {G * G + G + ρ, G * G + G, G * G, G + G, G, ρ} ∅ := by
    have := w4.insW (hρPG.trans le_self_add) hPGρδ
      (Or.inr ⟨G * G + G, by simp, ρ, by simp, lt_add_of_pos_right _ hρE.pos,
        hρPG.trans_lt (lt_add_of_pos_right _ hρE.pos), rfl⟩)
    simpa using this
  refine ⟨{G * G + G + ρ, G * G + G, G * G, G + G, G, ρ}, ∅, w5, by simp, fun A f hW _ C => ?_⟩
  have hGA : G ∈ A := hW (by simp)
  have hGGA : G + G ∈ A := hW (by simp)
  have hPA : G * G ∈ A := hW (by simp)
  have hPGA : G * G + G ∈ A := hW (by simp)
  have hPGρA : G * G + G + ρ ∈ A := hW (by simp)
  obtain ⟨hfE, hPge⟩ := GbK.gbImg h hGE hρG hGδ C hGA hGGA hPA hPGA
  have hyG : f ρ < f G := C.mono C.rho hGA hρG
  refine ⟨⟨f G, hfE.symm, opow_dvd_of_inE hfE hyG.le⟩, ?_⟩
  obtain ⟨hyE, hy1, -⟩ := h.vz_img_base C
  by_cases hU : UpsPt (f G)
  · exact (gcq_lt_next hyE hy1 le_rfl hyG hU.2).le
  · by_contra hlt
    push Not at hlt
    have hsrc : le1 G (G * G + G + ρ) := (h.lowδ _ _ hρG hPGρδ.le).2 hLG.1
    have himg := C.cov1 G hGA _ hPGρA hsrc
    have hR := (C.sk _ (C.low _ hGA) hU _).1 himg
    have hadd1 : f (G * G + G) + f ρ = f (G * G + G + ρ) := C.add (G * G + G) hPGA ρ C.rho _ hPGρA rfl
    have hadd2 : f (G * G) + f G = f (G * G + G) := C.add (G * G) hPA G hGA _ hPGA rfl
    have hle : f G * f G + f G + f ρ ≤ f (G * G + G + ρ) := by
      rw [← hadd1, ← hadd2]
      exact add_le_add_left (add_le_add_left hPge _) _
    have hlo : f G ≤ f G * f G + f G + f ρ :=
      ((le_mul_left _ hfE.pos).trans le_self_add).trans le_self_add
    exact gc_not_le1R_diag hyE hy1 hfE hyG hlt (le1R_of_le hlo hle hR)

end GcDK

end Googology.Trans.PoR.InaccPsi.R2.Gc
