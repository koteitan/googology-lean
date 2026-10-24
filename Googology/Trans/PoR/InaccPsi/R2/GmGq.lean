import Googology.Trans.PoR.InaccPsi.R2.GmSup

/-!
# OFFSETS UP TO `Γ_{x+2}`: the four facts of the layer construction for every offset `η < ϑˣ(Ω₁·Ω₁ + 1)`

The term-offset step (`Ge.geqLimB`) and the union step (`Gh.ghLimB`) use the bound `η < Γ_{x+1}` only through four
facts about `G(η) = ϑˣ(Ω₁·Ω₁ + η)` (`R2.GfGam`).  Here they hold for every offset `η < Γ_{x+2} = G(1)`, which covers
the readings of the codes `Γ_{Ω₁+1}·k + c` (the code `Γ_{Ω₁+1}` reads `Γ_{x+1}`):

* `gmq_gt` (**`η < G(η)` for every `η ∈ Tˣ ∩ Ω₁`**, [W07a] Lemma 3.30 through `lqLevel_lt_vt`), `gmq_lt` / `gmq_mono`
  (**`η ↦ G(η)` is strictly increasing on all of `Tˣ ∩ Ω₁`**);
* `gm1_facts`, `gm1_T` (**`η < Γ_{x+2}` lies in `Tˣ ∩ Ω₁`**), `gm1_lt`, `gm1_mono`, `gm1_sigma` (**some `σ < η` has
  `η < G(σ)`**: `0` below `Γ_{x+1}`, `1` above), `gm1_lh` (**`lh(G(η)) = G·G + G + logend(η)` for `0 < η < Γ_{x+2}`**);
* `gm1_lt_lim_iff` (**`v < G(λ)` iff `v < G(ν)` for some `ν < λ`**, every limit `λ < Γ_{x+2}`) and
  `gm1_not_le1R_lim` (no `ε`-number in `(G(λ'), G(λ))` is `≤₁ a·a + a + logend(λ)` in `R₁⁺`; above `G(0)` an
  `ε`-number `a = ϑˣ(ξ)` with `ξ ≥ Ω₁·Ω₁` is at least `G(1) > λ`).

No new axiom.  New definitions: none.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gm

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf

section GQ1

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **`η < ϑˣ(Ω₁·Ω₁ + η)`** for every `η ∈ Tˣ ∩ Ω₁`. -/
theorem gmq_gt {η : Ordinal.{0}} (hT : η ∈ Tset x) (h1 : η < Om1) : η < gq η x := by
  have h1T : (1 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 (lu_one_lt_E hx).le
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  have h1Ω : (1 : Ordinal.{0}) < Om1 := (lu_one_lt_E hx).trans hx1
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
  have h := (lqLevel_lt_vt hx hx1 le_rfl h1T h1Ω h0T h0Ω hT h1).2.2
  rw [mul_one, add_zero] at h
  exact h

/-- **`η ↦ ϑˣ(Ω₁·Ω₁ + η)` is strictly increasing on `Tˣ ∩ Ω₁`.** -/
theorem gmq_lt {j η : Ordinal.{0}} (hT : η ∈ Tset x) (h1 : η < Om1) (h : j < η) : gq j x < gq η x :=
  geq_lt_of hx hx1 (vz_T_down hx hx1 hT h1 h.le) (h.trans h1) hT h1 h (h.trans (gmq_gt hx hx1 hT h1))

theorem gmq_mono {j η : Ordinal.{0}} (hT : η ∈ Tset x) (h1 : η < Om1) (h : j ≤ η) : gq j x ≤ gq η x := by
  rcases h.lt_or_eq with h | rfl
  · exact (gmq_lt hx hx1 hT h1 h).le
  · exact le_rfl

theorem gm1_one_T : (1 : Ordinal.{0}) ∈ Tset x ∧ (1 : Ordinal.{0}) < Om1 :=
  ⟨mem_T_of_le hx hx1 (lu_one_lt_E hx).le, (lu_one_lt_E hx).trans hx1⟩

theorem gm1_facts : gq 1 x ∈ Tset x ∧ x < gq 1 x ∧ gq 1 x < Om1 ∧ InE (gq 1 x) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := geq_facts hx hx1 (gm1_one_T hx hx1).1 (gm1_one_T hx hx1).2
  exact ⟨h1, h2, h3, h4⟩

/-- **Every offset below `Γ_{x+2}` lies in `Tˣ ∩ Ω₁`.** -/
theorem gm1_T {η : Ordinal.{0}} (h : η < gq 1 x) : η ∈ Tset x ∧ η < Om1 := by
  obtain ⟨h1, -, h3, -⟩ := gm1_facts hx hx1
  exact ⟨vz_T_down hx hx1 h1 h3 h.le, h.trans h3⟩

theorem gm1_lt {j η : Ordinal.{0}} (hη : η < gq 1 x) (h : j < η) : gq j x < gq η x :=
  gmq_lt hx hx1 (gm1_T hx hx1 hη).1 (gm1_T hx hx1 hη).2 h

theorem gm1_mono {j η : Ordinal.{0}} (hη : η < gq 1 x) (h : j ≤ η) : gq j x ≤ gq η x :=
  gmq_mono hx hx1 (gm1_T hx hx1 hη).1 (gm1_T hx hx1 hη).2 h

theorem gm_G0_lt_G1 : gq 0 x < gq 1 x :=
  gmq_lt hx hx1 (gm1_one_T hx hx1).1 (gm1_one_T hx hx1).2 zero_lt_one

/-- **Some `σ < η` has `η < ϑˣ(Ω₁·Ω₁ + σ)`** for `0 < η < Γ_{x+2}`. -/
theorem gm1_sigma {η : Ordinal.{0}} (h : η < gq 1 x) (h0 : 0 < η) : ∃ σ, σ < η ∧ η < gq σ x := by
  rcases lt_or_ge η (gq 0 x) with h' | h'
  · exact ⟨0, h0, h'⟩
  · have h1G : (1 : Ordinal.{0}) < gq 0 x := (lu_one_lt_E hx).trans (gfq0_facts hx hx1).2.1
    exact ⟨1, h1G.trans_le h', h⟩

/-- **`lh(ϑˣ(Ω₁·Ω₁ + η)) = G·G + G + logend(η)`** for `0 < η < Γ_{x+2}`. -/
theorem gm1_lh {η : Ordinal.{0}} (hη : η < gq 1 x) (h0 : 0 < η) :
    IsLh1 (gq η x) (gq η x * gq η x + gq η x + lg η) :=
  (gfq_lh_gen hx hx1 (gm1_T hx hx1 hη).1 (gm1_T hx hx1 hη).2).1 (gm1_sigma hx hx1 hη h0)

/-- **`ε_{x+1} < ϑˣ(Ω₁·Ω₁ + η)`** for every `η ∈ Tˣ ∩ Ω₁`. -/
theorem gmq_eN_lt {η : Ordinal.{0}} (hT : η ∈ Tset x) (h1 : η < Om1) : eN x < gq η x :=
  (Gh.gh_eN_lt_gq0 hx hx1).trans_le (gfq0_le hx hx1 hT h1)

/-- **`v < ϑˣ(Ω₁·Ω₁ + λ)` iff `v < ϑˣ(Ω₁·Ω₁ + ν)` for some `ν < λ`** (`λ` a limit below `Γ_{x+2}`). -/
theorem gm1_lt_lim_iff {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlG : l < gq 1 x) :
    ∀ v, v < gq l x → ∃ ν < l, v < gq ν x := by
  obtain ⟨hlT, hl1⟩ := gm1_T hx hx1 hlG
  obtain ⟨hGT, -, hG1, -, -⟩ := geq_facts hx hx1 hlT hl1
  have h0T := mem_T_of_le hx hx1 (zero_le : (0 : Ordinal.{0}) ≤ x)
  have h01 : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
  have hG0 : l < gq 1 x := hlG
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  rcases le_or_gt v (max x l) with hvx | hxv0
  · have h1l : (1 : Ordinal.{0}) < l := by simpa using hl.add_one_lt hl.bot_lt
    exact ⟨1, h1l, hvx.trans_lt (max_lt (gm1_facts hx hx1).2.1 hG0)⟩
  have hxv : x < v := (le_max_left _ _).trans_lt hxv0
  have hlv : l < v := (le_max_right _ _).trans_lt hxv0
  have hv1 : v < Om1 := hv.trans hG1
  have hvT : v ∈ Tset x := vz_T_down hx hx1 hGT hG1 hv.le
  by_cases hI : Indec v
  · by_cases hvE' : InE v
    · obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 hvT hxv.le hv1 hI
      have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxv, by rw [hξv]; exact hvE'⟩
      have hξk : ξ < Om1 * Om1 + l :=
        lgLt_of_vt_lt hx hx1 hξT hξ2 hlT hl1 (by rw [hξv]; exact hlv) (by rw [hξv]; exact hv)
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
        have hml : max n1 n2 < l := max_lt hn1l hn2l
        refine ⟨max n1 n2, hml, ?_⟩
        have hq' : ξ / Om1 < gq (max n1 n2) x := hn1.trans_le (gm1_mono hx hx1 (hml.trans hlG) (le_max_left _ _))
        have hr' : ξ % Om1 < gq (max n1 n2) x := hn2.trans_le (gm1_mono hx hx1 (hml.trans hlG) (le_max_right _ _))
        obtain ⟨hmT, hm1⟩ := gm1_T hx hx1 (hml.trans hlG)
        have h := lgVt_lt_low hx hx1 hqT hqΩ hrT hr1 hmT hm1 hq' hr'
        rw [hdec, hξv] at h
        exact h
      · have hje : Om1 * Om1 + (ξ - Om1 * Om1) = ξ := Ordinal.add_sub_cancel_of_le hξs
        obtain ⟨j, hj⟩ : ∃ j, ξ - Om1 * Om1 = j := ⟨_, rfl⟩
        rw [hj] at hje
        have hjk : j < l := (add_lt_add_iff_left _).1 (by rw [hje]; exact hξk)
        refine ⟨j + 1, hl.add_one_lt hjk, ?_⟩
        have hvj : v = gq j x := by rw [← hξv, ← hje]; rfl
        rw [hvj]
        exact gm1_lt hx hx1 ((hl.add_one_lt hjk).trans hlG) (lt_add_one _)
    · obtain ⟨L, rfl⟩ := indec_eq_opow hI
      have hL : L < ω ^ L := lt_of_le_of_ne (right_le_opow _ one_lt_omega0)
        (fun h => hvE' (by unfold InE; rw [← h]; exact h.symm))
      obtain ⟨n, hnl, hn⟩ := IH L hL (hL.trans hv)
      exact ⟨n, hnl, (geq_facts hx hx1 (gm1_T hx hx1 (hnl.trans hlG)).1 (gm1_T hx hx1
          (hnl.trans hlG)).2).2.2.2.1.opow_lt hn⟩
  · have hD : DecompR0 v := not_not.1 hI
    rcases hD with h0 | ⟨u1, u2, hu1, hu2, hsum⟩
    · exact absurd h0 (lt_of_le_of_lt zero_le hxv).ne'
    obtain ⟨n1, hn1l, h1⟩ := IH u1 hu1 (hu1.trans hv)
    obtain ⟨n2, hn2l, h2⟩ := IH u2 hu2 (hu2.trans hv)
    have hml : max n1 n2 < l := max_lt hn1l hn2l
    refine ⟨max n1 n2, hml, ?_⟩
    rw [← hsum]
    exact (inE_indec (geq_facts hx hx1 (gm1_T hx hx1 (hml.trans hlG)).1
      (gm1_T hx hx1 (hml.trans hlG)).2).2.2.2.1).add_lt
      (h1.trans_le (gm1_mono hx hx1 (hml.trans hlG) (le_max_left _ _)))
      (h2.trans_le (gm1_mono hx hx1 (hml.trans hlG) (le_max_right _ _)))

/-- **No `ε`-number `a ∈ (ϑˣ(Ω₁·Ω₁ + λ'), ϑˣ(Ω₁·Ω₁ + λ))` has `a ≤₁ a·a + a + e` in `R₁⁺`**, for `λ = λ' + ω^e`,
`e = logend(λ)`, `ω^e ∣ λ'`, `λ < Γ_{x+2}`. -/
theorem gm1_not_le1R_lim {l l' : Ordinal.{0}} (hlG : l < gq 1 x) (hdec : l = l' + ω ^ lg l) (hdvd : ω ^ lg l ∣ l')
    (hl'l : l' < l) {a : Ordinal.{0}} (haE : InE a) (h1 : gq l' x < a) (h2 : a < gq l x) :
    ¬ le1R a (a * a + a + lg l) := by
  intro hR
  obtain ⟨hlT, hl1⟩ := gm1_T hx hx1 hlG
  obtain ⟨hGT, -, hG1, -, -⟩ := geq_facts hx hx1 hlT hl1
  obtain ⟨hl'T, hl'1⟩ := gm1_T hx hx1 (hl'l.trans hlG)
  have hxa : x < a := (geq_facts hx hx1 hl'T hl'1).2.1.trans h1
  have ha1 : a < Om1 := h2.trans hG1
  have haT : a ∈ Tset x := vz_T_down hx hx1 hGT hG1 h2.le
  obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 haT hxa.le ha1 (inE_indec haE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxa, by rw [hξv]; exact haE⟩
  have haa : a * a ≤ a * a + a + lg l := le_self_add.trans le_self_add
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
  · have hla : l < a := by
      rcases lt_or_ge a (gq 1 x) with ha1' | ha1'
      · exfalso
        have h1a : (1 : Ordinal.{0}) < a := (lu_one_lt_E hx).trans hxa
        obtain ⟨h1T, h1Ω⟩ := gm1_one_T hx hx1
        have hξ1 : ξ < Om1 * Om1 + 1 :=
          lgLt_of_vt_lt hx hx1 hξT hξ2 h1T h1Ω (by rw [hξv]; exact h1a) (by rw [hξv]; exact ha1')
        have hξe : ξ = Om1 * Om1 := le_antisymm (Order.lt_add_one_iff.1 hξ1) hξs
        have ha0 : a = gq 0 x := by rw [← hξv, hξe]; show vt x (Om1 * Om1) = vt x (Om1 * Om1 + 0); rw [add_zero]
        have h0l : gq 0 x ≤ gq l' x := gfq0_le hx hx1 hl'T hl'1
        rw [← ha0] at h0l
        exact absurd (h1.trans_le h0l) (lt_irrefl _)
      · exact hlG.trans_le ha1'
    have hξk : ξ < Om1 * Om1 + l :=
      lgLt_of_vt_lt hx hx1 hξT hξ2 hlT hl1 (by rw [hξv]; exact hla) (by rw [hξv]; exact h2)
    have hje : Om1 * Om1 + (ξ - Om1 * Om1) = ξ := Ordinal.add_sub_cancel_of_le hξs
    obtain ⟨ν, hν⟩ : ∃ ν, ξ - Om1 * Om1 = ν := ⟨_, rfl⟩
    rw [hν] at hje
    have hνl : ν < l := (add_lt_add_iff_left _).1 (by rw [hje]; exact hξk)
    have hva : a = gq ν x := by rw [← hξv, ← hje]; rfl
    have hl'ν : l' < ν := by
      by_contra hle
      push Not at hle
      have h3 : gq ν x ≤ gq l' x := gm1_mono hx hx1 (hl'l.trans hlG) hle
      rw [← hva] at h3
      exact absurd (h1.trans_le h3) (lt_irrefl _)
    have hν0 : 0 < ν := lt_of_le_of_lt zero_le hl'ν
    have hL := gm1_lh hx hx1 (hνl.trans hlG) hν0
    rw [← hva] at hL
    have hle := (add_le_add_iff_left (a * a + a)).1 (hL.2 _ hR)
    exact absurd hle (not_le.2 (gc_lg_lt hdec hdvd hl'ν hνl))

end GQ1

end Googology.Trans.PoR.InaccPsi.R2.Gm
