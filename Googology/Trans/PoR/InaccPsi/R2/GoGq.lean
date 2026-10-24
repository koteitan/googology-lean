import Googology.Trans.PoR.InaccPsi.R2.GoLv

/-!
# OFFSETS `Γ_{x+1+K}` FOR EVERY BOUND `K`: the facts of `R2.GmGq` without the bound `Γ_{x+2}`

`R2.GmGq`, `R2.GmU` and `R2.GmRS` bound every offset by `Γ_{x+2} = ϑˣ(Ω₁·Ω₁ + 1)`, so codes `≥ Γ_{Ω₁+2}` have no layer.
Here the same facts for an arbitrary bound `ϑˣ(Ω₁·Ω₁ + K)` (`K ∈ Tˣ ∩ Ω₁`, e.g. the reading `K = k(x)` of any code
`k`), the only change being that the reach formula of `ϑˣ(Ω₁·Ω₁ + η)` needs `η` not to be a fixed point of
`η ↦ ϑˣ(Ω₁·Ω₁ + η)` (`gfq_lh_gen`):

* `goq_facts`, `goq_T` (**every offset below `Γ_{x+1+K}` lies in `Tˣ ∩ Ω₁`**), `goq_lt`, `goq_mono`, `goq_lh`
  (**`lh(ϑˣ(Ω₁·Ω₁ + η)) = G·G + G + logend(η)` whenever `η < ϑˣ(Ω₁·Ω₁ + σ)` for some `σ < η`**, in particular for
  `K < η < Γ_{x+1+K}`), `goq_lh_of`;
* `goq_lt_lim_iff` (**`v < G(λ)` iff `v < G(ν)` for some `ν < λ`**, every non-fixed limit `λ < Γ_{x+1+K}`) and
  `goq_not_le1R_lim` (no `ε`-number `a ∈ (G(λ'), G(λ))` below `Γ_{x+2}` or above `λ` is `≤₁ a·a + a + logend(λ)`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Go

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gm

section GQK

variable {x K : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hK : K ∈ Tset x) (hK1 : K < Om1)
include hx hx1 hK hK1

theorem goq_facts : gq K x ∈ Tset x ∧ x < gq K x ∧ gq K x < Om1 ∧ InE (gq K x) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := geq_facts hx hx1 hK hK1
  exact ⟨h1, h2, h3, h4⟩

/-- **Every offset below `Γ_{x+1+K}` lies in `Tˣ ∩ Ω₁`.** -/
theorem goq_T {η : Ordinal.{0}} (h : η < gq K x) : η ∈ Tset x ∧ η < Om1 := by
  obtain ⟨h1, -, h3, -⟩ := goq_facts hx hx1 hK hK1
  exact ⟨vz_T_down hx hx1 h1 h3 h.le, h.trans h3⟩

theorem goq_lt {j η : Ordinal.{0}} (hη : η < gq K x) (h : j < η) : gq j x < gq η x :=
  gmq_lt hx hx1 (goq_T hx hx1 hK hK1 hη).1 (goq_T hx hx1 hK hK1 hη).2 h

theorem goq_mono {j η : Ordinal.{0}} (hη : η < gq K x) (h : j ≤ η) : gq j x ≤ gq η x :=
  gmq_mono hx hx1 (goq_T hx hx1 hK hK1 hη).1 (goq_T hx hx1 hK hK1 hη).2 h

/-- **`lh(ϑˣ(Ω₁·Ω₁ + η)) = G·G + G + logend(η)`** for every `η < Γ_{x+1+K}` below some `ϑˣ(Ω₁·Ω₁ + σ)`, `σ < η`. -/
theorem goq_lh {η : Ordinal.{0}} (hη : η < gq K x) (hsig : ∃ σ, σ < η ∧ η < gq σ x) :
    IsLh1 (gq η x) (gq η x * gq η x + gq η x + lg η) :=
  (gfq_lh_gen hx hx1 (goq_T hx hx1 hK hK1 hη).1 (goq_T hx hx1 hK hK1 hη).2).1 hsig

/-- **The reach for every offset `K < η < Γ_{x+1+K}`.** -/
theorem goq_lh_of {η : Ordinal.{0}} (hKη : K < η) (hη : η < gq K x) :
    IsLh1 (gq η x) (gq η x * gq η x + gq η x + lg η) :=
  goq_lh hx hx1 hK hK1 hη ⟨K, hKη, hη⟩

/-- **`v < ϑˣ(Ω₁·Ω₁ + λ)` iff `v < ϑˣ(Ω₁·Ω₁ + ν)` for some `ν < λ`**, for every limit `λ < Γ_{x+1+K}` that is not
a fixed point (`λ < ϑˣ(Ω₁·Ω₁ + σ)` for some `σ < λ`). -/
theorem goq_lt_lim_iff {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlG : l < gq K x)
    (hsig : ∃ σ, σ < l ∧ l < gq σ x) :
    ∀ v, v < gq l x → ∃ ν < l, v < gq ν x := by
  obtain ⟨hlT, hl1⟩ := goq_T hx hx1 hK hK1 hlG
  obtain ⟨hGT, -, hG1, -, -⟩ := geq_facts hx hx1 hlT hl1
  have h0T := mem_T_of_le hx hx1 (zero_le : (0 : Ordinal.{0}) ≤ x)
  have h01 : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  rcases le_or_gt v (max x l) with hvx | hxv0
  · obtain ⟨σ, hσl, hlσ⟩ := hsig
    have h1l : (1 : Ordinal.{0}) < l := by simpa using hl.add_one_lt hl.bot_lt
    rcases le_total x l with hxl | hlx
    · refine ⟨σ, hσl, hvx.trans_lt ?_⟩
      rw [max_eq_right hxl]; exact hlσ
    · refine ⟨1, h1l, hvx.trans_lt ?_⟩
      rw [max_eq_left hlx]; exact (gm1_facts hx hx1).2.1
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
        have hq' : ξ / Om1 < gq (max n1 n2) x :=
          hn1.trans_le (goq_mono hx hx1 hK hK1 (hml.trans hlG) (le_max_left _ _))
        have hr' : ξ % Om1 < gq (max n1 n2) x :=
          hn2.trans_le (goq_mono hx hx1 hK hK1 (hml.trans hlG) (le_max_right _ _))
        obtain ⟨hmT, hm1⟩ := goq_T hx hx1 hK hK1 (hml.trans hlG)
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
        exact goq_lt hx hx1 hK hK1 ((hl.add_one_lt hjk).trans hlG) (lt_add_one _)
    · obtain ⟨L, rfl⟩ := indec_eq_opow hI
      have hL : L < ω ^ L := lt_of_le_of_ne (right_le_opow _ one_lt_omega0)
        (fun h => hvE' (by unfold InE; rw [← h]; exact h.symm))
      obtain ⟨n, hnl, hn⟩ := IH L hL (hL.trans hv)
      exact ⟨n, hnl, (geq_facts hx hx1 (goq_T hx hx1 hK hK1 (hnl.trans hlG)).1 (goq_T hx hx1 hK hK1
          (hnl.trans hlG)).2).2.2.2.1.opow_lt hn⟩
  · have hD : DecompR0 v := not_not.1 hI
    rcases hD with h0 | ⟨u1, u2, hu1, hu2, hsum⟩
    · exact absurd h0 (lt_of_le_of_lt zero_le hxv).ne'
    obtain ⟨n1, hn1l, h1⟩ := IH u1 hu1 (hu1.trans hv)
    obtain ⟨n2, hn2l, h2⟩ := IH u2 hu2 (hu2.trans hv)
    have hml : max n1 n2 < l := max_lt hn1l hn2l
    refine ⟨max n1 n2, hml, ?_⟩
    rw [← hsum]
    exact (inE_indec (geq_facts hx hx1 (goq_T hx hx1 hK hK1 (hml.trans hlG)).1
      (goq_T hx hx1 hK hK1 (hml.trans hlG)).2).2.2.2.1).add_lt
      (h1.trans_le (goq_mono hx hx1 hK hK1 (hml.trans hlG) (le_max_left _ _)))
      (h2.trans_le (goq_mono hx hx1 hK hK1 (hml.trans hlG) (le_max_right _ _)))

/-- **No `ε`-number `a ∈ (ϑˣ(Ω₁·Ω₁ + λ'), ϑˣ(Ω₁·Ω₁ + λ))` with `a < Γ_{x+2}` or `λ < a` has `a ≤₁ a·a + a + e` in
`R₁⁺`**, for `λ = λ' + ω^e`, `e = logend(λ)`, `ω^e ∣ λ'`, `λ < Γ_{x+1+K}`. -/
theorem goq_not_le1R_lim {l l' : Ordinal.{0}} (hlG : l < gq K x) (hdec : l = l' + ω ^ lg l) (hdvd : ω ^ lg l ∣ l')
    (hl'l : l' < l) {a : Ordinal.{0}} (haE : InE a) (h1 : gq l' x < a) (h2 : a < gq l x)
    (hla0 : a < gq 1 x ∨ l < a) :
    ¬ le1R a (a * a + a + lg l) := by
  intro hR
  obtain ⟨hlT, hl1⟩ := goq_T hx hx1 hK hK1 hlG
  obtain ⟨hGT, -, hG1, -, -⟩ := geq_facts hx hx1 hlT hl1
  obtain ⟨hl'T, hl'1⟩ := goq_T hx hx1 hK hK1 (hl'l.trans hlG)
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
      · rcases hla0 with h | h
        · exact absurd ha1' (not_le.2 h)
        · exact h
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
      have h3 : gq ν x ≤ gq l' x := goq_mono hx hx1 hK hK1 (hl'l.trans hlG) hle
      rw [← hva] at h3
      exact absurd (h1.trans_le h3) (lt_irrefl _)
    obtain ⟨hνT, hν1⟩ := goq_T hx hx1 hK hK1 (hνl.trans hlG)
    have hlh := gfq_lh_gen hx hx1 hνT hν1
    have hlg0 : lg l ≠ 0 := by
      intro h0
      rw [h0, opow_zero] at hdec
      have hb : l' < ν := hl'ν
      have hc : ν < l' + 1 := hdec ▸ hνl
      exact absurd (Order.lt_add_one_iff.1 hc) (not_le.2 hb)
    by_cases hsig : ∃ σ, σ < ν ∧ ν < gq σ x
    · have hL := hlh.1 hsig
      rw [← hva] at hL
      have hle := (add_le_add_iff_left (a * a + a)).1 (hL.2 _ hR)
      exact absurd hle (not_le.2 (gc_lg_lt hdec hdvd hl'ν hνl))
    · push Not at hsig
      have hL := hlh.2 hsig
      rw [← hva] at hL
      have hle := hL.2 _ hR
      exact absurd hle (not_le.2 (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hlg0)))

end GQK

end Googology.Trans.PoR.InaccPsi.R2.Go
