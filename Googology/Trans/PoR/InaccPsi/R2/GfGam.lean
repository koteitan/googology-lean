import Googology.Trans.PoR.InaccPsi.R2.GfLoc

/-!
# Offsets up to `Γ_{x+1}` and the case that fails: the `Γ`-fixed point `ϑˣ(Ω₁²·2)`

The term-offset step (`R2.GeLad`) and the union step (`R2.GeLim`, `R2.GfLim`) use the bound `e(x) < ε_{x+1}` only
through four facts about `G(η) = ϑˣ(Ω₁·Ω₁ + η) = Γ_{x+1+η}`; here they hold for every offset `η < Γ_{x+1} = G(0)`:

* `gfq0_facts`, `gfq_T` (**`η < Γ_{x+1}` lies in `Tˣ ∩ Ω₁`**), `gfq0_le`, `gfq_lt` / `gfq_mono` (**`η ↦ G(η)` is
  strictly increasing below `Γ_{x+1}`**), `gfq_lh` (**`lh(G(η)) = G·G + G + logend(η)` for `0 < η < Γ_{x+1}`**);
* `gf_lt_lim_iff` (`v < G(λ)` iff `v < G(ν)` for some `ν < λ`) and `gf_not_le1R_lim` (no `ε`-number in
  `(G(λ'), G(λ))` is `≤₁ a·a + a + logend(λ)` in `R₁⁺`) for **every limit offset `λ < Γ_{x+1}`**;
* **the case that fails**, exactly: `gfq_lh_gen` (**for every `η ∈ Tˣ ∩ Ω₁`: `lh(G(η)) = G·G + G + logend(η)` when
  `η < G(σ)` for some `σ < η`, and `lh(G(η)) = G·G + G` when `G(σ) ≤ η` for every `σ < η`**: at a `Γ`-fixed point the
  reach of the top has no logend term), `gfFix2` (**`η* = ϑˣ(Ω₁·Ω₁·2)` is such a point: every `G(σ)`, `σ < η*`, lies
  below `η*`, so `lh(G(η*)) = G·G + G`**), `gfq_noSep` (**every top `G(ν)`, `0 < ν < Γ_{x+1}`, already has
  `G ≤₁ G·G + G` in `R₁⁺`**: the property `f(G) ≤₁ f(G)·f(G) + f(G)`, all that a covering copy of `G(η*) ≤₁ lh(G(η*))`
  keeps, holds at the tops below as well, so the separation of the limit witness has nothing to use).

No new axiom.  New definitions: none.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ly Lu
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Ge

section GQG

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem gfq0_facts : gq 0 x ∈ Tset x ∧ x < gq 0 x ∧ gq 0 x < Om1 ∧ InE (gq 0 x) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := geq_facts hx hx1 (mem_T_of_le hx hx1 zero_le) (hx.pos.trans hx1)
  exact ⟨h1, h2, h3, h4⟩

/-- **Every offset below `Γ_{x+1}` lies in `Tˣ ∩ Ω₁`.** -/
theorem gfq_T {η : Ordinal.{0}} (h : η < gq 0 x) : η ∈ Tset x ∧ η < Om1 := by
  obtain ⟨h1, -, h3, -⟩ := gfq0_facts hx hx1
  exact ⟨vz_T_down hx hx1 h1 h3 h.le, h.trans h3⟩

theorem gfq0_le {η : Ordinal.{0}} (hT : η ∈ Tset x) (h1 : η < Om1) : gq 0 x ≤ gq η x := by
  rcases eq_or_ne η 0 with rfl | h0
  · exact le_rfl
  have h0T := mem_T_of_le hx hx1 (zero_le : (0 : Ordinal.{0}) ≤ x)
  have h01 : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
  obtain ⟨-, hxv, -, -, -⟩ := geq_facts hx hx1 hT h1
  exact (geq_lt_of hx hx1 h0T h01 hT h1 (pos_iff_ne_zero.2 h0) (hx.pos.trans hxv)).le

/-- **`η ↦ ϑˣ(Ω₁·Ω₁ + η)` is strictly increasing below `Γ_{x+1}`.** -/
theorem gfq_lt {j η : Ordinal.{0}} (hη : η < gq 0 x) (h : j < η) : gq j x < gq η x := by
  obtain ⟨hT, h1⟩ := gfq_T hx hx1 hη
  obtain ⟨hjT, hj1⟩ := gfq_T hx hx1 (h.trans hη)
  exact geq_lt_of hx hx1 hjT hj1 hT h1 h ((h.trans hη).trans_le (gfq0_le hx hx1 hT h1))

theorem gfq_mono {j η : Ordinal.{0}} (hη : η < gq 0 x) (h : j ≤ η) : gq j x ≤ gq η x := by
  rcases h.lt_or_eq with h | rfl
  · exact (gfq_lt hx hx1 hη h).le
  · exact le_rfl

/-- **`lh(ϑˣ(Ω₁·Ω₁ + η)) = G·G + G + logend(η)`** for `0 < η < Γ_{x+1}`. -/
theorem gfq_lh {η : Ordinal.{0}} (hη : η < gq 0 x) (h0 : 0 < η) :
    IsLh1 (gq η x) (gq η x * gq η x + gq η x + lg η) := by
  obtain ⟨hT, h1⟩ := gfq_T hx hx1 hη
  have h := (Lq.lq_lh_sq hx hx1 hT h1).1
  have hz : lqZeta x (Om1 * Om1) η = lg η := by
    unfold lqZeta
    rw [if_pos ⟨0, h0, hη⟩]
  rw [hz] at h
  exact h

/-- **`v < ϑˣ(Ω₁·Ω₁ + λ)` iff `v < ϑˣ(Ω₁·Ω₁ + ν)` for some `ν < λ`** (`λ` a limit below `Γ_{x+1}`). -/
theorem gf_lt_lim_iff {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlG : l < gq 0 x) :
    ∀ v, v < gq l x → ∃ ν < l, v < gq ν x := by
  obtain ⟨hlT, hl1⟩ := gfq_T hx hx1 hlG
  obtain ⟨hGT, -, hG1, -, -⟩ := geq_facts hx hx1 hlT hl1
  have h0T := mem_T_of_le hx hx1 (zero_le : (0 : Ordinal.{0}) ≤ x)
  have h01 : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
  have hG0 : l < gq 0 x := hlG
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  rcases le_or_gt v (max x l) with hvx | hxv0
  · exact ⟨0, hl.bot_lt, hvx.trans_lt (max_lt (geq_facts hx hx1 h0T h01).2.1 hG0)⟩
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
        have hq' : ξ / Om1 < gq (max n1 n2) x := hn1.trans_le (gfq_mono hx hx1 (hml.trans hlG) (le_max_left _ _))
        have hr' : ξ % Om1 < gq (max n1 n2) x := hn2.trans_le (gfq_mono hx hx1 (hml.trans hlG) (le_max_right _ _))
        obtain ⟨hmT, hm1⟩ := gfq_T hx hx1 (hml.trans hlG)
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
        exact gfq_lt hx hx1 ((hl.add_one_lt hjk).trans hlG) (lt_add_one _)
    · obtain ⟨L, rfl⟩ := indec_eq_opow hI
      have hL : L < ω ^ L := lt_of_le_of_ne (right_le_opow _ one_lt_omega0)
        (fun h => hvE' (by unfold InE; rw [← h]; exact h.symm))
      obtain ⟨n, hnl, hn⟩ := IH L hL (hL.trans hv)
      exact ⟨n, hnl, (geq_facts hx hx1 (gfq_T hx hx1 (hnl.trans hlG)).1 (gfq_T hx hx1
          (hnl.trans hlG)).2).2.2.2.1.opow_lt hn⟩
  · have hD : DecompR0 v := not_not.1 hI
    rcases hD with h0 | ⟨u1, u2, hu1, hu2, hsum⟩
    · exact absurd h0 (lt_of_le_of_lt zero_le hxv).ne'
    obtain ⟨n1, hn1l, h1⟩ := IH u1 hu1 (hu1.trans hv)
    obtain ⟨n2, hn2l, h2⟩ := IH u2 hu2 (hu2.trans hv)
    have hml : max n1 n2 < l := max_lt hn1l hn2l
    refine ⟨max n1 n2, hml, ?_⟩
    rw [← hsum]
    exact (inE_indec (geq_facts hx hx1 (gfq_T hx hx1 (hml.trans hlG)).1
      (gfq_T hx hx1 (hml.trans hlG)).2).2.2.2.1).add_lt
      (h1.trans_le (gfq_mono hx hx1 (hml.trans hlG) (le_max_left _ _)))
      (h2.trans_le (gfq_mono hx hx1 (hml.trans hlG) (le_max_right _ _)))

/-- **No `ε`-number `a ∈ (ϑˣ(Ω₁·Ω₁ + λ'), ϑˣ(Ω₁·Ω₁ + λ))` has `a ≤₁ a·a + a + e` in `R₁⁺`**, for a constant limit
`λ = λ' + ω^e`, `e = logend(λ)`, `ω^e ∣ λ'`. -/
theorem gf_not_le1R_lim {l l' : Ordinal.{0}} (hlG : l < gq 0 x) (hdec : l = l' + ω ^ lg l) (hdvd : ω ^ lg l ∣ l')
    (hl'l : l' < l) {a : Ordinal.{0}} (haE : InE a) (h1 : gq l' x < a) (h2 : a < gq l x) :
    ¬ le1R a (a * a + a + lg l) := by
  intro hR
  obtain ⟨hlT, hl1⟩ := gfq_T hx hx1 hlG
  obtain ⟨hGT, -, hG1, -, -⟩ := geq_facts hx hx1 hlT hl1
  obtain ⟨hl'T, hl'1⟩ := gfq_T hx hx1 (hl'l.trans hlG)
  have hxa : x < a := (geq_facts hx hx1 hl'T hl'1).2.1.trans h1
  have hla : l < a := hlG.trans_le ((gfq_mono hx hx1 (hl'l.trans hlG) zero_le).trans h1.le)
  have ha1 : a < Om1 := h2.trans hG1
  have haT : a ∈ Tset x := vz_T_down hx hx1 hGT hG1 h2.le
  obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 haT hxa.le ha1 (inE_indec haE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxa, by rw [hξv]; exact haE⟩
  have hξk : ξ < Om1 * Om1 + l :=
    lgLt_of_vt_lt hx hx1 hξT hξ2 hlT hl1 (by rw [hξv]; exact hla) (by rw [hξv]; exact h2)
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
  · have hje : Om1 * Om1 + (ξ - Om1 * Om1) = ξ := Ordinal.add_sub_cancel_of_le hξs
    obtain ⟨ν, hν⟩ : ∃ ν, ξ - Om1 * Om1 = ν := ⟨_, rfl⟩
    rw [hν] at hje
    have hνl : ν < l := (add_lt_add_iff_left _).1 (by rw [hje]; exact hξk)
    have hva : a = gq ν x := by rw [← hξv, ← hje]; rfl
    have hl'ν : l' < ν := by
      by_contra hle
      push Not at hle
      have h3 : gq ν x ≤ gq l' x := gfq_mono hx hx1 (hl'l.trans hlG) hle
      rw [← hva] at h3
      exact absurd (h1.trans_le h3) (lt_irrefl _)
    have hν0 : 0 < ν := lt_of_le_of_lt zero_le hl'ν
    have hL := gfq_lh hx hx1 (hνl.trans hlG) hν0
    rw [← hva] at hL
    have hle := (add_le_add_iff_left (a * a + a)).1 (hL.2 _ hR)
    exact absurd hle (not_le.2 (gc_lg_lt hdec hdvd hl'ν hνl))


/-- **THE CASE THAT FAILS** (the reach of the top `G(η) = ϑˣ(Ω₁·Ω₁ + η)` for every `η ∈ Tˣ ∩ Ω₁`): with a logend term
when `η < G(σ)` for some `σ < η`, and **without one at a `Γ`-fixed point** (`G(σ) ≤ η` for every `σ < η`). -/
theorem gfq_lh_gen {η : Ordinal.{0}} (hT : η ∈ Tset x) (h1 : η < Om1) :
    ((∃ σ, σ < η ∧ η < gq σ x) → IsLh1 (gq η x) (gq η x * gq η x + gq η x + lg η)) ∧
    ((∀ σ, σ < η → gq σ x ≤ η) → IsLh1 (gq η x) (gq η x * gq η x + gq η x)) := by
  have h := (Lq.lq_lh_sq hx hx1 hT h1).1
  refine ⟨fun ⟨σ, hσ, hησ⟩ => ?_, fun hfix => ?_⟩
  · have hz : lqZeta x (Om1 * Om1) η = lg η := by unfold lqZeta; rw [if_pos ⟨σ, hσ, hησ⟩]
    rwa [hz] at h
  · have hz : lqZeta x (Om1 * Om1) η = 0 := by
      unfold lqZeta
      rw [if_neg]
      rintro ⟨σ, hσ, hησ⟩
      exact absurd (hfix σ hσ) (not_le.2 hησ)
    rwa [hz, add_zero] at h

/-- **The first `Γ`-fixed point is `η* = ϑˣ(Ω₁·(Ω₁·2))`**: it lies in `Tˣ ∩ Ω₁` above `Γ_{x+1}`, every `G(σ)` with
`σ < η*` lies below `η*` ([W07a] Lemma 3.30 through `lqVt_lt`), and **`lh(G(η*)) = G·G + G`**. -/
theorem gfFix2 :
    vt x (Om1 * (Om1 * 2 + 0) + 0) ∈ Tset x ∧ vt x (Om1 * (Om1 * 2 + 0) + 0) < Om1 ∧
      gq 0 x < vt x (Om1 * (Om1 * 2 + 0) + 0) ∧
      (∀ σ, σ < vt x (Om1 * (Om1 * 2 + 0) + 0) → gq σ x < vt x (Om1 * (Om1 * 2 + 0) + 0)) ∧
      IsLh1 (gq (vt x (Om1 * (Om1 * 2 + 0) + 0)) x)
        (gq (vt x (Om1 * (Om1 * 2 + 0) + 0)) x * gq (vt x (Om1 * (Om1 * 2 + 0) + 0)) x +
          gq (vt x (Om1 * (Om1 * 2 + 0) + 0)) x) := by
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
  have h1T : (1 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 (lu_one_lt_E hx).le
  have h1Ω : (1 : Ordinal.{0}) < Om1 := (lu_one_lt_E hx).trans hx1
  have h2x : (2 : Ordinal.{0}) < x := by
    have := natCast_lt_omega0 2
    exact_mod_cast this.trans (omega0_lt_inE hx)
  have h2T : (2 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 h2x.le
  have h2Ω : (2 : Ordinal.{0}) < Om1 := h2x.trans hx1
  have h12 : (1 : Ordinal.{0}) ≤ 2 := by norm_num
  obtain ⟨-, -, hvT, hxv, hv1, -, -, -, -, -⟩ := Lq.lq_facts hx hx1 h12 h2T h2Ω h0T h0Ω h0T h0Ω
  set η := vt x (Om1 * (Om1 * 2 + 0) + 0) with hη
  have hlt : ∀ σ, σ < η → gq σ x < η := by
    intro σ hσ
    have hσT : σ ∈ Tset x := vz_T_down hx hx1 hvT hv1 hσ.le
    have hσΩ : σ < Om1 := hσ.trans hv1
    have harg : Om1 * (Om1 * 1 + 0) + σ < Om1 * (Om1 * 2 + 0) + 0 := by
      have e2 : Om1 * (2 : Ordinal.{0}) = Om1 + Om1 := by
        rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one]
      rw [mul_one, add_zero, add_zero, add_zero, e2, mul_add]
      exact (add_lt_add_iff_left _).2 (hσΩ.trans_le (le_mul_left Om1 (Ordinal.omega_pos 1)))
    have h := lqVt_lt hx hx1 h1T h1Ω h0T h0Ω hσT hσΩ h12 h2T h2Ω h0T h0Ω h0T h0Ω harg
      ((lu_one_lt_E hx).trans hxv) (hx.pos.trans hxv) hσ
    have e : vt x (Om1 * (Om1 * 1 + 0) + σ) = gq σ x := by rw [mul_one, add_zero]; rfl
    rwa [e] at h
  refine ⟨hvT, hv1, hlt 0 (hx.pos.trans hxv), hlt, ?_⟩
  exact (gfq_lh_gen hx hx1 hvT hv1).2 fun σ hσ => (hlt σ hσ).le

/-- **No separation from the tops below**: every `G(ν)`, `0 < ν < Γ_{x+1}`, has `G ≤₁ G·G + G` in `R₁⁺`. -/
theorem gfq_noSep {ν : Ordinal.{0}} (hν : ν < gq 0 x) (h0 : 0 < ν) :
    le1R (gq ν x) (gq ν x * gq ν x + gq ν x) := by
  have hL := gfq_lh hx hx1 hν h0
  obtain ⟨hT, h1⟩ := gfq_T hx hx1 hν
  obtain ⟨-, -, -, hE, -⟩ := geq_facts hx hx1 hT h1
  exact le1R_of_le ((le_mul_left _ hE.pos).trans le_self_add) le_self_add hL.1

end GQG

end Googology.Trans.PoR.InaccPsi.R2.Gf
