import Googology.Trans.PoR.InaccPsi.R2.GeSub

/-!
# The limit of the ladder over a gated base with a TERM offset: the layer with top `ϑˣ(Ω₁·Ω₁ + e(x))`

`R2.GdLad` makes the limit of the gated ladder with a constant offset `η` (below every base above the gate).  Here
the offset is a function `e` of the base: `e(x) ∈ Tˣ ∩ Ω₁` with Lemma EXACT (`π_{σ,ρ}(e(ρ)) = e(σ)`), below `E_K(x)`,
and `ϑˣ(Ω₁·Ω₁ + j) ≤ E_K(x) < ϑˣ(Ω₁·Ω₁ + e(x))` for every `j ∈ Tˣ` below `e(x)` (`GeqH B e`); e.g. `e(x) = x + 1`
over the layer of `Γ_{x+x}`.

* `geq_facts`, `geq_lt_next`, `geq_le1R` (**`G ≤₁ G·G` in `R₁⁺`**, `G = ϑˣ(Ω₁·Ω₁ + η)`, for every `η ∈ Tˣ ∩ Ω₁`),
  `geq_lt` / `geq_mono` (**`η ↦ ϑˣ(Ω₁·Ω₁ + η)` is strictly increasing on `Tˣ ∩ ε_{x+1}`**), `geq_pi` (**EXACT for
  `ϑ^ρ(Ω₁·Ω₁ + e(ρ))`** from EXACT for `e`), `geq_lh` (**`lh(G) = G·G + G + logend(η)`** for `0 < η < ε_{x+1}`);
* `geq_gP_lt`, `geq_lt_iff` (**`v < ϑˣ(Ω₁·Ω₁ + e(x))` iff `v < gdP B n x` for some `n`**), `geq_not_le1R_sq`;
* `geqUSys`, `GeqK.geqTopWit` (the witness pair of the top for the copies that keep the gate), `geqLim : GdLay`,
  `geqLimB : GdB`.

No new axiom.  New definitions: `GeqH`, `geqUSys`, `geqLim`, `geqLimB`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ge

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ly Lu
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd

variable {B : GdB}

/-! ## `ϑˣ(Ω₁·Ω₁ + η)` for every `η ∈ Tˣ ∩ Ω₁` -/

section GQ

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem geq_facts {η : Ordinal.{0}} (hT : η ∈ Tset x) (h1 : η < Om1) :
    gq η x ∈ Tset x ∧ x < gq η x ∧ gq η x < Om1 ∧ InE (gq η x) ∧ Indec (gq η x) := by
  have hA : Om1 * Om1 + η ∈ Tset x := lgArg_mem hx hx1 hT h1
  have h2 : Om1 * Om1 + η < OmTwo := lg_OmOm_lt h1
  obtain ⟨hvT, -, hv1, hvP, -⟩ := vt_memTwo hx hx1 hA h2
  have hE := (vt_E_iff hx hx1 hA h2).2 (lg_Om1_le_OmOm.trans le_self_add)
  exact ⟨hvT, hE.1, hv1, hE.2, hvP⟩

theorem geq_lt_next {η : Ordinal.{0}} (hT : η ∈ Tset x) (h1 : η < Om1) {u : Ordinal.{0}} (hxu : x < u)
    (hu : LtInf1 u) : gq η x < u := by
  obtain ⟨m, -, -, hmin, hTm, -⟩ := T_next (Or.inr hx) hx1
  obtain ⟨hT', -, h1', -, -⟩ := geq_facts hx hx1 hT h1
  exact ((hTm _ h1').1 hT').trans_le (hmin u hxu hu)

/-- **`G ≤₁ G·G` in `R₁⁺`** for `G = ϑˣ(Ω₁·Ω₁ + η)`, `η ∈ Tˣ ∩ Ω₁`. -/
theorem geq_le1R {η : Ordinal.{0}} (hT : η ∈ Tset x) (h1 : η < Om1) : le1R (gq η x) (gq η x * gq η x) := by
  have hA : Om1 * Om1 + η ∈ Tset x := lgArg_mem hx hx1 hT h1
  have h2 : Om1 * Om1 + η < OmTwo := lg_OmOm_lt h1
  obtain ⟨hVT, hxV, hV1, hVE, hVP⟩ := geq_facts hx hx1 hT h1
  have hL := lh_eq_lhT (Or.inr hx) hx1 hVT hxV hV1 hVP
  have hsq := lgLhT_sq hx hx1 hA h2 le_self_add
  exact le1R_of_le (le_mul_left _ hVE.pos) hsq hL.1

/-- `ϑˣ(Ω₁·Ω₁ + j) < ϑˣ(Ω₁·Ω₁ + η)` for `j < η` in `Tˣ ∩ Ω₁` with `j < ϑˣ(Ω₁·Ω₁ + η)`. -/
theorem geq_lt_of {j η : Ordinal.{0}} (hjT : j ∈ Tset x) (hj1 : j < Om1) (hT : η ∈ Tset x) (h1 : η < Om1)
    (h : j < η) (hjG : j < gq η x) : gq j x < gq η x := by
  have h1T : (1 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 (lu_one_lt_E hx).le
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  have h1Ω : (1 : Ordinal.{0}) < Om1 := (lu_one_lt_E hx).trans hx1
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
  obtain ⟨-, hxv, -, -, -⟩ := geq_facts hx hx1 hT h1
  have e1 : ∀ z, Om1 * (Om1 * 1 + 0) + z = Om1 * Om1 + z := fun z => by rw [mul_one, add_zero]
  have := lqVt_lt hx hx1 h1T h1Ω h0T h0Ω hjT hj1 le_rfl h1T h1Ω h0T h0Ω hT h1
    (by rw [e1, e1]; exact (add_lt_add_iff_left _).2 h)
    (by rw [e1]; exact (lu_one_lt_E hx).trans hxv) (by rw [e1]; exact hx.pos.trans hxv)
    (by rw [e1]; exact hjG)
  rw [e1, e1] at this
  exact this

/-- `ε_{x+1} ≤ ϑˣ(Ω₁·Ω₁ + η)` for every `η ∈ Tˣ ∩ Ω₁`. -/
theorem geq_eN_le {η : Ordinal.{0}} (hT : η ∈ Tset x) (h1 : η < Om1) : eN x ≤ gq η x := by
  obtain ⟨-, hxv, -, hE, -⟩ := geq_facts hx hx1 hT h1
  exact eN_le hxv hE

theorem eN_lt_Om1' : eN x < Om1 :=
  (geq_eN_le hx hx1 (mem_T_of_le hx hx1 zero_le) (hx.pos.trans hx1)).trans_lt
    (geq_facts hx hx1 (mem_T_of_le hx hx1 zero_le) (hx.pos.trans hx1)).2.2.1

theorem eN_T {η : Ordinal.{0}} (h : η < eN x) : η ∈ Tset x ∧ η < Om1 := by
  have h0T := mem_T_of_le hx hx1 (zero_le : (0 : Ordinal.{0}) ≤ x)
  have h01 : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
  obtain ⟨hGT, -, hG1, -, -⟩ := geq_facts hx hx1 h0T h01
  exact ⟨vz_T_down hx hx1 hGT hG1 (h.le.trans (geq_eN_le hx hx1 h0T h01)),
    h.trans (eN_lt_Om1' hx hx1)⟩

/-- **`η ↦ ϑˣ(Ω₁·Ω₁ + η)` is strictly increasing below `ε_{x+1}`.** -/
theorem geq_lt {j η : Ordinal.{0}} (hη : η < eN x) (h : j < η) : gq j x < gq η x := by
  obtain ⟨hT, h1⟩ := eN_T hx hx1 hη
  obtain ⟨hjT, hj1⟩ := eN_T hx hx1 (h.trans hη)
  exact geq_lt_of hx hx1 hjT hj1 hT h1 h ((h.trans hη).trans_le (geq_eN_le hx hx1 hT h1))

theorem geq_mono {j η : Ordinal.{0}} (hη : η < eN x) (h : j ≤ η) : gq j x ≤ gq η x := by
  rcases h.lt_or_eq with h | rfl
  · exact (geq_lt hx hx1 hη h).le
  · exact le_rfl

/-- **`lh(ϑˣ(Ω₁·Ω₁ + η)) = G·G + G + logend(η)`** for `0 < η < ε_{x+1}`. -/
theorem geq_lh {η : Ordinal.{0}} (hη : η < eN x) (h0 : 0 < η) :
    IsLh1 (gq η x) (gq η x * gq η x + gq η x + lg η) := by
  obtain ⟨hT, h1⟩ := eN_T hx hx1 hη
  have h := (Lq.lq_lh_sq hx hx1 hT h1).1
  have hz : lqZeta x (Om1 * Om1) η = lg η := by
    unfold lqZeta
    have h0T := mem_T_of_le hx hx1 (zero_le : (0 : Ordinal.{0}) ≤ x)
    rw [if_pos ⟨0, h0, hη.trans_le (by
      have := geq_eN_le hx hx1 h0T (hx.pos.trans hx1); exact this)⟩]
  rw [hz] at h
  exact h

end GQ

/-- **EXACT for `ϑ^ρ(Ω₁·Ω₁ + a)`** from EXACT for `a`. -/
theorem geq_pi {σ ρ a b : Ordinal.{0}} (hB : Bases σ ρ) (h : a ∈ TB ρ σ ∧ pi σ ρ a = b) (ha1 : a < Om1) :
    gq a ρ ∈ TB ρ σ ∧ pi σ ρ (gq a ρ) = gq b σ := by
  obtain ⟨hσE, hρE, hσρ, hρ1⟩ := hB
  have hB' : Bases σ ρ := ⟨hσE, hρE, hσρ, hρ1⟩
  obtain ⟨hTB0, hpi0⟩ := lgPi_OmOm hB'
  obtain ⟨hTBs, hpis⟩ := pi_add hB' hTB0 h.1
  rw [hpi0, h.2] at hpis
  have h2 : Om1 * Om1 + a < OmTwo := lg_OmOm_lt ha1
  obtain ⟨hvT, -, -, -, hPar⟩ := vt_memTwo hρE hρ1 hTBs.1 h2
  refine ⟨⟨hvT, ?_⟩, ?_⟩
  · show ↑(Par ρ (vt ρ (Om1 * Om1 + a))) ⊆ Set.Iio σ
    rw [hPar]; exact hTBs.2
  · show pi σ ρ (vt ρ (Om1 * Om1 + a)) = vt σ (Om1 * Om1 + b)
    rw [pi_vt_two hB' hTBs h2, hpis]

/-! ## The limit hypothesis above the gate -/

/-- **The limit hypothesis with a term offset `e`** above the gate: `e(x) ∈ Tˣ ∩ Ω₁` below `E_K(x)`, Lemma EXACT for
`e`, and `ϑˣ(Ω₁·Ω₁ + j) ≤ E_K(x) < ϑˣ(Ω₁·Ω₁ + e(x))` for every `j ∈ Tˣ` below `e(x)`. -/
structure GeqH (B : GdB) (e : Ordinal.{0} → Ordinal.{0}) : Prop where
  mem : ∀ x, InE x → x < Om1 → B.g < x → e x ∈ Tset x ∧ e x < Om1
  elt : ∀ x, InE x → x < Om1 → B.g < x → e x < B.K.E x
  lo : ∀ x, InE x → x < Om1 → B.g < x → ∀ j, j ∈ Tset x → j < e x → gq j x ≤ B.K.E x
  hi : ∀ x, InE x → x < Om1 → B.g < x → B.K.E x < gq (e x) x
  pi : ∀ σ ρ, Bases σ ρ → B.g < σ → e ρ ∈ TB ρ σ ∧ pi σ ρ (e ρ) = e σ

theorem GeqH.facts {e : Ordinal.{0} → Ordinal.{0}} (H : GeqH B e) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
    (hg : B.g < x) : gq (e x) x ∈ Tset x ∧ x < gq (e x) x ∧ gq (e x) x < Om1 ∧ InE (gq (e x) x) ∧ Indec (gq (e x) x) :=
  geq_facts hx hx1 (H.mem x hx hx1 hg).1 (H.mem x hx hx1 hg).2

theorem GeqH.lt_next {e : Ordinal.{0} → Ordinal.{0}} (H : GeqH B e) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
    (hg : B.g < x) {u : Ordinal.{0}} (hxu : x < u) (hu : LtInf1 u) : gq (e x) x < u :=
  geq_lt_next hx hx1 (H.mem x hx hx1 hg).1 (H.mem x hx hx1 hg).2 hxu hu

section Lim

variable {e : Ordinal.{0} → Ordinal.{0}} (H : GeqH B e)
include H

theorem geq_gP_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : B.g < x) : ∀ n : ℕ, gdP B n x < gq (e x) x
  | 0 => H.hi x hx hx1 hg
  | n + 1 => by
      obtain ⟨hgT, -, hg1, -⟩ := gdP_facts B hx hx1 hg n
      obtain ⟨hkT, hk1⟩ := H.mem x hx hx1 hg
      have ih := geq_gP_lt hx hx1 hg n
      have h := lgVt_lt_low hx hx1 hgT hg1 (mem_T_of_le hx hx1 zero_le) (hx.pos.trans hx1) hkT hk1 ih
        (hx.pos.trans (H.facts hx hx1 hg).2.1)
      rw [add_zero] at h
      exact h

/-- **`v < ϑˣ(Ω₁·Ω₁ + η)` iff `v < gdP B n x` for some `n`** (above the gate). -/
theorem geq_lt_iff {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : B.g < x) :
    ∀ v, v < gq (e x) x → ∃ n, v < gdP B n x := by
  obtain ⟨hGT, -, hG1, -, -⟩ := H.facts hx hx1 hg
  obtain ⟨hkT, hk1⟩ := H.mem x hx hx1 hg
  have hEP1 : B.K.E x < gdP B 1 x := gdP_lt_succ B hx hx1 hg 0
  have hxE := gdx_E_gt hx hx1 hg
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  rcases le_or_gt v (B.K.E x) with hvE | hEv
  · exact ⟨1, hvE.trans_lt hEP1⟩
  have hxv : x < v := hxE.trans hEv
  have hv1 : v < Om1 := hv.trans hG1
  have hvT : v ∈ Tset x := vz_T_down hx hx1 hGT hG1 hv.le
  by_cases hI : Indec v
  · by_cases hvE' : InE v
    · obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 hvT hxv.le hv1 hI
      have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxv, by rw [hξv]; exact hvE'⟩
      have hξk : ξ < Om1 * Om1 + e x :=
        lgLt_of_vt_lt hx hx1 hξT hξ2 hkT hk1 (by rw [hξv]; exact (H.elt x hx hx1 hg).trans hEv)
          (by rw [hξv]; exact hv)
      rcases lt_or_ge ξ (Om1 * Om1) with hξs | hξs
      · obtain ⟨hq1, hrT, hr1, hdec⟩ := lu_split hx hx1 hξT hξ2 hΩξ
        have hqT : ξ / Om1 ∈ Tset x := lgQuot_mem hx hx1 hξT hξs
        have hqr : ξ / Om1 < v ∧ ξ % Om1 < v := by
          rcases lt_or_ge (ξ / Om1) x with hqx | hxq
          · have h := luLt_vt_self hx hx1 hq1 hqx hrT hr1
            rw [hdec, hξv] at h
            exact ⟨hqx.trans hxv, h⟩
          · have hqΩ : ξ / Om1 < Om1 := (Ordinal.lt_mul_iff_div_lt (Ordinal.omega_pos 1).ne').1 hξs
            have h := lvLevel_lt_vt hx hx1 hqT hxq hqΩ hrT hr1
            rw [hdec, hξv] at h
            exact h
        obtain ⟨n1, hn1⟩ := IH _ hqr.1 (hqr.1.trans hv)
        obtain ⟨n2, hn2⟩ := IH _ hqr.2 (hqr.2.trans hv)
        refine ⟨max n1 n2 + 1, ?_⟩
        have hq' : ξ / Om1 < gdP B (max n1 n2) x := hn1.trans_le (gdP_mono B hx hx1 hg (le_max_left _ _))
        have hr' : ξ % Om1 < gdP B (max n1 n2 + 1) x :=
          hn2.trans_le (gdP_mono B hx hx1 hg ((le_max_right _ _).trans (Nat.le_succ _)))
        rw [← hξv, ← hdec]
        exact gd_lt_top B hx hx1 hg hqT hq' hrT hr1 hr'
      · have hje : Om1 * Om1 + (ξ - Om1 * Om1) = ξ := Ordinal.add_sub_cancel_of_le hξs
        have hjk : ξ - Om1 * Om1 < e x := (add_lt_add_iff_left _).1 (by rw [hje]; exact hξk)
        obtain ⟨j, hj⟩ : ∃ j, j = ξ - Om1 * Om1 := ⟨_, rfl⟩
        have hvj : v = gq j x := by rw [← hξv, ← hje, ← hj]; rfl
        have hjT : j ∈ Tset x := vz_T_down hx hx1 hkT hk1 (hj ▸ hjk).le
        exact absurd (H.lo x hx hx1 hg j hjT (hj ▸ hjk)) (not_le.2 (hvj ▸ hEv))
    · obtain ⟨L, rfl⟩ := indec_eq_opow hI
      have hL : L < ω ^ L := lt_of_le_of_ne (right_le_opow _ one_lt_omega0)
        (fun h => hvE' (by unfold InE; rw [← h]; exact h.symm))
      obtain ⟨n, hn⟩ := IH L hL (hL.trans hv)
      exact ⟨n, (gdP_facts B hx hx1 hg n).2.2.2.opow_lt hn⟩
  · have hD : DecompR0 v := not_not.1 hI
    rcases hD with h0 | ⟨u1, u2, hu1, hu2, hsum⟩
    · exact absurd h0 (lt_of_le_of_lt zero_le hxv).ne'
    obtain ⟨n1, h1⟩ := IH u1 hu1 (hu1.trans hv)
    obtain ⟨n2, h2⟩ := IH u2 hu2 (hu2.trans hv)
    refine ⟨max n1 n2, ?_⟩
    rw [← hsum]
    exact (inE_indec (gdP_facts B hx hx1 hg _).2.2.2).add_lt
      (h1.trans_le (gdP_mono B hx hx1 hg (le_max_left _ _)))
      (h2.trans_le (gdP_mono B hx hx1 hg (le_max_right _ _)))

/-- **No `ε`-number `a ∈ (E_K(x), ϑˣ(Ω₁·Ω₁ + η))` has `a ≤₁ a·a` in `R₁⁺`** (above the gate). -/
theorem geq_not_le1R_sq {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : B.g < x) {a : Ordinal.{0}}
    (haE : InE a) (hEa : B.K.E x < a) (hak : a < gq (e x) x) : ¬ le1R a (a * a) := by
  intro hR
  have hxa : x < a := (gdx_E_gt hx hx1 hg).trans hEa
  obtain ⟨n, hn⟩ := geq_lt_iff H hx hx1 hg a hak
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 1 := by
    rcases n with _ | M
    · exact absurd hn (not_lt.2 hEa.le)
    · exact ⟨M, rfl⟩
  obtain ⟨hTT, -, hT1, -⟩ := gdP_facts B hx hx1 hg (M + 1)
  have ha1 : a < Om1 := hn.trans hT1
  have haT : a ∈ Tset x := vz_T_down hx hx1 hTT hT1 hn.le
  obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 haT hxa.le ha1 (inE_indec haE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxa, by rw [hξv]; exact haE⟩
  obtain ⟨hq1, hrT, hr1, hdec⟩ := lu_split hx hx1 hξT hξ2 hΩξ
  have hqM : ξ / Om1 < gdP B M x :=
    gd_quot hx hx1 hg M ξ hξT hξ2 (by rw [hξv]; exact hxa) (by rw [hξv]; exact haE) (by rw [hξv]; exact hEa)
      (by rw [hξv]; exact hn)
  obtain ⟨hMT, -, hM1, -⟩ := gdP_facts B hx hx1 hg M
  have hqT : ξ / Om1 ∈ Tset x := vz_T_down hx hx1 hMT hM1 hqM.le
  set q := ξ / Om1 with hq
  set r := ξ % Om1 with hr
  have hv : vt x (Om1 * q + r) = a := by rw [hdec, hξv]
  have hζr : luZeta x q r < a := by
    refine lu_zeta_le.trans_lt ?_
    rcases lt_or_ge q x with hqx | hxq
    · have := (lu_th_facts hx hx1 hq1 hqx hrT hr1).2.2.2.2.2.2.2
      rwa [hv] at this
    · have := (Lv.gen_facts hx hx1 hqT hxq (hqM.trans hM1) hrT hr1).2.2.2.2.2.2.2.2
      rwa [hv] at this
  have hL : IsLh1 a (luL a q + luZeta x q r) ∧ q < a := by
    rcases lt_or_ge q x with hqx | hxq
    · have h := lu_lh_th hx hx1 hq1 hqx hrT hr1
      rw [hv] at h
      exact ⟨h, hqx.trans hxa⟩
    · have h := Lv.lv_lh_gen hx hx1 hqT hxq (hqM.trans hM1) hrT hr1
      have hqv := (Lv.gen_facts hx hx1 hqT hxq (hqM.trans hM1) hrT hr1).2.2.2.2.2.2.2.1
      rw [hv] at h hqv
      exact ⟨h, hqv⟩
  have hle := hL.1.2 _ hR
  exact absurd hle (not_le.2 (lg_luL_lt_sq haE hL.2 hζr))

theorem geq_lt_next_ups {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) (hg : B.g < upsilon l) :
    gq (e (upsilon l)) (upsilon l) < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have h1 : l < l + ω := lt_add_of_pos_right l omega0_pos
  have hτU := upsPt_upsilon (hl0.trans h1)
  exact (H.lt_next (ups_inE hl) (ups_lt_Om1 l hl1) hg (upsilon_normal.strictMono h1)
    hτU.2).trans (upsilon_normal.strictMono (lt_add_one _))

end Lim

/-! ## The gated limit system and layer -/

/-- **The limit term system over the gated base**: all terms of `GdT B`, top `gq η = ϑˣ(Ω₁·Ω₁ + η)`. -/
noncomputable def geqUSys (B : GdB) (e : Ordinal.{0} → Ordinal.{0}) (H : GeqH B e) : GdSys B.g where
  Tm := GdT B
  val := GdT.val
  CB := GdT.CBt
  cs := GdT.cs
  cst := GdT.cst
  top := fun x => gq (e x) x
  cb_cst := fun _ _ h => GdT.cbt_cst h
  cb_iff := fun _ _ _ h hc => GdT.cbt_iff h hc
  val_cst := fun _ _ => rfl
  cb_cstI := fun _ _ h => h
  lt_top := fun l hl hl1 hg t hCB =>
    (GdT.gd_T (ups_inE hl) (ups_lt_Om1 l hl1) hg t hCB).2.trans
      (geq_gP_lt H (ups_inE hl) (ups_lt_Om1 l hl1) hg _)
  one_le_top := fun l hl hl1 hg =>
    one_le_iff_pos.2 (H.facts (ups_inE hl) (ups_lt_Om1 l hl1) hg).2.2.2.1.pos
  rep := fun l hl hl1 hg v hv => by
    obtain ⟨n, hn⟩ := geq_lt_iff H (ups_inE hl) (ups_lt_Om1 l hl1) hg v hv
    obtain ⟨t, h1, -, h3⟩ :=
      gd_rep (upsPt_upsilon (pos_iff_ne_zero.2 hl.1)) (ups_lt_Om1 l hl1) hg (gdxRep_ri hl hl1 hg) n v hn
    exact ⟨t, h1, h3⟩
  top_lt := fun l hl hl1 hg => geq_lt_next_ups H hl hl1 hg
  pkg := fun _ hl hl1 hg _ hCB h1 R => GdGK.pkgGd R hg (gdxRep_ri hl hl1 hg) (gdxBase_ri hl hl1 hg R) hCB h1
  rs := fun _ _ _ hg _ hCB => rsStep_Gd hg hCB
  uni_le := fun _ _ hσ hρ hB hg _ _ ht hu => GdT.uni_le hσ hρ hB hg ht hu
  small := gd_small

theorem geqUSys_top (B : GdB) (e : Ordinal.{0} → Ordinal.{0}) (H : GeqH B e) (x : Ordinal.{0}) :
    (geqUSys B e H).top x = gq (e x) x := rfl

namespace GeqK

variable {e : Ordinal.{0} → Ordinal.{0}} (H : GeqH B e) {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ) (hg : B.g < ρ)
include H h hg

theorem geq_lt_δ : gq (e ρ) ρ < δ :=
  (H.lt_next (upsPt_inE h.ρU) h.ρ1 hg h.ρτ h.τU.2).trans h.τδ

/-- **The witness pair of the top `gq η`** above the gate: `f(gq (e ρ) ρ) ∈ E` and `gq η (fρ) ≤ f(gq (e ρ) ρ)` for the
copies that keep the gate. -/
theorem geqTopWit : ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ gq (e ρ) ρ ∈ W ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → GdCtx B.g ρ A f →
      (∃ e', f (gq (e ρ) ρ) = ω ^ e' ∧ ω ^ f ρ ∣ e') ∧ gq (e (f ρ)) (f ρ) ≤ f (gq (e ρ) ρ) := by
  classical
  have hρE := upsPt_inE h.ρU
  obtain ⟨-, hρG, -, hGE, hGI⟩ := H.facts hρE h.ρ1 hg
  have hR0 := geq_le1R hρE h.ρ1 (H.mem ρ hρE h.ρ1 hg).1 (H.mem ρ hρE h.ρ1 hg).2
  set G := gq (e ρ) ρ with hG
  set P := G * G with hP
  have hGδ : G < δ := geq_lt_δ H h hg
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
  obtain ⟨WE, ZE, wE, hTE, hIE⟩ := B.K.top_wit ρ τ δ h hg
  have w5 : WZ ρ δ ({P + G, P, G + G, G} ∪ WE) (∅ ∪ ZE) := w4.union wE
  rw [Finset.empty_union] at w5
  refine ⟨{P + G, P, G + G, G} ∪ WE, ZE, w5, by simp, fun A f hW hZ C => ?_⟩
  have hGA : G ∈ A := hW (by simp)
  have hGGA : G + G ∈ A := hW (by simp)
  have hPA : P ∈ A := hW (by simp)
  have hPGA : P + G ∈ A := hW (by simp)
  have hWE : ↑WE ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hTA : B.K.sys.top ρ ∈ A := hWE (Finset.mem_coe.2 hTE)
  obtain ⟨hfE, hPge⟩ := GbK.gbImg h hGE hρG hGδ C.1 hGA hGGA hPA hPGA
  have hyG : f ρ < f G := C.mono C.rho hGA hρG
  refine ⟨⟨f G, hfE.symm, opow_dvd_of_inE hfE hyG.le⟩, ?_⟩
  obtain ⟨hyE, hy1, -⟩ := h.vz_img_base C.1
  have hgy : B.g < f ρ := C.lt hg
  have hTρ : B.K.sys.top ρ = B.K.E ρ := gdx_top hρE h.ρ1 hg
  have hTy : B.K.sys.top (f ρ) = B.K.E (f ρ) := gdx_top hyE hy1 hgy
  have hEG : B.K.E ρ < G := H.hi ρ hρE h.ρ1 hg
  have hfEG : f (B.K.sys.top ρ) < f G := C.mono hTA hGA (by rw [hTρ]; exact hEG)
  have hEy : B.K.E (f ρ) < f G := by
    have := (hIE A f hWE hZ C).2
    rw [hTy] at this
    exact this.trans_lt hfEG
  by_cases hU : UpsPt (f G)
  · exact (H.lt_next hyE hy1 hgy hyG hU.2).le
  · by_contra hlt
    push Not at hlt
    have hsrc1 : le1 G P := (h.lowδ _ _ hρG hPδ.le).2 hR0
    have hR1 : le1R (f G) (f P) := (C.sk _ (C.low _ hGA) hU _).1 (C.cov1 G hGA P hPA hsrc1)
    exact geq_not_le1R_sq H hyE hy1 hgy hfE hEy hlt (le1R_of_le (le_mul_left _ hfE.pos) hPge hR1)

end GeqK

/-- **The limit layer over the gated base**: `geqUSys B η H` with top `ϑˣ(Ω₁·Ω₁ + η)`, above the gate. -/
noncomputable def geqLim (B : GdB) (e : Ordinal.{0} → Ordinal.{0}) (H : GeqH B e) : GdLay B.g where
  sys := geqUSys B e H
  E := fun x => gq (e x) x
  top_eq := fun x hx hx1 hg => (H.facts hx hx1 hg).2.2.2.1.symm
  exp_dvd := fun x hx hx1 hg =>
    opow_dvd_of_inE (H.facts hx hx1 hg).2.2.2.1 (H.facts hx hx1 hg).2.1.le
  exp_lt := fun x hx hx1 hg => (H.facts hx hx1 hg).2.2.1
  top_gt := fun x hx hx1 hg => (H.facts hx hx1 hg).2.1
  top_lt_ups := fun x u hx hx1 hg hxu hu => H.lt_next hx hx1 hg hxu hu.2
  lt_top_E := fun x hx hx1 hg t ht => (GdT.gd_T hx hx1 hg t ht).2.trans (geq_gP_lt H hx hx1 hg _)
  exact := fun _ _ hσ hρ hB hg t ht => GdT.pi hσ hρ hB hg t ht
  exp_pi := fun σ ρ _ _ hB hg => geq_pi hB (H.pi σ ρ hB hg)
    (H.mem ρ hB.2.1 hB.2.2.2 (hg.trans hB.2.2.1)).2
  top_wit := fun _ _ _ h hg => GeqK.geqTopWit H h hg

/-- **The new gated base package**: the limit layer (same gate). -/
noncomputable def geqLimB (B : GdB) (e : Ordinal.{0} → Ordinal.{0}) (H : GeqH B e) : GdB where
  g := B.g
  K := geqLim B e H
  ek := fun x hx hx1 hg => (H.facts hx hx1 hg).2.2.2.1
  mem := fun x hx hx1 hg => (H.facts hx hx1 hg).1

theorem geqLimB_E (B : GdB) (e : Ordinal.{0} → Ordinal.{0}) (H : GeqH B e) (x : Ordinal.{0}) :
    (geqLimB B e H).K.E x = gq (e x) x := rfl

theorem geqLimB_g (B : GdB) (e : Ordinal.{0} → Ordinal.{0}) (H : GeqH B e) : (geqLimB B e H).g = B.g := rfl

end Googology.Trans.PoR.InaccPsi.R2.Ge
