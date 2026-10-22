import Googology.Trans.PoR.InaccPsi.R2.GbW

/-!
# The limit of the ladder over a base, with an ordinal offset: the layer with top `ϑˣ(Ω₁·Ω₁ + η)`

`R2.LpLim` makes the limit layer with top `gk k x = ϑˣ(Ω₁·Ω₁ + k)` for a natural number `k`.  Here the same for every
ordinal constant `η` below every `ε`-number (`GqCst η`, e.g. `η = ω + 1 + k`): for a base `B` whose top `E_K(x)`
lies in `[ϑˣ(Ω₁·Ω₁ + j), ϑˣ(Ω₁·Ω₁ + η))` for every `j < η` (`GqLimH B η`), the tower `lpSys B n`, `n < ω`, is one term
system `gqUSys B η H` with top `gq η x = ϑˣ(Ω₁·Ω₁ + η)`, again a layer with an `ε`-number top in `Tˣ`:

* `gq`, `gq_facts`, `gq_lt` (**`η ↦ ϑˣ(Ω₁·Ω₁ + η)` is strictly increasing on the constants**), `gq_le1R`
  (**`gq ≤₁ gq·gq` in `R₁⁺`**), `gq_pi` (EXACT), `gq_lt_next`;
* `gq_gP_lt`, `gq_lt_iff` (**`v < ϑˣ(Ω₁·Ω₁ + η)` iff `v < gP B n x` for some `n`**), `gq_not_le1R_sq` (no `ε`-number
  `a ∈ (E_K(x), gq η x)` has `a ≤₁ a·a`);
* `gqUSys`, `GqLK.gqTopWit` (the witness pair of the top), `gqLim B η H : XtLay`, `gqLimB`, `gqLimH_next`
  (**the hypothesis passes to the new base with `η + 1`**);
* `gqLim_topIn`, `gqFam_lt_lim` (**`Λ^B < Λ⁺(gqUSys)`**), `gqLim_topIn_K`, `gqLim_gt_K` (**`Λ⁺(K) < Λ⁺(gqUSys)`**),
  `gqLim_eq`.

For `η = k` this is `R2.LpLim` (`gq_nat`), and `gq ω = gbW` (`gq_omega`).  No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Lp Lu

/-- **`gq η x = ϑˣ(Ω₁·Ω₁ + η)`.** -/
noncomputable def gq (η x : Ordinal.{0}) : Ordinal.{0} := vt x (Om1 * Om1 + η)

theorem gq_nat (k : ℕ) (x : Ordinal.{0}) : gq (k : Ordinal.{0}) x = gk k x := rfl

theorem gq_omega (x : Ordinal.{0}) : gq ω x = gbW x := rfl

/-- **`η` is a constant**: below every `ε`-number. -/
def GqCst (η : Ordinal.{0}) : Prop := ∀ x, InE x → η < x

theorem gqCst_nat (k : ℕ) : GqCst (k : Ordinal.{0}) := fun _ hx => (natCast_lt_omega0 k).trans (omega0_lt_inE hx)

theorem gqCst_omega : GqCst ω := fun _ hx => omega0_lt_inE hx

theorem gqCst_succ {η : Ordinal.{0}} (h : GqCst η) : GqCst (η + 1) :=
  fun x hx => (inE_indec hx).add_lt (h x hx) (lu_one_lt_E hx)

section GQ

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem gq_cst {η : Ordinal.{0}} (hηx : η < x) : η ∈ Tset x ∧ η < Om1 :=
  ⟨mem_T_of_le hx hx1 hηx.le, hηx.trans hx1⟩

theorem gq_arg {η : Ordinal.{0}} (hηx : η < x) : Om1 * Om1 + η ∈ Tset x ∧ Om1 * Om1 + η < OmTwo := by
  obtain ⟨hT, h1⟩ := gq_cst hx hx1 hηx
  exact ⟨lgArg_mem hx hx1 hT h1, lg_OmOm_lt h1⟩

/-- The facts on `gq η x`. -/
theorem gq_facts {η : Ordinal.{0}} (hηx : η < x) :
    gq η x ∈ Tset x ∧ x < gq η x ∧ gq η x < Om1 ∧ InE (gq η x) ∧ Indec (gq η x) := by
  obtain ⟨hT, h2⟩ := gq_arg hx hx1 hηx
  obtain ⟨hvT, -, hv1, hvP, -⟩ := vt_memTwo hx hx1 hT h2
  have hE := (vt_E_iff hx hx1 hT h2).2 (lg_Om1_le_OmOm.trans le_self_add)
  exact ⟨hvT, hE.1, hv1, hE.2, hvP⟩

/-- **`η ↦ ϑˣ(Ω₁·Ω₁ + η)` is strictly increasing on the constants below `x`.** -/
theorem gq_lt {j η : Ordinal.{0}} (hηx : η < x) (h : j < η) : gq j x < gq η x := by
  have h1T : (1 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 (lu_one_lt_E hx).le
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  have h1Ω : (1 : Ordinal.{0}) < Om1 := (lu_one_lt_E hx).trans hx1
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
  have hjx : j < x := h.trans hηx
  obtain ⟨hjT, hj1⟩ := gq_cst hx hx1 hjx
  obtain ⟨hkT, hk1⟩ := gq_cst hx hx1 hηx
  obtain ⟨-, hxv, -, -, -⟩ := gq_facts hx hx1 hηx
  have e1 : ∀ z, Om1 * (Om1 * 1 + 0) + z = Om1 * Om1 + z := fun z => by rw [mul_one, add_zero]
  have := lqVt_lt hx hx1 h1T h1Ω h0T h0Ω hjT hj1 le_rfl h1T h1Ω h0T h0Ω hkT hk1
    (by rw [e1, e1]; exact (add_lt_add_iff_left _).2 h)
    (by rw [e1]; exact (lu_one_lt_E hx).trans hxv) (by rw [e1]; exact hx.pos.trans hxv)
    (by rw [e1]; exact hjx.trans hxv)
  rw [e1, e1] at this
  exact this

theorem gq_mono {j η : Ordinal.{0}} (hηx : η < x) (h : j ≤ η) : gq j x ≤ gq η x := by
  rcases h.lt_or_eq with h | rfl
  · exact (gq_lt hx hx1 hηx h).le
  · exact le_rfl

/-- **`gq η x ≤₁ gq η x · gq η x` in `R₁⁺`.** -/
theorem gq_le1R {η : Ordinal.{0}} (hηx : η < x) : le1R (gq η x) (gq η x * gq η x) := by
  obtain ⟨hT, h2⟩ := gq_arg hx hx1 hηx
  obtain ⟨hVT, hxV, hV1, hVE, hVP⟩ := gq_facts hx hx1 hηx
  have hL := lh_eq_lhT (Or.inr hx) hx1 hVT hxV hV1 hVP
  have hsq := lgLhT_sq hx hx1 hT h2 le_self_add
  exact le1R_of_le (le_mul_left _ hVE.pos) hsq hL.1

/-- `gq η x` lies below every next point above the base. -/
theorem gq_lt_next {η : Ordinal.{0}} (hηx : η < x) {u : Ordinal.{0}} (hxu : x < u) (hu : LtInf1 u) :
    gq η x < u := by
  obtain ⟨m, -, -, hmin, hTm, -⟩ := T_next (Or.inr hx) hx1
  obtain ⟨hT, -, h1, -, -⟩ := gq_facts hx hx1 hηx
  exact ((hTm _ h1).1 hT).trans_le (hmin u hxu hu)

end GQ

/-- **Lemma EXACT for `gq`**: `π_{σ,ρ}(ϑ^ρ(Ω₁·Ω₁ + η)) = ϑ^σ(Ω₁·Ω₁ + η)` for a constant `η < σ`. -/
theorem gq_pi {σ ρ η : Ordinal.{0}} (hB : Bases σ ρ) (hησ : η < σ) : gq η ρ ∈ TB ρ σ ∧ pi σ ρ (gq η ρ) = gq η σ := by
  obtain ⟨hσE, hρE, hσρ, hρ1⟩ := hB
  have hB' : Bases σ ρ := ⟨hσE, hρE, hσρ, hρ1⟩
  obtain ⟨hTB0, hpi0⟩ := lgPi_OmOm hB'
  obtain ⟨hTBs, hpis⟩ := pi_add hB' hTB0 (mem_TB_of_lt hB' hησ)
  rw [hpi0, pi_lt hB' hησ] at hpis
  have h2 := (gq_arg hρE hρ1 (hησ.trans hσρ)).2
  obtain ⟨hvT, -, -, -, hPar⟩ := vt_memTwo hρE hρ1 hTBs.1 h2
  refine ⟨⟨hvT, ?_⟩, ?_⟩
  · show ↑(Par ρ (vt ρ (Om1 * Om1 + η))) ⊆ Set.Iio σ
    rw [hPar]; exact hTBs.2
  · show pi σ ρ (vt ρ (Om1 * Om1 + η)) = vt σ (Om1 * Om1 + η)
    rw [pi_vt_two hB' hTBs h2, hpis]

theorem gq_lt_next_ups {η : Ordinal.{0}} (hη : GqCst η) {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) :
    gq η (upsilon l) < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have h1 : l < l + ω := lt_add_of_pos_right l omega0_pos
  have hτU := upsPt_upsilon (hl0.trans h1)
  exact (gq_lt_next (ups_inE hl) (ups_lt_Om1 l hl1) (hη _ (ups_inE hl)) (upsilon_normal.strictMono h1)
    hτU.2).trans (upsilon_normal.strictMono (lt_add_one _))

/-- **The limit hypothesis with an ordinal offset**: `η` a constant and `ϑˣ(Ω₁·Ω₁ + j) ≤ E_K(x) < ϑˣ(Ω₁·Ω₁ + η)` for
every `j < η`. -/
structure GqLimH (B : LpB) (η : Ordinal.{0}) : Prop where
  cst : GqCst η
  lo : ∀ x, InE x → x < Om1 → ∀ j, j < η → gq j x ≤ B.K.E x
  hi : ∀ x, InE x → x < Om1 → B.K.E x < gq η x

section Lim

variable {B : LpB} {η : Ordinal.{0}} (H : GqLimH B η)
include H

theorem gq_gP_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : ∀ n : ℕ, gP B n x < gq η x
  | 0 => H.hi x hx hx1
  | n + 1 => by
      obtain ⟨hgT, -, hg1, -⟩ := gP_facts B hx hx1 n
      obtain ⟨hkT, hk1⟩ := gq_cst hx hx1 (H.cst x hx)
      have ih := gq_gP_lt hx hx1 n
      have h := lgVt_lt_low hx hx1 hgT hg1 (mem_T_of_le hx hx1 zero_le) (hx.pos.trans hx1) hkT hk1 ih
        (hx.pos.trans (gq_facts hx hx1 (H.cst x hx)).2.1)
      rw [add_zero] at h
      exact h

/-- **`v < ϑˣ(Ω₁·Ω₁ + η)` iff `v < gP B n x` for some `n`.** -/
theorem gq_lt_iff {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    ∀ v, v < gq η x → ∃ n, v < gP B n x := by
  have hηx := H.cst x hx
  obtain ⟨hGT, -, hG1, -, -⟩ := gq_facts hx hx1 hηx
  obtain ⟨hkT, hk1⟩ := gq_cst hx hx1 hηx
  have hEP1 : B.K.E x < gP B 1 x := gP_lt_succ B hx hx1 0
  have hxE := Lx.lx_E_gt B.ek hx hx1
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
      have hξk : ξ < Om1 * Om1 + η :=
        lgLt_of_vt_lt hx hx1 hξT hξ2 hkT hk1 (by rw [hξv]; exact hηx.trans hxv) (by rw [hξv]; exact hv)
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
        obtain ⟨n1, hn1⟩ := IH _ hqr.1 (hqr.1.trans hv)
        obtain ⟨n2, hn2⟩ := IH _ hqr.2 (hqr.2.trans hv)
        refine ⟨max n1 n2 + 1, ?_⟩
        have hq' : ξ / Om1 < gP B (max n1 n2) x := hn1.trans_le (gP_mono B hx hx1 (le_max_left _ _))
        have hr' : ξ % Om1 < gP B (max n1 n2 + 1) x :=
          hn2.trans_le (gP_mono B hx hx1 ((le_max_right _ _).trans (Nat.le_succ _)))
        rw [← hξv, ← hdec]
        exact lp_lt_top B hx hx1 hqT hq' hrT hr1 hr'
      · have hje : Om1 * Om1 + (ξ - Om1 * Om1) = ξ := Ordinal.add_sub_cancel_of_le hξs
        have hjk : ξ - Om1 * Om1 < η := (add_lt_add_iff_left _).1 (by rw [hje]; exact hξk)
        obtain ⟨j, hj⟩ : ∃ j, j = ξ - Om1 * Om1 := ⟨_, rfl⟩
        have hvj : v = gq j x := by rw [← hξv, ← hje, ← hj]; rfl
        exact absurd (H.lo x hx hx1 j (hj ▸ hjk)) (not_le.2 (hvj ▸ hEv))
    · obtain ⟨L, rfl⟩ := indec_eq_opow hI
      have hL : L < ω ^ L := lt_of_le_of_ne (right_le_opow _ one_lt_omega0)
        (fun h => hvE' (by unfold InE; rw [← h]; exact h.symm))
      obtain ⟨n, hn⟩ := IH L hL (hL.trans hv)
      exact ⟨n, (gP_facts B hx hx1 n).2.2.2.opow_lt hn⟩
  · have hD : DecompR0 v := not_not.1 hI
    rcases hD with h0 | ⟨u1, u2, hu1, hu2, hsum⟩
    · exact absurd h0 (lt_of_le_of_lt zero_le hxv).ne'
    obtain ⟨n1, h1⟩ := IH u1 hu1 (hu1.trans hv)
    obtain ⟨n2, h2⟩ := IH u2 hu2 (hu2.trans hv)
    refine ⟨max n1 n2, ?_⟩
    rw [← hsum]
    exact (inE_indec (gP_facts B hx hx1 _).2.2.2).add_lt (h1.trans_le (gP_mono B hx hx1 (le_max_left _ _)))
      (h2.trans_le (gP_mono B hx hx1 (le_max_right _ _)))

/-- **No `ε`-number `a ∈ (E_K(x), ϑˣ(Ω₁·Ω₁ + η))` has `a ≤₁ a·a` in `R₁⁺`.** -/
theorem gq_not_le1R_sq {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {a : Ordinal.{0}} (haE : InE a)
    (hEa : B.K.E x < a) (hak : a < gq η x) : ¬ le1R a (a * a) := by
  intro hR
  have hxa : x < a := (Lx.lx_E_gt B.ek hx hx1).trans hEa
  obtain ⟨n, hn⟩ := gq_lt_iff H hx hx1 a hak
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 1 := by
    rcases n with _ | M
    · exact absurd hn (not_lt.2 hEa.le)
    · exact ⟨M, rfl⟩
  obtain ⟨hTT, -, hT1, -⟩ := gP_facts B hx hx1 (M + 1)
  have ha1 : a < Om1 := hn.trans hT1
  have haT : a ∈ Tset x := vz_T_down hx hx1 hTT hT1 hn.le
  obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 haT hxa.le ha1 (inE_indec haE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxa, by rw [hξv]; exact haE⟩
  obtain ⟨hq1, hrT, hr1, hdec⟩ := lu_split hx hx1 hξT hξ2 hΩξ
  have hqM : ξ / Om1 < gP B M x :=
    lp_quot hx hx1 M ξ hξT hξ2 (by rw [hξv]; exact hxa) (by rw [hξv]; exact haE) (by rw [hξv]; exact hEa)
      (by rw [hξv]; exact hn)
  obtain ⟨hMT, -, hM1, -⟩ := gP_facts B hx hx1 M
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

end Lim

/-- **The limit term system over the base**: all terms of `LpT B`, top `gq η = ϑˣ(Ω₁·Ω₁ + η)`. -/
noncomputable def gqUSys (B : LpB) (η : Ordinal.{0}) (H : GqLimH B η) : XtSys where
  Tm := LpT B
  val := LpT.val
  CB := LpT.CBt
  cs := LpT.cs
  cst := LpT.cst
  top := gq η
  cb_cst := fun _ _ h => LpT.cbt_cst h
  cb_iff := fun _ _ _ h hc => LpT.cbt_iff h hc
  val_cst := fun _ _ => rfl
  cb_cstI := fun _ _ h => h
  lt_top := fun l hl hl1 t hCB =>
    (LpT.lp_T (ups_inE hl) (ups_lt_Om1 l hl1) t hCB).2.trans (gq_gP_lt H (ups_inE hl) (ups_lt_Om1 l hl1) _)
  one_le_top := fun l hl hl1 =>
    one_le_iff_pos.2 (gq_facts (ups_inE hl) (ups_lt_Om1 l hl1) (H.cst _ (ups_inE hl))).2.2.2.1.pos
  rep := fun l hl hl1 v hv => by
    obtain ⟨n, hn⟩ := gq_lt_iff H (ups_inE hl) (ups_lt_Om1 l hl1) v hv
    obtain ⟨t, h1, -, h3⟩ :=
      lp_rep (upsPt_upsilon (pos_iff_ne_zero.2 hl.1)) (ups_lt_Om1 l hl1) (Lx.lxRep_ri B.ek hl hl1) n v hn
    exact ⟨t, h1, h3⟩
  top_lt := fun l hl hl1 => gq_lt_next_ups H.cst hl hl1
  pkg := fun _ hl hl1 _ hCB h1 R => LpGK.pkgLp R (Lx.lxRep_ri B.ek hl hl1) (Lx.lxBase_ri B.ek hl hl1 R) hCB h1
  rs := fun _ _ _ _ hCB => rsStep_Lp hCB
  uni_le := fun _ _ hσ hρ hB _ _ ht hu => LpT.uni_le hσ hρ hB ht hu
  small := fun t => by
    rcases lp_small t with h | h
    · exact Or.inl h
    · exact Or.inr fun x hx hx1 hc => h x hx hx1 hc

theorem gqUSys_top (B : LpB) (η : Ordinal.{0}) (H : GqLimH B η) (x : Ordinal.{0}) :
    (gqUSys B η H).top x = gq η x := rfl

namespace GqLK

variable {B : LpB} {η : Ordinal.{0}} (H : GqLimH B η) {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include H h

theorem gq_lt_δ : gq η ρ < δ :=
  (gq_lt_next (upsPt_inE h.ρU) h.ρ1 (H.cst _ (upsPt_inE h.ρU)) h.ρτ h.τU.2).trans h.τδ

/-- **The witness pair of the top `gq η`**: `f(gq η ρ) ∈ E` and `gq η (fρ) ≤ f(gq η ρ)`. -/
theorem gqTopWit : ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ gq η ρ ∈ W ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      (∃ e', f (gq η ρ) = ω ^ e' ∧ ω ^ f ρ ∣ e') ∧ gq η (f ρ) ≤ f (gq η ρ) := by
  classical
  have hρE := upsPt_inE h.ρU
  have hηρ := H.cst ρ hρE
  obtain ⟨-, hρG, -, hGE, hGI⟩ := gq_facts hρE h.ρ1 hηρ
  have hR0 := gq_le1R hρE h.ρ1 hηρ
  set G := gq η ρ with hG
  set P := G * G with hP
  have hGδ : G < δ := gq_lt_δ H h
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
  obtain ⟨WE, ZE, wE, hTE, hIE⟩ := B.K.top_wit ρ τ δ h
  have w5 : WZ ρ δ ({P + G, P, G + G, G} ∪ WE) (∅ ∪ ZE) := w4.union wE
  rw [Finset.empty_union] at w5
  refine ⟨{P + G, P, G + G, G} ∪ WE, ZE, w5, by simp, fun A f hW hZ C => ?_⟩
  have hGA : G ∈ A := hW (by simp)
  have hGGA : G + G ∈ A := hW (by simp)
  have hPA : P ∈ A := hW (by simp)
  have hPGA : P + G ∈ A := hW (by simp)
  have hWE : ↑WE ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hTA : B.K.sys.top ρ ∈ A := hWE (Finset.mem_coe.2 hTE)
  obtain ⟨hfE, hPge⟩ := GbK.gbImg h hGE hρG hGδ C hGA hGGA hPA hPGA
  have hyG : f ρ < f G := C.mono C.rho hGA hρG
  refine ⟨⟨f G, hfE.symm, opow_dvd_of_inE hfE hyG.le⟩, ?_⟩
  obtain ⟨hyE, hy1, -⟩ := h.vz_img_base C
  have hTρ : B.K.sys.top ρ = B.K.E ρ := Lx.lx_top B.ek hρE h.ρ1
  have hTy : B.K.sys.top (f ρ) = B.K.E (f ρ) := Lx.lx_top B.ek hyE hy1
  have hEG : B.K.E ρ < G := H.hi ρ hρE h.ρ1
  have hfEG : f (B.K.sys.top ρ) < f G := C.mono hTA hGA (by rw [hTρ]; exact hEG)
  have hEy : B.K.E (f ρ) < f G := by
    have := (hIE A f hWE hZ C).2
    rw [hTy] at this
    exact this.trans_lt hfEG
  by_cases hU : UpsPt (f G)
  · exact (gq_lt_next hyE hy1 (H.cst _ hyE) hyG hU.2).le
  · by_contra hlt
    push Not at hlt
    have hsrc1 : le1 G P := (h.lowδ _ _ hρG hPδ.le).2 hR0
    have hR1 : le1R (f G) (f P) := (C.sk _ (C.low _ hGA) hU _).1 (C.cov1 G hGA P hPA hsrc1)
    exact gq_not_le1R_sq H hyE hy1 hfE hEy hlt (le1R_of_le (le_mul_left _ hfE.pos) hPge hR1)

end GqLK

/-- **The limit layer over the base**: `gqUSys B η H` with top `ϑˣ(Ω₁·Ω₁ + η)`. -/
noncomputable def gqLim (B : LpB) (η : Ordinal.{0}) (H : GqLimH B η) : XtLay where
  sys := gqUSys B η H
  E := gq η
  top_eq := fun x hx hx1 => (gq_facts hx hx1 (H.cst x hx)).2.2.2.1.symm
  exp_dvd := fun x hx hx1 =>
    opow_dvd_of_inE (gq_facts hx hx1 (H.cst x hx)).2.2.2.1 (gq_facts hx hx1 (H.cst x hx)).2.1.le
  exp_lt := fun x hx hx1 => (gq_facts hx hx1 (H.cst x hx)).2.2.1
  top_gt := fun x hx hx1 => (gq_facts hx hx1 (H.cst x hx)).2.1
  top_lt_ups := fun x u hx hx1 hxu hu => gq_lt_next hx hx1 (H.cst x hx) hxu hu.2
  lt_top_E := fun x hx hx1 t ht => (LpT.lp_T hx hx1 t ht).2.trans (gq_gP_lt H hx hx1 _)
  exact := fun _ _ hσ hρ hB t ht => LpT.pi hσ hρ hB t ht
  exp_pi := fun σ _ _ _ hB => gq_pi hB (H.cst σ hB.1)
  top_wit := fun _ _ _ h => GqLK.gqTopWit H h

/-- **The new base package**: the limit layer. -/
noncomputable def gqLimB (B : LpB) (η : Ordinal.{0}) (H : GqLimH B η) : LpB where
  K := gqLim B η H
  ek := fun x hx hx1 => (gq_facts hx hx1 (H.cst x hx)).2.2.2.1
  mem := fun x hx hx1 => (gq_facts hx hx1 (H.cst x hx)).1

theorem gqLimB_E (B : LpB) (η : Ordinal.{0}) (H : GqLimH B η) (x : Ordinal.{0}) :
    (gqLimB B η H).K.E x = gq η x := rfl

/-- **The limit hypothesis passes to the new base with `η + 1`.** -/
theorem gqLimH_next (B : LpB) (η : Ordinal.{0}) (H : GqLimH B η) : GqLimH (gqLimB B η H) (η + 1) :=
  ⟨gqCst_succ H.cst,
    fun x hx hx1 j hj => gq_mono hx hx1 (H.cst x hx) (Order.lt_add_one_iff.1 hj),
    fun x hx hx1 => gq_lt hx hx1 (gqCst_succ H.cst x hx) (lt_add_one η)⟩

section Rel

variable {B : LpB} {η : Ordinal.{0}} (H : GqLimH B η)

/-- **The stage tops are terms of the limit system**, with gap `> 1`. -/
theorem gqLim_topIn (n : ℕ) : LyTopIn (gqUSys B η H) (lpSys B n) := by
  refine ⟨Lp.gTm n, fun x hx _ => ⟨(Lp.gTm_val (B := B) (upsPt_inE hx) n).1,
    (Lp.gTm_val (B := B) (upsPt_inE hx) n).2⟩,
    fun l hl hl1 => ?_⟩
  have hρE := ups_inE hl
  have hρ1 := ups_lt_Om1 l hl1
  have hE := (gP_facts B hρE hρ1 (n + 1)).2.2.2
  rw [lpSys_top, gqUSys_top]
  exact ((inE_indec hE).add_lt (gP_lt_succ B hρE hρ1 n) (lu_one_lt_E hE)).trans (gq_gP_lt H hρE hρ1 (n + 1))

/-- **The top of the base layer is a term of the limit system.** -/
theorem gqLim_topIn_K : LyTopIn (gqUSys B η H) B.K.sys := by
  refine ⟨LpT.tp, fun x hx hx1 => ⟨trivial, ?_⟩, fun l hl hl1 => ?_⟩
  · show B.K.E x = B.K.sys.top x
    rw [Lx.lx_top B.ek (upsPt_inE hx) hx1]
  · have hρE := ups_inE hl
    have hρ1 := ups_lt_Om1 l hl1
    have hG := (gq_facts hρE hρ1 (H.cst _ hρE)).2.2.2.1
    rw [gqUSys_top, Lx.lx_top B.ek hρE hρ1]
    exact (inE_indec hG).add_lt (H.hi _ hρE hρ1) (lu_one_lt_E hG)

theorem gqLim_topPkg : XtTopPkg (gqUSys B η H) := XtLay.topPkg (gqLim B η H)

/-- **`Λ^B = sup_n Λ⁺(lpSys B n) < Λ⁺(gqUSys B η H)`.** -/
theorem gqFam_lt_lim : (lpFam B).famSup < xtB1 (gqUSys B η H) := by
  refine lt_of_le_of_lt (Ordinal.iSup_le fun n => ?_) (lyLamLtB1 (gqLim_topPkg H))
  exact (lyLamGt (lpSys_topPkg n) (gqLim_topIn H n)).le

/-- **`Λ⁺(K) < Λ⁺(gqUSys B η H)`.** -/
theorem gqLim_gt_K : xtB1 B.K.sys < xtB1 (gqUSys B η H) :=
  lyB1_lt (gqLim_topPkg H) (XtLay.topPkg B.K) (gqLim_topIn_K H)

/-- **`O_{gqUSys} = O_{lpSys B n}` below `Λ⁺(lpSys B n)`.** -/
theorem gqLim_eq (n : ℕ) {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h : μ < xtB1 (lpSys B n)) :
    xtOrec (gqUSys B η H) μ = xtOrec (lpSys B n) μ :=
  lyEq (lpSys_topPkg n) (gqLim_topIn H n) hμ h

/-- **`O_{gqUSys} = O_K` below `Λ⁺(K)`.** -/
theorem gqLim_eq_K {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h : μ < xtB1 B.K.sys) :
    xtOrec (gqUSys B η H) μ = xtOrec B.K.sys μ :=
  lyEq (XtLay.topPkg B.K) (gqLim_topIn_K H) hμ h

end Rel

end Googology.Trans.PoR.InaccPsi.R2.Gb
