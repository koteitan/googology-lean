import Googology.Trans.PoR.InaccPsi.R2.LgLim
import Googology.Trans.PoR.InaccPsi.R2.CitedLg

/-!
# The limit top as a theta term: `lgG x = ϑˣ(Ω₁·Ω₁)`, its `R₁⁺`-reach, and the reaches below it

* `lgV x := ϑˣ(Ω₁·Ω₁)`, `lgV_facts`; `gT_lt_lgV` (**every `gT n x < ϑˣ(Ω₁·Ω₁)`**, by `lgVt_lt_low`);
  `lgV_eq` (**`ϑˣ(Ω₁·Ω₁) = lgG x = sup_n gT n x`**, by `lgLt_of_vt_lt` and `lgQuot_mem`); `lgG_facts`;
* `lgG_le1R` (**`lgG x ≤₁ lgG x · lgG x` in `R₁⁺`**, by `lgLhT_sq` and `lh_eq_lhT`);
* `lg_luL_lt_sq` (`luL a q + ζ < a·a` for `q, ζ < a ∈ E`), `lg_not_le1R_sq` (**no `ε`-number `a` with `x < a <
  lgG x` has `a ≤₁ a·a` in `R₁⁺`**: its reach is `luL a q + ζ` with `q = ξ/Ω₁ < a`, from `Lu.lu_lh_th` and
  `Lv.lv_lh_gen`).

Cited axioms: `R2.CitedLg` (`lgArg_mem`, `lgVt_lt_low`, `lgLt_of_vt_lt`, `lgQuot_mem`, `lgLhT_sq`).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order Lu

theorem lg_OmOm_lt {η : Ordinal.{0}} (hη1 : η < Om1) : Om1 * Om1 + η < OmTwo :=
  isPrincipal_add_omega 2 (isPrincipal_mul_omega 2 Om1_lt_OmTwo Om1_lt_OmTwo) (hη1.trans Om1_lt_OmTwo)

theorem lg_Om1_le_OmOm : Om1 ≤ Om1 * Om1 := le_mul_left _ (Ordinal.omega_pos 1)

/-- `ϑˣ(Ω₁·Ω₁)`. -/
noncomputable def lgV (x : Ordinal.{0}) : Ordinal.{0} := vt x (Om1 * Om1)

theorem lgG_inE (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : InE (lgG x) := by
  unfold InE lgG
  rw [(isNormal_opow one_lt_omega0).map_iSup Ordinal.bddAbove_of_small]
  congr 1
  funext n
  exact (gT_facts hx hx1 n).2.2.2

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem lgV_arg : Om1 * Om1 ∈ Tset x := by
  have := lgArg_mem hx hx1 (mem_T_of_le hx hx1 zero_le) (Ordinal.omega_pos 1)
  rwa [add_zero] at this

theorem lgV_facts : lgV x ∈ Tset x ∧ x < lgV x ∧ lgV x < Om1 ∧ InE (lgV x) ∧ Indec (lgV x) := by
  have hT := lgV_arg hx hx1
  have h2 : Om1 * Om1 < OmTwo := by simpa using lg_OmOm_lt (Ordinal.omega_pos 1)
  obtain ⟨h1, -, h3, h4, -⟩ := vt_memTwo hx hx1 hT h2
  obtain ⟨h5, h6⟩ := (vt_E_iff hx hx1 hT h2).2 lg_Om1_le_OmOm
  exact ⟨h1, h5, h3, h6, h4⟩

omit hx hx1 in
theorem lgV_add_zero : vt x (Om1 * Om1 + 0) = lgV x := by rw [add_zero]; rfl

/-- **Every `gT n x` is below `ϑˣ(Ω₁·Ω₁)`.** -/
theorem gT_lt_lgV : ∀ n : ℕ, gT n x < lgV x := by
  have h0T := mem_T_of_le hx hx1 (zero_le : (0 : Ordinal.{0}) ≤ x)
  have h1x : (1 : Ordinal.{0}) < x := lu_one_lt_E hx
  have hV0 : (0 : Ordinal.{0}) < lgV x := (lgV_facts hx hx1).2.2.2.1.pos
  intro n
  induction n with
  | zero =>
    rw [show gT 0 x = eN x from rfl, ← lvg_eN_eq hx hx1, ← lgV_add_zero]
    refine lgVt_lt_low hx hx1 (mem_T_of_le hx hx1 h1x.le) (h1x.trans hx1) h0T (Ordinal.omega_pos 1) h0T
      (Ordinal.omega_pos 1) ?_ ?_
    · rw [lgV_add_zero]; exact h1x.trans (lgV_facts hx hx1).2.1
    · rw [lgV_add_zero]; exact hV0
  | succ n ih =>
    obtain ⟨hT, -, h1, -⟩ := gT_facts hx hx1 n
    rw [show gT (n + 1) x = vt x (Om1 * gT n x + 0) by rw [add_zero]; rfl, ← lgV_add_zero]
    refine lgVt_lt_low hx hx1 hT h1 h0T (Ordinal.omega_pos 1) h0T (Ordinal.omega_pos 1) ?_ ?_
    · rw [lgV_add_zero]; exact ih
    · rw [lgV_add_zero]; exact hV0

theorem lgG_le_lgV : lgG x ≤ lgV x := lgG_le fun n => (gT_lt_lgV hx hx1 n).le

theorem lgG_indec : Indec (lgG x) := by
  rw [indec_iff]
  refine ⟨(lgG_pos hx hx1).ne', fun a b ha hb => ?_⟩
  obtain ⟨n, hn⟩ := lt_lgG_iff.1 ha
  obtain ⟨m, hm⟩ := lt_lgG_iff.1 hb
  have hE := (gT_facts hx hx1 (max n m)).2.2.2
  have h1 : a < gT (max n m) x := hn.trans_le (gT_mono hx hx1 (le_max_left n m))
  have h2 : b < gT (max n m) x := hm.trans_le (gT_mono hx hx1 (le_max_right n m))
  exact ((inE_indec hE).add_lt h1 h2).trans (gT_lt_lgG hx hx1 _)

/-- **`ϑˣ(Ω₁·Ω₁) ≤ lgG x`.** -/
theorem lgV_le_lgG : lgV x ≤ lgG x := by
  by_contra hlt
  push Not at hlt
  obtain ⟨hVT, hxV, hV1, -, -⟩ := lgV_facts hx hx1
  have h0T := mem_T_of_le hx hx1 (zero_le : (0 : Ordinal.{0}) ≤ x)
  have hGT : lgG x ∈ Tset x := vz_T_down hx hx1 hVT hV1 hlt.le
  have hxG : x < lgG x := (gT_facts hx hx1 0).2.1.trans (gT_lt_lgG hx hx1 0)
  have hG1 : lgG x < Om1 := hlt.trans hV1
  have hGE := lgG_inE x hx hx1
  obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 hGT hxG.le hG1 (lgG_indec hx hx1)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxG, by rw [hξv]; exact hGE⟩
  have hξΩ : ξ < Om1 * Om1 := by
    have := lgLt_of_vt_lt hx hx1 hξT hξ2 h0T (Ordinal.omega_pos 1) (by rw [hξv]; exact hGE.pos)
      (by rw [hξv, lgV_add_zero]; exact hlt)
    rwa [add_zero] at this
  obtain ⟨hq1, hrT, hr1, hdec⟩ := lu_split hx hx1 hξT hξ2 hΩξ
  have hqT := lgQuot_mem hx hx1 hξT hξΩ
  have hqΩ : ξ / Om1 < Om1 := (Ordinal.lt_mul_iff_div_lt (Ordinal.omega_pos 1).ne').1 hξΩ
  set q := ξ / Om1 with hq
  set r := ξ % Om1 with hr
  have hv : vt x (Om1 * q + r) = lgG x := by rw [hdec, hξv]
  -- `q, r < lgG x`
  have hqr : q < lgG x ∧ r < lgG x := by
    rcases lt_or_ge q x with hqx | hxq
    · obtain ⟨-, -, -, -, -, -, -, hrv⟩ := lu_th_facts hx hx1 hq1 hqx hrT hr1
      rw [hv] at hrv
      exact ⟨hqx.trans hxG, hrv⟩
    · obtain ⟨-, -, -, -, -, -, -, hqv, hrv⟩ := Lv.gen_facts hx hx1 hqT hxq hqΩ hrT hr1
      rw [hv] at hqv hrv
      exact ⟨hqv, hrv⟩
  obtain ⟨n, hn⟩ := lt_lgG_iff.1 hqr.1
  obtain ⟨m, hm⟩ := lt_lgG_iff.1 hqr.2
  have hqN : q < gT (max n m) x := hn.trans_le (gT_mono hx hx1 (le_max_left n m))
  have hrN : r < gT (max n m + 1) x :=
    hm.trans_le (gT_mono hx hx1 ((le_max_right n m).trans (Nat.le_succ _)))
  have h := lvg_lt_top hx hx1 hqT hqN hrT hr1 hrN
  rw [hv] at h
  exact absurd (gT_lt_lgG hx hx1 (max n m + 1)) (not_lt.2 h.le)

/-- **`ϑˣ(Ω₁·Ω₁) = lgG x = sup_n gT n x`.** -/
theorem lgV_eq : lgV x = lgG x := le_antisymm (lgV_le_lgG hx hx1) (lgG_le_lgV hx hx1)

theorem lgG_facts : lgG x ∈ Tset x ∧ x < lgG x ∧ lgG x < Om1 ∧ InE (lgG x) ∧ Indec (lgG x) := by
  rw [← lgV_eq hx hx1]; exact lgV_facts hx hx1

/-- **`lgG x ≤₁ lgG x · lgG x` in `R₁⁺`.** -/
theorem lgG_le1R : le1R (lgG x) (lgG x * lgG x) := by
  obtain ⟨hVT, hxV, hV1, hVE, hVP⟩ := lgV_facts hx hx1
  have h2 : Om1 * Om1 < OmTwo := by simpa using lg_OmOm_lt (Ordinal.omega_pos 1)
  have hL := lh_eq_lhT (Or.inr hx) hx1 hVT hxV hV1 hVP
  have hsq := lgLhT_sq hx hx1 (lgV_arg hx hx1) h2 le_rfl
  rw [← lgV_eq hx hx1]
  exact le1R_of_le (le_mul_left _ hVE.pos) hsq hL.1

end Base

/-- `luL a q + ζ < a·a` for `q < a`, `ζ < a`, `a ∈ E`. -/
theorem lg_luL_lt_sq {a q ζ : Ordinal.{0}} (ha : InE a) (hq : q < a) (hζ : ζ < a) : luL a q + ζ < a * a := by
  have ha0 : 0 < a := ha.pos
  have hωa : ω ≤ a := (lu_omega_lt_E ha).le
  by_cases hqω : q < ω
  · refine (lu_luL_fin_lt hqω hζ).trans_le ?_
    rw [← mul_add_one, ← mul_add_one]
    refine mul_le_mul_right ?_ a
    obtain ⟨n, rfl⟩ := lt_omega0.1 hqω
    have : ((n : Ordinal.{0}) + 1 + 1) = ((n + 2 : ℕ) : Ordinal.{0}) := by
      push_cast; rw [add_assoc, one_add_one_eq_two]
    rw [this]; exact (natCast_lt_omega0 _).le.trans hωa
  · push Not at hqω
    refine (lu_luL_inf_lt ha hqω hq hζ).trans_le ?_
    rw [← mul_add_one]
    exact mul_le_mul_right (add_one_le_of_lt hq) a

section Base2

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **No `ε`-number `a` with `x < a < lgG x` has `a ≤₁ a·a` in `R₁⁺`.** -/
theorem lg_not_le1R_sq {a : Ordinal.{0}} (haE : InE a) (hxa : x < a) (haG : a < lgG x) : ¬ le1R a (a * a) := by
  intro hR
  obtain ⟨n, hn⟩ := lt_lgG_iff.1 haG
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 1 := by
    rcases n with _ | M
    · exact absurd (eN_le hxa haE) (not_le.2 hn)
    · exact ⟨M, rfl⟩
  obtain ⟨hTT, -, hT1, -⟩ := gT_facts hx hx1 (M + 1)
  have ha1 : a < Om1 := hn.trans hT1
  have haT : a ∈ Tset x := vz_T_down hx hx1 hTT hT1 hn.le
  obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 haT hxa.le ha1 (inE_indec haE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxa, by rw [hξv]; exact haE⟩
  obtain ⟨hq1, hrT, hr1, hdec⟩ := lu_split hx hx1 hξT hξ2 hΩξ
  have hqM : ξ / Om1 < gT M x :=
    lvg_quot hx hx1 M ξ hξT hξ2 (by rw [hξv]; exact hxa) (by rw [hξv]; exact haE) (by rw [hξv]; exact hn)
  obtain ⟨hMT, -, hM1, -⟩ := gT_facts hx hx1 M
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

end Base2

end Googology.Trans.PoR.InaccPsi.R2
