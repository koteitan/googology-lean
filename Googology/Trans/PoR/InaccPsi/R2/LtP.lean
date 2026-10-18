import Googology.Trans.PoR.InaccPsi.R2.LtNS

/-!
# The top `ltP = sup_K c_K = ϑ(Ω₁·(ω+1))` of `lnSw`, its IMG package, and BLK^O up to `Λ⁺(lnSw)`

For a base `x ∈ E ∩ Ω₁` (`c_0 = y_ω`, `c_{K+1} = ϑˣ(Ω₁·ω + c_K)`, `ltP x = sup_K c_K(x)`, `R2.LtNS`):

* `lt_w1_facts`, `ltP_eq` (**`sup_K c_K(x) = ϑˣ(Ω₁·(ω+1))`**: `<` termwise by [W07a] Lemma 3.30 at `Ω₁·(ω+1)`
  (`ltVt_lt_w1`); a smaller value `ϑˣ(ξ)` has `ξ < Ω₁·(ω+1)` (`ltLt_of_vt_lt_w1`), so `ξ = Ω₁·q + r` (not a value of
  `φ_{q+1}`) or `ξ = Ω₁·ω + r` with `r < ϑˣ(ξ)` (`ltLt_vt_self_w`), and then `ϑˣ(ξ) ≤ c_{K+1}`), `ltP_lh`
  (**`lh(ϑˣ(Ω₁·(ω+1))) = ϑˣ(Ω₁·(ω+1))·ω + ϑˣ(Ω₁·(ω+1))`**: [W07b] Theorem 5.3 with the cited `ltLhT_w1`);
* `lt_w_ub0` (`ϑˣ(Ω₁·ω + σ) ≤ φ_ω(x + σ + 1)`), `ltC_lt_fix`, `ltP_le_fix` (**`sup_K c_K(x)` is below every fixed
  point `u > x` of `φ_ω`**), `lt_le1R_fix_w` (**`α ≤₁ α·ω + α` in `R₁⁺` gives `φ_ω(α) = α`**: `lt_le1R_copy_w`,
  `lt_le1R_ge_w`);
* `LpK.ltWitP`, `LpK.ltP_pkg` (**the IMG package of `ltP`**: a covering copy maps `v ≤₁ v·ω + v` to
  `f(v) ≤₁ f(v)·ω + f(v)`, so `f(v)` is a fixed point of `φ_ω` above `f(ρ)`), `lnSw_topPkg`;
* `ltC_lt_B1` (**`Λ_C⁺ < Λ⁺(lnSw)`**), `ltReachP` (**the exact reach at `Λ_C⁺`: `lh(ρ) = δ + ϑᵖ(Ω₁·(ω+1))`**),
  `lnSw_reach`, `lnSw_blk` (**BLK^O below `υ_{Λ⁺(lnSw)}`**), `lnSw_eqS`, `lnSw_init`, `lnSw_capV`, `lnSw_capAt`,
  `lnSw_iff`, `lnSw_iso`, `lnSw_fix_code`, `lnSw_of_cp`, `lnSwRoad3`, `lnSwRoad`, `lnSwRoad_cap`.

New axioms: `ltLt_vt_self_w`, `ltVt_lt_w1`, `ltLt_of_vt_lt_w1`, `ltLhT_w1` of `R2.CitedLt` (and `ltLhT_w_lim`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lt

open Ordinal Order Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Lz LnW

/-- **`α ≤₁ α·ω + α` in `R₁⁺` gives `φ_ω(α) = α`** (`α > 0`). -/
theorem lt_le1R_fix_w {a : Ordinal.{0}} (ha : 0 < a) (h : le1R a (a * ω + a)) : veblen ω a = a := by
  have hz : ∀ z, z < a → le1R a (a * ω + z) := fun z hz =>
    le1R_of_le ((lt_le_mul_w a).trans le_self_add) (add_le_add le_rfl hz.le) h
  have haP := vz_le1R_omega ha (lt_le1R_w_base h)
  have hE : InE a := vz_omega_E haP
  have h1a : (1 : Ordinal.{0}) < a := one_lt_omega0.trans (omega0_lt_inE hE)
  obtain ⟨e, he0, hea, he⟩ := lt_le1R_copy_w (hz 1 h1a) zero_lt_one ha ha
  rw [add_zero] at he
  obtain ⟨i', hi'⟩ := vz_le1R_omega he0 he
  have hle : ∀ j, j < a → veblen ω j ≤ a := fun j hj =>
    ((veblen_le_veblen_iff_right).2 ((right_le_opow j one_lt_omega0).trans le_add_self)).trans
      (lt_le1R_ge_w j a i' hj (by rw [hi']; exact hea) (hz j hj))
  refine le_antisymm ?_ (right_le_veblen _ _)
  rw [(isNormal_veblen ω).apply_of_isSuccLimit (ev_isSuccLimit_of_inE hE)]
  exact Ordinal.iSup_le (fun j => hle j.1 j.2)

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem lt_w1_arg : Om1 * (ω + 1) ∈ Tset x ∧ Om1 * (ω + 1) < OmTwo := by
  rw [mul_add_one]
  exact ⟨vzT_add hx hx1 (vzOm1w_T hx hx1) (Om1_T hx hx1), isPrincipal_add_omega 2 vzOm1w_lt Om1_lt_OmTwo⟩

/-- The facts on `ϑˣ(Ω₁·(ω+1))`. -/
theorem lt_w1_facts :
    vt x (Om1 * (ω + 1)) ∈ Tset x ∧ x < vt x (Om1 * (ω + 1)) ∧ vt x (Om1 * (ω + 1)) < Om1 ∧
      InE (vt x (Om1 * (ω + 1))) ∧ Indec (vt x (Om1 * (ω + 1))) := by
  obtain ⟨hT, h2⟩ := lt_w1_arg hx hx1
  obtain ⟨hvT, -, hv1, hvP, -⟩ := vt_memTwo hx hx1 hT h2
  have hΩ : Om1 ≤ Om1 * (ω + 1) := by
    calc Om1 = Om1 * 1 := (mul_one _).symm
      _ ≤ Om1 * (ω + 1) := mul_le_mul_right (one_le_iff_pos.2 (lt_of_le_of_lt zero_le (lt_add_one _))) Om1
  have hE := (vt_E_iff hx hx1 hT h2).2 hΩ
  exact ⟨hvT, hE.1, hv1, hE.2, hvP⟩

/-- **`sup_K c_K(x) = ϑˣ(Ω₁·(ω+1))`.** -/
theorem ltP_eq : ltP x = vt x (Om1 * (ω + 1)) := by
  obtain ⟨hQT, -, hQ1, hQE, -⟩ := lt_w1_facts hx hx1
  have hω := lt_omega_T hx hx1
  have hc : ∀ K, ltC x K < vt x (Om1 * (ω + 1)) := by
    intro K
    induction K with
    | zero =>
      show lzYw x < _
      rw [ltYw_eq hx hx1]
      exact ltVt_lt_w1 hx hx1 hω.1 hω.2 (omega0_lt_inE hQE)
    | succ K ih => exact ltVt_lt_w1 hx hx1 (ltC_facts hx hx1 K).1 (ltC_facts hx hx1 K).2.1 ih
  refine le_antisymm (Ordinal.iSup_le fun K => (hc K).le) ?_
  by_contra hlt
  push Not at hlt
  have hPω := ltP_omega hx hx1
  have hPE : InE (ltP x) := vz_omega_E hPω
  have hP1 : ltP x < Om1 := hlt.trans hQ1
  have hPT : ltP x ∈ Tset x := vz_T_down hx hx1 hQT hQ1 hlt.le
  have hxP : x < ltP x := (ltC_facts hx hx1 0).2.2.1.trans (ltC_lt_P hx hx1 0)
  obtain ⟨ξ, hξT, hξ2, hξP⟩ := vt_rep hx hx1 hPT hxP.le hP1 (inE_indec hPE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξP]; exact hxP, by rw [hξP]; exact hPE⟩
  have hξlt : ξ < Om1 * (ω + 1) := ltLt_of_vt_lt_w1 hx hx1 hξT hξ2 (by rw [hξP]; exact hlt)
  rcases lt_or_ge ξ (Om1 * ω) with hξω | hωξ
  · obtain ⟨hdec, hr1⟩ := vz_div_Om1 ξ
    set q := ξ / Om1 with hq
    set r := ξ % Om1 with hr
    have hqw : q < ω := by
      have h1 : Om1 * q < Om1 * ω := lt_of_le_of_lt (hdec ▸ le_self_add) hξω
      exact (mul_lt_mul_iff_right₀ (Ordinal.omega_pos 1)).1 h1
    obtain ⟨q', hq'⟩ := lt_omega0.1 hqw
    have hq'1 : 1 ≤ q' := by
      rcases Nat.eq_zero_or_pos q' with h0 | h0
      · exfalso
        rw [h0, Nat.cast_zero] at hq'
        rw [hq', mul_zero, zero_add] at hdec
        exact absurd (hdec ▸ hr1) (not_lt.2 hΩξ)
      · exact h0
    have hrT : r ∈ Tset x := vzRem_T hx hx1 hξT hξ2 hdec.symm (dvd_mul_right _ _) hr1
    have e : Om1 * (q' : Ordinal.{0}) + r = ξ := by rw [← hq']; exact hdec
    have hnot := vz_th_notP hx hx1 hq'1 hrT hr1
    rw [e, hξP] at hnot
    exact hnot (vz_omega_P hPω q')
  · have hξe : Om1 * ω + (ξ - Om1 * ω) = ξ := Ordinal.add_sub_cancel_of_le hωξ
    have hr1 : ξ - Om1 * ω < Om1 := by
      rw [mul_add_one] at hξlt
      exact (add_lt_add_iff_left _).1 (by rw [hξe]; exact hξlt)
    have hrT : ξ - Om1 * ω ∈ Tset x :=
      vzRem_T hx hx1 hξT hξ2 hξe.symm (dvd_mul_right Om1 ω) hr1
    have hrP : ξ - Om1 * ω < ltP x := by
      have := ltLt_vt_self_w hx hx1 hrT hr1
      rwa [hξe, hξP] at this
    obtain ⟨K, hK⟩ := ltP_lt_iff.1 hrP
    obtain ⟨hcT, hc1, -, -⟩ := ltC_facts hx hx1 K
    have h1 := ltn_mono_le hx hx1 hrT hcT hc1 (ltC_step hx hx1 K).1 hK.le
    rw [hξe, hξP, ← ltC_succ] at h1
    exact absurd (h1.trans_lt (ltC_lt_P hx hx1 (K + 1))) (lt_irrefl _)

/-- **The `R₁⁺`-reach of `ϑˣ(Ω₁·(ω+1))`**: `lh = ϑˣ(Ω₁·(ω+1))·ω + ϑˣ(Ω₁·(ω+1))`. -/
theorem ltP_lh : IsLh1 (ltP x) (ltP x * ω + ltP x) := by
  obtain ⟨hvT, hxv, hv1, -, hvP⟩ := lt_w1_facts hx hx1
  have h := lh_eq_lhT (Or.inr hx) hx1 hvT hxv hv1 hvP
  rw [ltLhT_w1 hx hx1] at h
  rw [ltP_eq hx hx1]
  exact h

/-- `ϑˣ(Ω₁·ω + σ) ≤ φ_ω(x + σ + 1)`. -/
theorem lt_w_ub0 : ∀ σ, σ ∈ Tset x → σ < Om1 → vt x (Om1 * ω + σ) ≤ veblen ω (x + σ + 1) := by
  intro σ
  induction σ using WellFoundedLT.induction with
  | ind σ IHσ =>
  intro hσT hσ1
  refine lt_w_min hx hx1 hσT hσ1 ⟨_, rfl⟩ ?_ ?_ (fun σ' hσ' => ?_)
  · exact lt_of_lt_of_le (lt_of_le_of_lt le_self_add (lt_add_one _)) (right_le_veblen _ _)
  · exact lt_of_lt_of_le (lt_of_le_of_lt le_add_self (lt_add_one _)) (right_le_veblen _ _)
  · have hσ'T : σ' ∈ Tset x := vz_T_down hx hx1 hσT hσ1 hσ'.le
    refine lt_of_le_of_lt (IHσ σ' hσ' hσ'T (hσ'.trans hσ1)) ((veblen_lt_veblen_iff_right).2 ?_)
    rw [add_assoc, add_assoc]
    exact (add_lt_add_iff_left x).2 ((add_one_le_of_lt hσ').trans_lt (lt_add_one σ))

/-- Every `c_K(x)` lies below every fixed point `u > x` of `φ_ω`. -/
theorem ltC_lt_fix {u : Ordinal.{0}} (hu : veblen ω u = u) (hxu : x < u) : ∀ K, ltC x K < u := by
  have huE : InE u := vz_omega_E ⟨u, hu⟩
  have huI := inE_indec huE
  have hb : ∀ σ, σ ∈ Tset x → σ < Om1 → σ < u → vt x (Om1 * ω + σ) < u := fun σ hσT hσ1 hσu =>
    (lt_w_ub0 hx hx1 σ hσT hσ1).trans_lt (by
      have := (veblen_lt_veblen_iff_right (o := ω)).2
        (huI.add_lt (huI.add_lt hxu hσu) (one_lt_omega0.trans (omega0_lt_inE huE)))
      rwa [hu] at this)
  intro K
  induction K with
  | zero =>
    show lzYw x < u
    rw [ltYw_eq hx hx1]
    exact hb ω (lt_omega_T hx hx1).1 (lt_omega_T hx hx1).2 (omega0_lt_inE huE)
  | succ K ih => exact hb _ (ltC_facts hx hx1 K).1 (ltC_facts hx hx1 K).2.1 ih

/-- **`sup_K c_K(x)` is below every fixed point `u > x` of `φ_ω`.** -/
theorem ltP_le_fix {u : Ordinal.{0}} (hu : veblen ω u = u) (hxu : x < u) : ltP x ≤ u :=
  Ordinal.iSup_le fun K => (ltC_lt_fix hx hx1 hu hxu K).le

end Base

/-! ## The IMG package of `ltP` -/

namespace LpK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

theorem ltP_lt_δ : ltP ρ < δ := (ltP_le_next h.ρE h.ρ1 h.ρτ h.τU.2).trans_lt h.τδ

/-- **The witness sets of `ltP(ρ)`**: every covering copy `f` has `ltP(f(ρ)) ≤ f(ltP(ρ))`. -/
theorem ltWitP : ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ ltP ρ ∈ W ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      ltP (f ρ) ≤ f (ltP ρ) := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hvE : InE (ltP ρ) := vz_omega_E (ltP_omega hρE hρ1)
  have hvI := inE_indec hvE
  have hρv : ρ < ltP ρ := (ltC_facts hρE hρ1 0).2.2.1.trans (ltC_lt_P hρE hρ1 0)
  have hvδ : ltP ρ < δ := ltP_lt_δ h
  have hvwδ : ltP ρ * ω < δ := vz_mul_omega_lt h.δE hvδ
  have hδI := inE_indec h.δE
  have hvwvδ : ltP ρ * ω + ltP ρ < δ := hδI.add_lt hvwδ hvδ
  have hvw := lt_le_mul_w (ltP ρ)
  have hvpos : 0 < ltP ρ := lt_of_le_of_lt zero_le hρv
  have hvwlt : ltP ρ * ω < ltP ρ * ω + ltP ρ := lt_add_of_pos_right _ hvpos
  have hvlt : ltP ρ < ltP ρ * ω + ltP ρ := hvw.trans_lt hvwlt
  have hsrc : le1 (ltP ρ) (ltP ρ * ω + ltP ρ) := (h.lowδ _ _ hρv hvwvδ.le).2 (ltP_lh hρE hρ1).1
  have hwI : Indec (ltP ρ * ω) := by
    have e2 : ltP ρ * ω = ω ^ (ltP ρ + 1) := by rw [opow_add, opow_one, show ω ^ ltP ρ = ltP ρ from hvE]
    rw [e2]; exact indec_opow _
  have w1 := (WZ.empty (ρ := ρ) (δ := δ)).insW hρv.le hvδ (Or.inl hvI)
  have w2 := w1.insW (hρv.le.trans hvw) hvwδ (Or.inl hwI)
  have w3 := w2.insW (hρv.le.trans (hvw.trans le_self_add)) hvwvδ
    (Or.inr ⟨ltP ρ * ω, by simp, ltP ρ, by simp, hvwlt, hvlt, rfl⟩)
  refine ⟨_, _, w3, by simp, fun A f hW _ C => ?_⟩
  have hvA : ltP ρ ∈ A := hW (by simp)
  have hvwA : ltP ρ * ω ∈ A := hW (by simp)
  have hvwvA : ltP ρ * ω + ltP ρ ∈ A := hW (by simp)
  have hyE := upsPt_inE C.ups
  have hy1 : f ρ < Om1 := (C.low ρ C.rho).trans hρ1
  have hyv : f ρ < f (ltP ρ) := C.mono C.rho hvA hρv
  by_cases hU : UpsPt (f (ltP ρ))
  · exact ltP_le_next hyE hy1 hyv hU.2
  have himg : le1 (f (ltP ρ)) (f (ltP ρ * ω) + f (ltP ρ)) := by
    have := C.cov1 _ hvA _ hvwvA hsrc
    rwa [← C.add _ hvwA _ hvA _ hvwvA rfl] at this
  have hR := (C.sk _ (C.low _ hvA) hU _).1 himg
  have haddv : f (ltP ρ) + f (ltP ρ * ω) = f (ltP ρ * ω) :=
    C.add _ hvA _ hvwA _ hvwA (add_eq_right_iff_mul_omega0_le.2 le_rfl)
  have hge : f (ltP ρ) * ω ≤ f (ltP ρ * ω) := add_eq_right_iff_mul_omega0_le.1 haddv
  have hR2 : le1R (f (ltP ρ)) (f (ltP ρ) * ω + f (ltP ρ)) :=
    le1R_of_le ((lt_le_mul_w _).trans le_self_add) (add_le_add hge le_rfl) hR
  exact ltP_le_fix hyE hy1 (lt_le1R_fix_w (lt_of_le_of_lt zero_le hyv) hR2) hyv

/-- **The IMG package of `ltP`.** -/
theorem ltP_pkg : ImgPkg ρ δ ltP := by
  obtain ⟨W, Z, hw, hvW, hI⟩ := ltWitP h
  have hpos : 0 < ltP ρ := lt_of_le_of_lt zero_le ((ltC_facts h.ρE h.ρ1 0).2.2.1.trans (ltC_lt_P h.ρE h.ρ1 0))
  exact ⟨one_le_iff_pos.2 hpos, ltP_lt_δ h, W, Z, hw, Finset.mem_union_left _ hvW, hI⟩

end LpK

theorem lnSw_top (x : Ordinal.{0}) : lnSw.top x = ltP x := rfl

/-- **The top `ϑ(Ω₁·(ω+1))` of `lnSw` has an IMG package.** -/
theorem lnSw_topPkg : XtTopPkg lnSw := fun _ _ _ R => LpK.ltP_pkg R

theorem lnSw_lamLtB1 : xtLam lnSw < xtB1 lnSw := lyLamLtB1 lnSw_topPkg

/-- **`Λ_C⁺ < Λ⁺(lnSw)`.** -/
theorem ltC_lt_B1 : lnFam.famSup < xtB1 lnSw := by
  rw [← lnSw_lam]; exact lnSw_lamLtB1

/-- **The exact reach at `Λ_C⁺`**: `lh(ρ) = δ + ltP(ρ)`. -/
theorem ltReachP :
    IsReach R2C (upsilon lnFam.famSup) (upsilon (lnFam.famSup + ω + 1) + ltP (upsilon lnFam.famSup)) := by
  rw [← ln_atSup]
  exact xtReach1 lnSw_topPkg ln_sup_ri ltC_lt_B1

/-- **The exact reach at `Λ_C⁺`** with `ltP(ρ) = ϑᵖ(Ω₁·(ω+1))`. -/
theorem ltReachP_vt :
    IsReach R2C (upsilon lnFam.famSup)
      (upsilon (lnFam.famSup + ω + 1) + vt (upsilon lnFam.famSup) (Om1 * (ω + 1))) := by
  rw [← ltP_eq (ups_inE ln_sup_ri) (ups_lt_Om1 _ lnFam.famSup_lt_Om1)]
  exact ltReachP

/-- **`O = O_k` below `Λ⁺(lnS (k+1))`.** -/
theorem lnSw_eqS (k : ℕ) {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h : μ < xtB1 (lnS (k + 1))) :
    xtOrec lnSw μ = xtOrec (lnS (k + 1)) μ :=
  lyEq (lnS_topPkg (k + 1)) (lnChain.inX k) hμ h

theorem lnSw_nonfix : XtNonfix (xtOrec lnSw) (xtB1 lnSw) :=
  fun _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 lnSw_topPkg))

/-- **The exact reach of every restart below `Λ⁺(lnSw)`**: `lh(ρ_λ) = δ_λ + O(λ)`. -/
theorem lnSw_reach {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < xtB1 lnSw) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec lnSw l) :=
  xtReach1 lnSw_topPkg hl hlB

/-- **Theorem BLK^O below `υ_{Λ⁺(lnSw)}`** in `R₂^C`. -/
theorem lnSw_blk :
    (∀ c d, c < d → d < upsilon (xtB1 lnSw) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 lnSw ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 lnSw →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec lnSw l)) ∧
    (∀ α < upsilon (xtB1 lnSw), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  xtBlk1 lnSw_topPkg


variable {S : InaccSeq.{0}}

/-- **UPPER and LOWER at every restart of the range below `Λ⁺(lnSw)` that is not a fixed point of `υ`.** -/
theorem lnSw_init {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lnSw) (hfix : l < upsilon l) :
    CdUpper S l ∧ CdLower S l :=
  xtInit (xtSpec1 lnSw_topPkg) lnSw_nonfix hr hl hfix

/-- **The cap of the values at every non-fixed restart of the range below `Λ⁺(lnSw)`.** -/
theorem lnSw_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lnSw) (hfix : l < upsilon l) :
    CdCapV S l := by
  have hww := cp_ww_lt_B0.trans_le hr.2.1
  exact xtCapV_nonfix (xtSpec1 lnSw_topPkg) hr.1 hww hfix hl (cp_name_L hr.2.2.1)
    (lnSw_nonfix l hr.1 hww hfix hl)

theorem lnSw_capAt {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hB : cdB0 ≤ l) (hlΛ : l < xtB1 lnSw)
    (hfix : l < upsilon l) (hname : upsilon l < Pv S η1) : CdCapAt S l := by
  have hww := cp_ww_lt_B0.trans_le hB
  exact xtCapAt_nonfix (xtSpec1 lnSw_topPkg) hl hww hfix hlΛ hname (lnSw_nonfix l hl hww hfix hlΛ)

/-- **Below `Λ⁺(lnSw)`, ENUM-REACH is the equation `Θ_λ(m_λ) = O(λ)`.** -/
theorem lnSw_iff {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < xtB1 lnSw) :
    (CdUpper S l ∧ CdLower S l ↔ cdTheta S l (cdCode S l) = xtOrec lnSw l) :=
  xtExact_iff (xtSpec1 lnSw_topPkg) hl hlB

/-- **The offset at an isolated fixed point below `Λ⁺(lnSw)`**: `O(F) = F`. -/
theorem lnSw_iso {F : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hFB : F < xtB1 lnSw)
    (hiso : CpIso F) : xtOrec lnSw F = F :=
  xtIso hF hfix (hFB.trans (xtB1_lt_Om1 lnSw_topPkg)) hiso

/-- **ENUM-REACH at an isolated fixed point of the range below `Λ⁺(lnSw)` reduces to the code.** -/
theorem lnSw_fix_code {F : Ordinal.{0}} (hr : CdRange S F) (hfix : upsilon F = F) (hFB : F < xtB1 lnSw)
    (hiso : CpIso F) : (F ≤ cdCode S F → CdUpper S F) ∧ (cdCode S F ≤ Om1 → CdLower S F) :=
  xtFix_code (xtSpec1 lnSw_topPkg) hr.1 hfix hFB (lnSw_iso hr.1 hfix hFB hiso) (cp_name_L hr.2.2.1)

/-- **The hypotheses of `lnSwRoad3` from those of `cpRoad3`.** -/
theorem lnSw_of_cp (hU : CpUPPERhigh S) (hL : CpLOWERhigh S) (hT : CpTHfix S) :
    (∀ l, CdRange S l → xtB1 lnSw ≤ l → CdUpper S l) ∧ (∀ l, CdRange S l → xtB1 lnSw ≤ l → CdLower S l) ∧
      (∀ l, CdRange S l → l < xtB1 lnSw → upsilon l = l → cdTheta S l (cdCode S l) = xtOrec lnSw l) := by
  obtain ⟨hU', hL', hT'⟩ := ln_of_cp hU hL hT
  have hle : lnFam.famSup ≤ xtB1 lnSw := ltC_lt_B1.le
  refine ⟨fun l hr h => hU' l hr (hle.trans h), fun l hr h => hL' l hr (hle.trans h), fun l hr hlB hfix => ?_⟩
  rcases lt_or_ge l lnFam.famSup with h | h
  · obtain ⟨k, hk⟩ := lnFam.famLt h
    rw [lnSw_eqS k hr.1 hk]; exact hT' k l hr hk hfix
  · exact (lnSw_iff hr.1 hlB).1 ⟨hU' l hr h, hL' l hr h⟩

/-- **The road with UPPER and LOWER asked only at `λ ≥ Λ⁺(lnSw)`**, `Θ_F(m_F) = O(F)` at the fixed points of the
range below `Λ⁺(lnSw)`, the cap of the values outside `Λ⁺(lnSw)`, (CL), EQ, TCrest, (EMB₂). -/
theorem lnSwRoad3 (hU : ∀ l, CdRange S l → xtB1 lnSw ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 lnSw ≤ l → CdLower S l)
    (hT : ∀ l, CdRange S l → l < xtB1 lnSw → upsilon l = l → cdTheta S l (cdCode S l) = xtOrec lnSw l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lnSw) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad3 (xtSpec1 lnSw_topPkg) lnSw_nonfix hU hL hT hV hC hEQ hrest hB2

/-- **The road with UPPER, LOWER and the cap of the values asked only outside `Λ⁺(lnSw)`.** -/
theorem lnSwRoad (hU : ∀ l, CdRange S l → XtOut (xtB1 lnSw) l → CdUpper S l)
    (hL : ∀ l, CdRange S l → XtOut (xtB1 lnSw) l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lnSw) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad (xtSpec1 lnSw_topPkg) lnSw_nonfix hU hL hV hC hEQ hrest hB2

/-- **The road with the caps asked only outside `Λ⁺(lnSw)`**: CAP-0, CAP-1 outside, (CL), (TC), (EMB₂). -/
theorem lnSwRoad_cap
    (h0 : ∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < cdMstar S → XtOut (xtB1 lnSw) l → CdCapAt S l)
    (h1 : ∀ l, IsRestartIdx l → cdB0 ≤ l → cdMstar S ≤ upsilon l → upsilon l < Nc.ncL S ω →
      cdCode S l < Nc.ncPp S → XtOut (xtB1 lnSw) l → CdCapAt S l) (hC : CdCL S) (hTC : CdTC S)
    (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad_cap (xtSpec1 lnSw_topPkg) lnSw_nonfix h0 h1 hC hTC hB2


end Googology.Trans.PoR.InaccPsi.R2.Lt
