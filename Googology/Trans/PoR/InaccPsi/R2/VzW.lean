import Googology.Trans.PoR.InaccPsi.R2.VzO

/-!
# `ϑᵗ(Ω₁·ω) = B(τ)`, the IMG package of `B`, and Theorem BLK^O at the block of `Λ_B`

`B(x) = VzB x = sup_N ϑˣ(Ω₁·N)` is the least value of `φ(ω, ·)` above `x` (`vzB_omega`).  From the cited facts of
`R2.CitedVz` at the argument `Ω₁·ω = ϑ₁(1)` ([W07a] Def 3.22, Lemma 4.2, Lemma 3.30; [W07b] Def 4.1 in the case
`δ > α`):

* `vzOm1w_lt`, `vz_w_facts`, `vz_vt_w_eq` (**`ϑᵗ(Ω₁·ω) = B(τ)`**: every `ϑᵗ(Ω₁·N)` lies below `ϑᵗ(Ω₁·ω)`; a value of
  `φ(ω, ·)` strictly below it would be some `ϑᵗ(Ω₁·q + r)`, `q < ω`, which is not a fixed point of `φ_q`, `vz_th_notP`);
* `vz_lh_B` (**`lh(B(τ)) = B(τ)·ω`** in `R₁⁺`, [W07b] Theorem 5.3 with `vzLhT_w`);
* `vz_le1R_omega` (**the `R₁⁺`-test `α ≤₁ α·ω` gives `α ∈ range φ(ω, ·)`**, from `vz_le1R_level` at every `n`);
* `RstK.vzPkgB` (**the IMG package of `B`**: the copy `f(B)` of `B ≤₁ B·ω` has `f(B) + f(B·ω) = f(B·ω)`, so
  `f(B) ≤₁ f(B)·ω`, and `f(B)` is a value of `φ(ω, ·)` above `f(ρ)`, or a `υ`-point);
* `vzTopIn_Lam`, `vzSpec2`, `vzBlk2` (**BLK^O below `υ_{Λ_B+ω²}`**), `vzCore2`, `vzReach_Lam`
  (**`lh(ρ_{Λ_B}) = δ + B(ρ)`**), `vzNuC_bound2` (**`υ_{Λ_B+ω²} ≤ ρ_L < ν_C`**).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order VzTm

theorem vzOm1w_lt : Om1 * ω < OmTwo :=
  isPrincipal_mul_omega 2 Om1_lt_OmTwo (omega0_lt_omega_one.trans Om1_lt_OmTwo)

/-- The facts on the term `ϑᵗ(Ω₁·ω)`: in `Tᵗ`, an `ε`-number in `(τ, Ω₁)`. -/
theorem vz_w_facts {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) :
    vt τ (Om1 * ω) ∈ Tset τ ∧ τ < vt τ (Om1 * ω) ∧ vt τ (Om1 * ω) < Om1 ∧ InE (vt τ (Om1 * ω)) ∧
      Indec (vt τ (Om1 * ω)) := by
  have hγT := vzOm1w_T hτ hτ1
  obtain ⟨hvT, -, hv1, hvP, -⟩ := vt_memTwo hτ hτ1 hγT vzOm1w_lt
  have hΩ : Om1 ≤ Om1 * ω := by
    calc Om1 = Om1 * 1 := (mul_one _).symm
      _ ≤ Om1 * ω := mul_le_mul_right one_lt_omega0.le Om1
  have hE := (vt_E_iff hτ hτ1 hγT vzOm1w_lt).2 hΩ
  exact ⟨hvT, hE.1, hv1, hE.2, hvP⟩

/-- A value of `φ(ω, ·)` is an `ε`-number and a fixed point of every `φ_k`, `k < ω`. -/
theorem vz_omega_P {a : Ordinal.{0}} (ha : a ∈ Set.range (veblen ω)) (k : ℕ) : VzP (k + 1) a :=
  vzP_succ.2 ((mem_range_veblen omega0_ne_zero).1 ha k (natCast_lt_omega0 k))

theorem vz_omega_E {a : Ordinal.{0}} (ha : a ∈ Set.range (veblen ω)) : InE a :=
  vzP_E (k := 1) le_rfl (vz_omega_P ha 0)

/-- **`ϑᵗ(Ω₁·ω) = B(τ)`**. -/
theorem vz_vt_w_eq {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) : vt τ (Om1 * ω) = VzB τ := by
  obtain ⟨haT, hτa, ha1, haE, -⟩ := vz_w_facts hτ hτ1
  set a := vt τ (Om1 * ω) with hadef
  have h0T := mem_T_of_le hτ hτ1 (zero_le : (0 : Ordinal.{0}) ≤ τ)
  obtain ⟨hBω, hτB, -⟩ := vzB_omega hτ hτ1
  refine le_antisymm ?_ (Ordinal.iSup_le (fun N => (vzVt_lt_w hτ hτ1 h0T (Ordinal.omega_pos 1) haE.pos).le))
  by_contra hlt
  push Not at hlt
  set z := VzB τ with hz
  have hz1 : z < Om1 := hlt.trans ha1
  have hzT : z ∈ Tset τ := vz_T_down hτ hτ1 haT ha1 hlt.le
  have hzE : InE z := vz_omega_E hBω
  obtain ⟨ξ, hξT, hξ2, hξz⟩ := vt_rep hτ hτ1 hzT hτB.le hz1 (inE_indec hzE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hτ hτ1 hξT hξ2).1 ⟨by rw [hξz]; exact hτB, by rw [hξz]; exact hzE⟩
  have hξw : ξ < Om1 * ω := vzLt_of_vt_lt_w hτ hτ1 hξT hξ2 (by rw [hξz]; exact hlt)
  obtain ⟨hdec, hr1⟩ := vz_div_Om1 ξ
  set q := ξ / Om1 with hq
  set r := ξ % Om1 with hr
  have hqw : q < ω := by
    have h1 : Om1 * q < Om1 * ω := lt_of_le_of_lt (hdec ▸ le_self_add) hξw
    exact (mul_lt_mul_iff_right₀ (Ordinal.omega_pos 1)).1 h1
  obtain ⟨q', hq'⟩ := lt_omega0.1 hqw
  have hq'1 : 1 ≤ q' := by
    rcases Nat.eq_zero_or_pos q' with h0 | h0
    · exfalso
      rw [h0, Nat.cast_zero] at hq'
      rw [hq', mul_zero, zero_add] at hdec
      exact absurd (hdec ▸ hr1) (not_lt.2 hΩξ)
    · exact h0
  have hrT : r ∈ Tset τ := vzRem_T hτ hτ1 hξT hξ2 hdec.symm (dvd_mul_right _ _) hr1
  have e : Om1 * (q' : Ordinal.{0}) + r = ξ := by rw [← hq']; exact hdec
  have hnot := vz_th_notP hτ hτ1 hq'1 hrT hr1
  rw [e, hξz] at hnot
  exact hnot (vz_omega_P hBω q')

/-- **The `R₁⁺`-reach of `B(τ)`**: `lh(B(τ)) = B(τ)·ω` ([W07b] Theorem 5.3 through `lh_eq_lhT`, with the cited value
`vzLhT_w` of [W07b] Def 4.1 at `ϑᵗ(Ω₁·ω)`). -/
theorem vz_lh_B {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) : IsLh1 (VzB τ) (VzB τ * ω) := by
  obtain ⟨haT, hτa, ha1, -, haP⟩ := vz_w_facts hτ hτ1
  have h := lh_eq_lhT (Or.inr hτ) hτ1 haT hτa ha1 haP
  rwa [vzLhT_w hτ hτ1, vz_vt_w_eq hτ hτ1] at h

/-- **The `R₁⁺`-test `α ≤₁ α·ω`**: it gives `α ∈ range φ(ω, ·)` (`α > 0`). -/
theorem vz_le1R_omega {a : Ordinal.{0}} (ha : 0 < a) (h : le1R a (a * ω)) : a ∈ Set.range (veblen ω) := by
  refine (mem_range_veblen omega0_ne_zero).2 (fun b hb => ?_)
  obtain ⟨k, rfl⟩ := lt_omega0.1 hb
  have hk : le1R a (a * ((k + 1 + 1 : ℕ) : Ordinal.{0})) :=
    le1R_of_le (vz_le_mul (by omega)) (mul_le_mul_right (natCast_lt_omega0 _).le a) h
  exact vzP_succ.1 (vz_le1R_level (k + 1) (by omega) a ha hk)

theorem vz_mul_omega_lt {a δ : Ordinal.{0}} (hδ : InE δ) (ha : a < δ) : a * ω < δ := by
  have hP := isPrincipal_mul_omega0_opow_opow δ
  have e : ω ^ ω ^ δ = δ := by rw [show ω ^ δ = δ from hδ, show ω ^ δ = δ from hδ]
  rw [e] at hP
  exact hP ha (omega0_lt_inE hδ)

namespace RstK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **The IMG package of `B`**: witness sets such that every covering copy `f` has `B(f(ρ)) ≤ f(B(ρ))`. -/
theorem vzPkgB : ImgPkg ρ δ VzB := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  set v := VzB ρ with hv
  obtain ⟨hvω, hρv, -⟩ := vzB_omega hρE hρ1
  have hvδ : v < δ := h.vz_B_lt_δ
  have hvE : InE v := vz_omega_E hvω
  have hvwδ : v * ω < δ := vz_mul_omega_lt h.δE hvδ
  have hvw : v ≤ v * ω := by
    calc v = v * 1 := (mul_one _).symm
      _ ≤ v * ω := mul_le_mul_right one_lt_omega0.le v
  have hsrc : le1 v (v * ω) := (h.lowδ _ _ hρv hvwδ.le).2 (vz_lh_B hρE hρ1).1
  have hwI : Indec (v * ω) := by
    have e : v * ω = ω ^ (v + 1) := by
      rw [opow_add, opow_one, show ω ^ v = v from hvE]
    rw [e]; exact indec_opow _
  have w1 : WZ ρ δ {ρ} ∅ := by
    have := (WZ.empty (ρ := ρ) (δ := δ)).insW le_rfl h.ρδ (Or.inl (inE_indec hρE))
    simpa using this
  have w2 : WZ ρ δ (insert v {ρ}) ∅ := w1.insW hρv.le hvδ (Or.inl (inE_indec hvE))
  have w3 : WZ ρ δ (insert (v * ω) (insert v {ρ})) ∅ := w2.insW (hρv.le.trans hvw) hvwδ (Or.inl hwI)
  refine ⟨(one_le_iff_pos.2 h.ρU.1).trans hρv.le, hvδ, _, _, w3, by simp [hv], fun A f hW _ C => ?_⟩
  have hvA : v ∈ A := hW (by simp)
  have hvwA : v * ω ∈ A := hW (by simp)
  have hfρE : InE (f ρ) := upsPt_inE C.ups
  have hfρ1 : f ρ < Om1 := (C.low ρ C.rho).trans h.ρ1
  have hfρv : f ρ < f v := C.mono C.rho hvA hρv
  have hadd : f v + f (v * ω) = f (v * ω) :=
    C.add v hvA (v * ω) hvwA (v * ω) hvwA (add_eq_right_iff_mul_omega0_le.2 le_rfl)
  have hge : f v * ω ≤ f (v * ω) := add_eq_right_iff_mul_omega0_le.1 hadd
  have himg : le1 (f v) (f (v * ω)) := C.cov1 v hvA _ hvwA hsrc
  by_cases hU : UpsPt (f v)
  · exact vzB_le_next hfρE hfρ1 hfρv hU.2
  · have hR := (C.sk _ (C.low _ hvA) hU _).1 himg
    have hfv0 : 0 < f v := lt_of_le_of_lt zero_le hfρv
    have hfvw : f v ≤ f v * ω := by
      calc f v = f v * 1 := (mul_one _).symm
        _ ≤ f v * ω := mul_le_mul_right one_lt_omega0.le (f v)
    have hR' : le1R (f v) (f v * ω) := le1R_of_le hfvw hge hR
    exact (vzB_omega hfρE hfρ1).2.2 (f v) (vz_le1R_omega hfv0 hR') hfρv

end RstK

/-! ## Theorem BLK^O at the block of `Λ_B` -/

/-- **The input of Lemma TOP at `Λ_B`** with the term `B` (`RstK.vzPkgB`). -/
theorem vzTopIn_Lam : TopInH VzOrec VzLam :=
  ⟨VzB, 0, vzOrec_Lam, (ups_ri vzLam_ri).1, fun _ hμ hμl _ => vzOrec_lt_top hμ hμl, fun R => R.vzPkgB⟩

/-- **`VzOrec` is a general offset specification up to `Λ_B + ω²`.** -/
theorem vzSpec2 : OffSpecGen VzOrec (VzLam + ω * ω) :=
  vzSpec (dvd_add (ri_iff.1 vzLam_ri).2 (dvd_refl _)) (Om1_add_lt vzLam_lt_Om1 ww_lt_Om1)
    (fun l hl hlB => by
      rcases lt_trichotomy l VzLam with hlt | rfl | hgt
      · exact vzTopIn hl (hlt.trans vzLam_lt_Om1) (vzOrec_lt_top hl hlt)
      · exact vzTopIn_Lam
      · exact absurd hlB (not_lt.2 (next_mult (ri_iff.1 vzLam_ri).2 (ri_iff.1 hl).2 hgt)))

/-- **Theorem BLK^O with `VzOrec` below `υ_{Λ_B+ω²}`** in `R₂^C` (the block of `ρ_{Λ_B}` included). -/
theorem vzBlk2 :
    (∀ c d, c < d → d < upsilon (VzLam + ω * ω) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < VzLam + ω * ω ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < VzLam + ω * ω →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + VzOrec l)) ∧
    (∀ α < upsilon (VzLam + ω * ω), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  blk_genGen vzSpec2

/-- **CORE-C up to `υ_{Λ_B+ω²}`.** -/
theorem vzCore2 : Set.Iio (upsilon (VzLam + ω * ω)) ⊆ Core R2C := core_genGen vzSpec2

/-- **The reach at `Λ_B`**: `lh(ρ) = δ + B(ρ)` for `ρ = ρ_{Λ_B}`, `B(ρ)` the least value of `φ(ω, ·)` above `ρ`. -/
theorem vzReach_Lam : IsReach R2C (upsilon VzLam) (upsilon (VzLam + ω + 1) + VzB (upsilon VzLam)) := by
  have := (vzBlk2.2.1 VzLam vzLam_ri (lt_add_of_pos_right _ (mul_pos omega0_pos omega0_pos))).2.2
  rwa [vzOrec_Lam] at this

/-- **Where the first non-standard pair lies**: `ρ_L <₂ ν_C = ρ_ξ` with `Λ_B + ω² ≤ L < ξ` restart indices,
`υ_{Λ_B+ω²} ≤ ρ_L < ν_C < Ω₁`. -/
theorem vzNuC_bound2 : ∃ L ξ, IsRestartIdx L ∧ IsRestartIdx ξ ∧ VzLam + ω * ω ≤ L ∧ L < ξ ∧
    upsilon (VzLam + ω * ω) ≤ upsilon L ∧ upsilon L < nuC ∧ nuC = upsilon ξ ∧ nuC < Om1 ∧
    le2 (upsilon L) nuC := by
  obtain ⟨L, ξ, hL, hξ, hLξ, he, h2, -, -, -⟩ := level2_restart
  have hLν : upsilon L < nuC := by rw [he]; exact upsilon_normal.strictMono hLξ
  have hle := left_ge_of_spec vzSpec2 hL hLν h2
  exact ⟨L, ξ, hL, hξ, hle, hLξ, upsilon_normal.strictMono.monotone hle, hLν, he, nuC_lt_Om1, h2⟩

end Googology.Trans.PoR.InaccPsi.R2
