import Googology.Trans.PoR.InaccPsi.R2.VjD
import Googology.Trans.PoR.InaccPsi.R2.VjTh
import Googology.Trans.PoR.InaccPsi.R2.LjExp

/-!
# The `ψ_{Ω₁}`-side of the move at EVERY level `μ < θ`: `B_n` maps the runs of `Φ_μ` to runs of `Φ_{B_n μ}`

`θ = ConjT.th S`, `Φ_μ = Ul.ulH S 0 μ`, `d = Ul.ulD S 0` (its datum), `u_μ = Le.leOe μ = Ω₁^μ`, `B_n = Bc.bcB S n`,
`c_n = L(n+1) = Bc.bcC S n`, `B = α_{n+1} + |r|`, `B' = α_ω + |σ r|` (the argument maps of `Bc`).  The proofs of
`R2.UfLeast` / `R2.UfB` (levels `< B₂`, codes `UcCl`) at every level `μ < θ` with `d(μ) < c_{n+1}`, from the
unconditional `ψ`-link and FWD of `Φ_μ` (`Vg.vg_phi_eq`, `Vg.vg_phi_fwd`) and the hull test of `Ui.ui_code_th`
(arguments `≥ Ω_ω`):

* `vj_Oe_eq` (`u_μ = Ω₁^μ`), `vj_lev_mem` (**`μ < θ` of the notation with `d(μ) < ψ_{Ω₁}(A)`, `A ≥ Ω_ω`,
  lies in `Cl(A, ψ_{Ω₁}(A))`**), `vj_U_mem`, `vj_OmW_le_of_lo` (every `K` with `c_n ≤ ψ_{Ω₁}(K)` is `≥ Ω_ω`),
  `vj_fwd`, `vj_validP`;
* `vj_leastP`, `vj_firstP` (**the first value `ψ_{Ω₁}(K + u_μ)` of `Φ_μ` above `m`**), `vj_B_least`;
* `vj_datB` (**`d(B_n μ) < B_n q ↔ d(μ) < q`** at a countable strongly critical `q < L(ω)`), `vj_B_lvl`
  (**`μ ∈ MvD`, `B_n μ < θ`, `d(B_n μ) < L(ω)`, `B_n(μ+1) = B_n μ + 1`**), `vj_dvd_th`, `vj_dvd_alpha`,
  `vj_dvd_alphaW`, `vj_dvd_sig`, `vj_B_dvd`;
* `vj_B_val`, `vj_B_fix` (**`B_n` maps values and fixed points `∈ [c_n, c_{n+1})` of `Φ_μ` to values and fixed
  points of `Φ_{B_n μ}`**), `vj_B_run` (**`B_n(Φ_μ(c₀ + 1 + δ)) = Φ_{B_n μ}(c₁ + 1 + B_n δ)`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul
  Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Rh
  Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Trans.PoR.InaccPsi.R2.Rb

variable {S : InaccSeq.{0}}

/-! ## Hulls, divisibility, FWD -/

theorem vj_O01 : (Om (0 + 1) : Ordinal.{0}) = Om 1 := by rw [zero_add]

/-- `u_μ = Ω₁^μ`. -/
theorem vj_Oe_eq (μ : Ordinal.{0}) : Le.leOe μ = Om (0 + 1) ^ μ := by
  unfold Le.leOe; rw [vj_O01]; conv_rhs => rw [← Bt.Om1_opow]
  rw [← opow_mul]

/-- **A level `μ < θ` with `d(μ) < ψ_{Ω₁}(A)` is of the notation and lies in `Cl(A, ψ_{Ω₁}(A))`** (`A ≥ Ω_ω`). -/
theorem vj_lev_mem {A μ : Ordinal.{0}} (hμθ : μ < ConjT.th S) (hA : Om ω ≤ A) (hd : ulD S 0 μ < S.psi A (Om 1)) :
    μ ∈ ⋃ a, S.CSet a 0 ∧ μ ∈ S.CSet A (S.psi A (Om 1)) := by
  have hq : SC (S.psi A (Om 1)) := SC_psi Low.InR_Om_one A
  have hq1 : S.psi A (Om 1) ≤ Om 1 := (psi_lt Low.InR_Om_one A).le
  have hN := vjK_notA le_rfl ((ul_vis hq).1 hd)
  have hdu : Ui.uiDat S μ < S.psi A (Om 1) := by
    rw [← Vd.vd_dat_ui hN hq hq1, Vd.vdD_eq]; exact hd
  exact ⟨hN, (Ui.ui_code_th hN hμθ hA hq1 (fun y hy hy1 => lt_psi_of_mem Low.InR_Om_one hy hy1) hq.1).2 hdu⟩

/-- **`u_μ·D ∈ Cl(A, ψ_{Ω₁}(A))`** for `μ < θ`, `d(μ) < ψ_{Ω₁}(A)`, `D < ψ_{Ω₁}(A)`, `A ≥ Ω_ω`. -/
theorem vj_U_mem {A μ D : Ordinal.{0}} (hμθ : μ < ConjT.th S) (hA : Om ω ≤ A) (hd : ulD S 0 μ < S.psi A (Om 1))
    (hD : D < S.psi A (Om 1)) : Le.leOe μ * D ∈ S.CSet A (S.psi A (Om 1)) := by
  rw [vj_Oe_eq]; exact ul_Wpow_mem omega0_pos (vj_lev_mem hμθ hA hd).2 (CSet.of_lt hD)

theorem vj_U_mem1 {A μ : Ordinal.{0}} (hμθ : μ < ConjT.th S) (hA : Om ω ≤ A) (hd : ulD S 0 μ < S.psi A (Om 1)) :
    Le.leOe μ ∈ S.CSet A (S.psi A (Om 1)) := by
  have := vj_U_mem (D := 1) hμθ hA hd (Uc.uc_one_lt_SC (SC_psi Low.InR_Om_one A))
  rwa [mul_one] at this

theorem vj_Oe_eq' (μ : Ordinal.{0}) : Le.leOe μ = Om 1 ^ μ := by rw [vj_Oe_eq, vj_O01]

/-- **Every `K` with `c_n ≤ ψ_{Ω₁}(K)` is `≥ Ω_ω`.** -/
theorem vj_OmW_le_of_lo {n : ℕ} {K : Ordinal.{0}} (hlo : Bc.bcC S n ≤ S.psi K (Om 1)) : Om ω ≤ K := by
  by_contra h
  push Not at h
  have h1 : S.psi K (Om 1) ≤ S.psi (Om ω) (Om 1) := (psi_mono Low.InR_Om_one h.le).1
  have hlt : (Om ω : Ordinal.{0}) < bcAlpha S (n + 1) := by
    unfold bcAlpha
    exact (lt_add_of_pos_right _ (SC_Om omega0_ne_zero).1).trans_le le_self_add
  have h2 : S.psi (Om ω) (Om 1) < S.psi (bcAlpha S (n + 1)) (Om 1) :=
    psi_lt_psi_of_mem Low.InR_Om_one hlt (ConjT.OmW_mem S _ _)
  have hc : Bc.bcC S n = S.psi (bcAlpha S (n + 1)) (Om 1) := Bc.ncL_nat_eq S (n + 1)
  exact absurd hlo (not_le.2 (h1.trans_lt (hc ▸ h2)))

/-- **FWD at a level `j < θ`** for an own `B ≥ Ω_ω` with `u_{j+1} ∣ B` and `d(j) < ψ_{Ω₁}(B)`. -/
theorem vj_fwd {j B : Ordinal.{0}} (hjθ : j < ConjT.th S) (hown : B ∈ S.CSet B (S.psi B (Om 1)))
    (hBW : Om ω ≤ B) (hdvd : Le.leOe (j + 1) ∣ B) (hB0 : B ≠ 0) (hd : ulD S 0 j < S.psi B (Om 1)) :
    ulH S 0 j (S.psi B (Om 1)) = S.psi B (Om 1) := by
  have h := Vg.vg_phi_fwd hjθ B (by rw [vj_O01]; exact hown) (by rw [← vj_Oe_eq]; exact hdvd) hB0
    (by rw [vj_O01]; exact (vj_lev_mem hjθ hBW hd).2)
  rwa [vj_O01] at h

/-- **CONV**: a fixed point `ψ_{Ω₁}(B)` of `Φ_μ` (`B` own) has `u_{μ+1} ∣ B`. -/
theorem vj_conv {μ B : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1)))
    (hp : ulH S 0 μ (S.psi B (Om 1)) = S.psi B (Om 1)) : Le.leOe (μ + 1) ∣ B := by
  have h := Ul.ul_conv omega0_pos μ B (by rw [vj_O01]; exact hown) (by rw [vj_O01]; exact hp)
  rwa [← vj_Oe_eq] at h

/-- **`u_μ ∣ B`** for an own `B` whose collapse is fixed by every `Φ_j`, `j < μ`, `d(j) < ψ_{Ω₁}(B)`. -/
theorem vj_dvd_range {μ B : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1)))
    (hfix : ∀ j < μ, ulD S 0 j < S.psi B (Om 1) → ulH S 0 j (S.psi B (Om 1)) = S.psi B (Om 1)) :
    Le.leOe μ ∣ B := by
  have h := Us.us_dvd_range (s := 0) omega0_pos (γ := μ) (by rw [vj_O01]; exact hown)
    (fun j hj hd => by rw [vj_O01] at hd ⊢; exact hfix j hj hd)
  rwa [← vj_Oe_eq] at h

/-- **Validity from `D < ψ_{Ω₁}(B + u_μ·D)`** (`u_μ ∣ B`, `Φ_μ(c) = ψ_{Ω₁}(B)`). -/
theorem vj_validP {μ B c D : Ordinal.{0}} (hB : Le.leOe μ ∣ B) (hc : ulH S 0 μ c = S.psi B (Om 1))
    (hv : D < S.psi (B + Le.leOe μ * D) (Om 1)) : ∀ d, d ≤ D → d < ulH S 0 μ (c + d) := by
  intro d hd
  by_contra hle
  push Not at hle
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact absurd hle (not_le.2 (ulH_SC _ _).1)
  have hB' : Om (0 + 1) ^ μ ∣ B := by rw [← vj_Oe_eq]; exact hB
  have hDΩ : D ≤ Om (0 + 1) := by rw [vj_O01]; exact hv.le.trans (psi_lt Low.InR_Om_one _).le
  have hprev : ∀ d'', d'' < D → d'' < ulH S 0 μ (c + d) →
      S.psi (B + Om (0 + 1) ^ μ * d'') (Om (0 + 1)) < ulH S 0 μ (c + d) := fun d'' hd'' hq => by
    have hUB := ulUB (S := S) (s := 0) omega0_pos μ B c d'' hB' (by rw [vj_O01, hc])
      (hd''.le.trans hDΩ)
    exact hUB.trans_lt ((ulH_lt_iff μ).2 ((add_lt_add_iff_left c).2 (hq.trans_le hle)))
  have hcl : ∀ j < μ, ulD S 0 j < ulH S 0 μ (c + d) → ∀ z < ulH S 0 μ (c + d),
      ulH S 0 j z < ulH S 0 μ (c + d) := fun j hj hdj z hz => by
    have hf := vj_fix_lower hj ⟨c + d, rfl⟩ hdj
    have := (ulH_lt_iff (S := S) (s := 0) j).2 hz
    rwa [hf] at this
  have hBq : S.psi B (Om (0 + 1)) < ulH S 0 μ (c + d) := by
    rw [vj_O01, ← hc]; exact (ulH_lt_iff μ).2 (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hd0))
  have h := ulInv (S := S) (s := 0) omega0_pos hB' (ulH_SC μ (c + d)) hcl hBq hDΩ hprev
  rw [vj_O01, ← vj_Oe_eq'] at h
  exact absurd ((h.trans hle).trans hd) (not_le.2 hv)

/-- **The `ψ`-link**: `D < ψ_{Ω₁}(B + u_μ·D) = Φ_μ(c + D)` for an own `B ≥ Ω_ω` with `u_μ ∣ B`, `Φ_μ(c) = ψ_{Ω₁}(B)`,
`d(μ) < ψ_{Ω₁}(B)`, `D < Ω₁` valid. -/
theorem vj_eqP {μ B c D : Ordinal.{0}} (hμθ : μ < ConjT.th S) (hown : B ∈ S.CSet B (S.psi B (Om 1)))
    (hBW : Om ω ≤ B) (hdvd : Le.leOe μ ∣ B) (hc : ulH S 0 μ c = S.psi B (Om 1)) (hd : ulD S 0 μ < S.psi B (Om 1))
    (hD : D < Om 1) (hcond : ∀ d, d ≤ D → d < ulH S 0 μ (c + d)) :
    D < S.psi (B + Le.leOe μ * D) (Om 1) ∧ S.psi (B + Le.leOe μ * D) (Om 1) = ulH S 0 μ (c + D) := by
  have h := Vg.vg_phi_eq hμθ (by rw [vj_O01]; exact hown) (by rw [← vj_Oe_eq]; exact hdvd)
    (by rw [vj_O01]; exact (vj_lev_mem hμθ hBW hd).2) (by rw [vj_O01]; exact hc) (by rw [vj_O01]; exact hD) hcond
  rw [vj_O01, ← vj_Oe_eq'] at h
  exact h

/-! ## The first value of `Φ_μ` above `m` -/

/-- **The first value of `Φ_μ` above `m`**: for an own `K ≥ Ω_ω` with `ψ_{Ω₁}(K) ≤ m < ψ_{Ω₁}(K + 1)` and
`d(μ) < v` at every strongly critical `v ∈ (m, Ω₁]` (`μ < θ`), `ψ_{Ω₁}(K + u_μ)` is a value of `Φ_μ` above `m`, below every value of `Φ_μ` above `m`;
`K + u_μ` is own. -/
theorem vj_leastP {μ K m : Ordinal.{0}} (hμθ : μ < ConjT.th S)
    (hown : K ∈ S.CSet K (S.psi K (Om 1))) (hKW : Om ω ≤ K)
    (hcm : S.psi K (Om 1) ≤ m) (hm1 : m < S.psi (K + 1) (Om 1))
    (hdm : ∀ v, SC v → v ≤ Om 1 → m < v → ulD S 0 μ < v) :
    S.psi (K + Le.leOe μ) (Om 1) ∈ range (ulH S 0 μ) ∧ m < S.psi (K + Le.leOe μ) (Om 1) ∧
      (∀ v ∈ range (ulH S 0 μ), m < v → S.psi (K + Le.leOe μ) (Om 1) ≤ v) ∧
      K + Le.leOe μ ∈ S.CSet (K + Le.leOe μ) (S.psi (K + Le.leOe μ) (Om 1)) := by
  set u := Le.leOe μ with hudef
  set E := K + u with hEdef
  have hu0 : u ≠ 0 := rhU_ne μ
  have h1u : (1 : Ordinal.{0}) ≤ u := one_le_iff_ne_zero.2 hu0
  have hEW : Om ω ≤ E := hKW.trans le_self_add
  have hmE : m < S.psi E (Om 1) :=
    hm1.trans_le (psi_mono (S := S) Low.InR_Om_one (add_le_add_right h1u K)).1
  have hμE : ulD S 0 μ < S.psi E (Om 1) := hdm _ (SC_psi Low.InR_Om_one E) (psi_lt Low.InR_Om_one E).le hmE
  have hownE : E ∈ S.CSet E (S.psi E (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hown) (vj_U_mem1 hμθ hEW hμE)
  have hdvdE : u ∣ E := rh_dvd_add_self μ K
  have hE0 : E ≠ 0 := (lt_of_lt_of_le (rhU_pos μ) le_add_self).ne'
  have hfixE : ∀ j < μ, ulD S 0 j < S.psi E (Om 1) → ulH S 0 j (S.psi E (Om 1)) = S.psi E (Om 1) :=
    fun j hj hd => vj_fwd (hj.trans hμθ) hownE hEW ((rhU_dvd_succ hj).trans hdvdE) hE0 hd
  have hval : S.psi E (Om 1) ∈ range (ulH S 0 μ) := vj_range (SC_psi Low.InR_Om_one E) hμE hfixE
  have hnone : ∀ v, m < v → v < S.psi E (Om 1) → v ∈ range (ulH S 0 μ) → False := by
    intro v hmv hvE hvR
    have hvSC : SC v := by obtain ⟨o, ho⟩ := hvR; rw [← ho]; exact ulH_SC μ o
    have hvF : ∀ j < μ, ulD S 0 j < v → ulH S 0 j v = v := fun j hj hd => vj_fix_lower hj hvR hd
    obtain ⟨V, hownV, hV⟩ := rb_own_of_SC hvSC hvE
    have hdvdV : u ∣ V := vj_dvd_range hownV (fun j hj hd => by rw [hV] at hd ⊢; exact hvF j hj hd)
    have hown1 : K + 1 ∈ S.CSet (K + 1) (S.psi (K + 1) (Om 1)) :=
      CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hown) (CSet.one_mem _ _)
    have hc1 : S.psi (K + 1) (Om 1) ≤ v := by
      refine not_lt.1 fun hlt => ?_
      have hcv : S.psi K (Om 1) < S.psi V (Om 1) := by rw [hV]; exact hcm.trans_lt hmv
      have h1 := compare_psi Low.InR_Om_one hown hownV
      rw [compare_lt_iff_lt.2 hcv] at h1
      have hBV : K < V := compare_lt_iff_lt.1 h1.symm
      have h2 := compare_psi Low.InR_Om_one hownV hown1
      rw [hV, compare_lt_iff_lt.2 hlt] at h2
      have hV1 : V < K + 1 := compare_lt_iff_lt.1 h2.symm
      exact absurd (Order.lt_add_one_iff.1 hV1) (not_le.2 hBV)
    have hBV : K < V := by
      have h1 := compare_psi Low.InR_Om_one hown1 hownV
      rcases hc1.lt_or_eq with hlt | heq
      · rw [hV, compare_lt_iff_lt.2 hlt] at h1
        exact (lt_add_one K).trans (compare_lt_iff_lt.1 h1.symm)
      · rw [← hV] at heq
        rw [← rh_own_inj hown1 hownV heq]; exact lt_add_one K
    have hVE : V < E := by
      have h1 := compare_psi Low.InR_Om_one hownV hownE
      rw [hV, compare_lt_iff_lt.2 hvE] at h1
      exact compare_lt_iff_lt.1 h1.symm
    set T := u * (K / u) with hTdef
    have hTB : T ≤ K := Ordinal.mul_div_le K u
    have hET : E = T + u := by
      rw [hEdef, hTdef]
      calc K + u = u * (K / u) + (K % u + u) := by rw [← add_assoc, Ordinal.div_add_mod]
        _ = u * (K / u) + u := by
            have := rdk_absorb (rhU_indec μ) (Ordinal.mod_lt K hu0) (le_refl (1 : Ordinal.{0}))
            rw [mul_one] at this; rw [this]
    have hTV : T ≤ V := hTB.trans hBV.le
    have hTd : u ∣ T := dvd_mul_right _ _
    have hVT : V = T + (V - T) := (Ordinal.add_sub_cancel_of_le hTV).symm
    have hdd : u ∣ V - T := by
      have := hdvdV
      rw [hVT] at this
      exact (Ordinal.dvd_add_iff hTd).1 this
    have hlt : V - T < u := by
      have := hVE
      rw [hET, hVT] at this
      exact (add_lt_add_iff_left T).1 this
    have h0 : V - T = 0 := by
      by_contra hne
      exact absurd (Ordinal.le_of_dvd hne hdd) (not_le.2 hlt)
    rw [h0, add_zero] at hVT
    exact absurd (hVT ▸ hTB) (not_le.2 hBV)
  exact ⟨hval, hmE, fun v hv hmv => not_lt.1 fun hlt => hnone v hmv hlt hv, hownE⟩

/-- **The index of the first value**: `ψ_{Ω₁}(K + u_μ) = Φ_μ(c₀)` with `Φ_μ(c) ≤ m` for every `c < c₀`. -/
theorem vj_firstP {μ K m : Ordinal.{0}} (hμθ : μ < ConjT.th S)
    (hown : K ∈ S.CSet K (S.psi K (Om 1))) (hKW : Om ω ≤ K)
    (hcm : S.psi K (Om 1) ≤ m) (hm1 : m < S.psi (K + 1) (Om 1))
    (hdm : ∀ v, SC v → v ≤ Om 1 → m < v → ulD S 0 μ < v) :
    ∃ c0, ulH S 0 μ c0 = S.psi (K + Le.leOe μ) (Om 1) ∧ ∀ c < c0, ulH S 0 μ c ≤ m := by
  obtain ⟨⟨c0, hc0⟩, -, hmin, -⟩ := vj_leastP (S := S) hμθ hown hKW hcm hm1 hdm
  refine ⟨c0, hc0, fun c hc => not_lt.1 fun hlt => ?_⟩
  have h1 := hmin _ ⟨c, rfl⟩ hlt
  rw [← hc0] at h1
  exact absurd ((ulH_le_iff μ).1 h1) (not_le.2 hc)

/-- **The move of the first value**: for `μ ∈ MvD` and an own `K` with `c_n ≤ ψ_{Ω₁}(K)`,
`ψ_{Ω₁}(K + u_μ) < c_{n+1}`: `B_n` maps `ψ_{Ω₁}(K)`, `ψ_{Ω₁}(K + 1)`, `ψ_{Ω₁}(K + u_μ)` to `ψ_{Ω₁}(K')`,
`ψ_{Ω₁}(K' + 1)`, `ψ_{Ω₁}(K' + u_{B_n μ})` for an own `K'`. -/
theorem vj_B_least {n : ℕ} {μ K : Ordinal.{0}} (hDμ : MvD S μ)
    (hown : K ∈ S.CSet K (S.psi K (Om 1))) (hlo : Bc.bcC S n ≤ S.psi K (Om 1))
    (hownE : K + Le.leOe μ ∈ S.CSet (K + Le.leOe μ) (S.psi (K + Le.leOe μ) (Om 1)))
    (hEX : S.psi (K + Le.leOe μ) (Om 1) < Bc.bcC S (n + 1)) :
    ∃ K', K' ∈ S.CSet K' (S.psi K' (Om 1)) ∧ Bc.bcB S n (S.psi K (Om 1)) = S.psi K' (Om 1) ∧
      Bc.bcB S n (S.psi (K + 1) (Om 1)) = S.psi (K' + 1) (Om 1) ∧
      Bc.bcB S n (S.psi (K + Le.leOe μ) (Om 1)) = S.psi (K' + Le.leOe (Bc.bcB S n μ)) (Om 1) := by
  have h1Lw : (1 : Ordinal.{0}) < Nc.ncL S ω := Ri.ri_one_lt_L S
  have hown1 : K + 1 ∈ S.CSet (K + 1) (S.psi (K + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hown) (CSet.one_mem _ _)
  have h1X : S.psi (K + 1) (Om 1) < Bc.bcC S (n + 1) :=
    ((psi_mono (S := S) Low.InR_Om_one (add_le_add_right (one_le_iff_ne_zero.2 (rhU_ne μ)) K)).1).trans_lt hEX
  obtain ⟨hDu, hBu⟩ := vjB_Oe (n := n) hDμ
  obtain ⟨r, -, -, hownB', hBc', hBE⟩ := rdB_psi_baseD hown hlo hownE hEX hDu
  obtain ⟨r2, -, -, hownB2, hBc2, hB1⟩ := rdB_psi_baseD hown hlo hown1 h1X (mvD_of_lt h1Lw)
  set K' := bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) with hK'def
  set K2 := bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r2) with hK2def
  have hK2eq : K2 = K' := rh_own_inj hownB2 hownB' (hBc2.symm.trans hBc')
  rw [hK2eq, Mw.mwB_one] at hB1
  rw [hBu] at hBE
  exact ⟨K', hownB', hBc', hB1, hBE⟩

/-! ## The level and its data under `B_n` -/

/-- **`d(B_n μ) < B_n q ↔ d(μ) < q`** at a strongly critical `q < c_{n+1}`, for `μ ∈ MvD`. -/
theorem vj_datB {n : ℕ} {μ q : Ordinal.{0}} (hDμ : MvD S μ) (hq : SC q) (hqc : q < Bc.bcC S (n + 1)) :
    ulD S 0 (Bc.bcB S n μ) < Bc.bcB S n q ↔ ulD S 0 μ < q := by
  obtain ⟨hqL, hq1, hBq1⟩ := Tz.ti_win (n := n) hqc
  have hBq : SC (Bc.bcB S n q) := (Mx.mxB_SC_iff hqL).2 hq
  rw [ul_vis hBq, ul_vis hq]
  exact Uo.uo_K_B hDμ (mvD_of_lt hqL) hq hq1.le hBq hBq1.le

/-- **The level moves**: for `μ < θ` with `d(μ) < c_{n+1}`: `μ ∈ MvD`, `B_n μ < θ`, `B_n(μ + 1) = B_n μ + 1`. -/
theorem vj_B_lvl {n : ℕ} {μ : Ordinal.{0}} (hμθ : μ < ConjT.th S) (hd : ulD S 0 μ < Bc.bcC S (n + 1)) :
    MvD S μ ∧ Bc.bcB S n μ < ConjT.th S ∧ Bc.bcB S n (μ + 1) = Bc.bcB S n μ + 1 := by
  obtain ⟨-, -, hDμ⟩ := vjD_lev (Lw.lw_L_SC S _) (Bc.bcC_lt S (n + 1)).le hd
  obtain ⟨hDθ, hBθ⟩ := Lj.ljB_th (S := S) (n := n)
  refine ⟨hDμ, ?_, Rk.rkB_succ hDμ⟩
  have := (mvB_lt_iff (k := n) hDμ hDθ).2 hμθ
  rwa [hBθ] at this

/-- An `ε`-number `p ≥ θ` is a multiple of every `u_μ`, `μ ≤ θ`. -/
theorem vj_dvd_eps {μ p : Ordinal.{0}} (hμ : μ ≤ ConjT.th S) (hp : ω ^ p = p) (hG : ConjT.th S ≤ p) :
    Le.leOe μ ∣ p := by
  have hI : Indec p := inE_indec hp
  have hθE : ω ^ ConjT.th S = ConjT.th S := Gg.gg_SC_eps vj_th_SC
  have hk : Om 1 * μ ≤ p := by
    have hGG : Om 1 * ConjT.th S = ConjT.th S := by
      conv_lhs => rw [← Bt.Om1_opow, ← hθE]
      rw [← opow_add, Ordinal.add_of_omega0_opow_le (by rw [hθE, ← Rj.rj_Om1]; exact vj_Om1_lt_th) hθE.le, hθE]
    calc Om 1 * μ ≤ Om 1 * ConjT.th S := mul_le_mul_right hμ _
      _ = ConjT.th S := hGG
      _ ≤ p := hG
  refine rh_dvd_of_indec μ hI ?_
  unfold Le.leOe
  rw [← hp]
  exact opow_le_opow_right omega0_pos hk

theorem vj_th_le_OmW : ConjT.th S ≤ Om ω :=
  (vj_th_lt_Om2.trans (by rw [Uf.uf_Om2]; exact Om_lt_Om.2 (Ui.ui_s1_lt_omega (s := 1) one_lt_omega0))).le

/-- **`u_μ ∣ α_j`** for `μ ≤ θ`. -/
theorem vj_dvd_alpha {μ : Ordinal.{0}} (hμ : μ ≤ ConjT.th S) (j : ℕ) : Le.leOe μ ∣ bcAlpha S j := by
  have h1 : Le.leOe μ ∣ Om (ω : Ordinal.{0}) :=
    vj_dvd_eps hμ (Low.opow_eq_self_of_SC (SC_Om omega0_pos.ne')) vj_th_le_OmW
  have h2 : Le.leOe μ ∣ Nc.ncPp S :=
    vj_dvd_eps hμ (Low.opow_eq_self_of_SC (Nc.ncPp_SC S)) (Nc.ncTh_lt_Pp S).le
  exact dvd_add (dvd_add h1 h1) (dvd_mul_of_dvd_left h2 _)

/-- **`u_μ ∣ α_ω`** for `μ ≤ θ`. -/
theorem vj_dvd_alphaW {μ : Ordinal.{0}} (hμ : μ ≤ ConjT.th S) : Le.leOe μ ∣ bcAlphaW S := by
  have h1 : Le.leOe μ ∣ Om (ω : Ordinal.{0}) :=
    vj_dvd_eps hμ (Low.opow_eq_self_of_SC (SC_Om omega0_pos.ne')) vj_th_le_OmW
  refine dvd_add (dvd_add h1 h1) ?_
  have hE : ω ^ Nc.ncPp S = Nc.ncPp S := Low.opow_eq_self_of_SC (Nc.ncPp_SC S)
  have h2 : Le.leOe μ ∣ Nc.ncPp S := vj_dvd_eps hμ hE (Nc.ncTh_lt_Pp S).le
  have hI : Indec (ω ^ (Nc.ncPp S + 1)) :=
    indec_iff.2 ⟨(opow_pos _ omega0_pos).ne', isPrincipal_add_omega0_opow _⟩
  refine rh_dvd_of_indec μ hI ((Ordinal.le_of_dvd (inE_indec hE).ne_zero h2).trans ?_)
  conv_lhs => rw [← hE]
  exact opow_le_opow_right omega0_pos le_self_add

/-- **`σ` maps `u_μ ∣ |r|` to `u_{B_n μ} ∣ |σ r|`** on its domain, for `μ ∈ MvD`. -/
theorem vj_dvd_sig {n : ℕ} {μ : Ordinal.{0}} (hDμ : MvD S μ) {r : Term}
    (hr : bcD S r) (h : Le.leOe μ ∣ val S r) :
    Le.leOe (Bc.bcB S n μ) ∣ val S (bcSig (bcPre (n + 1)) bcPreW r) := by
  obtain ⟨hDu, hBu⟩ := vjB_Oe (n := n) hDμ
  have hle : ∀ v : Term, bcD S v → Le.leOe μ ≤ val S v →
      Le.leOe (Bc.bcB S n μ) ≤ val S (bcSig (bcPre (n + 1)) bcPreW v) := fun v hv hlv => by
    have hDv := mvD_of_term hv
    rw [← mvB_term (k := n) hv, ← hBu]
    exact not_lt.1 fun hlt => absurd ((mvB_lt_iff hDv hDu).1 hlt) (not_lt.2 hlv)
  by_cases h0 : r = Term.zero
  · subst h0; rw [bcSig_zero]; exact dvd_zero _
  have hN' := bc_NF (k := n) hr
  have h0' : bcSig (bcPre (n + 1)) bcPreW r ≠ Term.zero := bcSig_ne_zero h0
  rw [rd_dvd_iff_last (rhU_indec _) hN' h0', rbLast_sig]
  exact hle _ (rbLast_D hr) ((rd_dvd_iff_last (rhU_indec μ) hr.1 h0).1 h)

/-- **`u_μ ∣ B` gives `u_{B_n μ} ∣ B'`** for `B = α_{n+1} + |r|`, `B' = α_ω + |σ r|`, `μ ∈ MvD`, `μ, B_n μ ≤ θ`. -/
theorem vj_B_dvd {n : ℕ} {μ : Ordinal.{0}} (hDμ : MvD S μ) (hμθ : μ ≤ ConjT.th S)
    (hBμθ : Bc.bcB S n μ ≤ ConjT.th S) {B : Ordinal.{0}} {r : Term} (hr : bcD S r)
    (hB : B = bcAlpha S (n + 1) + val S r) (h : Le.leOe μ ∣ B) :
    Le.leOe (Bc.bcB S n μ) ∣ bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) := by
  rw [hB, rd_dvd_add_left (vj_dvd_alpha hμθ _)] at h
  rw [rd_dvd_add_left (vj_dvd_alphaW hBμθ)]
  exact vj_dvd_sig hDμ hr h

theorem vj_alphaW_W : (Om ω : Ordinal.{0}) ≤ bcAlphaW S := by
  unfold bcAlphaW; exact le_self_add.trans le_self_add

/-! ## Values, fixed points and runs under `B_n` -/

/-- **`B_n` maps a value `v = ψ_{Ω₁}(B) ∈ [c_n, c_{n+1})` of `Φ_μ` (`B` own) to a value of `Φ_{B_n μ}`**, for
`μ < θ` with `d(μ) < c_{n+1}`; the image is `ψ_{Ω₁}(B')` with `B'` own and `u_{B_n μ} ∣ B'`. -/
theorem vj_B_val {n : ℕ} {μ B : Ordinal.{0}} (hμθ : μ < ConjT.th S) (hdμ : ulD S 0 μ < Bc.bcC S (n + 1))
    (hown : B ∈ S.CSet B (S.psi B (Om 1))) (hlo : Bc.bcC S n ≤ S.psi B (Om 1))
    (hhi : S.psi B (Om 1) < Bc.bcC S (n + 1)) (hv : S.psi B (Om 1) ∈ range (ulH S 0 μ)) :
    ∃ r : Term, bcD S r ∧ B = bcAlpha S (n + 1) + val S r ∧
      bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) ∈
        S.CSet (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r))
          (S.psi (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r)) (Om 1)) ∧
      Le.leOe (Bc.bcB S n μ) ∣ bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) ∧
      Bc.bcB S n (S.psi B (Om 1)) = S.psi (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r)) (Om 1) ∧
      Bc.bcB S n (S.psi B (Om 1)) ∈ range (ulH S 0 (Bc.bcB S n μ)) := by
  obtain ⟨hDμ, hμ'θ, -⟩ := vj_B_lvl hμθ hdμ
  set v := S.psi B (Om 1) with hvdef
  have hvSC : SC v := SC_psi Low.InR_Om_one B
  have hvd : ulD S 0 μ < v := by obtain ⟨o, ho⟩ := hv; rw [← ho]; exact ulH_D_lt μ o
  have hdvd : Le.leOe μ ∣ B := vj_dvd_range hown fun j hj hd => vj_fix_lower hj hv hd
  obtain ⟨r, hDr, hBr, hownB', hBv, -⟩ := rdB_psi_baseD (d := 0) hown hlo (by rw [add_zero]; exact hown)
    (by rw [add_zero]; exact hhi) (mvD_of_lt (Lw.lw_L_SC S ω).1)
  set B' := bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) with hB'def
  have hdvd' : Le.leOe (Bc.bcB S n μ) ∣ B' := vj_B_dvd hDμ hμθ.le hμ'θ.le hDr hBr hdvd
  refine ⟨r, hDr, hBr, hownB', hdvd', hBv, ?_⟩
  have hB'0 : B' ≠ 0 := by
    rw [hB'def]
    exact (lt_of_lt_of_le (lt_of_le_of_lt zero_le (Bc.bcAlpha_lt_W S 0)) le_self_add).ne'
  have hB'W : Om ω ≤ B' := vj_alphaW_W.trans le_self_add
  have hdv' : ulD S 0 (Bc.bcB S n μ) < S.psi B' (Om 1) := by
    rw [← hBv]; exact (vj_datB hDμ hvSC hhi).2 hvd
  rw [hBv]
  exact vj_range (SC_psi Low.InR_Om_one _) hdv' fun j hj hdj =>
    vj_fwd (hj.trans hμ'θ) hownB' hB'W ((rhU_dvd_succ hj).trans hdvd') hB'0 hdj

/-- **`B_n` maps a fixed point `p = ψ_{Ω₁}(B) ∈ [c_n, c_{n+1})` of `Φ_μ` (`B` own) to a fixed point of
`Φ_{B_n μ}`**, for `μ < θ` with `d(μ) < c_{n+1}`. -/
theorem vj_B_fix {n : ℕ} {μ B : Ordinal.{0}} (hμθ : μ < ConjT.th S) (hdμ : ulD S 0 μ < Bc.bcC S (n + 1))
    (hown : B ∈ S.CSet B (S.psi B (Om 1))) (hlo : Bc.bcC S n ≤ S.psi B (Om 1))
    (hhi : S.psi B (Om 1) < Bc.bcC S (n + 1)) (hp : ulH S 0 μ (S.psi B (Om 1)) = S.psi B (Om 1)) :
    ulH S 0 (Bc.bcB S n μ) (Bc.bcB S n (S.psi B (Om 1))) = Bc.bcB S n (S.psi B (Om 1)) := by
  obtain ⟨hDμ, hμ'θ, hBsucc⟩ := vj_B_lvl hμθ hdμ
  have hθS := vj_th_SC (S := S)
  obtain ⟨r, hDr, hBr, hownB', -, hBv, -⟩ := vj_B_val hμθ hdμ hown hlo hhi ⟨_, hp⟩
  have hdvd1 : Le.leOe (μ + 1) ∣ B := vj_conv hown hp
  have hD1 : MvD S (μ + 1) := (mvB_add (k := n) hDμ Rk.rk_one_D).1
  have hdvd1' := vj_B_dvd hD1 (hθS.add_one_lt hμθ).le (by rw [hBsucc]; exact (hθS.add_one_lt hμ'θ).le) hDr hBr
    hdvd1
  rw [hBsucc] at hdvd1'
  have hB'0 : bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) ≠ 0 :=
    (lt_of_lt_of_le (lt_of_le_of_lt zero_le (Bc.bcAlpha_lt_W S 0)) le_self_add).ne'
  have hdμv : ulD S 0 μ < S.psi B (Om 1) := by rw [← hp]; exact ulH_D_lt μ _
  have hdv' : ulD S 0 (Bc.bcB S n μ) < Bc.bcB S n (S.psi B (Om 1)) :=
    (vj_datB hDμ (SC_psi Low.InR_Om_one B) hhi).2 hdμv
  rw [hBv] at hdv' ⊢
  exact vj_fwd hμ'θ hownB' (vj_alphaW_W.trans le_self_add) hdvd1' hB'0 hdv'

/-- **The run of `Φ_μ` from an own base point moves to a run of `Φ_{B_n μ}`** (`μ < θ`, `d(μ) < c_{n+1}`). -/
theorem vj_B_run {n : ℕ} {μ B0 c0 δ : Ordinal.{0}} (hμθ : μ < ConjT.th S) (hdμ : ulD S 0 μ < Bc.bcC S (n + 1))
    (hown0 : B0 ∈ S.CSet B0 (S.psi B0 (Om 1))) (hdvd0 : Le.leOe μ ∣ B0)
    (hc0 : ulH S 0 μ c0 = S.psi B0 (Om 1)) (hlo : Bc.bcC S n ≤ S.psi B0 (Om 1))
    (hd0 : ulD S 0 μ < S.psi B0 (Om 1))
    (hx : ulH S 0 μ (c0 + 1 + δ) < Bc.bcC S (n + 1))
    (hcond : ∀ σ, σ ≤ δ → c0 + 1 + σ < ulH S 0 μ (c0 + 1 + σ)) :
    ∃ B', B' ∈ S.CSet B' (S.psi B' (Om 1)) ∧ Le.leOe (Bc.bcB S n μ) ∣ B' ∧
      Bc.bcB S n (S.psi B0 (Om 1)) = S.psi B' (Om 1) ∧
      ∀ c1, ulH S 0 (Bc.bcB S n μ) c1 = S.psi B' (Om 1) →
        Bc.bcB S n (ulH S 0 μ (c0 + 1 + δ)) = ulH S 0 (Bc.bcB S n μ) (c1 + 1 + Bc.bcB S n δ) ∧
        ∀ σ, σ ≤ Bc.bcB S n δ → c1 + 1 + σ < ulH S 0 (Bc.bcB S n μ) (c1 + 1 + σ) := by
  obtain ⟨hDμ, hμ'θ, -⟩ := vj_B_lvl hμθ hdμ
  set x := ulH S 0 μ (c0 + 1 + δ) with hxdef
  obtain ⟨hxL, hx1, hBx1⟩ := Tz.ti_win (n := n) hx
  have h1L : (1 : Ordinal.{0}) < Nc.ncL S ω := Ri.ri_one_lt_L S
  set D := 1 + δ with hDdef
  have hcD : c0 + D = c0 + 1 + δ := (add_assoc c0 1 δ).symm
  have hDx : D < x := by
    rw [hxdef, ← hcD]
    have h := hcond δ le_rfl
    rw [← hcD] at h
    exact le_add_self.trans_lt h
  have hDL : D < Nc.ncL S ω := hDx.trans hxL
  have hδL : δ < Nc.ncL S ω := (le_add_self.trans_lt hDx).trans hxL
  have hcondD : ∀ d, d ≤ D → d < ulH S 0 μ (c0 + d) := by
    intro d hd
    rcases eq_or_ne d 0 with rfl | hd0
    · exact (ulH_SC μ _).1
    have hσ : 1 + (d - 1) = d := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hd0)
    have hσδ : d - 1 ≤ δ := by
      rw [← hσ] at hd; exact (add_le_add_iff_left 1).1 hd
    have h := hcond _ hσδ
    rw [add_assoc, hσ] at h
    exact le_add_self.trans_lt h
  have hW0 := vj_OmW_le_of_lo hlo
  obtain ⟨hval, hψ⟩ := vj_eqP hμθ hown0 hW0 hdvd0 hc0 hd0 (hDx.trans hx1) hcondD
  have hψx : S.psi (B0 + Le.leOe μ * D) (Om 1) = x := by rw [hψ, hcD]
  have hown1 : B0 + Le.leOe μ * D ∈ S.CSet (B0 + Le.leOe μ * D) (S.psi (B0 + Le.leOe μ * D) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add : B0 ≤ B0 + Le.leOe μ * D)).2 hown0)
      (vj_U_mem hμθ (hW0.trans le_self_add) (hd0.trans_le (psi_mono (S := S) Low.InR_Om_one le_self_add).1)
        hval)
  obtain ⟨r, hDr, hBr, hownB', hB0', hBx⟩ := rdB_psi_baseD hown0 hlo hown1
    (by rw [hψx]; exact hx) (vjB_Wpow (n := n) hDμ (mvD_of_lt hDL) |> fun h => by
      rw [vj_Oe_eq']; exact h.1)
  set B' := bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) with hB'def
  have hdvd' : Le.leOe (Bc.bcB S n μ) ∣ B' := vj_B_dvd hDμ hμθ.le hμ'θ.le hDr hBr hdvd0
  rw [hψx] at hBx
  have hBm : Bc.bcB S n (Le.leOe μ * D) = Le.leOe (Bc.bcB S n μ) * Bc.bcB S n D := by
    rw [vj_Oe_eq', vj_Oe_eq']; exact (vjB_Wpow (n := n) hDμ (mvD_of_lt hDL)).2
  rw [hBm] at hBx
  have hBDx : Bc.bcB S n D < Bc.bcB S n x := (Bc.bcB_lt_iff hDL hxL).2 hDx
  have hval' : Bc.bcB S n D < S.psi (B' + Le.leOe (Bc.bcB S n μ) * Bc.bcB S n D) (Om 1) := by
    rw [← hBx]; exact hBDx
  have hBD : Bc.bcB S n D = 1 + Bc.bcB S n δ := by rw [hDdef, Bc.bcB_add h1L hδL, Mw.mwB_one]
  refine ⟨B', hownB', hdvd', hB0', fun c1 hc1 => ?_⟩
  have hcondD' := vj_validP hdvd' hc1 hval'
  have hvL : S.psi B0 (Om 1) < Bc.bcC S (n + 1) := by
    rw [← hc0]; exact ((ulH_le_iff μ).2 (le_self_add.trans le_self_add)).trans_lt hx
  have hd1 : ulD S 0 (Bc.bcB S n μ) < S.psi B' (Om 1) := by
    rw [← hB0']; exact (vj_datB hDμ (SC_psi Low.InR_Om_one B0) hvL).2 hd0
  have hBxF : Bc.bcB S n x = ulH S 0 (Bc.bcB S n μ) (c1 + Bc.bcB S n D) := by
    rw [hBx]
    exact (vj_eqP hμ'θ hownB' (vj_alphaW_W.trans le_self_add) hdvd' hc1 hd1 (hBDx.trans hBx1) hcondD').2
  refine ⟨by rw [hBxF, hBD, add_assoc], fun σ hσ => ?_⟩
  have h1 := hcondD' (1 + σ) (by rw [hBD]; exact (add_le_add_iff_left 1).2 hσ)
  have h2 : c1 < ulH S 0 (Bc.bcB S n μ) (c1 + (1 + σ)) :=
    (ulH_le_self _ c1).trans_lt
      ((ulH_lt_iff _).2 (lt_add_of_pos_right _ (lt_of_lt_of_le zero_lt_one le_self_add)))
  rw [add_assoc]
  exact (Lq.lq_SC_indec (ulH_SC _ _)).add_lt h2 h1

end Googology.Trans.PoR.InaccPsi.R2.Vj
