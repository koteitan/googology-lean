import Googology.Trans.PoR.InaccPsi.R2.RkPsi
import Googology.Trans.PoR.InaccPsi.R2.CitedRk
import Googology.Trans.PoR.InaccPsi.R2.RjFacts

/-!
# `ϑᵗ(Ω₁·(Ω₁ + μ) + η)` at every level `μ < ε_{Ω₁+1}`: the values of `Φ_μ` above `τ`

For a strongly critical base `τ < Ω₁`, `Φ_μ = Rk.rkP μ`, `rkDat μ = rjDat (Ω₁ + μ)`, `Δ_μ = Ω₁·(Ω₁ + μ)` (the level
`M = Ω₁ + μ` of `R2.CitedRj`), from the generic cited facts of `R2.CitedRj` (through `Rj.rjK_facts`, `Rj.rjK_SC`,
`Rj.rjK_lt`, `Rj.rjK_lt_lower`, `R2.rjLt_of_vt_lt`) and `R2.CitedRk` (`rkArg_dat`, the data of a lower level):

* `rkK_facts`, `rkK_lt`, `rkK_lt_lower`, `rkK_SC` (at every level `μ < ε_{Ω₁+1}` with `rkDat μ ∈ Tᵗ`);
* `RkKLE τ μ` (`ϑᵗ(Δ_μ + η) ≤ Φ_μ(τ + η + 1)`), `RkKREP2 τ μ` (**every value `w ∈ Tᵗ ∩ (τ, Ω₁)` of `Φ_μ` that is
  not a fixed point of `Φ_μ` is `ϑᵗ(Δ_μ + σ)`, `σ < w`**), proved together by induction on `μ` (`rkK_le`,
  `rkK_rep2`) for a base `τ` that is a fixed point of every `Φ_μ`, `rkDat μ < τ`;
* `rkK_fixv2` (**`ϑᵗ(Δ_μ + η)` is a fixed point of every `Φ_j`, `j < μ`, `rkDat j < ϑᵗ(Δ_μ + η)`**), `rkK_enum`
  (**`ϑᵗ(Δ_μ + η) = Φ_μ(τ + 1 + η)`** for `rkDat μ < τ`), `rkK_enum0` (**`ϑᵗ(Δ_μ + η) = Φ_μ(η)`** for
  `rkDat μ ≥ τ`: the values of `Φ_μ` all lie above `rkDat μ`), `rkK_enum_fix2` (**`ϑᵗ(Δ_μ + (p + δ)) =
  Φ_μ(p + 1 + δ)`** for a fixed point `p > τ` of `Φ_μ`), and the `ζ`-values `rkK_zeta`, `rkK_zeta0`,
  `rkK_zeta_fix2`, `rkK_zeta_fix_add2`.

The proofs of `R2.RiTh` with the generic levels.  New definitions: the statement names `RkKLE`, `RkKREP2`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rk

open Ordinal Order Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Lq
  Googology.Trans.PoR.InaccPsi.R2.Rb Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Trans.PoR.InaccPsi.R2.Rh
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj

/-- `rkDat j ∈ Tᵗ` from `rkDat j < v ∈ Tᵗ ∩ Ω₁`. -/
theorem rkK_dat_T {τ j v : Ordinal.{0}} (hτE : InE τ) (hτ1 : τ < Om1) (hvT : v ∈ Tset τ) (hv1 : v < Om1)
    (h : rkDat j < v) : rkDat j ∈ Tset τ := vz_T_down hτE hτ1 hvT hv1 h.le

/-- **LE(μ)**: `ϑᵗ(Δ_μ + η) ≤ Φ_μ(τ + η + 1)` for every `η ∈ Tᵗ ∩ Ω₁`. -/
def RkKLE (τ μ : Ordinal.{0}) : Prop :=
  ∀ η, η ∈ Tset τ → η < Om1 → vt τ (Om1 * (Om1 + μ) + η) ≤ rkP μ (τ + η + 1)

/-- **REP2(μ)**: every value `w ∈ Tᵗ ∩ (τ, Ω₁)` of `Φ_μ` with `rkDat μ < w` (strongly critical, a fixed point of
every `Φ_j`, `j < μ`, `rkDat j < w`) that is not a fixed point of `Φ_μ` is `ϑᵗ(Δ_μ + σ)` with `σ ∈ Tᵗ`, `σ < w`. -/
def RkKREP2 (τ μ : Ordinal.{0}) : Prop :=
  ∀ w, SC w → (∀ j < μ, rkDat j < w → rkP j w = w) → τ < w → rkDat μ < w → w ∈ Tset τ → w < Om1 →
    rkP μ w ≠ w → ∃ σ, σ ∈ Tset τ ∧ σ < Om1 ∧ σ < w ∧ vt τ (Om1 * (Om1 + μ) + σ) = w

section Base

variable {τ : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1)
include hτ hτ1

/-- **The facts on `ϑᵗ(Δ_μ + η)`** (`Rj.rjK_facts` at `M = Ω₁ + μ`). -/
theorem rkK_facts {μ : Ordinal.{0}} (hμT : rkDat μ ∈ Tset τ) (hμΩ : μ < ggE) {η : Ordinal.{0}}
    (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    Om1 * (Om1 + μ) + η ∈ Tset τ ∧ Om1 * (Om1 + μ) + η < OmTwo ∧
    vt τ (Om1 * (Om1 + μ) + η) ∈ Tset τ ∧ τ < vt τ (Om1 * (Om1 + μ) + η) ∧
    vt τ (Om1 * (Om1 + μ) + η) < Om1 ∧ InE (vt τ (Om1 * (Om1 + μ) + η)) ∧
    rkDat μ < vt τ (Om1 * (Om1 + μ) + η) ∧ η < vt τ (Om1 * (Om1 + μ) + η) := by
  obtain ⟨a, b, c, d, e, f, -, g1, g2⟩ := rjK_facts hτ hτ1 le_self_add (rk_Om1_add_lt hμΩ) hμT hη hηΩ
  exact ⟨a, b, c, d, e, f, g1, g2⟩

/-- **`η ↦ ϑᵗ(Δ_μ + η)` is strictly increasing.** -/
theorem rkK_lt {μ : Ordinal.{0}} (hμT : rkDat μ ∈ Tset τ) (hμΩ : μ < ggE) {σ η : Ordinal.{0}}
    (hσ : σ ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1) (h : σ < η) :
    vt τ (Om1 * (Om1 + μ) + σ) < vt τ (Om1 * (Om1 + μ) + η) :=
  rjK_lt hτ hτ1 le_self_add (rk_Om1_add_lt hμΩ) hμT hσ hη hηΩ h

/-- **`ϑᵗ(Δ_j + σ) < ϑᵗ(Δ_μ + η)`** for `j < μ` and `σ`, `rkDat j` below the right side. -/
theorem rkK_lt_lower {j μ : Ordinal.{0}} (hμT : rkDat μ ∈ Tset τ) (hμΩ : μ < ggE) (hjk : j < μ)
    {σ η : Ordinal.{0}} (hσ : σ ∈ Tset τ) (hσΩ : σ < Om1) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (hσv : σ < vt τ (Om1 * (Om1 + μ) + η)) (hjv : rkDat j < vt τ (Om1 * (Om1 + μ) + η)) :
    vt τ (Om1 * (Om1 + j) + σ) < vt τ (Om1 * (Om1 + μ) + η) :=
  rjK_lt_lower hτ hτ1 le_self_add (rk_Om1_add_lt hμΩ) hμT ((add_lt_add_iff_left _).2 hjk) hσ hσΩ hη hηΩ
    hσv hjv

/-- **`ϑᵗ(Δ_μ + η)` is strongly critical.** -/
theorem rkK_SC {μ : Ordinal.{0}} (hμT : rkDat μ ∈ Tset τ) (hμΩ : μ < ggE) {η : Ordinal.{0}}
    (hη : η ∈ Tset τ) (hηΩ : η < Om1) : SC (vt τ (Om1 * (Om1 + μ) + η)) :=
  rjK_SC hτ hτ1 le_self_add (rk_Om1_add_lt hμΩ) hμT hη hηΩ

/-- **Minimality at level `μ`**: `ϑᵗ(Δ_μ + η) ≤ s` for every strongly critical `s > τ, η, rkDat μ` that is a fixed
point of every `Φ_j`, `j < μ`, `rkDat j < s`, above all `ϑᵗ(Δ_μ + σ)`, `σ < η`, given LE at the levels below `μ`
whose data lie in `Tᵗ`. -/
theorem rkK_min {μ : Ordinal.{0}} (hμT : rkDat μ ∈ Tset τ) (hμΩ : μ < ggE)
    (hLE : ∀ j < μ, rkDat j ∈ Tset τ → RkKLE τ j)
    {η s : Ordinal.{0}} (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (hs : SC s) (hsF : ∀ j < μ, rkDat j < s → rkP j s = s) (hτs : τ < s) (hηs : η < s) (hμs : rkDat μ < s)
    (hprev : ∀ σ, σ < η → vt τ (Om1 * (Om1 + μ) + σ) < s) :
    vt τ (Om1 * (Om1 + μ) + η) ≤ s := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  obtain ⟨-, -, hvT, -, hv1, -, -, -⟩ := rkK_facts hτ hτ1 hμT hμΩ hη hηΩ
  by_contra hlt
  push Not at hlt
  obtain ⟨m, -, -, -, hTm, hm1, -⟩ := vz_next hτE hτ1
  have hvm : vt τ (Om1 * (Om1 + μ) + η) < m := (hTm _ hv1).1 hvT
  have hs1 : s < Om1 := hlt.trans hv1
  have hsT : s ∈ Tset τ := (hTm s hs1).2 (hlt.trans hvm)
  have hsE : InE s := Gg.gg_SC_eps hs
  have hsP : Indec s := inE_indec hsE
  obtain ⟨ξ, hξT, hξ2, hξs⟩ := vt_rep hτE hτ1 hsT hτs.le hs1 hsP
  have hlt' : vt τ ξ < vt τ (Om1 * (Om1 + μ) + η) := by rw [hξs]; exact hlt
  have hξlt : ξ < Om1 * (Om1 + μ) + η :=
    rjLt_of_vt_lt hτE hτ1 hξT hξ2 le_self_add (rk_Om1_add_lt hμΩ) hμT hη hηΩ
      (by rw [hξs]; exact hμs) (by rw [hξs]; exact hηs) hlt'
  rcases lt_or_ge ξ (Om1 * Om1) with hξ | hξ
  · rcases lt_or_ge ξ Om1 with hξ1 | hξ1
    · have := (vt_E_iff hτE hτ1 hξT hξ2).1 ⟨by rw [hξs]; exact hτs, by rw [hξs]; exact hsE⟩
      exact absurd this (not_le.2 hξ1)
    · obtain ⟨hq1, hrT, hr1, hdec⟩ := Lu.lu_split hτE hτ1 hξT hξ2 hξ1
      have hqT : ξ / Om1 ∈ Tset τ := lgQuot_mem hτE hτ1 hξT hξ
      have hqΩ : ξ / Om1 < Om1 := (Ordinal.lt_mul_iff_div_lt rj_Om1_pos.ne').1 hξ
      exact Mx.mxSC_ne_th hτE hτ1 hq1 hqT hqΩ hrT hr1 hs (by rw [hdec, hξs])
  · rcases lt_or_ge ξ (Om1 * (Om1 + μ)) with hξ' | hξ'
    · -- a lower level `j < μ`: `s = ϑᵗ(Δ_j + σ)` is not a fixed point of `Φ_j`
      obtain ⟨j, hjk, σ, hσΩ, he⟩ := Ri.riK_decomp hξ hξ'
      have hjΩ : j < ggE := hjk.trans hμΩ
      have hσT : σ ∈ Tset τ := vzRem_T hτE hτ1 hξT hξ2 he (dvd_mul_right _ _) hσΩ
      have hjT : rkDat j ∈ Tset τ := by
        have hξT' : Om1 * (Om1 + j) + σ ∈ Tset τ := by rw [← he]; exact hξT
        exact rkArg_dat hτE hτ1 le_self_add (rk_Om1_add_lt hjΩ) hσΩ hξT'
      have hle := hLE j hjk hjT σ hσT hσΩ
      rw [← he, hξs] at hle
      obtain ⟨-, -, -, -, -, -, hjv, hσv⟩ := rkK_facts hτ hτ1 hjT hjΩ hσT hσΩ
      rw [← he, hξs] at hσv hjv
      have h3 : τ + σ + 1 < s := hs.add_one_lt ((lq_SC_indec hs).add_lt hτs hσv)
      have h4 : rkP j (τ + σ + 1) < s := by
        conv_rhs => rw [← hsF j hjk hjv]
        exact (rkP_lt_iff j).2 h3
      exact absurd hle (not_le.2 h4)
    · have hσe : Om1 * (Om1 + μ) + (ξ - Om1 * (Om1 + μ)) = ξ := Ordinal.add_sub_cancel_of_le hξ'
      have hσ : ξ - Om1 * (Om1 + μ) < η := by
        rw [← hσe] at hξlt; exact (add_lt_add_iff_left _).1 hξlt
      have h := hprev _ hσ
      rw [hσe, hξs] at h
      exact lt_irrefl _ h

/-- **LE(μ)** from LE at the levels below `μ` whose data lie in `Tᵗ`. -/
theorem rkK_le_of {μ : Ordinal.{0}} (hμT : rkDat μ ∈ Tset τ) (hμΩ : μ < ggE)
    (hLE : ∀ j < μ, rkDat j ∈ Tset τ → RkKLE τ j) : RkKLE τ μ := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  intro η
  induction η using WellFoundedLT.induction with
  | ind η IH =>
  intro hη hηΩ
  refine rkK_min hτ hτ1 hμT hμΩ hLE hη hηΩ (rkP_SC μ _)
    (fun j hj hd => rkP_fix_lower hj ⟨_, rfl⟩ hd) ?_ ?_ ?_ fun σ hσ => ?_
  · exact (lt_of_le_of_lt le_self_add (lt_add_one _)).trans_le (rkP_le_self μ _)
  · exact lt_of_le_of_lt (le_add_self : η ≤ τ + η) ((lt_add_one (τ + η)).trans_le (rkP_le_self μ _))
  · exact rkDat_lt_rkP μ _
  · have hσT : σ ∈ Tset τ := vz_T_down hτE hτ1 hη hηΩ hσ.le
    refine (IH σ hσ hσT (hσ.trans hηΩ)).trans_lt ((rkP_lt_iff μ).2 ?_)
    exact (Order.add_one_le_of_lt ((add_lt_add_iff_left τ).2 hσ)).trans_lt (lt_add_one _)

/-- **LE(μ) at every level `μ < Ω₁·Ω₁` with `rkDat μ ∈ Tᵗ`.** -/
theorem rkK_le (μ : Ordinal.{0}) : μ < ggE → rkDat μ ∈ Tset τ → RkKLE τ μ := by
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμΩ hμT
  exact rkK_le_of hτ hτ1 hμT hμΩ fun j hj hjT => IH j hj (hj.trans hμΩ) hjT

/-- **`ϑᵗ(Δ_μ + η)` is a fixed point of every `Φ_j`, `j < μ`, with `rkDat j` below it**, given REP2 at the levels
below `μ` whose data lie in `Tᵗ`. -/
theorem rkK_fixv2_of {μ : Ordinal.{0}} (hμT : rkDat μ ∈ Tset τ) (hμΩ : μ < ggE)
    (hREP : ∀ j < μ, rkDat j ∈ Tset τ → RkKREP2 τ j) {η : Ordinal.{0}} (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    ∀ j < μ, rkDat j < vt τ (Om1 * (Om1 + μ) + η) →
      rkP j (vt τ (Om1 * (Om1 + μ) + η)) = vt τ (Om1 * (Om1 + μ) + η) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  obtain ⟨-, -, hvT, hτv, hv1, -, -, -⟩ := rkK_facts hτ hτ1 hμT hμΩ hη hηΩ
  have hvSC := rkK_SC hτ hτ1 hμT hμΩ hη hηΩ
  intro j
  induction j using WellFoundedLT.induction with
  | ind j IHj =>
  intro hjk hjv
  by_contra hnf
  obtain ⟨σ, hσT, hσΩ, hσv, he⟩ :=
    hREP j hjk (rkK_dat_T hτE hτ1 hvT hv1 hjv) _ hvSC (fun i hi hiv => IHj i hi (hi.trans hjk) hiv) hτv hjv
      hvT hv1 hnf
  have := rkK_lt_lower hτ hτ1 hμT hμΩ hjk hσT hσΩ hη hηΩ hσv hjv
  rw [he] at this
  exact lt_irrefl _ this

omit hτ hτ1 in
/-- `ϑᵗ(Δ_μ + σ) < p` for `σ < p` and every fixed point `p > τ` of `Φ_μ`, given LE(μ). -/
theorem rkK_below_fix_of {μ : Ordinal.{0}} (hLEk : RkKLE τ μ) {p : Ordinal.{0}} (hp : rkP μ p = p)
    (hτp : τ < p) (hp1 : p < Om1) {σ : Ordinal.{0}} (hσT : σ ∈ Tset τ) (hσ : σ < p) :
    vt τ (Om1 * (Om1 + μ) + σ) < p := by
  have hpSC : SC p := hp ▸ rkP_SC μ p
  have h1 : τ + σ + 1 < p := hpSC.add_one_lt ((lq_SC_indec hpSC).add_lt hτp hσ)
  refine (hLEk σ hσT (hσ.trans hp1)).trans_lt ?_
  conv_rhs => rw [← hp]
  exact (rkP_lt_iff μ).2 h1

/-- **`ϑᵗ(Δ_μ + η) = Φ_μ(c₀ + η)`** for `c₀` with `Φ_μ(c₀) > rkDat μ ≥ Φ_μ(c)`, `c < c₀`, `τ ≤ rkDat μ`, when
`c₀ + σ < Φ_μ(c₀+σ)` for every `σ ≤ η`. -/
theorem rkK_enum0_of {μ c0 : Ordinal.{0}} (hμT : rkDat μ ∈ Tset τ) (hμΩ : μ < ggE) (hτμ : τ ≤ rkDat μ)
    (hREP : ∀ j < μ, rkDat j ∈ Tset τ → RkKREP2 τ j) (hc0 : rkDat μ < rkP μ c0)
    (hmin : ∀ c < c0, rkP μ c ≤ rkDat μ) :
    ∀ η, η ∈ Tset τ → η < Om1 → (∀ σ, σ ≤ η → c0 + σ < rkP μ (c0 + σ)) →
      vt τ (Om1 * (Om1 + μ) + η) = rkP μ (c0 + η) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have hLE : ∀ j < μ, rkDat j ∈ Tset τ → RkKLE τ j := fun j hj hjT => rkK_le hτ hτ1 j (hj.trans hμΩ) hjT
  intro η
  induction η using WellFoundedLT.induction with
  | ind η IH =>
  intro hη hηΩ hcond
  have hIH : ∀ σ, σ < η → vt τ (Om1 * (Om1 + μ) + σ) = rkP μ (c0 + σ) := fun σ hσ =>
    IH σ hσ (vz_T_down hτE hτ1 hη hηΩ hσ.le) (hσ.trans hηΩ) fun σ' hσ' => hcond σ' (hσ'.trans hσ.le)
  have hμs : rkDat μ < rkP μ (c0 + η) := hc0.trans_le ((rkP_le_iff μ).2 le_self_add)
  apply le_antisymm
  · refine rkK_min hτ hτ1 hμT hμΩ hLE hη hηΩ (rkP_SC μ _) (fun j hj hd => rkP_fix_lower hj ⟨_, rfl⟩ hd)
      (hτμ.trans_lt hμs) (le_add_self.trans_lt (hcond η le_rfl)) hμs fun σ hσ => ?_
    rw [hIH σ hσ]; exact (rkP_lt_iff μ).2 ((add_lt_add_iff_left _).2 hσ)
  · obtain ⟨-, -, -, -, hv1, -, hμv, -⟩ := rkK_facts hτ hτ1 hμT hμΩ hη hηΩ
    obtain ⟨e, he⟩ := rkP_range (rkK_SC hτ hτ1 hμT hμΩ hη hηΩ) hμv
      (rkK_fixv2_of hτ hτ1 hμT hμΩ hREP hη hηΩ)
    rw [← he]
    refine (rkP_le_iff μ).2 (not_lt.1 fun hlt => ?_)
    rcases lt_or_ge e c0 with hec | hce
    · have := hmin e hec
      rw [he] at this
      exact absurd hμv (not_lt.2 this)
    · have hσe : c0 + (e - c0) = e := Ordinal.add_sub_cancel_of_le hce
      have hσ : e - c0 < η := by rw [← hσe] at hlt; exact (add_lt_add_iff_left _).1 hlt
      have h1 := rkK_lt hτ hτ1 hμT hμΩ (vz_T_down hτE hτ1 hη hηΩ hσ.le) hη hηΩ hσ
      rw [hIH _ hσ, hσe, he] at h1
      exact lt_irrefl _ h1

/-- **`ϑᵗ(Δ_μ + (p + δ)) = Φ_μ(p + 1 + δ)`** for a fixed point `p > τ` of `Φ_μ` when `p + 1 + σ < Φ_μ(p+1+σ)` for
every `σ ≤ δ`. -/
theorem rkK_enum_fix2_of {μ : Ordinal.{0}} (hμT : rkDat μ ∈ Tset τ) (hμΩ : μ < ggE)
    (hREP : ∀ j < μ, rkDat j ∈ Tset τ → RkKREP2 τ j) {p : Ordinal.{0}} (hp : rkP μ p = p) (hτp : τ < p) :
    ∀ δ, p + δ ∈ Tset τ → p + δ < Om1 → (∀ σ, σ ≤ δ → p + 1 + σ < rkP μ (p + 1 + σ)) →
      vt τ (Om1 * (Om1 + μ) + (p + δ)) = rkP μ (p + 1 + δ) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have hLE : ∀ j < μ, rkDat j ∈ Tset τ → RkKLE τ j := fun j hj hjT => rkK_le hτ hτ1 j (hj.trans hμΩ) hjT
  have hLEk := rkK_le hτ hτ1 μ hμΩ hμT
  intro δ
  induction δ using WellFoundedLT.induction with
  | ind δ IH =>
  intro hT h1 hcond
  have hp1 : p < Om1 := (le_self_add : p ≤ p + δ).trans_lt h1
  have hIH : ∀ δ', δ' < δ →
      vt τ (Om1 * (Om1 + μ) + (p + δ')) = rkP μ (p + 1 + δ') := fun δ' hδ' =>
    IH δ' hδ' (vz_T_down hτE hτ1 hT h1 ((add_le_add_iff_left p).2 hδ'.le))
      (((add_lt_add_iff_left p).2 hδ').trans h1) fun σ hσ => hcond σ (hσ.trans hδ'.le)
  have hpg : p < rkP μ (p + 1 + δ) := by
    conv_lhs => rw [← hp]
    exact (rkP_lt_iff μ).2 (lt_of_lt_of_le (lt_add_one p) le_self_add)
  apply le_antisymm
  · refine rkK_min hτ hτ1 hμT hμΩ hLE hT h1 (rkP_SC μ _) (fun j hj hd => rkP_fix_lower hj ⟨_, rfl⟩ hd)
      (hτp.trans hpg) ?_ ((rkDat_lt_fix hp).trans hpg) fun σ hσ => ?_
    · have : p + δ ≤ p + 1 + δ := by
        rw [add_assoc]; exact (add_le_add_iff_left p).2 le_add_self
      exact this.trans_lt (hcond δ le_rfl)
    · rcases lt_or_ge σ p with hσp | hσp
      · exact (rkK_below_fix_of hLEk hp hτp hp1
          (vz_T_down hτE hτ1 hT h1 (hσp.le.trans le_self_add)) hσp).trans hpg
      · have he : p + (σ - p) = σ := Ordinal.add_sub_cancel_of_le hσp
        have hδ' : σ - p < δ := by rw [← he] at hσ; exact (add_lt_add_iff_left p).1 hσ
        rw [← he, hIH _ hδ']
        exact (rkP_lt_iff μ).2 ((add_lt_add_iff_left _).2 hδ')
  · obtain ⟨-, -, -, -, hv1, -, hμv, hηv⟩ := rkK_facts hτ hτ1 hμT hμΩ hT h1
    obtain ⟨e, he⟩ := rkP_range (rkK_SC hτ hτ1 hμT hμΩ hT h1) hμv
      (rkK_fixv2_of hτ hτ1 hμT hμΩ hREP hT h1)
    rw [← he]
    refine (rkP_le_iff μ).2 (not_lt.1 fun hlt => ?_)
    have hpe : p < e := by
      refine (rkP_lt_iff μ).1 ?_
      rw [hp, he]; exact (le_self_add : p ≤ p + δ).trans_lt hηv
    have hp1e : p + 1 ≤ e := Order.add_one_le_of_lt hpe
    have hσe : p + 1 + (e - (p + 1)) = e := Ordinal.add_sub_cancel_of_le hp1e
    have hσ : e - (p + 1) < δ := by rw [← hσe] at hlt; exact (add_lt_add_iff_left _).1 hlt
    have hT' : p + (e - (p + 1)) ∈ Tset τ := vz_T_down hτE hτ1 hT h1 ((add_le_add_iff_left p).2 hσ.le)
    have h2 := rkK_lt hτ hτ1 hμT hμΩ hT' hT h1 ((add_lt_add_iff_left p).2 hσ)
    rw [hIH _ hσ, hσe, he] at h2
    exact lt_irrefl _ h2

end Base

section Fix

variable {τ : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1)
  (hτF : ∀ μ, μ < ggE → rkDat μ < τ → rkP μ τ = τ)
include hτ hτ1 hτF

/-- **`ϑᵗ(Δ_μ + η) = Φ_μ(τ + 1 + η)`** (`rkDat μ < τ`) when `1 + σ < Φ_μ(τ+1+σ)` for every `σ ≤ η`. -/
theorem rkK_enum_of {μ : Ordinal.{0}} (hμΩ : μ < ggE) (hμτ : rkDat μ < τ)
    (hREP : ∀ j < μ, rkDat j ∈ Tset τ → RkKREP2 τ j) :
    ∀ η, η ∈ Tset τ → η < Om1 → (∀ σ, σ ≤ η → 1 + σ < rkP μ (τ + 1 + σ)) →
      vt τ (Om1 * (Om1 + μ) + η) = rkP μ (τ + 1 + η) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have hμT : rkDat μ ∈ Tset τ := mem_T_of_le hτE hτ1 hμτ.le
  have hLE : ∀ j < μ, rkDat j ∈ Tset τ → RkKLE τ j := fun j hj hjT => rkK_le hτ hτ1 j (hj.trans hμΩ) hjT
  intro η
  induction η using WellFoundedLT.induction with
  | ind η IH =>
  intro hη hηΩ hcond
  have hIH : ∀ σ, σ < η → vt τ (Om1 * (Om1 + μ) + σ) = rkP μ (τ + 1 + σ) := fun σ hσ =>
    IH σ hσ (vz_T_down hτE hτ1 hη hηΩ hσ.le) (hσ.trans hηΩ) fun σ' hσ' => hcond σ' (hσ'.trans hσ.le)
  have hτs : τ < rkP μ (τ + 1 + η) := by
    conv_lhs => rw [← hτF μ hμΩ hμτ]
    exact (rkP_lt_iff μ).2 ((lt_add_one τ).trans_le le_self_add)
  apply le_antisymm
  · refine rkK_min hτ hτ1 hμT hμΩ hLE hη hηΩ (rkP_SC μ _) (fun j hj hd => rkP_fix_lower hj ⟨_, rfl⟩ hd)
      hτs ?_ (hμτ.trans hτs) fun σ hσ => ?_
    · exact (le_add_self).trans_lt (hcond η le_rfl)
    · rw [hIH σ hσ]; exact (rkP_lt_iff μ).2 ((add_lt_add_iff_left _).2 hσ)
  · obtain ⟨-, -, -, hτv, hv1, -, hμv, -⟩ := rkK_facts hτ hτ1 hμT hμΩ hη hηΩ
    obtain ⟨e, he⟩ := rkP_range (rkK_SC hτ hτ1 hμT hμΩ hη hηΩ) hμv
      (rkK_fixv2_of hτ hτ1 hμT hμΩ hREP hη hηΩ)
    rw [← he]
    refine (rkP_le_iff μ).2 (not_lt.1 fun hlt => ?_)
    have hce : τ < e := (rkP_lt_iff μ).1 (by rw [hτF μ hμΩ hμτ, he]; exact hτv)
    have hc1 : τ + 1 ≤ e := Order.add_one_le_of_lt hce
    have hσe : τ + 1 + (e - (τ + 1)) = e := Ordinal.add_sub_cancel_of_le hc1
    have hσ : e - (τ + 1) < η := by rw [← hσe] at hlt; exact (add_lt_add_iff_left _).1 hlt
    have h1 := rkK_lt hτ hτ1 hμT hμΩ (vz_T_down hτE hτ1 hη hηΩ hσ.le) hη hηΩ hσ
    rw [hIH _ hσ, hσe, he] at h1
    exact lt_irrefl _ h1

/-- **REP2(μ)** at every level `μ < Ω₁·Ω₁`, `rkDat μ ∈ Tᵗ`, from REP2 at the levels below `μ`. -/
theorem rkK_rep2_of {μ : Ordinal.{0}} (hμT : rkDat μ ∈ Tset τ) (hμΩ : μ < ggE)
    (hREP : ∀ j < μ, rkDat j ∈ Tset τ → RkKREP2 τ j) : RkKREP2 τ μ := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  intro w hw hwF hτw hμw hwT hw1 hnf
  obtain ⟨y, hy⟩ := rkP_range hw hμw hwF
  have hyw : y < w := by
    refine lt_of_le_of_ne (hy ▸ rkP_le_self μ y) fun e => hnf ?_
    rw [← e] at hy ⊢; rw [hy]
  obtain ⟨p, hbase, hpw, hmax⟩ := rh_base_below (rkP_normal μ) hτw hnf
  have hnofix : ∀ z, p < z → z < w → z < rkP μ z := by
    intro z hpz hzw
    by_contra h
    push Not at h
    have hz := le_antisymm h (rkP_le_self μ z)
    have hτz : τ < z := by
      rcases hbase with e | ⟨h', -⟩
      · rw [← e]; exact hpz
      · exact h'.trans hpz
    exact absurd (hmax z hz hτz hzw) (not_le.2 hpz)
  by_cases hcase : p = τ ∧ τ ≤ rkDat μ
  · -- no fixed point of `Φ_μ` in `(τ, w)` and `rkDat μ ≥ τ`: the base `c₀`
    obtain ⟨hpτ, hτμ⟩ := hcase
    set c0 : Ordinal.{0} := 0 with hc0def
    have hc0 : rkDat μ < rkP μ c0 := rkDat_lt_rkP μ c0
    have hmin : ∀ c < c0, rkP μ c ≤ rkDat μ := fun c hc => absurd hc (not_lt.2 zero_le)
    have hc0y : c0 ≤ y := by
      refine not_lt.1 fun hlt => ?_
      have := hmin y hlt
      rw [hy] at this
      exact absurd hμw (not_lt.2 this)
    set D := y - c0 with hDdef
    have hcD : c0 + D = y := Ordinal.add_sub_cancel_of_le hc0y
    have hDw : D < w := (Ordinal.sub_le_self y c0).trans_lt hyw
    have hcond : ∀ σ, σ ≤ D → c0 + σ < rkP μ (c0 + σ) := by
      intro σ hσ
      have hzy : c0 + σ ≤ y := by rw [← hcD]; exact (add_le_add_iff_left c0).2 hσ
      refine lt_of_le_of_ne (rkP_le_self μ _) fun hz => ?_
      have hzμ : rkDat μ ≤ c0 + σ := (rkDat_lt_rkP μ _).le.trans_eq hz.symm
      rcases (hτμ.trans hzμ).lt_or_eq with hτz | hτz
      · have := hnofix _ (by rw [hpτ]; exact hτz) (hzy.trans_lt hyw)
        rw [← hz] at this
        exact lt_irrefl _ this
      · have h1 : rkP μ τ = τ := by rw [hτz]; exact hz.symm
        exact rkP_ne_self_of_dat hτμ h1
    have hT : D ∈ Tset τ := vz_T_down hτE hτ1 hwT hw1 hDw.le
    refine ⟨D, hT, hDw.trans hw1, hDw, ?_⟩
    rw [rkK_enum0_of hτ hτ1 hμT hμΩ hτμ hREP hc0 hmin D hT (hDw.trans hw1) hcond, hcD, hy]
  · have hpp : rkP μ p = p := by
      rcases hbase with e | ⟨-, h⟩
      · have hμτ : rkDat μ < τ := not_le.1 fun h' => hcase ⟨e, h'⟩
        rw [e]; exact hτF μ hμΩ hμτ
      · exact h
    have hpy : p < y := (rkP_lt_iff μ).1 (by rw [hpp, hy]; exact hpw)
    set D := y - p with hDdef
    have hpD : p + D = y := Ordinal.add_sub_cancel_of_le hpy.le
    have hD0 : D ≠ 0 := by
      rintro h0; rw [h0, add_zero] at hpD; exact absurd hpD hpy.ne
    set δ := D - 1 with hδdef
    have hδ : 1 + δ = D := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hD0)
    have hpδy : p + 1 + δ = y := by rw [add_assoc, hδ, hpD]
    have hδle : δ ≤ p + δ := le_add_self
    have hpδw : p + δ < w := by
      refine lt_of_le_of_lt ?_ hyw
      rw [← hpδy, add_assoc]; exact (add_le_add_iff_left p).2 le_add_self
    have hcond : ∀ σ, σ ≤ δ → p + 1 + σ < rkP μ (p + 1 + σ) := by
      intro σ hσ
      refine hnofix _ (lt_of_lt_of_le (lt_add_one p) le_self_add) (lt_of_le_of_lt ?_ hyw)
      rw [← hpδy]; exact (add_le_add_iff_left _).2 hσ
    rcases hbase with hpτ | ⟨hτp, -⟩
    · -- `p = τ`, `rkDat μ < τ`
      have hμτ : rkDat μ < τ := not_le.1 fun h' => hcase ⟨hpτ, h'⟩
      have hδw : δ < w := hδle.trans_lt hpδw
      have hT : δ ∈ Tset τ := vz_T_down hτE hτ1 hwT hw1 hδw.le
      have hc : ∀ σ, σ ≤ δ → 1 + σ < rkP μ (τ + 1 + σ) := by
        intro σ hσ
        have h := hcond σ hσ
        rw [hpτ] at h
        refine lt_of_le_of_lt ?_ h
        rw [add_assoc]; exact le_add_self
      refine ⟨δ, hT, hδw.trans hw1, hδw, ?_⟩
      rw [rkK_enum_of hτ hτ1 hτF hμΩ hμτ hREP δ hT (hδw.trans hw1) hc, ← hpτ, hpδy, hy]
    · have hT : p + δ ∈ Tset τ := vz_T_down hτE hτ1 hwT hw1 hpδw.le
      refine ⟨p + δ, hT, hpδw.trans hw1, hpδw, ?_⟩
      rw [rkK_enum_fix2_of hτ hτ1 hμT hμΩ hREP hpp hτp δ hT (hpδw.trans hw1) hcond, hpδy, hy]

/-- **REP2(μ) at every level `μ < Ω₁·Ω₁` with `rkDat μ ∈ Tᵗ`.** -/
theorem rkK_rep2 (μ : Ordinal.{0}) : μ < ggE → rkDat μ ∈ Tset τ → RkKREP2 τ μ := by
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμΩ hμT
  exact rkK_rep2_of hτ hτ1 hτF hμT hμΩ fun j hj hjT => IH j hj (hj.trans hμΩ) hjT

/-- **`ϑᵗ(Δ_μ + η)` is a fixed point of every `Φ_j`, `j < μ`, `rkDat j` below it.** -/
theorem rkK_fixv2 {μ : Ordinal.{0}} (hμT : rkDat μ ∈ Tset τ) (hμΩ : μ < ggE) {η : Ordinal.{0}}
    (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    ∀ j < μ, rkDat j < vt τ (Om1 * (Om1 + μ) + η) →
      rkP j (vt τ (Om1 * (Om1 + μ) + η)) = vt τ (Om1 * (Om1 + μ) + η) :=
  rkK_fixv2_of hτ hτ1 hμT hμΩ (fun j hj hjT => rkK_rep2 hτ hτ1 hτF j (hj.trans hμΩ) hjT) hη hηΩ

/-- **`ϑᵗ(Δ_μ + η) = Φ_μ(τ + 1 + η)`** (`rkDat μ < τ`). -/
theorem rkK_enum {μ : Ordinal.{0}} (hμΩ : μ < ggE) (hμτ : rkDat μ < τ) :
    ∀ η, η ∈ Tset τ → η < Om1 → (∀ σ, σ ≤ η → 1 + σ < rkP μ (τ + 1 + σ)) →
      vt τ (Om1 * (Om1 + μ) + η) = rkP μ (τ + 1 + η) :=
  rkK_enum_of hτ hτ1 hτF hμΩ hμτ fun j hj hjT => rkK_rep2 hτ hτ1 hτF j (hj.trans hμΩ) hjT

/-- **`ϑᵗ(Δ_μ + η) = Φ_μ(c₀ + η)`** at a level `rkDat μ ≥ τ`. -/
theorem rkK_enum0 {μ c0 : Ordinal.{0}} (hμT : rkDat μ ∈ Tset τ) (hμΩ : μ < ggE) (hτμ : τ ≤ rkDat μ)
    (hc0 : rkDat μ < rkP μ c0) (hmin : ∀ c < c0, rkP μ c ≤ rkDat μ) :
    ∀ η, η ∈ Tset τ → η < Om1 → (∀ σ, σ ≤ η → c0 + σ < rkP μ (c0 + σ)) →
      vt τ (Om1 * (Om1 + μ) + η) = rkP μ (c0 + η) :=
  rkK_enum0_of hτ hτ1 hμT hμΩ hτμ (fun j hj hjT => rkK_rep2 hτ hτ1 hτF j (hj.trans hμΩ) hjT) hc0 hmin

/-- **`ϑᵗ(Δ_μ + (p + δ)) = Φ_μ(p + 1 + δ)`** for a fixed point `p > τ` of `Φ_μ`. -/
theorem rkK_enum_fix2 {μ : Ordinal.{0}} (hμT : rkDat μ ∈ Tset τ) (hμΩ : μ < ggE) {p : Ordinal.{0}}
    (hp : rkP μ p = p) (hτp : τ < p) :
    ∀ δ, p + δ ∈ Tset τ → p + δ < Om1 → (∀ σ, σ ≤ δ → p + 1 + σ < rkP μ (p + 1 + σ)) →
      vt τ (Om1 * (Om1 + μ) + (p + δ)) = rkP μ (p + 1 + δ) :=
  rkK_enum_fix2_of hτ hτ1 hμT hμΩ (fun j hj hjT => rkK_rep2 hτ hτ1 hτF j (hj.trans hμΩ) hjT) hp hτp

omit hτF in
/-- **`ζᵗ = 0` at a fixed point `p > τ` of `Φ_μ`.** -/
theorem rkK_zeta_fix2 {μ : Ordinal.{0}} (hμT : rkDat μ ∈ Tset τ) (hμΩ : μ < ggE) {p : Ordinal.{0}}
    (hp : rkP μ p = p) (hτp : τ < p) (hpT : p ∈ Tset τ) (hp1 : p < Om1) :
    lqZeta τ (Om1 * (Om1 + μ)) p = 0 := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have hLE := rkK_le hτ hτ1 μ hμΩ hμT
  unfold lqZeta
  rw [if_neg]
  rintro ⟨σ, hσ, hlt⟩
  exact absurd hlt (not_lt.2 (rkK_below_fix_of hLE hp hτp hp1 (vz_T_down hτE hτ1 hpT hp1 hσ.le) hσ).le)

/-- **`ζᵗ = logend(p + δ)`** for `δ ≠ 0` under the condition of `rkK_enum_fix2`. -/
theorem rkK_zeta_fix_add2 {μ : Ordinal.{0}} (hμT : rkDat μ ∈ Tset τ) (hμΩ : μ < ggE)
    {p δ : Ordinal.{0}} (hp : rkP μ p = p) (hτp : τ < p) (hδ0 : δ ≠ 0) (hT : p + δ ∈ Tset τ) (h1 : p + δ < Om1)
    (hcond : ∀ σ, σ ≤ δ → p + 1 + σ < rkP μ (p + 1 + σ)) :
    lqZeta τ (Om1 * (Om1 + μ)) (p + δ) = lg (p + δ) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have hen : ∀ δ', δ' ≤ δ →
      vt τ (Om1 * (Om1 + μ) + (p + δ')) = rkP μ (p + 1 + δ') := fun δ' hδ' =>
    rkK_enum_fix2 hτ hτ1 hτF hμT hμΩ hp hτp δ' (vz_T_down hτE hτ1 hT h1 ((add_le_add_iff_left p).2 hδ'))
      (((add_le_add_iff_left p).2 hδ').trans_lt h1) fun σ hσ => hcond σ (hσ.trans hδ')
  unfold lqZeta
  rw [if_pos]
  rcases zero_or_succ_or_isSuccLimit δ with h0 | ⟨δ0, rfl⟩ | hlim
  · exact absurd h0 hδ0
  · refine ⟨p + δ0, (add_lt_add_iff_left p).2 (Order.lt_succ δ0), ?_⟩
    rw [hen δ0 (Order.le_succ δ0), Order.succ_eq_add_one, ← add_assoc]
    have hle : p + δ0 + 1 ≤ p + 1 + δ0 + 1 := by
      refine add_le_add ?_ le_rfl
      rw [add_assoc]; exact (add_le_add_iff_left p).2 le_add_self
    exact hle.trans_lt ((rkP_SC μ _).add_one_lt (hcond δ0 (Order.le_succ δ0)))
  · have hlim' : IsSuccLimit (p + 1 + δ) := isSuccLimit_add _ hlim
    have hpδ : p + δ < rkP μ (p + 1 + δ) := by
      have : p + δ ≤ p + 1 + δ := by rw [add_assoc]; exact (add_le_add_iff_left p).2 le_add_self
      exact this.trans_lt (hcond δ le_rfl)
    obtain ⟨x, hx, hpx⟩ := ((rkP_normal μ).lt_iff_exists_lt hlim').1 hpδ
    rcases lt_or_ge x (p + 1) with hxp | hxp
    · exfalso
      have : rkP μ x ≤ p := by
        conv_rhs => rw [← hp]
        exact (rkP_le_iff μ).2 (Order.lt_add_one_iff.1 hxp)
      exact absurd (hpx.trans_le this) (not_lt.2 le_self_add)
    · have hσe : p + 1 + (x - (p + 1)) = x := Ordinal.add_sub_cancel_of_le hxp
      have hσ : x - (p + 1) < δ := by rw [← hσe] at hx; exact (add_lt_add_iff_left _).1 hx
      refine ⟨p + (x - (p + 1)), (add_lt_add_iff_left p).2 hσ, ?_⟩
      rw [hen _ hσ.le, hσe]
      exact hpx

/-- **`ζᵗ = logend(η)`** at `ϑᵗ(Δ_μ + η)` under the condition of `rkK_enum` (`rkDat μ < τ`). -/
theorem rkK_zeta {μ : Ordinal.{0}} (hμΩ : μ < ggE) (hμτ : rkDat μ < τ) {η : Ordinal.{0}}
    (hη : η ∈ Tset τ) (hηΩ : η < Om1) (hcond : ∀ σ, σ ≤ η → 1 + σ < rkP μ (τ + 1 + σ)) :
    lqZeta τ (Om1 * (Om1 + μ)) η = lg η := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have hen : ∀ σ, σ ≤ η → vt τ (Om1 * (Om1 + μ) + σ) = rkP μ (τ + 1 + σ) := fun σ hσ =>
    rkK_enum hτ hτ1 hτF hμΩ hμτ σ (vz_T_down hτE hτ1 hη hηΩ hσ) (hσ.trans_lt hηΩ)
      fun σ' hσ' => hcond σ' (hσ'.trans hσ)
  unfold lqZeta
  rcases eq_or_ne η 0 with rfl | hη0
  · rw [if_neg (fun ⟨σ, hσ, _⟩ => absurd hσ (not_lt.2 zero_le))]
    unfold lg; simp
  rw [if_pos]
  rcases zero_or_succ_or_isSuccLimit η with h0 | ⟨σ, rfl⟩ | hlim
  · exact absurd h0 hη0
  · refine ⟨σ, Order.lt_succ σ, ?_⟩
    rw [hen σ (Order.le_succ σ), Order.succ_eq_add_one]
    exact (rkP_SC μ _).add_one_lt ((le_add_self).trans_lt (hcond σ (Order.le_succ σ)))
  · have hηg : η < rkP μ (τ + 1 + η) := (le_add_self).trans_lt (hcond η le_rfl)
    obtain ⟨x, hx, hηx⟩ := ((rkP_normal μ).lt_iff_exists_lt (isSuccLimit_add _ hlim)).1 hηg
    rcases lt_or_ge x (τ + 1) with hxc | hxc
    · refine ⟨0, hlim.bot_lt, ?_⟩
      rw [hen 0 zero_le, add_zero]
      exact hηx.trans ((rkP_lt_iff μ).2 hxc)
    · have hσe : τ + 1 + (x - (τ + 1)) = x := Ordinal.add_sub_cancel_of_le hxc
      have hσ : x - (τ + 1) < η := by rw [← hσe] at hx; exact (add_lt_add_iff_left _).1 hx
      refine ⟨x - (τ + 1), hσ, ?_⟩
      rw [hen _ hσ.le, hσe]
      exact hηx

/-- **`ζᵗ = logend(η)`** at `ϑᵗ(Δ_μ + η)` under the condition of `rkK_enum0` (`rkDat μ ≥ τ`). -/
theorem rkK_zeta0 {μ c0 : Ordinal.{0}} (hμT : rkDat μ ∈ Tset τ) (hμΩ : μ < ggE) (hτμ : τ ≤ rkDat μ)
    (hc0 : rkDat μ < rkP μ c0) (hmin : ∀ c < c0, rkP μ c ≤ rkDat μ) {η : Ordinal.{0}} (hη : η ∈ Tset τ)
    (hηΩ : η < Om1) (hcond : ∀ σ, σ ≤ η → c0 + σ < rkP μ (c0 + σ)) :
    lqZeta τ (Om1 * (Om1 + μ)) η = lg η := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have hen : ∀ σ, σ ≤ η → vt τ (Om1 * (Om1 + μ) + σ) = rkP μ (c0 + σ) := fun σ hσ =>
    rkK_enum0 hτ hτ1 hτF hμT hμΩ hτμ hc0 hmin σ (vz_T_down hτE hτ1 hη hηΩ hσ) (hσ.trans_lt hηΩ)
      fun σ' hσ' => hcond σ' (hσ'.trans hσ)
  unfold lqZeta
  rcases eq_or_ne η 0 with rfl | hη0
  · rw [if_neg (fun ⟨σ, hσ, _⟩ => absurd hσ (not_lt.2 zero_le))]
    unfold lg; simp
  rw [if_pos]
  rcases zero_or_succ_or_isSuccLimit η with h0 | ⟨σ, rfl⟩ | hlim
  · exact absurd h0 hη0
  · refine ⟨σ, Order.lt_succ σ, ?_⟩
    rw [hen σ (Order.le_succ σ), Order.succ_eq_add_one]
    exact (rkP_SC μ _).add_one_lt ((le_add_self).trans_lt (hcond σ (Order.le_succ σ)))
  · have hηg : η < rkP μ (c0 + η) := (le_add_self).trans_lt (hcond η le_rfl)
    obtain ⟨x, hx, hηx⟩ := ((rkP_normal μ).lt_iff_exists_lt (isSuccLimit_add _ hlim)).1 hηg
    rcases lt_or_ge x c0 with hxc | hxc
    · refine ⟨0, hlim.bot_lt, ?_⟩
      rw [hen 0 zero_le, add_zero]
      exact hηx.trans ((rkP_lt_iff μ).2 hxc)
    · have hσe : c0 + (x - c0) = x := Ordinal.add_sub_cancel_of_le hxc
      have hσ : x - c0 < η := by rw [← hσe] at hx; exact (add_lt_add_iff_left _).1 hx
      refine ⟨x - c0, hσ, ?_⟩
      rw [hen _ hσ.le, hσe]
      exact hηx

end Fix

end Googology.Trans.PoR.InaccPsi.R2.Rk
