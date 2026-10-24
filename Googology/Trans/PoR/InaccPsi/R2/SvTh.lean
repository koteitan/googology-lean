import Googology.Trans.PoR.InaccPsi.R2.SvCit

/-!
# `ϑᵗ(Δ_μ + η)` at every level `E₁ ≤ μ < M` over a level-closed base, under `SvCit M`

`Δ_μ = Ω₁·(Ω₁ + μ)`, `Φ_μ = Ss.ssP μ` (data `ssDatL μ`), `E₁ = ε_{Ω₁+1}`, `τ` a strongly critical base `< Ω₁` that is a
fixed point of every `Φ_j`, `j < E₁`, `ssDatL j < τ` (level-closed: `hτF`).  `R2.RkTh` proves the facts below at the
levels `< E₁` for a base fixed by the level; `R2.SsTh` at the level `E₁` for a base that is a value of `Φ_{E₁}`.  Here
**the base need not be a value of `Φ_μ`**: the index of the first value is `c₀ :=` the least `c` with `Φ_μ(c) >
max(τ, ssDatL μ)`, and the generic level facts are those of the package `SvCit M` (`R2.SvCit`):

* `svK_facts`, `svK_lt`, `svK_lt_lower` (**the lower levels `j < μ` stay below**), `svK_SC` (**`ϑᵗ(Δ_μ + η)` is
  strongly critical**), `svK_inj`;
* `SvLE τ μ` (`ϑᵗ(Δ_μ + η) ≤ Φ_μ(τ + η + 1)`), `SvREP τ μ` (**every value `w ∈ Tᵗ ∩ (τ, Ω₁)` of `Φ_μ` above the data
  that is not a fixed point of `Φ_μ` is `ϑᵗ(Δ_μ + σ)`, `σ < w`**), the lower levels `sv_LE_low`, `sv_REP_low`
  (`R2.RkTh`), `svK_min`, `svK_le`, `svK_rep2` (by induction on `μ ∈ [E₁, M)`);
* `svK_fixv2` (**`ϑᵗ(Δ_μ + η)` is a value of `Φ_μ`**), `svK_enum0` (**`ϑᵗ(Δ_μ + η) = Φ_μ(c₀ + η)`** for the least
  index `c₀` with `Φ_μ(c₀) > max(τ, ssDatL μ)`, when `σ < Φ_μ(c₀ + σ)` for `σ ≤ η`), `svK_enum_fix2`
  (**`ϑᵗ(Δ_μ + (p + δ)) = Φ_μ(p + 1 + δ)`** for a fixed point `p > τ` of `Φ_μ`).

No new axiom.  New definitions: the statement names `SvLE`, `SvREP`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Sv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rb Googology.Trans.PoR.InaccPsi.R2.Rd
  Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj
  Googology.Trans.PoR.InaccPsi.R2.Rk Googology.Trans.PoR.InaccPsi.R2.Ss

/-- **LE(μ)**: `ϑᵗ(Δ_μ + η) ≤ Φ_μ(τ + η + 1)` for every `η ∈ Tᵗ ∩ Ω₁`. -/
def SvLE (τ μ : Ordinal.{0}) : Prop :=
  ∀ η, η ∈ Tset τ → η < Om1 → vt τ (Om1 * (Om1 + μ) + η) ≤ ssP μ (τ + η + 1)

/-- **REP(μ)**: every value `w ∈ Tᵗ ∩ (τ, Ω₁)` of `Φ_μ` with `ssDatL μ < w` that is not a fixed point of `Φ_μ` is
`ϑᵗ(Δ_μ + σ)` with `σ ∈ Tᵗ`, `σ < w`. -/
def SvREP (τ μ : Ordinal.{0}) : Prop :=
  ∀ w, SC w → (∀ j < μ, ssDatL j < w → ssP j w = w) → τ < w → ssDatL μ < w → w ∈ Tset τ → w < Om1 →
    ssP μ w ≠ w → ∃ σ, σ ∈ Tset τ ∧ σ < Om1 ∧ σ < w ∧ vt τ (Om1 * (Om1 + μ) + σ) = w

/-! ## The levels below `E₁` (from `R2.RkTh`) -/

section Low

variable {τ : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1)
include hτ hτ1

theorem sv_LE_low {j : Ordinal.{0}} (hj : j < ggE) (hjT : ssDatL j ∈ Tset τ) : SvLE τ j := by
  intro η hη hηΩ
  rw [ssP_eq_rkP j hj.le]
  exact rkK_le hτ hτ1 j hj (by rw [← ssDatL_eq hj]; exact hjT) η hη hηΩ

theorem sv_facts_low {j σ : Ordinal.{0}} (hj : j < ggE) (hjT : ssDatL j ∈ Tset τ) (hσ : σ ∈ Tset τ)
    (hσΩ : σ < Om1) :
    vt τ (Om1 * (Om1 + j) + σ) ∈ Tset τ ∧ τ < vt τ (Om1 * (Om1 + j) + σ) ∧
      vt τ (Om1 * (Om1 + j) + σ) < Om1 ∧
      ssDatL j < vt τ (Om1 * (Om1 + j) + σ) ∧ σ < vt τ (Om1 * (Om1 + j) + σ) := by
  obtain ⟨-, -, a, b, c, -, d, e⟩ := rkK_facts hτ hτ1 (by rw [← ssDatL_eq hj]; exact hjT) hj hσ hσΩ
  exact ⟨a, b, c, by rw [ssDatL_eq hj]; exact d, e⟩

theorem sv_REP_low (hτF : ∀ μ, μ < ggE → rkDat μ < τ → rkP μ τ = τ) {j : Ordinal.{0}} (hj : j < ggE)
    (hjT : ssDatL j ∈ Tset τ) : SvREP τ j := by
  intro w hw hwF hτw hjw hwT hw1 hnf
  have hR := rkK_rep2 hτ hτ1 hτF j hj (by rw [← ssDatL_eq hj]; exact hjT)
  have hwF' : ∀ i < j, rkDat i < w → rkP i w = w := fun i hi hd => by
    have hiE : i < ggE := hi.trans hj
    rw [← ssP_eq_rkP i hiE.le]; exact hwF i hi (by rw [ssDatL_eq hiE]; exact hd)
  rw [ssP_eq_rkP j hj.le] at hnf
  exact hR w hw hwF' hτw (by rw [← ssDatL_eq hj]; exact hjw) hwT hw1 hnf

end Low

/-- The least index of a value of `Φ_μ` above `m`. -/
theorem sv_first_idx (μ m : Ordinal.{0}) :
    ∃ c0, m < ssP μ c0 ∧ ∀ c < c0, ssP μ c ≤ m := by
  have hne : {c | m < ssP μ c}.Nonempty := ⟨m + 1, (lt_add_one m).trans_le (ssP_le_self μ _)⟩
  refine ⟨sInf {c | m < ssP μ c}, csInf_mem hne, fun c hc => not_lt.1 fun h => ?_⟩
  exact absurd (csInf_le' (show c ∈ {c | m < ssP μ c} from h)) (not_le.2 hc)

/-! ## The levels `E₁ ≤ μ < M` -/

section Base

variable {M : Ordinal.{0}} (hC : SvCit M) (hMG : M ≤ ggGam) {τ : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1)
include hC hMG hτ hτ1

/-- **The facts on `ϑᵗ(Δ_μ + η)`.** -/
theorem svK_facts {μ : Ordinal.{0}} (hEμ : ggE ≤ μ) (hμM : μ < M) (hμT : ssDatL μ ∈ Tset τ) {η : Ordinal.{0}}
    (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    Om1 * (Om1 + μ) + η ∈ Tset τ ∧ Om1 * (Om1 + μ) + η < OmTwo ∧
    vt τ (Om1 * (Om1 + μ) + η) ∈ Tset τ ∧ τ < vt τ (Om1 * (Om1 + μ) + η) ∧
    vt τ (Om1 * (Om1 + μ) + η) < Om1 ∧ InE (vt τ (Om1 * (Om1 + μ) + η)) ∧
    ssDatL μ < vt τ (Om1 * (Om1 + μ) + η) ∧ η < vt τ (Om1 * (Om1 + μ) + η) := by
  have hτE : InE τ := gg_SC_eps hτ
  have hargT := svc_mem hC hτE hτ1 hEμ hμM hμT hη hηΩ
  have harg2 : Om1 * (Om1 + μ) + η < OmTwo := (sv_arg_lt (hμM.trans_le hMG) hηΩ).trans_le sv_G_le_Om2
  obtain ⟨hvT, -, hv1, -, -⟩ := vt_memTwo hτE hτ1 hargT harg2
  have hO : Om1 ≤ Om1 * (Om1 + μ) + η :=
    (le_mul_left Om1 (lt_of_lt_of_le rj_Om1_pos le_self_add)).trans le_self_add
  have hE := (vt_E_iff hτE hτ1 hargT harg2).2 hO
  obtain ⟨h1, h2⟩ := svc_level hC hτE hτ1 hEμ hμM hμT hη hηΩ
  exact ⟨hargT, harg2, hvT, hE.1, hv1, hE.2, h1, h2⟩

/-- **`η ↦ ϑᵗ(Δ_μ + η)` is strictly increasing.** -/
theorem svK_lt {μ : Ordinal.{0}} (hEμ : ggE ≤ μ) (hμM : μ < M) (hμT : ssDatL μ ∈ Tset τ) {σ η : Ordinal.{0}}
    (hσ : σ ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1) (h : σ < η) :
    vt τ (Om1 * (Om1 + μ) + σ) < vt τ (Om1 * (Om1 + μ) + η) := by
  have hτE : InE τ := gg_SC_eps hτ
  obtain ⟨-, -, -, -, -, -, hdv, hηv⟩ := svK_facts hC hMG hτ hτ1 hEμ hμM hμT hη hηΩ
  exact svc_vt_lt hC hτE hτ1 hEμ hμM le_rfl hμT hσ (h.trans hηΩ) hμT hη hηΩ
    ((add_lt_add_iff_left _).2 h) hdv (h.trans hηv)

omit hMG in
/-- **A lower level stays below**: `ϑᵗ(Δ_j + σ) < ϑᵗ(Δ_μ + η)` for `j < μ` with `ssDatL j` and `σ` below the right
side. -/
theorem svK_lt_lower {j μ σ η : Ordinal.{0}} (hEμ : ggE ≤ μ) (hμM : μ < M) (hμT : ssDatL μ ∈ Tset τ)
    (hjμ : j < μ) (hjT : ssDatL j ∈ Tset τ) (hσ : σ ∈ Tset τ) (hσΩ : σ < Om1)
    (hη : η ∈ Tset τ) (hηΩ : η < Om1) (hσv : σ < vt τ (Om1 * (Om1 + μ) + η))
    (hjv : ssDatL j < vt τ (Om1 * (Om1 + μ) + η)) :
    vt τ (Om1 * (Om1 + j) + σ) < vt τ (Om1 * (Om1 + μ) + η) := by
  have hτE : InE τ := gg_SC_eps hτ
  have hM' : Om1 + j ≤ Om1 + μ := (add_le_add_iff_left _).2 hjμ.le
  have harg : Om1 * (Om1 + j) + σ < Om1 * (Om1 + μ) + η := by
    calc Om1 * (Om1 + j) + σ < Om1 * (Om1 + j) + Om1 := (add_lt_add_iff_left _).2 hσΩ
      _ = Om1 * (Om1 + j + 1) := by rw [mul_add_one]
      _ ≤ Om1 * (Om1 + μ) := by
          refine mul_le_mul_right ?_ _
          rw [add_assoc]; exact (add_le_add_iff_left _).2 (Order.add_one_le_of_lt hjμ)
      _ ≤ _ := le_self_add
  exact svc_vt_lt hC hτE hτ1 hEμ hμM hM' hjT hσ hσΩ hμT hη hηΩ harg hjv hσv

/-- **`ϑᵗ(Δ_μ + η)` is strongly critical** (the argument of `Ss.ssK_SC`). -/
theorem svK_SC {μ : Ordinal.{0}} (hEμ : ggE ≤ μ) (hμM : μ < M) (hμT : ssDatL μ ∈ Tset τ) {η : Ordinal.{0}}
    (hη : η ∈ Tset τ) (hηΩ : η < Om1) : SC (vt τ (Om1 * (Om1 + μ) + η)) := by
  have hτE : InE τ := gg_SC_eps hτ
  obtain ⟨-, -, hvT, hτv, hv1, hvE, -, -⟩ := svK_facts hC hMG hτ hτ1 hEμ hμM hμT hη hηΩ
  set v := vt τ (Om1 * (Om1 + μ) + η) with hv
  have hvE' : ω ^ v = v := hvE
  have hvl : IsSuccLimit v := ev_isSuccLimit_of_inE hvE
  have hTv : ∀ z, z < v → z ∈ Tset τ := fun z hz => vz_T_down hτE hτ1 hvT hv1 hz.le
  have key : ∀ a b, 1 ≤ a → a < v → (τ < a → ¬ SC a) → b < v → veblen a b < v := by
    intro a b ha1 hav haSC hbv
    by_cases hfix : veblen a b = b
    · rw [hfix]; exact hbv
    by_cases hle : veblen a b ≤ τ
    · exact hle.trans_lt hτv
    push Not at hle
    have hbP : ¬ Lu.LuP (a + 1) b := fun h => hfix (Lu.luP_succ.1 h)
    have hind : lvInd a τ b ≤ b := Cd.cdOtp_le_self _ b
    have hindv : lvInd a τ b < v := hind.trans_lt hbv
    have haT := hTv a hav
    have haΩ : a < Om1 := hav.trans hv1
    rw [lvPhLev hτ hτ1 ha1 haT haΩ (Mx.mxLev_u ha1 haSC) b hle hbP (hTv _ hindv) (hindv.trans hv1)]
    have harg : Om1 * a + lvInd a τ b < Om1 * (Om1 + μ) + η := by
      calc Om1 * a + lvInd a τ b < Om1 * a + Om1 := (add_lt_add_iff_left _).2 (hindv.trans hv1)
        _ = Om1 * (a + 1) := by rw [mul_add_one]
        _ ≤ Om1 * Om1 := mul_le_mul_right (Order.add_one_le_of_lt haΩ) _
        _ ≤ Om1 * (Om1 + μ) := mul_le_mul_right le_self_add _
        _ ≤ _ := le_self_add
    have hM' : a ≤ Om1 + μ := haΩ.le.trans le_self_add
    exact svc_vt_lt hC hτE hτ1 hEμ hμM hM' (by rw [ssDat_small haΩ]; exact haT) (hTv _ hindv)
      (hindv.trans hv1) hμT hη hηΩ harg (by rw [ssDat_small haΩ]; exact hav) hindv
  refine ⟨hvE.pos, fun a ha b hb => ?_⟩
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [veblen_zero_apply, ← hvE']; exact (opow_lt_opow_iff_right one_lt_omega0).2 hb
  have ha1 : 1 ≤ a := one_le_iff_ne_zero.2 ha0
  by_cases hs : τ < a ∧ SC a
  · have ha1v : a + 1 < v := hvl.add_one_lt ha
    have hnsc : τ < a + 1 → ¬ SC (a + 1) := fun _ h => SC.ne_add_one h a rfl
    have h2 := key (a + 1) b (le_add_self) ha1v hnsc hb
    have h3 : veblen a b ≤ veblen (a + 1) b := by
      calc veblen a b ≤ veblen a (veblen (a + 1) b) :=
            veblen_le_veblen_iff_right.2 (right_le_veblen _ _)
        _ = veblen (a + 1) b := veblen_veblen_of_lt (lt_add_one a) b
    exact h3.trans_lt h2
  · push Not at hs
    exact key a b ha1 ha hs hb

/-- `η ↦ ϑᵗ(Δ_μ + η)` is injective on `Tᵗ ∩ Ω₁`. -/
theorem svK_inj {μ a b : Ordinal.{0}} (hEμ : ggE ≤ μ) (hμM : μ < M) (hμT : ssDatL μ ∈ Tset τ)
    (ha : a ∈ Tset τ) (ha1 : a < Om1) (hb : b ∈ Tset τ) (hb1 : b < Om1)
    (h : vt τ (Om1 * (Om1 + μ) + a) = vt τ (Om1 * (Om1 + μ) + b)) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (svK_lt hC hMG hτ hτ1 hEμ hμM hμT ha hb hb1 hab).ne
  · exact hab
  · exact absurd h (svK_lt hC hMG hτ hτ1 hEμ hμM hμT hb ha ha1 hab).ne'

/-- The facts at a lower level `j < M` (below `E₁` from `R2.RkTh`). -/
theorem sv_lowfacts {j σ : Ordinal.{0}} (hjM : j < M) (hjT : ssDatL j ∈ Tset τ) (hσ : σ ∈ Tset τ)
    (hσΩ : σ < Om1) :
    ssDatL j < vt τ (Om1 * (Om1 + j) + σ) ∧ σ < vt τ (Om1 * (Om1 + j) + σ) := by
  rcases lt_or_ge j ggE with hj | hj
  · obtain ⟨-, -, -, a, b⟩ := sv_facts_low hτ hτ1 hj hjT hσ hσΩ
    exact ⟨a, b⟩
  · obtain ⟨-, -, -, -, -, -, a, b⟩ := svK_facts hC hMG hτ hτ1 hj hjM hjT hσ hσΩ
    exact ⟨a, b⟩

omit hMG in
/-- The data of a lower level `j < M` from its argument (below `E₁` from `R2.CitedRk`). -/
theorem sv_lowdat {j σ : Ordinal.{0}} (hjM : j < M) (hσΩ : σ < Om1)
    (h : Om1 * (Om1 + j) + σ ∈ Tset τ) : ssDatL j ∈ Tset τ := by
  have hτE : InE τ := gg_SC_eps hτ
  rcases lt_or_ge j ggE with hj | hj
  · rw [ssDatL_eq hj]
    exact rkArg_dat hτE hτ1 le_self_add (rk_Om1_add_lt hj) hσΩ h
  · exact svc_dat hC hτE hτ1 hj hjM hσΩ h

/-- **Minimality at the level `μ`**: `ϑᵗ(Δ_μ + η) ≤ s` for every strongly critical `s > τ, η, ssDatL μ` that is a fixed
point of every `Φ_j`, `j < μ`, `ssDatL j < s`, above all `ϑᵗ(Δ_μ + σ)`, `σ < η`. -/
theorem svK_min {μ : Ordinal.{0}} (hEμ : ggE ≤ μ) (hμM : μ < M) (hμT : ssDatL μ ∈ Tset τ)
    (hLE : ∀ j, ggE ≤ j → j < μ → ssDatL j ∈ Tset τ → SvLE τ j)
    {η s : Ordinal.{0}} (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (hs : SC s) (hsF : ∀ j < μ, ssDatL j < s → ssP j s = s) (hτs : τ < s) (hηs : η < s) (hμs : ssDatL μ < s)
    (hprev : ∀ σ, σ < η → vt τ (Om1 * (Om1 + μ) + σ) < s) :
    vt τ (Om1 * (Om1 + μ) + η) ≤ s := by
  have hτE : InE τ := gg_SC_eps hτ
  obtain ⟨-, -, hvT, -, hv1, -, -, -⟩ := svK_facts hC hMG hτ hτ1 hEμ hμM hμT hη hηΩ
  by_contra hlt
  push Not at hlt
  obtain ⟨m, -, -, -, hTm, hm1, -⟩ := vz_next hτE hτ1
  have hvm : vt τ (Om1 * (Om1 + μ) + η) < m := (hTm _ hv1).1 hvT
  have hs1 : s < Om1 := hlt.trans hv1
  have hsT : s ∈ Tset τ := (hTm s hs1).2 (hlt.trans hvm)
  have hsE : InE s := gg_SC_eps hs
  have hsP : Indec s := inE_indec hsE
  obtain ⟨ξ, hξT, hξ2, hξs⟩ := vt_rep hτE hτ1 hsT hτs.le hs1 hsP
  have hlt' : vt τ ξ < vt τ (Om1 * (Om1 + μ) + η) := by rw [hξs]; exact hlt
  have hξlt : ξ < Om1 * (Om1 + μ) + η :=
    svc_lt_of hC hτE hτ1 hEμ hμM hξT hξ2 hμT hη hηΩ (by rw [hξs]; exact hμs) (by rw [hξs]; exact hηs) hlt'
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
      have hjM : j < M := hjk.trans hμM
      have hσT : σ ∈ Tset τ := vzRem_T hτE hτ1 hξT hξ2 he (dvd_mul_right _ _) hσΩ
      have hjT : ssDatL j ∈ Tset τ := sv_lowdat hC hτ hτ1 hjM hσΩ (by rw [← he]; exact hξT)
      have hle : vt τ (Om1 * (Om1 + j) + σ) ≤ ssP j (τ + σ + 1) := by
        rcases lt_or_ge j ggE with hj | hj
        · exact sv_LE_low hτ hτ1 hj hjT σ hσT hσΩ
        · exact hLE j hj hjk hjT σ hσT hσΩ
      rw [← he, hξs] at hle
      obtain ⟨hjv, hσv⟩ := sv_lowfacts hC hMG hτ hτ1 hjM hjT hσT hσΩ
      rw [← he, hξs] at hσv hjv
      have h3 : τ + σ + 1 < s := hs.add_one_lt ((lq_SC_indec hs).add_lt hτs hσv)
      have h4 : ssP j (τ + σ + 1) < s := by
        conv_rhs => rw [← hsF j hjk hjv]
        exact (ssP_lt_iff j).2 h3
      exact absurd hle (not_le.2 h4)
    · have hσe : Om1 * (Om1 + μ) + (ξ - Om1 * (Om1 + μ)) = ξ := Ordinal.add_sub_cancel_of_le hξ'
      have hσ : ξ - Om1 * (Om1 + μ) < η := by
        rw [← hσe] at hξlt; exact (add_lt_add_iff_left _).1 hξlt
      have h := hprev _ hσ
      rw [hσe, hξs] at h
      exact lt_irrefl _ h

/-- **LE(μ)** from LE at the levels in `[E₁, μ)` whose data lie in `Tᵗ`. -/
theorem svK_le_of {μ : Ordinal.{0}} (hEμ : ggE ≤ μ) (hμM : μ < M) (hμT : ssDatL μ ∈ Tset τ)
    (hLE : ∀ j, ggE ≤ j → j < μ → ssDatL j ∈ Tset τ → SvLE τ j) : SvLE τ μ := by
  have hτE : InE τ := gg_SC_eps hτ
  intro η
  induction η using WellFoundedLT.induction with
  | ind η IH =>
  intro hη hηΩ
  refine svK_min hC hMG hτ hτ1 hEμ hμM hμT hLE hη hηΩ (ssP_SC μ _)
    (fun j hj hd => ssP_fix_lower hj ⟨_, rfl⟩ hd) ?_ ?_ (ssDatL_lt_ssP μ _) fun σ hσ => ?_
  · exact (lt_of_le_of_lt le_self_add (lt_add_one _)).trans_le (ssP_le_self μ _)
  · exact lt_of_le_of_lt (le_add_self : η ≤ τ + η) ((lt_add_one (τ + η)).trans_le (ssP_le_self μ _))
  · have hσT : σ ∈ Tset τ := vz_T_down hτE hτ1 hη hηΩ hσ.le
    refine (IH σ hσ hσT (hσ.trans hηΩ)).trans_lt ((ssP_lt_iff μ).2 ?_)
    exact (Order.add_one_le_of_lt ((add_lt_add_iff_left τ).2 hσ)).trans_lt (lt_add_one _)

/-- **LE(μ) at every level `E₁ ≤ μ < M` with `ssDatL μ ∈ Tᵗ`.** -/
theorem svK_le (μ : Ordinal.{0}) : ggE ≤ μ → μ < M → ssDatL μ ∈ Tset τ → SvLE τ μ := by
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hEμ hμM hμT
  exact svK_le_of hC hMG hτ hτ1 hEμ hμM hμT fun j hj hjμ hjT => IH j hjμ hj (hjμ.trans hμM) hjT

omit hC hMG hτ hτ1 in
/-- `ϑᵗ(Δ_μ + σ) < p` for `σ < p` and every fixed point `p > τ` of `Φ_μ`, given LE(μ). -/
theorem svK_below_fix {μ : Ordinal.{0}} (hLEk : SvLE τ μ) {p : Ordinal.{0}} (hp : ssP μ p = p)
    (hτp : τ < p) (hp1 : p < Om1) {σ : Ordinal.{0}} (hσT : σ ∈ Tset τ) (hσ : σ < p) :
    vt τ (Om1 * (Om1 + μ) + σ) < p := by
  have hpSC : SC p := hp ▸ ssP_SC μ p
  have h1 : τ + σ + 1 < p := hpSC.add_one_lt ((lq_SC_indec hpSC).add_lt hτp hσ)
  refine (hLEk σ hσT (hσ.trans hp1)).trans_lt ?_
  conv_rhs => rw [← hp]
  exact (ssP_lt_iff μ).2 h1

/-- **`ϑᵗ(Δ_μ + η)` is a fixed point of every `Φ_j`, `j < μ`, `ssDatL j` below it**, given REP at the levels below
`μ` whose data lie in `Tᵗ`. -/
theorem svK_fixv2_of {μ : Ordinal.{0}} (hEμ : ggE ≤ μ) (hμM : μ < M) (hμT : ssDatL μ ∈ Tset τ)
    (hREP : ∀ j < μ, ssDatL j ∈ Tset τ → SvREP τ j) {η : Ordinal.{0}} (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    ∀ j < μ, ssDatL j < vt τ (Om1 * (Om1 + μ) + η) →
      ssP j (vt τ (Om1 * (Om1 + μ) + η)) = vt τ (Om1 * (Om1 + μ) + η) := by
  have hτE : InE τ := gg_SC_eps hτ
  obtain ⟨-, -, hvT, hτv, hv1, -, -, -⟩ := svK_facts hC hMG hτ hτ1 hEμ hμM hμT hη hηΩ
  have hvSC := svK_SC hC hMG hτ hτ1 hEμ hμM hμT hη hηΩ
  intro j
  induction j using WellFoundedLT.induction with
  | ind j IHj =>
  intro hjk hjv
  by_contra hnf
  have hjT : ssDatL j ∈ Tset τ := vz_T_down hτE hτ1 hvT hv1 hjv.le
  obtain ⟨σ, hσT, hσΩ, hσv, he⟩ :=
    hREP j hjk hjT _ hvSC (fun i hi hiv => IHj i hi (hi.trans hjk) hiv) hτv hjv hvT hv1 hnf
  have := svK_lt_lower hC hτ hτ1 hEμ hμM hμT hjk hjT hσT hσΩ hη hηΩ hσv hjv
  rw [he] at this
  exact lt_irrefl _ this

/-- **`ϑᵗ(Δ_μ + η) = Φ_μ(c₀ + η)`** for an index `c₀` with `Φ_μ(c₀)` above `τ` and `ssDatL μ` and every lower index
`c < c₀` with `Φ_μ(c) ≤ τ` or `Φ_μ(c) ≤ ssDatL μ`, when `σ < Φ_μ(c₀+σ)` for every `σ ≤ η`. -/
theorem svK_enum0_of {μ c0 : Ordinal.{0}} (hEμ : ggE ≤ μ) (hμM : μ < M) (hμT : ssDatL μ ∈ Tset τ)
    (hREP : ∀ j < μ, ssDatL j ∈ Tset τ → SvREP τ j) (hc0τ : τ < ssP μ c0) (hc0d : ssDatL μ < ssP μ c0)
    (hmin : ∀ c < c0, ssP μ c ≤ τ ∨ ssP μ c ≤ ssDatL μ) :
    ∀ η, η ∈ Tset τ → η < Om1 → (∀ σ, σ ≤ η → σ < ssP μ (c0 + σ)) →
      vt τ (Om1 * (Om1 + μ) + η) = ssP μ (c0 + η) := by
  have hτE : InE τ := gg_SC_eps hτ
  have hLE : ∀ j, ggE ≤ j → j < μ → ssDatL j ∈ Tset τ → SvLE τ j := fun j hj hjμ hjT =>
    svK_le hC hMG hτ hτ1 j hj (hjμ.trans hμM) hjT
  intro η
  induction η using WellFoundedLT.induction with
  | ind η IH =>
  intro hη hηΩ hcond
  have hIH : ∀ σ, σ < η → vt τ (Om1 * (Om1 + μ) + σ) = ssP μ (c0 + σ) := fun σ hσ =>
    IH σ hσ (vz_T_down hτE hτ1 hη hηΩ hσ.le) (hσ.trans hηΩ) fun σ' hσ' => hcond σ' (hσ'.trans hσ.le)
  have hmono : ssP μ c0 ≤ ssP μ (c0 + η) := (ssP_le_iff μ).2 le_self_add
  apply le_antisymm
  · refine svK_min hC hMG hτ hτ1 hEμ hμM hμT hLE hη hηΩ (ssP_SC μ _)
      (fun j hj hd => ssP_fix_lower hj ⟨_, rfl⟩ hd) (hc0τ.trans_le hmono)
      (hcond η le_rfl) (hc0d.trans_le hmono) fun σ hσ => ?_
    rw [hIH σ hσ]; exact (ssP_lt_iff μ).2 ((add_lt_add_iff_left _).2 hσ)
  · obtain ⟨-, -, -, hτv, -, -, hμv, -⟩ := svK_facts hC hMG hτ hτ1 hEμ hμM hμT hη hηΩ
    obtain ⟨e, he⟩ := ssP_range (svK_SC hC hMG hτ hτ1 hEμ hμM hμT hη hηΩ) hμv
      (svK_fixv2_of hC hMG hτ hτ1 hEμ hμM hμT hREP hη hηΩ)
    rw [← he]
    refine (ssP_le_iff μ).2 (not_lt.1 fun hlt => ?_)
    rcases lt_or_ge e c0 with hec | hce
    · rcases hmin e hec with h | h
      · rw [he] at h; exact absurd hτv (not_lt.2 h)
      · rw [he] at h; exact absurd hμv (not_lt.2 h)
    · have hσe : c0 + (e - c0) = e := Ordinal.add_sub_cancel_of_le hce
      have hσ : e - c0 < η := by rw [← hσe] at hlt; exact (add_lt_add_iff_left _).1 hlt
      have h1 := svK_lt hC hMG hτ hτ1 hEμ hμM hμT (vz_T_down hτE hτ1 hη hηΩ hσ.le) hη hηΩ hσ
      rw [hIH _ hσ, hσe, he] at h1
      exact lt_irrefl _ h1

/-- **`ϑᵗ(Δ_μ + (p + δ)) = Φ_μ(p + 1 + δ)`** for a fixed point `p > τ` of `Φ_μ` when `p + 1 + σ < Φ_μ(p+1+σ)` for
every `σ ≤ δ`. -/
theorem svK_enum_fix2_of {μ : Ordinal.{0}} (hEμ : ggE ≤ μ) (hμM : μ < M) (hμT : ssDatL μ ∈ Tset τ)
    (hREP : ∀ j < μ, ssDatL j ∈ Tset τ → SvREP τ j) {p : Ordinal.{0}} (hp : ssP μ p = p) (hτp : τ < p) :
    ∀ δ, p + δ ∈ Tset τ → p + δ < Om1 → (∀ σ, σ ≤ δ → p + 1 + σ < ssP μ (p + 1 + σ)) →
      vt τ (Om1 * (Om1 + μ) + (p + δ)) = ssP μ (p + 1 + δ) := by
  have hτE : InE τ := gg_SC_eps hτ
  have hLE : ∀ j, ggE ≤ j → j < μ → ssDatL j ∈ Tset τ → SvLE τ j := fun j hj hjμ hjT =>
    svK_le hC hMG hτ hτ1 j hj (hjμ.trans hμM) hjT
  have hLEk := svK_le hC hMG hτ hτ1 μ hEμ hμM hμT
  intro δ
  induction δ using WellFoundedLT.induction with
  | ind δ IH =>
  intro hT h1 hcond
  have hp1 : p < Om1 := (le_self_add : p ≤ p + δ).trans_lt h1
  have hIH : ∀ δ', δ' < δ →
      vt τ (Om1 * (Om1 + μ) + (p + δ')) = ssP μ (p + 1 + δ') := fun δ' hδ' =>
    IH δ' hδ' (vz_T_down hτE hτ1 hT h1 ((add_le_add_iff_left p).2 hδ'.le))
      (((add_lt_add_iff_left p).2 hδ').trans h1) fun σ hσ => hcond σ (hσ.trans hδ'.le)
  have hpg : p < ssP μ (p + 1 + δ) := by
    conv_lhs => rw [← hp]
    exact (ssP_lt_iff μ).2 (lt_of_lt_of_le (lt_add_one p) le_self_add)
  apply le_antisymm
  · refine svK_min hC hMG hτ hτ1 hEμ hμM hμT hLE hT h1 (ssP_SC μ _)
      (fun j hj hd => ssP_fix_lower hj ⟨_, rfl⟩ hd) (hτp.trans hpg) ?_ ((ssDatL_lt_fix hp).trans hpg)
      fun σ hσ => ?_
    · have : p + δ ≤ p + 1 + δ := by
        rw [add_assoc]; exact (add_le_add_iff_left p).2 le_add_self
      exact this.trans_lt (hcond δ le_rfl)
    · rcases lt_or_ge σ p with hσp | hσp
      · exact (svK_below_fix hLEk hp hτp hp1
          (vz_T_down hτE hτ1 hT h1 (hσp.le.trans le_self_add)) hσp).trans hpg
      · have he : p + (σ - p) = σ := Ordinal.add_sub_cancel_of_le hσp
        have hδ' : σ - p < δ := by rw [← he] at hσ; exact (add_lt_add_iff_left p).1 hσ
        rw [← he, hIH _ hδ']
        exact (ssP_lt_iff μ).2 ((add_lt_add_iff_left _).2 hδ')
  · obtain ⟨-, -, -, -, -, -, hμv, hηv⟩ := svK_facts hC hMG hτ hτ1 hEμ hμM hμT hT h1
    obtain ⟨e, he⟩ := ssP_range (svK_SC hC hMG hτ hτ1 hEμ hμM hμT hT h1) hμv
      (svK_fixv2_of hC hMG hτ hτ1 hEμ hμM hμT hREP hT h1)
    rw [← he]
    refine (ssP_le_iff μ).2 (not_lt.1 fun hlt => ?_)
    have hpe : p < e := by
      refine (ssP_lt_iff μ).1 ?_
      rw [hp, he]; exact (le_self_add : p ≤ p + δ).trans_lt hηv
    have hp1e : p + 1 ≤ e := Order.add_one_le_of_lt hpe
    have hσe : p + 1 + (e - (p + 1)) = e := Ordinal.add_sub_cancel_of_le hp1e
    have hσ : e - (p + 1) < δ := by rw [← hσe] at hlt; exact (add_lt_add_iff_left _).1 hlt
    have hT' : p + (e - (p + 1)) ∈ Tset τ := vz_T_down hτE hτ1 hT h1 ((add_le_add_iff_left p).2 hσ.le)
    have h2 := svK_lt hC hMG hτ hτ1 hEμ hμM hμT hT' hT h1 ((add_lt_add_iff_left p).2 hσ)
    rw [hIH _ hσ, hσe, he] at h2
    exact lt_irrefl _ h2

/-- **REP(μ)** at a level `E₁ ≤ μ < M` with `ssDatL μ ∈ Tᵗ`, from REP at the levels below `μ`. -/
theorem svK_rep2_of {μ : Ordinal.{0}} (hEμ : ggE ≤ μ) (hμM : μ < M) (hμT : ssDatL μ ∈ Tset τ)
    (hREP : ∀ j < μ, ssDatL j ∈ Tset τ → SvREP τ j) : SvREP τ μ := by
  have hτE : InE τ := gg_SC_eps hτ
  intro w hw hwF hτw hμw hwT hw1 hnf
  obtain ⟨y, hy⟩ := ssP_range hw hμw hwF
  have hyw : y < w := by
    refine lt_of_le_of_ne (hy ▸ ssP_le_self μ y) fun e => hnf ?_
    rw [← e] at hy ⊢; rw [hy]
  set m0 := max τ (ssDatL μ) with hm0
  have hm0w : m0 < w := max_lt hτw hμw
  obtain ⟨p, hbase, hpw, hmax⟩ := rh_base_below (ssP_normal μ) hm0w hnf
  have hnofix : ∀ z, p < z → z < w → z < ssP μ z := by
    intro z hpz hzw
    by_contra h
    push Not at h
    have hz := le_antisymm h (ssP_le_self μ z)
    have hm0z : m0 < z := by
      rcases hbase with e | ⟨h', -⟩
      · rw [← e]; exact hpz
      · exact h'.trans hpz
    exact absurd (hmax z hz hm0z hzw) (not_le.2 hpz)
  rcases hbase with hpm | ⟨hm0p, hpp⟩
  · -- no fixed point of `Φ_μ` in `(m0, w)`: the first index `c₀` above `m0`
    obtain ⟨c0, hc0, hmin⟩ := sv_first_idx μ m0
    have hc0y : c0 ≤ y := by
      refine not_lt.1 fun hlt => ?_
      have := hmin y hlt
      rw [hy] at this
      exact absurd hm0w (not_lt.2 this)
    set D := y - c0 with hDdef
    have hcD : c0 + D = y := Ordinal.add_sub_cancel_of_le hc0y
    have hDw : D < w := (Ordinal.sub_le_self y c0).trans_lt hyw
    have hcond : ∀ σ, σ ≤ D → c0 + σ < ssP μ (c0 + σ) := by
      intro σ hσ
      have hzy : c0 + σ ≤ y := by rw [← hcD]; exact (add_le_add_iff_left c0).2 hσ
      refine lt_of_le_of_ne (ssP_le_self μ _) fun hz => ?_
      have hpz : p < c0 + σ := by rw [hpm, hz]; exact hc0.trans_le ((ssP_le_iff μ).2 le_self_add)
      have := hnofix _ hpz (hzy.trans_lt hyw)
      rw [← hz] at this; exact lt_irrefl _ this
    have hT : D ∈ Tset τ := vz_T_down hτE hτ1 hwT hw1 hDw.le
    refine ⟨D, hT, hDw.trans hw1, hDw, ?_⟩
    rw [svK_enum0_of hC hMG hτ hτ1 hEμ hμM hμT hREP ((le_max_left _ _).trans_lt hc0)
      ((le_max_right _ _).trans_lt hc0) (fun c hc => le_max_iff.1 (hmin c hc)) D hT (hDw.trans hw1)
      (fun σ hσ => le_add_self.trans_lt (hcond σ hσ)),
      hcD, hy]
  · have hτp : τ < p := (le_max_left _ _).trans_lt hm0p
    have hpy : p < y := (ssP_lt_iff μ).1 (by rw [hpp, hy]; exact hpw)
    set D := y - p with hDdef
    have hpD : p + D = y := Ordinal.add_sub_cancel_of_le hpy.le
    have hD0 : D ≠ 0 := by
      rintro h0; rw [h0, add_zero] at hpD; exact absurd hpD hpy.ne
    set δ := D - 1 with hδdef
    have hδ : 1 + δ = D := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hD0)
    have hpδy : p + 1 + δ = y := by rw [add_assoc, hδ, hpD]
    have hpδw : p + δ < w := by
      refine lt_of_le_of_lt ?_ hyw
      rw [← hpδy, add_assoc]; exact (add_le_add_iff_left p).2 le_add_self
    have hcond : ∀ σ, σ ≤ δ → p + 1 + σ < ssP μ (p + 1 + σ) := by
      intro σ hσ
      refine hnofix _ (lt_of_lt_of_le (lt_add_one p) le_self_add) (lt_of_le_of_lt ?_ hyw)
      rw [← hpδy]; exact (add_le_add_iff_left _).2 hσ
    have hT : p + δ ∈ Tset τ := vz_T_down hτE hτ1 hwT hw1 hpδw.le
    refine ⟨p + δ, hT, hpδw.trans hw1, hpδw, ?_⟩
    rw [svK_enum_fix2_of hC hMG hτ hτ1 hEμ hμM hμT hREP hpp hτp δ hT (hpδw.trans hw1) hcond, hpδy, hy]

end Base

/-! ## Over a level-closed base -/

section Fix

variable {M : Ordinal.{0}} (hC : SvCit M) (hMG : M ≤ ggGam) {τ : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1)
  (hτF : ∀ μ, μ < ggE → rkDat μ < τ → rkP μ τ = τ)
include hC hMG hτ hτ1 hτF

/-- **REP(μ) at every level `μ < M` with `ssDatL μ ∈ Tᵗ`** (below `E₁` from `R2.RkTh`). -/
theorem svK_rep2 (μ : Ordinal.{0}) : μ < M → ssDatL μ ∈ Tset τ → SvREP τ μ := by
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμM hμT
  rcases lt_or_ge μ ggE with hμE | hEμ
  · exact sv_REP_low hτ hτ1 hτF hμE hμT
  · exact svK_rep2_of hC hMG hτ hτ1 hEμ hμM hμT fun j hj hjT => IH j hj (hj.trans hμM) hjT

/-- **`ϑᵗ(Δ_μ + η)` is a fixed point of every `Φ_j`, `j < μ`, `ssDatL j` below it** (`E₁ ≤ μ < M`). -/
theorem svK_fixv2 {μ : Ordinal.{0}} (hEμ : ggE ≤ μ) (hμM : μ < M) (hμT : ssDatL μ ∈ Tset τ) {η : Ordinal.{0}}
    (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    ∀ j < μ, ssDatL j < vt τ (Om1 * (Om1 + μ) + η) →
      ssP j (vt τ (Om1 * (Om1 + μ) + η)) = vt τ (Om1 * (Om1 + μ) + η) :=
  svK_fixv2_of hC hMG hτ hτ1 hEμ hμM hμT
    (fun j hj hjT => svK_rep2 hC hMG hτ hτ1 hτF j (hj.trans hμM) hjT) hη hηΩ

/-- **`ϑᵗ(Δ_μ + η)` is a value of `Φ_μ`** (`E₁ ≤ μ < M`). -/
theorem svK_range {μ : Ordinal.{0}} (hEμ : ggE ≤ μ) (hμM : μ < M) (hμT : ssDatL μ ∈ Tset τ) {η : Ordinal.{0}}
    (hη : η ∈ Tset τ) (hηΩ : η < Om1) : ∃ e, ssP μ e = vt τ (Om1 * (Om1 + μ) + η) :=
  ssP_range (svK_SC hC hMG hτ hτ1 hEμ hμM hμT hη hηΩ) (svK_facts hC hMG hτ hτ1 hEμ hμM hμT hη hηΩ).2.2.2.2.2.2.1
    (svK_fixv2 hC hMG hτ hτ1 hτF hEμ hμM hμT hη hηΩ)

/-- **`ϑᵗ(Δ_μ + η) = Φ_μ(c₀ + η)`** for the first index `c₀` above `τ` and `ssDatL μ` (`E₁ ≤ μ < M`). -/
theorem svK_enum0 {μ c0 : Ordinal.{0}} (hEμ : ggE ≤ μ) (hμM : μ < M) (hμT : ssDatL μ ∈ Tset τ)
    (hc0τ : τ < ssP μ c0) (hc0d : ssDatL μ < ssP μ c0) (hmin : ∀ c < c0, ssP μ c ≤ τ ∨ ssP μ c ≤ ssDatL μ) :
    ∀ η, η ∈ Tset τ → η < Om1 → (∀ σ, σ ≤ η → σ < ssP μ (c0 + σ)) →
      vt τ (Om1 * (Om1 + μ) + η) = ssP μ (c0 + η) :=
  svK_enum0_of hC hMG hτ hτ1 hEμ hμM hμT
    (fun j hj hjT => svK_rep2 hC hMG hτ hτ1 hτF j (hj.trans hμM) hjT) hc0τ hc0d hmin

/-- **`ϑᵗ(Δ_μ + (p + δ)) = Φ_μ(p + 1 + δ)`** for a fixed point `p > τ` of `Φ_μ` (`E₁ ≤ μ < M`). -/
theorem svK_enum_fix2 {μ : Ordinal.{0}} (hEμ : ggE ≤ μ) (hμM : μ < M) (hμT : ssDatL μ ∈ Tset τ)
    {p : Ordinal.{0}} (hp : ssP μ p = p) (hτp : τ < p) :
    ∀ δ, p + δ ∈ Tset τ → p + δ < Om1 → (∀ σ, σ ≤ δ → p + 1 + σ < ssP μ (p + 1 + σ)) →
      vt τ (Om1 * (Om1 + μ) + (p + δ)) = ssP μ (p + 1 + δ) :=
  svK_enum_fix2_of hC hMG hτ hτ1 hEμ hμM hμT
    (fun j hj hjT => svK_rep2 hC hMG hτ hτ1 hτF j (hj.trans hμM) hjT) hp hτp

end Fix

end Googology.Trans.PoR.InaccPsi.R2.Sv
