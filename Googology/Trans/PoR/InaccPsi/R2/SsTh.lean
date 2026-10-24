import Googology.Trans.PoR.InaccPsi.R2.SsLev
import Googology.Trans.PoR.InaccPsi.R2.CitedSs

/-!
# `ϑᵗ(ε_{Ω₁+1} + η)`: the values of `Φ_{E₁}` above a level-closed base

For a strongly critical base `τ < Ω₁` that is a fixed point of every level `Φ_μ`, `μ < ε_{Ω₁+1}`, `rkDat μ < τ`
(i.e. `τ` level-closed), `E₁ = ε_{Ω₁+1} = Gg.ggE`, `Φ_{E₁} = Rk.rkP E₁` (the enumeration of the level-closed points,
`Ss.ssLC_iff`), from the cited facts of `R2.CitedSs` (`ssE_mem`, `ssVt_lt`, `ssLt_of_vt_lt`, `ssLevel_lt`) and the
lower levels of `R2.RkTh`:

* `ssK_facts`, `ssK_lt` (**`η ↦ ϑᵗ(E₁ + η)` is strictly increasing**), `ssK_lt_lower` (**the terms of the lower
  levels `ϑᵗ(Ω₁·(Ω₁ + j) + σ)`, `j < E₁`, stay below**), `ssK_SC` (**`ϑᵗ(E₁ + η)` is strongly critical**), `ssK_inj`;
* `ssK_min` (minimality), `ssK_le` (**`ϑᵗ(E₁ + η) ≤ Φ_{E₁}(τ + η + 1)`**), `ssK_fixv2` (**`ϑᵗ(E₁ + η)` is a fixed
  point of every `Φ_j`, `j < E₁`, `rkDat j` below it**, i.e. level-closed), `ssK_below_fix`;
* `ssK_enum` (**`ϑᵗ(E₁ + η) = Φ_{E₁}(c + 1 + η)`** for `τ = Φ_{E₁}(c)` when `c + 1 + σ < Φ_{E₁}(c + 1 + σ)` for
  every `σ ≤ η`: the base need not be a fixed point of `Φ_{E₁}`), `ssK_enum_fix2` (**`ϑᵗ(E₁ + (p + δ)) = Φ_{E₁}(p +
  1 + δ)`** for a fixed point `p > τ` of `Φ_{E₁}`).

The proofs of `R2.RkTh` at the level `μ = E₁`.  No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ss

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rb Googology.Trans.PoR.InaccPsi.R2.Rd
  Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj
  Googology.Trans.PoR.InaccPsi.R2.Rk

/-- `rjDat E₁ = 0`. -/
theorem ss_rjDat_E : rjDat ggE = 0 := by
  rw [rjDat, dif_neg (fun h => absurd h.2 (lt_irrefl _)), if_neg (not_lt.2 rj_Om1_lt_E.le)]

/-- `E₁ < Γ_{Ω₁+1}`: `E₁ = φ(1, Ω₁ + 1)` is not strongly critical. -/
theorem ss_E_lt_Gam : (ggE : Ordinal.{0}) < ggGam := by
  refine lt_of_le_of_ne ggE_le_ggGam fun e => ?_
  have hSC : SC ggE := e ▸ ggGam_spec.1
  have h1 : (1 : Ordinal.{0}) < ggE := gg_one_lt_of_SC hSC
  have h2 : Om 1 + 1 < ggE := (ev_isSuccLimit_of_inE rk_E_inE).add_one_lt rk_Om1_E
  have := hSC.2 1 h1 (Om 1 + 1) h2
  rw [← rk_E_eq] at this
  exact lt_irrefl _ this

theorem ss_E_lt_Om2 : (ggE : Ordinal.{0}) < OmTwo := by
  have h := ss_E_lt_Gam.trans_le ggGam_le_Om2
  rwa [Om_of_ne_zero (by norm_num), one_add_one_eq_two] at h

theorem ss_arg_lt {η : Ordinal.{0}} (hηΩ : η < Om1) : ggE + η < OmTwo :=
  isPrincipal_add_omega 2 ss_E_lt_Om2 (hηΩ.trans Om1_lt_OmTwo)

/-- `Ω₁·M' + σ < E₁` for a code `M' < E₁` and `σ < Ω₁`. -/
theorem ss_lower_lt {M' σ : Ordinal.{0}} (hM' : M' < ggE) (hσ : σ < Om1) : Om1 * M' + σ < ggE := by
  calc Om1 * M' + σ < Om1 * M' + Om1 := (add_lt_add_iff_left _).2 hσ
    _ = Om1 * (M' + 1) := by rw [mul_add_one]
    _ ≤ Om1 * ggE := mul_le_mul_right ((ev_isSuccLimit_of_inE rk_E_inE).add_one_lt hM').le _
    _ = ggE := ss_Om1_mul_E

section Base

variable {τ : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1)
include hτ hτ1

/-- **The facts on `ϑᵗ(E₁ + η)`.** -/
theorem ssK_facts {η : Ordinal.{0}} (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    ggE + η ∈ Tset τ ∧ ggE + η < OmTwo ∧ vt τ (ggE + η) ∈ Tset τ ∧ τ < vt τ (ggE + η) ∧
    vt τ (ggE + η) < Om1 ∧ InE (vt τ (ggE + η)) ∧ η < vt τ (ggE + η) := by
  have hτE : InE τ := gg_SC_eps hτ
  have hargT : ggE + η ∈ Tset τ := vzT_add hτE hτ1 (ssE_mem hτE hτ1) hη
  have harg2 := ss_arg_lt hηΩ
  obtain ⟨hvT, -, hv1, -, -⟩ := vt_memTwo hτE hτ1 hargT harg2
  have hE := (vt_E_iff hτE hτ1 hargT harg2).2 (rj_Om1_lt_E.le.trans le_self_add)
  exact ⟨hargT, harg2, hvT, hE.1, hv1, hE.2, ssLevel_lt hτE hτ1 hη hηΩ⟩

/-- **`η ↦ ϑᵗ(E₁ + η)` is strictly increasing.** -/
theorem ssK_lt {σ η : Ordinal.{0}} (hσ : σ ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1) (h : σ < η) :
    vt τ (ggE + σ) < vt τ (ggE + η) := by
  have hτE : InE τ := gg_SC_eps hτ
  obtain ⟨-, -, -, -, -, hvE, hηv⟩ := ssK_facts hτ hτ1 hη hηΩ
  have := ssVt_lt hτE hτ1 le_rfl (by rw [ss_rjDat_E]; exact mem_T_of_le hτE hτ1 zero_le) hσ (h.trans hηΩ) hη hηΩ
    (by rw [ss_Om1_mul_E]; exact (add_lt_add_iff_left _).2 h) (by rw [ss_rjDat_E]; exact hvE.pos)
    (h.trans hηv)
  rwa [ss_Om1_mul_E] at this

/-- **A lower level stays below**: `ϑᵗ(Ω₁·(Ω₁ + j) + σ) < ϑᵗ(E₁ + η)` for `j < E₁` and `σ`, `rkDat j` below the
right side. -/
theorem ssK_lt_lower {j σ η : Ordinal.{0}} (hj : j < ggE) (hσ : σ ∈ Tset τ) (hσΩ : σ < Om1)
    (hη : η ∈ Tset τ) (hηΩ : η < Om1) (hσv : σ < vt τ (ggE + η)) (hjv : rkDat j < vt τ (ggE + η)) :
    vt τ (Om1 * (Om1 + j) + σ) < vt τ (ggE + η) := by
  have hτE : InE τ := gg_SC_eps hτ
  obtain ⟨-, -, hvT, -, hv1, -, -⟩ := ssK_facts hτ hτ1 hη hηΩ
  have hjT : rkDat j ∈ Tset τ := vz_T_down hτE hτ1 hvT hv1 hjv.le
  exact ssVt_lt hτE hτ1 (rk_Om1_add_lt hj).le hjT hσ hσΩ hη hηΩ
    ((ss_lower_lt (rk_Om1_add_lt hj) hσΩ).trans_le le_self_add) hjv hσv

/-- **`ϑᵗ(E₁ + η)` is strongly critical** (the argument of `Rj.rjK_SC`, with `ssVt_lt` at the lower levels
`Ω₁·a + ι`, `a < Ω₁`). -/
theorem ssK_SC {η : Ordinal.{0}} (hη : η ∈ Tset τ) (hηΩ : η < Om1) : SC (vt τ (ggE + η)) := by
  have hτE : InE τ := gg_SC_eps hτ
  obtain ⟨-, -, hvT, hτv, hv1, hvE, -⟩ := ssK_facts hτ hτ1 hη hηΩ
  set v := vt τ (ggE + η) with hv
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
    have haE : a < ggE := haΩ.trans rj_Om1_lt_E
    have harg : Om1 * a + lvInd a τ b < ggE + η :=
      (ss_lower_lt haE (hindv.trans hv1)).trans_le le_self_add
    exact ssVt_lt hτE hτ1 haE.le (by rw [rjDat_small haΩ]; exact haT) (hTv _ hindv) (hindv.trans hv1) hη hηΩ
      harg (by rw [rjDat_small haΩ]; exact hav) hindv
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

/-- `η ↦ ϑᵗ(E₁ + η)` is injective on `Tᵗ ∩ Ω₁`. -/
theorem ssK_inj {a b : Ordinal.{0}} (ha : a ∈ Tset τ) (ha1 : a < Om1) (hb : b ∈ Tset τ) (hb1 : b < Om1)
    (h : vt τ (ggE + a) = vt τ (ggE + b)) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (ssK_lt hτ hτ1 ha hb hb1 hab).ne
  · exact hab
  · exact absurd h (ssK_lt hτ hτ1 hb ha ha1 hab).ne'

/-- **Minimality at the level `E₁`**: `ϑᵗ(E₁ + η) ≤ s` for every strongly critical `s > τ, η` that is a fixed point
of every `Φ_j`, `j < E₁`, `rkDat j < s`, above all `ϑᵗ(E₁ + σ)`, `σ < η` (the proof of `Rk.rkK_min`). -/
theorem ssK_min {η s : Ordinal.{0}} (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (hs : SC s) (hsF : ∀ j < ggE, rkDat j < s → rkP j s = s) (hτs : τ < s) (hηs : η < s)
    (hprev : ∀ σ, σ < η → vt τ (ggE + σ) < s) :
    vt τ (ggE + η) ≤ s := by
  have hτE : InE τ := gg_SC_eps hτ
  obtain ⟨-, -, hvT, -, hv1, -, -⟩ := ssK_facts hτ hτ1 hη hηΩ
  by_contra hlt
  push Not at hlt
  obtain ⟨m, -, -, -, hTm, hm1, -⟩ := vz_next hτE hτ1
  have hvm : vt τ (ggE + η) < m := (hTm _ hv1).1 hvT
  have hs1 : s < Om1 := hlt.trans hv1
  have hsT : s ∈ Tset τ := (hTm s hs1).2 (hlt.trans hvm)
  have hsE : InE s := gg_SC_eps hs
  have hsP : Indec s := inE_indec hsE
  obtain ⟨ξ, hξT, hξ2, hξs⟩ := vt_rep hτE hτ1 hsT hτs.le hs1 hsP
  have hlt' : vt τ ξ < vt τ (ggE + η) := by rw [hξs]; exact hlt
  have hξlt : ξ < ggE + η := ssLt_of_vt_lt hτE hτ1 hξT hξ2 hη hηΩ (by rw [hξs]; exact hηs) hlt'
  rcases lt_or_ge ξ (Om1 * Om1) with hξ | hξ
  · rcases lt_or_ge ξ Om1 with hξ1 | hξ1
    · have := (vt_E_iff hτE hτ1 hξT hξ2).1 ⟨by rw [hξs]; exact hτs, by rw [hξs]; exact hsE⟩
      exact absurd this (not_le.2 hξ1)
    · obtain ⟨hq1, hrT, hr1, hdec⟩ := Lu.lu_split hτE hτ1 hξT hξ2 hξ1
      have hqT : ξ / Om1 ∈ Tset τ := lgQuot_mem hτE hτ1 hξT hξ
      have hqΩ : ξ / Om1 < Om1 := (Ordinal.lt_mul_iff_div_lt rj_Om1_pos.ne').1 hξ
      exact Mx.mxSC_ne_th hτE hτ1 hq1 hqT hqΩ hrT hr1 hs (by rw [hdec, hξs])
  · rcases lt_or_ge ξ ggE with hξ' | hξ'
    · -- a lower level `j < E₁`: `s = ϑᵗ(Δ_j + σ)` is not a fixed point of `Φ_j`
      have hξ'' : ξ < Om1 * (Om1 + ggE) := by rw [ss_Om1_add_E, ss_Om1_mul_E]; exact hξ'
      obtain ⟨j, hjk, σ, hσΩ, he⟩ := Ri.riK_decomp hξ hξ''
      have hσT : σ ∈ Tset τ := vzRem_T hτE hτ1 hξT hξ2 he (dvd_mul_right _ _) hσΩ
      have hjT : rkDat j ∈ Tset τ := by
        have hξT' : Om1 * (Om1 + j) + σ ∈ Tset τ := by rw [← he]; exact hξT
        exact rkArg_dat hτE hτ1 le_self_add (rk_Om1_add_lt hjk) hσΩ hξT'
      have hle := rkK_le hτ hτ1 j hjk hjT σ hσT hσΩ
      rw [← he, hξs] at hle
      obtain ⟨-, -, -, -, -, -, hjv, hσv⟩ := rkK_facts hτ hτ1 hjT hjk hσT hσΩ
      rw [← he, hξs] at hσv hjv
      have h3 : τ + σ + 1 < s := hs.add_one_lt ((lq_SC_indec hs).add_lt hτs hσv)
      have h4 : rkP j (τ + σ + 1) < s := by
        conv_rhs => rw [← hsF j hjk hjv]
        exact (rkP_lt_iff j).2 h3
      exact absurd hle (not_le.2 h4)
    · have hσe : ggE + (ξ - ggE) = ξ := Ordinal.add_sub_cancel_of_le hξ'
      have hσ : ξ - ggE < η := by
        rw [← hσe] at hξlt; exact (add_lt_add_iff_left _).1 hξlt
      have h := hprev _ hσ
      rw [hσe, hξs] at h
      exact lt_irrefl _ h

/-- **LE(E₁)**: `ϑᵗ(E₁ + η) ≤ Φ_{E₁}(τ + η + 1)` (the proof of `Rk.rkK_le_of`). -/
theorem ssK_le : ∀ η, η ∈ Tset τ → η < Om1 → vt τ (ggE + η) ≤ rkP ggE (τ + η + 1) := by
  have hτE : InE τ := gg_SC_eps hτ
  intro η
  induction η using WellFoundedLT.induction with
  | ind η IH =>
  intro hη hηΩ
  refine ssK_min hτ hτ1 hη hηΩ (rkP_SC ggE _)
    (fun j hj hd => rkP_fix_lower hj ⟨_, rfl⟩ hd) ?_ ?_ fun σ hσ => ?_
  · exact (lt_of_le_of_lt le_self_add (lt_add_one _)).trans_le (rkP_le_self ggE _)
  · exact lt_of_le_of_lt (le_add_self : η ≤ τ + η) ((lt_add_one (τ + η)).trans_le (rkP_le_self ggE _))
  · have hσT : σ ∈ Tset τ := vz_T_down hτE hτ1 hη hηΩ hσ.le
    refine (IH σ hσ hσT (hσ.trans hηΩ)).trans_lt ((rkP_lt_iff ggE).2 ?_)
    exact (Order.add_one_le_of_lt ((add_lt_add_iff_left τ).2 hσ)).trans_lt (lt_add_one _)

omit hτ hτ1 in
/-- `ϑᵗ(E₁ + σ) < p` for `σ < p` and every fixed point `p > τ` of `Φ_{E₁}`, given LE(E₁). -/
theorem ssK_below_fix (hLE : ∀ η, η ∈ Tset τ → η < Om1 → vt τ (ggE + η) ≤ rkP ggE (τ + η + 1))
    {p : Ordinal.{0}} (hp : rkP ggE p = p) (hτp : τ < p) (hp1 : p < Om1) {σ : Ordinal.{0}}
    (hσT : σ ∈ Tset τ) (hσ : σ < p) : vt τ (ggE + σ) < p := by
  have hpSC : SC p := hp ▸ rkP_SC ggE p
  have h1 : τ + σ + 1 < p := hpSC.add_one_lt ((lq_SC_indec hpSC).add_lt hτp hσ)
  refine (hLE σ hσT (hσ.trans hp1)).trans_lt ?_
  conv_rhs => rw [← hp]
  exact (rkP_lt_iff ggE).2 h1

section Fix

variable (hτF : ∀ μ, μ < ggE → rkDat μ < τ → rkP μ τ = τ)
include hτF

/-- **`ϑᵗ(E₁ + η)` is level-closed**: a fixed point of every `Φ_j`, `j < E₁`, `rkDat j` below it (the proof of
`Rk.rkK_fixv2_of`, with REP2 at the levels `j < E₁` from `Rk.rkK_rep2`). -/
theorem ssK_fixv2 {η : Ordinal.{0}} (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    ∀ j < ggE, rkDat j < vt τ (ggE + η) → rkP j (vt τ (ggE + η)) = vt τ (ggE + η) := by
  have hτE : InE τ := gg_SC_eps hτ
  obtain ⟨-, -, hvT, hτv, hv1, -, -⟩ := ssK_facts hτ hτ1 hη hηΩ
  have hvSC := ssK_SC hτ hτ1 hη hηΩ
  intro j
  induction j using WellFoundedLT.induction with
  | ind j IHj =>
  intro hjk hjv
  by_contra hnf
  have hjT := rkK_dat_T hτE hτ1 hvT hv1 hjv
  obtain ⟨σ, hσT, hσΩ, hσv, he⟩ :=
    rkK_rep2 hτ hτ1 hτF j hjk hjT _ hvSC (fun i hi hiv => IHj i hi (hi.trans hjk) hiv) hτv hjv hvT hv1 hnf
  have := ssK_lt_lower hτ hτ1 hjk hσT hσΩ hη hηΩ hσv hjv
  rw [he] at this
  exact lt_irrefl _ this

/-- `ϑᵗ(E₁ + η)` is a value of `Φ_{E₁}`. -/
theorem ssK_range {η : Ordinal.{0}} (hη : η ∈ Tset τ) (hηΩ : η < Om1) : ∃ e, rkP ggE e = vt τ (ggE + η) :=
  rkP_range (ssK_SC hτ hτ1 hη hηΩ) (by rw [ssDatE]; exact (ssK_SC hτ hτ1 hη hηΩ).1)
    (ssK_fixv2 hτ hτ1 hτF hη hηΩ)

/-- **`ϑᵗ(E₁ + η) = Φ_{E₁}(c + 1 + η)`** for a base `τ = Φ_{E₁}(c)` when `c + 1 + σ < Φ_{E₁}(c+1+σ)` for every
`σ ≤ η` (the proof of `Rk.rkK_enum_of` with the index `c` of the base in place of `τ`). -/
theorem ssK_enum {c : Ordinal.{0}} (hc : rkP ggE c = τ) :
    ∀ η, η ∈ Tset τ → η < Om1 → (∀ σ, σ ≤ η → c + 1 + σ < rkP ggE (c + 1 + σ)) →
      vt τ (ggE + η) = rkP ggE (c + 1 + η) := by
  have hτE : InE τ := gg_SC_eps hτ
  intro η
  induction η using WellFoundedLT.induction with
  | ind η IH =>
  intro hη hηΩ hcond
  have hIH : ∀ σ, σ < η → vt τ (ggE + σ) = rkP ggE (c + 1 + σ) := fun σ hσ =>
    IH σ hσ (vz_T_down hτE hτ1 hη hηΩ hσ.le) (hσ.trans hηΩ) fun σ' hσ' => hcond σ' (hσ'.trans hσ.le)
  have hτs : τ < rkP ggE (c + 1 + η) := by
    rw [← hc]; exact (rkP_lt_iff ggE).2 ((lt_add_one c).trans_le le_self_add)
  apply le_antisymm
  · refine ssK_min hτ hτ1 hη hηΩ (rkP_SC ggE _) (fun j hj hd => rkP_fix_lower hj ⟨_, rfl⟩ hd)
      hτs ?_ fun σ hσ => ?_
    · exact (le_add_self).trans_lt (hcond η le_rfl)
    · rw [hIH σ hσ]; exact (rkP_lt_iff ggE).2 ((add_lt_add_iff_left _).2 hσ)
  · obtain ⟨-, -, -, hτv, -, -, -⟩ := ssK_facts hτ hτ1 hη hηΩ
    obtain ⟨e, he⟩ := ssK_range hτ hτ1 hτF hη hηΩ
    rw [← he]
    refine (rkP_le_iff ggE).2 (not_lt.1 fun hlt => ?_)
    have hce : c < e := (rkP_lt_iff ggE).1 (by rw [hc, he]; exact hτv)
    have hc1 : c + 1 ≤ e := Order.add_one_le_of_lt hce
    have hσe : c + 1 + (e - (c + 1)) = e := Ordinal.add_sub_cancel_of_le hc1
    have hσ : e - (c + 1) < η := by rw [← hσe] at hlt; exact (add_lt_add_iff_left _).1 hlt
    have h1 := ssK_lt hτ hτ1 (vz_T_down hτE hτ1 hη hηΩ hσ.le) hη hηΩ hσ
    rw [hIH _ hσ, hσe, he] at h1
    exact lt_irrefl _ h1

/-- **`ϑᵗ(E₁ + (p + δ)) = Φ_{E₁}(p + 1 + δ)`** for a fixed point `p > τ` of `Φ_{E₁}` when `p + 1 + σ <
Φ_{E₁}(p+1+σ)` for every `σ ≤ δ` (the proof of `Rk.rkK_enum_fix2_of`). -/
theorem ssK_enum_fix2 {p : Ordinal.{0}} (hp : rkP ggE p = p) (hτp : τ < p) :
    ∀ δ, p + δ ∈ Tset τ → p + δ < Om1 → (∀ σ, σ ≤ δ → p + 1 + σ < rkP ggE (p + 1 + σ)) →
      vt τ (ggE + (p + δ)) = rkP ggE (p + 1 + δ) := by
  have hτE : InE τ := gg_SC_eps hτ
  have hLEk := ssK_le hτ hτ1
  intro δ
  induction δ using WellFoundedLT.induction with
  | ind δ IH =>
  intro hT h1 hcond
  have hp1 : p < Om1 := (le_self_add : p ≤ p + δ).trans_lt h1
  have hIH : ∀ δ', δ' < δ →
      vt τ (ggE + (p + δ')) = rkP ggE (p + 1 + δ') := fun δ' hδ' =>
    IH δ' hδ' (vz_T_down hτE hτ1 hT h1 ((add_le_add_iff_left p).2 hδ'.le))
      (((add_lt_add_iff_left p).2 hδ').trans h1) fun σ hσ => hcond σ (hσ.trans hδ'.le)
  have hpg : p < rkP ggE (p + 1 + δ) := by
    conv_lhs => rw [← hp]
    exact (rkP_lt_iff ggE).2 (lt_of_lt_of_le (lt_add_one p) le_self_add)
  apply le_antisymm
  · refine ssK_min hτ hτ1 hT h1 (rkP_SC ggE _) (fun j hj hd => rkP_fix_lower hj ⟨_, rfl⟩ hd)
      (hτp.trans hpg) ?_ fun σ hσ => ?_
    · have : p + δ ≤ p + 1 + δ := by
        rw [add_assoc]; exact (add_le_add_iff_left p).2 le_add_self
      exact this.trans_lt (hcond δ le_rfl)
    · rcases lt_or_ge σ p with hσp | hσp
      · exact (ssK_below_fix hLEk hp hτp hp1
          (vz_T_down hτE hτ1 hT h1 (hσp.le.trans le_self_add)) hσp).trans hpg
      · have he : p + (σ - p) = σ := Ordinal.add_sub_cancel_of_le hσp
        have hδ' : σ - p < δ := by rw [← he] at hσ; exact (add_lt_add_iff_left p).1 hσ
        rw [← he, hIH _ hδ']
        exact (rkP_lt_iff ggE).2 ((add_lt_add_iff_left _).2 hδ')
  · obtain ⟨-, -, -, -, -, -, hηv⟩ := ssK_facts hτ hτ1 hT h1
    obtain ⟨e, he⟩ := ssK_range hτ hτ1 hτF hT h1
    rw [← he]
    refine (rkP_le_iff ggE).2 (not_lt.1 fun hlt => ?_)
    have hpe : p < e := by
      refine (rkP_lt_iff ggE).1 ?_
      rw [hp, he]; exact (le_self_add : p ≤ p + δ).trans_lt hηv
    have hp1e : p + 1 ≤ e := Order.add_one_le_of_lt hpe
    have hσe : p + 1 + (e - (p + 1)) = e := Ordinal.add_sub_cancel_of_le hp1e
    have hσ : e - (p + 1) < δ := by rw [← hσe] at hlt; exact (add_lt_add_iff_left _).1 hlt
    have hT' : p + (e - (p + 1)) ∈ Tset τ := vz_T_down hτE hτ1 hT h1 ((add_le_add_iff_left p).2 hσ.le)
    have h2 := ssK_lt hτ hτ1 hT' hT h1 ((add_lt_add_iff_left p).2 hσ)
    rw [hIH _ hσ, hσe, he] at h2
    exact lt_irrefl _ h2

end Fix

end Base

end Googology.Trans.PoR.InaccPsi.R2.Ss
