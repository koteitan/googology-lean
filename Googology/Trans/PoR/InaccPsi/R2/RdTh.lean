import Googology.Trans.PoR.InaccPsi.R2.RbTh

/-!
# `ϑᵗ(Ω₁·(Ω₁+1) + η)`: the fixed points of `Γ_` above `τ`, enumerated by `F = deriv Γ_`

For a strongly critical base `τ < Ω₁` (`Γ_ = Ordinal.gamma`, `F = Ordinal.deriv Γ_`, the enumeration of the fixed
points of `Γ_`), from the cited facts of `R2.CitedLq` at `γ = β = 1` ([W07a] Lemma 3.30 at `Ω₁·(Ω₁·γ + β) + η`,
[W07b] Def 4.1 there):

* `rd1_facts`, `rd1_lt` (**`η ↦ ϑᵗ(Ω₁·(Ω₁+1) + η)` is strictly increasing**), `rd_sq_lt_1` (`ϑᵗ(Ω₁·Ω₁ + σ) <
  ϑᵗ(Ω₁·(Ω₁+1) + η)` for `σ` below the right side);
* `rd_sq_rep` (**every strongly critical `w ∈ Tᵗ ∩ (τ, Ω₁)` that is not a fixed point of `Γ_` is `ϑᵗ(Ω₁·Ω₁ + σ)` with
  `σ < w`**: `Lq.lq_sq_rep` or `Rb.rb_sq_enum_fix` past the largest fixed point below `w`);
* `rd1_SC` (**strongly critical**), `rd1_fix` (**a fixed point of `Γ_`**);
* `rd1_min` (**minimality**: `ϑᵗ(Ω₁·(Ω₁+1) + η) ≤ s` for every fixed point `s > τ, η` of `Γ_` above all
  `ϑᵗ(Ω₁·(Ω₁+1) + σ)`, `σ < η`), `rd1_le` (`≤ F(c + η + 1)`, `F(c) = τ`), `rd1_below_fix`;
* `rd1_enum` (**`ϑᵗ(Ω₁·(Ω₁+1) + η) = F(c + 1 + η)`** for `F(c) = τ` when `1 + σ < F(c+1+σ)` for every `σ ≤ η`),
  `rd1_enum_fix` (**`ϑᵗ(Ω₁·(Ω₁+1) + (p + δ)) = F(p + 1 + δ)`** for a fixed point `p = F(p) > τ` of `F` when
  `p + 1 + σ < F(p+1+σ)` for every `σ ≤ δ`);
* `rd1_zeta`, `rd1_zeta_fix`, `rd1_zeta_fix_add` (**`ζᵗ = lqZeta τ (Ω₁·(Ω₁+1)) η`** in the three cases: `logend(η)`,
  `0` at a fixed point `p` of `F`, `logend(p + δ)` for `δ ≠ 0`);
* `rd1_lh` (**`lhᵗ(x) = x·x + x + x + ζᵗ_x`** for `x = ϑᵗ(Ω₁·(Ω₁+1) + η)`, `Lq.lq_lh` at `γ = β = 1`).

No new axiom beyond `R2.CitedLq`, `R2.CitedLg` and the axioms used by `R2.RbTh`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rd

open Ordinal Order Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Lq
  Googology.Trans.PoR.InaccPsi.R2.Rb

/-! ## The enumeration `F` of the fixed points of `Γ_` -/

theorem rdF_fix (o : Ordinal.{0}) : gamma (deriv gamma o) = deriv gamma o := deriv_fp isNormal_gamma o

theorem rdF_SC (o : Ordinal.{0}) : SC (deriv gamma o) := by
  have h := lq_gamma_SC (deriv gamma o)
  rwa [rdF_fix] at h

theorem rdF_lt {a b : Ordinal.{0}} : deriv gamma a < deriv gamma b ↔ a < b := (deriv_strictMono gamma).lt_iff_lt

theorem rdF_le {a b : Ordinal.{0}} : deriv gamma a ≤ deriv gamma b ↔ a ≤ b := (deriv_strictMono gamma).le_iff_le

theorem rd_le_F (o : Ordinal.{0}) : o ≤ deriv gamma o := (isNormal_deriv gamma).strictMono.le_apply

/-- A fixed point of `Γ_` is a value of `F`. -/
theorem rdF_of_fix {x : Ordinal.{0}} (h : gamma x = x) : ∃ e, deriv gamma e = x :=
  (le_iff_deriv isNormal_gamma).1 h.le

/-- A fixed point of `Γ_` is strongly critical. -/
theorem rd_SC_of_fix {x : Ordinal.{0}} (h : gamma x = x) : SC x := by
  have := lq_gamma_SC x; rwa [h] at this

theorem rd_Om1_eq : Om1 * (Om1 * 1 + 1) = Om1 * Om1 + Om1 := by rw [mul_one, mul_add, mul_one]

section Base

variable {τ : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1)
include hτ hτ1

/-- **The facts on `ϑᵗ(Ω₁·(Ω₁+1) + η)`.** -/
theorem rd1_facts {η : Ordinal.{0}} (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    Om1 * (Om1 * 1 + 1) + η ∈ Tset τ ∧ Om1 * (Om1 * 1 + 1) + η < OmTwo ∧
    vt τ (Om1 * (Om1 * 1 + 1) + η) ∈ Tset τ ∧ τ < vt τ (Om1 * (Om1 * 1 + 1) + η) ∧
    vt τ (Om1 * (Om1 * 1 + 1) + η) < Om1 ∧ InE (vt τ (Om1 * (Om1 * 1 + 1) + η)) ∧
    (1 : Ordinal.{0}) < vt τ (Om1 * (Om1 * 1 + 1) + η) ∧ η < vt τ (Om1 * (Om1 * 1 + 1) + η) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have h1T : (1 : Ordinal.{0}) ∈ Tset τ := mem_T_of_le hτE hτ1 (Lu.lu_one_lt_E hτE).le
  have h1Ω : (1 : Ordinal.{0}) < Om1 := (Lu.lu_one_lt_E hτE).trans hτ1
  obtain ⟨a, b, c, d, e, f, -, g1, -, g3⟩ := lq_facts hτE hτ1 le_rfl h1T h1Ω h1T h1Ω hη hηΩ
  exact ⟨a, b, c, d, e, f, g1, g3⟩

/-- **`η ↦ ϑᵗ(Ω₁·(Ω₁+1) + η)` is strictly increasing** on `Tᵗ ∩ Ω₁`. -/
theorem rd1_lt {σ η : Ordinal.{0}} (hσ : σ ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1) (h : σ < η) :
    vt τ (Om1 * (Om1 * 1 + 1) + σ) < vt τ (Om1 * (Om1 * 1 + 1) + η) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have h1T : (1 : Ordinal.{0}) ∈ Tset τ := mem_T_of_le hτE hτ1 (Lu.lu_one_lt_E hτE).le
  have h1Ω : (1 : Ordinal.{0}) < Om1 := (Lu.lu_one_lt_E hτE).trans hτ1
  obtain ⟨-, -, -, -, -, -, h1v, hηv⟩ := rd1_facts hτ hτ1 hη hηΩ
  exact lqVt_lt hτE hτ1 h1T h1Ω h1T h1Ω hσ (h.trans hηΩ) le_rfl h1T h1Ω h1T h1Ω hη hηΩ
    ((add_lt_add_iff_left _).2 h) h1v h1v (h.trans hηv)

/-- `ϑᵗ(Ω₁·Ω₁ + σ) < ϑᵗ(Ω₁·(Ω₁+1) + η)` for `σ ∈ Tᵗ` below the right side. -/
theorem rd_sq_lt_1 {σ η : Ordinal.{0}} (hσ : σ ∈ Tset τ) (hσΩ : σ < Om1) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (hσv : σ < vt τ (Om1 * (Om1 * 1 + 1) + η)) :
    vt τ (Om1 * Om1 + σ) < vt τ (Om1 * (Om1 * 1 + 1) + η) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have h1T : (1 : Ordinal.{0}) ∈ Tset τ := mem_T_of_le hτE hτ1 (Lu.lu_one_lt_E hτE).le
  have h1Ω : (1 : Ordinal.{0}) < Om1 := (Lu.lu_one_lt_E hτE).trans hτ1
  have h0T : (0 : Ordinal.{0}) ∈ Tset τ := mem_T_of_le hτE hτ1 zero_le
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hτE.pos.trans hτ1
  obtain ⟨-, -, -, hτv, -, -, h1v, -⟩ := rd1_facts hτ hτ1 hη hηΩ
  have e1 : Om1 * (Om1 * 1 + 0) + σ = Om1 * Om1 + σ := by rw [mul_one, add_zero]
  have harg : Om1 * (Om1 * 1 + 0) + σ < Om1 * (Om1 * 1 + 1) + η := by
    rw [e1, rd_Om1_eq]
    calc Om1 * Om1 + σ < Om1 * Om1 + Om1 := (add_lt_add_iff_left _).2 hσΩ
      _ ≤ _ := le_self_add
  have := lqVt_lt hτE hτ1 h1T h1Ω h0T h0Ω hσ hσΩ le_rfl h1T h1Ω h1T h1Ω hη hηΩ harg h1v
    (hτE.pos.trans hτv) hσv
  rwa [e1] at this

/-- **Every strongly critical `w ∈ Tᵗ ∩ (τ, Ω₁)` that is not a fixed point of `Γ_` is `ϑᵗ(Ω₁·Ω₁ + σ)`** with
`σ ∈ Tᵗ`, `σ < w`. -/
theorem rd_sq_rep {w : Ordinal.{0}} (hw : SC w) (hτw : τ < w) (hwT : w ∈ Tset τ) (hw1 : w < Om1)
    (hnf : gamma w ≠ w) : ∃ σ, σ ∈ Tset τ ∧ σ < Om1 ∧ σ < w ∧ vt τ (Om1 * Om1 + σ) = w := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  obtain ⟨c, hc⟩ := lq_SC_gamma hτ
  obtain ⟨p, hbase, hpw, hmax⟩ := rb_base_below hτw hnf
  rcases hbase with rfl | ⟨hτp, hpp⟩
  · have hfix : ∀ q, gamma q = q → p < q → w < q := by
      intro q hq hτq
      by_contra hle
      push Not at hle
      have hqw : q < w := lt_of_le_of_ne hle fun e => hnf (e ▸ hq)
      exact absurd (hmax q hq hτq hqw) (not_le.2 hτq)
    obtain ⟨η, hηT, hηΩ, hηw, -, -, he⟩ := lq_sq_rep hτ hτ1 hc hw hτw hwT hw1 hfix
    exact ⟨η, hηT, hηΩ, hηw, he.symm⟩
  · obtain ⟨y, hy⟩ := lq_SC_gamma hw
    have hyw : y < w := by
      refine lt_of_le_of_ne (hy ▸ lq_le_gamma y) fun e => hnf ?_
      rw [← e] at hy ⊢; rw [hy]
    have hnofix : ∀ z, p < z → z < w → z < gamma z := by
      intro z hpz hzw
      by_contra h
      push Not at h
      have hz := le_antisymm h (lq_le_gamma z)
      exact absurd (hmax z hz (hτp.trans hpz) hzw) (not_le.2 hpz)
    have hpy : p < y := gamma_lt_gamma.1 (by rw [hpp, hy]; exact hpw)
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
    have hcond : ∀ σ, σ ≤ δ → p + 1 + σ < gamma (p + 1 + σ) := by
      intro σ hσ
      refine hnofix _ (lt_of_lt_of_le (lt_add_one p) le_self_add) (lt_of_le_of_lt ?_ hyw)
      rw [← hpδy]; exact (add_le_add_iff_left _).2 hσ
    have hT : p + δ ∈ Tset τ := vz_T_down hτE hτ1 hwT hw1 hpδw.le
    refine ⟨p + δ, hT, hpδw.trans hw1, hpδw, ?_⟩
    rw [rb_sq_enum_fix hτ hτ1 hc hpp hτp δ hT (hpδw.trans hw1) hcond, hpδy, hy]

/-- **`ϑᵗ(Ω₁·(Ω₁+1) + η)` is strongly critical.** -/
theorem rd1_SC {η : Ordinal.{0}} (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    SC (vt τ (Om1 * (Om1 * 1 + 1) + η)) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have h1T : (1 : Ordinal.{0}) ∈ Tset τ := mem_T_of_le hτE hτ1 (Lu.lu_one_lt_E hτE).le
  have h1Ω : (1 : Ordinal.{0}) < Om1 := (Lu.lu_one_lt_E hτE).trans hτ1
  have h0T : (0 : Ordinal.{0}) ∈ Tset τ := mem_T_of_le hτE hτ1 zero_le
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hτE.pos.trans hτ1
  obtain ⟨-, -, hvT, hτv, hv1, hvE, -, -⟩ := rd1_facts hτ hτ1 hη hηΩ
  set v := vt τ (Om1 * (Om1 * 1 + 1) + η) with hv
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
    have e0 : Om1 * (Om1 * 0 + a) + lvInd a τ b = Om1 * a + lvInd a τ b := by rw [mul_zero, zero_add]
    have harg : Om1 * (Om1 * 0 + a) + lvInd a τ b < Om1 * (Om1 * 1 + 1) + η := by
      rw [e0, rd_Om1_eq]
      calc Om1 * a + lvInd a τ b < Om1 * a + Om1 := (add_lt_add_iff_left _).2 (hindv.trans hv1)
        _ = Om1 * (a + 1) := by rw [mul_add, mul_one]
        _ ≤ Om1 * Om1 := mul_le_mul_right (Order.add_one_le_of_lt haΩ) Om1
        _ ≤ Om1 * Om1 + Om1 := le_self_add
        _ ≤ _ := le_self_add
    have := lqVt_lt hτE hτ1 h0T h0Ω haT haΩ (hTv _ hindv) (hindv.trans hv1) le_rfl h1T h1Ω h1T h1Ω hη hηΩ
      harg (hτE.pos.trans hτv) hav hindv
    rwa [e0] at this
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

/-- **`ϑᵗ(Ω₁·(Ω₁+1) + η)` is a fixed point of `Γ_`.** -/
theorem rd1_fix {η : Ordinal.{0}} (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    gamma (vt τ (Om1 * (Om1 * 1 + 1) + η)) = vt τ (Om1 * (Om1 * 1 + 1) + η) := by
  obtain ⟨-, -, hvT, hτv, hv1, -, -, -⟩ := rd1_facts hτ hτ1 hη hηΩ
  by_contra hnf
  obtain ⟨σ, hσT, hσΩ, hσv, he⟩ := rd_sq_rep hτ hτ1 (rd1_SC hτ hτ1 hη hηΩ) hτv hvT hv1 hnf
  have := rd_sq_lt_1 hτ hτ1 hσT hσΩ hη hηΩ hσv
  rw [he] at this
  exact lt_irrefl _ this

/-- **Minimality**: `ϑᵗ(Ω₁·(Ω₁+1) + η) ≤ s` for every fixed point `s > τ, η` of `Γ_` above all
`ϑᵗ(Ω₁·(Ω₁+1) + σ)`, `σ < η`. -/
theorem rd1_min {η s : Ordinal.{0}} (hη : η ∈ Tset τ) (hηΩ : η < Om1) (hs : gamma s = s) (hτs : τ < s)
    (hηs : η < s) (hprev : ∀ σ, σ < η → vt τ (Om1 * (Om1 * 1 + 1) + σ) < s) :
    vt τ (Om1 * (Om1 * 1 + 1) + η) ≤ s := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have h1T : (1 : Ordinal.{0}) ∈ Tset τ := mem_T_of_le hτE hτ1 (Lu.lu_one_lt_E hτE).le
  have h1Ω : (1 : Ordinal.{0}) < Om1 := (Lu.lu_one_lt_E hτE).trans hτ1
  have hsSC : SC s := rd_SC_of_fix hs
  obtain ⟨-, -, hvT, -, hv1, -, -, -⟩ := rd1_facts hτ hτ1 hη hηΩ
  by_contra hlt
  push Not at hlt
  obtain ⟨m, -, -, -, hTm, hm1, -⟩ := vz_next hτE hτ1
  have hvm : vt τ (Om1 * (Om1 * 1 + 1) + η) < m := (hTm _ hv1).1 hvT
  have hs1 : s < Om1 := hlt.trans hv1
  have hsT : s ∈ Tset τ := (hTm s hs1).2 (hlt.trans hvm)
  have hsP : Indec s := inE_indec (Gg.gg_SC_eps hsSC)
  have h1s : (1 : Ordinal.{0}) < s := (Lu.lu_one_lt_E hτE).trans hτs
  obtain ⟨ξ, hξT, hξ2, hξs⟩ := vt_rep hτE hτ1 hsT hτs.le hs1 hsP
  have hξlt : ξ < Om1 * (Om1 * 1 + 1) + η :=
    lqLt_of_vt_lt hτE hτ1 hξT hξ2 le_rfl h1T h1Ω h1T h1Ω hη hηΩ (by rw [hξs]; exact h1s)
      (by rw [hξs]; exact h1s) (by rw [hξs]; exact hηs) (by rw [hξs]; exact hlt)
  have hsE : InE s := Gg.gg_SC_eps hsSC
  rcases lt_or_ge ξ (Om1 * Om1) with hξ | hξ
  · rcases lt_or_ge ξ Om1 with hξ1 | hξ1
    · have := (vt_E_iff hτE hτ1 hξT hξ2).1 ⟨by rw [hξs]; exact hτs, by rw [hξs]; exact hsE⟩
      exact absurd this (not_le.2 hξ1)
    · obtain ⟨hq1, hrT, hr1, hdec⟩ := Lu.lu_split hτE hτ1 hξT hξ2 hξ1
      have hqT : ξ / Om1 ∈ Tset τ := lgQuot_mem hτE hτ1 hξT hξ
      have hqΩ : ξ / Om1 < Om1 := (Ordinal.lt_mul_iff_div_lt (Ordinal.omega_pos 1).ne').1 hξ
      exact Mx.mxSC_ne_th hτE hτ1 hq1 hqT hqΩ hrT hr1 hsSC (by rw [hdec, hξs])
  · rcases lt_or_ge ξ (Om1 * Om1 + Om1) with hξ' | hξ'
    · -- `s = ϑᵗ(Ω₁·Ω₁ + σ)` is not a fixed point of `Γ_`
      have hσe : Om1 * Om1 + (ξ - Om1 * Om1) = ξ := Ordinal.add_sub_cancel_of_le hξ
      have hσΩ : ξ - Om1 * Om1 < Om1 := by
        rw [← hσe] at hξ'; exact (add_lt_add_iff_left _).1 hξ'
      have hσT : ξ - Om1 * Om1 ∈ Tset τ :=
        vzRem_T hτE hτ1 hξT hξ2 hσe.symm (dvd_mul_right _ _) hσΩ
      obtain ⟨c, hc⟩ := lq_SC_gamma hτ
      have hle := rb_sq_le hτ hτ1 hc _ hσT hσΩ
      rw [hσe, hξs] at hle
      obtain ⟨-, -, -, -, -, -, hσv⟩ := lq_sq_facts hτ hτ1 hσT hσΩ
      rw [hσe, hξs] at hσv
      have hcs : c < s := (lq_le_gamma c).trans_lt (hc ▸ hτs)
      have h3 : c + (ξ - Om1 * Om1) + 1 < s :=
        hsSC.add_one_lt ((lq_SC_indec hsSC).add_lt hcs hσv)
      have h4 : gamma (c + (ξ - Om1 * Om1) + 1) < s := by
        conv_rhs => rw [← hs]
        exact gamma_lt_gamma.2 h3
      exact absurd hle (not_le.2 h4)
    · have hσe : Om1 * (Om1 * 1 + 1) + (ξ - Om1 * (Om1 * 1 + 1)) = ξ := by
        rw [rd_Om1_eq]; exact Ordinal.add_sub_cancel_of_le hξ'
      have hσ : ξ - Om1 * (Om1 * 1 + 1) < η := by
        rw [← hσe] at hξlt; exact (add_lt_add_iff_left _).1 hξlt
      have h := hprev _ hσ
      rw [hσe, hξs] at h
      exact lt_irrefl _ h

/-- **`ϑᵗ(Ω₁·(Ω₁+1) + η) ≤ F(c + η + 1)`**, `F(c) = τ`. -/
theorem rd1_le {c : Ordinal.{0}} (hc : deriv gamma c = τ) :
    ∀ η, η ∈ Tset τ → η < Om1 → vt τ (Om1 * (Om1 * 1 + 1) + η) ≤ deriv gamma (c + η + 1) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  intro η
  induction η using WellFoundedLT.induction with
  | ind η IH =>
  intro hη hηΩ
  refine rd1_min hτ hτ1 hη hηΩ (rdF_fix _) ?_ ?_ fun σ hσ => ?_
  · rw [← hc]; exact rdF_lt.2 (lt_of_le_of_lt le_self_add (lt_add_one _))
  · exact lt_of_le_of_lt (le_add_self : η ≤ c + η) ((lt_add_one (c + η)).trans_le (rd_le_F _))
  · have hσT : σ ∈ Tset τ := vz_T_down hτE hτ1 hη hηΩ hσ.le
    refine (IH σ hσ hσT (hσ.trans hηΩ)).trans_lt (rdF_lt.2 ?_)
    exact (Order.add_one_le_of_lt ((add_lt_add_iff_left c).2 hσ)).trans_lt (lt_add_one _)

/-- **`ϑᵗ(Ω₁·(Ω₁+1) + σ) < p`** for `σ < p` and every fixed point `p = F(p) > τ` of `F`. -/
theorem rd1_below_fix {c p : Ordinal.{0}} (hc : deriv gamma c = τ) (hp : deriv gamma p = p) (hτp : τ < p)
    (hp1 : p < Om1) {σ : Ordinal.{0}} (hσT : σ ∈ Tset τ) (hσ : σ < p) :
    vt τ (Om1 * (Om1 * 1 + 1) + σ) < p := by
  have hpSC : SC p := hp ▸ rdF_SC p
  have hcp : c < p := (rd_le_F c).trans_lt (hc ▸ hτp)
  have h1 : c + σ + 1 < p := hpSC.add_one_lt ((lq_SC_indec hpSC).add_lt hcp hσ)
  refine (rd1_le hτ hτ1 hc σ hσT (hσ.trans hp1)).trans_lt ?_
  conv_rhs => rw [← hp]
  exact rdF_lt.2 h1

/-- **`ϑᵗ(Ω₁·(Ω₁+1) + η) = F(c + 1 + η)`** for `F(c) = τ` when `1 + σ < F(c+1+σ)` for every `σ ≤ η`. -/
theorem rd1_enum {c : Ordinal.{0}} (hc : deriv gamma c = τ) :
    ∀ η, η ∈ Tset τ → η < Om1 → (∀ σ, σ ≤ η → 1 + σ < deriv gamma (c + 1 + σ)) →
      vt τ (Om1 * (Om1 * 1 + 1) + η) = deriv gamma (c + 1 + η) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  intro η
  induction η using WellFoundedLT.induction with
  | ind η IH =>
  intro hη hηΩ hcond
  have hIH : ∀ σ, σ < η → vt τ (Om1 * (Om1 * 1 + 1) + σ) = deriv gamma (c + 1 + σ) := fun σ hσ =>
    IH σ hσ (vz_T_down hτE hτ1 hη hηΩ hσ.le) (hσ.trans hηΩ) fun σ' hσ' => hcond σ' (hσ'.trans hσ.le)
  apply le_antisymm
  · refine rd1_min hτ hτ1 hη hηΩ (rdF_fix _) ?_ ?_ fun σ hσ => ?_
    · rw [← hc]; exact rdF_lt.2 ((lt_add_one c).trans_le le_self_add)
    · exact (le_add_self).trans_lt (hcond η le_rfl)
    · rw [hIH σ hσ]; exact rdF_lt.2 ((add_lt_add_iff_left _).2 hσ)
  · obtain ⟨-, -, -, hτv, -, -, -, -⟩ := rd1_facts hτ hτ1 hη hηΩ
    obtain ⟨e, he⟩ := rdF_of_fix (rd1_fix hτ hτ1 hη hηΩ)
    rw [← he]
    refine rdF_le.2 (not_lt.1 fun hlt => ?_)
    have hce : c < e := rdF_lt.1 (by rw [hc, he]; exact hτv)
    have hc1 : c + 1 ≤ e := Order.add_one_le_of_lt hce
    have hσe : c + 1 + (e - (c + 1)) = e := Ordinal.add_sub_cancel_of_le hc1
    have hσ : e - (c + 1) < η := by rw [← hσe] at hlt; exact (add_lt_add_iff_left _).1 hlt
    have h1 := rd1_lt hτ hτ1 (vz_T_down hτE hτ1 hη hηΩ hσ.le) hη hηΩ hσ
    rw [hIH _ hσ, hσe, ← he] at h1
    exact lt_irrefl _ h1

/-- **`ϑᵗ(Ω₁·(Ω₁+1) + (p + δ)) = F(p + 1 + δ)`** for a fixed point `p = F(p) > τ` of `F` when `p + 1 + σ <
F(p+1+σ)` for every `σ ≤ δ`. -/
theorem rd1_enum_fix {c p : Ordinal.{0}} (hc : deriv gamma c = τ) (hp : deriv gamma p = p) (hτp : τ < p) :
    ∀ δ, p + δ ∈ Tset τ → p + δ < Om1 → (∀ σ, σ ≤ δ → p + 1 + σ < deriv gamma (p + 1 + σ)) →
      vt τ (Om1 * (Om1 * 1 + 1) + (p + δ)) = deriv gamma (p + 1 + δ) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  intro δ
  induction δ using WellFoundedLT.induction with
  | ind δ IH =>
  intro hT h1 hcond
  have hp1 : p < Om1 := (le_self_add : p ≤ p + δ).trans_lt h1
  have hIH : ∀ δ', δ' < δ → vt τ (Om1 * (Om1 * 1 + 1) + (p + δ')) = deriv gamma (p + 1 + δ') := fun δ' hδ' =>
    IH δ' hδ' (vz_T_down hτE hτ1 hT h1 ((add_le_add_iff_left p).2 hδ'.le))
      (((add_lt_add_iff_left p).2 hδ').trans h1) fun σ hσ => hcond σ (hσ.trans hδ'.le)
  have hpg : p < deriv gamma (p + 1 + δ) := by
    conv_lhs => rw [← hp]
    exact rdF_lt.2 (lt_of_lt_of_le (lt_add_one p) le_self_add)
  apply le_antisymm
  · refine rd1_min hτ hτ1 hT h1 (rdF_fix _) (hτp.trans hpg) ?_ fun σ hσ => ?_
    · have : p + δ ≤ p + 1 + δ := by
        rw [add_assoc]; exact (add_le_add_iff_left p).2 le_add_self
      exact this.trans_lt (hcond δ le_rfl)
    · rcases lt_or_ge σ p with hσp | hσp
      · exact (rd1_below_fix hτ hτ1 hc hp hτp hp1 (vz_T_down hτE hτ1 hT h1 (hσp.le.trans le_self_add))
          hσp).trans hpg
      · have he : p + (σ - p) = σ := Ordinal.add_sub_cancel_of_le hσp
        have hδ' : σ - p < δ := by rw [← he] at hσ; exact (add_lt_add_iff_left p).1 hσ
        rw [← he, hIH _ hδ']
        exact rdF_lt.2 ((add_lt_add_iff_left _).2 hδ')
  · obtain ⟨-, -, -, -, -, -, -, hηv⟩ := rd1_facts hτ hτ1 hT h1
    obtain ⟨e, he⟩ := rdF_of_fix (rd1_fix hτ hτ1 hT h1)
    rw [← he]
    refine rdF_le.2 (not_lt.1 fun hlt => ?_)
    have hpe : p < e := by
      refine rdF_lt.1 ?_
      rw [hp, he]; exact (le_self_add : p ≤ p + δ).trans_lt hηv
    have hp1e : p + 1 ≤ e := Order.add_one_le_of_lt hpe
    have hσe : p + 1 + (e - (p + 1)) = e := Ordinal.add_sub_cancel_of_le hp1e
    have hσ : e - (p + 1) < δ := by rw [← hσe] at hlt; exact (add_lt_add_iff_left _).1 hlt
    have hT' : p + (e - (p + 1)) ∈ Tset τ := vz_T_down hτE hτ1 hT h1 ((add_le_add_iff_left p).2 hσ.le)
    have h2 := rd1_lt hτ hτ1 hT' hT h1 ((add_lt_add_iff_left p).2 hσ)
    rw [hIH _ hσ, hσe, ← he] at h2
    exact lt_irrefl _ h2

/-- **`ζᵗ = logend(η)`** at `ϑᵗ(Ω₁·(Ω₁+1) + η)` under the condition of `rd1_enum`. -/
theorem rd1_zeta {c η : Ordinal.{0}} (hc : deriv gamma c = τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (hcond : ∀ σ, σ ≤ η → 1 + σ < deriv gamma (c + 1 + σ)) :
    lqZeta τ (Om1 * (Om1 * 1 + 1)) η = lg η := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have hen : ∀ σ, σ ≤ η → vt τ (Om1 * (Om1 * 1 + 1) + σ) = deriv gamma (c + 1 + σ) := fun σ hσ =>
    rd1_enum hτ hτ1 hc σ (vz_T_down hτE hτ1 hη hηΩ hσ) (hσ.trans_lt hηΩ) fun σ' hσ' => hcond σ' (hσ'.trans hσ)
  unfold lqZeta
  rcases eq_or_ne η 0 with rfl | hη0
  · rw [if_neg (fun ⟨σ, hσ, _⟩ => absurd hσ (not_lt.2 zero_le))]
    unfold lg; simp
  rw [if_pos]
  rcases zero_or_succ_or_isSuccLimit η with h0 | ⟨σ, rfl⟩ | hlim
  · exact absurd h0 hη0
  · refine ⟨σ, Order.lt_succ σ, ?_⟩
    rw [hen σ (Order.le_succ σ), Order.succ_eq_add_one]
    exact (rdF_SC _).add_one_lt ((le_add_self).trans_lt (hcond σ (Order.le_succ σ)))
  · have hηg : η < deriv gamma (c + 1 + η) := (le_add_self).trans_lt (hcond η le_rfl)
    obtain ⟨x, hx, hηx⟩ := ((isNormal_deriv gamma).lt_iff_exists_lt (isSuccLimit_add _ hlim)).1 hηg
    rcases lt_or_ge x (c + 1) with hxc | hxc
    · refine ⟨0, hlim.bot_lt, ?_⟩
      rw [hen 0 zero_le, add_zero]
      exact hηx.trans (rdF_lt.2 hxc)
    · have hσe : c + 1 + (x - (c + 1)) = x := Ordinal.add_sub_cancel_of_le hxc
      have hσ : x - (c + 1) < η := by rw [← hσe] at hx; exact (add_lt_add_iff_left _).1 hx
      refine ⟨x - (c + 1), hσ, ?_⟩
      rw [hen _ hσ.le, hσe]
      exact hηx

/-- **`ζᵗ = 0` at a fixed point `p = F(p) > τ` of `F`.** -/
theorem rd1_zeta_fix {c p : Ordinal.{0}} (hc : deriv gamma c = τ) (hp : deriv gamma p = p) (hτp : τ < p)
    (hpT : p ∈ Tset τ) (hp1 : p < Om1) : lqZeta τ (Om1 * (Om1 * 1 + 1)) p = 0 := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  unfold lqZeta
  rw [if_neg]
  rintro ⟨σ, hσ, hlt⟩
  exact absurd hlt (not_lt.2 (rd1_below_fix hτ hτ1 hc hp hτp hp1 (vz_T_down hτE hτ1 hpT hp1 hσ.le) hσ).le)

/-- **`ζᵗ = logend(p + δ)`** for `δ ≠ 0` under the condition of `rd1_enum_fix`. -/
theorem rd1_zeta_fix_add {c p δ : Ordinal.{0}} (hc : deriv gamma c = τ) (hp : deriv gamma p = p) (hτp : τ < p)
    (hδ0 : δ ≠ 0) (hT : p + δ ∈ Tset τ) (h1 : p + δ < Om1)
    (hcond : ∀ σ, σ ≤ δ → p + 1 + σ < deriv gamma (p + 1 + σ)) :
    lqZeta τ (Om1 * (Om1 * 1 + 1)) (p + δ) = lg (p + δ) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have hen : ∀ δ', δ' ≤ δ → vt τ (Om1 * (Om1 * 1 + 1) + (p + δ')) = deriv gamma (p + 1 + δ') := fun δ' hδ' =>
    rd1_enum_fix hτ hτ1 hc hp hτp δ' (vz_T_down hτE hτ1 hT h1 ((add_le_add_iff_left p).2 hδ'))
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
    exact hle.trans_lt ((rdF_SC _).add_one_lt (hcond δ0 (Order.le_succ δ0)))
  · have hlim' : IsSuccLimit (p + 1 + δ) := isSuccLimit_add _ hlim
    have hpδ : p + δ < deriv gamma (p + 1 + δ) := by
      have : p + δ ≤ p + 1 + δ := by rw [add_assoc]; exact (add_le_add_iff_left p).2 le_add_self
      exact this.trans_lt (hcond δ le_rfl)
    obtain ⟨x, hx, hpx⟩ := ((isNormal_deriv gamma).lt_iff_exists_lt hlim').1 hpδ
    rcases lt_or_ge x (p + 1) with hxp | hxp
    · exfalso
      have : deriv gamma x ≤ p := by
        conv_rhs => rw [← hp]
        exact rdF_le.2 (Order.lt_add_one_iff.1 hxp)
      exact absurd (hpx.trans_le this) (not_lt.2 le_self_add)
    · have hσe : p + 1 + (x - (p + 1)) = x := Ordinal.add_sub_cancel_of_le hxp
      have hσ : x - (p + 1) < δ := by rw [← hσe] at hx; exact (add_lt_add_iff_left _).1 hx
      refine ⟨p + (x - (p + 1)), (add_lt_add_iff_left p).2 hσ, ?_⟩
      rw [hen _ hσ.le, hσe]
      exact hpx

/-- **`lhᵗ(x) = x·x + x + x + ζᵗ_x`** for `x = ϑᵗ(Ω₁·(Ω₁+1) + η)`, `ζᵗ_x = lqZeta τ (Ω₁·(Ω₁+1)) η`; also as an
`R₁⁺`-reach. -/
theorem rd1_lh {η : Ordinal.{0}} (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    IsLh1 (vt τ (Om1 * (Om1 * 1 + 1) + η))
        (vt τ (Om1 * (Om1 * 1 + 1) + η) * vt τ (Om1 * (Om1 * 1 + 1) + η) + vt τ (Om1 * (Om1 * 1 + 1) + η) +
          vt τ (Om1 * (Om1 * 1 + 1) + η) + lqZeta τ (Om1 * (Om1 * 1 + 1)) η) ∧
      lhT τ (vt τ (Om1 * (Om1 * 1 + 1) + η)) =
        vt τ (Om1 * (Om1 * 1 + 1) + η) * vt τ (Om1 * (Om1 * 1 + 1) + η) + vt τ (Om1 * (Om1 * 1 + 1) + η) +
          vt τ (Om1 * (Om1 * 1 + 1) + η) + lqZeta τ (Om1 * (Om1 * 1 + 1)) η := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have h1T : (1 : Ordinal.{0}) ∈ Tset τ := mem_T_of_le hτE hτ1 (Lu.lu_one_lt_E hτE).le
  have h1Ω : (1 : Ordinal.{0}) < Om1 := (Lu.lu_one_lt_E hτE).trans hτ1
  have h := lq_lh hτE hτ1 le_rfl h1T h1Ω h1T h1Ω hη hηΩ
  obtain ⟨-, -, -, -, -, hvE, -, -⟩ := rd1_facts hτ hτ1 hη hηΩ
  set v := vt τ (Om1 * (Om1 * 1 + 1) + η) with hv
  have e2 : lqL v 1 1 = v * v + v + v := by
    unfold lqL
    rw [log_one_right, opow_zero, mul_one, add_zero, mul_one, lq_lg_mul_two hvE, mul_add_one,
      Ordinal.add_sub_cancel]
  rw [e2] at h
  exact h

end Base

end Googology.Trans.PoR.InaccPsi.R2.Rd
