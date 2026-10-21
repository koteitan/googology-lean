import Googology.Trans.PoR.InaccPsi.R2.LqLh
import Googology.Trans.PoR.InaccPsi.R2.MxLev

/-!
# The Γ-level `Ω₁·Ω₁`: `ϑᵗ(Ω₁·Ω₁ + η)` is the `η`-th strongly critical ordinal above `τ` (no fixed point of `Γ`)

For a strongly critical base `τ < Ω₁` (`Γ_ = Ordinal.gamma`, the enumeration of the strongly critical ordinals,
`τ = Γ_c`), from `R2.CitedLq` and `R2.CitedLg` (Lemma 3.30 at `Ω₁·Ω₁ + η`), `vt_rep`, `vt_E_iff`, `lgQuot_mem` and the
level lemma `lvPhLev`:

* `lq_sq_facts`, `lq_sq_lt` (**`η ↦ ϑᵗ(Ω₁·Ω₁ + η)` is strictly increasing**);
* `lq_sq_SC` (**`ϑᵗ(Ω₁·Ω₁ + η)` is strongly critical**: every `φ_a(b)`, `a, b` below it, is a fixed point, `≤ τ`, or
  `ϑᵗ(Ω₁·a + ind(b))` by `lvPhLev` (a strongly critical level `a` is raised to `a + 1`), which is below by
  `lgVt_lt_low`);
* `lq_sq_min` (**`ϑᵗ(Ω₁·Ω₁ + η)` is below every strongly critical `s > τ, η` above all `ϑᵗ(Ω₁·Ω₁ + σ)`, `σ < η`**: by
  `vt_rep` and `lgLt_of_vt_lt`, `s = ϑᵗ(ξ)` with `ξ < Ω₁·Ω₁ + η`; `ξ < Ω₁` is not an `ε`-number, `Ω₁ ≤ ξ < Ω₁·Ω₁` is
  excluded by `Mx.mxSC_ne_th`, and `ξ = Ω₁·Ω₁ + σ` by the hypothesis);
* `lq_sq_enum` (**`ϑᵗ(Ω₁·Ω₁ + η) = Γ_{c+1+η}`** when `1 + σ < Γ_{c+1+σ}` for every `σ ≤ η`, i.e. no fixed point of
  `Γ_` in `(τ, Γ_{c+1+η}]`);
* `lq_sq_zeta` (**`ζᵗ = lqZeta τ (Ω₁·Ω₁) η = logend(η)`** there), `lq_sq_lhT` (**`lhᵗ(Γ_{c+1+η}) = x·x + x +
  logend(η)`**, `x = Γ_{c+1+η}`);
* `lq_sq_rep` (**every strongly critical `x ∈ (τ, Ω₁) ∩ Tᵗ` with no fixed point of `Γ_` in `(τ, x]` is `Γ_{c+1+η} =
  ϑᵗ(Ω₁·Ω₁ + η)` with `η < x`** and the condition of `lq_sq_enum`).

No new axiom beyond `R2.CitedLq` and `R2.CitedLg`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Lq

open Ordinal Order Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2

/-! ## The strongly critical ordinals -/

theorem lq_gamma_SC (o : Ordinal.{0}) : SC (gamma o) := Mw.mwSC_of_fix gamma_pos (veblen_gamma_zero o)

theorem lq_SC_gamma {x : Ordinal.{0}} (hx : SC x) : ∃ e, gamma e = x := mem_range_gamma.2 hx.veblen_zero

theorem lq_le_gamma (o : Ordinal.{0}) : o ≤ gamma o := isNormal_gamma.strictMono.le_apply

section Base

variable {τ : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1)
include hτ hτ1

theorem lq_sq_facts {η : Ordinal.{0}} (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    Om1 * Om1 + η ∈ Tset τ ∧ Om1 * Om1 + η < OmTwo ∧ vt τ (Om1 * Om1 + η) ∈ Tset τ ∧
    τ < vt τ (Om1 * Om1 + η) ∧ vt τ (Om1 * Om1 + η) < Om1 ∧ InE (vt τ (Om1 * Om1 + η)) ∧
    η < vt τ (Om1 * Om1 + η) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have h1T : (1 : Ordinal.{0}) ∈ Tset τ := mem_T_of_le hτE hτ1 (Lu.lu_one_lt_E hτE).le
  have h0T : (0 : Ordinal.{0}) ∈ Tset τ := mem_T_of_le hτE hτ1 zero_le
  have h1Ω : (1 : Ordinal.{0}) < Om1 := (Lu.lu_one_lt_E hτE).trans hτ1
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hτE.pos.trans hτ1
  have h := lq_facts hτE hτ1 le_rfl h1T h1Ω h0T h0Ω hη hηΩ
  have e1 : Om1 * (Om1 * 1 + 0) = Om1 * Om1 := by rw [mul_one, add_zero]
  rw [e1] at h
  obtain ⟨a, b, c, d, e, f, -, -, -, g⟩ := h
  exact ⟨a, b, c, d, e, f, g⟩

/-- **`η ↦ ϑᵗ(Ω₁·Ω₁ + η)` is strictly increasing** on `Tᵗ ∩ Ω₁`. -/
theorem lq_sq_lt {σ η : Ordinal.{0}} (hσ : σ ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1) (h : σ < η) :
    vt τ (Om1 * Om1 + σ) < vt τ (Om1 * Om1 + η) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have h1T : (1 : Ordinal.{0}) ∈ Tset τ := mem_T_of_le hτE hτ1 (Lu.lu_one_lt_E hτE).le
  have h0T : (0 : Ordinal.{0}) ∈ Tset τ := mem_T_of_le hτE hτ1 zero_le
  have h1Ω : (1 : Ordinal.{0}) < Om1 := (Lu.lu_one_lt_E hτE).trans hτ1
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hτE.pos.trans hτ1
  obtain ⟨-, -, -, hτv, -, -, hηv⟩ := lq_sq_facts hτ hτ1 hη hηΩ
  have e1 : ∀ z, Om1 * (Om1 * 1 + 0) + z = Om1 * Om1 + z := fun z => by rw [mul_one, add_zero]
  have := lqVt_lt hτE hτ1 h1T h1Ω h0T h0Ω hσ (h.trans hηΩ) le_rfl h1T h1Ω h0T h0Ω hη hηΩ
    (by rw [e1, e1]; exact (add_lt_add_iff_left _).2 h)
    (by rw [e1]; exact (Lu.lu_one_lt_E hτE).trans hτv) (by rw [e1]; exact hτE.pos.trans hτv)
    (by rw [e1]; exact h.trans hηv)
  rwa [e1, e1] at this

/-- **`ϑᵗ(Ω₁·Ω₁ + η)` is strongly critical.** -/
theorem lq_sq_SC {η : Ordinal.{0}} (hη : η ∈ Tset τ) (hηΩ : η < Om1) : SC (vt τ (Om1 * Om1 + η)) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  obtain ⟨-, -, hvT, hτv, hv1, hvE, hηv⟩ := lq_sq_facts hτ hτ1 hη hηΩ
  set v := vt τ (Om1 * Om1 + η) with hv
  have hvE' : ω ^ v = v := hvE
  have hvl : IsSuccLimit v := ev_isSuccLimit_of_inE hvE
  have hTv : ∀ z, z < v → z ∈ Tset τ := fun z hz => vz_T_down hτE hτ1 hvT hv1 hz.le
  -- a level that is not strongly critical above `τ`
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
    exact lgVt_lt_low hτE hτ1 haT haΩ (hTv _ hindv) (hindv.trans hv1) hη hηΩ hav hindv
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

/-- **Minimality**: `ϑᵗ(Ω₁·Ω₁ + η) ≤ s` for every strongly critical `s > τ, η` above all `ϑᵗ(Ω₁·Ω₁ + σ)`, `σ < η`. -/
theorem lq_sq_min {η s : Ordinal.{0}} (hη : η ∈ Tset τ) (hηΩ : η < Om1) (hs : SC s) (hτs : τ < s)
    (hηs : η < s) (hprev : ∀ σ, σ < η → vt τ (Om1 * Om1 + σ) < s) : vt τ (Om1 * Om1 + η) ≤ s := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  obtain ⟨-, -, hvT, -, hv1, -, -⟩ := lq_sq_facts hτ hτ1 hη hηΩ
  by_contra hlt
  push Not at hlt
  obtain ⟨m, -, -, -, hTm, hm1, -⟩ := vz_next hτE hτ1
  have hvm : vt τ (Om1 * Om1 + η) < m := (hTm _ hv1).1 hvT
  have hs1 : s < Om1 := hlt.trans hv1
  have hsT : s ∈ Tset τ := (hTm s hs1).2 (hlt.trans hvm)
  have hsP : Indec s := inE_indec (Gg.gg_SC_eps hs)
  obtain ⟨ξ, hξT, hξ2, hξs⟩ := vt_rep hτE hτ1 hsT hτs.le hs1 hsP
  have hξlt : ξ < Om1 * Om1 + η := lgLt_of_vt_lt hτE hτ1 hξT hξ2 hη hηΩ (by rw [hξs]; exact hηs)
    (by rw [hξs]; exact hlt)
  have hsE : InE s := Gg.gg_SC_eps hs
  rcases lt_or_ge ξ (Om1 * Om1) with hξ | hξ
  · rcases lt_or_ge ξ Om1 with hξ1 | hξ1
    · have := (vt_E_iff hτE hτ1 hξT hξ2).1 ⟨by rw [hξs]; exact hτs, by rw [hξs]; exact hsE⟩
      exact absurd this (not_le.2 hξ1)
    · obtain ⟨hq1, hrT, hr1, hdec⟩ := Lu.lu_split hτE hτ1 hξT hξ2 hξ1
      have hqT : ξ / Om1 ∈ Tset τ := lgQuot_mem hτE hτ1 hξT hξ
      have hqΩ : ξ / Om1 < Om1 := (Ordinal.lt_mul_iff_div_lt (Ordinal.omega_pos 1).ne').1 hξ
      exact Mx.mxSC_ne_th hτE hτ1 hq1 hqT hqΩ hrT hr1 hs (by rw [hdec, hξs])
  · have hσe : Om1 * Om1 + (ξ - Om1 * Om1) = ξ := Ordinal.add_sub_cancel_of_le hξ
    have hσ : ξ - Om1 * Om1 < η := by
      rw [← hσe] at hξlt; exact (add_lt_add_iff_left _).1 hξlt
    have h := hprev _ hσ
    rw [hσe, hξs] at h
    exact lt_irrefl _ h

/-- **`ϑᵗ(Ω₁·Ω₁ + η) = Γ_{c+1+η}`** for `τ = Γ_c` when `1 + σ < Γ_{c+1+σ}` for every `σ ≤ η` (no fixed point of `Γ_`
in `(τ, Γ_{c+1+η}]`). -/
theorem lq_sq_enum {c : Ordinal.{0}} (hc : gamma c = τ) :
    ∀ η, η ∈ Tset τ → η < Om1 → (∀ σ, σ ≤ η → 1 + σ < gamma (c + 1 + σ)) →
      vt τ (Om1 * Om1 + η) = gamma (c + 1 + η) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  intro η
  induction η using WellFoundedLT.induction with
  | ind η IH =>
  intro hη hηΩ hcond
  have hIH : ∀ σ, σ < η → vt τ (Om1 * Om1 + σ) = gamma (c + 1 + σ) := fun σ hσ =>
    IH σ hσ (vz_T_down hτE hτ1 hη hηΩ hσ.le) (hσ.trans hηΩ) fun σ' hσ' => hcond σ' (hσ'.trans hσ.le)
  apply le_antisymm
  · refine lq_sq_min hτ hτ1 hη hηΩ (lq_gamma_SC _) ?_ ?_ fun σ hσ => ?_
    · rw [← hc]; exact gamma_lt_gamma.2 ((lt_add_one c).trans_le le_self_add)
    · exact (le_add_self).trans_lt (hcond η le_rfl)
    · rw [hIH σ hσ]; exact gamma_lt_gamma.2 ((add_lt_add_iff_left _).2 hσ)
  · obtain ⟨-, -, -, hτv, -, -, -⟩ := lq_sq_facts hτ hτ1 hη hηΩ
    obtain ⟨e, he⟩ := lq_SC_gamma (lq_sq_SC hτ hτ1 hη hηΩ)
    rw [← he]
    refine gamma_le_gamma.2 (not_lt.1 fun hlt => ?_)
    have hce : c < e := gamma_lt_gamma.1 (by rw [hc, he]; exact hτv)
    have hc1 : c + 1 ≤ e := Order.add_one_le_of_lt hce
    have hσe : c + 1 + (e - (c + 1)) = e := Ordinal.add_sub_cancel_of_le hc1
    have hσ : e - (c + 1) < η := by rw [← hσe] at hlt; exact (add_lt_add_iff_left _).1 hlt
    have h1 := lq_sq_lt hτ hτ1 (vz_T_down hτE hτ1 hη hηΩ hσ.le) hη hηΩ hσ
    rw [hIH _ hσ, hσe, ← he] at h1
    exact lt_irrefl _ h1

/-- **`ζᵗ = logend(η)`** at `ϑᵗ(Ω₁·Ω₁ + η)` under the condition of `lq_sq_enum`. -/
theorem lq_sq_zeta {c η : Ordinal.{0}} (hc : gamma c = τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (hcond : ∀ σ, σ ≤ η → 1 + σ < gamma (c + 1 + σ)) : lqZeta τ (Om1 * Om1) η = lg η := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have hen : ∀ σ, σ ≤ η → vt τ (Om1 * Om1 + σ) = gamma (c + 1 + σ) := fun σ hσ =>
    lq_sq_enum hτ hτ1 hc σ (vz_T_down hτE hτ1 hη hηΩ hσ) (hσ.trans_lt hηΩ) fun σ' hσ' => hcond σ' (hσ'.trans hσ)
  unfold lqZeta
  rcases eq_or_ne η 0 with rfl | hη0
  · rw [if_neg (fun ⟨σ, hσ, _⟩ => absurd hσ (not_lt.2 zero_le))]
    unfold lg; simp
  rw [if_pos]
  rcases zero_or_succ_or_isSuccLimit η with h0 | ⟨σ, rfl⟩ | hlim
  · exact absurd h0 hη0
  · refine ⟨σ, Order.lt_succ σ, ?_⟩
    rw [hen σ (Order.le_succ σ), Order.succ_eq_add_one]
    exact (lq_gamma_SC _).add_one_lt ((le_add_self).trans_lt (hcond σ (Order.le_succ σ)))
  · have hηg : η < gamma (c + 1 + η) := (le_add_self).trans_lt (hcond η le_rfl)
    obtain ⟨x, hx, hηx⟩ := (isNormal_gamma.lt_iff_exists_lt (isSuccLimit_add _ hlim)).1 hηg
    rcases lt_or_ge x (c + 1) with hxc | hxc
    · refine ⟨0, hlim.bot_lt, ?_⟩
      rw [hen 0 zero_le, add_zero]
      exact hηx.trans (gamma_lt_gamma.2 hxc)
    · have hσe : c + 1 + (x - (c + 1)) = x := Ordinal.add_sub_cancel_of_le hxc
      have hσ : x - (c + 1) < η := by rw [← hσe] at hx; exact (add_lt_add_iff_left _).1 hx
      refine ⟨x - (c + 1), hσ, ?_⟩
      rw [hen _ hσ.le, hσe]
      exact hηx

/-- **`lhᵗ(Γ_{c+1+η}) = x·x + x + logend(η)`**, `x = Γ_{c+1+η} = ϑᵗ(Ω₁·Ω₁ + η)`, under the condition of
`lq_sq_enum`; also as an `R₁⁺`-reach. -/
theorem lq_sq_lhT {c η : Ordinal.{0}} (hc : gamma c = τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (hcond : ∀ σ, σ ≤ η → 1 + σ < gamma (c + 1 + σ)) :
    IsLh1 (gamma (c + 1 + η)) (gamma (c + 1 + η) * gamma (c + 1 + η) + gamma (c + 1 + η) + lg η) ∧
      lhT τ (gamma (c + 1 + η)) = gamma (c + 1 + η) * gamma (c + 1 + η) + gamma (c + 1 + η) + lg η := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have h := lq_lh_sq hτE hτ1 hη hηΩ
  rw [lq_sq_zeta hτ hτ1 hc hη hηΩ hcond, lq_sq_enum hτ hτ1 hc η hη hηΩ hcond] at h
  exact h

/-- **Every strongly critical `x ∈ (τ, Ω₁) ∩ Tᵗ` with no fixed point of `Γ_` in `(τ, x]` is `Γ_{c+1+η} =
ϑᵗ(Ω₁·Ω₁ + η)`** with `η < x` and the condition of `lq_sq_enum`. -/
theorem lq_sq_rep {c x : Ordinal.{0}} (hc : gamma c = τ) (hx : SC x) (hτx : τ < x) (hxT : x ∈ Tset τ)
    (hx1 : x < Om1) (hfix : ∀ q, gamma q = q → τ < q → x < q) :
    ∃ η, η ∈ Tset τ ∧ η < Om1 ∧ η < x ∧ (∀ σ, σ ≤ η → 1 + σ < gamma (c + 1 + σ)) ∧
      x = gamma (c + 1 + η) ∧ x = vt τ (Om1 * Om1 + η) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  obtain ⟨e, he⟩ := lq_SC_gamma hx
  have hce : c < e := gamma_lt_gamma.1 (by rw [hc, he]; exact hτx)
  have hc1 : c + 1 ≤ e := Order.add_one_le_of_lt hce
  set η := e - (c + 1) with hηdef
  have hηe : c + 1 + η = e := Ordinal.add_sub_cancel_of_le hc1
  have hηx : η < x := by
    have h1 : η ≤ e := by rw [← hηe]; exact le_add_self
    have h2 : e ≤ x := by rw [← he]; exact lq_le_gamma e
    refine lt_of_le_of_ne (h1.trans h2) fun h => ?_
    have heq : e = x := le_antisymm h2 (h ▸ h1)
    have hgx : gamma x = x := by rw [heq] at he; exact he
    exact lt_irrefl x (hfix x hgx hτx)
  have hηΩ : η < Om1 := hηx.trans hx1
  have hηT : η ∈ Tset τ := vz_T_down hτE hτ1 hxT hx1 hηx.le
  have hcond : ∀ σ, σ ≤ η → 1 + σ < gamma (c + 1 + σ) := by
    intro σ hσ
    by_contra hle
    push Not at hle
    have h1 : gamma (c + 1 + σ) ≤ c + 1 + σ := by
      calc gamma (c + 1 + σ) ≤ 1 + σ := hle
        _ ≤ c + (1 + σ) := le_add_self
        _ = c + 1 + σ := (add_assoc _ _ _).symm
    have hq : gamma (c + 1 + σ) = c + 1 + σ := le_antisymm h1 (lq_le_gamma _)
    have hτq : τ < c + 1 + σ := by
      rw [← hq, ← hc]; exact gamma_lt_gamma.2 ((lt_add_one c).trans_le le_self_add)
    have hqx : c + 1 + σ ≤ x := by
      rw [← hq, ← he, ← hηe]; exact gamma_le_gamma.2 ((add_le_add_iff_left _).2 hσ)
    exact absurd (hfix _ hq hτq) (not_lt.2 hqx)
  refine ⟨η, hηT, hηΩ, hηx, hcond, by rw [hηe, he], ?_⟩
  rw [lq_sq_enum hτ hτ1 hc η hηT hηΩ hcond, hηe, he]

end Base

end Googology.Trans.PoR.InaccPsi.R2.Lq
