import Googology.Trans.PoR.InaccPsi.R2.RbPsi

/-!
# `ϑᵗ(Ω₁·Ω₁ + p + δ) = Γ_{p+1+δ}` past a fixed point `p` of `Γ_`

For a strongly critical base `τ = Γ_c < Ω₁` (`Γ_ = Ordinal.gamma`), from `Lq.lq_sq_min`, `Lq.lq_sq_SC`, `Lq.lq_sq_lt`
(Lemma 3.30 at `Ω₁·Ω₁ + η`, cited in `R2.CitedLq` and `R2.CitedLg`):

* `rb_sq_le` (**`ϑᵗ(Ω₁·Ω₁ + η) ≤ Γ_{c+η+1}`**), `rb_sq_below_fix` (**`ϑᵗ(Ω₁·Ω₁ + σ) < p`** for `σ < p` and every fixed
  point `p = Γ_p > τ`);
* `rb_sq_enum_fix` (**`ϑᵗ(Ω₁·Ω₁ + (p + δ)) = Γ_{p+1+δ}`** for a fixed point `p = Γ_p > τ` when `p + 1 + σ <
  Γ_{p+1+σ}` for every `σ ≤ δ`, i.e. no fixed point of `Γ_` in `(p, Γ_{p+1+δ}]`);
* `rb_zeta_fix` (**`ζᵗ = lqZeta τ (Ω₁·Ω₁) p = 0`** at a fixed point `p`), `rb_zeta_fix_add`
  (**`ζᵗ = logend(p + δ)`** for `δ ≠ 0` under the condition of `rb_sq_enum_fix`).

No new axiom beyond `R2.CitedLq` and `R2.CitedLg`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rb

open Ordinal Order Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Lq

section Base

variable {τ : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1)
include hτ hτ1

/-- **`ϑᵗ(Ω₁·Ω₁ + η) ≤ Γ_{c+η+1}`**, `τ = Γ_c`. -/
theorem rb_sq_le {c : Ordinal.{0}} (hc : gamma c = τ) :
    ∀ η, η ∈ Tset τ → η < Om1 → vt τ (Om1 * Om1 + η) ≤ gamma (c + η + 1) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  intro η
  induction η using WellFoundedLT.induction with
  | ind η IH =>
  intro hη hηΩ
  refine lq_sq_min hτ hτ1 hη hηΩ (lq_gamma_SC _) ?_ ?_ fun σ hσ => ?_
  · rw [← hc]; exact gamma_lt_gamma.2 (lt_of_le_of_lt le_self_add (lt_add_one _))
  · exact lt_of_le_of_lt (le_add_self : η ≤ c + η) ((lt_add_one (c + η)).trans_le (lq_le_gamma _))
  · have hσT : σ ∈ Tset τ := vz_T_down hτE hτ1 hη hηΩ hσ.le
    refine (IH σ hσ hσT (hσ.trans hηΩ)).trans_lt (gamma_lt_gamma.2 ?_)
    exact (Order.add_one_le_of_lt ((add_lt_add_iff_left c).2 hσ)).trans_lt (lt_add_one _)

/-- **`ϑᵗ(Ω₁·Ω₁ + σ) < p`** for `σ < p` and every fixed point `p = Γ_p > τ` below `Ω₁`. -/
theorem rb_sq_below_fix {c p : Ordinal.{0}} (hc : gamma c = τ) (hp : gamma p = p) (hτp : τ < p) (hp1 : p < Om1)
    {σ : Ordinal.{0}} (hσT : σ ∈ Tset τ) (hσ : σ < p) : vt τ (Om1 * Om1 + σ) < p := by
  have hpSC : SC p := hp ▸ lq_gamma_SC p
  have hcp : c < p := (lq_le_gamma c).trans_lt (hc ▸ hτp)
  have h1 : c + σ + 1 < p := hpSC.add_one_lt ((lq_SC_indec hpSC).add_lt hcp hσ)
  refine (rb_sq_le hτ hτ1 hc σ hσT (hσ.trans hp1)).trans_lt ?_
  conv_rhs => rw [← hp]
  exact gamma_lt_gamma.2 h1

/-- **`ϑᵗ(Ω₁·Ω₁ + (p + δ)) = Γ_{p+1+δ}`** for a fixed point `p = Γ_p > τ` when `p + 1 + σ < Γ_{p+1+σ}` for every
`σ ≤ δ`. -/
theorem rb_sq_enum_fix {c p : Ordinal.{0}} (hc : gamma c = τ) (hp : gamma p = p) (hτp : τ < p) :
    ∀ δ, p + δ ∈ Tset τ → p + δ < Om1 → (∀ σ, σ ≤ δ → p + 1 + σ < gamma (p + 1 + σ)) →
      vt τ (Om1 * Om1 + (p + δ)) = gamma (p + 1 + δ) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  intro δ
  induction δ using WellFoundedLT.induction with
  | ind δ IH =>
  intro hT h1 hcond
  have hp1 : p < Om1 := (le_self_add : p ≤ p + δ).trans_lt h1
  have hIH : ∀ δ', δ' < δ → vt τ (Om1 * Om1 + (p + δ')) = gamma (p + 1 + δ') := fun δ' hδ' =>
    IH δ' hδ' (vz_T_down hτE hτ1 hT h1 ((add_le_add_iff_left p).2 hδ'.le))
      (((add_lt_add_iff_left p).2 hδ').trans h1) fun σ hσ => hcond σ (hσ.trans hδ'.le)
  have hpg : p < gamma (p + 1 + δ) := by
    conv_lhs => rw [← hp]
    exact gamma_lt_gamma.2 (lt_of_lt_of_le (lt_add_one p) le_self_add)
  apply le_antisymm
  · refine lq_sq_min hτ hτ1 hT h1 (lq_gamma_SC _) (hτp.trans hpg) ?_ fun σ hσ => ?_
    · have : p + δ ≤ p + 1 + δ := by
        rw [add_assoc]; exact (add_le_add_iff_left p).2 le_add_self
      exact this.trans_lt (hcond δ le_rfl)
    · rcases lt_or_ge σ p with hσp | hσp
      · exact (rb_sq_below_fix hτ hτ1 hc hp hτp hp1 (vz_T_down hτE hτ1 hT h1 (hσp.le.trans le_self_add))
          hσp).trans hpg
      · have he : p + (σ - p) = σ := Ordinal.add_sub_cancel_of_le hσp
        have hδ' : σ - p < δ := by rw [← he] at hσ; exact (add_lt_add_iff_left p).1 hσ
        rw [← he, hIH _ hδ']
        exact gamma_lt_gamma.2 ((add_lt_add_iff_left _).2 hδ')
  · obtain ⟨-, -, -, -, -, -, hηv⟩ := lq_sq_facts hτ hτ1 hT h1
    obtain ⟨e, he⟩ := lq_SC_gamma (lq_sq_SC hτ hτ1 hT h1)
    rw [← he]
    refine gamma_le_gamma.2 (not_lt.1 fun hlt => ?_)
    have hpe : p < e := by
      refine gamma_lt_gamma.1 ?_
      rw [hp, he]; exact (le_self_add : p ≤ p + δ).trans_lt hηv
    have hp1e : p + 1 ≤ e := Order.add_one_le_of_lt hpe
    have hσe : p + 1 + (e - (p + 1)) = e := Ordinal.add_sub_cancel_of_le hp1e
    have hσ : e - (p + 1) < δ := by rw [← hσe] at hlt; exact (add_lt_add_iff_left _).1 hlt
    have hT' : p + (e - (p + 1)) ∈ Tset τ := vz_T_down hτE hτ1 hT h1 ((add_le_add_iff_left p).2 hσ.le)
    have h2 := lq_sq_lt hτ hτ1 hT' hT h1 ((add_lt_add_iff_left p).2 hσ)
    rw [hIH _ hσ, hσe, ← he] at h2
    exact lt_irrefl _ h2

/-- **`ζᵗ = 0` at a fixed point `p = Γ_p > τ`.** -/
theorem rb_zeta_fix {c p : Ordinal.{0}} (hc : gamma c = τ) (hp : gamma p = p) (hτp : τ < p) (hpT : p ∈ Tset τ)
    (hp1 : p < Om1) : lqZeta τ (Om1 * Om1) p = 0 := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  unfold lqZeta
  rw [if_neg]
  rintro ⟨σ, hσ, hlt⟩
  exact absurd hlt (not_lt.2 (rb_sq_below_fix hτ hτ1 hc hp hτp hp1 (vz_T_down hτE hτ1 hpT hp1 hσ.le) hσ).le)

/-- **`ζᵗ = logend(p + δ)`** for `δ ≠ 0` under the condition of `rb_sq_enum_fix`. -/
theorem rb_zeta_fix_add {c p δ : Ordinal.{0}} (hc : gamma c = τ) (hp : gamma p = p) (hτp : τ < p) (hδ0 : δ ≠ 0)
    (hT : p + δ ∈ Tset τ) (h1 : p + δ < Om1) (hcond : ∀ σ, σ ≤ δ → p + 1 + σ < gamma (p + 1 + σ)) :
    lqZeta τ (Om1 * Om1) (p + δ) = lg (p + δ) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have hen : ∀ δ', δ' ≤ δ → vt τ (Om1 * Om1 + (p + δ')) = gamma (p + 1 + δ') := fun δ' hδ' =>
    rb_sq_enum_fix hτ hτ1 hc hp hτp δ' (vz_T_down hτE hτ1 hT h1 ((add_le_add_iff_left p).2 hδ'))
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
    exact hle.trans_lt ((lq_gamma_SC _).add_one_lt (hcond δ0 (Order.le_succ δ0)))
  · have hlim' : IsSuccLimit (p + 1 + δ) := isSuccLimit_add _ hlim
    have hpδ : p + δ < gamma (p + 1 + δ) := by
      have : p + δ ≤ p + 1 + δ := by rw [add_assoc]; exact (add_le_add_iff_left p).2 le_add_self
      exact this.trans_lt (hcond δ le_rfl)
    obtain ⟨x, hx, hpx⟩ := (isNormal_gamma.lt_iff_exists_lt hlim').1 hpδ
    rcases lt_or_ge x (p + 1) with hxp | hxp
    · exfalso
      have : gamma x ≤ p := by
        conv_rhs => rw [← hp]
        exact gamma_le_gamma.2 (Order.lt_add_one_iff.1 hxp)
      exact absurd (hpx.trans_le this) (not_lt.2 le_self_add)
    · have hσe : p + 1 + (x - (p + 1)) = x := Ordinal.add_sub_cancel_of_le hxp
      have hσ : x - (p + 1) < δ := by rw [← hσe] at hx; exact (add_lt_add_iff_left _).1 hx
      refine ⟨p + (x - (p + 1)), (add_lt_add_iff_left p).2 hσ, ?_⟩
      rw [hen _ hσ.le, hσe]
      exact hpx

end Base

end Googology.Trans.PoR.InaccPsi.R2.Rb
