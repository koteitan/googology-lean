import Googology.Trans.PoR.InaccPsi.R2.CitedVz
import Googology.Trans.PoR.InaccPsi.R2.EvZ
import Googology.Trans.PoR.InaccPsi.R2.EvR

/-!
# `ϑᵗ(Ω₁·2) = ζ_{τ+1}`, its base change, its `R₁⁺`-reach `ζ_{τ+1}·3`, and the `R₁⁺`-test `α ≤₁ α·3`

From the cited facts of `R2.CitedVz` ([W07a] Def 3.22, Convention 4.1, Lemma 3.30; [W07b] Def 4.1) and of
`R2.CitedEv`:

* `vzOm1_mul_T` (`Ω₁·n + η ∈ Tᵗ`), `vzOm1_two_T`, `vzOm1_two_lt`;
* `vz_vt_two_eq` (**`ϑᵗ(Ω₁·2) = evZ τ`**, the least fixed point of `ε` above `τ`: every `ϑᵗ(Ω₁ + η) = ε_{τ+1+η}`
  with `η < ϑᵗ(Ω₁·2)` lies below it, so it is a fixed point; an `ε`-fixed point strictly below it would be some
  `ϑᵗ(Ω₁ + η)`, `η ∈ Tᵗ` by Convention 4.1);
* `vz_evZ_T` (`evZ τ ∈ Tᵗ ∩ Ω₁`), `vz_evZ_lt_ltInf` (**`evZ τ` lies strictly below every `<₁ ∞`-point above
  `τ`**), `vz_evZ_lt_ups`;
* `vz_lh_evZ` (**`lh(ζ_{τ+1}) = ζ_{τ+1}·3`** in `R₁⁺`, [W07b] Theorem 5.3 with `vzLhT_fix`);
* `vz_pi_evZ` (**`ζ_{ρ+1} ∈ Tᵖ[σ]` and `π_{σ,ρ}(ζ_{ρ+1}) = ζ_{σ+1}`**, `pi_vt_two` at `Ω₁ + Ω₁`);
* `vz_le1R_three` (**`α ≤₁ α·3` in `R₁⁺` and an `ε`-number `b < α` give `evZ b ≤ α`**: `α ≤₁ α·2 + z'` for every
  `z' < α`, so `α ≥ ε_{b+ω^{z'}}` (`le1R_ge_evAg`), `α ≥ ε_{b+α}`, a fixed point of `ε` above `b`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-- `Ω₁·n + η ∈ Tᵗ` for `η ∈ Tᵗ` (`vzT_add` from `Ω₁ ∈ Tᵗ`). -/
theorem vzOm1_mul_T {τ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hη : η ∈ Tset τ) :
    ∀ n : ℕ, Om1 * (n : Ordinal.{0}) + η ∈ Tset τ
  | 0 => by rw [Nat.cast_zero, mul_zero, zero_add]; exact hη
  | n + 1 => by
    have := vzT_add hτ hτ1 (Om1_T hτ hτ1) (vzOm1_mul_T hτ hτ1 hη n)
    rwa [← add_assoc, ← mul_one_add, ← Nat.cast_one, ← Nat.cast_add, add_comm 1 n] at this

theorem vzOm1_mul_lt {η : Ordinal.{0}} (hη : η < Om1) (n : ℕ) : Om1 * (n : Ordinal.{0}) + η < OmTwo := by
  have hP := isPrincipal_add_omega 2
  have hO : Om1 < OmTwo := Om1_lt_OmTwo
  induction n with
  | zero => rw [Nat.cast_zero, mul_zero, zero_add]; exact hη.trans hO
  | succ n ih =>
    rw [Nat.cast_succ, mul_add_one, add_assoc]
    have h1 : Om1 * (n : Ordinal.{0}) < OmTwo := lt_of_le_of_lt le_self_add ih
    exact hP h1 (hP hO (hη.trans hO))

theorem vz_two_cast : Om1 * ((2 : ℕ) : Ordinal.{0}) + 0 = Om1 * 2 := by
  rw [add_zero]; norm_num

theorem vz_one_cast (η : Ordinal.{0}) : Om1 * ((1 : ℕ) : Ordinal.{0}) + η = Om1 + η := by
  rw [Nat.cast_one, mul_one]

theorem vzOm1_two_T {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) : Om1 * 2 ∈ Tset τ := by
  rw [← vz_two_cast]; exact vzOm1_mul_T hτ hτ1 (mem_T_of_le hτ hτ1 zero_le) 2

theorem vzOm1_two_lt : Om1 * 2 < OmTwo := by
  rw [← vz_two_cast]; exact vzOm1_mul_lt (Ordinal.omega_pos 1) 2

/-- The facts on the term `ϑᵗ(Ω₁·2)`: in `Tᵗ`, an `ε`-number in `(τ, Ω₁)`. -/
theorem vz_two_facts {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) :
    vt τ (Om1 * 2) ∈ Tset τ ∧ τ < vt τ (Om1 * 2) ∧ vt τ (Om1 * 2) < Om1 ∧ InE (vt τ (Om1 * 2)) ∧
      Indec (vt τ (Om1 * 2)) := by
  have hγT := vzOm1_two_T hτ hτ1
  obtain ⟨hvT, -, hv1, hvP, -⟩ := vt_memTwo hτ hτ1 hγT vzOm1_two_lt
  have hE := (vt_E_iff hτ hτ1 hγT vzOm1_two_lt).2 (by rw [mul_two_eq]; exact le_self_add)
  exact ⟨hvT, hE.1, hv1, hE.2, hvP⟩

/-- **`ϑᵗ(Ω₁·2) = evZ τ`** (`ζ_{τ+1}` for an `ε`-number `τ` that is not a fixed point of `ε`). -/
theorem vz_vt_two_eq {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) : vt τ (Om1 * 2) = evZ τ := by
  obtain ⟨haT, hτa, ha1, haE, -⟩ := vz_two_facts hτ hτ1
  set a := vt τ (Om1 * 2) with hadef
  obtain ⟨m, -, -, -, hTm, -⟩ := T_next (Or.inr hτ) hτ1
  have ham : a < m := (hTm a ha1).1 haT
  have h0T : (0 : Ordinal.{0}) ∈ Tset τ := mem_T_of_le hτ hτ1 zero_le
  refine le_antisymm ?_ ?_
  · -- `a ≤ evZ τ`: a fixed point strictly below `a` would be some `ϑᵗ(Ω₁ + η)`
    by_contra hlt
    push Not at hlt
    set z := evZ τ with hz
    have hz1 : z < Om1 := hlt.trans ha1
    have hzT : z ∈ Tset τ := (hTm z hz1).2 (hlt.trans ham)
    obtain ⟨ξ, hξT, hξ2, hξz⟩ := vt_rep hτ hτ1 hzT (lt_evZ τ).le hz1 (inE_indec (evZ_E τ))
    have hΩξ : Om1 ≤ ξ :=
      (vt_E_iff hτ hτ1 hξT hξ2).1 ⟨by rw [hξz]; exact lt_evZ τ, by rw [hξz]; exact evZ_E τ⟩
    have hξγ : ξ < Om1 * 2 := by
      have := vzLt_of_vt_lt (n := 2) hτ hτ1 hξT hξ2 h0T (hτ.pos.trans hτ1)
        (by rw [hξz]; exact (evZ_E τ).pos)
        (by rw [vz_two_cast, hξz]; exact hlt)
      rwa [vz_two_cast] at this
    set η := ξ - Om1 with hηdef
    have hξe : Om1 + η = ξ := Ordinal.add_sub_cancel_of_le hΩξ
    have hη1 : η < Om1 := by
      have : Om1 + η < Om1 + Om1 := by rw [hξe, ← mul_two_eq]; exact hξγ
      exact (add_lt_add_iff_left Om1).1 this
    have hηT : η ∈ Tset τ := vzRem_T hτ hτ1 hξT hξ2 hξe.symm (dvd_refl _) hη1
    rcases lt_or_ge η z with hηz | hzη
    · have hv := vt_Om1_add_evZ hτ hτ1 hηz
      rw [hξe, hξz] at hv
      have : evA τ (1 + η) < z := evA_lt_evZ hτ (add_lt_evZ (lt_of_lt_of_le one_lt_omega0
        (omega0_lt_inE (evZ_E τ)).le) hηz)
      rw [← hv] at this
      exact lt_irrefl _ this
    · have := lt_vt_Om1_add hτ hτ1 hηT hη1
      rw [hξe, hξz] at this
      exact absurd hzη (not_le.2 this)
  · -- `evZ τ ≤ a`: every `ε_{τ+(1+η)}`, `η < a`, is below `a`, so `a` is a fixed point of `ε`
    by_contra hlt
    push Not at hlt
    have key : ∀ η, η < a → evA τ (1 + η) < a := by
      intro η hη
      have hη1 : η < Om1 := hη.trans ha1
      have hηT : η ∈ Tset τ := (hTm η hη1).2 (hη.trans ham)
      rw [← vt_Om1_add_evZ hτ hτ1 (hη.trans hlt), ← vz_one_cast, hadef, ← vz_two_cast]
      refine vzVt_lt hτ hτ1 hηT hη1 h0T (hτ.pos.trans hτ1) ?_ (by rw [vz_two_cast]; exact hη)
      rw [vz_one_cast, vz_two_cast, mul_two_eq]
      exact (add_lt_add_iff_left Om1).2 hη1
    have hle : evA τ a ≤ a := by
      rw [evA_lim τ (ev_isSuccLimit_of_inE haE)]
      exact Ordinal.iSup_le (fun b => (evA_le_iff.2 le_add_self).trans (key b.1 b.2).le)
    have hfix : Ordinal.epsilon a = a := by
      refine le_antisymm ?_ (right_le_veblen 1 a)
      exact ((veblen_le_veblen_iff_right (o := 1)).2 le_add_self).trans hle
    exact absurd (evZ_le hτa hfix) (not_le.2 hlt)

/-- **`evZ τ ∈ Tᵗ ∩ Ω₁`.** -/
theorem vz_evZ_T {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) : evZ τ ∈ Tset τ ∧ evZ τ < Om1 := by
  obtain ⟨haT, -, ha1, -, -⟩ := vz_two_facts hτ hτ1
  rw [← vz_vt_two_eq hτ hτ1]; exact ⟨haT, ha1⟩

/-- **`evZ τ` lies strictly below every `<₁ ∞`-point above `τ`.** -/
theorem vz_evZ_lt_ltInf {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {u : Ordinal.{0}} (hτu : τ < u)
    (hu : LtInf1 u) : evZ τ < u := by
  obtain ⟨m, -, -, hmin, hTm, -⟩ := T_next (Or.inr hτ) hτ1
  obtain ⟨hT, h1⟩ := vz_evZ_T hτ hτ1
  exact lt_of_lt_of_le ((hTm _ h1).1 hT) (hmin u hτu hu)

theorem vz_evZ_lt_ups {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {u : Ordinal.{0}} (hτu : τ < u)
    (hu : UpsPt u) : evZ τ < u :=
  vz_evZ_lt_ltInf hτ hτ1 hτu hu.2

theorem vz_mul_three (a : Ordinal.{0}) : a * ((2 + 1 : ℕ) : Ordinal.{0}) = a * 2 + a := by
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, mul_add_one]

/-- **The `R₁⁺`-reach of `ζ_{τ+1}`**: `lh(evZ τ) = evZ τ·3` ([W07b] Theorem 5.3 through `lh_eq_lhT`, with the
cited value `vzLhT_fix` of [W07b] Def 4.1 at `ϑᵗ(Ω₁·2)`). -/
theorem vz_lh_evZ {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) : IsLh1 (evZ τ) (evZ τ * 2 + evZ τ) := by
  obtain ⟨haT, hτa, ha1, -, haP⟩ := vz_two_facts hτ hτ1
  have h := lh_eq_lhT (Or.inr hτ) hτ1 haT hτa ha1 haP
  have hl := vzLhT_fix (n := 2) (η := 0) hτ hτ1 (by norm_num) (mem_T_of_le hτ hτ1 zero_le)
    (hτ.pos.trans hτ1) (fun σ hσ => absurd hσ (not_lt.2 zero_le))
  rw [vz_two_cast, vz_mul_three] at hl
  rw [hl, vz_vt_two_eq hτ hτ1] at h
  exact h

/-- **`ζ_{ρ+1} ∈ Tᵖ[σ]` and `π_{σ,ρ}(ζ_{ρ+1}) = ζ_{σ+1}`.** -/
theorem vz_pi_evZ {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) : evZ ρ ∈ TB ρ σ ∧ pi σ ρ (evZ ρ) = evZ σ := by
  have hρE := hB.2.1
  have hσE := hB.1
  have hρ1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨hOT, hpO⟩ := pi_Om1 hB
  obtain ⟨hγTB, hpγ⟩ := pi_add hB hOT hOT
  rw [← mul_two_eq] at hγTB hpγ
  rw [hpO, ← mul_two_eq] at hpγ
  obtain ⟨hvT, -, -, -, hvP⟩ := vt_memTwo hρE hρ1 hγTB.1 vzOm1_two_lt
  rw [← vz_vt_two_eq hρE hρ1, ← vz_vt_two_eq hσE hσ1]
  refine ⟨⟨hvT, by rw [hvP]; exact hγTB.2⟩, ?_⟩
  rw [pi_vt_two hB hγTB vzOm1_two_lt, hpγ]

/-- **The `R₁⁺`-test `α ≤₁ α·3`**: if `α ≤₁ α·2 + α` in `R₁⁺` and `b < α` is an `ε`-number, then `evZ b ≤ α`. -/
theorem vz_le1R_three {a b : Ordinal.{0}} (hb : InE b) (hba : b < a) (h : le1R a (a * 2 + a)) :
    evZ b ≤ a := by
  have ha0 : 0 < a := lt_of_le_of_lt zero_le hba
  have haE : InE a := le1R_two_add_E ha0 h
  have hz : ∀ z, z < a → evA b (ω ^ z) ≤ a := by
    intro z hz
    have hz' : le1R a (a * 2 + z) :=
      le1R_of_le ((show a ≤ a * 2 by rw [mul_two_eq]; exact le_self_add).trans le_self_add)
        (add_le_add_right hz.le _) h
    exact le1R_ge_evAg z a b hb hba hz hz'
  have hle : evA b a ≤ a := by
    rw [evA_lim b (ev_isSuccLimit_of_inE haE)]
    refine Ordinal.iSup_le (fun c => ?_)
    exact (evA_le_iff.2 (right_le_opow c.1 one_lt_omega0)).trans (hz c.1 c.2)
  have hfix : Ordinal.epsilon a = a := by
    refine le_antisymm ?_ (right_le_veblen 1 a)
    exact ((veblen_le_veblen_iff_right (o := 1)).2 le_add_self).trans hle
  exact evZ_le hba hfix

end Googology.Trans.PoR.InaccPsi.R2
