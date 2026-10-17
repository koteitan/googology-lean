import Googology.Trans.PoR.InaccPsi.R2.CitedXt
import Googology.Trans.PoR.InaccPsi.R2.VzW

/-!
# Lemma EXACT for `B(x)` and for `ω^E·γ`, and the lexicographic order of `b·γ + a`

`B(x) = VzB x` is the least value of `φ(ω, ·)` above `x` (`vzB_omega`), `B(x) = ϑˣ(Ω₁·ω)` (`vz_vt_w_eq`).

* `xt_B_lt_ups` (**`B(x)` lies below every `υ`-point above `x`**: `lh(B) = B·ω` in `R₁⁺`), `xt_B_E`, `xt_B_lt_Om1`;
* `xtPiB` (**Lemma EXACT for `B`**: `B(ρ) ∈ Tᵖ[σ]`, `π_{σ,ρ}(B(ρ)) = B(σ)`, from [W07a] Def 5.1 fourth clause
  (`pi_vt_two`) and the cited `π_{σ,ρ}(Ω₁·ω) = Ω₁·ω` of `R2.CitedXt`);
* `xtPi_mul_nat`, `xtPiOpowMul` (**`π_{σ,ρ}(ω^E·γ) = ω^{π(E)}·γ`** for a constant `γ < σ`);
* `xt1_lex_lt`, `xt1_lex_le` (for `a, a' < b`: `b·γ + a < b·γ' + a'` iff `γ < γ'` or `γ = γ'`, `a < a'`).

The only new axiom is `xtOm1w_TB` (`R2.CitedXt`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Xt

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 VzTm

/-- **`B(x)` lies below every `υ`-point above `x`.** -/
theorem xt_B_lt_ups {x u : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hxu : x < u) (hu : UpsPt u) :
    VzB x < u := by
  rcases (vzB_le_next hx hx1 hxu hu.2).lt_or_eq with h | h
  · exact h
  · exfalso
    have hl := vz_lh_B hx hx1
    rw [h] at hl
    have := hl.2 (u * ω + 1) (hu.2 _ ((le_mul_left u omega0_pos).trans le_self_add))
    exact absurd this (not_le.2 (lt_add_one _))

theorem xt_B_E {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : InE (VzB x) :=
  vz_omega_E (vzB_omega hx hx1).1

theorem xt_B_lt_Om1 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : VzB x < Om1 := by
  rw [← vz_vt_w_eq hx hx1]; exact (vz_w_facts hx hx1).2.2.1

/-! ## Lemma EXACT for `B` and `B·γ` -/

/-- **Lemma EXACT for `B`**: `B(ρ) ∈ Tᵖ[σ]` and `π_{σ,ρ}(B(ρ)) = B(σ)`. -/
theorem xtPiB {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) : VzB ρ ∈ TB ρ σ ∧ pi σ ρ (VzB ρ) = VzB σ := by
  obtain ⟨hOT, hpO⟩ := xtOm1w_TB hB
  have hρE := hB.2.1
  have hρ1 := hB.2.2.2
  have hσ1 := hB.2.2.1.trans hρ1
  obtain ⟨hvT, -, -, -, hvP⟩ := vt_memTwo hρE hρ1 hOT.1 vzOm1w_lt
  rw [← vz_vt_w_eq hρE hρ1, ← vz_vt_w_eq hB.1 hσ1]
  refine ⟨⟨hvT, by rw [hvP]; exact hOT.2⟩, ?_⟩
  rw [pi_vt_two hB hOT vzOm1w_lt, hpO]

theorem xtPi_mul_nat {σ ρ x : Ordinal.{0}} (hB : Bases σ ρ) (hx : x ∈ TB ρ σ) :
    ∀ n : ℕ, x * (n : Ordinal.{0}) ∈ TB ρ σ ∧ pi σ ρ (x * (n : Ordinal.{0})) = pi σ ρ x * (n : Ordinal.{0})
  | 0 => by
    simp only [Nat.cast_zero, mul_zero]
    exact ⟨mem_TB_of_lt hB hB.1.pos, pi_lt hB hB.1.pos⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := xtPi_mul_nat hB hx n
    obtain ⟨h3, h4⟩ := pi_add hB h1 hx
    rw [Nat.cast_succ, mul_add_one, mul_add_one]
    exact ⟨h3, by rw [h4, h2]⟩

/-- **Lemma EXACT for `ω^E·γ`** (`γ < σ` a constant, `E ∈ Tᵖ[σ] ∩ Ω₁` with `π_{σ,ρ}(E) = E'`):
`π_{σ,ρ}(ω^E·γ) = ω^{E'}·γ` (`ω^E·γ = ω^{E+g}·n + ω^E·m` for `γ = ω^g·n + m`; `pi_opowZ`, `pi_add`). -/
theorem xtPiOpowMul {σ ρ E E' : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ)
    (hE : E ∈ TB ρ σ) (hpE : pi σ ρ E = E') (hE1 : E < Om1) :
    ∀ γ, γ < σ → ω ^ E * γ ∈ TB ρ σ ∧ pi σ ρ (ω ^ E * γ) = ω ^ E' * γ := by
  have hσ1 := hB.2.2.1.trans hB.2.2.2
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγσ
  rcases eq_or_ne γ 0 with rfl | hγ0
  · simp only [mul_zero]
    exact ⟨mem_TB_of_lt hB hB.1.pos, pi_lt hB hB.1.pos⟩
  set g := log ω γ with hg
  set m := γ % ω ^ g with hm
  have hω0 : ω ^ g ≠ 0 := (opow_pos g omega0_pos).ne'
  have hdm : ω ^ g * (γ / ω ^ g) + m = γ := div_add_mod γ (ω ^ g)
  have hmlt : m < ω ^ g := mod_lt γ hω0
  have hgle : ω ^ g ≤ γ := opow_log_le_self ω hγ0
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt γ one_lt_omega0)
  rw [hn] at hdm
  have hgγ : g ≤ γ := log_le_self ω γ
  have hgσ : g < σ := lt_of_le_of_lt hgγ hγσ
  have hmγ : m < γ := lt_of_lt_of_le hmlt hgle
  have hdec : ∀ t : Ordinal.{0}, ω ^ t * γ = ω ^ (t + g) * (n : Ordinal.{0}) + ω ^ t * m := by
    intro t
    conv_lhs => rw [← hdm, mul_add, ← mul_assoc, ← opow_add]
  obtain ⟨h1, h2⟩ := pi_add hB hE (mem_TB_of_lt hB hgσ)
  rw [hpE, pi_lt hB hgσ] at h2
  have hEg1 : E + g < Om1 := Om1_add_lt hE1 (hgσ.trans hσ1)
  obtain ⟨h3, h4⟩ := pi_opowZ hσ hρ hB h1 hEg1
  rw [h2] at h4
  obtain ⟨h5, h6⟩ := xtPi_mul_nat hB h3 n
  rw [h4] at h6
  obtain ⟨h7, h8⟩ := IH m hmγ (hmγ.trans hγσ)
  obtain ⟨h9, h10⟩ := pi_add hB h5 h7
  rw [hdec E, hdec E']
  exact ⟨h9, by rw [h10, h6, h8]⟩

/-! ## The order of the values -/

/-- **The values are ordered lexicographically**: for `a, a' < b`, `b·γ + a < b·γ' + a'` iff `γ < γ'` or
`γ = γ'` and `a < a'`. -/
theorem xt1_lex_lt {b a a' γ γ' : Ordinal.{0}} (ha : a < b) (ha' : a' < b) :
    b * γ + a < b * γ' + a' ↔ γ < γ' ∨ (γ = γ' ∧ a < a') := by
  have key : ∀ {c c' e e' : Ordinal.{0}}, e < b → c < c' → b * c + e < b * c' + e' := by
    intro c c' e e' he hc
    calc b * c + e < b * c + b := (add_lt_add_iff_left _).2 he
      _ = b * (c + 1) := (mul_add_one b c).symm
      _ ≤ b * c' := mul_le_mul_right (add_one_le_of_lt hc) b
      _ ≤ b * c' + e' := le_self_add
  constructor
  · intro h
    rcases lt_trichotomy γ γ' with hγ | rfl | hγ
    · exact Or.inl hγ
    · exact Or.inr ⟨rfl, (add_lt_add_iff_left _).1 h⟩
    · exact absurd (key ha' hγ) (not_lt.2 h.le)
  · rintro (h | ⟨rfl, h⟩)
    · exact key ha h
    · exact (add_lt_add_iff_left _).2 h

theorem xt1_lex_le {b a a' γ γ' : Ordinal.{0}} (ha : a < b) (ha' : a' < b) :
    b * γ + a ≤ b * γ' + a' ↔ γ < γ' ∨ (γ = γ' ∧ a ≤ a') := by
  rw [← not_lt, xt1_lex_lt ha' ha]
  constructor
  · intro h
    rcases lt_trichotomy γ γ' with hγ | rfl | hγ
    · exact Or.inl hγ
    · exact Or.inr ⟨rfl, not_lt.1 fun h' => h (Or.inr ⟨rfl, h'⟩)⟩
    · exact absurd (Or.inl hγ) h
  · rintro (h | ⟨rfl, h⟩) (h' | ⟨e, h'⟩)
    · exact absurd h (lt_asymm h')
    · exact absurd e h.ne'
    · exact lt_irrefl _ h'
    · exact absurd h' (not_lt.2 h)

end Googology.Trans.PoR.InaccPsi.R2.Xt
