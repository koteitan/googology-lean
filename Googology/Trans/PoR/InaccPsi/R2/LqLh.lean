import Googology.Trans.PoR.InaccPsi.R2.CitedLq
import Googology.Trans.PoR.InaccPsi.R2.LuTh

/-!
# The terms `ϑᵗ(Ω₁·(Ω₁·γ + β) + η)` (`γ ≥ 1`) and their exact `R₁⁺`-reach

For a base `τ ∈ E ∩ Ω₁`, from the cited facts of `R2.CitedLq` ([W07a] Lemma 3.30, Def 3.22 at the arguments
`Ω₁·(Ω₁·γ + β) + η`, [W07b] Def 4.1 there) with [W07b] Theorem 2.2 and Theorem 5.3 (`le1R_thm22`, `le1R_two_iff`,
`lh_eq_lhT`):

* `lq_arg_lt`, `lq_OmOm_le`, `lq_facts` (**`ϑᵗ(Ω₁·(Ω₁·γ + β) + η)` is an `ε`-number in `(τ, Ω₁) ∩ Tᵗ` above `γ`, `β`,
  `η`**);
* `lq_lg_add` (`logend(x + y) = logend(y)` when `ω^{logend(y)+1} ∣ x`), `lq_lg_mul_two` (`logend(α·2) = α`);
* `lqL` (`lqL α γ β = α·α·ω^g + logend(α·2 + g) + (α·(α·γ + β) − α·α·ω^g)`, `g = log_ω γ`), `lq_lh` (**`lh(ϑᵗ(Ω₁·(Ω₁·γ
  + β) + η)) = lqL(α, γ, β) + ζᵗ_α`**, and `lhᵗ(α)` is that value), `lq_lh_sq` (**`lh(ϑᵗ(Ω₁·Ω₁ + η)) = α·α + α +
  ζᵗ_α`**, `α = ϑᵗ(Ω₁·Ω₁ + η)`, `ζᵗ_α = lqZeta τ (Ω₁·Ω₁) η`).

No new axiom beyond `R2.CitedLq`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Lq

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2

/-! ## Arithmetic -/

/-- `logend(x + y) = logend(y)` when `y ≠ 0` and `ω^{logend(y)+1}` divides `x`. -/
theorem lq_lg_add {x y : Ordinal.{0}} (hy : y ≠ 0) (hx : ω ^ (lg y + 1) ∣ x) : lg (x + y) = lg y := by
  have hxy : x + y ≠ 0 := fun h => hy (Ordinal.add_eq_zero_iff.1 h).2
  have hd : ω ^ lg y ∣ x := (pow_dvd_pow_of_le' (le_self_add)).trans hx
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    have h1 : ω ^ (lg y + 1) ∣ x + y := ((le_lg_iff hxy _).1 (Order.add_one_le_of_lt hlt))
    have h2 : ω ^ (lg y + 1) ∣ y := (Ordinal.dvd_add_iff hx).1 h1
    have h3 := (le_lg_iff hy _).2 h2
    exact absurd h3 (not_le.2 (lt_add_one _))
  · exact (le_lg_iff hxy _).2 ((Ordinal.dvd_add_iff hd).2 (lg_dvd hy))
where
  pow_dvd_pow_of_le' {a b : Ordinal.{0}} (h : a ≤ b) : ω ^ a ∣ ω ^ b := by
    rw [← Ordinal.add_sub_cancel_of_le h, opow_add]; exact dvd_mul_right _ _

/-- `logend(α·2) = α` for an `ε`-number `α`. -/
theorem lq_lg_mul_two {α : Ordinal.{0}} (hα : InE α) : lg (α * 2) = α := by
  have hE : ω ^ α = α := hα
  have h0 : α * 2 ≠ 0 := (mul_pos hα.pos (by norm_num)).ne'
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    have h1 : ω ^ (α + 1) ∣ α * 2 := (le_lg_iff h0 _).1 (Order.add_one_le_of_lt hlt)
    obtain ⟨k, hk⟩ := h1
    rcases eq_or_ne k 0 with rfl | hk0
    · rw [mul_zero] at hk; exact h0 hk
    · have hle : ω ^ (α + 1) ≤ α * 2 := by
        rw [hk]; exact le_mul_left _ (pos_iff_ne_zero.2 hk0)
      rw [opow_add, hE, opow_one] at hle
      have : α * 2 < α * ω := (mul_lt_mul_iff_right₀ hα.pos).2 (by exact_mod_cast natCast_lt_omega0 2)
      exact absurd hle (not_le.2 this)
  · exact (le_lg_iff h0 _).2 (by rw [hE]; exact dvd_mul_right _ _)

section Base

variable {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1)
include hτ hτ1

omit hτ hτ1 in
theorem lq_arg_lt {γ β η : Ordinal.{0}} (hγΩ : γ < Om1) (hβΩ : β < Om1) (hηΩ : η < Om1) :
    Om1 * (Om1 * γ + β) + η < OmTwo := by
  have hO : Om1 < OmTwo := Om1_lt_OmTwo
  have h1 : Om1 * γ + β < OmTwo := Lu.luOm1_mul_lt hγΩ hβΩ
  have h2 : Om1 * (Om1 * γ + β) < OmTwo := isPrincipal_mul_omega 2 hO h1
  exact isPrincipal_add_omega 2 h2 (hηΩ.trans hO)

omit hτ hτ1 in
theorem lq_OmOm_le {γ β η : Ordinal.{0}} (hγ1 : 1 ≤ γ) : Om1 * Om1 ≤ Om1 * (Om1 * γ + β) + η := by
  calc Om1 * Om1 = Om1 * (Om1 * 1) := by rw [mul_one]
    _ ≤ Om1 * (Om1 * γ) := mul_le_mul_right (mul_le_mul_right hγ1 Om1) Om1
    _ ≤ Om1 * (Om1 * γ + β) := mul_le_mul_right le_self_add Om1
    _ ≤ _ := le_self_add

omit hτ hτ1 in
theorem lq_Om1_le {γ β η : Ordinal.{0}} (hγ1 : 1 ≤ γ) : Om1 ≤ Om1 * (Om1 * γ + β) + η := by
  refine le_trans ?_ (lq_OmOm_le hγ1)
  calc Om1 = Om1 * 1 := (mul_one _).symm
    _ ≤ Om1 * Om1 := mul_le_mul_right (one_le_iff_pos.2 (Ordinal.omega_pos 1)) Om1

/-- **The facts on a term `ϑᵗ(Ω₁·(Ω₁·γ + β) + η)`** (`γ ≥ 1`, `γ, β, η ∈ Tᵗ ∩ Ω₁`). -/
theorem lq_facts {γ β η : Ordinal.{0}} (hγ1 : 1 ≤ γ) (hγ : γ ∈ Tset τ) (hγΩ : γ < Om1) (hβ : β ∈ Tset τ)
    (hβΩ : β < Om1) (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    Om1 * (Om1 * γ + β) + η ∈ Tset τ ∧ Om1 * (Om1 * γ + β) + η < OmTwo ∧
    vt τ (Om1 * (Om1 * γ + β) + η) ∈ Tset τ ∧ τ < vt τ (Om1 * (Om1 * γ + β) + η) ∧
    vt τ (Om1 * (Om1 * γ + β) + η) < Om1 ∧ InE (vt τ (Om1 * (Om1 * γ + β) + η)) ∧
    Indec (vt τ (Om1 * (Om1 * γ + β) + η)) ∧ γ < vt τ (Om1 * (Om1 * γ + β) + η) ∧
    β < vt τ (Om1 * (Om1 * γ + β) + η) ∧ η < vt τ (Om1 * (Om1 * γ + β) + η) := by
  have hargT := lqArg_mem hτ hτ1 hγ1 hγ hγΩ hβ hβΩ hη hηΩ
  have harg2 := lq_arg_lt hγΩ hβΩ hηΩ
  obtain ⟨hvT, -, hv1, hvP, -⟩ := vt_memTwo hτ hτ1 hargT harg2
  have hE := (vt_E_iff hτ hτ1 hargT harg2).2 (lq_Om1_le hγ1)
  have hl := lqLevel_lt_vt hτ hτ1 hγ1 hγ hγΩ hβ hβΩ hη hηΩ
  exact ⟨hargT, harg2, hvT, hE.1, hv1, hE.2, hvP, hl.1, hl.2.1, hl.2.2⟩

end Base

/-! ## The exact reach -/

/-- **The reach of a term at the level `Ω₁·(Ω₁·γ + β)`** at `a`: `a·a·ω^g + logend(a·2 + g) + (a·(a·γ + β) − a·a·ω^g)`,
`g = log_ω γ`. -/
noncomputable def lqL (a γ β : Ordinal.{0}) : Ordinal.{0} :=
  a * a * ω ^ log ω γ + lg (a * 2 + log ω γ) + (a * (a * γ + β) - a * a * ω ^ log ω γ)

/-- **`lh(ϑᵗ(Ω₁·(Ω₁·γ + β) + η)) = lqL(α, γ, β) + ζᵗ_α`**, and `lhᵗ(α)` is that value ([W07b] Def 4.1 through
`lqLhT`, Theorem 2.2 through `Lu.lu_lh_opow`, Theorem 5.3 through `lh_eq_lhT`). -/
theorem lq_lh {τ γ β η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hγ1 : 1 ≤ γ) (hγ : γ ∈ Tset τ)
    (hγΩ : γ < Om1) (hβ : β ∈ Tset τ) (hβΩ : β < Om1) (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    IsLh1 (vt τ (Om1 * (Om1 * γ + β) + η))
        (lqL (vt τ (Om1 * (Om1 * γ + β) + η)) γ β + lqZeta τ (Om1 * (Om1 * γ + β)) η) ∧
      lhT τ (vt τ (Om1 * (Om1 * γ + β) + η)) =
        lqL (vt τ (Om1 * (Om1 * γ + β) + η)) γ β + lqZeta τ (Om1 * (Om1 * γ + β)) η := by
  obtain ⟨-, -, hvT, hτv, hv1, hvE, hvP, hγv, hβv, -⟩ := lq_facts hτ hτ1 hγ1 hγ hγΩ hβ hβΩ hη hηΩ
  set a := vt τ (Om1 * (Om1 * γ + β) + η) with ha
  set ζ := lqZeta τ (Om1 * (Om1 * γ + β)) η with hζ
  set g := log ω γ with hg
  have haE : ω ^ a = a := hvE
  have hγ0 : γ ≠ 0 := (lt_of_lt_of_le zero_lt_one hγ1).ne'
  have hgγ : g ≤ γ := log_le_self ω γ
  have hga : g < a := hgγ.trans_lt hγv
  -- `δ = a·a·ω^g = ω^c`, `c = a·2 + g`
  set c := a * 2 + g with hc
  have hδc : a * a * ω ^ g = ω ^ c := by rw [hc, opow_add, mul_two_eq, opow_add, haE]
  have hc0 : c ≠ 0 := (lt_of_lt_of_le (mul_pos hvE.pos (by norm_num)) le_self_add).ne'
  have hca : c < a * a := by
    calc c < a * 2 + a := (add_lt_add_iff_left _).2 hga
      _ = a * 3 := by rw [show (3 : Ordinal.{0}) = 2 + 1 by norm_num, mul_add_one]
      _ < a * ω := (mul_lt_mul_iff_right₀ hvE.pos).2 (by exact_mod_cast natCast_lt_omega0 3)
      _ ≤ a * a := mul_le_mul_right (omega0_lt_inE hvE).le a
  have hcE : c < ω ^ c := by
    refine hca.trans_le ?_
    rw [← hδc]; exact le_mul_of_one_le_right zero_le (one_le_iff_pos.2 (opow_pos _ omega0_pos))
  have hL : IsLh1 (a * a * ω ^ g) (a * a * ω ^ g + lg c) := by rw [hδc]; exact Lu.lu_lh_opow hc0 hcE
  -- `δ ∈ Tᵗ`
  obtain ⟨m, -, -, -, hTm, hm1, hmE⟩ := vz_next hτ hτ1
  have ham : a < m := (hTm a hv1).1 hvT
  have hδm : a * a * ω ^ g < m := by
    have h2 : a * 2 < m := by rw [mul_two_eq]; exact (inE_indec hmE).add_lt ham ham
    rw [hδc]; exact hmE.opow_lt ((inE_indec hmE).add_lt h2 (hga.trans ham))
  have hδ1 : a * a * ω ^ g < Om1 := hδm.trans hm1
  have hδT : a * a * ω ^ g ∈ Tset τ := (hTm _ hδ1).2 hδm
  have haδ : a ≤ a * a * ω ^ g := by
    rw [hδc]
    calc a = ω ^ a := haE.symm
      _ ≤ ω ^ c := opow_le_opow_right omega0_pos ((by rw [mul_two_eq]; exact le_self_add : a ≤ a * 2).trans
        le_self_add)
  have hτδ : τ < a * a * ω ^ g := hτv.trans_le haδ
  have hδP : Indec (a * a * ω ^ g) := by rw [hδc]; exact indec_opow _
  have hlhδ := Lu.lu_lhT_eq hτ hτ1 hδT hτδ hδ1 hδP hL
  -- the value
  have hle : a * a * ω ^ g ≤ a * (a * γ + β) := by
    rw [mul_assoc]
    exact mul_le_mul_right ((mul_le_mul_right (opow_log_le_self ω hγ0) a).trans le_self_add) a
  have e : a * (a * γ + β) + ζ = a * a * ω ^ g + ((a * (a * γ + β) - a * a * ω ^ g) + ζ) := by
    rw [← add_assoc, Ordinal.add_sub_cancel_of_le hle]
  have hlh : lhT τ a = lqL a γ β + ζ := by
    rw [lqLhT hτ hτ1 hγ1 hγ hγΩ hβ hβΩ hη hηΩ, ← ha, ← hg, ← hζ, hlhδ, e, Ordinal.add_sub_cancel]
    unfold lqL
    rw [← hg, ← hc]
    simp only [add_assoc]
  refine ⟨?_, hlh⟩
  rw [← hlh]
  exact lh_eq_lhT (Or.inr hτ) hτ1 hvT hτv hv1 hvP

/-- **`lh(ϑᵗ(Ω₁·Ω₁ + η)) = α·α + α + ζᵗ_α`**, `α = ϑᵗ(Ω₁·Ω₁ + η)`, `ζᵗ_α = lqZeta τ (Ω₁·Ω₁) η`, and `lhᵗ(α)` is that
value. -/
theorem lq_lh_sq {τ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    IsLh1 (vt τ (Om1 * Om1 + η))
        (vt τ (Om1 * Om1 + η) * vt τ (Om1 * Om1 + η) + vt τ (Om1 * Om1 + η) + lqZeta τ (Om1 * Om1) η) ∧
      lhT τ (vt τ (Om1 * Om1 + η)) =
        vt τ (Om1 * Om1 + η) * vt τ (Om1 * Om1 + η) + vt τ (Om1 * Om1 + η) + lqZeta τ (Om1 * Om1) η := by
  have h1T : (1 : Ordinal.{0}) ∈ Tset τ := mem_T_of_le hτ hτ1 (Lu.lu_one_lt_E hτ).le
  have h0T : (0 : Ordinal.{0}) ∈ Tset τ := mem_T_of_le hτ hτ1 zero_le
  have h1Ω : (1 : Ordinal.{0}) < Om1 := (Lu.lu_one_lt_E hτ).trans hτ1
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hτ.pos.trans hτ1
  have h := lq_lh hτ hτ1 le_rfl h1T h1Ω h0T h0Ω hη hηΩ
  have e1 : Om1 * (Om1 * 1 + 0) = Om1 * Om1 := by rw [mul_one, add_zero]
  rw [e1] at h
  obtain ⟨-, -, -, -, -, hvE, -⟩ := lq_facts hτ hτ1 le_rfl h1T h1Ω h0T h0Ω hη hηΩ
  rw [e1] at hvE
  have e2 : lqL (vt τ (Om1 * Om1 + η)) 1 0 = vt τ (Om1 * Om1 + η) * vt τ (Om1 * Om1 + η) +
      vt τ (Om1 * Om1 + η) := by
    unfold lqL
    rw [log_one_right, opow_zero, mul_one, add_zero, mul_one, add_zero, Ordinal.sub_self, add_zero,
      lq_lg_mul_two hvE]
  rw [e2] at h
  exact h

end Googology.Trans.PoR.InaccPsi.R2.Lq
