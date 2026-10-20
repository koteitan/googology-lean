import Googology.Trans.PoR.InaccPsi.R2.CitedLv
import Googology.Trans.PoR.InaccPsi.R2.LuTh

/-!
# The theta terms at the levels `x ≤ β < Ω₁`: comparison and the exact `R₁⁺`-reach

From the axioms of `R2.CitedLv` (stated once for every level `β ∈ Tˣ`, `x ≤ β < Ω₁`):

* `lvVt_lt`, `lvVt_eta_lt` (comparison at a lower and at the same level), `lvLt_vt_self_tau_add` (`η < ϑˣ(Ω₁·(x+b)+η)`);
* `Lv.lv_lh_gen` (**the `R₁⁺`-reach at every level `x ≤ β < Ω₁`**: `lh(ϑˣ(Ω₁·β + η)) = luL(ϑˣ(Ω₁·β + η), β) + ζ`, the
  same block `luL` as for the constant levels in `R2.LuTh`);
* `Lv.luL_eq_L` (`luL(a, x + b) = a·x + x + a·b` for `b ≤ x`), `Lv.lh_th_L` (the reach at the level `x + b`, `b < x`),
  `Lv.lh_top` (**the reach of `ϑˣ(Ω₁·(x + x))`**: `a·x + x + a·x`).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-- The comparison at a lower level (from `lvVt_lt_gen`). -/
theorem lvVt_lt {τ β' β η' η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1)
    (hβ' : β' ∈ Tset τ) (hβ'1 : β' < Om1)
    (hβ : β ∈ Tset τ) (hτβ : τ ≤ β) (hβ1 : β < Om1)
    (hη' : η' ∈ Tset τ) (hη'1 : η' < Om1) (hη : η ∈ Tset τ) (hη1 : η < Om1)
    (_hβ'β : β' < β) (harg : Om1 * β' + η' < Om1 * β + η)
    (hβ'θ : β' < vt τ (Om1 * β + η)) (hη'θ : η' < vt τ (Om1 * β + η)) :
    vt τ (Om1 * β' + η') < vt τ (Om1 * β + η) :=
  lvVt_lt_gen hτ hτ1 hβ' hβ'1 hβ hτβ hβ1 hη' hη'1 hη hη1 harg hβ'θ hη'θ

/-- The comparison at the same level `τ ≤ β < Ω₁` (from `lvVt_lt_gen` and `lvLevel_lt_vt`). -/
theorem lvVt_eta_lt {τ β η' η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1)
    (hβ : β ∈ Tset τ) (hτβ : τ ≤ β) (hβ1 : β < Om1)
    (hη' : η' ∈ Tset τ) (hη'1 : η' < Om1) (hη : η ∈ Tset τ) (hη1 : η < Om1)
    (hη'η : η' < η) (hη'θ : η' < vt τ (Om1 * β + η)) :
    vt τ (Om1 * β + η') < vt τ (Om1 * β + η) :=
  lvVt_lt_gen hτ hτ1 hβ hβ1 hβ hτβ hβ1 hη' hη'1 hη hη1 ((add_lt_add_iff_left _).2 hη'η)
    (lvLevel_lt_vt hτ hτ1 hβ hτβ hβ1 hη hη1).1 hη'θ

/-- `η < ϑᵗ(Ω₁·(τ + β₀) + η)` for `β₀ < τ` (from `lvLevel_lt_vt`). -/
theorem lvLt_vt_self_tau_add {τ β₀ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hβ₀ : β₀ < τ)
    (hη : η ∈ Tset τ) (hη1 : η < Om1) :
    η < vt τ (Om1 * (τ + β₀) + η) :=
  (lvLevel_lt_vt hτ hτ1 (vzT_add hτ hτ1 (mem_T_of_le hτ hτ1 le_rfl) (mem_T_of_le hτ hτ1 hβ₀.le))
    le_self_add (Om1_add_lt hτ1 (hβ₀.trans hτ1)) hη hη1).2

namespace Lv

/-- The non-remainder part of the exact reach at level `τ+b`. -/
noncomputable def L (τ b α : Ordinal.{0}) : Ordinal.{0} :=
  (α * τ + τ) + α * b

/-- The facts on `ϑˣ(Ω₁·β + η)` at a level `β ∈ Tˣ`, `x ≤ β < Ω₁`. -/
theorem gen_facts {x β η : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hβ : β ∈ Tset x) (hxβ : x ≤ β)
    (hβ1 : β < Om1) (hη : η ∈ Tset x) (hη1 : η < Om1) :
    Om1 * β + η ∈ Tset x ∧ Om1 * β + η < OmTwo ∧
    vt x (Om1 * β + η) ∈ Tset x ∧ x < vt x (Om1 * β + η) ∧
    vt x (Om1 * β + η) < Om1 ∧ InE (vt x (Om1 * β + η)) ∧
    Indec (vt x (Om1 * β + η)) ∧ β < vt x (Om1 * β + η) ∧ η < vt x (Om1 * β + η) := by
  have hargT := lvArg_mem hx hx1 hβ hxβ hβ1 hη hη1
  have harg2 := Lu.luOm1_mul_lt hβ1 hη1
  obtain ⟨hvT, -, hv1, hvP, -⟩ := vt_memTwo hx hx1 hargT harg2
  have hβ1' : 1 ≤ β := (Lu.lu_one_lt_E hx).le.trans hxβ
  have hΩ : Om1 ≤ Om1 * β + η := by
    calc Om1 = Om1 * 1 := (mul_one _).symm
      _ ≤ Om1 * β := mul_le_mul_right hβ1' Om1
      _ ≤ _ := le_self_add
  have hE := (vt_E_iff hx hx1 hargT harg2).2 hΩ
  have hl := lvLevel_lt_vt hx hx1 hβ hxβ hβ1 hη hη1
  exact ⟨hargT, harg2, hvT, hE.1, hv1, hE.2, hvP, hl.1, hl.2⟩

/-- **The `R₁⁺`-reach at every level `x ≤ β < Ω₁`**: `lh(ϑˣ(Ω₁·β + η)) = luL(ϑˣ(Ω₁·β + η), β) + ζ` ([W07b] Theorem
5.3 through `lh_eq_lhT`, with `lvLhT_gen` and `lu_lhT_mul_opow`). -/
theorem lv_lh_gen {x β η : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hβ : β ∈ Tset x) (hxβ : x ≤ β)
    (hβ1 : β < Om1) (hη : η ∈ Tset x) (hη1 : η < Om1) :
    IsLh1 (vt x (Om1 * β + η)) (Lu.luL (vt x (Om1 * β + η)) β + luZeta x β η) := by
  obtain ⟨-, -, hvT, hxv, hv1, hvE, hvP, hβv, -⟩ := gen_facts hx hx1 hβ hxβ hβ1 hη hη1
  have h := lh_eq_lhT (Or.inr hx) hx1 hvT hxv hv1 hvP
  set a := vt x (Om1 * β + η) with ha
  have hβω : ω ≤ β := (Lu.lu_omega_lt_E hx).le.trans hxβ
  unfold Lu.luL
  rw [if_neg (not_lt.2 hβω)]
  have hβ0 : β ≠ 0 := (lt_of_lt_of_le omega0_pos hβω).ne'
  set b := log ω β with hb
  have hb1 : 1 ≤ b := one_le_iff_pos.2 (log_pos one_lt_omega0 hβ0 hβω)
  have hba : b < a := lt_of_le_of_lt (log_le_self ω β) hβv
  have hlh := (Lu.lu_lhT_mul_opow hx hx1 hvT hxv hv1 hvE hb1 hba).2
  rw [lvLhT_gen hx hx1 hβ hxβ hβ1 hη hη1, ← ha, ← hb, hlh] at h
  have hgle : ω ^ b ≤ β := opow_log_le_self ω hβ0
  have e : a * β + luZeta x β η = a * ω ^ b + (a * (β - ω ^ b) + luZeta x β η) := by
    rw [← add_assoc, ← mul_add, Ordinal.add_sub_cancel_of_le hgle]
  rw [e, Ordinal.add_sub_cancel, ← add_assoc] at h
  exact h

/-- `luL(a, x + b) = a·x + x + a·b` for an `ε`-number `x` and `b ≤ x`. -/
theorem luL_eq_L {x b a : Ordinal.{0}} (hx : InE x) (hb : b ≤ x) : Lu.luL a (x + b) = L x b a := by
  have hxω : ω ≤ x + b := (Lu.lu_omega_lt_E hx).le.trans le_self_add
  have hx' : ω ^ x = x := hx
  have hlog : log ω (x + b) = x := by
    rcases hb.lt_or_eq with hbx | hbx
    · have := log_opow_mul_add (b := ω) (u := x) (v := 1) (w := b) one_lt_omega0 one_ne_zero
        (by rw [hx']; exact hbx)
      rw [log_one_right, add_zero, mul_one, hx'] at this
      exact this
    · rw [hbx]
      have h2 : (2 : Ordinal.{0}) < ω := by exact_mod_cast natCast_lt_omega0 2
      have := log_opow_mul_add (b := ω) (u := x) (v := 2) (w := 0) one_lt_omega0 two_ne_zero
        (opow_pos x omega0_pos)
      have e : ω ^ x * 2 + 0 = x + x := by rw [add_zero, hx', mul_two_eq]
      rw [e, log_eq_zero h2, add_zero] at this
      exact this
  unfold Lu.luL L
  rw [if_neg (not_lt.2 hxω), hlog, hx', Lu.lu_lg_E hx, Ordinal.add_sub_cancel]

/-- The elementary facts for the first theta family whose level depends on the base. -/
theorem th_facts {τ b η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hb : b < τ)
    (hη : η ∈ Tset τ) (hη1 : η < Om1) :
    Om1 * (τ + b) + η ∈ Tset τ ∧ Om1 * (τ + b) + η < OmTwo ∧
    vt τ (Om1 * (τ + b) + η) ∈ Tset τ ∧ τ < vt τ (Om1 * (τ + b) + η) ∧
    vt τ (Om1 * (τ + b) + η) < Om1 ∧ InE (vt τ (Om1 * (τ + b) + η)) ∧
    Indec (vt τ (Om1 * (τ + b) + η)) ∧ η < vt τ (Om1 * (τ + b) + η) := by
  have hβT : τ + b ∈ Tset τ := vzT_add hτ hτ1
    (mem_T_of_le hτ hτ1 le_rfl) (mem_T_of_le hτ hτ1 hb.le)
  have hβO : τ + b < Om1 := Om1_add_lt hτ1 (hb.trans hτ1)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -, h9⟩ := gen_facts hτ hτ1 hβT le_self_add hβO hη hη1
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h9⟩

/-- The argument remainder is strictly increasing inside a base-dependent theta level. -/
theorem th_lt {τ b σ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hb : b < τ)
    (hσ : σ ∈ Tset τ) (hη : η ∈ Tset τ) (hη1 : η < Om1) (hση : σ < η)
    (hηθ : η < vt τ (Om1 * (τ + b) + η)) :
    vt τ (Om1 * (τ + b) + σ) < vt τ (Om1 * (τ + b) + η) := by
  have hβT : τ + b ∈ Tset τ := vzT_add hτ hτ1
    (mem_T_of_le hτ hτ1 le_rfl) (mem_T_of_le hτ hτ1 hb.le)
  have hβO : τ + b < Om1 := Om1_add_lt hτ1 (hb.trans hτ1)
  exact lvVt_eta_lt hτ hτ1 hβT le_self_add hβO hσ (lt_trans hση hη1) hη hη1 hση
    (lt_trans hση hηθ)

/-- Weak monotonicity in the remainder of a base-dependent theta term. -/
theorem th_le {τ b σ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hb : b < τ)
    (hσ : σ ∈ Tset τ) (hη : η ∈ Tset τ) (hη1 : η < Om1)
    (hση : σ ≤ η) (hηθ : η < vt τ (Om1 * (τ + b) + η)) :
    vt τ (Om1 * (τ + b) + σ) ≤ vt τ (Om1 * (τ + b) + η) := by
  rcases eq_or_lt_of_le hση with hEq | hlt
  · subst σ
    exact le_rfl
  · exact (th_lt hτ hτ1 hb hσ hη hη1 hlt hηθ).le

/-- The exact reach at the level `τ + b` splits into the block `L` and the remainder `ζ`. -/
theorem lh_th_L {τ b η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hb : b < τ)
    (hη : η ∈ Tset τ) (hη1 : η < Om1) :
    IsLh1 (vt τ (Om1 * (τ + b) + η))
      (L τ b (vt τ (Om1 * (τ + b) + η)) + luZeta τ (τ + b) η) := by
  have hβT : τ + b ∈ Tset τ := vzT_add hτ hτ1
    (mem_T_of_le hτ hτ1 le_rfl) (mem_T_of_le hτ hτ1 hb.le)
  have hβO : τ + b < Om1 := Om1_add_lt hτ1 (hb.trans hτ1)
  have h := lv_lh_gen hτ hτ1 hβT le_self_add hβO hη hη1
  rwa [luL_eq_L hτ hb.le] at h

/-- **The exact reach of `ϑˣ(Ω₁·(x + x))`**: `a·x + x + a·x`. -/
theorem lh_top {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    IsLh1 (vt x (Om1 * (x + x))) (L x x (vt x (Om1 * (x + x)))) := by
  have hxT : x ∈ Tset x := mem_T_of_le hx hx1 le_rfl
  have hβT : x + x ∈ Tset x := vzT_add hx hx1 hxT hxT
  have hβO : x + x < Om1 := Om1_add_lt hx1 hx1
  have h := lv_lh_gen hx hx1 hβT le_self_add hβO (mem_T_of_le hx hx1 zero_le) (Ordinal.omega_pos 1)
  rw [add_zero, Lu.lu_zeta_zero, add_zero, luL_eq_L hx le_rfl] at h
  exact h

end Lv

end Googology.Trans.PoR.InaccPsi.R2
