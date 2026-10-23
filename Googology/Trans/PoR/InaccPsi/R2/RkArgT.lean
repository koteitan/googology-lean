import Googology.Trans.PoR.InaccPsi.R2.RjArg
import Googology.Trans.PoR.InaccPsi.R2.CitedRk

/-!
# The statements of `R2.riArg_T` and `R2.rjArgT_gamma` as theorems placed before `R2.RiTh` (audit MINOR 2 of
# round 75)

* `rkArgT_gamma` (**`Ω₁·(Ω₁·γ + β) + η ∈ Tᵗ ⇒ γ ∈ Tᵗ`**, the statement of the axiom `R2.rjArgT_gamma`): from the
  generic cited fact `R2.rkArg_dat` (`rjDat M ∈ Tᵗ` for `M = Ω₁·γ + β`), since `log_ω γ ≤ rjDat M` and `Tᵗ ∩ Ω₁` is
  an `ε`-number (`R2.vz_next`);
* `rkArg_T` (**`Ω₁·(Ω₁·γ + β) + η ∈ Tᵗ ⇒ γ, β ∈ Tᵗ`**, the statement of the axiom `R2.riArg_T`): `rkArgT_gamma` and
  the theorem `Rj.rjArgT_beta`.

This module imports only `R2.RjArg` and `R2.CitedRk` (neither imports `R2.RiTh`, `R2.CitedRi` or `R2.RjFacts`), so
`R2.RiTh` can use `rkArg_T` in place of `R2.riArg_T` and `R2.RjFacts` can use `rkArgT_gamma` in place of
`R2.rjArgT_gamma`; then `R2.riArg_T` (the only axiom of `R2.CitedRi`) and `R2.rjArgT_gamma` are not used anywhere and
can be removed.  The patched `R2.RiTh` and `R2.RjFacts` (one import and one name changed each) are checked
separately.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rk

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Rj
  Googology.Trans.PoR.InaccPsi.R2.Gg

/-- `log_ω γ ≤ rjDat (Ω₁·γ + β)` for `γ, β < Ω₁`. -/
theorem rk_log_le_dat {γ β : Ordinal.{0}} (hγ : γ < Om1) (hβ : β < Om1) : log ω γ ≤ rjDat (Om1 * γ + β) := by
  have hO := rj_Om1_opow
  rcases eq_or_ne γ 0 with rfl | hγ0
  · rw [log_zero_right]; exact zero_le
  set g := log ω γ with hg
  set k := γ / ω ^ g with hk
  set r := γ % ω ^ g with hr
  have hγd : ω ^ g * k + r = γ := Ordinal.div_add_mod γ _
  have hrg : r < ω ^ g := Ordinal.mod_lt γ (opow_pos _ omega0_pos).ne'
  have hk0 : k ≠ 0 := by
    intro e
    have : γ < ω ^ g := by rw [← hγd, e, mul_zero, zero_add]; exact hrg
    exact absurd (opow_log_le_self ω hγ0) (not_le.2 this)
  have hgγ : g ≤ γ := log_le_self ω γ
  have hOg : (Om1 : Ordinal.{0}) * ω ^ g = ω ^ (Om1 + g) := by rw [opow_add, hO]
  have hrest : Om1 * r + β < ω ^ (Om1 + g) := by
    rw [← hOg]
    calc Om1 * r + β < Om1 * r + Om1 := (add_lt_add_iff_left _).2 hβ
      _ = Om1 * (r + 1) := by rw [mul_add_one]
      _ ≤ Om1 * ω ^ g := mul_le_mul_right (Order.add_one_le_of_lt hrg) _
  have hzf : Om1 * γ + β = ω ^ (Om1 + g) * k + (Om1 * r + β) := by
    conv_lhs => rw [← hγd]
    rw [mul_add, ← mul_assoc, hOg, add_assoc]
  have hE := rj_E_inE
  have hzE : Om1 * γ + β < ggE :=
    hE.add_lt (hE.mul_lt rj_Om1_lt_E (hγ.trans rj_Om1_lt_E)) (hβ.trans rj_Om1_lt_E)
  rcases eq_or_ne g 0 with hg0 | hg0
  · rw [hg0]; exact zero_le
  have hOz : Om1 < Om1 * γ + β := by
    have h1 : Om1 < ω ^ (Om1 + g) := by
      conv_lhs => rw [← hO]
      exact (opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hg0))
    refine h1.trans_le ?_
    rw [hzf]
    exact (le_mul_left _ (pos_iff_ne_zero.2 hk0)).trans le_self_add
  have hzlog : log ω (Om1 * γ + β) = Om1 + g := by
    have hkω : k < ω := div_opow_log_lt γ one_lt_omega0
    rw [hzf, log_opow_mul_add one_lt_omega0 hk0 hrest, Ordinal.log_eq_zero hkω, add_zero]
  have h := rjDat_log_le hOz hzE
  rw [hzlog, rjDat_Om1_add hg0 (hgγ.trans_lt hγ)] at h
  exact h

/-- **The statement of `R2.rjArgT_gamma`, proved from `R2.rkArg_dat`.** -/
theorem rkArgT_gamma {τ γ β η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hγΩ : γ < Om1) (hβΩ : β < Om1)
    (hηΩ : η < Om1) (h : Om1 * (Om1 * γ + β) + η ∈ Tset τ) : γ ∈ Tset τ := by
  rcases eq_or_ne γ 0 with rfl | hγ0
  · exact mem_T_of_le hτ hτ1 zero_le
  have hM1 : Om1 ≤ Om1 * γ + β :=
    (le_mul_of_one_le_right zero_le (one_le_iff_ne_zero.2 hγ0)).trans le_self_add
  have hE := rj_E_inE
  have hME : Om1 * γ + β < ggE :=
    hE.add_lt (hE.mul_lt rj_Om1_lt_E (hγΩ.trans rj_Om1_lt_E)) (hβΩ.trans rj_Om1_lt_E)
  have hd := rkArg_dat hτ hτ1 hM1 hME hηΩ h
  obtain ⟨m, -, -, -, hTm, -, hmE⟩ := vz_next hτ hτ1
  have hdm : rjDat (Om1 * γ + β) < m := (hTm _ (rjDat_lt_Om1 _ hME)).1 hd
  have hγm : γ < m := by
    have h1 : γ < ω ^ (log ω γ + 1) := lt_opow_succ_log_self one_lt_omega0 γ
    have h2 : log ω γ + 1 < m :=
      (inE_indec hmE).add_lt ((rk_log_le_dat hγΩ hβΩ).trans_lt hdm) (one_lt_omega0.trans (omega0_lt_inE hmE))
    have h3 : ω ^ (log ω γ + 1) < m := by
      conv_rhs => rw [← hmE]
      exact (opow_lt_opow_iff_right one_lt_omega0).2 h2
    exact h1.trans h3
  exact (hTm γ hγΩ).2 hγm

/-- **The statement of `R2.riArg_T`, proved from `R2.rkArg_dat` and `Rj.rjArgT_beta`.** -/
theorem rkArg_T {τ γ β η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hγΩ : γ < Om1) (hβΩ : β < Om1)
    (hηΩ : η < Om1) (h : Om1 * (Om1 * γ + β) + η ∈ Tset τ) : γ ∈ Tset τ ∧ β ∈ Tset τ :=
  ⟨rkArgT_gamma hτ hτ1 hγΩ hβΩ hηΩ h, rjArgT_beta hτ hτ1 hγΩ hβΩ hηΩ h⟩

end Googology.Trans.PoR.InaccPsi.R2.Rk
