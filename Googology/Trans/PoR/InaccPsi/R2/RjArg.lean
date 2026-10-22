import Googology.Trans.PoR.InaccPsi.R2.BaseC
import Googology.Trans.PoR.InaccPsi.R2.CitedLq
import Googology.Trans.PoR.InaccPsi.R2.BrStep
import Googology.Trans.PoR.InaccPsi.R2.BtJ

/-!
# The `β` half of `R2.riArg_T` without that axiom (audit MINOR 2 of round 74)

`Ω₁ = Om1`, `Tᵗ = Tset τ`, `comps x` the additive components of `x`.

* `rj_comps_add` (**`comps y ⊆ comps (a + y)` when `ω^e ∣ a` and `y < ω^e`**: the components of a tail survive);
* `rj_T_of_lead` (**a countable `β` with `ω^{log_ω β} ∈ Tᵗ` lies in `Tᵗ`**: `Tᵗ ∩ Ω₁` is an initial segment closed
  under `+`);
* `rjArgT_beta` (**`Ω₁·(Ω₁·γ + β) + η ∈ Tᵗ ⇒ β ∈ Tᵗ`** for `γ, β, η < Ω₁`), from `R2.Par_comps_eq` (the component
  `Ω₁·ω^{log β}` is in `Tᵗ`), `R2.lgQuot_mem` (its quotient `ω^{log β}` is in `Tᵗ`), `R2.T_inter_Om1` (through
  `R2.T_next`) and `R2.vzT_add`.  `R2.riArg_T` is NOT used.

So the `β` half of `R2.riArg_T` is a theorem from the earlier axioms; only the `γ` half (`Ω₁²·ω^c ∈ Tᵗ ⇒ c ∈ Tᵗ`)
needs a cited fact (`R2.CitedRj.rjArgT_gamma`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rj

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2

/-- **The components of a tail survive**: if `ω^e ∣ a` and `y < ω^e` then every additive component of `y` is an
additive component of `a + y`. -/
theorem rj_comps_add {e : Ordinal.{0}} :
    ∀ a : Ordinal.{0}, ω ^ e ∣ a → ∀ y, y < ω ^ e → ∀ p ∈ comps y, p ∈ comps (a + y) := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IH =>
  intro ha y hy p hp
  rcases eq_or_ne a 0 with rfl | ha0
  · rwa [zero_add]
  have hay0 : a + y ≠ 0 := fun h => ha0 (le_antisymm (h ▸ le_self_add) zero_le)
  set L := log ω (a + y) with hL
  have hcomps : comps (a + y) = ω ^ L :: comps ((a + y) % ω ^ L) := by
    unfold comps; rw [CNF.ne_zero hay0]; rfl
  have hea : ω ^ e ≤ a := Ordinal.le_of_dvd ha0 ha
  have heL : e ≤ L := le_log_of_opow_le one_lt_omega0 (hea.trans le_self_add)
  have hyL : y < ω ^ L := hy.trans_le (opow_le_opow_right omega0_pos heL)
  have hP := isPrincipal_add_omega0_opow L
  have hLa : ω ^ L ≤ a := by
    by_contra hc
    exact absurd (opow_log_le_self ω hay0) (not_le.2 (hP (not_le.1 hc) hyL))
  have hpos : (ω : Ordinal.{0}) ^ L ≠ 0 := (opow_pos L omega0_pos).ne'
  set r := a % ω ^ L with hr
  have hrL : r < ω ^ L := Ordinal.mod_lt a hpos
  have hra : r < a := hrL.trans_le hLa
  have hdec : ω ^ L * (a / ω ^ L) + r = a := Ordinal.div_add_mod a _
  have hmod : (a + y) % ω ^ L = r + y := by
    conv_lhs => rw [← hdec, add_assoc]
    rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt (hP hrL hyL)]
  have hdr : ω ^ e ∣ r := by
    have h1 : ω ^ e ∣ ω ^ L * (a / ω ^ L) := dvd_mul_of_dvd_left (opow_dvd_opow ω heL) _
    exact (Ordinal.dvd_add_iff h1).1 (by rw [hdec]; exact ha)
  rw [hcomps, hmod]
  exact List.mem_cons_of_mem _ (IH r hra hdr y hy p hp)

theorem rj_Om1_inE : InE Om1 := by unfold InE; rw [Br.Om1_eq]; exact Bt.Om1_opow

/-- **A countable `β` with `ω^{log_ω β} ∈ Tᵗ` lies in `Tᵗ`.** -/
theorem rj_T_of_lead {τ β : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hβΩ : β < Om1) (hβ0 : β ≠ 0)
    (hlead : ω ^ log ω β ∈ Tset τ) : β ∈ Tset τ := by
  obtain ⟨m, hτm, -, -, hT, hm1⟩ := T_next (Or.inr hτ) hτ1
  have hOE := rj_Om1_inE
  set w := ω ^ log ω β with hw
  have hw1 : w < Om1 := (opow_log_le_self ω hβ0).trans_lt hβΩ
  have hwm : w < m := (hT w hw1).1 hlead
  have hmul : ∀ n : ℕ, w * (n : Ordinal.{0}) < m := by
    intro n
    induction n with
    | zero => rw [Nat.cast_zero, mul_zero]; exact (zero_le).trans_lt hτm
    | succ n ih =>
      have hs : w * ((n + 1 : ℕ) : Ordinal.{0}) = w * n + w := by rw [Nat.cast_succ, mul_add_one]
      have hn1 : w * (n : Ordinal.{0}) < Om1 := ih.trans hm1
      have hT1 : w * (n : Ordinal.{0}) ∈ Tset τ := (hT _ hn1).2 ih
      have hsT : w * (n : Ordinal.{0}) + w ∈ Tset τ := vzT_add hτ hτ1 hT1 hlead
      rw [hs]
      exact (hT _ (hOE.add_lt hn1 hw1)).1 hsT
  have hk : β / w < ω := div_opow_log_lt β one_lt_omega0
  obtain ⟨k, hkk⟩ := lt_omega0.1 hk
  have hβlt : β < w * ((k + 1 : ℕ) : Ordinal.{0}) := by
    have hd := Ordinal.div_add_mod β w
    have hw0 : w ≠ 0 := (opow_pos _ omega0_pos).ne'
    calc β = w * (β / w) + β % w := hd.symm
      _ < w * (β / w) + w := (add_lt_add_iff_left _).2 (Ordinal.mod_lt β hw0)
      _ = w * ((k + 1 : ℕ) : Ordinal.{0}) := by rw [hkk, Nat.cast_succ, mul_add_one]
  exact (hT β hβΩ).2 (hβlt.trans (hmul (k + 1)))

/-- **The `β` half of `R2.riArg_T`, proved**: for `γ, β, η < Ω₁`, `Ω₁·(Ω₁·γ + β) + η ∈ Tᵗ` gives `β ∈ Tᵗ`. -/
theorem rjArgT_beta {τ γ β η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hγΩ : γ < Om1) (hβΩ : β < Om1)
    (hηΩ : η < Om1) (h : Om1 * (Om1 * γ + β) + η ∈ Tset τ) : β ∈ Tset τ := by
  have hOE := rj_Om1_inE
  have hO0 : (Om1 : Ordinal.{0}) ≠ 0 := hOE.pos.ne'
  rcases eq_or_ne β 0 with rfl | hβ0
  · obtain ⟨m, hτm, -, -, hT, -⟩ := T_next (Or.inr hτ) hτ1
    exact (hT 0 hOE.pos).2 ((zero_le).trans_lt hτm)
  have hOm : ω ^ Om1 = Om1 := hOE
  have hOO : Om1 * Om1 = ω ^ (Om1 + Om1) := by rw [opow_add, hOm]
  set y := Om1 * β + η with hy
  have hxe : Om1 * (Om1 * γ + β) + η = Om1 * Om1 * γ + y := by
    rw [hy, mul_add, mul_assoc, add_assoc]
  have hylt : y < ω ^ (Om1 + Om1) := by
    rw [← hOO]
    calc y < Om1 * β + Om1 := (add_lt_add_iff_left _).2 hηΩ
      _ = Om1 * (β + 1) := by rw [mul_add_one]
      _ ≤ Om1 * Om1 := mul_le_mul_right (Order.add_one_le_of_lt hβΩ) _
  have hdvd : ω ^ (Om1 + Om1) ∣ Om1 * Om1 * γ := by rw [← hOO]; exact dvd_mul_right _ _
  have hy0 : y ≠ 0 := by
    intro e
    have : Om1 * β ≤ y := le_self_add
    rw [e] at this
    exact hβ0 ((mul_eq_zero.1 (le_antisymm this zero_le)).resolve_left hO0)
  have hylog : log ω y = Om1 + log ω β := by
    have : y = ω ^ Om1 * β + η := by rw [hOm]
    rw [this]; exact log_opow_mul_add one_lt_omega0 hβ0 (by rw [hOm]; exact hηΩ)
  have hlead : ω ^ (Om1 + log ω β) ∈ comps y := by rw [← hylog]; exact lead_comp hy0
  have hpx : ω ^ (Om1 + log ω β) ∈ comps (Om1 * (Om1 * γ + β) + η) := by
    rw [hxe]; exact rj_comps_add _ hdvd y hylt _ hlead
  have hτx : τ ≤ Om1 * (Om1 * γ + β) + η := by
    refine hτ1.le.trans ?_
    calc Om1 ≤ Om1 * β := le_mul_left Om1 (pos_iff_ne_zero.2 hβ0)
      _ ≤ Om1 * (Om1 * γ + β) := mul_le_mul_right le_add_self _
      _ ≤ _ := le_self_add
  have hpT := (Par_comps_eq hτ hτ1 h hτx).1 _ hpx
  have hpe : ω ^ (Om1 + log ω β) = Om1 * ω ^ log ω β := by rw [opow_add, hOm]
  rw [hpe] at hpT
  have hlb : ω ^ log ω β < Om1 := (opow_log_le_self ω hβ0).trans_lt hβΩ
  have hp2 : Om1 * ω ^ log ω β < Om1 * Om1 := (mul_lt_mul_iff_right₀ hOE.pos).2 hlb
  have hq := lgQuot_mem hτ hτ1 hpT hp2
  rw [Ordinal.mul_div_cancel _ hO0] at hq
  exact rj_T_of_lead hτ hτ1 hβΩ hβ0 hq

end Googology.Trans.PoR.InaccPsi.R2.Rj
