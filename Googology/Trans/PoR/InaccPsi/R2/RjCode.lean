import Googology.Trans.PoR.InaccPsi.R2.GgOtp
import Googology.Trans.PoR.InaccPsi.R2.PhLL
import Googology.Trans.PoR.InaccPsi.R2.BrStep

/-!
# The levels below `ε_{Ω₁+1}`: the countable data `rjDat` of a code

`Ω₁ = Om1 = Om 1`, `ε_{Ω₁+1} = Gg.ggE` (the least `ε`-number above `Ω₁`), `GgCl Z` the codes over `Z` (`Gg.GgCl`),
`Θ_y = Gg.ggTh y` (the reading).

Every `z < ε_{Ω₁+1}` has a hereditary Cantor normal form over `{0, Ω₁}` and countable "leaves": for `Ω₁ < z <
ε_{Ω₁+1}`, `z = ω^e·k + r` with `e = log_ω z < z`, `k < ω`, `r < ω^e`, and the leaves of `z` are those of `e` and of
`r`; a countable `z` is its own leaf; `Ω₁` has none.  `rjDat z` is the largest leaf (`0` if there is none).

* `rj_log_lt` (**`log_ω z < z` for `Ω₁ < z < ε_{Ω₁+1}`**), `rj_mod_lt`;
* `rjDat` (**the countable data of a code**), `rjDat_small`, `rjDat_Om1`, `rjDat_eq` (the recursion),
  `rjDat_lt_Om1` (**the data of `z < ε_{Ω₁+1}` is countable**);
* `rj_code` (**`z < ε_{Ω₁+1}` with `rjDat z < a` is a code over `a`**), `rj_lead_lt` (the leading exponent of
  `z ∈ (Ω₁, ε_{Ω₁+1})` is `≥ Ω₁`), `rjDat_log_le`, `rjDat_mod_le`;
* `rjDat_OmL` (**`rjDat (Ω₁·γ + β) ≤ max(γ, β)`** for `γ, β < Ω₁`: the data of the levels of `R2.CitedLq`).

No new axiom.  New definition: `rjDat`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg

theorem rj_Om1 : (Om1 : Ordinal.{0}) = Om 1 := Br.Om1_eq

theorem rj_Om1_opow : ω ^ (Om1 : Ordinal.{0}) = Om1 := by rw [rj_Om1]; exact Bt.Om1_opow

theorem rj_Om1_pos : (0 : Ordinal.{0}) < Om1 := Ordinal.omega_pos 1

theorem rj_Om1_lt_E : (Om1 : Ordinal.{0}) < ggE := by rw [rj_Om1]; exact ggE_spec.2

/-- **`log_ω z < z` for `Ω₁ < z < ε_{Ω₁+1}`.** -/
theorem rj_log_lt {z : Ordinal.{0}} (h1 : Om1 < z) (h2 : z < ggE) : log ω z < z := by
  refine lt_of_le_of_ne (log_le_self ω z) fun e => ?_
  have hz0 : z ≠ 0 := (rj_Om1_pos.trans h1).ne'
  have hle : ω ^ z ≤ z := by
    have := opow_log_le_self ω hz0; rwa [e] at this
  have hE : ω ^ z = z := le_antisymm hle (right_le_opow z one_lt_omega0)
  exact absurd (ggE_le hE (by rw [← rj_Om1]; exact h1)) (not_le.2 h2)

theorem rj_mod_lt {z : Ordinal.{0}} (h : z ≠ 0) : z % ω ^ log ω z < z :=
  (Ordinal.mod_lt z (opow_pos _ omega0_pos).ne').trans_le (opow_log_le_self ω h)

/-- **The countable data of a code `z < ε_{Ω₁+1}`**: the largest countable leaf of its hereditary Cantor normal form
over `{0, Ω₁}` (`z` itself if `z < Ω₁`; `0` for `z = Ω₁`; for `Ω₁ < z`, the larger of the data of the leading
exponent and of the remainder; finite coefficients are not data).  Junk value `0` from `ε_{Ω₁+1}` on. -/
noncomputable def rjDat (z : Ordinal.{0}) : Ordinal.{0} :=
  if hz : Om1 < z ∧ z < ggE then
    have : log ω z < z := rj_log_lt hz.1 hz.2
    have : z % ω ^ log ω z < z := rj_mod_lt (rj_Om1_pos.trans hz.1).ne'
    max (rjDat (log ω z)) (rjDat (z % ω ^ log ω z))
  else if z < Om1 then z else 0
termination_by z

theorem rjDat_small {z : Ordinal.{0}} (h : z < Om1) : rjDat z = z := by
  rw [rjDat, dif_neg (fun hz => absurd hz.1 (not_lt.2 h.le)), if_pos h]

theorem rjDat_Om1 : rjDat Om1 = 0 := by
  rw [rjDat, dif_neg (fun hz => absurd hz.1 (lt_irrefl _)), if_neg (lt_irrefl _)]

theorem rjDat_eq {z : Ordinal.{0}} (h1 : Om1 < z) (h2 : z < ggE) :
    rjDat z = max (rjDat (log ω z)) (rjDat (z % ω ^ log ω z)) := by
  rw [rjDat, dif_pos ⟨h1, h2⟩]

theorem rjDat_log_le {z : Ordinal.{0}} (h1 : Om1 < z) (h2 : z < ggE) : rjDat (log ω z) ≤ rjDat z := by
  rw [rjDat_eq h1 h2]; exact le_max_left _ _

theorem rjDat_mod_le {z : Ordinal.{0}} (h1 : Om1 < z) (h2 : z < ggE) :
    rjDat (z % ω ^ log ω z) ≤ rjDat z := by
  rw [rjDat_eq h1 h2]; exact le_max_right _ _

/-- The leading exponent of `z ∈ (Ω₁, ε_{Ω₁+1})` is at least `Ω₁`. -/
theorem rj_lead_lt {z : Ordinal.{0}} (h1 : Om1 < z) : Om1 ≤ log ω z :=
  le_log_of_opow_le one_lt_omega0 (by rw [rj_Om1_opow]; exact h1.le)

/-- **The data of `z < ε_{Ω₁+1}` is countable.** -/
theorem rjDat_lt_Om1 : ∀ z : Ordinal.{0}, z < ggE → rjDat z < Om1 := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hzE
  rcases lt_trichotomy z Om1 with h | rfl | h
  · rw [rjDat_small h]; exact h
  · rw [rjDat_Om1]; exact rj_Om1_pos
  · have hl := rj_log_lt h hzE
    have hm := rj_mod_lt (rj_Om1_pos.trans h).ne'
    rw [rjDat_eq h hzE]
    exact max_lt (IH _ hl (hl.trans hzE)) (IH _ hm (hm.trans hzE))

/-- **A code**: `z < ε_{Ω₁+1}` with `rjDat z < a` is a code over `a`. -/
theorem rj_code {a : Ordinal.{0}} (ha : 0 < a) : ∀ z : Ordinal.{0}, z < ggE → rjDat z < a → GgCl a z := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hzE hd
  rcases lt_trichotomy z Om1 with h | rfl | h
  · rw [rjDat_small h] at hd; exact GgCl.small hd
  · rw [rj_Om1]; exact GgCl.om
  · have hz0 : z ≠ 0 := (rj_Om1_pos.trans h).ne'
    have hl := rj_log_lt h hzE
    have hm := rj_mod_lt hz0
    have he := IH _ hl (hl.trans hzE) ((rjDat_log_le h hzE).trans_lt hd)
    have hr := IH _ hm (hm.trans hzE) ((rjDat_mod_le h hzE).trans_lt hd)
    obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt z one_lt_omega0)
    have hdec : ω ^ log ω z * (z / ω ^ log ω z) + z % ω ^ log ω z = z := Ordinal.div_add_mod z _
    rw [← hdec, hk]
    exact GgCl.add (GgCl.mul_nat ha (GgCl.opow ha he) k) hr

theorem rj_E_inE : InE (ggE : Ordinal.{0}) := ggE_spec.1

/-- `Ω₁ + g` for `0 < g < Ω₁` has the data `g`. -/
theorem rjDat_Om1_add {g : Ordinal.{0}} (hg0 : g ≠ 0) (hg1 : g < Om1) : rjDat (Om1 + g) = g := by
  have hO := rj_Om1_opow
  have h1 : Om1 < Om1 + g := (lt_add_iff_pos_right _).2 (pos_iff_ne_zero.2 hg0)
  have h2 : Om1 + g < ggE := rj_E_inE.add_lt rj_Om1_lt_E (hg1.trans rj_Om1_lt_E)
  have hf : Om1 + g = ω ^ Om1 * 1 + g := by rw [mul_one, hO]
  have hgO : g < ω ^ (Om1 : Ordinal.{0}) := by rw [hO]; exact hg1
  have hlog : log ω (Om1 + g) = Om1 := by
    rw [hf, log_opow_mul_add one_lt_omega0 one_ne_zero hgO, log_one_right, add_zero]
  have hmod : (Om1 + g) % ω ^ log ω (Om1 + g) = g := by
    rw [hlog, hf, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hgO]
  rw [rjDat_eq h1 h2, hmod, hlog, rjDat_Om1, rjDat_small hg1]
  exact max_eq_right zero_le

/-- **The data of a level of `R2.CitedLq`**: `rjDat (Ω₁·γ + β) ≤ max(γ, β)` for `γ, β < Ω₁`. -/
theorem rjDat_OmL {β : Ordinal.{0}} (hβ : β < Om1) :
    ∀ γ : Ordinal.{0}, γ < Om1 → rjDat (Om1 * γ + β) ≤ max γ β := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγ
  have hO := rj_Om1_opow
  rcases eq_or_ne γ 0 with rfl | hγ0
  · rw [mul_zero, zero_add, rjDat_small hβ]; exact le_max_right _ _
  set g := log ω γ with hg
  set k := γ / ω ^ g with hk
  set r := γ % ω ^ g with hr
  have hγd : ω ^ g * k + r = γ := Ordinal.div_add_mod γ _
  have hrg : r < ω ^ g := Ordinal.mod_lt γ (opow_pos _ omega0_pos).ne'
  have hk0 : k ≠ 0 := by
    intro e
    have : γ < ω ^ g := by rw [← hγd, e, mul_zero, zero_add]; exact hrg
    exact absurd (opow_log_le_self ω hγ0) (not_le.2 this)
  have hrγ : r < γ := hrg.trans_le (opow_log_le_self ω hγ0)
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
  have hrd : rjDat (Om1 * r + β) ≤ max γ β :=
    (IH r hrγ (hrγ.trans hγ)).trans (max_le_max hrγ.le le_rfl)
  have hE := rj_E_inE
  have hzE : Om1 * γ + β < ggE :=
    hE.add_lt (hE.mul_lt rj_Om1_lt_E (hγ.trans rj_Om1_lt_E)) (hβ.trans rj_Om1_lt_E)
  rcases (show Om1 ≤ Om1 * γ + β from
      (le_mul_of_one_le_right zero_le (one_le_iff_ne_zero.2 hγ0)).trans le_self_add).lt_or_eq with hOz | hOz
  · have hzlog : log ω (Om1 * γ + β) = Om1 + g := by
      have hkω : k < ω := div_opow_log_lt γ one_lt_omega0
      rw [hzf, log_opow_mul_add one_lt_omega0 hk0 hrest, Ordinal.log_eq_zero hkω,
        add_zero]
    have hzmod : (Om1 * γ + β) % ω ^ log ω (Om1 * γ + β) = Om1 * r + β := by
      rw [hzlog, hzf, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hrest]
    rw [rjDat_eq hOz hzE, hzmod, hzlog]
    refine max_le ?_ hrd
    rcases eq_or_ne g 0 with hg0 | hg0
    · rw [hg0, add_zero, rjDat_Om1]; exact zero_le
    · rw [rjDat_Om1_add hg0 (hgγ.trans_lt hγ)]; exact hgγ.trans (le_max_left _ _)
  · rw [← hOz, rjDat_Om1]; exact zero_le

end Googology.Trans.PoR.InaccPsi.R2.Rj
