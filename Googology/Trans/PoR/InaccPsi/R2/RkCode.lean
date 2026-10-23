import Googology.Trans.PoR.InaccPsi.R2.RjCode
import Googology.Trans.PoR.InaccPsi.R2.LeELay

/-!
# The codes below `ε_{Ω₁+1}` as levels: data, codes over a strongly critical `q`, and `Ω₁`-division

`Ω₁ = Om 1 = Om1`, `ε_{Ω₁+1} = Gg.ggE`, `GgCl Z` the codes over `Z` (`Gg.GgCl`), `rjDat` the countable data of a code
(`Rj.rjDat`), `u_μ = Ω₁^μ = Le.leOe μ = ω^{Ω₁·μ}`.

* `rk_cl_dat` (**a code over a strongly critical `Z` has its data below `Z`**: the converse of `Rj.rj_code`, by
  `Gg.ggDec`), `rk_cl_iff` (**for `z < ε_{Ω₁+1}`: `GgCl Z z ↔ rjDat z < Z`**);
* `rk_cl_div` (**`GgCl Z y ⇒ GgCl Z (y / Ω₁)`**), `rk_cl_Om1_mul` (`GgCl Z μ ⇒ GgCl Z (Ω₁·μ)`);
* `rkDat μ = rjDat (Ω₁ + μ)` (**the data of the level `μ`**, the level of `ϑᵗ(Ω₁·(Ω₁ + μ) + η)`), `rkDat_lt_iff`
  (**`rkDat μ < q ↔ GgCl q μ`** for strongly critical `q`, `μ < ε_{Ω₁+1}`), `rkDat_zero`, `rkDat_lt_Om1`;
* `rkU_mem`, `rkU_mul_mem` (**`u_μ`, `u_μ·D ∈ Cl(a, b)`** for a code `μ` over a strongly critical `b`, `D < b`).

No new axiom.  New definition: `rkDat`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj

variable {S : InaccSeq.{0}}

theorem rk_Om1_E : (Om 1 : Ordinal.{0}) < ggE := ggE_spec.2

theorem rk_E_inE : InE (ggE : Ordinal.{0}) := ggE_spec.1

/-- **A code over a strongly critical `Z` has its data below `Z`.** -/
theorem rk_cl_dat {Z : Ordinal.{0}} (hZ : SC Z) : ∀ z, GgCl Z z → rjDat z < Z := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hz
  rcases lt_or_ge z ggE with hzE | hzE
  · rcases lt_trichotomy z Om1 with h | rfl | h
    · rw [rjDat_small h]; exact hz.lt_of_lt_Om1 hZ (by rw [← rj_Om1]; exact h)
    · rw [rjDat_Om1]; exact hZ.1
    · have hz0 : z ≠ 0 := (rj_Om1_pos.trans h).ne'
      obtain ⟨hsub, hlog⟩ := ggDec hZ z hz
      set g := log ω z with hg
      have hgz : g < z := rj_log_lt h hzE
      obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt z one_lt_omega0)
      have hdec : ω ^ g * (z / ω ^ g) + z % ω ^ g = z := Ordinal.div_add_mod z _
      rw [hk] at hdec
      have hwk : GgCl Z (ω ^ g * k) := GgCl.mul_nat hZ.1 (GgCl.opow hZ.1 hlog) k
      have hle : ω ^ g * k ≤ z := by
        conv_rhs => rw [← hdec]
        exact le_self_add
      have hr : GgCl Z (z % ω ^ g) := by
        have e : z - ω ^ g * k = z % ω ^ g := by
          nth_rewrite 1 [← hdec]; exact Ordinal.add_sub_cancel _ _
        rw [← e]; exact hsub _ hwk hle
      rw [rjDat_eq h hzE]
      exact max_lt (IH g hgz hlog) (IH _ (rj_mod_lt hz0) hr)
  · have h1 : ¬ (Om1 < z ∧ z < ggE) := fun h => absurd h.2 (not_lt.2 hzE)
    have h2 : ¬ z < Om1 := fun h => absurd (h.trans rj_Om1_lt_E) (not_lt.2 hzE)
    rw [rjDat, dif_neg h1, if_neg h2]
    exact hZ.1

/-- **For `z < ε_{Ω₁+1}`: `z` is a code over a strongly critical `Z` iff `rjDat z < Z`.** -/
theorem rk_cl_iff {Z z : Ordinal.{0}} (hZ : SC Z) (hzE : z < ggE) : GgCl Z z ↔ rjDat z < Z :=
  ⟨rk_cl_dat hZ z, rj_code hZ.1 z hzE⟩

/-- **The codes over a strongly critical `Z` are closed under `y ↦ y / Ω₁`.** -/
theorem rk_cl_div {Z : Ordinal.{0}} (hZ : SC Z) : ∀ y, GgCl Z y → GgCl Z (y / Om 1) := by
  have hO0 : (Om 1 : Ordinal.{0}) ≠ 0 := by rw [← rj_Om1]; exact rj_Om1_pos.ne'
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hy
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [Ordinal.zero_div]; exact GgCl.zero hZ.1
  obtain ⟨hsub, hlog⟩ := ggDec hZ y hy
  set g := log ω y with hg
  obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt y one_lt_omega0)
  have hdec : ω ^ g * (y / ω ^ g) + y % ω ^ g = y := Ordinal.div_add_mod y _
  rw [hk] at hdec
  have hrg : y % ω ^ g < ω ^ g := Ordinal.mod_lt y (opow_pos _ omega0_pos).ne'
  rcases lt_or_ge g (Om 1) with hgO | hgO
  · -- `y < Ω₁`
    have hy1 : y < Om 1 := by
      have h1 : y < ω ^ (g + 1) := lt_opow_succ_log_self one_lt_omega0 y
      refine h1.trans_le ?_
      rw [← Bt.Om1_opow]
      exact opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hgO)
    rw [Ordinal.div_eq_zero_of_lt hy1]; exact GgCl.zero hZ.1
  · set g' := g - Om 1 with hg'
    have hge : Om 1 + g' = g := Ordinal.add_sub_cancel_of_le hgO
    have hg'C : GgCl Z g' := (ggDec hZ g hlog).1 _ GgCl.om hgO
    have hwk : GgCl Z (ω ^ g * k) := GgCl.mul_nat hZ.1 (GgCl.opow hZ.1 hlog) k
    have hle : ω ^ g * k ≤ y := by
      conv_rhs => rw [← hdec]
      exact le_self_add
    have hr : GgCl Z (y % ω ^ g) := by
      have e : y - ω ^ g * k = y % ω ^ g := by
        nth_rewrite 1 [← hdec]; exact Ordinal.add_sub_cancel _ _
      rw [← e]; exact hsub _ hwk hle
    have hry : y % ω ^ g < y := rj_mod_lt hy0
    have e : y = Om 1 * (ω ^ g' * k) + y % ω ^ g := by
      conv_lhs => rw [← hdec]
      rw [← hge, opow_add, Bt.Om1_opow, mul_assoc]
    rw [e, Ordinal.mul_add_div _ hO0]
    exact GgCl.add (GgCl.mul_nat hZ.1 (GgCl.opow hZ.1 hg'C) k) (IH _ hry hr)

/-- `GgCl Z μ ⇒ GgCl Z (Ω₁·μ)`. -/
theorem rk_cl_Om1_mul {Z μ : Ordinal.{0}} (hZ : SC Z) (hμ : GgCl Z μ) : GgCl Z (Om 1 * μ) := by
  have := Ph.ph_cl_opow_mul hZ GgCl.om μ hμ
  rwa [Bt.Om1_opow] at this

/-- `GgCl Z (Ω₁ + μ) ↔ GgCl Z μ`. -/
theorem rk_cl_Om1_add {Z μ : Ordinal.{0}} (hZ : SC Z) : GgCl Z (Om 1 + μ) ↔ GgCl Z μ := by
  refine ⟨fun h => ?_, fun h => GgCl.add GgCl.om h⟩
  have := (ggDec hZ _ h).1 _ GgCl.om le_self_add
  rwa [Ordinal.add_sub_cancel] at this

/-! ## The data of a level -/

/-- **The data of the level `μ`**: the data of the code `Ω₁ + μ` (the level of `ϑᵗ(Ω₁·(Ω₁ + μ) + η)`). -/
noncomputable def rkDat (μ : Ordinal.{0}) : Ordinal.{0} := rjDat (Om1 + μ)

theorem rk_Om1_add_lt {μ : Ordinal.{0}} (hμ : μ < ggE) : Om1 + μ < ggE :=
  rk_E_inE.add_lt rj_Om1_lt_E hμ

/-- **`rkDat μ < q ↔ GgCl q μ`** for a strongly critical `q` and `μ < ε_{Ω₁+1}`. -/
theorem rkDat_lt_iff {q μ : Ordinal.{0}} (hq : SC q) (hμ : μ < ggE) : rkDat μ < q ↔ GgCl q μ := by
  unfold rkDat
  rw [← rk_cl_iff hq (rk_Om1_add_lt hμ), rj_Om1]
  exact rk_cl_Om1_add hq

theorem rkDat_zero : rkDat 0 = 0 := by unfold rkDat; rw [add_zero, rjDat_Om1]

theorem rkDat_lt_Om1 {μ : Ordinal.{0}} (hμ : μ < ggE) : rkDat μ < Om1 := rjDat_lt_Om1 _ (rk_Om1_add_lt hμ)

/-- `rkDat μ < q` for a code `μ` over a strongly critical `q`, any `μ` (junk `0` from `ε_{Ω₁+1}` on). -/
theorem rkDat_lt_of_cl {q μ : Ordinal.{0}} (hq : SC q) (hμ : GgCl q μ) : rkDat μ < q :=
  rk_cl_dat hq _ (by rw [rj_Om1]; exact GgCl.add GgCl.om hμ)

/-! ## The multipliers `u_μ` in the closures -/

/-- **`u_μ = Ω₁^μ ∈ Cl(a, b)`** for a code `μ` over a strongly critical `b`. -/
theorem rkU_mem {μ a b : Ordinal.{0}} (hb : SC b) (hμ : GgCl b μ) : Le.leOe μ ∈ S.CSet a b :=
  (GgCl.opow hb.1 (rk_cl_Om1_mul hb hμ)).mem_CSet le_rfl

/-- **`u_μ·D ∈ Cl(a, b)`** for a code `μ` over a strongly critical `b` and `D < b`. -/
theorem rkU_mul_mem {μ a b D : Ordinal.{0}} (hb : SC b) (hμ : GgCl b μ) (hD : D < b) :
    Le.leOe μ * D ∈ S.CSet a b :=
  (Ph.ph_cl_opow_mul hb (rk_cl_Om1_mul hb hμ) D (GgCl.small hD)).mem_CSet le_rfl

end Googology.Trans.PoR.InaccPsi.R2.Rk
