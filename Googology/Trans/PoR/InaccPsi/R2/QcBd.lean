import Googology.Trans.PoR.InaccPsi.R2.QcUps

/-!
# QcBd: THE BOUND OF THE LAYER TOPS PAST `X` — BELOW A POINT OF A GENERIC LEVEL WITH ITS DATA BELOW THE BASE

The union and ladder steps (`Yw.YwUF`, `Yw.YwLH`) asked their tops below `X^x = ϑˣ(Ω₁·Ω₁·2)` only to have Lemma IMG
there (`Yw.ywImg`).  With Lemma IMG below every `ϑᵖ(Ω₁·N)`, `Ω₁ ≤ N < ε_{Ω₁+1}`, `rjDat N < ρ` (`Qc.qc_img_rst`),
the bound becomes:

* `QcBd x v` (**`v < ϑˣ(Ω₁·N)` for a level `Ω₁ ≤ N < ε_{Ω₁+1}` with `rjDat N < x`**), `qcBd_of_X` (every `v < X^x`),
  `qcBd_mono`, `qcBd_lt` (`v < Ω₁`), `qcBd_T` (`v ∈ Tˣ`), `qc_img_bd` (**Lemma IMG at every `v` with `QcBd ρ v`**).

No new axiom.  New definition: `QcBd`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Gn

/-- **`v` is below a point `ϑˣ(Ω₁·N)` of a level `Ω₁ ≤ N < ε_{Ω₁+1}` with its data below `x`.** -/
def QcBd (x v : Ordinal.{0}) : Prop :=
  ∃ N, Om1 ≤ N ∧ N < ggE ∧ rjDat N < x ∧ v < vt x (Om1 * N)

theorem qcBd_mono {x v w : Ordinal.{0}} (hwv : w ≤ v) (h : QcBd x v) : QcBd x w := by
  obtain ⟨N, h1, h2, h3, h4⟩ := h
  exact ⟨N, h1, h2, h3, hwv.trans_lt h4⟩

/-- The point `ϑˣ(Ω₁·N)` is in `Tˣ ∩ Ω₁`. -/
theorem qc_bd_pt {x N : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hN1 : Om1 ≤ N) (hNE : N < ggE)
    (hNx : rjDat N < x) : vt x (Om1 * N) ∈ Tset x ∧ vt x (Om1 * N) < Om1 := by
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
  have hargT := rjArg_mem hx hx1 hN1 hNE (mem_T_of_le hx hx1 hNx.le) h0T h0Ω
  rw [add_zero] at hargT
  obtain ⟨hT, -, h1, -, -⟩ := vt_memTwo hx hx1 hargT (by simpa using qc_arg_lt hNE h0Ω)
  exact ⟨hT, h1⟩

theorem qcBd_lt {x v : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (h : QcBd x v) : v < Om1 := by
  obtain ⟨N, h1, h2, h3, h4⟩ := h
  exact h4.trans (qc_bd_pt hx hx1 h1 h2 h3).2

theorem qcBd_T {x v : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (h : QcBd x v) : v ∈ Tset x := by
  obtain ⟨N, h1, h2, h3, h4⟩ := h
  obtain ⟨hT, h1'⟩ := qc_bd_pt hx hx1 h1 h2 h3
  exact vz_T_down hx hx1 hT h1' h4.le

/-- **Every `v < X^x` is below a point of a generic level** (`N = Ω₁·2`). -/
theorem qcBd_of_X {x v : Ordinal.{0}} (hx : InE x) (hv : v < Yw.ywX x) : QcBd x v := by
  have h2 : (2 : Ordinal.{0}) < x := by
    have := natCast_lt_omega0 2
    exact_mod_cast this.trans (omega0_lt_inE hx)
  have hgE : InE ggE := ggE_spec.1
  have hO2 : Om1 * 2 < ggE := hgE.mul_lt (by rw [rj_Om1]; exact ggE_spec.2)
    ((natCast_lt_omega0 2).trans (omega0_lt_inE hgE))
  have hdat : rjDat (Om1 * 2) ≤ 2 := by
    have h2Ω : (2 : Ordinal.{0}) < Om1 := by
      have := (natCast_lt_omega0 2).trans (omega0_lt_inE (Low.opow_eq_self_of_SC qc_Om1_SC))
      exact_mod_cast this
    have := rjDat_OmL (β := 0) rj_Om1_pos 2 h2Ω
    rwa [add_zero, max_eq_left zero_le] at this
  refine ⟨Om1 * 2, le_mul_of_one_le_right' (by norm_num), hO2, hdat.trans_lt h2, ?_⟩
  have e : Yw.ywX x = vt x (Om1 * (Om1 * 2)) := by
    show vt x (Om1 * (Om1 * 2 + 0) + 0) = vt x (Om1 * (Om1 * 2))
    rw [add_zero, add_zero]
  rwa [e] at hv

/-- **Lemma IMG at every `v` below a point of a generic level** (in a restart context). -/
theorem qc_img_bd {ρ τ δ v : Ordinal.{0}} (h : RstK ρ τ δ) (hb : QcBd ρ v) : GnI ρ δ v := by
  obtain ⟨N, h1, h2, h3, h4⟩ := hb
  exact qc_img_rst h h1 h2 h3 v h4

end Googology.Trans.PoR.InaccPsi.R2.Qc
