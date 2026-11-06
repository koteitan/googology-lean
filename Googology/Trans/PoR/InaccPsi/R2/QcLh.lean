import Googology.Trans.PoR.InaccPsi.R2.QcCopy
import Googology.Trans.PoR.InaccPsi.R2.RjLh

/-!
# QcLh: THE REACH AT A GENERIC LEVEL AS A READING `Θ_α(Λ_M)` OF ONE CODE

`Θ_y = Gg.ggTh y` (a strongly critical `y`), `rjL l = ω^c + logend(c) + (l − ω^c)`, `c = log_ω l` (`Rj.rjL`).  The
reach of `α = ϑᵗ(Ω₁·M + η)` is `rjL(Θ_α(Ω₁·M)) + ζ` (`Rj.rj_lh`).  `Θ_y` keeps `+`, `ω^·`, hence `log_ω`,
`logend` and `−`, so the reach is the reading of the single code `Λ_M := rjL(Ω₁·M)` (read at `α`):

* `qc_th_log`, `qc_th_lg`, `qc_th_sub` (**`Θ_y` commutes with `log_ω`, `logend`, `−`**), `qc_lg_code`,
  `qc_th_rjL` (**`rjL(Θ_y(x)) = Θ_y(rjL x)`**), `qc_rjL_code` (`rjL x` is a code);
* `qc_rjL_gap` (**`rjL(Ω₁·M') + Ω₁ ≤ rjL(Ω₁·M)`** for `Ω₁ ≤ M' < M`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Lu

theorem qc_lg_zero : lg (0 : Ordinal.{0}) = 0 := by unfold lg; simp

variable {y : Ordinal.{0}} (hy : SC y)
include hy

/-- **`Θ_y(log_ω x) = log_ω(Θ_y(x))`** for a code `x`. -/
theorem qc_th_log {x : Ordinal.{0}} (hx : GgCl y x) : ggTh y (log ω x) = log ω (ggTh y x) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [log_zero_right, ggTh_small zero_le, log_zero_right]
  obtain ⟨hsub, hlog⟩ := ggDec hy x hx
  obtain ⟨hdec, hk0, hkω, hr⟩ := Si.si_dec hx0
  set L := log ω x with hL
  obtain ⟨k, hk⟩ := lt_omega0.1 hkω
  rw [hk] at hdec hk0
  have hwk : GgCl y (ω ^ L * k) := GgCl.mul_nat hy.1 (GgCl.opow hy.1 hlog) k
  have hle : ω ^ L * k ≤ x := by
    conv_rhs => rw [← hdec]
    exact le_self_add
  have hrC : GgCl y (x % ω ^ L) := by
    have e : x - ω ^ L * k = x % ω ^ L := by
      nth_rewrite 1 [← hdec]; exact Ordinal.add_sub_cancel _ _
    rw [← e]; exact hsub _ hwk hle
  have hkC : GgCl y (k : Ordinal.{0}) := Ph.ph_cl_nat hy k
  have hThk : ggTh y (k : Ordinal.{0}) = k :=
    ggTh_small (((natCast_lt_omega0 k).trans (Lw.lw_omega_lt_SC hy)).le)
  have hThx : ggTh y x = ω ^ ggTh y L * k + ggTh y (x % ω ^ L) := by
    conv_lhs => rw [← hdec]
    rw [ggTh_add hy hwk, Ph.phTh_opow_mul hy hlog k hkC, hThk]
  have hrlt : ggTh y (x % ω ^ L) < ω ^ ggTh y L := by
    rw [← ggTh_opow hy hlog]; exact ggTh_lt hrC hr
  have hk0' : (0 : Ordinal.{0}) < k := pos_iff_ne_zero.2 hk0
  rw [hThx]
  symm
  refine (log_eq_iff one_lt_omega0 ?_ _).2 ⟨?_, ?_⟩
  · exact (lt_of_lt_of_le (mul_pos (opow_pos _ omega0_pos) hk0') le_self_add).ne'
  · exact (le_mul_left _ hk0').trans le_self_add
  · calc ω ^ ggTh y L * k + ggTh y (x % ω ^ L) < ω ^ ggTh y L * k + ω ^ ggTh y L := (add_lt_add_iff_left _).2 hrlt
      _ = ω ^ ggTh y L * (k + 1) := (mul_add_one _ _).symm
      _ ≤ ω ^ ggTh y L * ω := mul_le_mul_right (by exact_mod_cast (natCast_lt_omega0 (k + 1)).le) _
      _ = ω ^ succ (ggTh y L) := (opow_succ _ _).symm

/-- **The last exponent of a code is a code.** -/
theorem qc_lg_code {x : Ordinal.{0}} (hx : GgCl y x) : GgCl y (lg x) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [qc_lg_zero]; exact GgCl.zero hy.1
  obtain ⟨x₁, x₂, -, -, -, hx₂C, hx₂l, -⟩ := qc_split hy x hx hx0
  rw [← hx₂l]; exact hx₂C

/-- **`Θ_y(logend x) = logend(Θ_y(x))`** for a nonzero code `x`. -/
theorem qc_th_lg {x : Ordinal.{0}} (hx : GgCl y x) (hx0 : x ≠ 0) : ggTh y (lg x) = lg (ggTh y x) := by
  obtain ⟨x₁, x₂, hxs, -, hx₁C, hx₂C, hx₂l, -⟩ := qc_split hy x hx hx0
  rw [← hx₂l, hxs, ggTh_add hy hx₁C, ggTh_opow hy hx₂C, lu_lg_add_right (opow_pos _ omega0_pos).ne',
    LvE.lve_lg_opow]

/-- **`Θ_y(x − w) = Θ_y(x) − Θ_y(w)`** for codes `w ≤ x`. -/
theorem qc_th_sub {x w : Ordinal.{0}} (hw : GgCl y w) (hwx : w ≤ x) :
    ggTh y (x - w) = ggTh y x - ggTh y w := by
  have e : ggTh y x = ggTh y w + ggTh y (x - w) := by
    conv_lhs => rw [← Ordinal.add_sub_cancel_of_le hwx]
    exact ggTh_add hy hw _
  rw [e, Ordinal.add_sub_cancel]

/-- **`rjL(Θ_y(x)) = Θ_y(rjL x)`** for a nonzero code `x`, and `rjL x` is a code. -/
theorem qc_th_rjL {x : Ordinal.{0}} (hx : GgCl y x) (hx0 : x ≠ 0) :
    GgCl y (rjL x) ∧ ggTh y (rjL x) = rjL (ggTh y x) := by
  obtain ⟨hsub, hlog⟩ := ggDec hy x hx
  have hw : GgCl y (ω ^ log ω x) := GgCl.opow hy.1 hlog
  have hwx : ω ^ log ω x ≤ x := opow_log_le_self ω hx0
  have hlgC : GgCl y (lg (log ω x)) := qc_lg_code hy hlog
  have hrC : GgCl y (x - ω ^ log ω x) := hsub _ hw hwx
  have h1 : GgCl y (ω ^ log ω x + lg (log ω x)) := GgCl.add hw hlgC
  refine ⟨GgCl.add h1 hrC, ?_⟩
  unfold rjL
  rw [ggTh_add hy h1, ggTh_add hy hw, ggTh_opow hy hlog, qc_th_sub hy hw hwx, ggTh_opow hy hlog,
    qc_th_log hy hx]
  rcases eq_or_ne (log ω x) 0 with hl0 | hl0
  · have e0 : lg (log ω x) = 0 := by rw [hl0, qc_lg_zero]
    have e0' : lg (log ω (ggTh y x)) = 0 := by
      rw [← qc_th_log hy hx, hl0, ggTh_small zero_le, qc_lg_zero]
    rw [e0, e0', ggTh_small zero_le]
  · rw [qc_th_lg hy hlog hl0, qc_th_log hy hx]

omit hy in
/-- **The gap of the reaches**: `rjL(Ω₁·M') + Ω₁ ≤ rjL(Ω₁·M)` for `Ω₁ ≤ M' < M`. -/
theorem qc_rjL_gap {M' M : Ordinal.{0}} (hM' : Om 1 ≤ M') (hM'M : M' < M) :
    rjL (Om 1 * M') + Om 1 ≤ rjL (Om 1 * M) := by
  have hO0 : (0 : Ordinal.{0}) < Om 1 := Om_pos one_ne_zero
  have hl' : Om 1 * M' + Om 1 ≤ Om 1 * M := by
    rw [← mul_add_one]; exact mul_le_mul_right (Order.add_one_le_of_lt hM'M) _
  set l' := Om 1 * M' with hl'def
  set l := Om 1 * M with hldef
  have hl'0 : l' ≠ 0 := (mul_pos hO0 (hO0.trans_le hM')).ne'
  have hl0 : l ≠ 0 := (mul_pos hO0 ((hO0.trans_le hM').trans hM'M)).ne'
  have hOO : Om 1 * Om 1 ≤ l' := mul_le_mul_right hM' _
  have hOOe : Om 1 * Om 1 = ω ^ (Om 1 * 2) := by
    rw [mul_two_eq, opow_add, Bt.Om1_opow]
  set c' := log ω l' with hc'
  set c := log ω l with hc
  have hc'2 : Om 1 * 2 ≤ c' := le_log_of_opow_le one_lt_omega0 (by rw [← hOOe]; exact hOO)
  have hcc : c' ≤ c := log_mono_right _ (le_self_add.trans hl')
  have hOc : Om 1 < ω ^ c := by
    calc Om 1 < Om 1 * 2 := lt_mul_of_one_lt_right hO0 one_lt_two
      _ ≤ c' := hc'2
      _ ≤ c := hcc
      _ ≤ ω ^ c := right_le_opow c one_lt_omega0
  rcases hcc.lt_or_eq with hlt | heq
  · -- a smaller leading exponent
    have hrj' : rjL l' < ω ^ c := by
      have hlt1 : l' < ω ^ succ c' := lt_opow_succ_log_self one_lt_omega0 l'
      have hsl : ω ^ succ c' ≤ ω ^ c := opow_le_opow_right omega0_pos (Order.succ_le_of_lt hlt)
      have hI : IsPrincipal (· + ·) (ω ^ c) := isPrincipal_add_omega0_opow c
      unfold rjL
      rw [← hc']
      have h1 : ω ^ c' < ω ^ c := (opow_lt_opow_iff_right one_lt_omega0).2 hlt
      have hc'0 : c' ≠ 0 := (lt_of_lt_of_le (mul_pos hO0 two_pos) hc'2).ne'
      have h2 : lg c' < ω ^ c := (lg_le hc'0).trans_lt ((right_le_opow c' one_lt_omega0).trans_lt h1)
      have h3 : l' - ω ^ c' < ω ^ c := (Ordinal.sub_le_self _ _).trans_lt (hlt1.trans_le hsl)
      exact hI (hI h1 h2) h3
    have hI : IsPrincipal (· + ·) (ω ^ c) := isPrincipal_add_omega0_opow c
    refine le_of_lt ?_
    calc rjL l' + Om 1 < ω ^ c := hI hrj' hOc
      _ ≤ ω ^ c + lg c + (l - ω ^ c) := le_self_add.trans le_self_add
      _ = rjL l := by unfold rjL; rw [← hc]
  · -- the same leading exponent
    have hw' : ω ^ c ≤ l' := by rw [← heq]; exact opow_log_le_self ω hl'0
    have hd : (l' - ω ^ c) + Om 1 ≤ l - ω ^ c := by
      have e1 : ω ^ c + ((l' - ω ^ c) + Om 1) = l' + Om 1 := by
        rw [← add_assoc, Ordinal.add_sub_cancel_of_le hw']
      have hw : ω ^ c ≤ l := opow_log_le_self ω hl0
      have e2 : ω ^ c + (l - ω ^ c) = l := Ordinal.add_sub_cancel_of_le hw
      have : ω ^ c + ((l' - ω ^ c) + Om 1) ≤ ω ^ c + (l - ω ^ c) := by rw [e1, e2]; exact hl'
      exact (add_le_add_iff_left _).1 this
    unfold rjL
    rw [← hc', ← hc, heq, add_assoc]
    exact add_le_add le_rfl hd

end Googology.Trans.PoR.InaccPsi.R2.Qc
