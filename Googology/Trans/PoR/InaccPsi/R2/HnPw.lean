import Googology.Trans.PoR.InaccPsi.R2.HnU

/-!
# HnPw: THE BAND GATE AT EVERY `Ω₁`-POWER: THE `Ω₁^k`-DIGIT OF A CODE IS BELOW ITS BASE

Generalization of `Hm.hmSq_cl_mod`, `Hm.hmSq_gate_cube_remcoef`, `Hm.hmSq_band_gate` (the `Ω₁`-digit of a code taken
mod `Ω₁²`) to every finite power: for `1 ≤ k < ω`, writing `Ω₁^k = ω^(Ω₁·k)`, a `G`-code `y` over a strongly critical
`Z ≤ Ω₁` has `(y mod Ω₁^(k+1)) / Ω₁^k < Z` (`hn_cl_digit`), and a code in a band `[P + Ω₁^k·M, P + Ω₁^k·(M+1))` with
`Ω₁^(k+1) ∣ P`, `M < Ω₁`, has `M < Z` (`hn_band_gate_k`).  This is the code gate for the levels in
`[Ω₁^k, Ω₁^(k+1))` asked by the unions per `Ω₁`-power (`k = 1`: `Hm.hmSq_band_gate`).

* `hn_cl_mod_opow` (modulo `ω^e`, `Ω₁ ≤ e`, `ω^e ≤ G`, keeps the code grammar);
* `hn_eps_gt_pow` (an `ε`-number above `Ω₁` is above every `Ω₁^(k+1)`);
* `hn_cl_digit_lt` (bounded form), `hn_cl_digit` (**THE `Ω₁^k`-DIGIT GATE**), `hn_band_gate_k`.

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hn

open Googology.Trans.PoR.InaccPsi.R2.Hl
open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk
open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

theorem hn_Om_E : ω ^ (Om 1 : Ordinal.{0}) = Om 1 := by simpa [Br.Om1_eq] using Bt.Om1_opow

/-- **Modulo `ω^e` (`Ω₁ ≤ e`, `ω^e ≤ G`) keeps the `G`-code grammar.** -/
theorem hn_cl_mod_opow {Z e : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (he : Om 1 ≤ e) (heG : ω ^ e ≤ gcG 0)
    {y : Ordinal.{0}} (h : GxCl Z {gcG 0} y) : GxCl Z {gcG 0} (y % ω ^ e) := by
  set B : Ordinal.{0} := ω ^ e with hBdef
  have hB0 : 0 < B := opow_pos _ omega0_pos
  have hBne : B ≠ 0 := hB0.ne'
  have hBp : IsPrincipal (· + ·) B := isPrincipal_add_omega0_opow _
  have hOB : Om 1 ≤ B := hn_Om_E.symm.le.trans (opow_le_opow_right omega0_pos he)
  have hdvdE : ∀ E, InE E → B ≤ E → B ∣ E := fun E hE hBE => by
    have hfix : ω ^ E = E := hE
    have heE : e ≤ E := by
      apply (opow_le_opow_iff_right one_lt_omega0).1
      rw [hfix]; exact hBE
    rw [hBdef, ← hfix]; exact opow_dvd_opow ω heE
  induction h with
  | @small x hx =>
    rw [Ordinal.mod_eq_of_lt ((hx.trans_le hZ1).trans_le hOB)]
    exact GxCl.small hx
  | om =>
    rcases hOB.lt_or_eq with hlt | heq
    · rw [Ordinal.mod_eq_of_lt hlt]; exact GxCl.om
    · rw [heq, Ordinal.mod_self]; exact GxCl.small hZ.1
  | @atom s hs =>
    rw [Set.mem_singleton_iff] at hs
    subst s
    rw [(Ordinal.dvd_iff_mod_eq_zero).1 (hdvdE _ (Low.opow_eq_self_of_SC (gcG_SC 0)) heG)]
    exact GxCl.small hZ.1
  | @add x y _ _ ihx ihy =>
    have hxD := Ordinal.div_add_mod x B
    have hyD := Ordinal.div_add_mod y B
    have hrx : x % B < B := Ordinal.mod_lt x hBne
    rcases lt_or_ge y B with hyB | hyB
    · have e : x + y = B * (x / B) + (x % B + y) := by
        conv_lhs => rw [← hxD]
        rw [add_assoc]
      rw [e, Gw.gwY_mod_eq hB0 (hBp hrx hyB)]
      rw [Ordinal.mod_eq_of_lt hyB] at ihy
      exact GxCl.add ihx ihy
    · have hq : 1 ≤ y / B := by
        rw [Order.one_le_iff_pos]
        exact (Ordinal.div_pos hBne).2 hyB
      obtain ⟨q, hq⟩ := exists_add_of_le hq
      have hry : y % B < B := Ordinal.mod_lt y hBne
      have e1 : x % B + B * (1 + q) = B * (1 + q) := by
        rw [mul_add, mul_one, ← add_assoc, hBp.add_eq_right hrx]
      have e : x + y = B * (x / B + y / B) + y % B := by
        conv_lhs => rw [← hxD, ← hyD]
        rw [hq, ← add_assoc (B * (x / B) + x % B), add_assoc (B * (x / B)) (x % B), e1, ← mul_add]
      rw [e, Gw.gwY_mod_eq hB0 hry]
      exact ihy
  | @phi a b ha hb _ _ =>
    rcases lt_or_ge (veblen a b) B with hv | hv
    · rw [Ordinal.mod_eq_of_lt hv]
      exact GxCl.phi ha hb
    · have hdiv : B ∣ veblen a b := by
        rcases eq_or_ne a 0 with rfl | ha0
        · rw [veblen_zero_apply] at hv ⊢
          have hbE : e ≤ b := (opow_le_opow_iff_right one_lt_omega0).1 hv
          exact opow_dvd_opow ω hbE
        · exact hdvdE _ (gg_veblen_eps ha0) hv
      rw [(Ordinal.dvd_iff_mod_eq_zero).1 hdiv]
      exact GxCl.small hZ.1

/-- **`Ω₁^(k+1) = ω^(Ω₁·(k+1)) ≤ G`.** -/
theorem hn_pow_le_G (k : ℕ) : ω ^ (Om 1 * ((k + 1 : ℕ) : Ordinal.{0})) ≤ gcG 0 := by
  have hG : InE (gcG 0) := Low.opow_eq_self_of_SC (gcG_SC 0)
  have hO : (Om 1 : Ordinal.{0}) < gcG 0 := by rw [← Br.Om1_eq]; exact hg_Om1_lt_G 0
  have hk : ((k + 1 : ℕ) : Ordinal.{0}) < gcG 0 := (natCast_lt_omega0 _).trans (omega0_lt_inE hG)
  have h := opow_le_opow_right omega0_pos (InE.mul_lt hG hO hk).le
  rwa [hG] at h

/-- **An `ε`-number above `Ω₁` lies above every `Ω₁^(k+1) = ω^(Ω₁·(k+1))`.** -/
theorem hn_eps_gt_pow {E : Ordinal.{0}} (hE : InE E) (hOE : Om 1 < E) (k : ℕ) :
    ω ^ (Om 1 * ((k + 1 : ℕ) : Ordinal.{0})) < E := by
  have hk : ((k + 1 : ℕ) : Ordinal.{0}) < E := (natCast_lt_omega0 _).trans (omega0_lt_inE hE)
  have h := (opow_lt_opow_iff_right one_lt_omega0).2 (InE.mul_lt hE hOE hk)
  rwa [hE] at h

theorem hn_one_lt_Z {Z : Ordinal.{0}} (hZ : SC Z) : (1 : Ordinal.{0}) < Z := by
  have h := hZ.2 0 hZ.1 0 hZ.1
  rwa [veblen_zero_apply, opow_zero] at h

/-- **THE `Ω₁^k`-DIGIT GATE, BOUNDED FORM**: a `G`-code `y < Ω₁^(k+1)` over `Z` has `y / Ω₁^k < Z` (`1 ≤ k`). -/
theorem hn_cl_digit_lt {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (k : ℕ) (hk : 1 ≤ k) {y : Ordinal.{0}}
    (h : GxCl Z {gcG 0} y) (hy : y < ω ^ (Om 1 * ((k + 1 : ℕ) : Ordinal.{0}))) :
    y / ω ^ (Om 1 * (k : Ordinal.{0})) < Z := by
  set D : Ordinal.{0} := ω ^ (Om 1 * (k : Ordinal.{0})) with hDdef
  have hD0 : 0 < D := opow_pos _ omega0_pos
  have hDne : D ≠ 0 := hD0.ne'
  have hDp : IsPrincipal (· + ·) D := isPrincipal_add_omega0_opow _
  have hk1 : (1 : Ordinal.{0}) ≤ (k : Ordinal.{0}) := by exact_mod_cast hk
  have hOD : Om 1 ≤ D :=
    hn_Om_E.symm.le.trans (opow_le_opow_right omega0_pos (le_mul_of_one_le_right' hk1))
  have hOm : Om 1 / D < Z := by
    rcases hOD.lt_or_eq with hlt | heq
    · rw [Ordinal.div_eq_zero_of_lt hlt]; exact hZ.1
    · rw [heq, Ordinal.div_self hDne]; exact hn_one_lt_Z hZ
  induction h with
  | @small x hx =>
    rw [Ordinal.div_eq_zero_of_lt ((hx.trans_le hZ1).trans_le hOD)]; exact hZ.1
  | om => exact hOm
  | @atom s hs =>
    rw [Set.mem_singleton_iff] at hs
    rw [hs] at hy
    exact absurd (hy.trans_le (hn_pow_le_G k)) (lt_irrefl _)
  | @add x y _ _ ihx ihy =>
    have hx' : x < ω ^ (Om 1 * ((k + 1 : ℕ) : Ordinal.{0})) := lt_of_le_of_lt le_self_add hy
    have hy' : y < ω ^ (Om 1 * ((k + 1 : ℕ) : Ordinal.{0})) := lt_of_le_of_lt le_add_self hy
    have h1 := ihx hx'
    have h2 := ihy hy'
    have ex := Ordinal.div_add_mod x D
    have ey := Ordinal.div_add_mod y D
    have hr1 : x % D < D := Ordinal.mod_lt x hDne
    have hr2 : y % D < D := Ordinal.mod_lt y hDne
    rcases lt_or_ge y D with hyD | hyD
    · have e : x + y = D * (x / D) + (x % D + y) := by
        conv_lhs => rw [← ex]
        rw [add_assoc]
      rw [e, Ordinal.mul_add_div _ hDne, Ordinal.div_eq_zero_of_lt (hDp hr1 hyD), add_zero]
      exact h1
    · have hq : 1 ≤ y / D := by
        rw [Order.one_le_iff_pos]
        exact (Ordinal.div_pos hDne).2 hyD
      obtain ⟨b', hb'⟩ := exists_add_of_le hq
      have e1 : x % D + D * (1 + b') = D * (1 + b') := by
        rw [mul_add, mul_one, ← add_assoc, hDp.add_eq_right hr1]
      have e : x + y = D * (x / D + y / D) + y % D := by
        conv_lhs => rw [← ex, ← ey]
        rw [hb', ← add_assoc (D * (x / D) + x % D), add_assoc (D * (x / D)) (x % D), e1, ← mul_add]
      rw [e, Ordinal.mul_add_div _ hDne, Ordinal.div_eq_zero_of_lt hr2, add_zero]
      exact hZ.isPrincipal h1 h2
  | @phi a b ha hb _ _ =>
    rcases eq_or_ne a 0 with rfl | ha0
    · rw [veblen_zero_apply] at hy ⊢
      have hb1 : b < Om 1 * ((k + 1 : ℕ) : Ordinal.{0}) := (opow_lt_opow_iff_right one_lt_omega0).1 hy
      rcases lt_or_ge b (Om 1 * (k : Ordinal.{0})) with hbk | hbk
      · rw [Ordinal.div_eq_zero_of_lt ((opow_lt_opow_iff_right one_lt_omega0).2 hbk)]; exact hZ.1
      · obtain ⟨q', r', hr', e⟩ := gv_cl_tail hZ hZ1 gr_GxAt hb
        have hrO : r' < Om 1 := hr'.trans_le hZ1
        have hO0 : Om 1 ≠ 0 := gw_Om_pos.ne'
        have hq' : q' = k := by
          have h1 : b / Om 1 = q' := by
            rw [e, Ordinal.mul_add_div _ hO0, Ordinal.div_eq_zero_of_lt hrO, add_zero]
          apply le_antisymm
          · have : b / Om 1 < ((k + 1 : ℕ) : Ordinal.{0}) := (Ordinal.lt_mul_iff_div_lt hO0).1 hb1
            rw [h1, Nat.cast_add, Nat.cast_one] at this
            exact Order.lt_add_one_iff.1 this
          · rw [← h1]; exact (Ordinal.le_div hO0).2 hbk
        have hpow : ω ^ b = D * ω ^ r' := by rw [e, hq', opow_add]
        rw [hpow, Ordinal.mul_div_cancel _ hDne]
        have htail := hZ.2 0 hZ.1 r' hr'
        simpa [veblen_zero_apply] using htail
    · have hE : InE (veblen a b) := gg_veblen_eps ha0
      rcases lt_or_ge (veblen a b) (Om 1) with hv | hv
      · rw [Ordinal.div_eq_zero_of_lt (hv.trans_le hOD)]; exact hZ.1
      · rcases hv.lt_or_eq with hlt | heq
        · exact absurd (hy.trans (hn_eps_gt_pow hE hlt k)) (lt_irrefl _)
        · rw [← heq]; exact hOm

/-- **THE `Ω₁^k`-DIGIT GATE** (`1 ≤ k < ω`): a `G`-code `y` over a strongly critical `Z ≤ Ω₁` has
`(y mod Ω₁^(k+1)) / Ω₁^k < Z`. -/
theorem hn_cl_digit {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (k : ℕ) (hk : 1 ≤ k) {y : Ordinal.{0}}
    (h : GxCl Z {gcG 0} y) :
    (y % ω ^ (Om 1 * ((k + 1 : ℕ) : Ordinal.{0}))) / ω ^ (Om 1 * (k : Ordinal.{0})) < Z := by
  have he : Om 1 ≤ Om 1 * ((k + 1 : ℕ) : Ordinal.{0}) :=
    le_mul_of_one_le_right' (by exact_mod_cast Nat.succ_pos k)
  exact hn_cl_digit_lt hZ hZ1 k hk (hn_cl_mod_opow hZ hZ1 he (hn_pow_le_G k) h)
    (Ordinal.mod_lt _ (opow_pos _ omega0_pos).ne')

/-- **THE BAND GATE AT `Ω₁^k`** (`1 ≤ k < ω`): a `G`-code `y = P + Ω₁^k·M + r` over a strongly critical `Z ≤ Ω₁`,
with `Ω₁^(k+1) ∣ P`, `M < Ω₁`, `r < Ω₁^k`, has `M < Z`. -/
theorem hn_band_gate_k {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (k : ℕ) (hk : 1 ≤ k)
    {P M r : Ordinal.{0}} (hP : ω ^ (Om 1 * ((k + 1 : ℕ) : Ordinal.{0})) ∣ P) (hM : M < Om 1)
    (hr : r < ω ^ (Om 1 * (k : Ordinal.{0}))) (h : GxCl Z {gcG 0} (P + ω ^ (Om 1 * (k : Ordinal.{0})) * M + r)) :
    M < Z := by
  set D : Ordinal.{0} := ω ^ (Om 1 * (k : Ordinal.{0})) with hDdef
  set B : Ordinal.{0} := ω ^ (Om 1 * ((k + 1 : ℕ) : Ordinal.{0})) with hBdef
  have hDne : D ≠ 0 := (opow_pos _ omega0_pos).ne'
  have hB0 : 0 < B := opow_pos _ omega0_pos
  have hBD : B = D * Om 1 := by
    rw [hBdef, hDdef, Nat.cast_add, Nat.cast_one, mul_add_one, opow_add, hn_Om_E]
  have hlt : D * M + r < B := by
    rw [hBD]
    calc D * M + r < D * M + D := (add_lt_add_iff_left _).2 hr
    _ = D * (M + 1) := by rw [mul_add_one]
    _ ≤ D * Om 1 := mul_le_mul_left' (Order.add_one_le_of_lt hM) _
  obtain ⟨q, rfl⟩ := hP
  have hmod : (B * q + D * M + r) % B = D * M + r := by
    rw [add_assoc]; exact Gw.gwY_mod_eq hB0 hlt
  have hdig := hn_cl_digit hZ hZ1 k hk h
  rw [hmod, Ordinal.mul_add_div _ hDne, Ordinal.div_eq_zero_of_lt hr, add_zero] at hdig
  exact hdig

end Googology.Trans.PoR.InaccPsi.R2.Hn
