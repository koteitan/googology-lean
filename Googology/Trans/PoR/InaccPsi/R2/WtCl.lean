import Googology.Trans.PoR.InaccPsi.R2.WnLv3
import Googology.Trans.PoR.InaccPsi.R2.GoStep

/-!
# WtCl: CODES OVER `Z` WITH THE ATOM `G` ARE CLOSED UNDER `y ↦ y / Ω₁`, `b ↦ Ω₁·b`, AND THE HEAD OF A LEVEL

`G = Γ_{Ω₁+1}`.  For a strongly critical `Z` the codes `GxCl Z {G}` (built from ordinals `< Z`, `Ω₁`, `G` by `+` and
`φ`) are closed under the decomposition of `Mx.gxDec`.  This module adds, for every such `Z`:

* `wt_GxAt` (`{G}` is a set of atoms: strongly critical, above `Ω₁`);
* `wt_cl_Om1_mul` (**`b` a code ⇒ `Ω₁·b` a code**), `wt_cl_div` (**`y` a code ⇒ `y / Ω₁` a code**);
* `wt_cl_head` (**THE HEAD OF A LEVEL IS A CODE**: if a code `y` lies in `[Ω₁·(Ω₁·a + q), Ω₁·(Ω₁·a) + Ω₁²)`
  then `Ω₁·(Ω₁·a + q)` is a code over `Z`).

These are the facts the code-gate field `g_cl` of a level datum needs when the gate is given by a code system
(`Go.GoD.code_gate`) and no gate arithmetic for `y / Ω₁` is available.

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wt

open Googology.Trans.PoR.InaccPsi.R2.Ho
open Googology.Trans.PoR.InaccPsi.R2.Hn Googology.Trans.PoR.InaccPsi.R2.Hl
open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk
open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Gf
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd
open Googology.Trans.PoR.InaccPsi.R2.Wh Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Rj

variable {Z : Ordinal.{0}}

/-- `{G}` is a set of atoms (strongly critical, above `Ω₁`). -/
theorem wt_GxAt : GxAt ({gcG 0} : Set Ordinal.{0}) := by
  intro s hs
  rw [Set.mem_singleton_iff] at hs
  subst hs
  exact ⟨gcG_SC 0, gcG_Om1_lt 0⟩

theorem wt_cl_Om1 : GxCl Z {gcG 0} Om1 := by rw [Br.Om1_eq]; exact GxCl.om

/-- **`Ω₁·b` is a code over `Z` when `b` is.** -/
theorem wt_cl_Om1_mul (hZ : SC Z) : ∀ b, GxCl Z {gcG 0} b → GxCl Z {gcG 0} (Om1 * b) := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hb
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [mul_zero]; exact GxCl.zero hZ.1
  obtain ⟨hsub, hlog⟩ := gxDec hZ wt_GxAt b hb
  set g := log ω b with hg
  obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt b one_lt_omega0)
  have hdec : ω ^ g * (b / ω ^ g) + b % ω ^ g = b := Ordinal.div_add_mod b _
  rw [hk] at hdec
  have hwk : GxCl Z {gcG 0} (ω ^ g * k) := gx_mul_nat hZ.1 (GxCl.opow hZ.1 hlog) k
  have hle : ω ^ g * k ≤ b := by
    conv_rhs => rw [← hdec]
    exact le_self_add
  have hr : GxCl Z {gcG 0} (b % ω ^ g) := by
    have e : b - ω ^ g * k = b % ω ^ g := by
      nth_rewrite 1 [← hdec]; exact Ordinal.add_sub_cancel _ _
    rw [← e]; exact hsub _ hwk hle
  have hrb : b % ω ^ g < b := rj_mod_lt hb0
  have e : Om1 * b = ω ^ (Om1 + g) * k + Om1 * (b % ω ^ g) := by
    conv_lhs => rw [← hdec]
    rw [mul_add, ← mul_assoc, opow_add, rj_Om1_opow]
  rw [e]
  exact GxCl.add (gx_mul_nat hZ.1 (GxCl.opow hZ.1 (GxCl.add wt_cl_Om1 hlog)) k) (IH _ hrb hr)

/-- **`y / Ω₁` is a code over `Z` when `y` is.** -/
theorem wt_cl_div (hZ : SC Z) : ∀ y, GxCl Z {gcG 0} y → GxCl Z {gcG 0} (y / Om1) := by
  have hO0 : (Om1 : Ordinal.{0}) ≠ 0 := wh_Om1_pos.ne'
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hy
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [Ordinal.zero_div]; exact GxCl.zero hZ.1
  obtain ⟨hsub, hlog⟩ := gxDec hZ wt_GxAt y hy
  set g := log ω y with hg
  obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt y one_lt_omega0)
  have hdec : ω ^ g * (y / ω ^ g) + y % ω ^ g = y := Ordinal.div_add_mod y _
  rw [hk] at hdec
  rcases lt_or_ge g Om1 with hgO | hgO
  · have hy1 : y < Om1 := by
      have h1 : y < ω ^ (g + 1) := lt_opow_succ_log_self one_lt_omega0 y
      refine h1.trans_le ?_
      rw [← rj_Om1_opow]
      exact opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hgO)
    rw [Ordinal.div_eq_zero_of_lt hy1]; exact GxCl.zero hZ.1
  · set g' := g - Om1 with hg'
    have hge : Om1 + g' = g := Ordinal.add_sub_cancel_of_le hgO
    have hg'C : GxCl Z {gcG 0} g' := (gxDec hZ wt_GxAt g hlog).1 _ wt_cl_Om1 hgO
    have hwk : GxCl Z {gcG 0} (ω ^ g * k) := gx_mul_nat hZ.1 (GxCl.opow hZ.1 hlog) k
    have hle : ω ^ g * k ≤ y := by
      conv_rhs => rw [← hdec]
      exact le_self_add
    have hr : GxCl Z {gcG 0} (y % ω ^ g) := by
      have e : y - ω ^ g * k = y % ω ^ g := by
        nth_rewrite 1 [← hdec]; exact Ordinal.add_sub_cancel _ _
      rw [← e]; exact hsub _ hwk hle
    have hry : y % ω ^ g < y := rj_mod_lt hy0
    have e : y = Om1 * (ω ^ g' * k) + y % ω ^ g := by
      conv_lhs => rw [← hdec]
      rw [← hge, opow_add, rj_Om1_opow, mul_assoc]
    rw [e, Ordinal.mul_add_div _ hO0]
    exact GxCl.add (gx_mul_nat hZ.1 (GxCl.opow hZ.1 hg'C) k) (IH _ hry hr)

/-- **THE HEAD OF A LEVEL IS A CODE**: a code `y` over a strongly critical `Z` with
`Ω₁·(Ω₁·a + q) ≤ y < Ω₁·(Ω₁·a) + Ω₁²` makes `Ω₁·(Ω₁·a + q)` a code over `Z`. -/
theorem wt_cl_head (hZ : SC Z) {y a q : Ordinal.{0}} (hy : GxCl Z {gcG 0} y)
    (hLy : Om1 * (Om1 * a + q) ≤ y) (hy2 : y < Om1 * (Om1 * a) + Om1 * Om1) :
    GxCl Z {gcG 0} (Om1 * (Om1 * a + q)) := by
  have hO0 : (Om1 : Ordinal.{0}) ≠ 0 := wh_Om1_pos.ne'
  set w := y / Om1
  have hw : GxCl Z {gcG 0} w := wt_cl_div hZ y hy
  have hw1 : w < Om1 * a + Om1 := by
    rw [← mul_add_one]
    refine (Ordinal.div_lt hO0).2 ?_
    calc y < Om1 * (Om1 * a) + Om1 * Om1 := hy2
    _ = Om1 * (Om1 * (a + 1)) := by rw [mul_add_one, mul_add]
  have hw2 : Om1 * a + q ≤ w := (Ordinal.le_div hO0).2 hLy
  obtain ⟨t, ht⟩ := exists_add_of_le (le_self_add.trans hw2 : Om1 * a ≤ w)
  have htO : t < Om1 := by rw [ht] at hw1; exact (add_lt_add_iff_left _).1 hw1
  have hqt : q ≤ t := by rw [ht] at hw2; exact (add_le_add_iff_left _).1 hw2
  have hwd : w / Om1 = a := by
    rw [ht, Ordinal.mul_add_div _ hO0, Ordinal.div_eq_zero_of_lt htO, add_zero]
  have ha : GxCl Z {gcG 0} a := hwd ▸ wt_cl_div hZ w hw
  have hOa : GxCl Z {gcG 0} (Om1 * a) := wt_cl_Om1_mul hZ a ha
  have htC : GxCl Z {gcG 0} t := by
    have e : w - Om1 * a = t := by rw [ht]; exact Ordinal.add_sub_cancel _ _
    rw [← e]
    exact (gxDec hZ wt_GxAt w hw).1 _ hOa (le_self_add.trans hw2)
  have htZ : t < Z := GxCl.lt_of_lt_Om1 hZ wt_GxAt htC (by rw [← Br.Om1_eq]; exact htO)
  exact wt_cl_Om1_mul hZ _ (GxCl.add hOa (GxCl.small (hqt.trans_lt htZ)))

end Googology.Trans.PoR.InaccPsi.R2.Wt
