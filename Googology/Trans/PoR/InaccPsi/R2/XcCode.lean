import Googology.Trans.PoR.InaccPsi.R2.WyLv
import Googology.Trans.PoR.InaccPsi.R2.WxTop

/-!
# XcCode: THE CODE INTERFACE OF REGION (A3) BELOW `t₀ = ε_{G+1}`

`G = Γ_{Ω₁+1}`, `t₀ = Wj.wjT 0`.  The hereditary code system `Wt.wtD = Go.goGl.step` reads every code `c < t₀`
(`G^k·d + r`, read with `Ω₁ ↦ x`, `G ↦ Γ_{x+1}`).  This module states it as a code interface `Ws.WsC`:

* `xg c = max 1 (wtD.g c)` (the gate; the convention of `Ws.wsA2`: equal to `Ws.gh` below `G`, `xg_low`);
* `xc_add_Om1` (**`R(a + Ω₁) x = R a x + x` and the gate laws of `a ↦ a + Ω₁`** for every `Ω₁ ∣ a < t₀`, by one
  induction on the normal form `G^k·d + r`);
* `xcA3 : WsC` (**THE (A3) CODE INTERFACE**: bound `t₀`, reading `wtD.R`, gate `xg`, outer low field `Wn.wnZo`);
* `xcR_low`, `xg_low` (below `G` it is `Ws.wsA2`).

No new axiom.  New definitions: `xg`, `xcA3`.
-/

set_option autoImplicit false

open Googology.Trans.PoR.InaccPsi.R2.Wm Googology.Trans.PoR.InaccPsi.R2.Wh Googology.Trans.PoR.InaccPsi.R2.Ho
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
open Googology.Trans.PoR.InaccPsi.R2.Wo Googology.Trans.PoR.InaccPsi.R2.Wn Googology.Trans.PoR.InaccPsi.R2.Wp
  Googology.Trans.PoR.InaccPsi.R2.Ws Googology.Trans.PoR.InaccPsi.R2.Wt Googology.Trans.PoR.InaccPsi.R2.Wy
  Googology.Trans.PoR.InaccPsi.R2.Wx

namespace Googology.Trans.PoR.InaccPsi.R2.Xc

/-- **THE (A3) GATE**: `max 1 (wtD.g c)`. -/
noncomputable def xg (c : Ordinal.{0}) : Ordinal.{0} := max 1 (wtD.g c)

theorem xg_lt_iff {c x : Ordinal.{0}} (hx : InE x) : xg c < x ↔ wtD.g c < x :=
  ⟨fun h => (le_max_right _ _).trans_lt h, fun h => max_lt (wo_one_lt_inE hx) h⟩

theorem xg_lt_SC {c Z : Ordinal.{0}} (hZ : SC Z) (h : wtD.g c < Z) : xg c < Z :=
  max_lt (one_lt_omega0.trans (wn_omega_lt_SC hZ)) h

theorem wtD_B_eq : wtD.B = Wj.wjT 0 := wtD_B

theorem xc_lt_B {c : Ordinal.{0}} (h : c < Wj.wjT 0) : c < wtD.B := by rw [wtD_B]; exact h

/-- Below `G` the reading is `glR`. -/
theorem xcR_low {c : Ordinal.{0}} (hc : c < gcG 0) (x : Ordinal.{0}) : wtD.R c x = glR c x :=
  goGl.step_R_low hc x

/-- Below `G` the gate is `glG`. -/
theorem xcG_low {c : Ordinal.{0}} (hc : c < gcG 0) : wtD.g c = glG c := goGl.step_g_low hc

/-- **Below `G` the (A3) gate is the (A2) gate `gh`.** -/
theorem xg_low {c : Ordinal.{0}} (hc : c < gcG 0) : xg c = gh c := by unfold xg gh; rw [xcG_low hc]

theorem xc_t0_E : InE (Wj.wjT 0) := wnT0_E

theorem xc_G_lt_t0 : gcG 0 < Wj.wjT 0 := (Wj.wjT_spec 0).1

theorem xc_Om1_dvd_pow {k : Ordinal.{0}} (hk : k ≠ 0) : Om1 ∣ gcG 0 ^ k := by
  rw [show gcG 0 ^ k = ω ^ (gcG 0 * k) by rw [opow_mul, gl_G0_E]]
  exact wt_dvd_opow (gl_Om1_lt_G0.le.trans (Ordinal.le_mul_left _ (pos_iff_ne_zero.2 hk)))

theorem xc_Om1_lt_pow {k : Ordinal.{0}} (hk : k ≠ 0) : Om1 < gcG 0 ^ k :=
  gl_Om1_lt_G0.trans_le (by
    calc gcG 0 = gcG 0 ^ (1 : Ordinal.{0}) := (opow_one _).symm
    _ ≤ gcG 0 ^ k := opow_le_opow_right gl_G0_E.pos (one_le_iff_ne_zero.2 hk))

/-- **`R(a + Ω₁) = R a + x` and the gate laws of `a ↦ a + Ω₁`** for every `Ω₁ ∣ a < t₀`. -/
theorem xc_add_Om1 : ∀ a, a < Wj.wjT 0 → Om1 ∣ a →
    (∀ x, wtD.R (a + Om1) x = wtD.R a x + x) ∧ wtD.g a ≤ wtD.g (a + Om1) ∧
      ∀ x, InE x → wtD.g a < x → wtD.g (a + Om1) < x := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IH =>
  intro ha hd
  rcases lt_or_ge a (gcG 0) with haG | haG
  · have haO : a + Om1 < gcG 0 := (inE_indec gl_G0_E).add_lt haG gl_Om1_lt_G0
    refine ⟨fun x => ?_, ?_, fun x hx hg => ?_⟩
    · rw [xcR_low haO, xcR_low haG]; exact (wn_glR_add_Om1 a haG hd x).1
    · rw [xcG_low haO, xcG_low haG]; exact (wn_glR_add_Om1 a haG hd 0).2
    · rw [xcG_low haO]; rw [xcG_low haG] at hg; exact wn_glG_add_Om1_lt hx haG hg
  -- `a = G^k·d + r`
  have hB : goGl.B ≤ a := haG
  have hNB : a < goGl.NB := xc_lt_B ha
  obtain ⟨hk, hd0, hdE, hr, hdec, hka, hra⟩ := goGl.parts hB hNB
  set k := log (goGl.B) a
  set d := a / goGl.B ^ k
  set r := a % goGl.B ^ k
  have hBG : goGl.B = gcG 0 := rfl
  have hA : Om1 ∣ goGl.B ^ k * d := Dvd.dvd.mul_right (xc_Om1_dvd_pow hk) _
  have hrd : Om1 ∣ r := (Ordinal.dvd_add_iff hA).1 (by rw [hdec]; exact hd)
  have hrO : r + Om1 < goGl.B ^ k := goGl.pow_indec r Om1 hr (xc_Om1_lt_pow hk)
  have hsum : a + Om1 = goGl.B ^ k * d + (r + Om1) := by rw [← add_assoc, hdec]
  have haO : a + Om1 < goGl.NB := (inE_indec goGl.NB_E).add_lt hNB (gl_Om1_lt_G0.trans goGl.B_lt_NB)
  have hcnf : goGl.B ^ k * d + (r + Om1) < goGl.NB := hsum ▸ haO
  have hcnf0 : goGl.B ^ k * d + r < goGl.NB := hdec.symm ▸ hNB
  obtain ⟨IR, Ig, Il⟩ := IH r hra (hra.trans ha) hrd
  have eR : ∀ x, wtD.R a x = goGl.b x ^ goGl.hR k x * goGl.R d x + goGl.hR r x := fun x => by
    show goGl.hR a x = _
    conv_lhs => rw [← hdec]
    exact goGl.hR_cnf hk hd0 hdE hr hcnf0 x
  have eR' : ∀ x, wtD.R (a + Om1) x = goGl.b x ^ goGl.hR k x * goGl.R d x + goGl.hR (r + Om1) x := fun x => by
    show goGl.hR (a + Om1) x = _
    rw [hsum]; exact goGl.hR_cnf hk hd0 hdE hrO hcnf x
  have eG : wtD.g a = max (max (goGl.hQ k) (goGl.Q d)) (goGl.hG r) := by
    show goGl.hG a = _
    conv_lhs => rw [← hdec]
    exact goGl.hG_cnf hk hd0 hdE hr hcnf0
  have eG' : wtD.g (a + Om1) = max (max (goGl.hQ k) (goGl.Q d)) (goGl.hG (r + Om1)) := by
    show goGl.hG (a + Om1) = _
    rw [hsum]; exact goGl.hG_cnf hk hd0 hdE hrO hcnf
  refine ⟨fun x => ?_, ?_, fun x hx hg => ?_⟩
  · rw [eR', eR, add_assoc]; congr 1; exact IR x
  · rw [eG, eG']; exact max_le_max le_rfl Ig
  · rw [eG] at hg; rw [eG']
    exact max_lt (max_lt_iff.1 hg).1 (Il x hx (max_lt_iff.1 hg).2)

theorem xcR_Om1 (x : Ordinal.{0}) : wtD.R Om1 x = x := by
  rw [xcR_low gl_Om1_lt_G0, glR_low Om1_lt_eW, (rdc_Om1 x).1]

theorem xcG_Om1 : wtD.g Om1 = 1 := by rw [xcG_low gl_Om1_lt_G0, glG_low Om1_lt_eW, (rdc_Om1 0).2]

theorem xc_one_lt_t0 : (1 : Ordinal.{0}) < Wj.wjT 0 := wh_one_lt_Om1.trans wnT0_Om1_lt

/-- **THE (A3) CODE INTERFACE**: bound `t₀ = ε_{G+1}`, reading `wtD.R`, gate `xg = max 1 wtD.g`, outer low field
`Wn.wnZo`. -/
noncomputable def xcA3 : WsC where
  Bd := Wj.wjT 0
  R := wtD.R
  g := xg
  Zo := wnZo
  Om1_lt := wnT0_Om1_lt
  Bd_lt1 := (Wj.wjT_spec 0).2.1
  add_lt := fun _ _ ha hb => (inE_indec xc_t0_E).add_lt ha hb
  g_lt := fun a ha => max_lt wh_one_lt_Om1 (wtD.g_lt a (xc_lt_B ha))
  R_Om1 := xcR_Om1
  g_Om1 := by unfold xg; rw [xcG_Om1, max_self]
  succ_R := fun a ha hd x => (xc_add_Om1 a ha hd).1 x
  succ_g := fun a ha hd => max_le_max le_rfl (xc_add_Om1 a ha hd).2.1
  succ_g_lt := fun hx ha hd hg => (xg_lt_iff hx).2 ((xc_add_Om1 _ ha hd).2.2 _ hx ((xg_lt_iff hx).1 hg))
  g_succ1 := fun {x t} hx ht hg => (xg_lt_iff hx).2 (wtD.g_succ x (ev_isSuccLimit_of_inE hx) t
    (xc_lt_B ((inE_indec xc_t0_E).add_lt ht xc_one_lt_t0)) ((xg_lt_iff hx).1 hg))
  le_R := fun {x ℓ} hx hx1 h1 hB hg => by
    rcases h1.lt_or_eq with h | h
    · have := wtD.mono x hx hx1 ℓ (xc_lt_B hB) Om1 h ((xg_lt_iff hx).1 hg)
        (by rw [xcG_Om1]; exact wo_one_lt_inE hx)
      rw [xcR_Om1] at this; exact this.le
    · rw [← h, xcR_Om1]
  R_lt := fun hx hx1 hB hg => goGl.hR_lt1 hx hx1 (xc_lt_B hB) ((xg_lt_iff hx).1 hg)
  R_mono := fun hx hx1 hc hbc hgc hgb =>
    wtD.mono _ hx hx1 _ (xc_lt_B hc) _ hbc ((xg_lt_iff hx).1 hgc) ((xg_lt_iff hx).1 hgb)
  R_cof := fun hx hx1 hc hg ν hν => by
    obtain ⟨b, hb, hgb, hνb⟩ := wtD.cof _ hx hx1 _ (xc_lt_B hc) ((xg_lt_iff hx).1 hg) ν hν
    exact ⟨b, hb, (xg_lt_iff hx).2 hgb, hνb⟩
  R_pi := fun hB ha hg => wtD.ex _ _ hB _ (xc_lt_B ha) ((xg_lt_iff hB.1).1 hg)
  g_cl := fun ℓ _ h2 h3 Z y hZ hZ1 hy hLy hy2 => by
    rw [← Br.Om1_eq] at hy2
    have hLe := (wh_L_dec h2).1
    have hLC : GxCl Z {gcG 0} ℓ := by
      rw [hLe, ← mul_add]
      rw [hLe, ← mul_add] at hLy
      exact wt_cl_head hZ hy hLy hy2
    have hZ1' : Z ≤ Om1 := by rw [Br.Om1_eq]; exact hZ1
    exact xg_lt_SC hZ (wtD.code_gate Z hZ1' hZ.1 (fun u v hu hv => hZ.isPrincipal hu hv)
      (fun u v hu hv => hZ.2 u hu v hv) {gcG 0} (fun s hs => Or.inl hs) ℓ hLC (xc_lt_B h3))
  L_mem := fun ℓ h S a b ha hb => (wtD.mem S a b ha ℓ (xc_lt_B h) ((le_max_right _ _).trans_lt hb)).1
  Zo_fix := wnZo_fix
  Zo_G1 := fun _ hx hx1 => wnZo_G1 hx hx1

theorem xcA3_Bd : xcA3.Bd = Wj.wjT 0 := rfl

theorem xcA3_R : xcA3.R = wtD.R := rfl

theorem xcA3_g : xcA3.g = xg := rfl

/-- **The towers are levels of `xcA3`.** -/
theorem xc_lev_tw (n : ℕ) : xcA3.Lev (wtTw n) := ⟨(gl_Om1_lt_G0.trans (wtTw_G n)).le, wtTw_dvd n, wtTw_lt n⟩

theorem xg_tw (n : ℕ) : xg (wtTw n) = 1 := by unfold xg; rw [wtTw_g, max_eq_left zero_le]

/-- The reading of the tower datum at an `ε`-number. -/
theorem xc_tw_l (n : ℕ) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    (xcA3.lv (wtTw n) (xc_lev_tw n)).l x = wtD.R (wtTw n) x :=
  xcA3.lv_l (xc_lev_tw n) hx hx1 (by rw [xcA3_g, xg_tw]; exact wo_one_lt_inE hx)

end Googology.Trans.PoR.InaccPsi.R2.Xc
