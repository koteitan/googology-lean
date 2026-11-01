import Googology.Trans.PoR.InaccPsi.R2.XuGate

/-!
# XuC: THE (A3) CODE INTERFACE BELOW EVERY `ε`-NUMBER BOUND `B ∈ [t₀, Γ(1))`

`R2.Xu*` read every code `c < Γ(1)` (`xuR`, `xuG`).  This module states the reading as a code interface `Ws.WsC`
once for every bound `B`: an `ε`-number with `t₀ ≤ B < Γ(1)` (`t_n = Wj.wjT n` for every `n`, `xuCn`).

* `xu_add_Om1` (**`R(a + Ω₁) x = R a x + x` and the gate laws of `a ↦ a + Ω₁`** for every `Ω₁ ∣ a < Γ(1)`);
* `xuGg` (the gate `max 1 xuG`, the convention of `Xc.xg`), `xuC` (**THE (A3) CODE INTERFACE BELOW `B`**: reading
  `xuR`, gate `xuGg`, outer low field `Wn.wnZo`), `xuCn n` (bound `t_n`), `xuC_low` (**below `t₀` the reading and the
  gate are those of `Xc.xcA3`**).

No new axiom.  New definitions: `xuGg`, `xuC`, `xuCn`.
-/

set_option autoImplicit false

open Googology.Trans.PoR.InaccPsi.R2.Wm Googology.Trans.PoR.InaccPsi.R2.Wh Googology.Trans.PoR.InaccPsi.R2.Ho
open Googology.Trans.PoR.InaccPsi.R2.Hn Googology.Trans.PoR.InaccPsi.R2.Hl
open Googology.Trans.PoR.InaccPsi.R2.Hg Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Gf
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb
  Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gk
open Googology.Trans.PoR.InaccPsi.R2.Wo Googology.Trans.PoR.InaccPsi.R2.Wn Googology.Trans.PoR.InaccPsi.R2.Ws
  Googology.Trans.PoR.InaccPsi.R2.Wt Googology.Trans.PoR.InaccPsi.R2.Xc

namespace Googology.Trans.PoR.InaccPsi.R2.Xu

/-- **`R(a + Ω₁) = R a + x` and the gate laws of `a ↦ a + Ω₁`** for every `Ω₁ ∣ a < Γ(1)`. -/
theorem xu_add_Om1 : ∀ a, a < gcG 1 → Om1 ∣ a →
    (∀ x, xuR (a + Om1) x = xuR a x + x) ∧ xuG a ≤ xuG (a + Om1) ∧
      ∀ x, InE x → xuG a < x → xuG (a + Om1) < x := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IH =>
  intro ha hd
  rcases lt_or_ge a (Wj.wjT 0) with hat | hat
  · have haO : a + Om1 < Wj.wjT 0 := (inE_indec xu_t0_E).add_lt hat xu_Om1_lt_t0
    obtain ⟨h1, h2, h3⟩ := xc_add_Om1 a hat hd
    refine ⟨fun x => ?_, ?_, fun x hx hg => ?_⟩
    · rw [xuR_low haO, xuR_low hat]; exact h1 x
    · rw [xuG_low haO, xuG_low hat]; exact h2
    · rw [xuG_low haO]; rw [xuG_low hat] at hg; exact h3 x hx hg
  have haE := xu_gfE_le hat
  obtain ⟨hk, hd0, hdE, hr, hdec, hka, hra, -⟩ := gl_parts haE
  set E := guE a with hEdef
  have hE : InE E := guE_E a
  have hEt : Wj.wjT 0 ≤ E := xu_E_ge hat
  set k := log E a
  set d := a / E ^ k
  set r := a % E ^ k
  have hOE : Om1 < E := xu_Om1_lt_t0.trans_le hEt
  have hEk : E ≤ E * k := le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hk)
  have hpow : E ^ k = ω ^ (E * k) := gu_pow_eq hE k
  have hA : Om1 ∣ E ^ k * d := by
    rw [hpow]; exact Dvd.dvd.mul_right (wt_dvd_opow (hOE.le.trans hEk)) _
  have hrd : Om1 ∣ r := (Ordinal.dvd_add_iff hA).1 (by rw [hdec]; exact hd)
  have hOk : Om1 < E ^ k := by rw [hpow]; exact (hOE.trans_le hEk).trans_le (right_le_opow _ one_lt_omega0)
  have hrO : r + Om1 < E ^ k := by
    rw [hpow] at hr hOk ⊢; exact isPrincipal_add_omega0_opow _ hr hOk
  have hsum : a + Om1 = E ^ k * d + (r + Om1) := by rw [← add_assoc, hdec]
  have haN : a < eN E := gl_lt_eN haE
  have haO : a + Om1 < eN E := (inE_indec (eN_E E)).add_lt haN (hOE.trans (lt_eN E))
  have haOB : a + Om1 < gcG 1 := (inE_indec xu_G1_E).add_lt ha xu_Om1_lt_G1
  have hcnf : E ^ k * d + (r + Om1) < eN E := hsum ▸ haO
  have hcnf0 : E ^ k * d + r < eN E := hdec.symm ▸ haN
  obtain ⟨IR, Ig, Il⟩ := IH r hra (hra.trans ha) hrd
  have eR : ∀ x, xuR a x = glA (xuR (xuK E) x) (xuR (xuI E) x) x ^ xuR k x * xuR d x + xuR r x := fun x => by
    conv_lhs => rw [← hdec]
    exact xuR_cnf hE hEt hk hd0 hdE hr hcnf0 (hdec.symm ▸ ha) x
  have eR' : ∀ x, xuR (a + Om1) x =
      glA (xuR (xuK E) x) (xuR (xuI E) x) x ^ xuR k x * xuR d x + xuR (r + Om1) x := fun x => by
    rw [hsum]; exact xuR_cnf hE hEt hk hd0 hdE hrO hcnf (hsum ▸ haOB) x
  have eG : xuG a = max (max (xuQE E) (xuQ k)) (max (xuQ d) (xuG r)) := by
    conv_lhs => rw [← hdec]
    exact xuG_cnf hE hEt hk hd0 hdE hr hcnf0 (hdec.symm ▸ ha)
  have eG' : xuG (a + Om1) = max (max (xuQE E) (xuQ k)) (max (xuQ d) (xuG (r + Om1))) := by
    rw [hsum]; exact xuG_cnf hE hEt hk hd0 hdE hrO hcnf (hsum ▸ haOB)
  refine ⟨fun x => ?_, ?_, fun x hx hg => ?_⟩
  · rw [eR', eR, add_assoc]; congr 1; exact IR x
  · rw [eG, eG']; exact max_le_max le_rfl (max_le_max le_rfl Ig)
  · rw [eG] at hg; rw [eG']
    exact max_lt (max_lt_iff.1 hg).1 (max_lt (max_lt_iff.1 (max_lt_iff.1 hg).2).1
      (Il x hx (max_lt_iff.1 (max_lt_iff.1 hg).2).2))

/-- **The (A3) gate**: `max 1 xuG`. -/
noncomputable def xuGg (c : Ordinal.{0}) : Ordinal.{0} := max 1 (xuG c)

theorem xuGg_lt_iff {c x : Ordinal.{0}} (hx : InE x) : xuGg c < x ↔ xuG c < x :=
  ⟨fun h => (le_max_right _ _).trans_lt h, fun h => max_lt (wo_one_lt_inE hx) h⟩

theorem xuGg_lt_SC {c Z : Ordinal.{0}} (hZ : SC Z) (h : xuG c < Z) : xuGg c < Z :=
  max_lt (one_lt_omega0.trans (wn_omega_lt_SC hZ)) h

/-- **Below `t₀` the gate is `Xc.xg`.** -/
theorem xuGg_low {c : Ordinal.{0}} (hc : c < Wj.wjT 0) : xuGg c = xg c := by
  unfold xuGg xg; rw [xuG_low hc]

theorem xuR_Om1 (x : Ordinal.{0}) : xuR Om1 x = x := by rw [xuR_low xu_Om1_lt_t0]; exact xcR_Om1 x

theorem xuG_Om1 : xuG Om1 = 1 := by rw [xuG_low xu_Om1_lt_t0]; exact xcG_Om1

/-- **THE (A3) CODE INTERFACE BELOW AN `ε`-NUMBER BOUND `B ∈ [t₀, Γ(1))`**: reading `xuR`, gate `xuGg`, outer low
field `Wn.wnZo`. -/
noncomputable def xuC (B : Ordinal.{0}) (hBE : InE B) (hBt : Wj.wjT 0 ≤ B) (hB1 : B < gcG 1) : WsC where
  Bd := B
  R := xuR
  g := xuGg
  Zo := wnZo
  Om1_lt := xu_Om1_lt_t0.trans_le hBt
  Bd_lt1 := hB1
  add_lt := fun _ _ ha hb => (inE_indec hBE).add_lt ha hb
  g_lt := fun a ha => max_lt wh_one_lt_Om1 (xuG_lt_Om1 a (ha.trans hB1))
  R_Om1 := xuR_Om1
  g_Om1 := by unfold xuGg; rw [xuG_Om1, max_self]
  succ_R := fun a ha hd x => (xu_add_Om1 a (ha.trans hB1) hd).1 x
  succ_g := fun a ha hd => max_le_max le_rfl (xu_add_Om1 a (ha.trans hB1) hd).2.1
  succ_g_lt := fun hx ha hd hg =>
    (xuGg_lt_iff hx).2 ((xu_add_Om1 _ (ha.trans hB1) hd).2.2 _ hx ((xuGg_lt_iff hx).1 hg))
  g_succ1 := fun {x t} hx ht hg => (xuGg_lt_iff hx).2 (xuG_succ (ev_isSuccLimit_of_inE hx) t
    (((inE_indec hBE).add_lt ht (xu_one_lt_inE hBE)).trans hB1) ((xuGg_lt_iff hx).1 hg))
  le_R := fun {x ℓ} hx hx1 h1 hB hg => by
    rcases h1.lt_or_eq with h | h
    · have := xuR_mono hx hx1 (hB.trans hB1) h ((xuGg_lt_iff hx).1 hg)
        (by rw [xuG_Om1]; exact wo_one_lt_inE hx)
      rw [xuR_Om1] at this; exact this.le
    · rw [← h, xuR_Om1]
  R_lt := fun hx hx1 hB hg => xuR_lt1 hx hx1 (hB.trans hB1) ((xuGg_lt_iff hx).1 hg)
  R_mono := fun hx hx1 hc hbc hgc hgb =>
    xuR_mono hx hx1 (hc.trans hB1) hbc ((xuGg_lt_iff hx).1 hgc) ((xuGg_lt_iff hx).1 hgb)
  R_cof := fun hx hx1 hc hg ν hν => by
    obtain ⟨b, hb, hgb, hνb⟩ := xuR_cof hx hx1 _ (hc.trans hB1) ((xuGg_lt_iff hx).1 hg) ν hν
    exact ⟨b, hb, (xuGg_lt_iff hx).2 hgb, hνb⟩
  R_pi := fun hB ha hg => xu_pi hB _ (ha.trans hB1) ((xuGg_lt_iff hB.1).1 hg)
  g_cl := fun ℓ _ h2 h3 Z y hZ hZ1 hy hLy hy2 => by
    rw [← Br.Om1_eq] at hy2
    have hLe := (wh_L_dec h2).1
    have hLC : GxCl Z {gcG 0} ℓ := by
      rw [hLe, ← mul_add]
      rw [hLe, ← mul_add] at hLy
      exact wt_cl_head hZ hy hLy hy2
    have hZ1' : Z ≤ Om1 := by rw [Br.Om1_eq]; exact hZ1
    exact xuGg_lt_SC hZ (xu_code_gate hZ hZ1' ℓ hLC (h3.trans hB1))
  L_mem := fun ℓ h S a b ha hb => (xu_mem ha ℓ (h.trans hB1) ((le_max_right _ _).trans_lt hb)).1
  Zo_fix := wnZo_fix
  Zo_G1 := fun _ hx hx1 => wnZo_G1 hx hx1

theorem xuC_Bd {B : Ordinal.{0}} (hBE : InE B) (hBt : Wj.wjT 0 ≤ B) (hB1 : B < gcG 1) :
    (xuC B hBE hBt hB1).Bd = B := rfl

theorem xuC_R {B : Ordinal.{0}} (hBE : InE B) (hBt : Wj.wjT 0 ≤ B) (hB1 : B < gcG 1) :
    (xuC B hBE hBt hB1).R = xuR := rfl

theorem xuC_g {B : Ordinal.{0}} (hBE : InE B) (hBt : Wj.wjT 0 ≤ B) (hB1 : B < gcG 1) :
    (xuC B hBE hBt hB1).g = xuGg := rfl

/-- **Below `t₀` the interface is `Xc.xcA3`** (same reading, same gate). -/
theorem xuC_low {B : Ordinal.{0}} (hBE : InE B) (hBt : Wj.wjT 0 ≤ B) (hB1 : B < gcG 1) {c : Ordinal.{0}}
    (hc : c < Wj.wjT 0) : (xuC B hBE hBt hB1).R c = xcA3.R c ∧ (xuC B hBE hBt hB1).g c = xcA3.g c :=
  ⟨funext fun x => xuR_low hc x, xuGg_low hc⟩

/-- **The interface with bound `t_n`.** -/
noncomputable def xuCn (n : ℕ) : WsC :=
  xuC (Wj.wjT n) (Wj.wjT_spec n).2.2.1 (Wj.wjT_mono (Nat.zero_le n)) (Wj.wjT_spec n).2.1

theorem xuCn_Bd (n : ℕ) : (xuCn n).Bd = Wj.wjT n := rfl

end Googology.Trans.PoR.InaccPsi.R2.Xu
