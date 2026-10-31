import Googology.Trans.PoR.InaccPsi.R2.WhSucc
import Googology.Trans.PoR.InaccPsi.R2.WjVeb

/-!
# WnLv: THE SMALL LEAVES OF REGION (A2): shape, the level datum, the gate of the cofinal levels

The levels of region (A2) are the codes `ℓ` with `Ω₁ ≤ ℓ`, `Ω₁ ∣ ℓ`, `ℓ < G = Γ_{Ω₁+1}` (Cantor normal form over
`ε`-number codes, read by `Gl.glR`, gate `Gl.glG`).  This module proves, with no hypothesis:

* `wnShape` (**the five shapes of a level `< G`**: `Ω₁`, `ℓ' + Ω₁`, `P + Ω₁^{e+1}`, `P + Ω₁^e` with `e` a limit,
  `P + Ω₁^e·c` with `c < Ω₁` a limit);
* `wn_glR_add_Om1` (**`glR (a + Ω₁) x = glR a x + x`**, `glG a ≤ glG (a + Ω₁)`), `wn_glG_add_Om1_lt`,
  `wn_glR_step` (**`glR a x + x ≤ glR b x`** for levels `a < b < G` with gates below `x`);
* `wn_glG_div` (`glG (y/Ω₁) < Z` and `(y/Ω₁) mod Ω₁ < Z` from `glG y < Z`), `wn_glG_Om1_mul`
  (`glG (Ω₁·b) < Z` from `glG b < Z`);
* `wnLv` (**THE LEVEL DATUM OF EVERY LEVEL BELOW `G`**: an `Hn.HnLv` with `L = ℓ`, gate `glG ℓ`, reading
  `glR ℓ x` above the gate), `wnLvDatumAll`;
* `wnGateBn` (**the cofinal levels `Gl.glBn n` have gate below `Γ₀`**).

No new axiom.  New definitions: `wnRd`, `wnLv`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wn

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
open Googology.Trans.PoR.InaccPsi.R2.Wh Googology.Trans.PoR.InaccPsi.R2.Gk

/-! ## The shape of a level below `G` -/

/-- **THE FIVE SHAPES OF A LEVEL** `Ω₁ ≤ ℓ`, `Ω₁ ∣ ℓ`, `ℓ < G` (`Wh.whShape` with the bound `G`). -/
theorem wnShape (ℓ : Ordinal.{0}) (h1 : Om1 ≤ ℓ) (h2 : Om1 ∣ ℓ) (h3 : ℓ < gcG 0) :
    ℓ = Om1 ∨ (∃ ℓ', (Om1 ≤ ℓ' ∧ Om1 ∣ ℓ' ∧ ℓ' < gcG 0) ∧ ℓ = ℓ' + Om1) ∨
      (∃ (P e : Ordinal.{0}), 1 ≤ e ∧ Om1 ^ (e + 1) ∣ P ∧ ℓ = P + Om1 ^ (e + 1)) ∨
      (∃ (P e : Ordinal.{0}), IsSuccLimit e ∧ Om1 ^ e ∣ P ∧ ℓ = P + Om1 ^ e) ∨
      (∃ (P e c : Ordinal.{0}), 1 ≤ e ∧ IsSuccLimit c ∧ c < Om1 ∧ Om1 ^ (e + 1) ∣ P ∧
        ℓ = P + Om1 ^ e * c) := by
  have hℓ0 : ℓ ≠ 0 := (wh_Om1_pos.trans_le h1).ne'
  obtain ⟨P, e, c, hc0, hc, hP, hℓ⟩ := wh_last_term ℓ hℓ0
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [zero_add, opow_one] at hP
    rw [opow_zero, one_mul] at hℓ
    have hdc : Om1 ∣ c := (Ordinal.dvd_add_iff hP).1 (hℓ ▸ h2)
    exact absurd (Ordinal.le_of_dvd hc0.ne' hdc) (not_le.2 hc)
  have he1 : 1 ≤ e := Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 he0)
  have hPe : Om1 ^ e ∣ P := (opow_dvd_opow _ (le_self_add)).trans hP
  rcases zero_or_succ_or_isSuccLimit c with hc' | ⟨c', hcs⟩ | hcl
  · exact absurd hc' hc0.ne'
  · rw [← Ordinal.add_one_eq_succ] at hcs; subst hcs
    have hℓ' : ℓ = P + Om1 ^ e * c' + Om1 ^ e := by rw [hℓ, mul_add_one, add_assoc]
    have hP' : Om1 ^ e ∣ P + Om1 ^ e * c' := dvd_add hPe (dvd_mul_right _ _)
    rcases zero_or_succ_or_isSuccLimit e with he' | ⟨e', hes⟩ | hel
    · exact absurd he' he0
    · rw [← Ordinal.add_one_eq_succ] at hes; subst hes
      rcases eq_or_ne e' 0 with rfl | he'0
      · rw [zero_add, opow_one] at hℓ' hP'
        rcases eq_or_ne (P + Om1 * c') 0 with hz | hz
        · left; rw [hℓ', hz, zero_add]
        · right; left
          refine ⟨P + Om1 * c', ⟨Ordinal.le_of_dvd hz hP', hP', ?_⟩, hℓ'⟩
          exact (lt_add_of_pos_right _ wh_Om1_pos).trans_le (hℓ' ▸ le_rfl) |>.trans h3
      · right; right; left
        exact ⟨P + Om1 ^ (e' + 1) * c', e', Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 he'0), hP', hℓ'⟩
    · right; right; right; left
      exact ⟨P + Om1 ^ e * c', e, hel, hP', hℓ'⟩
  · right; right; right; right
    exact ⟨P, e, c, he1, hcl, hc, hP, hℓ⟩

/-! ## Codes below `G`: adding `Ω₁`, dividing by `Ω₁`, multiplying by `Ω₁` -/

theorem wn_div_le (a : Ordinal.{0}) : a / Om1 ≤ a := Ordinal.div_le_of_le_mul (le_mul_right a wh_Om1_pos)

/-- `Ω₁ ∣ e^j` and `Ω₁·e^j = e^j` for an `ε`-number `e > Ω₁` and `j ≠ 0`. -/
theorem wn_Om1_mul_pow {e j : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) (hj : j ≠ 0) : Om1 * e ^ j = e ^ j := by
  have hj1 : 1 ≤ j := one_le_iff_ne_zero.2 hj
  have h1 : Om1 < ω ^ e := by rw [he]; exact hOe
  have h2 : ω ^ e ≤ e * j := by rw [he]; exact le_mul_of_one_le_right' hj1
  conv_lhs => rw [← gl_Om1_E]
  rw [gu_pow_eq he, ← opow_add, add_absorp h1 h2]

theorem wn_Om1_lt_pow {e j : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) (hj : j ≠ 0) : Om1 < e ^ j :=
  hOe.trans_le (left_le_opow e (pos_iff_ne_zero.2 hj))

/-- **`glR (a + Ω₁) x = glR a x + x`** and `glG a ≤ glG (a + Ω₁)` for a multiple `a` of `Ω₁` below `G`. -/
theorem wn_glR_add_Om1 : ∀ a, a < gcG 0 → Om1 ∣ a → ∀ x, glR (a + Om1) x = glR a x + x ∧
    glG a ≤ glG (a + Om1) := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IH =>
  intro haB hd x
  rcases lt_or_ge a gfE with haE | haE
  · have hE' : a + Om1 < gfE := eW_indec.add_lt haE Om1_lt_eW
    rw [glR_low hE', glR_low haE, glG_low haE, glG_low hE']
    exact wh_rdc_add_Om1 a haE hd x
  obtain ⟨hk, hd0, hdE, hr, hdec, -, hra, -⟩ := gl_parts haE
  have hE : InE (guE a) := guE_E a
  have hOe : Om1 < guE a := gl_Om1_lt_E haE
  have hOej : Om1 ∣ guE a ^ log (guE a) a := by
    rw [← wn_Om1_mul_pow hE hOe hk]; exact dvd_mul_right _ _
  have hdr : Om1 ∣ a % guE a ^ log (guE a) a :=
    (Ordinal.dvd_add_iff (Dvd.dvd.mul_right hOej _)).1 (by rw [hdec]; exact hd)
  have hrO : a % guE a ^ log (guE a) a + Om1 < guE a ^ log (guE a) a := by
    have hp := wn_Om1_lt_pow hE hOe hk
    rw [gu_pow_eq hE] at hr hp ⊢
    exact isPrincipal_add_omega0_opow _ hr hp
  have e1 : a + Om1 = guE a ^ log (guE a) a * (a / guE a ^ log (guE a) a) +
      (a % guE a ^ log (guE a) a + Om1) := by rw [← add_assoc, hdec]
  have hv : guE a ^ log (guE a) a * (a / guE a ^ log (guE a) a) + (a % guE a ^ log (guE a) a + Om1) <
      eN (guE a) := by
    rw [← e1]; exact (inE_indec (eN_E _)).add_lt (gl_lt_eN haE) (hOe.trans (lt_eN _))
  have hB' : guE a ^ log (guE a) a * (a / guE a ^ log (guE a) a) + (a % guE a ^ log (guE a) a + Om1) <
      gcG 0 := by
    rw [← e1]; exact (inE_indec gl_G0_E).add_lt haB gl_Om1_lt_G0
  obtain ⟨i1, i2⟩ := IH _ hra (hra.trans haB) hdr x
  rw [e1, glR_cnf hE hOe hk hd0 hdE hrO hv hB' x, i1, glR_dec haE haB x,
    glG_cnf hE hOe hk hd0 hdE hrO hv hB', glG_dec haE haB, add_assoc]
  exact ⟨rfl, max_le_max le_rfl (max_le_max le_rfl i2)⟩

/-- **`glG (a + Ω₁) < x`** from `glG a < x` at an `ε`-number `x`. -/
theorem wn_glG_add_Om1_lt {x a : Ordinal.{0}} (hx : InE x) (haB : a < gcG 0) (hg : glG a < x) :
    glG (a + Om1) < x := by
  refine gl_add (fun _ _ hu hv => (inE_indec hx).add_lt hu hv) (omega0_lt_inE hx) a Om1
    ((inE_indec gl_G0_E).add_lt haB gl_Om1_lt_G0) hg ?_
  rw [glG_low Om1_lt_eW, (rdc_Om1 0).2]; exact one_lt_omega0.trans (omega0_lt_inE hx)

/-- **`glR a x + x ≤ glR b x`** for levels `a < b < G` with gates below the `ε`-number `x < Ω₁`. -/
theorem wn_glR_step {x a b : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (ha : Om1 ∣ a) (hb : Om1 ∣ b)
    (hab : a < b) (hbB : b < gcG 0) (hga : glG a < x) (hgb : glG b < x) : glR a x + x ≤ glR b x := by
  rw [← (wn_glR_add_Om1 a (hab.trans hbB) ha x).1]
  rcases (wh_lev_succ_le ha hb hab).lt_or_eq with h | h
  · exact (glR_mono hx hx1 hbB h hgb (wn_glG_add_Om1_lt hx (hab.trans hbB) hga)).le
  · rw [h]

/-- **`glG (y/Ω₁) < Z` and `(y/Ω₁) mod Ω₁ < Z`** from `glG y < Z`, for `y < G` and `Z > ω`. -/
theorem wn_glG_div {Z : Ordinal.{0}} (hωZ : ω < Z) : ∀ y, y < gcG 0 → glG y < Z →
    glG (y / Om1) < Z ∧ (y / Om1) % Om1 < Z := by
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hyB hg
  rcases lt_or_ge y gfE with hyE | hyE
  · have hwE : y / Om1 < gfE := (wn_div_le y).trans_lt hyE
    rw [glG_low hyE] at hg
    rw [glG_low hwE]
    obtain ⟨g1, -⟩ := gtc_div y hyE
    obtain ⟨-, g2⟩ := gtc_div (y / Om1) hwE
    exact ⟨g1.trans_lt hg, (g2.trans g1).trans_lt hg⟩
  obtain ⟨hk, hd0, hdE, hr, hdec, -, hry, -⟩ := gl_parts hyE
  obtain ⟨q0n, q0a, q0d, g0r⟩ := gl_parts_Q hyE hyB hg
  have hE : InE (guE y) := guE_E y
  have hOe : Om1 < guE y := gl_Om1_lt_E hyE
  have hOm := wn_Om1_mul_pow hE hOe hk
  have hO0 : (Om1 : Ordinal.{0}) ≠ 0 := wh_Om1_pos.ne'
  set e := guE y
  set j := log e y
  set d := y / e ^ j
  set r := y % e ^ j
  have hy : y = Om1 * (e ^ j * d) + r := by rw [← mul_assoc, hOm, hdec]
  have hdiv : y / Om1 = e ^ j * d + r / Om1 := by
    conv_lhs => rw [hy]
    rw [Ordinal.mul_add_div _ hO0]
  have hrq : r / Om1 < e ^ j := (wn_div_le r).trans_lt hr
  have hle : y / Om1 ≤ y := wn_div_le y
  have hv : e ^ j * d + r / Om1 < eN e := by rw [← hdiv]; exact hle.trans_lt (gl_lt_eN hyE)
  have hB : e ^ j * d + r / Om1 < gcG 0 := by rw [← hdiv]; exact hle.trans_lt hyB
  obtain ⟨i1, i2⟩ := IH r hry (hry.trans hyB) g0r
  refine ⟨?_, ?_⟩
  · rw [hdiv, glG_cnf hE hOe hk hd0 hdE hrq hv hB]
    exact max_lt (max_lt q0n q0a) (max_lt q0d i1)
  · rw [hdiv]
    have : e ^ j * d = Om1 * (e ^ j * d) := by rw [← mul_assoc, hOm]
    rw [this, Ordinal.mul_add_mod_self]
    exact i2

/-- **`glG (Ω₁·b) < Z`** from `glG b < Z`, for `b < G` and a limit `Z > ω`. -/
theorem wn_glG_Om1_mul {Z : Ordinal.{0}} (hZ : IsSuccLimit Z) (hωZ : ω < Z) :
    ∀ b, b < gcG 0 → glG b < Z → glG (Om1 * b) < Z := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hbB hg
  rcases lt_or_ge b gfE with hbE | hbE
  · have hOb : Om1 * b < gfE := eW_E.mul_lt Om1_lt_eW hbE
    rw [glG_low hbE] at hg
    rw [glG_low hOb]
    exact wh_gtc_Om1_mul hZ b hbE hg
  obtain ⟨hk, hd0, hdE, hr, hdec, -, hrb, -⟩ := gl_parts hbE
  obtain ⟨q0n, q0a, q0d, g0r⟩ := gl_parts_Q hbE hbB hg
  have hE : InE (guE b) := guE_E b
  have hOe : Om1 < guE b := gl_Om1_lt_E hbE
  have hOm := wn_Om1_mul_pow hE hOe hk
  set e := guE b
  set j := log e b
  set d := b / e ^ j
  set r := b % e ^ j
  have heq : Om1 * b = e ^ j * d + Om1 * r := by
    conv_lhs => rw [← hdec]
    rw [mul_add, ← mul_assoc, hOm]
  have hrq : Om1 * r < e ^ j := by
    calc Om1 * r < Om1 * e ^ j := mul_lt_mul_of_pos_left hr wh_Om1_pos
      _ = e ^ j := hOm
  have hv : e ^ j * d + Om1 * r < eN e := by
    rw [← heq]; exact (eN_E e).mul_lt (hOe.trans (lt_eN e)) (gl_lt_eN hbE)
  have hB : e ^ j * d + Om1 * r < gcG 0 := by
    rw [← heq]; exact gl_G0_E.mul_lt gl_Om1_lt_G0 hbB
  have i1 := IH r hrb (hrb.trans hbB) g0r
  rw [heq, glG_cnf hE hOe hk hd0 hdE hrq hv hB]
  exact max_lt (max_lt q0n q0a) (max_lt q0d i1)

/-! ## The level datum of every level below `G` -/

theorem wn_omega_lt_SC {Z : Ordinal.{0}} (hZ : SC Z) : ω < Z :=
  omega0_lt_inE (Low.opow_eq_self_of_SC hZ)

/-- `x ≤ glR ℓ x` at an `ε`-number `x < Ω₁` above the gate, for `Ω₁ ≤ ℓ < G`. -/
theorem wn_le_glR {x ℓ : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (h1 : Om1 ≤ ℓ) (hB : ℓ < gcG 0)
    (hg : glG ℓ < x) : x ≤ glR ℓ x := by
  have hO : glR Om1 x = x := by rw [glR_low Om1_lt_eW, (rdc_Om1 x).1]
  rcases h1.lt_or_eq with h | h
  · have hgO : glG Om1 < x := by
      rw [glG_low Om1_lt_eW, (rdc_Om1 0).2]; exact one_lt_omega0.trans (omega0_lt_inE hx)
    calc x = glR Om1 x := hO.symm
      _ ≤ glR ℓ x := (glR_mono hx hx1 hB h hg hgO).le
  · rw [← h, hO]

/-- The reading of the level datum: `glR ℓ x` (at least `x`) above the gate `glG ℓ`, `x` at or below it. -/
noncomputable def wnRd (ℓ x : Ordinal.{0}) : Ordinal.{0} := if glG ℓ < x then max x (glR ℓ x) else x

theorem wnRd_eq {ℓ x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (h1 : Om1 ≤ ℓ) (hB : ℓ < gcG 0)
    (hg : glG ℓ < x) : wnRd ℓ x = glR ℓ x := by
  unfold wnRd; rw [if_pos hg, max_eq_right (wn_le_glR hx hx1 h1 hB hg)]

/-- **THE LEVEL DATUM OF EVERY LEVEL** `Ω₁ ≤ ℓ`, `Ω₁ ∣ ℓ`, `ℓ < G`: `L = ℓ`, gate `glG ℓ`, reading `glR ℓ x` above
the gate (`Wh.whLv` with `(rdc, gtc, ε_{Ω₁+1})` replaced by `(glR, glG, G)`). -/
noncomputable def wnLv (ℓ : Ordinal.{0}) (h1 : Om1 ≤ ℓ) (h2 : Om1 ∣ ℓ) (h3 : ℓ < gcG 0) : HnLv where
  L := ℓ
  l := wnRd ℓ
  u := Om1 * (ℓ / (Om1 * Om1))
  q := (ℓ % (Om1 * Om1)) / Om1
  g := glG ℓ
  g_lt := glG_lt_Om1 ℓ h3
  q_lt := (wh_L_dec h2).2
  OL := h1
  L_G := h3
  L_eq := by rw [← Br.Om1_eq]; exact (wh_L_dec h2).1
  g_cl := fun Z y hZ hZ1 hy hLy hy2 => by
    rw [← Br.Om1_eq] at hy2
    set a := ℓ / (Om1 * Om1)
    set q := (ℓ % (Om1 * Om1)) / Om1
    have hℓ : ℓ = Om1 * (Om1 * a + q) := by rw [mul_add]; exact (wh_L_dec h2).1
    have hqO : q < Om1 := (wh_L_dec h2).2
    have haℓ : a ≤ ℓ := Ordinal.div_le_of_le_mul (Ordinal.le_mul_right _ (mul_pos wh_Om1_pos wh_Om1_pos))
    have haB : a < gcG 0 := haℓ.trans_lt h3
    have hyB : y < gcG 0 := by
      refine hy2.trans_le ?_
      have : Om1 * (Om1 * a) + Om1 * Om1 = Om1 * (Om1 * (a + 1)) := by rw [mul_add_one, mul_add]
      rw [this]
      exact (gl_G0_E.mul_lt gl_Om1_lt_G0 (gl_G0_E.mul_lt gl_Om1_lt_G0
        ((inE_indec gl_G0_E).add_lt haB ((wh_one_lt_Om1).trans gl_Om1_lt_G0)))).le
    have hgy := Wj.wjDigitGateG Z hZ hZ1 y hy hyB
    have hωZ := wn_omega_lt_SC hZ
    set w := y / Om1
    have hw1 : w < Om1 * a + Om1 := by
      rw [← mul_add_one]
      refine (Ordinal.div_lt wh_Om1_pos.ne').2 ?_
      calc y < Om1 * (Om1 * a) + Om1 * Om1 := hy2
      _ = Om1 * (Om1 * (a + 1)) := by rw [mul_add_one, mul_add]
    have hw2 : Om1 * a + q ≤ w := (Ordinal.mul_le_iff_le_div wh_Om1_pos.ne').1 (hℓ ▸ hLy)
    obtain ⟨t, ht⟩ := exists_add_of_le (le_self_add.trans hw2 : Om1 * a ≤ w)
    have htO : t < Om1 := by rw [ht] at hw1; exact (add_lt_add_iff_left _).1 hw1
    have hqt : q ≤ t := by rw [ht] at hw2; exact (add_le_add_iff_left _).1 hw2
    have hwd : w / Om1 = a := by
      rw [ht, Ordinal.mul_add_div _ wh_Om1_pos.ne', Ordinal.div_eq_zero_of_lt htO, add_zero]
    have hwm : w % Om1 = t := by rw [ht, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt htO]
    have hwB : w < gcG 0 := (wn_div_le y).trans_lt hyB
    obtain ⟨g1, g1'⟩ := wn_glG_div hωZ y hyB hgy
    obtain ⟨g2, -⟩ := wn_glG_div hωZ w hwB g1
    rw [hwd] at g2
    rw [hwm] at g1'
    have hqZ : q < Z := hqt.trans_lt g1'
    have hZl : IsSuccLimit Z := hZ.isSuccLimit
    have hOa : Om1 * a < gcG 0 := gl_G0_E.mul_lt gl_Om1_lt_G0 haB
    have hsB : Om1 * a + q < gcG 0 := (inE_indec gl_G0_E).add_lt hOa (hqO.trans gl_Om1_lt_G0)
    have hg1 := wn_glG_Om1_mul hZl hωZ a haB g2
    have hg2 : glG (Om1 * a + q) < Z :=
      gl_add (fun u v hu hv => hZ.isPrincipal hu hv) hωZ _ _ hsB hg1
        (by rw [glG_low (hqO.trans Om1_lt_eW), (rdc_const hqO 0).2]; exact hqZ)
    rw [hℓ]
    exact wn_glG_Om1_mul hZl hωZ _ hsB hg2
  L_mem := fun _ _ _ _ hb => (gl_mem ℓ h3 hb).1
  l_ge := fun x => by unfold wnRd; split_ifs; exacts [le_max_left _ _, le_rfl]
  l_lt := fun x hx hx1 => by
    unfold wnRd; split_ifs with hg
    · exact max_lt (lgG_facts hx hx1).2.1 (glR_lt_G hx hx1 h3 hg)
    · exact (lgG_facts hx hx1).2.1
  l_pi := fun σ ρ hB hg => by
    rw [wnRd_eq hB.2.1 hB.2.2.2 h1 h3 (hg.trans hB.2.2.1), wnRd_eq hB.1 (hB.2.2.1.trans hB.2.2.2) h1 h3 hg]
    exact gl_pi hB ℓ h3 hg

theorem wnLv_L {ℓ : Ordinal.{0}} (h1 : Om1 ≤ ℓ) (h2 : Om1 ∣ ℓ) (h3 : ℓ < gcG 0) : (wnLv ℓ h1 h2 h3).L = ℓ := rfl

theorem wnLv_g {ℓ : Ordinal.{0}} (h1 : Om1 ≤ ℓ) (h2 : Om1 ∣ ℓ) (h3 : ℓ < gcG 0) : (wnLv ℓ h1 h2 h3).g = glG ℓ :=
  rfl

/-- **EVERY LEVEL BELOW `G` HAS A LEVEL DATUM** (`L = ℓ`, gate `= glG ℓ`, reading `glR ℓ x` above it). -/
theorem wnLvDatumAll : ∀ ℓ, (Om1 ≤ ℓ ∧ Om1 ∣ ℓ ∧ ℓ < gcG 0) → ∃ Λ : HnLv, Λ.L = ℓ ∧ Λ.g ≤ glG ℓ ∧
    ∀ x, InE x → x < Om1 → Λ.g < x → Λ.l x = glR ℓ x := fun ℓ h =>
  ⟨wnLv ℓ h.1 h.2.1 h.2.2, rfl, le_rfl, fun _ hx hx1 hg => wnRd_eq hx hx1 h.1 h.2.2 hg⟩

/-! ## The gate of the cofinal levels -/

/-- The cofinal levels `glBn n` are codes over every strongly critical `Z` (with the atom `G`). -/
theorem wnBn_code {Z : Ordinal.{0}} (hZ : SC Z) : ∀ n, GxCl Z {gcG 0} (glBn n)
  | 0 => by
    show GxCl Z {gcG 0} (veblen ω (Om1 + 1))
    have h1 : (1 : Ordinal.{0}) < Z := one_lt_omega0.trans (wn_omega_lt_SC hZ)
    refine GxCl.phi (GxCl.small (wn_omega_lt_SC hZ)) (GxCl.add ?_ (GxCl.small h1))
    rw [Br.Om1_eq]; exact GxCl.om
  | n + 1 => GxCl.phi (wnBn_code hZ n) (GxCl.small hZ.1)

/-- **THE GATE OF THE COFINAL LEVELS**: `glG (glBn n) < Γ₀`. -/
theorem wnGateBn (n : ℕ) : glG (glBn n) < gamma 0 :=
  Wj.wjDigitGateG (gamma 0) (Lq.lq_gamma_SC 0) (by rw [← Br.Om1_eq]; exact gq_gam_lt_Om1.le) _
    (wnBn_code (Lq.lq_gamma_SC 0) n) (glBn_spec n).1

/-- **The gate of the cofinal levels is below `K`.** -/
theorem wnGateBnK (S : InaccSeq.{0}) (n : ℕ) : glG (glBn n) < Td.tdK S :=
  (wnGateBn n).trans_le (Td.tdGam_le_K (S := S))

end Googology.Trans.PoR.InaccPsi.R2.Wn
