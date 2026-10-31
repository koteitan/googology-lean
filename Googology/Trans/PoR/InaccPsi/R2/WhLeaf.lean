import Googology.Trans.PoR.InaccPsi.R2.HoPU

/-!
# WhLeaf: THE SMALL LEAVES OF THE LEVEL-CODE INDUCTION (region A1 of the frontier)

The levels of the induction are the codes `ℓ` with `Ω₁ ≤ ℓ`, `Ω₁ ∣ ℓ`, `ℓ < ε_{Ω₁+1}` (Cantor normal form in
`Ω₁`-powers, read `Ω₁ ↦ x` by `Gf.rdc`, gate `Gf.gtc`).  This module proves, with no hypothesis:

* `wh_last_term` (**every `ℓ ≠ 0` is `P + Ω₁^e·c` with `0 < c < Ω₁` and `Ω₁^{e+1} ∣ P`**), `whShape` (**the five
  shapes of a level**: `Ω₁`, a successor `ℓ' + Ω₁`, `P + Ω₁^{e+1}` with `e ≥ 1`, `P + Ω₁^e` with `e` a limit,
  `P + Ω₁^e·c` with `c < Ω₁` a limit);
* `whCofLev` (**the levels are cofinal**: every `B < φ(ε_{Ω₁+1}, G+1)` is `≤ φ(ℓ, G+1)` for a level `ℓ` with gate
  below `K`; `ℓ` is a member of the tower `Gf.gfTw`);
* `whDigitGate` (**THE TRANSFINITE DIGIT GATE**: a code over a strongly critical `Z ≤ Ω₁` with the atom `G`, below
  `ε_{Ω₁+1}`, has its gate `gtc` below `Z`; from `Gf.gfCode_gate`);
* `wh_gtc_Om1_mul` (`gtc (Ω₁·b) < Z` from `gtc b < Z` at a limit `Z`), `wh_le_rdc` (`x ≤ rdc ℓ x` at an
  `ε`-number `x`), `wh_L_dec` (`ℓ = Ω₁·(Ω₁·a) + Ω₁·q`), `whLv` (**THE LEVEL DATUM OF EVERY LEVEL**: an `Hn.HnLv`
  with `L = ℓ`, gate `gtc ℓ`, reading `rdc ℓ x` above the gate), `whLvDatumAll`;
* `whStepBase` (**the entry at the level `Ω₁`**: the package `Hn.hnPk1` and the system `Hg.hgU`).

No new axiom.  New definitions: `whRd`, `whLv`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wh

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

/-! ## The shape of a level -/

theorem wh_Om1_pos : (0 : Ordinal.{0}) < Om1 := gv_Om1_pos

theorem wh_one_lt_Om1 : (1 : Ordinal.{0}) < Om1 := gf_one_lt_Om1

/-- **The last term of a nonzero ordinal**: `ℓ = P + Ω₁^e·c` with `0 < c < Ω₁` and `Ω₁^{e+1} ∣ P`. -/
theorem wh_last_term : ∀ ℓ : Ordinal.{0}, ℓ ≠ 0 →
    ∃ P e c : Ordinal.{0}, 0 < c ∧ c < Om1 ∧ Om1 ^ (e + 1) ∣ P ∧ ℓ = P + Om1 ^ e * c := by
  intro ℓ
  induction ℓ using WellFoundedLT.induction with
  | ind ℓ IH =>
  intro hℓ
  obtain ⟨hd0, hd, hr, hdec, hrl, _⟩ := parts hℓ
  set L := log Om1 ℓ
  set d := ℓ / Om1 ^ L
  set r := ℓ % Om1 ^ L
  rcases eq_or_ne r 0 with h0 | h0
  · refine ⟨0, L, d, hd0, hd, dvd_zero _, ?_⟩
    rw [zero_add]; rw [h0, add_zero] at hdec; exact hdec.symm
  obtain ⟨P, e, c, hc0, hc, hP, hre⟩ := IH r hrl h0
  have heL : e + 1 ≤ L := by
    refine Order.add_one_le_of_lt ((opow_lt_opow_iff_right wh_one_lt_Om1).1 ?_)
    calc Om1 ^ e ≤ Om1 ^ e * c := le_mul_of_one_le_right' (Order.one_le_iff_pos.2 hc0)
    _ ≤ P + Om1 ^ e * c := le_add_self
    _ = r := hre.symm
    _ < Om1 ^ L := hr
  refine ⟨Om1 ^ L * d + P, e, c, hc0, hc, dvd_add (Dvd.dvd.mul_right (opow_dvd_opow _ heL) d) hP, ?_⟩
  rw [add_assoc, ← hre, hdec]

/-- **THE FIVE SHAPES OF A LEVEL** `Ω₁ ≤ ℓ`, `Ω₁ ∣ ℓ`, `ℓ < ε_{Ω₁+1}`. -/
theorem whShape (ℓ : Ordinal.{0}) (h1 : Om1 ≤ ℓ) (h2 : Om1 ∣ ℓ) (h3 : ℓ < gfE) :
    ℓ = Om1 ∨ (∃ ℓ', (Om1 ≤ ℓ' ∧ Om1 ∣ ℓ' ∧ ℓ' < gfE) ∧ ℓ = ℓ' + Om1) ∨
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

/-! ## The levels are cofinal in `φ(ε_{Ω₁+1}, G+1)` -/

/-- **THE LEVELS ARE COFINAL**: every `B < φ(ε_{Ω₁+1}, G+1)` is `≤ φ(ℓ, G+1)` for a level `ℓ` (a member of the
tower `Gf.gfTw`) whose gate is below `K`. -/
theorem whCofLev (S : InaccSeq.{0}) : ∀ B, B < veblen gfE (gcG 0 + 1) →
    ∃ ℓ, (Om1 ≤ ℓ ∧ Om1 ∣ ℓ ∧ ℓ < gfE) ∧ gtc ℓ < Td.tdK S ∧ B ≤ veblen ℓ (gcG 0 + 1) := by
  intro B hB
  have hfix : veblen gfE (gcG 0) = gcG 0 := gn_veb_fix (gcG_SC 0) gfE_lt_G0
  rw [← hdNx_fixP hfix] at hB
  obtain ⟨k, hk⟩ := hdNx_cof eW_lim (β := gfTw) gfTw_lt (fun k => (gfTw_strictMono (Nat.lt_succ_self k)).le)
    (fun t ht => gfTw_cof ht) hB
  have hOk : Om1 ≤ gfTw k := (le_self_add).trans (gfTw_ge k)
  refine ⟨gfTw (k + 1), ⟨?_, ?_, gfTw_lt _⟩, ?_, ?_⟩
  · rw [gfTw_succ]
    calc Om1 = ω ^ Om1 := gl_Om1_E.symm
    _ ≤ ω ^ gfTw k := opow_le_opow_right omega0_pos hOk
  · rw [gfTw_succ]
    obtain ⟨t, ht⟩ := exists_add_of_le hOk
    rw [ht, opow_add, gl_Om1_E]
    exact dvd_mul_right _ _
  · exact (gfTw_gtc (k + 1)).trans (gq_eps0_lt_gam.trans_le (Td.tdGam_le_K (S := S)))
  · refine hk.le.trans (hcN_le ?_ ((lt_add_one _).trans_le (right_le_veblen _ _)))
    exact veblen_veblen_of_lt (gfTw_strictMono (Nat.lt_succ_self k)) _

/-! ## The transfinite digit gate -/

/-- **THE TRANSFINITE DIGIT GATE**: a code `y < ε_{Ω₁+1}` over a strongly critical `Z ≤ Ω₁` with the atom `G` has
its gate (largest hereditary `Ω₁`-digit) below `Z`. -/
theorem whDigitGate : ∀ Z, SC Z → Z ≤ Om 1 → ∀ y, GxCl Z {gcG 0} y → y < gfE → gtc y < Z := by
  intro Z hZ hZ1 y hy hyW
  refine gfCode_gate (by rw [Br.Om1_eq]; exact hZ1) hZ.1 (fun u v hu hv => hZ.isPrincipal hu hv)
    (fun u v hu hv => hZ.2 u hu v hv) (fun s hs => ?_) hy hyW
  rw [Set.mem_singleton_iff.1 hs]; exact gfE_lt_G0

/-! ## The level datum of every level -/

/-- **`gtc (Ω₁·b) < Z`** from `gtc b < Z`, for a limit `Z`. -/
theorem wh_gtc_Om1_mul {Z : Ordinal.{0}} (hZ : IsSuccLimit Z) :
    ∀ b, b < gfE → gtc b < Z → gtc (Om1 * b) < Z := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hbW hg
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [mul_zero, gtc_zero]; exact hZ.bot_lt
  obtain ⟨hd0, hd, hr, hdec, hrb, _⟩ := parts hb0
  have hgp := gtc_parts hb0 hbW
  have hLW : log Om1 b < gfE := (log_lt hb0 hbW).trans hbW
  obtain ⟨h1L, hg1L⟩ := gtc_one_add hLW hZ (hgp.1.trans_lt hg)
  have hr' : Om1 * (b % Om1 ^ log Om1 b) < Om1 ^ (1 + log Om1 b) := by
    rw [opow_add, opow_one]; exact mul_lt_mul_of_pos_left hr wh_Om1_pos
  have heq : Om1 * b = Om1 ^ (1 + log Om1 b) * (b / Om1 ^ log Om1 b) + Om1 * (b % Om1 ^ log Om1 b) := by
    conv_lhs => rw [← hdec]
    rw [mul_add, ← mul_assoc, opow_add, opow_one]
  have hIH := IH _ hrb (hrb.trans hbW) (hgp.2.2.trans_lt hg)
  rw [heq, (rdc_cnf h1L hd0.ne' hd hr' 0).2]
  exact max_lt (max_lt hg1L (hgp.2.1.trans_lt hg)) hIH

/-- **`x ≤ rdc ℓ x`** at an `ε`-number `x`, for a code `Ω₁ ≤ ℓ < ε_{Ω₁+1}`. -/
theorem wh_le_rdc {x ℓ : Ordinal.{0}} (hx : InE x) (h1 : Om1 ≤ ℓ) (hW : ℓ < gfE) : x ≤ rdc ℓ x := by
  have hℓ0 : ℓ ≠ 0 := (wh_Om1_pos.trans_le h1).ne'
  have hlog : 1 ≤ log Om1 ℓ := (opow_le_iff_le_log wh_one_lt_Om1 hℓ0).1 (by rw [opow_one]; exact h1)
  have hl0 : log Om1 ℓ ≠ 0 := (zero_lt_one.trans_le hlog).ne'
  have hpos := rdc_pos hx hl0 ((log_lt hℓ0 hW).trans hW)
  rw [rdc_dec hℓ0 hW]
  calc x ≤ x ^ rdc (log Om1 ℓ) x := left_le_opow x hpos
  _ ≤ x ^ rdc (log Om1 ℓ) x * (ℓ / Om1 ^ log Om1 ℓ) :=
    le_mul_of_one_le_right' (Order.one_le_iff_pos.2 (parts hℓ0).1)
  _ ≤ _ := le_self_add

/-- **`ℓ = Ω₁·(Ω₁·a) + Ω₁·q`** with `a = ℓ / Ω₁²`, `q = (ℓ mod Ω₁²)/Ω₁ < Ω₁`, for `Ω₁ ∣ ℓ`. -/
theorem wh_L_dec {ℓ : Ordinal.{0}} (h2 : Om1 ∣ ℓ) :
    ℓ = Om1 * (Om1 * (ℓ / (Om1 * Om1))) + Om1 * ((ℓ % (Om1 * Om1)) / Om1) ∧
      (ℓ % (Om1 * Om1)) / Om1 < Om1 := by
  have hO2 : (Om1 : Ordinal.{0}) * Om1 ≠ 0 := (mul_pos wh_Om1_pos wh_Om1_pos).ne'
  have hd := Ordinal.div_add_mod ℓ (Om1 * Om1)
  have hdv : Om1 ∣ Om1 * Om1 * (ℓ / (Om1 * Om1)) := by rw [mul_assoc]; exact dvd_mul_right _ _
  have hm : Om1 ∣ ℓ % (Om1 * Om1) := (Ordinal.dvd_add_iff hdv).1 (by rw [hd]; exact h2)
  have hm' := Ordinal.div_add_mod (ℓ % (Om1 * Om1)) Om1
  rw [Ordinal.mod_eq_zero_of_dvd hm, add_zero] at hm'
  refine ⟨?_, (Ordinal.div_lt wh_Om1_pos.ne').2 (Ordinal.mod_lt ℓ hO2)⟩
  conv_lhs => rw [← hd, ← hm']
  rw [mul_assoc]

/-- The reading of the level datum: `rdc ℓ x` (at least `x`) above the gate `gtc ℓ`, `x` at or below it. -/
noncomputable def whRd (ℓ x : Ordinal.{0}) : Ordinal.{0} := if gtc ℓ < x then max x (rdc ℓ x) else x

theorem whRd_eq {ℓ x : Ordinal.{0}} (hx : InE x) (h1 : Om1 ≤ ℓ) (hW : ℓ < gfE) (hg : gtc ℓ < x) :
    whRd ℓ x = rdc ℓ x := by
  unfold whRd; rw [if_pos hg, max_eq_right (wh_le_rdc hx h1 hW)]

/-- **THE LEVEL DATUM OF EVERY LEVEL** `Ω₁ ≤ ℓ`, `Ω₁ ∣ ℓ`, `ℓ < ε_{Ω₁+1}`: `L = ℓ`, gate `gtc ℓ`, reading
`rdc ℓ x` above the gate. -/
noncomputable def whLv (ℓ : Ordinal.{0}) (h1 : Om1 ≤ ℓ) (h2 : Om1 ∣ ℓ) (h3 : ℓ < gfE) : HnLv where
  L := ℓ
  l := whRd ℓ
  u := Om1 * (ℓ / (Om1 * Om1))
  q := (ℓ % (Om1 * Om1)) / Om1
  g := gtc ℓ
  g_lt := gtc_lt_Om1 ℓ h3
  q_lt := (wh_L_dec h2).2
  OL := h1
  L_G := h3.trans gfE_lt_G0
  L_eq := by rw [← Br.Om1_eq]; exact (wh_L_dec h2).1
  g_cl := fun Z y hZ hZ1 hy hLy hy2 => by
    rw [← Br.Om1_eq] at hy2
    set a := ℓ / (Om1 * Om1)
    set q := (ℓ % (Om1 * Om1)) / Om1
    have hℓ : ℓ = Om1 * (Om1 * a + q) := by rw [mul_add]; exact (wh_L_dec h2).1
    have hqO : q < Om1 := (wh_L_dec h2).2
    have haℓ : a ≤ ℓ := Ordinal.div_le_of_le_mul (Ordinal.le_mul_right _ (mul_pos wh_Om1_pos wh_Om1_pos))
    have hyW : y < gfE := by
      refine hy2.trans_le ?_
      have : Om1 * (Om1 * a) + Om1 * Om1 = Om1 * (Om1 * (a + 1)) := by rw [mul_add_one, mul_add]
      rw [this]
      exact (eW_E.mul_lt Om1_lt_eW (eW_E.mul_lt Om1_lt_eW (eW_indec.add_lt (haℓ.trans_lt h3)
        (gf_one_lt_Om1.trans Om1_lt_eW)))).le
    have hgy := whDigitGate Z hZ hZ1 y hy hyW
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
    have hwW : w < gfE := (Ordinal.div_le_of_le_mul (Ordinal.le_mul_right _ wh_Om1_pos)).trans_lt hyW
    obtain ⟨g1, _⟩ := gtc_div y hyW
    obtain ⟨g2, g3⟩ := gtc_div w hwW
    rw [hwd] at g2; rw [hwm] at g3
    have hga : gtc a < Z := (g2.trans g1).trans_lt hgy
    have hqZ : q < Z := (hqt.trans (g3.trans g1)).trans_lt hgy
    have hZl : IsSuccLimit Z := hZ.isSuccLimit
    have haW : a < gfE := haℓ.trans_lt h3
    have hOa : Om1 * a < gfE := eW_E.mul_lt Om1_lt_eW haW
    have hg1 := wh_gtc_Om1_mul hZl a haW hga
    have hg2 : gtc (Om1 * a + q) < Z :=
      gtc_add (fun u v hu hv => hZ.isPrincipal hu hv) _ _ hOa (hqO.trans Om1_lt_eW) hg1
        (by rw [(rdc_const hqO 0).2]; exact hqZ)
    have hsW : Om1 * a + q < gfE := eW_indec.add_lt hOa (hqO.trans Om1_lt_eW)
    rw [hℓ]
    exact wh_gtc_Om1_mul hZl _ hsW hg2
  L_mem := fun S a b ha hb => by
    have hlt : ℓ < hgU.B := (h3.trans gfE_lt_G0).trans_le hgU.G_le
    refine (hgU.mem S a b ha ℓ hlt ?_).1
    rw [hgU.g_lowE ℓ h3]; exact hb
  l_ge := fun x => by unfold whRd; split_ifs; exacts [le_max_left _ _, le_rfl]
  l_lt := fun x hx hx1 => by
    unfold whRd; split_ifs with hg
    · exact max_lt (lgG_facts hx hx1).2.1 ((rdc_lt_eN hx ℓ hg).trans (gT_lt_lgG hx hx1 0))
    · exact (lgG_facts hx hx1).2.1
  l_pi := fun σ ρ hB hg => by
    rw [whRd_eq hB.2.1 h1 h3 (hg.trans hB.2.2.1), whRd_eq hB.1 h1 h3 hg]
    exact rdc_pi hB h3 hg

theorem whLv_L {ℓ : Ordinal.{0}} (h1 : Om1 ≤ ℓ) (h2 : Om1 ∣ ℓ) (h3 : ℓ < gfE) : (whLv ℓ h1 h2 h3).L = ℓ := rfl

theorem whLv_g {ℓ : Ordinal.{0}} (h1 : Om1 ≤ ℓ) (h2 : Om1 ∣ ℓ) (h3 : ℓ < gfE) : (whLv ℓ h1 h2 h3).g = gtc ℓ :=
  rfl

theorem whLv_l {ℓ : Ordinal.{0}} (h1 : Om1 ≤ ℓ) (h2 : Om1 ∣ ℓ) (h3 : ℓ < gfE) {x : Ordinal.{0}} (hx : InE x)
    (hg : gtc ℓ < x) : (whLv ℓ h1 h2 h3).l x = rdc ℓ x := whRd_eq hx h1 h3 hg

/-- **EVERY LEVEL HAS A LEVEL DATUM** (`L = ℓ`, gate `= gtc ℓ`, reading `rdc ℓ x` above it). -/
theorem whLvDatumAll : ∀ ℓ, (Om1 ≤ ℓ ∧ Om1 ∣ ℓ ∧ ℓ < gfE) → ∃ Λ : HnLv, Λ.L = ℓ ∧ Λ.g ≤ gtc ℓ ∧
    ∀ x, InE x → x < Om1 → Λ.g < x → Λ.l x = rdc ℓ x := fun ℓ h =>
  ⟨whLv ℓ h.1 h.2.1 h.2.2, rfl, le_rfl, fun _ hx _ hg => whLv_l h.1 h.2.1 h.2.2 hx hg⟩

/-! ## The entry at the level `Ω₁` -/

theorem wh_hnPk1_L : hnPk1.Λ.L = Om1 := rfl

theorem wh_hnPk1_l (x : Ordinal.{0}) : hnPk1.Λ.l x = x := rfl

/-- **THE ENTRY AT THE LEVEL `Ω₁`**: the package `Hn.hnPk1` (level `Ω₁`, read `x`) and the system `Hg.hgU`
(bound `φ(Ω₁, G+1)`, gate `0 ≤ gtc Ω₁ = 1`). -/
theorem whStepBase : hnPk1.Λ.L = Om1 ∧ (∀ x, InE x → x < Om1 → hnPk1.Λ.g < x → hnPk1.Λ.l x = rdc Om1 x) ∧
    hgU.B = veblen Om1 (gcG 0 + 1) ∧ hgU.γ ≤ gtc Om1 :=
  ⟨rfl, fun x _ _ _ => (rdc_Om1 x).1.symm, hgU_B, by rw [hgU_γ]; exact zero_le⟩

end Googology.Trans.PoR.InaccPsi.R2.Wh
