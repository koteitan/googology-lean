import Googology.Trans.PoR.InaccPsi.R2.WmA1

/-!
# WoArith: `Ω₁`-SEQUENCES FOR THE LEVELS OF COFINALITY `Ω₁`

A level `ℓ < ε_{Ω₁+1}` that is not `Ω₁`, not a successor `ℓ' + Ω₁` and has no `ω`-sequence (`Wm.WmFs`) has an
`Ω₁`-sequence of levels `s μ` (`μ < Ω₁`): strictly increasing, below `ℓ`, with gates below every `ε`-number `x`
above `gtc ℓ` when `μ < x`, and GATE-COFINAL: every `b < ℓ` with `gtc b < σ` (`σ` an `ε`-number) lies below some
`s μ` with `μ < σ`.

* `WoSeq1 a s` (an `Ω₁`-sequence below `a`), `WoFs1 ℓ s` (of levels);
* `wo_seq_term` (**`E + Ω₁^{f+1}`**: `s μ = E + Ω₁^f·(μ+1)`), `wo_seq_pow` (**`P + Ω₁^f`** from an `Ω₁`-sequence
  `f_μ` of `f`: `s μ = P + Ω₁^{f_μ}`);
* `wo_seq_exp` (**every limit exponent with no `ω`-sequence has an `Ω₁`-sequence**), `wo_fs1` (**EVERY LEVEL OF THE
  REMAINING CASE OF `Wm.WmOm1Step` HAS AN `Ω₁`-SEQUENCE OF LEVELS**).

No new axiom.  New definitions: `WoSeq1`, `WoFs1`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wo

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

/-- **AN `Ω₁`-SEQUENCE BELOW `a`**: `1 ≤ s μ < a`, strictly increasing, gates below every `ε`-number `x > gtc a`
when `μ < x`, and gate-cofinal (`gtc b < σ` ⇒ `b < s μ` for some `μ < σ`). -/
def WoSeq1 (a : Ordinal.{0}) (s : Ordinal.{0} → Ordinal.{0}) : Prop :=
  (∀ μ, μ < Om1 → 1 ≤ s μ ∧ s μ < a) ∧ (∀ μ' μ, μ' < μ → μ < Om1 → s μ' < s μ) ∧
    (∀ x, InE x → x < Om1 → gtc a < x → ∀ μ, μ < x → gtc (s μ) < x) ∧
    ∀ σ, InE σ → σ < Om1 → ∀ b, b < a → gtc b < σ → ∃ μ, μ < σ ∧ b < s μ

/-- **AN `Ω₁`-SEQUENCE OF LEVELS BELOW `ℓ`.** -/
def WoFs1 (ℓ : Ordinal.{0}) (s : Ordinal.{0} → Ordinal.{0}) : Prop :=
  WoSeq1 ℓ s ∧ ∀ μ, μ < Om1 → Om1 ≤ s μ ∧ Om1 ∣ s μ

theorem wo_add_one_lt_inE {x μ : Ordinal.{0}} (hx : InE x) (h : μ < x) : μ + 1 < x :=
  (ev_isSuccLimit_of_inE hx).add_one_lt h

theorem wo_indec_inE {x : Ordinal.{0}} (hx : InE x) : ∀ u v, u < x → v < x → u + v < x :=
  fun _ _ hu hv => (inE_indec hx).add_lt hu hv

/-- `gtc f ≤ gtc (f + 1)`. -/
theorem wo_gtc_succ_ge {f : Ordinal.{0}} (hf : f < gfE) : gtc f ≤ gtc (f + 1) := (rdc_succ f hf 0).2.1

/-- **The gates of the prefix and of the exponent**: `Ω₁^f ∣ P` ⇒ `gtc P ≤ gtc (P + Ω₁^f)` and
`gtc f ≤ gtc (P + Ω₁^f)`. -/
theorem wo_gtc_pre {P f : Ordinal.{0}} (hP : Om1 ^ f ∣ P) (hW : P + Om1 ^ f < gfE) :
    gtc P ≤ gtc (P + Om1 ^ f) ∧ gtc f ≤ gtc (P + Om1 ^ f) := by
  obtain ⟨A, m, hA, hm, rfl⟩ := wm_split hP
  have hm1 : m + 1 < Om1 := gl_Om1_lim.add_one_lt hm
  have eL : A + Om1 ^ f * m + Om1 ^ f = A + (Om1 ^ f * (m + 1) + 0) := by
    rw [add_zero, mul_add_one, add_assoc]
  have hg : gtc (A + Om1 ^ f * m + Om1 ^ f) = max (gtc A) (max (max (gtc f) (m + 1)) 0) := by
    rw [eL, wm_gtc_tail (by rw [← eL]; exact hW) hA (wm_add_one_pos _).ne' hm1 (wm_pow_pos f), gtc_zero]
  rw [hg]
  refine ⟨?_, (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))⟩
  rcases eq_or_ne m 0 with rfl | hm0
  · rw [mul_zero, add_zero]; exact le_max_left _ _
  · have hW' : A + (Om1 ^ f * m + 0) < gfE := by
      rw [add_zero]; exact (le_self_add.trans_lt hW)
    have h := wm_gtc_tail hW' hA hm0 hm (wm_pow_pos f)
    rw [add_zero, gtc_zero] at h
    rw [h]
    exact max_le_max le_rfl (max_le_max (max_le_max le_rfl (le_self_add : m ≤ m + 1)) le_rfl)

theorem wo_pow_lt {f g : Ordinal.{0}} (h : f < g) : Om1 ^ f < Om1 ^ g :=
  (opow_lt_opow_iff_right wh_one_lt_Om1).2 h

/-! ## The term case `E + Ω₁^{f+1}` -/

section Term

variable {E f : Ordinal.{0}} (hE : Om1 ^ (f + 1) ∣ E) (hW : E + Om1 ^ (f + 1) < gfE)
include hE hW

/-- **THE TERM CASE**: `s μ = E + Ω₁^f·(μ+1)` is an `Ω₁`-sequence below `E + Ω₁^{f+1}`. -/
theorem wo_seq_term : WoSeq1 (E + Om1 ^ (f + 1)) (fun μ => E + Om1 ^ f * (μ + 1)) := by
  have hf1W : f + 1 < gfE := (wm_le_pow (f + 1)).trans_lt (le_add_self.trans_lt hW)
  have hfW : f < gfE := (lt_add_one f).trans hf1W
  have hpw : Om1 ^ (f + 1) = Om1 ^ f * Om1 := by rw [opow_add, opow_one]
  have hlt : ∀ μ, μ < Om1 → E + Om1 ^ f * (μ + 1) < E + Om1 ^ (f + 1) := fun μ hμ =>
    (add_lt_add_iff_left E).2 (wm_term_lt (gl_Om1_lim.add_one_lt hμ))
  obtain ⟨gE, gf1⟩ := wo_gtc_pre hE hW
  refine ⟨fun μ hμ => ⟨?_, hlt μ hμ⟩, fun μ' μ h hμ => ?_, fun x hx hx1 hg μ hμ => ?_,
    fun σ hσ hσ1 b hb hgb => ?_⟩
  · exact (one_le_iff_pos.2 (mul_pos (wm_pow_pos f) (wm_add_one_pos μ))).trans le_add_self
  · exact (add_lt_add_iff_left E).2 (mul_lt_mul_of_pos_left (wm_succ_lt h) (wm_pow_pos f))
  · have hμ1 : μ + 1 < Om1 := gl_Om1_lim.add_one_lt (hμ.trans hx1)
    have hkW : E + (Om1 ^ f * (μ + 1) + 0) < gfE := by
      rw [add_zero]; exact (hlt μ (hμ.trans hx1)).trans hW
    have h := wm_gtc_tail hkW hE (wm_add_one_pos _).ne' hμ1 (wm_pow_pos f)
    rw [add_zero, gtc_zero] at h
    show gtc (E + Om1 ^ f * (μ + 1)) < x
    rw [h]
    refine max_lt (gE.trans_lt hg) (max_lt (max_lt ?_ (wo_add_one_lt_inE hx hμ)) hx.pos)
    exact ((wo_gtc_succ_ge hfW).trans gf1).trans_lt hg
  · rcases lt_or_ge b E with hbE | hbE
    · exact ⟨0, hσ.pos, hbE.trans_le le_self_add⟩
    obtain ⟨t, rfl⟩ := exists_add_of_le hbE
    have ht : t < Om1 ^ f * Om1 := by rw [← hpw]; exact (add_lt_add_iff_left E).1 hb
    set d := t / Om1 ^ f
    have hdO : d < Om1 := (Ordinal.div_lt (opow_ne_zero _ wh_Om1_pos.ne')).2 ht
    have htd : t < Om1 ^ f * (d + 1) := by
      have := Ordinal.lt_mul_succ_div t (opow_ne_zero f wh_Om1_pos.ne'); rwa [succ_eq_add_one] at this
    refine ⟨d, ?_, (add_lt_add_iff_left E).2 htd⟩
    rcases eq_or_ne d 0 with hd0 | hd0
    · rw [hd0]; exact hσ.pos
    have hr : t % Om1 ^ f < Om1 ^ f := Ordinal.mod_lt t (opow_ne_zero f wh_Om1_pos.ne')
    have et : t = Om1 ^ f * d + t % Om1 ^ f := (Ordinal.div_add_mod t _).symm
    have hbW : E + t < gfE := hb.trans hW
    have hgt := wm_gtc_cat E (le_self_add.trans_lt hbW) (f + 1) t hE (by rw [hpw]; exact ht)
    have hgt2 := (rdc_cnf hfW hd0 hdO hr 0).2
    rw [← et] at hgt2
    rw [hgt, hgt2] at hgb
    exact (le_max_right _ _ |>.trans (le_max_left _ _) |>.trans (le_max_right _ _)).trans_lt hgb

end Term

/-! ## The power case `P + Ω₁^f` -/

section Pow

variable {P f : Ordinal.{0}} {fs : Ordinal.{0} → Ordinal.{0}} (hP : Om1 ^ f ∣ P) (hW : P + Om1 ^ f < gfE)
  (hF : WoSeq1 f fs)
include hP hW hF

/-- **THE POWER CASE**: `s μ = P + Ω₁^{f_μ}` is an `Ω₁`-sequence below `P + Ω₁^f`. -/
theorem wo_seq_pow : WoSeq1 (P + Om1 ^ f) (fun μ => P + Om1 ^ fs μ) := by
  obtain ⟨h1, hmono, hgate, hcof⟩ := hF
  have hfW : f < gfE := (wm_le_pow f).trans_lt (le_add_self.trans_lt hW)
  obtain ⟨gP, gf⟩ := wo_gtc_pre hP hW
  have hlt : ∀ μ, μ < Om1 → P + Om1 ^ fs μ < P + Om1 ^ f := fun μ hμ =>
    (add_lt_add_iff_left P).2 (wo_pow_lt (h1 μ hμ).2)
  refine ⟨fun μ hμ => ⟨?_, hlt μ hμ⟩, fun μ' μ h hμ => ?_, fun x hx hx1 hg μ hμ => ?_,
    fun σ hσ hσ1 b hb hgb => ?_⟩
  · exact (one_le_iff_pos.2 (wm_pow_pos _)).trans le_add_self
  · exact (add_lt_add_iff_left P).2 (wo_pow_lt (hmono μ' μ h hμ))
  · have hμ1 : μ < Om1 := hμ.trans hx1
    have hfμW : fs μ < gfE := (h1 μ hμ1).2.trans hfW
    have hgf := hgate x hx hx1 (gf.trans_lt hg) μ hμ
    show gtc (P + Om1 ^ fs μ) < x
    have hsW : P + Om1 ^ fs μ < gfE := (hlt μ hμ1).trans hW
    refine gtc_add (wo_indec_inE hx) P _ (le_self_add.trans_lt hsW) (le_add_self.trans_lt hsW)
      (gP.trans_lt hg) ?_
    rw [wm_gtc_pow hfμW]
    exact max_lt hgf (one_lt_omega0.trans (omega0_lt_inE hx))
  · rcases lt_or_ge b P with hbP | hbP
    · exact ⟨0, hσ.pos, hbP.trans_le le_self_add⟩
    obtain ⟨t, rfl⟩ := exists_add_of_le hbP
    have ht : t < Om1 ^ f := (add_lt_add_iff_left P).1 hb
    rcases eq_or_ne t 0 with rfl | ht0
    · exact ⟨0, hσ.pos, by rw [add_zero]; exact lt_add_of_pos_right _ (wm_pow_pos _)⟩
    have hbW : P + t < gfE := hb.trans hW
    have hgt := wm_gtc_cat P (le_self_add.trans_lt hbW) f t hP ht
    have htW : t < gfE := le_add_self.trans_lt hbW
    have hgl : gtc (log Om1 t) < σ :=
      ((gtc_parts ht0 htW).1.trans ((le_max_right _ _).trans hgt.ge)).trans_lt hgb
    have hlf : log Om1 t < f := (lt_opow_iff_log_lt wh_one_lt_Om1 ht0).1 ht
    obtain ⟨μ, hμ, hlμ⟩ := hcof σ hσ hσ1 _ hlf hgl
    refine ⟨μ, hμ, (add_lt_add_iff_left P).2 ?_⟩
    exact (lt_opow_succ_log_self wh_one_lt_Om1 t).trans_le
      (opow_le_opow_right wh_Om1_pos (add_one_le_of_lt hlμ))

end Pow

/-! ## The classification -/

/-- **EVERY LIMIT EXPONENT WITH NO `ω`-SEQUENCE HAS AN `Ω₁`-SEQUENCE.** -/
theorem wo_seq_exp : ∀ e, e < gfE → IsSuccLimit e → ¬ WmExpFs e → ∃ s, WoSeq1 e s := by
  intro e
  induction e using WellFoundedLT.induction with
  | ind e IH =>
  intro heW hel hno
  obtain ⟨E, f, c, hc0, hc, hE, rfl⟩ := wh_last_term e hel.ne_bot
  rcases zero_or_succ_or_isSuccLimit c with hc' | ⟨c', hcs⟩ | hcl
  · exact absurd hc' hc0.ne'
  · rw [← Ordinal.add_one_eq_succ] at hcs; subst hcs
    have e1 : E + Om1 ^ f * (c' + 1) = E + Om1 ^ f * c' + Om1 ^ f := by rw [mul_add_one, add_assoc]
    rw [e1] at heW hel hno ⊢
    have hE' : Om1 ^ f ∣ E + Om1 ^ f * c' :=
      dvd_add (dvd_trans (opow_dvd_opow Om1 le_self_add) hE) (dvd_mul_right _ _)
    rcases zero_or_succ_or_isSuccLimit f with hf0 | ⟨f', hfs⟩ | hfl
    · subst hf0
      rw [opow_zero] at hel
      exact absurd hel (not_isSuccLimit_add_one _)
    · rw [← Ordinal.add_one_eq_succ] at hfs; subst hfs
      exact ⟨_, wo_seq_term hE' heW⟩
    · have hfW : f < gfE := (wm_le_pow f).trans_lt (le_add_self.trans_lt heW)
      have hnf : ¬ WmExpFs f := fun hF => hno (wmExpFs_lim hfl ((lt_add_one c').trans hc) hE heW hF)
      have hfe : f < E + Om1 ^ f * c' + Om1 ^ f := (lt_Om1_pow hfW).trans_le le_add_self
      obtain ⟨fs, hfs⟩ := IH f (by rw [e1]; exact hfe) hfW hfl hnf
      exact ⟨_, wo_seq_pow hE' heW hfs⟩
  · exact absurd (wmExpFs_digit hcl hc hE heW) hno

/-- **A TERM SEQUENCE OF LEVELS**: `E + Ω₁^{f+1}` with `1 ≤ f`. -/
theorem wo_fs1_term {E f : Ordinal.{0}} (hf : 1 ≤ f) (hE : Om1 ^ (f + 1) ∣ E) (hW : E + Om1 ^ (f + 1) < gfE) :
    WoFs1 (E + Om1 ^ (f + 1)) (fun μ => E + Om1 ^ f * (μ + 1)) := by
  refine ⟨wo_seq_term hE hW, fun μ _ => ⟨?_, ?_⟩⟩
  · exact (wm_Om1_le_pow hf).trans ((le_mul_of_one_le_right' le_add_self).trans le_add_self)
  · exact dvd_add ((wm_Om1_dvd_pow (le_add_self : (1 : Ordinal.{0}) ≤ f + 1)).trans hE)
      (Dvd.dvd.mul_right (wm_Om1_dvd_pow hf) _)

/-- **A POWER SEQUENCE OF LEVELS**: `P + Ω₁^f` (`Ω₁ ∣ P`) from an `Ω₁`-sequence of `f`. -/
theorem wo_fs1_pow {P f : Ordinal.{0}} {fs : Ordinal.{0} → Ordinal.{0}} (hP : Om1 ^ f ∣ P) (hPd : Om1 ∣ P)
    (hW : P + Om1 ^ f < gfE) (hF : WoSeq1 f fs) : WoFs1 (P + Om1 ^ f) (fun μ => P + Om1 ^ fs μ) := by
  refine ⟨wo_seq_pow hP hW hF, fun μ hμ => ⟨?_, ?_⟩⟩
  · exact (wm_Om1_le_pow (hF.1 μ hμ).1).trans le_add_self
  · exact dvd_add hPd (wm_Om1_dvd_pow (hF.1 μ hμ).1)

/-- **EVERY LEVEL OF THE REMAINING CASE OF `Wm.WmOm1Step` HAS AN `Ω₁`-SEQUENCE OF LEVELS.** -/
theorem wo_fs1 {ℓ : Ordinal.{0}} (hℓ : WmLev ℓ) (h1 : ℓ ≠ Om1) (h2 : ¬ ∃ ℓ', WmLev ℓ' ∧ ℓ = ℓ' + Om1)
    (h3 : ¬ WmFs ℓ) : ∃ s, WoFs1 ℓ s := by
  rcases whShape ℓ hℓ.1 hℓ.2.1 hℓ.2.2 with h | h | ⟨P, e, he, hP, rfl⟩ | ⟨P, e, he, hP, rfl⟩ |
      ⟨P, e, c, he, hc, hcO, hP, rfl⟩
  · exact absurd h h1
  · exact absurd h h2
  · exact ⟨_, wo_fs1_term he hP hℓ.2.2⟩
  · have heW : e < gfE := (wm_le_pow e).trans_lt (le_add_self.trans_lt hℓ.2.2)
    have he1 : 1 ≤ e := one_le_iff_pos.2 he.bot_lt
    have hPd : Om1 ∣ P := (wm_Om1_dvd_pow he1).trans hP
    have hnE : ¬ WmExpFs e := fun hE => h3 (wmFs_exp he hP hℓ.2.2 hE)
    obtain ⟨fs, hfs⟩ := wo_seq_exp e heW he hnE
    exact ⟨_, wo_fs1_pow hP hPd hℓ.2.2 hfs⟩
  · exact absurd (wmFs_coef he hc hcO hP hℓ.2.2) h3

end Googology.Trans.PoR.InaccPsi.R2.Wo
