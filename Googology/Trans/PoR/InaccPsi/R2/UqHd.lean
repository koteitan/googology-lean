import Googology.Trans.PoR.InaccPsi.R2.UqPre

/-!
# Head lemmas for level-2 codes past `Γ₂`

`W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `log_W = Sg.sgLW`, `C_k(Q) = Ug.UgC S k Q` (codes of level `k` with
`ψ_{Ω_{k+1}}`-atoms).  `Sw.swCl_mulW`, `Sw.swCl_divW`, `Tu.tuExp_code`, `Tu.tuHead`, `Tu.tuCl_of_succ`,
`Tu.tuCodeHeadX`, `Tu.tuCofK`, `Tu.tuModW`, `Tu.tuModO` for the level codes (`Ug.ugCDec`, `Ug.ugC_mod`, `Ug.ugC_div`,
`Ug.ugC_divOp`, `Ug.ugC_mulOp`, `Ug.ugC_cnf`, `Uq.uqC_pred` in place of the `LeCl` lemmas).

* `uqWe`, `uqOe`, `uqMulW`, `uqMulO`, `uqDivW` (`W^e`, `Ω^x`, `W^e·y`, `Ω^x·y`, `x / W^e` are codes);
* `uqExp_code`, `uqHeadE` (**THE HEAD LEMMA FOR LEVEL-2 CODES**: a code `z` with `P + W^g ≤ z ≤ P + W^f`, `W^f ∣ P`,
  gives the code `P` and a code `h ∈ [g, f]`), `uqCl_of_succ`, `uqCodeHeadX` (**a code `P + W^e·c`, `W^{e+1} ∣ P`,
  `1 ≤ c < Ω₂`, gives the codes `P`, `e` and `c < Q`**);
* `uqCofK` (**a level-`k` code `x < ω^{Ω_k·e}·Ω_k` is below `ω^{Ω_k·e}·c'` for some `c' < Q`**), `uqModW`, `uqModO`.

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Uq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.St Googology.Trans.PoR.InaccPsi.R2.Tu Googology.Trans.PoR.InaccPsi.R2.Ug

variable {S : InaccSeq.{0}}

/-- `W^e` is a level-2 code when `e` is. -/
theorem uqWe {Q e : Ordinal.{0}} (hQ : SC Q) (he : UgC S (1 + 1) Q e) : UgC S (1 + 1) Q (leWe e) :=
  UgC.opow hQ.1 (ugC_mulK hQ ugTwo_ne e he)

/-- `Ω^x` is a level-1 code when `x` is. -/
theorem uqOe {Q x : Ordinal.{0}} (hQ : SC Q) (hx : UgC S 1 Q x) : UgC S 1 Q (leOe x) :=
  UgC.opow hQ.1 (ugC_mulK hQ one_ne_zero x hx)

/-- `W^e·y` is a level-2 code for codes `e`, `y`. -/
theorem uqMulW {Q e y : Ordinal.{0}} (hQ : SC Q) (he : UgC S (1 + 1) Q e) (hy : UgC S (1 + 1) Q y) :
    UgC S (1 + 1) Q (leWe e * y) :=
  ugC_mulOp hQ ugTwo_ne (ugC_mulK hQ ugTwo_ne e he) y hy

/-- `Ω^x·y` is a level-1 code for codes `x`, `y`. -/
theorem uqMulO {Q x y : Ordinal.{0}} (hQ : SC Q) (hx : UgC S 1 Q x) (hy : UgC S 1 Q y) :
    UgC S 1 Q (leOe x * y) :=
  ugC_mulOp hQ one_ne_zero (ugC_mulK hQ one_ne_zero x hx) y hy

/-- `x / W^e` is a level-2 code for codes `x`, `e`. -/
theorem uqDivW {Q e x : Ordinal.{0}} (hQ : SC Q) (he : UgC S (1 + 1) Q e) (hx : UgC S (1 + 1) Q x) :
    UgC S (1 + 1) Q (x / leWe e) :=
  ugC_divOp hQ ugTwo_ne (ugC_mulK hQ ugTwo_ne e he) x hx

/-- **A level-2 code `P + W^f` with `W^f ∣ P` gives the code `f`.** -/
theorem uqExp_code {Q P f : Ordinal.{0}} (hQ : SC Q) (hd : leWe f ∣ P)
    (hz : UgC S (1 + 1) Q (P + leWe f)) : UgC S (1 + 1) Q f := by
  have hk := ugTwo_ne
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  obtain ⟨q, rfl⟩ := hd
  have hm := ugC_mod hQ hk (Om (1 + 1) * f + 1) hz
  have e1 : ω ^ (Om (1 + 1) * f + 1) = leWe f * ω := by unfold leWe; rw [opow_add, opow_one]
  have e2 : leWe f * q + leWe f = leWe f * (q + 1) := (mul_add_one _ _).symm
  rw [e1, e2, Ordinal.mul_mod_mul, tuMod_succ] at hm
  have hlog := (ugCDec hQ hk _ hm).2
  have hm0 : q % ω + 1 ≠ 0 := (zero_lt_one.trans_le le_add_self).ne'
  have hlt : q % ω + 1 < ω := isSuccLimit_omega0.add_one_lt (Ordinal.mod_lt q omega0_pos.ne')
  have e3 : log ω (leWe f * (q % ω + 1)) = Om (1 + 1) * f := by
    unfold leWe
    have := log_opow_mul_add (b := ω) (u := Om (1 + 1) * f) (v := q % ω + 1) (w := 0) one_lt_omega0 hm0
      (opow_pos _ omega0_pos)
    rw [add_zero] at this
    rw [this, log_eq_zero hlt, add_zero]
  rw [e3] at hlog
  have := ugC_div hQ hk _ hlog
  rwa [Ordinal.mul_div_cancel _ hW0] at this

/-- **THE HEAD LEMMA FOR LEVEL-2 CODES**: a code `z` with `P + W^g ≤ z ≤ P + W^f` (`W^f ∣ P`) gives the code `P`
and a code `h` with `g ≤ h ≤ f`. -/
theorem uqHeadE {Q P g f z : Ordinal.{0}} (hQ : SC Q) (hd : leWe f ∣ P) (h1 : P + leWe g ≤ z)
    (h2 : z ≤ P + leWe f) (hz : UgC S (1 + 1) Q z) :
    UgC S (1 + 1) Q P ∧ ∃ h, g ≤ h ∧ h ≤ f ∧ UgC S (1 + 1) Q h := by
  have hk := ugTwo_ne
  obtain ⟨x, rfl⟩ := exists_add_of_le (le_self_add.trans h1 : P ≤ z)
  have hx1 : leWe g ≤ x := (add_le_add_iff_left P).1 h1
  have hx2 : x ≤ leWe f := (add_le_add_iff_left P).1 h2
  rcases hx2.lt_or_eq with hx | rfl
  · have hxm : (P + x) % leWe f = x := by
      obtain ⟨q, rfl⟩ := hd
      rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hx]
    have hxc : UgC S (1 + 1) Q x := by
      have h := ugC_mod hQ hk (Om (1 + 1) * f) hz
      have e : ω ^ (Om (1 + 1) * f) = leWe f := rfl
      rwa [e, hxm] at h
    obtain ⟨hhc, -, -⟩ := ugC_cnf hQ hxc
    obtain ⟨hgh, hhf⟩ := sjLogW hx1 hx
    have hh1 : UgC S (1 + 1) Q (sgLW x + 1) := UgC.add hhc (UgC.small (gg_one_lt_of_SC hQ))
    have hd1 : leWe (sgLW x + 1) ∣ P := (tuWe_dvd (Order.add_one_le_of_lt hhf)).trans hd
    have hxl : x < leWe (sgLW x + 1) := sgLW_lt x
    have hP : leWe (sgLW x + 1) * ((P + x) / leWe (sgLW x + 1)) = P := by
      obtain ⟨p, rfl⟩ := hd1
      rw [Ordinal.mul_add_div _ (leWe_pos _).ne', Ordinal.div_eq_zero_of_lt hxl, add_zero]
    have := uqMulW hQ hh1 (uqDivW hQ hh1 hz)
    rw [hP] at this
    exact ⟨this, sgLW x, hgh, hhf.le, hhc⟩
  · have hfc := uqExp_code hQ hd hz
    obtain ⟨q, rfl⟩ := hd
    have e : (leWe f * q + leWe f) / leWe f = q + 1 := by
      rw [← mul_add_one, Ordinal.mul_div_cancel _ (leWe_pos _).ne']
    have hq := uqDivW hQ hfc hz
    rw [e] at hq
    have hgf : g ≤ f := by
      by_contra hc; push Not at hc
      exact absurd hx1 (not_le.2 (leWe_lt hc))
    exact ⟨uqMulW hQ hfc (uqC_pred hQ hk q hq), f, hgf, le_rfl, hfc⟩

/-- A level-2 code `h` with `e ≤ h ≤ e + 1` gives the code `e`. -/
theorem uqCl_of_succ {Q e h : Ordinal.{0}} (hQ : SC Q) (h1 : e ≤ h) (h2 : h ≤ e + 1)
    (hh : UgC S (1 + 1) Q h) : UgC S (1 + 1) Q e := by
  rcases h1.lt_or_eq with hlt | rfl
  · have : h = e + 1 := le_antisymm h2 (Order.add_one_le_of_lt hlt)
    subst this; exact uqC_pred hQ ugTwo_ne e hh
  · exact hh

/-- **A level-2 code `P + W^e·c`** (`W^{e+1} ∣ P`, `1 ≤ c < Ω₂`) **gives the codes `P` and `e`, and `c < Q`.** -/
theorem uqCodeHeadX {Q P e c : Ordinal.{0}} (hQ : SC Q) (hd : leWe (e + 1) ∣ P) (hc1 : 1 ≤ c)
    (hcW : c < Om (1 + 1)) (h : UgC S (1 + 1) Q (P + leWe e * c)) :
    UgC S (1 + 1) Q P ∧ UgC S (1 + 1) Q e ∧ c < Q := by
  have h1 : P + leWe e ≤ P + leWe e * c :=
    (add_le_add_iff_left P).2 ((mul_one (leWe e)).symm.le.trans (mul_le_mul_right hc1 _))
  have h2 : P + leWe e * c ≤ P + leWe (e + 1) := by
    rw [leWe_succ]; exact (add_le_add_iff_left P).2 (mul_le_mul_right hcW.le _)
  obtain ⟨hP, hh, heh, hhf, hhc⟩ := uqHeadE hQ hd h1 h2 h
  have hec := uqCl_of_succ hQ heh hhf hhc
  have hdiv := uqDivW hQ hec h
  obtain ⟨p, rfl⟩ := hd
  have e1 : (leWe (e + 1) * p + leWe e * c) / leWe e = Om (1 + 1) * p + c := by
    rw [leWe_succ, mul_assoc, ← mul_add, Ordinal.mul_div_cancel _ (leWe_pos _).ne']
  rw [e1] at hdiv
  exact ⟨hP, hec, (uqHead hQ (dvd_mul_right _ _) hcW hdiv).2.2⟩

/-- **A level-`k` code `x < ω^{Ω_k·e}·Ω_k` is below `ω^{Ω_k·e}·c'` for some `c' < Q`.** -/
theorem uqCofK {k Q e x : Ordinal.{0}} (hQ : SC Q) (hk : k ≠ 0) (hx : UgC S k Q x)
    (hxe : x < ω ^ (Om k * e) * Om k) : ∃ c', c' < Q ∧ x < ω ^ (Om k * e) * c' := by
  have hκ : SC (Om k) := SC_Om hk
  have hκ0 : Om k ≠ 0 := hκ.1.ne'
  rcases lt_or_ge x (ω ^ (Om k * e)) with hlt | hge
  · exact ⟨1, gg_one_lt_of_SC hQ, by rwa [mul_one]⟩
  have hx0 : x ≠ 0 := (lt_of_lt_of_le (opow_pos _ omega0_pos) hge).ne'
  have e0 : ω ^ (Om k * e) * Om k = ω ^ (Om k * e + Om k) := by rw [opow_add, gg_SC_eps hκ]
  have hL1 : Om k * e ≤ log ω x := (opow_le_iff_le_log one_lt_omega0 hx0).1 hge
  have hL2 : log ω x < Om k * e + Om k := (lt_opow_iff_log_lt one_lt_omega0 hx0).1 (e0 ▸ hxe)
  have hLc := (ugCDec hQ hk x hx).2
  have hr := ugC_mod hQ hk (Om k) hLc
  rw [gg_SC_eps hκ] at hr
  have hq : log ω x / Om k = e := by
    refine le_antisymm ?_ ((Ordinal.mul_le_iff_le_div hκ0).1 hL1)
    have : log ω x < Om k * (e + 1) := by rwa [mul_add_one]
    exact Order.lt_add_one_iff.1 ((Ordinal.lt_mul_iff_div_lt hκ0).1 this)
  have hrκ : log ω x % Om k < Om k := Ordinal.mod_lt _ hκ0
  have hrQ : log ω x % Om k < Q := ugC_lt_om hQ hr hrκ
  refine ⟨ω ^ (log ω x % Om k + 1), ldOpow_lt_SC hQ (hQ.isSuccLimit.add_one_lt hrQ), ?_⟩
  have hL : log ω x = Om k * e + log ω x % Om k := by
    conv_lhs => rw [← Ordinal.div_add_mod (log ω x) (Om k)]
    rw [hq]
  calc x < ω ^ (log ω x + 1) := by
        rw [← Order.succ_eq_add_one]; exact lt_opow_succ_log_self one_lt_omega0 x
    _ = ω ^ (Om k * e) * ω ^ (log ω x % Om k + 1) := by
        conv_lhs => rw [hL]
        rw [add_assoc, opow_add]

/-- The part of a level-2 code `e + x` below `W^f` (`W^f ∣ e`) is a code. -/
theorem uqModW {Q e f x : Ordinal.{0}} (hQ : SC Q) (hd : leWe f ∣ e) (hx : x < leWe f)
    (hw : UgC S (1 + 1) Q (e + x)) : UgC S (1 + 1) Q x := by
  have h := ugC_mod hQ ugTwo_ne (Om (1 + 1) * f) hw
  have e0 : ω ^ (Om (1 + 1) * f) = leWe f := rfl
  obtain ⟨q, hq⟩ := hd
  rwa [e0, hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hx] at h

/-- The part of a level-1 code `e + x` below `Ω^f` (`Ω^f ∣ e`) is a code. -/
theorem uqModO {Q e f x : Ordinal.{0}} (hQ : SC Q) (hd : leOe f ∣ e) (hx : x < leOe f)
    (hw : UgC S 1 Q (e + x)) : UgC S 1 Q x := by
  have h := ugC_mod hQ one_ne_zero (Om 1 * f) hw
  have e0 : ω ^ (Om 1 * f) = leOe f := rfl
  obtain ⟨q, hq⟩ := hd
  rwa [e0, hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hx] at h

end Googology.Trans.PoR.InaccPsi.R2.Uq
