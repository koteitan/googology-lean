import Googology.Trans.PoR.InaccPsi.R2.StRoad

/-!
# Codes are closed under the division by `ω^a` for every code `a`, in particular by `W^e`

`W^e = Ω₂^e = ω^{Ω₂·e}` (`Le.leWe`), codes = `Le.LeCl κ Q` (generator `κ` strongly critical, `Q` strongly critical).

* `swCl_divOp` (**THE DIVISION LEMMA: `x / ω^a` is a code for codes `x`, `a`**, one induction on `x`: the leading
  term `ω^L` with `L ≥ a` gives `ω^{L - a}`, `L - a` a code by `Le.leClDec`), `swCl_divW` (**`x / W^e` is a code
  for codes `x`, `e`**; only `Sj.sjCl_div` by `Ω₂` existed);
* `swCl_mulW` (`W^e·y` is a code), `swCl_headW` (**a code `x` gives the codes `W^e·(x / W^e)` and `x mod W^e`**:
  the part of `x` above `W^e` and the part below);
* `swCl_cnf` (**the base-`Ω₂` normal form of a code `x ≠ 0`**: `log_W x` and `x mod W^{log_W x}` are codes and the
  leading digit `x / W^{log_W x}` is below `Q`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Sg
  Googology.Trans.PoR.InaccPsi.R2.Sj

/-- **THE DIVISION LEMMA: `x / ω^a` is a code for codes `x` and `a`.** -/
theorem swCl_divOp {κ Q a : Ordinal.{0}} (hQ : SC Q) (hκ : SC κ) (ha : LeCl κ Q a) :
    ∀ x, LeCl κ Q x → LeCl κ Q (x / ω ^ a) := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Ordinal.zero_div]; exact LeCl.zero hQ.1
  obtain ⟨hsub, hlog⟩ := leClDec hQ hκ x hx
  have hlead : ω ^ log ω x ≤ x := opow_log_le_self ω hx0
  have hdec : ω ^ log ω x + (x - ω ^ log ω x) = x := Ordinal.add_sub_cancel_of_le hlead
  have hr : LeCl κ Q (x - ω ^ log ω x) := hsub _ (LeCl.opow hQ.1 hlog) hlead
  have hrlt : x - ω ^ log ω x < x := leRest_lt hx0
  have hP0 : ω ^ a ≠ 0 := (opow_pos a omega0_pos).ne'
  rcases lt_or_ge (log ω x) a with hla | hla
  · have hxa : x < ω ^ a := by
      have h1 := lt_opow_succ_log_self one_lt_omega0 x
      exact h1.trans_le (opow_le_opow_right omega0_pos (Order.succ_le_of_lt hla))
    rw [Ordinal.div_eq_zero_of_lt hxa]; exact LeCl.zero hQ.1
  · have e1 : ω ^ log ω x = ω ^ a * ω ^ (log ω x - a) := by
      conv_lhs => rw [← Ordinal.add_sub_cancel_of_le hla]
      rw [opow_add]
    have e2 : x / ω ^ a = ω ^ (log ω x - a) + (x - ω ^ log ω x) / ω ^ a :=
      calc x / ω ^ a = (ω ^ a * ω ^ (log ω x - a) + (x - ω ^ log ω x)) / ω ^ a := by rw [← e1, hdec]
        _ = ω ^ (log ω x - a) + (x - ω ^ log ω x) / ω ^ a := Ordinal.mul_add_div _ hP0 _
    rw [e2]
    exact LeCl.add (LeCl.opow hQ.1 ((leClDec hQ hκ _ hlog).1 a ha hla)) (IH _ hrlt hr)

/-- **`x / W^e` is a code** for codes `x`, `e`. -/
theorem swCl_divW {Q e x : Ordinal.{0}} (hQ : SC Q) (he : LeCl (Om (1 + 1)) Q e)
    (hx : LeCl (Om (1 + 1)) Q x) : LeCl (Om (1 + 1)) Q (x / leWe e) :=
  swCl_divOp hQ ldOm2_SC (LeCl.mulK hQ ldOm2_SC e he) x hx

/-- `W^e·y` is a code for codes `e`, `y`. -/
theorem swCl_mulW {Q e y : Ordinal.{0}} (hQ : SC Q) (he : LeCl (Om (1 + 1)) Q e)
    (hy : LeCl (Om (1 + 1)) Q y) : LeCl (Om (1 + 1)) Q (leWe e * y) :=
  rvCl_mulOp hQ (LeCl.mulK hQ ldOm2_SC e he) ldOm2_SC y hy

/-- **The part above `W^e` and the part below `W^e` of a code are codes.** -/
theorem swCl_headW {Q e x : Ordinal.{0}} (hQ : SC Q) (he : LeCl (Om (1 + 1)) Q e)
    (hx : LeCl (Om (1 + 1)) Q x) :
    LeCl (Om (1 + 1)) Q (leWe e * (x / leWe e)) ∧ LeCl (Om (1 + 1)) Q (x % leWe e) :=
  ⟨swCl_mulW hQ he (swCl_divW hQ he hx), LeCl.mod hQ.1 ldOm2_SC.isPrincipal (Om (1 + 1) * e) hx⟩

/-- **The base-`Ω₂` normal form of a code.** -/
theorem swCl_cnf {Q x : Ordinal.{0}} (hQ : SC Q) (hx : LeCl (Om (1 + 1)) Q x) :
    LeCl (Om (1 + 1)) Q (sgLW x) ∧ LeCl (Om (1 + 1)) Q (x % leWe (sgLW x)) ∧ x / leWe (sgLW x) < Q := by
  have hlog : LeCl (Om (1 + 1)) Q (log ω x) := (leClDec hQ ldOm2_SC x hx).2
  have he : LeCl (Om (1 + 1)) Q (sgLW x) := sjCl_div hQ ldOm2_SC _ hlog
  have hq : LeCl (Om (1 + 1)) Q (x / leWe (sgLW x)) := swCl_divW hQ he hx
  have hqW : x / leWe (sgLW x) < Om (1 + 1) := by
    have hW0 : leWe (sgLW x) ≠ 0 := (leWe_pos _).ne'
    have h2 : x < leWe (sgLW x) * Om (1 + 1) := by rw [← leWe_succ]; exact sgLW_lt x
    exact (Ordinal.lt_mul_iff_div_lt hW0).1 h2
  exact ⟨he, LeCl.mod hQ.1 ldOm2_SC.isPrincipal (Om (1 + 1) * sgLW x) hx, LeCl.lt_of_lt hQ hq hqW⟩

end Googology.Trans.PoR.InaccPsi.R2.Sw
