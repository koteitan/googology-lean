import Googology.Trans.PoR.InaccPsi.R2.LeUni

/-!
# Digits at transfinite positions, and `log_ω` in the closures

`κ` strongly critical, `Q` strongly critical, `LeCl κ Q` the codes over `Q` with the generator `κ` (`R2.LeDig`).

* `LeCl.mulK` (**`κ·y` is a code** for every code `y`), `leCl_boundY` (**a code below `κ^{y+1}` is below `κ^y·Q`** for
  every code `y`: the digit at position `y` is below `Q`), `leCl_boundK` (**a code below `κ·κ` is below `κ·Q`**: the
  position of the leading digit is below `Q`);
* `leLog_mem` (**`Cl(a, b)` is closed under `x ↦ log_ω x`**).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Le

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld

variable {S : InaccSeq.{0}} {κ Q : Ordinal.{0}}

theorem leRest_lt {x : Ordinal.{0}} (hx0 : x ≠ 0) : x - ω ^ log ω x < x := by
  have hlead : ω ^ log ω x ≤ x := opow_log_le_self ω hx0
  have hxlt : x < ω ^ log ω x * ω := by
    rw [← opow_succ]; exact lt_opow_succ_log_self one_lt_omega0 x
  have hdec : ω ^ log ω x + (x - ω ^ log ω x) = x := Ordinal.add_sub_cancel_of_le hlead
  refine lt_of_le_of_ne (Ordinal.sub_le_self _ _) fun e => ?_
  have h' : ω ^ log ω x + x = x := by
    calc ω ^ log ω x + x = ω ^ log ω x + (x - ω ^ log ω x) := by rw [e]
      _ = x := hdec
  have := Ordinal.add_eq_right_iff_mul_omega0_le.1 h'
  exact absurd (lt_of_lt_of_le hxlt this) (lt_irrefl _)

/-- **`κ·y` is a code** for every code `y`. -/
theorem LeCl.mulK (hQ : SC Q) (hκ : SC κ) : ∀ y, LeCl κ Q y → LeCl κ Q (κ * y) := by
  have hE : ω ^ κ = κ := gg_SC_eps hκ
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hy
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [mul_zero]; exact LeCl.zero hQ.1
  obtain ⟨hsub, hlog⟩ := leClDec hQ hκ y hy
  have hlead : ω ^ log ω y ≤ y := opow_log_le_self ω hy0
  have hdec : ω ^ log ω y + (y - ω ^ log ω y) = y := Ordinal.add_sub_cancel_of_le hlead
  have e : κ * y = ω ^ (κ + log ω y) + κ * (y - ω ^ log ω y) := by
    conv_lhs => rw [← hdec]
    rw [mul_add, opow_add, hE]
  rw [e]
  exact LeCl.add (LeCl.opow hQ.1 (LeCl.add LeCl.om hlog))
    (IH _ (leRest_lt hy0) (hsub _ (LeCl.opow hQ.1 hlog) hlead))

/-- **The digit at position `y` of a code is below `Q`**: a code below `ω^{κ·y + κ}` is below `ω^{κ·y}·Q`, for every
code `y`. -/
theorem leCl_boundY (hQ : SC Q) (hκ : SC κ) {y : Ordinal.{0}} (hy : LeCl κ Q y) :
    ∀ x, LeCl κ Q x → x < ω ^ (κ * y + κ) → x < ω ^ (κ * y) * Q := by
  have eQ : ω ^ (κ * y) * Q = ω ^ (κ * y + Q) := by rw [opow_add, gg_SC_eps hQ]
  have hpr : IsPrincipal (· + ·) (ω ^ (κ * y) * Q) := by rw [eQ]; exact isPrincipal_add_omega0_opow _
  have hκy := LeCl.mulK hQ hκ y hy
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx hxb
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [eQ]; exact opow_pos _ omega0_pos
  obtain ⟨hsub, hlog⟩ := leClDec hQ hκ x hx
  set a := log ω x with ha_def
  have hlead : ω ^ a ≤ x := opow_log_le_self ω hx0
  have hdec : ω ^ a + (x - ω ^ a) = x := Ordinal.add_sub_cancel_of_le hlead
  have hr := IH _ (leRest_lt hx0) (hsub _ (LeCl.opow hQ.1 hlog) hlead) ((Ordinal.sub_le_self _ _).trans_lt hxb)
  have ha : a < κ * y + κ := (opow_lt_opow_iff_right one_lt_omega0).1 (hlead.trans_lt hxb)
  have hl : ω ^ a < ω ^ (κ * y) * Q := by
    rw [eQ]
    refine (opow_lt_opow_iff_right one_lt_omega0).2 ?_
    rcases lt_or_ge a (κ * y) with h | h
    · exact h.trans_le le_self_add
    · have hc : LeCl κ Q (a - κ * y) := (leClDec hQ hκ a hlog).1 _ hκy h
      have hdec' : κ * y + (a - κ * y) = a := Ordinal.add_sub_cancel_of_le h
      have hcκ : a - κ * y < κ := by
        have : κ * y + (a - κ * y) < κ * y + κ := by rw [hdec']; exact ha
        exact (add_lt_add_iff_left _).1 this
      rw [← hdec']
      exact (add_lt_add_iff_left _).2 (LeCl.lt_of_lt hQ hc hcκ)
  rw [← hdec]; exact hpr hl hr

/-- **The position of the leading digit of a code is below `Q`**: a code below `κ·κ` is below `κ·Q`. -/
theorem leCl_boundK (hQ : SC Q) (hκ : SC κ) : ∀ x, LeCl κ Q x → x < κ * κ → x < κ * Q := by
  have hE : ω ^ κ = κ := gg_SC_eps hκ
  have eQ : κ * Q = ω ^ (κ + Q) := by rw [opow_add, hE, gg_SC_eps hQ]
  have eK : κ * κ = ω ^ (κ + κ) := by rw [opow_add, hE]
  have hpr : IsPrincipal (· + ·) (κ * Q) := by rw [eQ]; exact isPrincipal_add_omega0_opow _
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx hxb
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [eQ]; exact opow_pos _ omega0_pos
  obtain ⟨hsub, hlog⟩ := leClDec hQ hκ x hx
  set a := log ω x with ha_def
  have hlead : ω ^ a ≤ x := opow_log_le_self ω hx0
  have hdec : ω ^ a + (x - ω ^ a) = x := Ordinal.add_sub_cancel_of_le hlead
  have hr := IH _ (leRest_lt hx0) (hsub _ (LeCl.opow hQ.1 hlog) hlead) ((Ordinal.sub_le_self _ _).trans_lt hxb)
  have ha : a < κ + κ := by
    rw [eK] at hxb; exact (opow_lt_opow_iff_right one_lt_omega0).1 (hlead.trans_lt hxb)
  have hl : ω ^ a < κ * Q := by
    rw [eQ]
    refine (opow_lt_opow_iff_right one_lt_omega0).2 ?_
    rcases lt_or_ge a κ with h | h
    · exact h.trans_le le_self_add
    · have hc : LeCl κ Q (a - κ) := (leClDec hQ hκ a hlog).1 _ LeCl.om h
      have hdec' : κ + (a - κ) = a := Ordinal.add_sub_cancel_of_le h
      have hcκ : a - κ < κ := by
        have : κ + (a - κ) < κ + κ := by rw [hdec']; exact ha
        exact (add_lt_add_iff_left _).1 this
      rw [← hdec']
      exact (add_lt_add_iff_left _).2 (LeCl.lt_of_lt hQ hc hcκ)
  rw [← hdec]; exact hpr hl hr

/-- **`Cl(a, b)` is closed under `x ↦ log_ω x`.** -/
theorem leLog_mem {a b x : Ordinal.{0}} (hx : x ∈ S.CSet a b) : log ω x ∈ S.CSet a b := by
  have fix : ∀ {p : Ordinal.{0}}, ω ^ p = p → p ∈ S.CSet a b → log ω p ∈ S.CSet a b := by
    intro p hpE hpC
    have : log ω p = p := by conv_lhs => rw [← hpE]; exact log_opow one_lt_omega0 _
    rw [this]; exact hpC
  induction hx with
  | small h => exact CSet.of_lt ((log_le_self ω _).trans_lt h)
  | zero => rw [log_zero_right]; exact CSet.zero_mem a b
  | inacc n => exact fix (Low.opow_eq_self_of_SC (SC_I (S := S) n)) (CSet.I_mem a b n)
  | inaccW => exact fix (Low.opow_eq_self_of_SC (SC_Iw (S := S))) (CSet.Iw_mem a b)
  | @add x y _ _ ihx ihy =>
    rcases ggLog_add x y with e | e <;> rw [e]
    · exact ihx
    · exact ihy
  | @phi x y hx hy _ _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [veblen_zero_apply, log_opow one_lt_omega0]; exact hy
    · exact fix (gg_veblen_eps hx0) (CSet.phi_mem hx hy)
  | @om x hx _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero, log_zero_right]; exact CSet.zero_mem a b
    · exact fix (Low.opow_eq_self_of_SC (SC_Om hx0)) (CSet.Om_mem hx)
  | @coll π e hπ hπC heC _ _ =>
    exact fix (Low.opow_eq_self_of_SC (SC_psi hπ e.1)) (CSet.psi_mem e.2 hπ hπC heC)

end Googology.Trans.PoR.InaccPsi.R2.Le
