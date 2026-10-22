import Googology.Trans.PoR.InaccPsi.R2.RiFn

/-!
# The digits and the levels of the members of `Cl(a, q)`

`u_j = Ω₁^j = Le.leOe j`, `dig_j(x) = (x / u_j) mod Ω₁` (as in `Rh.rhk_digits`), `riDat j = max(j/Ω₁, j mod Ω₁)`.
A **level** of `x` is a `j < Ω₁·Ω₁` with `dig_j(x) ≠ 0`.

* `ri_dig_count` (a countable `x` has no level but `0`), `ri_dig_opow_ne` (**a level `j` of `ω^y` has `Ω₁·j ≤ y <
  Ω₁·j + Ω₁`**, so `j = y / Ω₁`), `ri_dig_eps` (an `ε`-number `p ≥ Ω₁` has no level above `1`);
* `ri_diglev` (**every member of `Cl(a, q)` has all its digits below `q` and all its levels `j` with `riDat j < q`**,
  for a strongly critical `q`, once every collapse `ψ_{Ω₁}(e)`, `e < a`, of a member `e` with these two properties is
  below `q`; the levels of `ω^y` are read off the digits of `y` at `u₁ = Ω₁` and `u₂ = Ω₁·Ω₁`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ri

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rb
  Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Trans.PoR.InaccPsi.R2.Rh

variable {S : InaccSeq.{0}}

/-- The levels condition on `x` below `q`. -/
def RiLev (q x : Ordinal.{0}) : Prop :=
  ∀ j, j < Om 1 * Om 1 → x / Le.leOe j % Om 1 ≠ 0 → riDat j < q

/-- The digits condition on `x` below `q`. -/
def RiDg (q x : Ordinal.{0}) : Prop := ∀ j : Ordinal.{0}, x / Le.leOe j % Om 1 < q

theorem ri_leOe_two : Le.leOe 2 = Om 1 * Om 1 := by
  unfold Le.leOe; rw [rd_u_eq]; congr 1
  rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one]

theorem ri_div_div (y : Ordinal.{0}) : y / (Om 1 * Om 1) = y / Om 1 / Om 1 := by
  conv_lhs => rw [← ri_div_mod y]
  exact Ordinal.mul_add_div_mul (ri_mod_lt y) _ _

/-- `riDat j < Ω₁` for `j < Ω₁·Ω₁`. -/
theorem riDat_lt_Om {j : Ordinal.{0}} (hj : j < Om 1 * Om 1) : riDat j < Om 1 :=
  riDat_lt_iff.2 ⟨(Ordinal.lt_mul_iff_div_lt rd_Om1_ne).1 hj, ri_mod_lt j⟩

/-- **A countable `x` has no level but `0`.** -/
theorem ri_dig_count {x j : Ordinal.{0}} (hx : x < Om 1) (h : x / Le.leOe j % Om 1 ≠ 0) : j = 0 := by
  by_contra hj
  have hu : Om 1 ≤ Le.leOe j := by
    rw [← Le.leOe_one]; exact Le.leOe_mono (one_le_iff_ne_zero.2 hj)
  rw [Ordinal.div_eq_zero_of_lt (hx.trans_le hu), Ordinal.zero_mod] at h
  exact h rfl

/-- **A level `j` of `ω^y` has `Ω₁·j ≤ y < Ω₁·j + Ω₁`.** -/
theorem ri_dig_opow_ne {j y : Ordinal.{0}} (h : ω ^ y / Le.leOe j % Om 1 ≠ 0) :
    Om 1 * j ≤ y ∧ y < Om 1 * j + Om 1 := by
  rcases lt_or_ge y (Om 1 * j) with hlt | hge
  · exfalso
    have : ω ^ y < Le.leOe j := by unfold Le.leOe; exact (opow_lt_opow_iff_right one_lt_omega0).2 hlt
    rw [Ordinal.div_eq_zero_of_lt this, Ordinal.zero_mod] at h
    exact h rfl
  refine ⟨hge, not_le.1 fun hge' => h ?_⟩
  set y' := y - Om 1 * j with hy'
  have hye : Om 1 * j + y' = y := Ordinal.add_sub_cancel_of_le hge
  have hy'1 : Om 1 ≤ y' := by rw [← hye] at hge'; exact (add_le_add_iff_left _).1 hge'
  have e : ω ^ y = Le.leOe j * ω ^ y' := by unfold Le.leOe; rw [← hye, opow_add]
  rw [e, Ordinal.mul_div_cancel _ (rhU_ne j)]
  have hI' : Indec (ω ^ y') := indec_iff.2 ⟨(opow_pos _ omega0_pos).ne', isPrincipal_add_omega0_opow _⟩
  have hge'' : Om 1 ≤ ω ^ y' := by rw [← Bt.Om1_opow]; exact opow_le_opow_right omega0_pos hy'1
  exact lq_mod_indec hI' hge''

/-- **An `ε`-number `p ≥ Ω₁` has no level above `1`.** -/
theorem ri_dig_eps {p j : Ordinal.{0}} (hp : ω ^ p = p) (h1 : Om 1 ≤ p) (hj : j < Om 1 * Om 1)
    (h : p / Le.leOe j % Om 1 ≠ 0) : j ≤ 1 := by
  rw [← hp] at h
  obtain ⟨hlo, hhi⟩ := ri_dig_opow_ne h
  rcases eq_or_lt_of_le h1 with e | hlt
  · rw [← e] at hlo
    by_contra hj1
    push Not at hj1
    have : Om 1 * 1 < Om 1 * j := (mul_lt_mul_iff_right₀ rb_Om1_indec.pos).2 hj1
    rw [mul_one] at this
    exact absurd hlo (not_le.2 this)
  · exfalso
    have hI : Indec p := inE_indec hp
    have h3 : Om 1 + Om 1 + Om 1 < p := hI.add_lt (hI.add_lt hlt hlt) hlt
    have hbig : Om 1 * (Om 1 * Om 1) < p := by
      have e1 : Om 1 * (Om 1 * Om 1) = ω ^ (Om 1 + Om 1 + Om 1) := by
        rw [opow_add, opow_add, Bt.Om1_opow, mul_assoc]
      rw [e1, ← hp]; exact (opow_lt_opow_iff_right one_lt_omega0).2 h3
    have hle : Om 1 * j + Om 1 ≤ Om 1 * (Om 1 * Om 1) := by
      rw [← mul_add_one]; exact mul_le_mul_right (Order.add_one_le_of_lt hj) _
    exact absurd (hhi.trans_le hle) (not_lt.2 hbig.le)

/-- The levels of `ω^y` from the digits of `y`. -/
theorem ri_lev_opow {q y : Ordinal.{0}} (hdy : RiDg q y) : RiLev q (ω ^ y) := by
  intro j hj h
  obtain ⟨hlo, hhi⟩ := ri_dig_opow_ne h
  have hye : Om 1 * j + (y - Om 1 * j) = y := Ordinal.add_sub_cancel_of_le hlo
  have hr : y - Om 1 * j < Om 1 := by rw [← hye] at hhi; exact (add_lt_add_iff_left _).1 hhi
  have hjy : y / Om 1 = j := by rw [← hye]; exact (ri_lvl hr).1
  have hjΩ : j / Om 1 < Om 1 := (Ordinal.lt_mul_iff_div_lt rd_Om1_ne).1 hj
  refine riDat_lt_iff.2 ⟨?_, ?_⟩
  · have h2 := hdy 2
    rw [ri_leOe_two, ri_div_div, hjy, Ordinal.mod_eq_of_lt hjΩ] at h2
    exact h2
  · have h1 := hdy 1
    rwa [Le.leOe_one, hjy] at h1

/-- **The digits and the levels of the members of `Cl(a, q)`** for a strongly critical `q`, once every collapse
`ψ_{Ω₁}(e)`, `e < a`, of a member `e` with digits and levels below `q` is below `q`. -/
theorem ri_diglev {a q : Ordinal.{0}} (hq : SC q)
    (hcoll : ∀ e, e < a → e ∈ S.CSet a q → RiDg q e → RiLev q e → S.psi e (Om 1) < q) :
    ∀ x, x ∈ S.CSet a q → RiDg q x ∧ RiLev q x := by
  have hqI : Indec q := lq_SC_indec hq
  have h1q : (1 : Ordinal.{0}) < q := by
    have := hq.2 0 hq.1 0 hq.1; rwa [veblen_zero_apply, opow_zero] at this
  have hopq : ∀ f, f < q → ω ^ f < q := fun f hf => by
    have := hq.2 0 hq.1 f hf; rwa [veblen_zero_apply] at this
  have hsmallD : ∀ v, v < q → RiDg q v := fun v hv j => (rhk_dig_le j v).trans_lt hv
  have hcount : ∀ v, v < Om 1 → RiLev q v := by
    intro v hv j _ h
    rw [ri_dig_count hv h]
    unfold riDat; rw [Ordinal.zero_div, Ordinal.zero_mod, max_self]; exact hq.1
  have hepsD : ∀ p, ω ^ p = p → Om 1 ≤ p → RiDg q p := by
    intro p hp h j
    have h1 := rhk_dig_opow j p
    rw [hp, lq_mod_indec (inE_indec hp) h, opow_zero] at h1
    exact h1.trans_lt h1q
  have hepsL : ∀ p, ω ^ p = p → Om 1 ≤ p → RiLev q p := by
    intro p hp h j hj hd
    have hj1 := ri_dig_eps hp h hj hd
    have hj1' : j < Om 1 := hj1.trans_lt (one_lt_omega0.trans_le (omega0_le_of_isSuccLimit
      (Om_isSuccLimit one_ne_zero)))
    rw [riDat_lt_Om1 hj1']
    exact hj1.trans_lt h1q
  have hsmall : ∀ v, v < q → v < Om 1 → RiDg q v ∧ RiLev q v := fun v hv hv1 => ⟨hsmallD v hv, hcount v hv1⟩
  have heps : ∀ p, ω ^ p = p → Om 1 ≤ p → RiDg q p ∧ RiLev q p := fun p hp h => ⟨hepsD p hp h, hepsL p hp h⟩
  intro x hx
  induction hx with
  | @small x hxb =>
    refine ⟨hsmallD x hxb, ?_⟩
    rcases lt_or_ge x (Om 1) with h1 | h1
    · exact hcount x h1
    · intro j hj _
      exact (riDat_lt_Om hj).trans_le (h1.trans hxb.le)
  | zero => exact hsmall 0 hq.1 rb_Om1_indec.pos
  | inacc n => exact heps _ (Low.opow_eq_self_of_SC (SC_I (S := S) n)) (Gg.gg_Om1_lt_I S n).le
  | inaccW => exact heps _ (Low.opow_eq_self_of_SC (SC_Iw (S := S))) (Gg.gg_Om1_lt_Iw S).le
  | @add x y _ _ ihx ihy =>
    refine ⟨fun j => (rhk_dig_add j x y).trans_lt (hqI.add_lt (ihx.1 j) (ihy.1 j)), ?_⟩
    intro j hj h
    by_cases hx0 : x / Le.leOe j % Om 1 = 0
    · by_cases hy0 : y / Le.leOe j % Om 1 = 0
      · exfalso
        have := rhk_dig_add j x y
        rw [hx0, hy0, add_zero] at this
        exact h (le_antisymm this zero_le)
      · exact ihy.2 j hj hy0
    · exact ihx.2 j hj hx0
  | @phi x y _ _ ihx ihy =>
    by_cases hv : veblen x y < Om 1
    · have hx1 : x < Om 1 := (left_le_veblen x y).trans_lt hv
      have hy1 : y < Om 1 := (right_le_veblen x y).trans_lt hv
      have hxq : x < q := by have := ihx.1 0; rwa [rhk_dig_zero, Ordinal.mod_eq_of_lt hx1] at this
      have hyq : y < q := by have := ihy.1 0; rwa [rhk_dig_zero, Ordinal.mod_eq_of_lt hy1] at this
      exact hsmall _ (hq.2 x hxq y hyq) hv
    · push Not at hv
      rcases eq_or_ne x 0 with rfl | hx0
      · rw [veblen_zero_apply]
        refine ⟨fun j => ?_, ri_lev_opow ihy.1⟩
        have hy0 := ihy.1 0
        rw [rhk_dig_zero] at hy0
        exact (rhk_dig_opow j y).trans_lt (hopq _ hy0)
      · exact heps _ (Tp.tpVeblen_fix (pos_iff_ne_zero.2 hx0)) hv
  | @om x _ _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero]; exact hsmall 0 hq.1 rb_Om1_indec.pos
    · exact heps _ (Low.opow_eq_self_of_SC (SC_Om hx0)) (Om_le_Om.2 (one_le_iff_ne_zero.2 hx0))
  | @coll π e hπ _ heC _ ihe =>
    show RiDg q (S.psi e.1 π) ∧ RiLev q (S.psi e.1 π)
    by_cases hπ1 : π = Om 1
    · subst hπ1
      exact hsmall _ (hcoll e.1 e.2 heC ihe.1 ihe.2) (psi_lt Low.InR_Om_one _)
    · exact heps _ (Low.opow_eq_self_of_SC (SC_psi hπ e.1)) (Mx.mxOm1_le_psi hπ hπ1)

end Googology.Trans.PoR.InaccPsi.R2.Ri
