import Googology.Trans.PoR.InaccPsi.R2.RkFn
import Googology.Trans.PoR.InaccPsi.R2.RiDig

/-!
# The digits and the levels below `ε_{Ω₁+1}` of the members of `Cl(a, q)`

`u_j = Ω₁^j = Le.leOe j`, `dig_j(x) = (x / u_j) mod Ω₁`, `rkDat j = rjDat (Ω₁ + j)`.  A **level** of `x` is a
`j < ε_{Ω₁+1}` with `dig_j(x) ≠ 0`.

* `RkLev q x` (**every level `j` of `x` has `rkDat j < q`**); the digits condition is `Ri.RiDg q x`;
* `rk_dig_opow_lvl` (**a level `j < ε_{Ω₁+1}` of `ω^y` is `y / Ω₁`, with `y < ε_{Ω₁+1}`**), `rk_dig_eps` (**an
  `ε`-number `p ≥ Ω₁` has no level `j < ε_{Ω₁+1}` above `1`**);
* `rk_diglev` (**every member `x` of `Cl(a, q)` has all its digits below `q`, all its levels `j` with `rkDat j < q`,
  and is a code over `q` when `x < Γ_{Ω₁+1}`**, for a strongly critical `q`, once every collapse `ψ_{Ω₁}(e)`, `e < a`,
  of a member `e` with these digit and level properties is below `q`): the level of `ω^y` is `y / Ω₁`, a code over
  `q` when `y` is (`Rk.rk_cl_div`).

No new axiom.  New definition: the statement name `RkLev`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rb
  Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Ri
  Googology.Trans.PoR.InaccPsi.R2.Gg

variable {S : InaccSeq.{0}}

/-- The levels condition on `x` below `q`: every level `j < ε_{Ω₁+1}` of `x` has `rkDat j < q`. -/
def RkLev (q x : Ordinal.{0}) : Prop :=
  ∀ j, j < ggE → x / Le.leOe j % Om 1 ≠ 0 → rkDat j < q

theorem rk_Om1_mul_succ_lt {j : Ordinal.{0}} (hj : j < ggE) : Om 1 * j + Om 1 < ggE := by
  rw [← mul_add_one]
  exact rk_E_inE.mul_lt rk_Om1_E (rk_E_inE.add_lt hj ((Lu.lu_one_lt_E rk_E_inE)))

/-- **A level `j < ε_{Ω₁+1}` of `ω^y` is `y / Ω₁`, and `y < ε_{Ω₁+1}`.** -/
theorem rk_dig_opow_lvl {j y : Ordinal.{0}} (hj : j < ggE) (h : ω ^ y / Le.leOe j % Om 1 ≠ 0) :
    y / Om 1 = j ∧ y < ggE := by
  obtain ⟨hlo, hhi⟩ := ri_dig_opow_ne h
  have hye : Om 1 * j + (y - Om 1 * j) = y := Ordinal.add_sub_cancel_of_le hlo
  have hr : y - Om 1 * j < Om 1 := by rw [← hye] at hhi; exact (add_lt_add_iff_left _).1 hhi
  refine ⟨by rw [← hye]; exact (ri_lvl hr).1, hhi.trans (rk_Om1_mul_succ_lt hj)⟩

/-- **An `ε`-number `p ≥ Ω₁` has no level `j < ε_{Ω₁+1}` above `1`.** -/
theorem rk_dig_eps {p j : Ordinal.{0}} (hp : ω ^ p = p) (h1 : Om 1 ≤ p) (hj : j < ggE)
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
    have hE : ggE ≤ p := ggE_le hp hlt
    exact absurd ((hhi.trans (rk_Om1_mul_succ_lt hj)).trans_le hE) (lt_irrefl _)

/-- **The digits and the levels of the members of `Cl(a, q)`**, and the codes among them below `Γ_{Ω₁+1}`, for a
strongly critical `q`, once every collapse `ψ_{Ω₁}(e)`, `e < a`, of a member `e` with digits and levels below `q` is
below `q`. -/
theorem rk_diglev {a q : Ordinal.{0}} (hq : SC q)
    (hcoll : ∀ e, e < a → e ∈ S.CSet a q → RiDg q e → RkLev q e → S.psi e (Om 1) < q) :
    ∀ x, x ∈ S.CSet a q → RiDg q x ∧ RkLev q x ∧ (x < ggGam → GgCl q x) := by
  have hqI : Indec q := lq_SC_indec hq
  have h1q : (1 : Ordinal.{0}) < q := by
    have := hq.2 0 hq.1 0 hq.1; rwa [veblen_zero_apply, opow_zero] at this
  have hopq : ∀ f, f < q → ω ^ f < q := fun f hf => by
    have := hq.2 0 hq.1 f hf; rwa [veblen_zero_apply] at this
  have hsmallD : ∀ v, v < q → RiDg q v := fun v hv j => (rhk_dig_le j v).trans_lt hv
  have hcount : ∀ v, v < Om 1 → RkLev q v := by
    intro v hv j _ h
    rw [ri_dig_count hv h, rkDat_zero]; exact hq.1
  have hepsD : ∀ p, ω ^ p = p → Om 1 ≤ p → RiDg q p := by
    intro p hp h j
    have h1 := rhk_dig_opow j p
    rw [hp, lq_mod_indec (inE_indec hp) h, opow_zero] at h1
    exact h1.trans_lt h1q
  have hepsL : ∀ p, ω ^ p = p → Om 1 ≤ p → RkLev q p := by
    intro p hp h j hj hd
    have hj1 := rk_dig_eps hp h hj hd
    refine (rkDat_lt_iff hq hj).2 (GgCl.small (hj1.trans_lt h1q))
  have hsmall : ∀ v, v < q → v < Om 1 → RiDg q v ∧ RkLev q v ∧ (v < ggGam → GgCl q v) :=
    fun v hv hv1 => ⟨hsmallD v hv, hcount v hv1, fun _ => GgCl.small hv⟩
  have hbig : ∀ p, ggGam ≤ p → (p < ggGam → GgCl q p) := fun p hp h => absurd h (not_lt.2 hp)
  intro x hx
  induction hx with
  | @small x hxb =>
    refine ⟨hsmallD x hxb, ?_, fun _ => GgCl.small hxb⟩
    rcases lt_or_ge x (Om 1) with h1 | h1
    · exact hcount x h1
    · intro j hj _
      exact (rkDat_lt_Om1 hj).trans_le (by rw [← Rj.rj_Om1] at h1; exact h1.trans hxb.le)
  | zero => exact hsmall 0 hq.1 rb_Om1_indec.pos
  | inacc n =>
    exact ⟨hepsD _ (Low.opow_eq_self_of_SC (SC_I (S := S) n)) (gg_Om1_lt_I S n).le,
      hepsL _ (Low.opow_eq_self_of_SC (SC_I (S := S) n)) (gg_Om1_lt_I S n).le,
      hbig _ (ggGam_le (SC_I (S := S) n) (gg_Om1_lt_I S n))⟩
  | inaccW =>
    exact ⟨hepsD _ (Low.opow_eq_self_of_SC (SC_Iw (S := S))) (gg_Om1_lt_Iw S).le,
      hepsL _ (Low.opow_eq_self_of_SC (SC_Iw (S := S))) (gg_Om1_lt_Iw S).le,
      hbig _ (ggGam_le (SC_Iw (S := S)) (gg_Om1_lt_Iw S))⟩
  | @add x y _ _ ihx ihy =>
    refine ⟨fun j => (rhk_dig_add j x y).trans_lt (hqI.add_lt (ihx.1 j) (ihy.1 j)), ?_, fun h => ?_⟩
    · intro j hj h
      by_cases hx0 : x / Le.leOe j % Om 1 = 0
      · by_cases hy0 : y / Le.leOe j % Om 1 = 0
        · exfalso
          have := rhk_dig_add j x y
          rw [hx0, hy0, add_zero] at this
          exact h (le_antisymm this zero_le)
        · exact ihy.2.1 j hj hy0
      · exact ihx.2.1 j hj hx0
    · exact GgCl.add (ihx.2.2 (lt_of_le_of_lt le_self_add h)) (ihy.2.2 (lt_of_le_of_lt le_add_self h))
  | @phi x y _ _ ihx ihy =>
    by_cases hv : veblen x y < Om 1
    · have hx1 : x < Om 1 := (left_le_veblen x y).trans_lt hv
      have hy1 : y < Om 1 := (right_le_veblen x y).trans_lt hv
      have hxq : x < q := by have := ihx.1 0; rwa [rhk_dig_zero, Ordinal.mod_eq_of_lt hx1] at this
      have hyq : y < q := by have := ihy.1 0; rwa [rhk_dig_zero, Ordinal.mod_eq_of_lt hy1] at this
      exact hsmall _ (hq.2 x hxq y hyq) hv
    · push Not at hv
      have hcl : veblen x y < ggGam → GgCl q (veblen x y) := fun h =>
        GgCl.phi (ihx.2.2 ((left_le_veblen x y).trans_lt h)) (ihy.2.2 ((right_le_veblen x y).trans_lt h))
      rcases eq_or_ne x 0 with rfl | hx0
      · refine ⟨fun j => ?_, fun j hj h => ?_, hcl⟩
        · rw [veblen_zero_apply]
          have hy0 := ihy.1 0
          rw [rhk_dig_zero] at hy0
          exact (rhk_dig_opow j y).trans_lt (hopq _ hy0)
        · rw [veblen_zero_apply] at h
          obtain ⟨hjy, hyE⟩ := rk_dig_opow_lvl hj h
          have hyC : GgCl q y := ihy.2.2 (hyE.trans_le ggE_le_ggGam)
          rw [rkDat_lt_iff hq hj, ← hjy]
          exact rk_cl_div hq y hyC
      · exact ⟨hepsD _ (Tp.tpVeblen_fix (pos_iff_ne_zero.2 hx0)) hv,
          hepsL _ (Tp.tpVeblen_fix (pos_iff_ne_zero.2 hx0)) hv, hcl⟩
  | @om x hx1 _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero]; exact hsmall 0 hq.1 rb_Om1_indec.pos
    · refine ⟨hepsD _ (Low.opow_eq_self_of_SC (SC_Om hx0)) (Om_le_Om.2 (one_le_iff_ne_zero.2 hx0)),
        hepsL _ (Low.opow_eq_self_of_SC (SC_Om hx0)) (Om_le_Om.2 (one_le_iff_ne_zero.2 hx0)), fun h => ?_⟩
      have h2 : x < 1 + 1 := Om_lt_Om.1 (h.trans_le ggGam_le_Om2)
      rcases (Order.lt_add_one_iff.1 h2).lt_or_eq with h0 | h1
      · rw [Order.lt_one_iff] at h0; exact absurd h0 hx0
      · rw [h1]; exact GgCl.om
  | @coll π e hπ _ heC _ ihe =>
    show RiDg q (S.psi e.1 π) ∧ RkLev q (S.psi e.1 π) ∧ (S.psi e.1 π < ggGam → GgCl q (S.psi e.1 π))
    by_cases hπ1 : π = Om 1
    · subst hπ1
      exact hsmall _ (hcoll e.1 e.2 heC ihe.1 ihe.2.1) (psi_lt Low.InR_Om_one _)
    · have hge : Om 1 ≤ S.psi e.1 π := Mx.mxOm1_le_psi hπ hπ1
      have hne : Om 1 ≠ S.psi e.1 π := fun h' =>
        psi_notMem hπ e.1 (h' ▸ CSet.Om_mem (CSet.one_mem _ _))
      exact ⟨hepsD _ (Low.opow_eq_self_of_SC (SC_psi hπ e.1)) hge,
        hepsL _ (Low.opow_eq_self_of_SC (SC_psi hπ e.1)) hge,
        hbig _ (ggGam_le (SC_psi hπ _) (lt_of_le_of_ne hge hne))⟩

end Googology.Trans.PoR.InaccPsi.R2.Rk
