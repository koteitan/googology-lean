import Googology.Trans.PoR.InaccPsi.R2.SsFwd

/-!
# The digits and the levels below `Γ_{Ω₁+1}` of the members of `Cl(a, q)`, on the generic data

`u_j = Ω₁^j = Le.leOe j`, `dig_j(x) = (x / u_j) mod Ω₁`, `ssDatL j = Ss.ssDat (Ω₁ + j)` (the data of the level `j` on
Veblen normal forms, `R2.SsFn`), `Γ_{Ω₁+1} = Gg.ggGam`.  A **level** of `x` is a `j < Γ_{Ω₁+1}` with `dig_j(x) ≠ 0`.
`R2.RkDig` checks the levels `j < ε_{Ω₁+1}` only (with `Rk.rkDat`); here every level below `Γ_{Ω₁+1}` is checked.

* `SvLev q x` (**every level `j < Γ_{Ω₁+1}` of `x` has `ssDatL j < q`**);
* `sv_dig_opow_lvl` (**a level `j < Γ_{Ω₁+1}` of `ω^y` is `y / Ω₁`, with `y < Γ_{Ω₁+1}`**), `sv_lvl_of_cl` (**`ssDatL
  (y / Ω₁) < q` for a code `y` over a strongly critical `q`**), `sv_eps_lev` (**an `ε`-number `p ≥ Ω₁` that is a code
  over `q` when `p < Γ_{Ω₁+1}` has all its levels below `q`**: its only level is `p / Ω₁`);
* `sv_diglev` (**every member `x` of `Cl(a, q)` has all its digits below `q`, all its levels `j < Γ_{Ω₁+1}` with
  `ssDatL j < q`, and is a code over `q` when `x < Γ_{Ω₁+1}`**, for a strongly critical `q`, once every collapse
  `ψ_{Ω₁}(e)`, `e < a`, of a member `e` with these digit and level properties is below `q`; it extends
  `Rk.rk_diglev` from the levels `< ε_{Ω₁+1}` to the levels `< Γ_{Ω₁+1}`).

No new axiom.  New definition: the statement name `SvLev`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Sv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rb
  Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Ri
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rk Googology.Trans.PoR.InaccPsi.R2.Ss

variable {S : InaccSeq.{0}}

/-- The levels condition on `x` below `q`: every level `j < Γ_{Ω₁+1}` of `x` has `ssDatL j < q`. -/
def SvLev (q x : Ordinal.{0}) : Prop :=
  ∀ j, j < ggGam → x / Le.leOe j % Om 1 ≠ 0 → ssDatL j < q

/-- The data of a level is countable. -/
theorem sv_datL_lt (j : Ordinal.{0}) : ssDatL j < Om 1 := by rw [← Rj.rj_Om1]; exact ssDat_lt_Om1 _

theorem sv_Gam_inE : InE (ggGam : Ordinal.{0}) := Low.opow_eq_self_of_SC ggGam_spec.1

theorem sv_Om1_mul_succ_lt {j : Ordinal.{0}} (hj : j < ggGam) : Om 1 * j + Om 1 < ggGam := by
  rw [← mul_add_one]
  exact sv_Gam_inE.mul_lt ggGam_spec.2 (sv_Gam_inE.add_lt hj (gg_one_lt_of_SC ggGam_spec.1))

/-- **A level `j < Γ_{Ω₁+1}` of `ω^y` is `y / Ω₁`, and `y < Γ_{Ω₁+1}`.** -/
theorem sv_dig_opow_lvl {j y : Ordinal.{0}} (hj : j < ggGam) (h : ω ^ y / Le.leOe j % Om 1 ≠ 0) :
    y / Om 1 = j ∧ y < ggGam := by
  obtain ⟨hlo, hhi⟩ := ri_dig_opow_ne h
  have hye : Om 1 * j + (y - Om 1 * j) = y := Ordinal.add_sub_cancel_of_le hlo
  have hr : y - Om 1 * j < Om 1 := by rw [← hye] at hhi; exact (add_lt_add_iff_left _).1 hhi
  refine ⟨by rw [← hye]; exact (ri_lvl hr).1, hhi.trans (sv_Om1_mul_succ_lt hj)⟩

/-- **`ssDatL (y / Ω₁) < q` for a code `y` over a strongly critical `q`.** -/
theorem sv_lvl_of_cl {q y : Ordinal.{0}} (hq : SC q) (hy : GgCl q y) : ssDatL (y / Om 1) < q := by
  unfold ssDatL
  rw [Rj.rj_Om1]
  exact ss_cl_dat hq _ (GgCl.add GgCl.om (rk_cl_div hq y hy))

/-- **An `ε`-number `p ≥ Ω₁` that is a code over `q` when `p < Γ_{Ω₁+1}` has all its levels below `q`.** -/
theorem sv_eps_lev {q p : Ordinal.{0}} (hq : SC q) (hp : ω ^ p = p) (hcl : p < ggGam → GgCl q p) :
    SvLev q p := by
  intro j hj hd
  rw [← hp] at hd
  obtain ⟨hjy, hyG⟩ := sv_dig_opow_lvl hj hd
  rw [← hjy]
  exact sv_lvl_of_cl hq (hcl hyG)

/-- **The digits and the levels below `Γ_{Ω₁+1}` of the members of `Cl(a, q)`**, and the codes among them below
`Γ_{Ω₁+1}`, for a strongly critical `q`, once every collapse `ψ_{Ω₁}(e)`, `e < a`, of a member `e` with digits and
levels below `q` is below `q`. -/
theorem sv_diglev {a q : Ordinal.{0}} (hq : SC q)
    (hcoll : ∀ e, e < a → e ∈ S.CSet a q → RiDg q e → SvLev q e → S.psi e (Om 1) < q) :
    ∀ x, x ∈ S.CSet a q → RiDg q x ∧ SvLev q x ∧ (x < ggGam → GgCl q x) := by
  have hqI : Indec q := lq_SC_indec hq
  have h1q : (1 : Ordinal.{0}) < q := by
    have := hq.2 0 hq.1 0 hq.1; rwa [veblen_zero_apply, opow_zero] at this
  have hopq : ∀ f, f < q → ω ^ f < q := fun f hf => by
    have := hq.2 0 hq.1 f hf; rwa [veblen_zero_apply] at this
  have hsmallD : ∀ v, v < q → RiDg q v := fun v hv j => (rhk_dig_le j v).trans_lt hv
  have hcount : ∀ v, v < Om 1 → SvLev q v := by
    intro v hv j _ h
    rw [ri_dig_count hv h, ssDatL_zero]; exact hq.1
  have hepsD : ∀ p, ω ^ p = p → Om 1 ≤ p → RiDg q p := by
    intro p hp h j
    have h1 := rhk_dig_opow j p
    rw [hp, lq_mod_indec (inE_indec hp) h, opow_zero] at h1
    exact h1.trans_lt h1q
  have hsmall : ∀ v, v < q → v < Om 1 → RiDg q v ∧ SvLev q v ∧ (v < ggGam → GgCl q v) :=
    fun v hv hv1 => ⟨hsmallD v hv, hcount v hv1, fun _ => GgCl.small hv⟩
  have hbig : ∀ p, ggGam ≤ p → (p < ggGam → GgCl q p) := fun p hp h => absurd h (not_lt.2 hp)
  have hbigE : ∀ p, ω ^ p = p → ggGam ≤ p → RiDg q p ∧ SvLev q p ∧ (p < ggGam → GgCl q p) := fun p hp hG =>
    ⟨hepsD p hp (ggGam_spec.2.le.trans hG), sv_eps_lev hq hp (hbig p hG), hbig p hG⟩
  intro x hx
  induction hx with
  | @small x hxb =>
    refine ⟨hsmallD x hxb, ?_, fun _ => GgCl.small hxb⟩
    rcases lt_or_ge x (Om 1) with h1 | h1
    · exact hcount x h1
    · intro j _ _
      exact (sv_datL_lt j).trans_le (h1.trans hxb.le)
  | zero => exact hsmall 0 hq.1 rb_Om1_indec.pos
  | inacc n =>
    exact hbigE _ (Low.opow_eq_self_of_SC (SC_I (S := S) n))
      (ggGam_le (SC_I (S := S) n) (gg_Om1_lt_I S n))
  | inaccW =>
    exact hbigE _ (Low.opow_eq_self_of_SC (SC_Iw (S := S))) (ggGam_le (SC_Iw (S := S)) (gg_Om1_lt_Iw S))
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
          obtain ⟨hjy, hyG⟩ := sv_dig_opow_lvl hj h
          rw [← hjy]
          exact sv_lvl_of_cl hq (ihy.2.2 hyG)
      · exact ⟨hepsD _ (Tp.tpVeblen_fix (pos_iff_ne_zero.2 hx0)) hv,
          sv_eps_lev hq (Tp.tpVeblen_fix (pos_iff_ne_zero.2 hx0)) hcl, hcl⟩
  | @om x hx1 _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero]; exact hsmall 0 hq.1 rb_Om1_indec.pos
    · have hcl : Om x < ggGam → GgCl q (Om x) := fun h => by
        have h2 : x < 1 + 1 := Om_lt_Om.1 (h.trans_le ggGam_le_Om2)
        rcases (Order.lt_add_one_iff.1 h2).lt_or_eq with h0 | h1
        · rw [Order.lt_one_iff] at h0; exact absurd h0 hx0
        · rw [h1]; exact GgCl.om
      exact ⟨hepsD _ (Low.opow_eq_self_of_SC (SC_Om hx0)) (Om_le_Om.2 (one_le_iff_ne_zero.2 hx0)),
        sv_eps_lev hq (Low.opow_eq_self_of_SC (SC_Om hx0)) hcl, hcl⟩
  | @coll π e hπ _ heC _ ihe =>
    show RiDg q (S.psi e.1 π) ∧ SvLev q (S.psi e.1 π) ∧ (S.psi e.1 π < ggGam → GgCl q (S.psi e.1 π))
    by_cases hπ1 : π = Om 1
    · subst hπ1
      exact hsmall _ (hcoll e.1 e.2 heC ihe.1 ihe.2.1) (psi_lt Low.InR_Om_one _)
    · have hge : Om 1 ≤ S.psi e.1 π := Mx.mxOm1_le_psi hπ hπ1
      have hne : Om 1 ≠ S.psi e.1 π := fun h' =>
        psi_notMem hπ e.1 (h' ▸ CSet.Om_mem (CSet.one_mem _ _))
      exact hbigE _ (Low.opow_eq_self_of_SC (SC_psi hπ e.1))
        (ggGam_le (SC_psi hπ _) (lt_of_le_of_ne hge hne))

end Googology.Trans.PoR.InaccPsi.R2.Sv
