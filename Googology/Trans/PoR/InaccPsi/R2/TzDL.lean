import Googology.Trans.PoR.InaccPsi.R2.TzM
import Googology.Trans.PoR.InaccPsi.R2.TlFn

/-!
# The direct hull lemma below `X`

`ψ = S.psi`, `X = Tl.tlX = ψ_{Ω₂}(Ω₂^{Ω₂})`, `W = Ω₂^{Ω₂}`, `u_j = Ω₁^j = Le.leOe j`,
`tlDatL j = Tl.tlDat (Ω₁ + j)` (the data of the level `j`, `R2.TlFn`), `TlCl q` the codes over `q` with the atoms
`F_β(y)`, `RiDg q x` (all `Ω₁`-digits of `x` below `q`), `TzG (TzK q) x` (every base-`Ω₂` component of `x` is a code
over `q` or `≥ X`).  The port of `Tf.tf_diglev` from `B_Γ` to `X`:

* `TzLev q x` (**every level `j < X` of `x` has `tlDatL j < q`**), `tz_dig_opow_lvl`, `tz_lvl_of_cl`, `tz_eps_lev`;
* `tz_diglev` (**every member `x` of `Cl(a, q)` has all its `Ω₁`-digits below `q`, all its levels `j < X` with
  `tlDatL j < q`, is a code `TlCl q x` when `x < X`, and has all its base-`Ω₂` components codes or `≥ X` when
  `x < W`**, for a strongly critical `q ≤ Ω₁`, once every collapse `ψ_{Ω₁}(e)`, `e < a`, of a member `e` with these
  digits and levels is below `q`; a collapse `ψ_{Ω₂}(e) < X` is a code by `Tz.tz_key`).

No new axiom.  New definition: `TzLev`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rb
  Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Ri Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Tl
  Googology.Trans.PoR.InaccPsi.R2.Ts Googology.Trans.PoR.InaccPsi.R2.Tw

variable {S : InaccSeq.{0}}

/-- The levels condition on `x` below `q`: every level `j < X` of `x` has `tlDatL j < q`. -/
def TzLev (q x : Ordinal.{0}) : Prop :=
  ∀ j, j < tlX → x / Le.leOe j % Om 1 ≠ 0 → tlDatL j < q

/-- The data of a level is countable. -/
theorem tz_datL_lt (j : Ordinal.{0}) : tlDatL j < Om 1 := by rw [← rj_Om1]; exact tlDat_lt_Om1 _

theorem tz_X_inE : InE (tlX : Ordinal.{0}) := Low.opow_eq_self_of_SC tlX_SC

theorem tz_Om1_mul_succ_lt {j : Ordinal.{0}} (hj : j < tlX) : Om 1 * j + Om 1 < tlX := by
  rw [← mul_add_one]
  exact tz_X_inE.mul_lt tw_Om1_lt_X (tz_X_inE.add_lt hj (gg_one_lt_of_SC tlX_SC))

/-- **A level `j < X` of `ω^y` is `y / Ω₁`, and `y < X`.** -/
theorem tz_dig_opow_lvl {j y : Ordinal.{0}} (hj : j < tlX) (h : ω ^ y / Le.leOe j % Om 1 ≠ 0) :
    y / Om 1 = j ∧ y < tlX := by
  obtain ⟨hlo, hhi⟩ := ri_dig_opow_ne h
  have hye : Om 1 * j + (y - Om 1 * j) = y := Ordinal.add_sub_cancel_of_le hlo
  have hr : y - Om 1 * j < Om 1 := by rw [← hye] at hhi; exact (add_lt_add_iff_left _).1 hhi
  refine ⟨by rw [← hye]; exact (ri_lvl hr).1, hhi.trans (tz_Om1_mul_succ_lt hj)⟩

/-- **`tlDatL (y / Ω₁) < q` for a code `y` over a strongly critical `q`.** -/
theorem tz_lvl_of_cl {q y : Ordinal.{0}} (hq : SC q) (hy : TlCl q y) : tlDatL (y / Om 1) < q := by
  unfold tlDatL
  rw [← rj_Om1]
  exact tl_cl_dat hq _ (TlCl.add TlCl.om (tl_cl_div hq y hy))

/-- **An `ε`-number `p ≥ Ω₁` that is a code over `q` when `p < X` has all its levels below `q`.** -/
theorem tz_eps_lev {q p : Ordinal.{0}} (hq : SC q) (hp : ω ^ p = p) (hcl : p < tlX → TlCl q p) :
    TzLev q p := by
  intro j hj hd
  rw [← hp] at hd
  obtain ⟨hjy, hyX⟩ := tz_dig_opow_lvl hj hd
  rw [← hjy]
  exact tz_lvl_of_cl hq (hcl hyX)

/-- An `ε`-number above `Ω₂` is `≥ W`. -/
theorem tz_not_lt_W {p : Ordinal.{0}} (hp : ω ^ p = p) (h2 : Om (1 + 1) < p) : ¬ p < leWe (Om (1 + 1)) :=
  not_lt.2 (ts_eps_ge_W hp h2)

/-- **The direct hull lemma below `X`.** For a strongly critical `q ≤ Ω₁`, once every collapse `ψ_{Ω₁}(e)`, `e < a`,
of a member `e` of `Cl(a, q)` with all digits and levels below `q` is below `q`: every member `x` of `Cl(a, q)` has all
its `Ω₁`-digits below `q`, all its levels `j < X` with `tlDatL j < q`, is a code over `q` when `x < X`, and has every
base-`Ω₂` component a code over `q` or `≥ X` when `x < W`. -/
theorem tz_diglev {a q : Ordinal.{0}} (hq : SC q) (hq1 : q ≤ Om 1)
    (hcoll : ∀ e, e < a → e ∈ S.CSet a q → RiDg q e → TzLev q e → S.psi e (Om 1) < q) :
    ∀ x, x ∈ S.CSet a q → RiDg q x ∧ TzLev q x ∧ (x < tlX → TlCl q x) ∧
      (x < leWe (Om (1 + 1)) → TzG (TzK q) x) := by
  have hqI : Indec q := lq_SC_indec hq
  have h1q : (1 : Ordinal.{0}) < q := gg_one_lt_of_SC hq
  have hopq : ∀ f, f < q → ω ^ f < q := fun f hf => by
    have := hq.2 0 hq.1 f hf; rwa [veblen_zero_apply] at this
  have hq2 : q < Om (1 + 1) := hq1.trans_lt ts_Om1_lt_Om2
  have hsmallD : ∀ v, v < q → RiDg q v := fun v hv j => (rhk_dig_le j v).trans_lt hv
  have hcount : ∀ v, v < Om 1 → TzLev q v := by
    intro v hv j _ h
    rw [ri_dig_count hv h, tlDatL_zero]; exact hq.1
  have hepsD : ∀ p, ω ^ p = p → Om 1 ≤ p → RiDg q p := by
    intro p hp h j
    have h1 := rhk_dig_opow j p
    rw [hp, lq_mod_indec (inE_indec hp) h, opow_zero] at h1
    exact h1.trans_lt h1q
  have hsmall : ∀ v, v < q → RiDg q v ∧ TzLev q v ∧ (v < tlX → TlCl q v) ∧
      (v < leWe (Om (1 + 1)) → TzG (TzK q) v) :=
    fun v hv => ⟨hsmallD v hv, hcount v (hv.trans_le hq1), fun _ => TlCl.small hv,
      fun _ => tzG_small (tzK_zero hq) (fun _ => TlCl.small hv) (hv.trans hq2)⟩
  have hX2 : (tlX : Ordinal.{0}) < Om (1 + 1) := tw_X_lt_Om2
  have hbig : ∀ p, ω ^ p = p → Om (1 + 1) < p → RiDg q p ∧ TzLev q p ∧ (p < tlX → TlCl q p) ∧
      (p < leWe (Om (1 + 1)) → TzG (TzK q) p) := by
    intro p hp h2
    have hcl : p < tlX → TlCl q p := fun h => absurd (h.trans hX2) (not_lt.2 h2.le)
    exact ⟨hepsD p hp (ts_Om1_lt_Om2.le.trans h2.le), tz_eps_lev hq hp hcl, hcl,
      fun h => absurd h (tz_not_lt_W hp h2)⟩
  have hSCmid : ∀ p, SC p → Om 1 < p → p < Om (1 + 1) → (p < tlX → TlCl q p) →
      RiDg q p ∧ TzLev q p ∧ (p < tlX → TlCl q p) ∧ (p < leWe (Om (1 + 1)) → TzG (TzK q) p) := by
    intro p hp h1 h2 hcl
    exact ⟨hepsD p (Low.opow_eq_self_of_SC hp) h1.le, tz_eps_lev hq (Low.opow_eq_self_of_SC hp) hcl, hcl,
      fun _ => tzG_small (tzK_zero hq) hcl h2⟩
  intro x hx
  induction hx with
  | @small x hxb => exact hsmall x hxb
  | zero => exact hsmall 0 hq.1
  | inacc n => exact hbig _ (Low.opow_eq_self_of_SC (SC_I (S := S) n)) (Mx.mxOm2_lt_I n)
  | inaccW => exact hbig _ (Low.opow_eq_self_of_SC (SC_Iw (S := S))) Mx.mxOm2_lt_Iw
  | @add x y _ _ ihx ihy =>
    refine ⟨fun j => (rhk_dig_add j x y).trans_lt (hqI.add_lt (ihx.1 j) (ihy.1 j)), ?_, fun h => ?_, fun h => ?_⟩
    · intro j hj h
      by_cases hx0 : x / Le.leOe j % Om 1 = 0
      · by_cases hy0 : y / Le.leOe j % Om 1 = 0
        · exfalso
          have := rhk_dig_add j x y
          rw [hx0, hy0, add_zero] at this
          exact h (le_antisymm this zero_le)
        · exact ihy.2.1 j hj hy0
      · exact ihx.2.1 j hj hx0
    · exact TlCl.add (ihx.2.2.1 (lt_of_le_of_lt le_self_add h)) (ihy.2.2.1 (lt_of_le_of_lt le_add_self h))
    · exact tzG_add tzK_add (ihx.2.2.2 (lt_of_le_of_lt le_self_add h)) (ihy.2.2.2 (lt_of_le_of_lt le_add_self h))
  | @phi x y _ _ ihx ihy =>
    have hG : veblen x y < leWe (Om (1 + 1)) → TzG (TzK q) (veblen x y) := fun h =>
      tzG_phi (tzK_zero hq) (tzK_one hq) tzK_phi (ihx.2.2.2 ((left_le_veblen x y).trans_lt h))
        (ihy.2.2.2 ((right_le_veblen x y).trans_lt h)) h
    have hcl : veblen x y < tlX → TlCl q (veblen x y) := fun h =>
      TlCl.phi (ihx.2.2.1 ((left_le_veblen x y).trans_lt h)) (ihy.2.2.1 ((right_le_veblen x y).trans_lt h))
    by_cases hv : veblen x y < Om 1
    · have hx1 : x < Om 1 := (left_le_veblen x y).trans_lt hv
      have hy1 : y < Om 1 := (right_le_veblen x y).trans_lt hv
      have hxq : x < q := by have := ihx.1 0; rwa [rhk_dig_zero, Ordinal.mod_eq_of_lt hx1] at this
      have hyq : y < q := by have := ihy.1 0; rwa [rhk_dig_zero, Ordinal.mod_eq_of_lt hy1] at this
      exact hsmall _ (hq.2 x hxq y hyq)
    · push Not at hv
      rcases eq_or_ne x 0 with rfl | hx0
      · refine ⟨fun j => ?_, fun j hj h => ?_, hcl, hG⟩
        · rw [veblen_zero_apply]
          have hy0 := ihy.1 0
          rw [rhk_dig_zero] at hy0
          exact (rhk_dig_opow j y).trans_lt (hopq _ hy0)
        · rw [veblen_zero_apply] at h
          obtain ⟨hjy, hyX⟩ := tz_dig_opow_lvl hj h
          rw [← hjy]
          exact tz_lvl_of_cl hq (ihy.2.2.1 hyX)
      · exact ⟨hepsD _ (Tp.tpVeblen_fix (pos_iff_ne_zero.2 hx0)) hv,
          tz_eps_lev hq (Tp.tpVeblen_fix (pos_iff_ne_zero.2 hx0)) hcl, hcl, hG⟩
  | @om x _ _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero]; exact hsmall 0 hq.1
    have hε : ω ^ Om x = Om x := Low.opow_eq_self_of_SC (SC_Om hx0)
    rcases lt_trichotomy (Om x) (Om (1 + 1)) with hlt | heq | hgt
    · have hx2 : x < 1 + 1 := Om_lt_Om.1 hlt
      have hx1 : x = 1 := le_antisymm (Order.lt_add_one_iff.1 hx2) (Order.one_le_iff_ne_zero.2 hx0)
      subst hx1
      have hcl : Om 1 < tlX → TlCl q (Om 1) := fun _ => by rw [← rj_Om1]; exact TlCl.om
      exact ⟨hepsD _ hε le_rfl, tz_eps_lev hq hε hcl, hcl, fun _ => tzG_small (tzK_zero hq) hcl ts_Om1_lt_Om2⟩
    · rw [heq]
      have hcl : Om (1 + 1) < tlX → TlCl q (Om (1 + 1)) := fun h => absurd (h.trans hX2) (lt_irrefl _)
      have hε2 : ω ^ Om (1 + 1) = Om (1 + 1) := ts_Om2_opow
      exact ⟨hepsD _ hε2 ts_Om1_lt_Om2.le, tz_eps_lev hq hε2 hcl, hcl, fun _ => tzG_Om2 (tzK_one hq)⟩
    · exact hbig _ hε hgt
  | @coll π e hπ _ heC _ ihe =>
    show RiDg q (S.psi e.1 π) ∧ TzLev q (S.psi e.1 π) ∧ (S.psi e.1 π < tlX → TlCl q (S.psi e.1 π)) ∧
      (S.psi e.1 π < leWe (Om (1 + 1)) → TzG (TzK q) (S.psi e.1 π))
    by_cases hπ1 : π = Om 1
    · subst hπ1
      exact hsmall _ (hcoll e.1 e.2 heC ihe.1 ihe.2.1)
    by_cases hπ2 : π = Om (1 + 1)
    · subst hπ2
      have hκ : S.InR (Om (1 + 1)) := InR_Om_succ 1
      have hcl : S.psi e.1 (Om (1 + 1)) < tlX → TlCl q (S.psi e.1 (Om (1 + 1))) := by
        intro h
        have heW : e.1 < leWe (Om (1 + 1)) := by
          by_contra hc
          push Not at hc
          have := (psi_mono hκ hc).1
          rw [ts_psiW_eq_X] at this
          exact absurd h (not_lt.2 this)
        exact tz_key hq (ihe.2.2.2 heW) h
      exact hSCmid _ (SC_psi hκ e.1) (ts_Om1_lt_psi _) (ts_psi_lt _) hcl
    · exact hbig _ (Low.opow_eq_self_of_SC (SC_psi hπ e.1)) (ts_Om2_lt_psi hπ hπ1 hπ2)

end Googology.Trans.PoR.InaccPsi.R2.Tz
