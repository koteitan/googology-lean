import Googology.Trans.PoR.InaccPsi.R2.RdTh
import Googology.Trans.PoR.InaccPsi.R2.RbMove
import Googology.Trans.PoR.InaccPsi.R2.LeEMove

/-!
# `ψ_{Ω₁}(B + Ω₁·D)` is the `D`-th fixed point of `Γ_` above `ψ_{Ω₁}(B)`, and `B_n` there

`ψ = S.psi`, `Γ_ = Ordinal.gamma`, `F = Ordinal.deriv Γ_` (the enumeration of the fixed points of `Γ_`), `u = Ω₁·Ω₁`,
`B_n = Bc.bcB S n`, `σ = bcSig (bcPre (n+1)) bcPreW`, `α_k`, `α_ω` as in `R2.RbPsi`.  An argument `B` is *own* when
`B ∈ Cl(B, ψ_{Ω₁}(B))`.  The *digits* of `x` are `x mod Ω₁` and `(x / Ω₁) mod Ω₁`.

* `rd_digits` (**every member of `Cl(a, q)` has both digits below `q`**, for a strongly critical `q`, once the collapses
  `ψ_{Ω₁}(e)`, `e < a`, of members with small digits are below `q`), `rd_dig_add`, `rd_dig_opow`, `rd_dig_eps`;
* `rd_psi_le_gamma` (`ψ_{Ω₁}(A) ≤ Γ_z` gives `ψ_{Ω₁}(A + r) ≤ Γ_{z+r}`), `rd_psi_inv` (**`ψ_{Ω₁}(B + Ω₁·D) ≤ q`** for a
  fixed point `q` of `Γ_` when `Ω₁ ∣ B`, `ψ_{Ω₁}(B) < q`, `D ≤ Ω₁` and `ψ_{Ω₁}(B + Ω₁·d) < q` for `d < D`, `d < q`),
  `rd_psi_F_le` (**`ψ_{Ω₁}(B + Ω₁·D) ≤ F(c + D)`** when `ψ_{Ω₁}(B) ≤ F(c)`);
* `rd_psi_F_of` (**`ψ_{Ω₁}(B + Ω₁·D) = F(c + D)` and `D` is valid** when `d < F(c+d)` for every `d ≤ D`, `B` own,
  `Ω₁ ∣ B`, `F(c) = ψ_{Ω₁}(B)`), `rd_psi_F_valid` (**a valid `D` has `d < F(c+d)` for every `d ≤ D`**);
* `rd_base_below_F` (the largest point below `x` that is `τ` or a fixed point of `F` above `τ`), `rd_mod2_mem`
  (`Cl(a, b)` contains `Ω₁·(Ω₁·(x/Ω₁/Ω₁))` with `x`), `rd_fix_psiOm1` (`ψ_{Ω₁}(Ω₁)` is a fixed point of `Γ_`);
* `rd_fix2_of_dvd` (**`ψ_{Ω₁}(B)` is a fixed point of `F` for every own `B ≠ 0` with `Ω₁·Ω₁ ∣ B`**), `rd_dvd2_of_fix`
  (**the converse**);
* `rdB_psi_baseD` (`Rb.rbB_psi_base` with `d` in the normal-form domain `Mv.MvD` instead of `d < L(ω)`), `rdB_psi_Om1`
  (**`B_n(ψ_{Ω₁}(B + Ω₁·D)) = ψ_{Ω₁}(B' + Ω₁·B_n D)`**), `rd_dvd2_sig`, `rdB_dvd2` (**`σ` keeps `Ω₁·Ω₁ ∣ ·`**),
  `rd_dvd2_A` (**`Ω₁·Ω₁ ∣ A_η`**).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Sf Googology.Trans.PoR.InaccPsi.R2.Lq
  Googology.Trans.PoR.InaccPsi.R2.Rb

variable {S : InaccSeq.{0}}

/-! ## Digits -/

theorem rd_Om1_ne : (Om 1 : Ordinal.{0}) ≠ 0 := rb_Om1_indec.ne_zero

theorem rd_div_le (x : Ordinal.{0}) : x / Om 1 ≤ x :=
  (le_mul_right (x / Om 1) rb_Om1_indec.pos).trans (Ordinal.mul_div_le x (Om 1))

/-- `d ≤ (b + d) mod Ω₁` for `d < Ω₁`. -/
theorem rd_le_mod_add (b : Ordinal.{0}) {d : Ordinal.{0}} (hd : d < Om 1) : d ≤ (b + d) % Om 1 := by
  have h0 := rd_Om1_ne
  have hr : b % Om 1 + d < Om 1 := rb_Om1_indec.add_lt (Ordinal.mod_lt b h0) hd
  have e : b + d = Om 1 * (b / Om 1) + (b % Om 1 + d) := by
    rw [← add_assoc, Ordinal.div_add_mod]
  rw [e, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]
  exact le_add_self

/-- `((x + y)/Ω₁) mod Ω₁ ≤ (x/Ω₁) mod Ω₁ + (y/Ω₁) mod Ω₁`. -/
theorem rd_dig_add (x y : Ordinal.{0}) :
    (x + y) / Om 1 % Om 1 ≤ x / Om 1 % Om 1 + y / Om 1 % Om 1 := by
  have h0 := rd_Om1_ne
  have hx := Ordinal.div_add_mod x (Om 1)
  have hy := Ordinal.div_add_mod y (Om 1)
  have hxr : x % Om 1 < Om 1 := Ordinal.mod_lt x h0
  rcases eq_or_ne (y / Om 1) 0 with hq | hq
  · have e : x + y = Om 1 * (x / Om 1) + (x % Om 1 + y % Om 1) := by
      conv_lhs => rw [← hx, ← hy]
      rw [hq, mul_zero, zero_add, add_assoc]
    have hr : x % Om 1 + y % Om 1 < Om 1 := lq_Om1_indec.add_lt hxr (Ordinal.mod_lt y h0)
    rw [e, Ordinal.mul_add_div _ h0, Ordinal.div_eq_zero_of_lt hr, add_zero]
    exact le_self_add
  · have e : x + y = Om 1 * (x / Om 1 + y / Om 1) + y % Om 1 := by
      conv_lhs => rw [← hx, ← hy]
      rw [add_assoc, ← add_assoc (x % Om 1), lq_absorb hxr (one_le_iff_ne_zero.2 hq), ← add_assoc, ← mul_add]
    rw [e, Ordinal.mul_add_div _ h0, Ordinal.div_eq_zero_of_lt (Ordinal.mod_lt y h0), add_zero]
    exact lq_mod_add_le _ _

/-- The digits of `ω^y` for `y ≥ Ω₁`: `0` and at most `ω^{y mod Ω₁}`. -/
theorem rd_dig_opow {y : Ordinal.{0}} (h : Om 1 ≤ y) :
    ω ^ y % Om 1 = 0 ∧ ω ^ y / Om 1 % Om 1 ≤ ω ^ (y % Om 1) := by
  have h0 := rd_Om1_ne
  have hI : Indec (ω ^ y) := indec_iff.2 ⟨(opow_pos _ omega0_pos).ne', isPrincipal_add_omega0_opow _⟩
  have hge : Om 1 ≤ ω ^ y := by rw [← Bt.Om1_opow]; exact opow_le_opow_right omega0_pos h
  refine ⟨lq_mod_indec hI hge, ?_⟩
  set y' := y - Om 1 with hy'
  have hye : Om 1 + y' = y := Ordinal.add_sub_cancel_of_le h
  have e : ω ^ y = Om 1 * ω ^ y' := by rw [← hye, opow_add, Bt.Om1_opow]
  rw [e, Ordinal.mul_div_cancel _ h0]
  rcases lt_or_ge y' (Om 1) with hlt | hge'
  · have hlt' : ω ^ y' < Om 1 := by
      rw [← Bt.Om1_opow]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hlt
    rw [Ordinal.mod_eq_of_lt hlt']
    have hym : y % Om 1 = y' := by
      rw [← hye]
      have := Ordinal.mul_add_mod_self (Om 1) 1 y'
      rw [mul_one] at this
      rw [this, Ordinal.mod_eq_of_lt hlt]
    rw [hym]
  · have hI' : Indec (ω ^ y') := indec_iff.2 ⟨(opow_pos _ omega0_pos).ne', isPrincipal_add_omega0_opow _⟩
    have hge'' : Om 1 ≤ ω ^ y' := by rw [← Bt.Om1_opow]; exact opow_le_opow_right omega0_pos hge'
    rw [lq_mod_indec hI' hge'']; exact zero_le

/-- The digits of an `ε`-number `p ≥ Ω₁`: `0` and at most `1`. -/
theorem rd_dig_eps {p : Ordinal.{0}} (hp : ω ^ p = p) (h : Om 1 ≤ p) : p % Om 1 = 0 ∧ p / Om 1 % Om 1 ≤ 1 := by
  have := rd_dig_opow h
  rw [hp] at this
  exact ⟨this.1, this.2.trans (by rw [this.1, opow_zero])⟩

/-- **Every member of `Cl(a, q)` has both digits below `q`** for a strongly critical `q`, once every collapse
`ψ_{Ω₁}(e)`, `e < a`, of a member `e` with digits below `q` is below `q`. -/
theorem rd_digits {a q : Ordinal.{0}} (hq : SC q)
    (hcoll : ∀ e, e < a → e ∈ S.CSet a q → e % Om 1 < q → e / Om 1 % Om 1 < q → S.psi e (Om 1) < q) :
    ∀ x, x ∈ S.CSet a q → x % Om 1 < q ∧ x / Om 1 % Om 1 < q := by
  have hqI : Indec q := lq_SC_indec hq
  have h1q : (1 : Ordinal.{0}) < q := by
    have := hq.2 0 hq.1 0 hq.1; rwa [veblen_zero_apply, opow_zero] at this
  have hopq : ∀ f, f < q → ω ^ f < q := fun f hf => by
    have := hq.2 0 hq.1 f hf; rwa [veblen_zero_apply] at this
  have heps : ∀ p, ω ^ p = p → Om 1 ≤ p → p % Om 1 < q ∧ p / Om 1 % Om 1 < q := fun p hp h => by
    have := rd_dig_eps hp h
    exact ⟨by rw [this.1]; exact hq.1, this.2.trans_lt h1q⟩
  intro x hx
  induction hx with
  | @small x hxb =>
    exact ⟨(Ordinal.mod_le x _).trans_lt hxb, ((Ordinal.mod_le _ _).trans (rd_div_le x)).trans_lt hxb⟩
  | zero => rw [Ordinal.zero_mod, Ordinal.zero_div, Ordinal.zero_mod]; exact ⟨hq.1, hq.1⟩
  | inacc n => exact heps _ (Low.opow_eq_self_of_SC (SC_I (S := S) n)) (Gg.gg_Om1_lt_I S n).le
  | inaccW => exact heps _ (Low.opow_eq_self_of_SC (SC_Iw (S := S))) (Gg.gg_Om1_lt_Iw S).le
  | @add x y _ _ ihx ihy =>
    exact ⟨(lq_mod_add_le x y).trans_lt (hqI.add_lt ihx.1 ihy.1),
      (rd_dig_add x y).trans_lt (hqI.add_lt ihx.2 ihy.2)⟩
  | @phi x y _ _ ihx ihy =>
    by_cases hv : veblen x y < Om 1
    · have hx1 : x < Om 1 := (left_le_veblen x y).trans_lt hv
      have hy1 : y < Om 1 := (right_le_veblen x y).trans_lt hv
      have hxq : x < q := by have := ihx.1; rwa [Ordinal.mod_eq_of_lt hx1] at this
      have hyq : y < q := by have := ihy.1; rwa [Ordinal.mod_eq_of_lt hy1] at this
      rw [Ordinal.mod_eq_of_lt hv, Ordinal.div_eq_zero_of_lt hv, Ordinal.zero_mod]
      exact ⟨hq.2 x hxq y hyq, hq.1⟩
    · push Not at hv
      rcases eq_or_ne x 0 with rfl | hx0
      · rw [veblen_zero_apply] at hv ⊢
        have hy : Om 1 ≤ y := by
          rw [← Bt.Om1_opow] at hv; exact (opow_le_opow_iff_right one_lt_omega0).1 hv
        have hd := rd_dig_opow hy
        exact ⟨by rw [hd.1]; exact hq.1, hd.2.trans_lt (hopq _ ihy.1)⟩
      · exact heps _ (Tp.tpVeblen_fix (pos_iff_ne_zero.2 hx0)) hv
  | @om x _ _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero, Ordinal.zero_mod, Ordinal.zero_div, Ordinal.zero_mod]
      exact ⟨hq.1, hq.1⟩
    · exact heps _ (Low.opow_eq_self_of_SC (SC_Om hx0)) (Om_le_Om.2 (one_le_iff_ne_zero.2 hx0))
  | @coll π e hπ _ heC _ ihe =>
    show S.psi e.1 π % Om 1 < q ∧ S.psi e.1 π / Om 1 % Om 1 < q
    by_cases hπ1 : π = Om 1
    · subst hπ1
      have hlt := psi_lt (S := S) Low.InR_Om_one e.1
      rw [Ordinal.mod_eq_of_lt hlt, Ordinal.div_eq_zero_of_lt hlt, Ordinal.zero_mod]
      exact ⟨hcoll e.1 e.2 heC ihe.1 ihe.2, hq.1⟩
    · exact heps _ (Low.opow_eq_self_of_SC (SC_psi hπ e.1)) (Mx.mxOm1_le_psi hπ hπ1)


/-! ## `ψ_{Ω₁}(B + Ω₁·D)` and `F` -/

/-- `ψ_{Ω₁}(A) ≤ Γ_z` gives `ψ_{Ω₁}(A + r) ≤ Γ_{z+r}` for every `r`. -/
theorem rd_psi_le_gamma {A z : Ordinal.{0}} (hz : S.psi A (Om 1) ≤ gamma z) :
    ∀ r, S.psi (A + r) (Om 1) ≤ gamma (z + r) := by
  intro r
  induction r using WellFoundedLT.induction with
  | ind r IH =>
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [add_zero, add_zero]; exact hz
  refine lq_psi_le (lq_gamma_SC _) ?_ fun d hd => ?_
  · exact hz.trans_lt (gamma_lt_gamma.2 (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hr0)))
  · exact (IH d hd).trans_lt (gamma_lt_gamma.2 ((add_lt_add_iff_left _).2 hd))

/-- **`ψ_{Ω₁}(B + Ω₁·D) ≤ q`** for a fixed point `q` of `Γ_` when `Ω₁ ∣ B`, `ψ_{Ω₁}(B) < q`, `D ≤ Ω₁` and
`ψ_{Ω₁}(B + Ω₁·d) < q` for every `d < D` with `d < q`. -/
theorem rd_psi_inv {B D q : Ordinal.{0}} (hB : Om 1 ∣ B) (hq : SC q) (hqf : gamma q = q)
    (hBq : S.psi B (Om 1) < q) (hD : D ≤ Om 1)
    (hprev : ∀ d, d < D → d < q → S.psi (B + Om 1 * d) (Om 1) < q) :
    S.psi (B + Om 1 * D) (Om 1) ≤ q := by
  rcases le_or_gt (Om 1) q with h1 | h1
  · exact (psi_lt Low.InR_Om_one _).le.trans h1
  have h0 := rd_Om1_ne
  have hqI : Indec q := lq_SC_indec hq
  have hcoll : ∀ e, e < B + Om 1 * D → e ∈ S.CSet (B + Om 1 * D) q → e % Om 1 < q → e / Om 1 % Om 1 < q →
      S.psi e (Om 1) < q := by
    intro e he _ hr hd
    rcases lt_or_ge e B with heB | heB
    · exact lt_of_le_of_lt (psi_mono Low.InR_Om_one heB.le).1 hBq
    set e' := e - B with he'def
    have hee : B + e' = e := Ordinal.add_sub_cancel_of_le heB
    have he' : e' < Om 1 * D := by rw [← hee] at he; exact (add_lt_add_iff_left B).1 he
    have hdD : e' / Om 1 < D := (Ordinal.lt_mul_iff_div_lt h0).1 he'
    have hdΩ : e' / Om 1 < Om 1 := hdD.trans_le hD
    have her : Om 1 * (e' / Om 1) + e' % Om 1 = e' := Ordinal.div_add_mod e' (Om 1)
    obtain ⟨k, hk⟩ := hB
    have hrlt : e' % Om 1 < Om 1 := Ordinal.mod_lt _ h0
    have he_eq : e = Om 1 * (k + e' / Om 1) + e' % Om 1 := by
      rw [← hee]
      conv_lhs => rw [← her, hk]
      rw [← add_assoc, ← mul_add]
    have hrmod : e % Om 1 = e' % Om 1 := by
      rw [he_eq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hrlt]
    have hdiv : e / Om 1 = k + e' / Om 1 := by
      rw [he_eq, Ordinal.mul_add_div _ h0, Ordinal.div_eq_zero_of_lt hrlt, add_zero]
    have hdq : e' / Om 1 < q := by
      refine lt_of_le_of_lt ?_ hd
      rw [hdiv]; exact rd_le_mod_add k hdΩ
    have hrq : e' % Om 1 < q := by rw [← hrmod]; exact hr
    have hPd := hprev _ hdD hdq
    obtain ⟨z, hz⟩ := lq_SC_gamma (SC_psi (S := S) Low.InR_Om_one (B + Om 1 * (e' / Om 1)))
    have hzq : z < q := gamma_lt_gamma.1 (by rw [hz, hqf]; exact hPd)
    have hle := rd_psi_le_gamma (S := S) hz.symm.le (e' % Om 1)
    have hee2 : B + Om 1 * (e' / Om 1) + e' % Om 1 = e := by rw [add_assoc, her, hee]
    rw [hee2] at hle
    refine hle.trans_lt ?_
    conv_rhs => rw [← hqf]
    exact gamma_lt_gamma.2 (hqI.add_lt hzq hrq)
  have hinv := rd_digits (S := S) hq hcoll
  refine psi_le_of_good (CSet.Om_mem (CSet.one_mem _ _)) fun x hx hx1 => ?_
  have := (hinv x hx).1
  rwa [Ordinal.mod_eq_of_lt hx1] at this

/-- **`ψ_{Ω₁}(B + Ω₁·D) ≤ F(c + D)`** for every `D ≤ Ω₁` when `Ω₁ ∣ B` and `ψ_{Ω₁}(B) ≤ F(c)`. -/
theorem rd_psi_F_le {B c : Ordinal.{0}} (hB : Om 1 ∣ B) (hc : S.psi B (Om 1) ≤ deriv gamma c) :
    ∀ D, D ≤ Om 1 → S.psi (B + Om 1 * D) (Om 1) ≤ deriv gamma (c + D) := by
  intro D
  induction D using WellFoundedLT.induction with
  | ind D IH =>
  intro hD
  rcases eq_or_ne D 0 with rfl | hD0
  · rw [mul_zero, add_zero, add_zero]; exact hc
  have hprev : ∀ d, d < D → d < deriv gamma (c + D) →
      S.psi (B + Om 1 * d) (Om 1) < deriv gamma (c + D) := fun d hd _ =>
    (IH d hd (hd.le.trans hD)).trans_lt (rdF_lt.2 ((add_lt_add_iff_left c).2 hd))
  exact rd_psi_inv hB (rdF_SC _) (rdF_fix _)
    (hc.trans_lt (rdF_lt.2 (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hD0)))) hD hprev

/-- **`ψ_{Ω₁}(B + Ω₁·D) = F(c + D)`, and `D < ψ_{Ω₁}(B + Ω₁·D)`**, when `d < F(c+d)` for every `d ≤ D`, for an own
`B` with `Ω₁ ∣ B` and `F(c) = ψ_{Ω₁}(B)`. -/
theorem rd_psi_F_of {B c : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1))) (hB : Om 1 ∣ B)
    (hc : deriv gamma c = S.psi B (Om 1)) :
    ∀ D, D < Om 1 → (∀ d, d ≤ D → d < deriv gamma (c + d)) →
      D < S.psi (B + Om 1 * D) (Om 1) ∧ S.psi (B + Om 1 * D) (Om 1) = deriv gamma (c + D) := by
  intro D
  induction D using WellFoundedLT.induction with
  | ind D IH =>
  intro hDΩ hcond
  have hIH : ∀ d, d < D → S.psi (B + Om 1 * d) (Om 1) = deriv gamma (c + d) :=
    fun d hd => (IH d hd (hd.trans hDΩ) fun d' hd' => hcond d' (hd'.trans hd.le)).2
  have heq : S.psi (B + Om 1 * D) (Om 1) = deriv gamma (c + D) := by
    rcases eq_or_ne D 0 with rfl | hD0
    · rw [mul_zero, add_zero, add_zero, hc]
    set v := S.psi (B + Om 1 * D) (Om 1) with hv
    have hvSC : SC v := SC_psi Low.InR_Om_one _
    have hBv : S.psi B (Om 1) ≤ v := (psi_mono (S := S) Low.InR_Om_one le_self_add).1
    have hlt : ∀ d, d < D → deriv gamma (c + d) < v := by
      intro d hd
      have hle : S.psi (B + Om 1 * d) (Om 1) ≤ v :=
        (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left B).2 (mul_le_mul_right hd.le _))).1
      have hdv : d < v := (hcond d hd.le).trans_le (by rw [← hIH d hd]; exact hle)
      have hmem : B + Om 1 * d ∈ S.CSet (B + Om 1 * D) v :=
        CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add : B ≤ B + Om 1 * D)).2 hown)
          (Nm.mem_Om1_mul hdv)
      rw [← hIH d hd]
      exact psi_lt_psi_of_mem Low.InR_Om_one
        ((add_lt_add_iff_left B).2 ((mul_lt_mul_iff_right₀ rb_Om1_indec.pos).2 hd)) hmem
    apply le_antisymm
    · exact rd_psi_F_le hB hc.ge D hDΩ.le
    · rcases zero_or_succ_or_isSuccLimit D with h0 | ⟨d0, rfl⟩ | hlim
      · exact absurd h0 hD0
      · rw [Order.succ_eq_add_one] at hlt hDΩ ⊢
        have hd0v : d0 < v := (hcond d0 (Order.le_succ d0)).trans (hlt d0 (lt_add_one d0))
        have hDv : d0 + 1 < v := hvSC.add_one_lt hd0v
        have hown1 : B + Om 1 * (d0 + 1) ∈ S.CSet (B + Om 1 * (d0 + 1)) v :=
          CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add : B ≤ B + Om 1 * (d0 + 1))).2 hown)
            (Nm.mem_Om1_mul hDv)
        have hBlt : S.psi B (Om 1) < v := by
          have := hlt 0 (lt_of_le_of_lt zero_le (lt_add_one d0))
          rwa [add_zero, hc] at this
        have hfix : gamma v = v := rbFix_of_dvd hown hown1 (dvd_add hB (dvd_mul_right _ _)) hBlt
        obtain ⟨e, he⟩ := rdF_of_fix hfix
        rw [← he]
        refine rdF_le.2 (not_lt.1 fun hlt' => ?_)
        have hle : e ≤ c + d0 := by
          rw [← add_assoc] at hlt'; exact Order.lt_add_one_iff.1 hlt'
        have := (rdF_le.2 hle).trans_lt (hlt d0 (lt_add_one d0))
        rw [he] at this
        exact lt_irrefl _ this
      · refine not_lt.1 fun hlt' => ?_
        obtain ⟨e, he, hve⟩ := ((isNormal_deriv gamma).lt_iff_exists_lt (isSuccLimit_add c hlim)).1 hlt'
        rcases lt_or_ge e c with hec | hce
        · have : deriv gamma e < v := (rdF_lt.2 hec).trans_le (by rw [hc]; exact hBv)
          exact absurd hve (not_lt.2 this.le)
        · have hσe : c + (e - c) = e := Ordinal.add_sub_cancel_of_le hce
          have hσ : e - c < D := by rw [← hσe] at he; exact (add_lt_add_iff_left c).1 he
          have := hlt _ hσ
          rw [hσe] at this
          exact absurd hve (not_lt.2 this.le)
  exact ⟨by rw [heq]; exact hcond D le_rfl, heq⟩

/-- **A valid `D` has `d < F(c+d)` for every `d ≤ D`** (`Ω₁ ∣ B`, `F(c) = ψ_{Ω₁}(B)`). -/
theorem rd_psi_F_valid {B c D : Ordinal.{0}} (hB : Om 1 ∣ B) (hc : deriv gamma c = S.psi B (Om 1))
    (hv : D < S.psi (B + Om 1 * D) (Om 1)) : ∀ d, d ≤ D → d < deriv gamma (c + d) := by
  intro d hd
  by_contra hle
  push Not at hle
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact absurd hle (not_le.2 (rdF_SC _).1)
  have hDΩ : D ≤ Om 1 := hv.le.trans (psi_lt Low.InR_Om_one _).le
  have hprev : ∀ d'', d'' < D → d'' < deriv gamma (c + d) →
      S.psi (B + Om 1 * d'') (Om 1) < deriv gamma (c + d) := fun d'' hd'' hq =>
    (rd_psi_F_le hB hc.ge d'' (hd''.le.trans hDΩ)).trans_lt
      (rdF_lt.2 ((add_lt_add_iff_left c).2 (hq.trans_le hle)))
  have h := rd_psi_inv (S := S) hB (rdF_SC (c + d)) (rdF_fix (c + d))
    (by rw [← hc]; exact rdF_lt.2 (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hd0))) hDΩ hprev
  exact absurd ((h.trans hle).trans hd) (not_le.2 hv)

/-! ## The fixed points of `F` among the collapses -/

/-- `Ω₁·Ω₁ = ω^{Ω₁+Ω₁}`. -/
theorem rd_u_eq : (Om 1 : Ordinal.{0}) * Om 1 = ω ^ (Om 1 + Om 1) := by rw [opow_add, Bt.Om1_opow]

theorem rd_u_indec : Indec ((Om 1 : Ordinal.{0}) * Om 1) := by
  rw [rd_u_eq]; exact indec_iff.2 ⟨(opow_pos _ omega0_pos).ne', isPrincipal_add_omega0_opow _⟩

theorem rd_Om1_lt_u : (Om 1 : Ordinal.{0}) < Om 1 * Om 1 := by
  have h : (Om 1 : Ordinal.{0}) * 1 < Om 1 * Om 1 :=
    (mul_lt_mul_iff_right₀ rb_Om1_indec.pos).2 (Lu.lu_one_lt_E Bt.Om1_opow)
  rwa [mul_one] at h

/-- An additive principal `p ≥ Ω₁·Ω₁` is a multiple of `Ω₁·Ω₁`. -/
theorem rd_dvd_u_of_indec {p : Ordinal.{0}} (hp : Indec p) (h : Om 1 * Om 1 ≤ p) : Om 1 * Om 1 ∣ p := by
  obtain ⟨e, rfl⟩ := indec_eq_opow hp
  have he : Om 1 + Om 1 ≤ e := by
    rw [rd_u_eq] at h; exact (opow_le_opow_iff_right one_lt_omega0).1 h
  refine ⟨ω ^ (e - (Om 1 + Om 1)), ?_⟩
  rw [rd_u_eq, ← opow_add, Ordinal.add_sub_cancel_of_le he]

/-- `b < B`, `u ∣ B`, `e < u` give `b + e < B`, for an additive principal `u`. -/
theorem rd_add_lt_of_dvd {u B b e : Ordinal.{0}} (hu : Indec u) (hB : u ∣ B) (hb : b < B) (he : e < u) :
    b + e < B := by
  have h0 : u ≠ 0 := hu.ne_zero
  obtain ⟨k, rfl⟩ := hB
  have hdiv : b / u < k := (Ordinal.lt_mul_iff_div_lt h0).1 hb
  have hq : b / u + 1 ≤ k := Order.add_one_le_of_lt hdiv
  have hr : b % u + e < u := hu.add_lt (Ordinal.mod_lt _ h0) he
  calc b + e = u * (b / u) + (b % u + e) := by rw [← add_assoc, Ordinal.div_add_mod]
    _ < u * (b / u) + u := (add_lt_add_iff_left _).2 hr
    _ = u * (b / u + 1) := by rw [mul_add, mul_one]
    _ ≤ u * k := mul_le_mul_right hq u

/-- **Below a point `x > τ` that is not a fixed point of `F` there is a largest `p < x` that is `τ` or a fixed point
of `F` above `τ`.** -/
theorem rd_base_below_F {τ x : Ordinal.{0}} (hτx : τ < x) (hnf : deriv gamma x ≠ x) :
    ∃ p, (p = τ ∨ (τ < p ∧ deriv gamma p = p)) ∧ p < x ∧
      ∀ q, deriv gamma q = q → τ < q → q < x → q ≤ p := by
  set P : Set Ordinal.{0} := {q | q < x ∧ (q = τ ∨ (τ < q ∧ deriv gamma q = q))} with hPdef
  have hτP : τ ∈ P := ⟨hτx, Or.inl rfl⟩
  have hPne : P.Nonempty := ⟨τ, hτP⟩
  have hPb : BddAbove P := ⟨x, fun q hq => hq.1.le⟩
  set p := sSup P with hpdef
  have hpx : p ≤ x := csSup_le hPne fun q hq => hq.1.le
  have hτp : τ ≤ p := le_csSup hPb hτP
  have hmax : ∀ q, deriv gamma q = q → τ < q → q < x → q ≤ p := fun q hq hτq hqx =>
    le_csSup hPb ⟨hqx, Or.inr ⟨hτq, hq⟩⟩
  have hbase : p = τ ∨ (τ < p ∧ deriv gamma p = p) := by
    by_cases hmem : p ∈ P
    · exact hmem.2
    right
    have hτp' : τ < p := lt_of_le_of_ne hτp fun e => hmem (e ▸ hτP)
    refine ⟨hτp', ?_⟩
    have hcof : ∀ a < p, ∃ f, a < f ∧ f < p ∧ τ < f ∧ deriv gamma f = f := by
      intro a ha
      obtain ⟨f, hfP, hf⟩ := exists_lt_of_lt_csSup hPne (max_lt ha hτp')
      have hfp : f < p := lt_of_le_of_ne (le_csSup hPb hfP) fun e => hmem (e ▸ hfP)
      have hτf : τ < f := (le_max_right a τ).trans_lt hf
      rcases hfP.2 with e | ⟨-, hff⟩
      · exact absurd e hτf.ne'
      · exact ⟨f, (le_max_left a τ).trans_lt hf, hfp, hτf, hff⟩
    have hlim : IsSuccLimit p := by
      refine Ordinal.isSuccLimit_iff.2 ⟨(lt_of_le_of_lt zero_le hτp').ne', ?_⟩
      refine isSuccPrelimit_of_succ_lt fun a ha => ?_
      obtain ⟨f, haf, hfp, -⟩ := hcof a ha
      exact (Order.succ_le_of_lt haf).trans_lt hfp
    refine le_antisymm (not_lt.1 fun hlt => ?_) (rd_le_F p)
    obtain ⟨b, hb, hpb⟩ := ((isNormal_deriv gamma).lt_iff_exists_lt hlim).1 hlt
    obtain ⟨f, hbf, hfp, -, hff⟩ := hcof b hb
    have : deriv gamma b < f := by rw [← hff]; exact rdF_lt.2 hbf
    exact absurd (hpb.trans (this.trans hfp)) (lt_irrefl _)
  have hpx' : p < x := by
    refine lt_of_le_of_ne hpx fun e => ?_
    rcases hbase with h | ⟨-, h⟩
    · exact hτx.ne (h ▸ e)
    · exact hnf (e ▸ h)
  exact ⟨p, hbase, hpx', hmax⟩

/-- **`Cl(a, b)` contains `Ω₁·(Ω₁·(x/Ω₁/Ω₁))` with `x`.** -/
theorem rd_mod2_mem {a b : Ordinal.{0}} :
    ∀ x, x ∈ S.CSet a b → Om 1 * (Om 1 * (x / Om 1 / Om 1)) ∈ S.CSet a b := by
  have h0 := rd_Om1_ne
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Ordinal.zero_div, Ordinal.zero_div, mul_zero, mul_zero]
    exact CSet.zero_mem _ _
  obtain ⟨hl, ht⟩ := lead_tail_mem hx hx0
  have hlt := lead_add_tail hx0
  rcases le_or_gt (Om 1 * Om 1) (lead x) with h1 | h1
  · have hI : Indec (lead x) := indec_iff.2 ⟨(opow_pos _ omega0_pos).ne', isPrincipal_add_omega0_opow _⟩
    obtain ⟨m, hm⟩ := rd_dvd_u_of_indec hI h1
    have ih := IH (tail x) (tail_lt hx0) ht
    have e2 : Om 1 * (Om 1 * (x / Om 1 / Om 1)) = lead x + Om 1 * (Om 1 * (tail x / Om 1 / Om 1)) := by
      conv_lhs => rw [← hlt, hm, mul_assoc]
      rw [Ordinal.mul_add_div _ h0, Ordinal.mul_add_div _ h0, mul_add, mul_add, hm, mul_assoc]
    rw [e2]
    exact CSet.add_mem hl ih
  · have hlog : Ordinal.log ω x < Om 1 + Om 1 := by
      have := h1
      unfold lead at this
      rw [rd_u_eq] at this
      exact (opow_lt_opow_iff_right one_lt_omega0).1 this
    have hlim : IsSuccLimit (Om 1 + Om 1 : Ordinal.{0}) := isSuccLimit_add _ (Om_isSuccLimit one_ne_zero)
    have hlog1 : Ordinal.log ω x + 1 < Om 1 + Om 1 := hlim.add_one_lt hlog
    have hxu : x < Om 1 * Om 1 := by
      refine (lt_opow_log_add_one x).trans ?_
      rw [rd_u_eq]
      exact (opow_lt_opow_iff_right one_lt_omega0).2 hlog1
    have hx1 : x / Om 1 < Om 1 := (Ordinal.lt_mul_iff_div_lt h0).1 hxu
    rw [Ordinal.div_eq_zero_of_lt hx1, mul_zero, mul_zero]
    exact CSet.zero_mem _ _

/-- **`ψ_{Ω₁}(Ω₁)` is a fixed point of `Γ_`.** -/
theorem rd_fix_psiOm1 : gamma (S.psi (Om 1) (Om 1)) = S.psi (Om 1) (Om 1) := by
  have hown0 : (0 : Ordinal.{0}) ∈ S.CSet 0 (S.psi 0 (Om 1)) := CSet.zero_mem _ _
  have hown1 : Om 1 ∈ S.CSet (Om 1) (S.psi (Om 1) (Om 1)) := CSet.Om_mem (CSet.one_mem _ _)
  have hlt : S.psi 0 (Om 1) < S.psi (Om 1) (Om 1) := psi_lt_psi Low.InR_Om_one rb_Om1_indec.pos hown0
  exact rbFix_of_dvd hown0 hown1 (dvd_refl _) hlt

/-- **`ψ_{Ω₁}(B)` is a fixed point of `F`** for every own `B ≠ 0` with `Ω₁·Ω₁ ∣ B`. -/
theorem rd_fix2_of_dvd {B : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1))) (hdvd : Om 1 * Om 1 ∣ B)
    (hB0 : B ≠ 0) : deriv gamma (S.psi B (Om 1)) = S.psi B (Om 1) := by
  set x := S.psi B (Om 1) with hxdef
  have hx1 : x < Om 1 := psi_lt Low.InR_Om_one B
  have hΩB : Om 1 < B := rd_Om1_lt_u.trans_le (Ordinal.le_of_dvd hB0 hdvd)
  have hown0 : Om 1 ∈ S.CSet (Om 1) (S.psi (Om 1) (Om 1)) := CSet.Om_mem (CSet.one_mem _ _)
  have hlt0 : S.psi (Om 1) (Om 1) < x :=
    psi_lt_psi_of_mem Low.InR_Om_one hΩB (CSet.Om_mem (CSet.one_mem _ _))
  have hxfix : gamma x = x :=
    rbFix_of_dvd hown0 hown ((dvd_mul_right (Om 1) (Om 1)).trans hdvd) hlt0
  by_contra hnf
  obtain ⟨y, hy⟩ := rdF_of_fix hxfix
  have hyx : y < x := by
    refine lt_of_le_of_ne (hy ▸ rd_le_F y) fun e => hnf ?_
    rw [← e] at hy ⊢; rw [hy]
  obtain ⟨p, hbase, hpx, hmax⟩ := rd_base_below_F hlt0 hnf
  have hpΓ : gamma p = p := by
    rcases hbase with e | ⟨-, h⟩
    · rw [e]; exact rd_fix_psiOm1
    · have := rdF_fix p; rwa [h] at this
  obtain ⟨c, hc⟩ := rdF_of_fix hpΓ
  obtain ⟨Bp, hownp, hBp, hdvdp⟩ : ∃ Bp, Bp ∈ S.CSet Bp (S.psi Bp (Om 1)) ∧ S.psi Bp (Om 1) = p ∧
      Om 1 ∣ Bp := by
    rcases hbase with e | -
    · exact ⟨Om 1, hown0, e.symm, dvd_refl _⟩
    · obtain ⟨Bp, hownp, hBp⟩ := rb_own_of_SC (rd_SC_of_fix hpΓ) hpx
      exact ⟨Bp, hownp, hBp, rbDvd_of_fix hownp (by rw [hBp]; exact hpΓ)⟩
  have hcy : c < y := rdF_lt.1 (by rw [hc, hy]; exact hpx)
  set D := y - c with hDdef
  have hcD : c + D = y := Ordinal.add_sub_cancel_of_le hcy.le
  have hcond : ∀ d, d ≤ D → d < deriv gamma (c + d) := by
    intro d hd
    by_contra hle
    push Not at hle
    have hz : deriv gamma (c + d) = c + d :=
      le_antisymm (hle.trans le_add_self) (rd_le_F _)
    have hzy : c + d ≤ y := by rw [← hcD]; exact (add_le_add_iff_left c).2 hd
    have hpz : p ≤ c + d := by rw [← hc, ← hz]; exact rdF_le.2 le_self_add
    rcases hpz.lt_or_eq with hpz | hpz
    · have hτz : S.psi (Om 1) (Om 1) < c + d := by
        rcases hbase with e | ⟨h, -⟩
        · rw [← e]; exact hpz
        · exact h.trans hpz
      exact absurd (hmax _ hz hτz (hzy.trans_lt hyx)) (not_le.2 hpz)
    · have hpp : deriv gamma p = p := by rw [hpz]; exact hz
      have hcp : c = p := (deriv_strictMono gamma).injective (hc.trans hpp.symm)
      have hd0 : d = 0 := by
        have : c + d = c + 0 := by rw [add_zero, ← hpz, hcp]
        exact add_left_cancel this
      rw [hd0, add_zero] at hle
      exact absurd hle (not_le.2 (rdF_SC _).1)
  have hDx : D < x := (Ordinal.sub_le_self y c).trans_lt hyx
  obtain ⟨-, hψ⟩ := rd_psi_F_of hownp hdvdp (hc.trans hBp.symm) D (hDx.trans hx1) hcond
  have hψx : S.psi (Bp + Om 1 * D) (Om 1) = x := by rw [hψ, hcD, hy]
  have hBpB : Bp < B := by
    have h := compare_psi Low.InR_Om_one hownp hown
    rw [hBp, compare_lt_iff_lt.2 hpx] at h
    exact compare_lt_iff_lt.1 h.symm
  have hlt2 : Bp + Om 1 * D < B :=
    rd_add_lt_of_dvd rd_u_indec hdvd hBpB ((mul_lt_mul_iff_right₀ rb_Om1_indec.pos).2 (hDx.trans hx1))
  have hmem : Bp + Om 1 * D ∈ S.CSet B x :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one hBpB.le).2 hownp) (Nm.mem_Om1_mul hDx)
  have hψmem : S.psi (Bp + Om 1 * D) (Om 1) ∈ S.CSet B x :=
    CSet.psi_mem hlt2 Low.InR_Om_one (mem_CSet_psi Low.InR_Om_one B) hmem
  have := lt_psi_of_mem Low.InR_Om_one hψmem (psi_lt Low.InR_Om_one _)
  rw [hψx] at this
  exact lt_irrefl _ this

/-- **`Ω₁·Ω₁ ∣ B` for every own `B` with `ψ_{Ω₁}(B)` a fixed point of `F`.** -/
theorem rd_dvd2_of_fix {B : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1)))
    (hfix : deriv gamma (S.psi B (Om 1)) = S.psi B (Om 1)) : Om 1 * Om 1 ∣ B := by
  have h0 := rd_Om1_ne
  set p := S.psi B (Om 1) with hpdef
  have hpSC : SC p := SC_psi Low.InR_Om_one B
  have hpΓ : gamma p = p := by have := rdF_fix p; rwa [hfix] at this
  obtain ⟨k, hk⟩ := rbDvd_of_fix hown hpΓ
  by_contra hnd
  set D0 := k % Om 1 with hD0
  set B0 := Om 1 * (Om 1 * (k / Om 1)) with hB0
  have hBe : B0 + Om 1 * D0 = B := by
    rw [hk, hB0, hD0, ← mul_add, Ordinal.div_add_mod]
  have hD00 : D0 ≠ 0 := by
    intro e
    apply hnd
    rw [← hBe, e, mul_zero, add_zero, hB0, ← mul_assoc]
    exact dvd_mul_right _ _
  -- the digits of `B` are below `p`
  have hcoll : ∀ e, e < B → e ∈ S.CSet B p → e % Om 1 < p → e / Om 1 % Om 1 < p → S.psi e (Om 1) < p :=
    fun e he heC _ _ => lt_psi_of_mem Low.InR_Om_one
      (CSet.psi_mem he Low.InR_Om_one (mem_CSet_psi Low.InR_Om_one B) heC) (psi_lt Low.InR_Om_one _)
  have hdig := (rd_digits (S := S) hpSC hcoll B hown).2
  have hkdiv : B / Om 1 = k := by rw [hk, Ordinal.mul_div_cancel _ h0]
  rw [hkdiv] at hdig
  have hD0p : D0 < p := hdig
  have hB0m : B0 ∈ S.CSet B p := by
    have := rd_mod2_mem (S := S) B hown
    rwa [hkdiv] at this
  have hB0B : B0 < B := by
    rw [← hBe]; exact lt_add_of_pos_right _ (mul_pos rb_Om1_indec.pos (pos_iff_ne_zero.2 hD00))
  have hB0p : S.psi B0 (Om 1) < p := psi_lt_psi_of_mem Low.InR_Om_one hB0B hB0m
  have hle := rd_psi_F_le (S := S) (dvd_mul_right (Om 1) _) (rd_le_F (S.psi B0 (Om 1))) D0
    (Ordinal.mod_lt k h0).le
  rw [hBe] at hle
  have hlt : S.psi B0 (Om 1) + D0 < p := (lq_SC_indec hpSC).add_lt hB0p hD0p
  have h2 : deriv gamma (S.psi B0 (Om 1) + D0) < p := by
    conv_rhs => rw [← hfix]
    exact rdF_lt.2 hlt
  exact absurd (hle.trans_lt h2) (lt_irrefl _)

/-! ## `B_n` at `ψ_{Ω₁}(B + Ω₁·D)` -/

/-- **`Rb.rbB_psi_base` for every `d` in the normal-form domain `Mv.MvD`**: `B_n(ψ_{Ω₁}(B)) = ψ_{Ω₁}(B')`,
`B_n(ψ_{Ω₁}(B + d)) = ψ_{Ω₁}(B' + B_n d)`, `B = α_{n+1} + |r|`, `B' = α_ω + |σ r|` own. -/
theorem rdB_psi_baseD {n : ℕ} {B d : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1)))
    (hlo : Bc.bcC S n ≤ S.psi B (Om 1)) (hown1 : B + d ∈ S.CSet (B + d) (S.psi (B + d) (Om 1)))
    (hhi : S.psi (B + d) (Om 1) < Bc.bcC S (n + 1)) (hdD : Mv.MvD S d) :
    ∃ r : Term, bcD S r ∧ B = bcAlpha S (n + 1) + val S r ∧
      bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) ∈
        S.CSet (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r))
          (S.psi (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r)) (Om 1)) ∧
      Bc.bcB S n (S.psi B (Om 1)) = S.psi (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r)) (Om 1) ∧
      Bc.bcB S n (S.psi (B + d) (Om 1)) =
        S.psi (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) + Bc.bcB S n d) (Om 1) := by
  have hP1 : S.psi B (Om 1) ≤ S.psi (B + d) (Om 1) :=
    (psi_mono (S := S) Low.InR_Om_one (le_self_add : B ≤ B + d)).1
  have hαA : bcAlpha S (n + 1) ≤ B := sfArg_le (sfOwn_alpha S n) hown hlo
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Qq.qqL_lt_omega S (n + 1 + 1)
  have hx0 : S.psi B (Om 1) < Nc.ncL S ω := (hP1.trans_lt hhi).trans hLw
  have hx1 : S.psi (B + d) (Om 1) < Nc.ncL S ω := hhi.trans hLw
  have hDe : bcD S (bcNf S d) := hdD.2
  have hve : val S (bcNf S d) = d := Mv.mvD_val hdD
  obtain ⟨a, ha, hva⟩ := sfNf_psi hown (bcD_nf S hx0).1 (val_nf S hx0)
  obtain ⟨a1, ha1, hva1⟩ := sfNf_psi hown1 (bcD_nf S hx1).1 (val_nf S hx1)
  have hD : bcD S (psiS Term.zero a) := ha ▸ bcD_nf S hx0
  have hD1 : bcD S (psiS Term.zero a1) := ha1 ▸ bcD_nf S hx1
  have hN := hD.1
  have hN1 := hD1.1
  have hAW : val S a < bcAlphaW S := hD.2.2.2 rfl
  have hA1W : val S a1 < bcAlphaW S := hD1.2.2.2 rfl
  have hlo0 : bcAlpha S (n + 1) ≤ val S a := hva ▸ hαA
  have hlo1 : bcAlpha S (n + 1) ≤ val S a1 := by rw [hva1]; exact hαA.trans le_self_add
  have hB0 := sfB_psi (n := n) hN hlo0 hAW
  have hB1 := sfB_psi (n := n) hN1 hlo1 hA1W
  rw [hva] at hB0
  rw [hva1] at hB1
  have hpre := (bc_pre_iff S hN.2.1 hAW).2 hlo0
  have hpre1 := (bc_pre_iff S hN1.2.1 hA1W).2 hlo1
  have hvρ : val S a = bcAlpha S (n + 1) + val S (bcDrop (n + 3) a) := by
    have := val_of_pre S hN.2.1 hpre; rwa [sfPre_len] at this
  have hvρ1 : val S a1 = bcAlpha S (n + 1) + val S (bcDrop (n + 3) a1) := by
    have := val_of_pre S hN1.2.1 hpre1; rwa [sfPre_len] at this
  have hDa : bcD S a := bcD_sub hD (sub_psiS_a _ _)
  have hDρ : bcD S (bcDrop (n + 3) a) := bcD_drop hDa (n + 3)
  have hvr1 : val S (bcDrop (n + 3) a1) = val S (bcDrop (n + 3) a) + d := by
    have e1 : bcAlpha S (n + 1) + val S (bcDrop (n + 3) a1) =
        bcAlpha S (n + 1) + (val S (bcDrop (n + 3) a) + d) := by
      rw [← hvρ1, hva1, ← hva, hvρ, add_assoc]
    exact add_left_cancel e1
  have hNρ1 : NF (bcDrop (n + 3) a1) := NF_bcDrop _ hN1.2.1
  obtain ⟨hNadd, hvadd, -⟩ := addNF_spec (S := S) hDρ.1 hDe.1
  have hρ1 : bcDrop (n + 3) a1 = addNF (bcDrop (n + 3) a) (bcNf S d) :=
    eq_of_val_eq S hNρ1 hNadd (by rw [hvadd, hve, hvr1])
  have hσ1 : val S (bcSig (bcPre (n + 1)) bcPreW (bcDrop (n + 3) a1)) =
      val S (bcSig (bcPre (n + 1)) bcPreW (bcDrop (n + 3) a)) + Bc.bcB S n d := by
    rw [hρ1, bcSig_addNF (k := n) hDρ hDe,
      (addNF_spec (S := S) (bc_NF (k := n) hDρ) (bc_NF (k := n) hDe)).2.1]
    rfl
  refine ⟨bcDrop (n + 3) a, hDρ, by rw [← hva, hvρ], ?_, hB0, ?_⟩
  · have hσN : NF (bcSig (bcPre (n + 1)) bcPreW (psiS Term.zero a)) := bc_NF (k := n) hD
    rw [bcSig_psiS_zero, bcArg_of_pre hpre, sfPre_len] at hσN
    have hsem : Sem S (psiS Term.zero (bcApp bcPreW
        (bcSig (bcPre (n + 1)) bcPreW (bcDrop (n + 3) a)))) := sem_of_NF hσN
    have h2 := hsem.2.2
    rw [show Om (val S Term.zero + 1) = Om 1 by rw [show val S Term.zero = 0 from rfl, zero_add],
      val_bcApp_preW] at h2
    exact h2
  · rw [hB1, hσ1, add_assoc]

/-- **`B_n(ψ_{Ω₁}(B + Ω₁·D)) = ψ_{Ω₁}(B' + Ω₁·B_n D)`** for an own `B` in the window and an own `B + Ω₁·D` with a
countable `D < L(n+2)`, with `B = α_{n+1} + |r|`, `B' = α_ω + |σ r|` own and `B_n(ψ_{Ω₁}(B)) = ψ_{Ω₁}(B')`. -/
theorem rdB_psi_Om1 {n : ℕ} {B D : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1)))
    (hlo : Bc.bcC S n ≤ S.psi B (Om 1))
    (hown1 : B + Om 1 * D ∈ S.CSet (B + Om 1 * D) (S.psi (B + Om 1 * D) (Om 1)))
    (hhi : S.psi (B + Om 1 * D) (Om 1) < Bc.bcC S (n + 1)) (hD1 : D < Om 1) (hDc : D < Bc.bcC S (n + 1)) :
    ∃ r : Term, bcD S r ∧ B = bcAlpha S (n + 1) + val S r ∧
      bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) ∈
        S.CSet (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r))
          (S.psi (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r)) (Om 1)) ∧
      Bc.bcB S n (S.psi B (Om 1)) = S.psi (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r)) (Om 1) ∧
      Bc.bcB S n (S.psi (B + Om 1 * D) (Om 1)) =
        S.psi (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) + Om 1 * Bc.bcB S n D) (Om 1) := by
  obtain ⟨hDm, hBm⟩ := Le.leB_mulOm1 (S := S) (n := n) hD1 hDc
  obtain ⟨r, h1, h2, h3, h4, h5⟩ := rdB_psi_baseD hown hlo hown1 hhi hDm
  exact ⟨r, h1, h2, h3, h4, by rw [h5, hBm]⟩

/-! ## `σ` keeps `Ω₁·Ω₁ ∣ ·` -/

/-- **`u ∣ x + y ↔ u ≤ y`** for additive principal `u`, `y`. -/
theorem rd_dvd_prin {u x y : Ordinal.{0}} (hu : Indec u) (hy : Indec y) : u ∣ x + y ↔ u ≤ y := by
  have h0 : u ≠ 0 := hu.ne_zero
  have hdec : x + y = u * (x / u) + (x % u + y) := by
    rw [← add_assoc, Ordinal.div_add_mod]
  constructor
  · intro hd
    by_contra hlt
    push Not at hlt
    have hr : x % u + y < u := hu.add_lt (Ordinal.mod_lt _ h0) hlt
    have hm := Ordinal.mod_eq_zero_of_dvd hd
    rw [hdec, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr] at hm
    exact hy.ne_zero (le_antisymm (hm ▸ le_add_self) zero_le)
  · intro h1
    obtain ⟨e, rfl⟩ := indec_eq_opow hu
    obtain ⟨f, rfl⟩ := indec_eq_opow hy
    have hef : e ≤ f := (opow_le_opow_iff_right one_lt_omega0).1 h1
    have hdy : ω ^ e ∣ ω ^ f := ⟨ω ^ (f - e), by rw [← opow_add, Ordinal.add_sub_cancel_of_le hef]⟩
    have hab : x % ω ^ e + ω ^ f = ω ^ f := hy.add_eq ((Ordinal.mod_lt _ h0).trans_le h1)
    rw [hdec, hab]
    exact dvd_add (dvd_mul_right _ _) hdy

theorem rd_dvd_iff_last {u : Ordinal.{0}} (hu : Indec u) {t : Term} (ht : NF t) (h0 : t ≠ Term.zero) :
    u ∣ val S t ↔ u ≤ val S (rbLast t) := by
  obtain ⟨x, hx⟩ := rbLast_val (S := S) t
  obtain ⟨hN, hl0, hP⟩ := rbLast_NF ht h0
  have hI : Indec (val S (rbLast t)) :=
    indec_iff.2 ⟨val_ne_zero S hN hl0, isPrincipal_val S hN hP⟩
  rw [hx]
  exact rd_dvd_prin hu hI

/-- `Ω₁·Ω₁` is in the domain of `B_n` and fixed by it. -/
theorem rdB_u {n : ℕ} : Mv.MvD S (Om 1 * Om 1) ∧ Bc.bcB S n (Om 1 * Om 1) = Om 1 * Om 1 := by
  obtain ⟨hD1, hB1⟩ := Mv.mvB_Om1 (S := S) (k := n)
  obtain ⟨hD2, hB2⟩ := Mv.mvB_add (k := n) hD1 hD1
  have hne : ω ^ (Om 1 + Om 1) ≠ Om 1 + Om 1 := by
    rw [← rd_u_eq]
    refine ne_of_gt ?_
    calc Om 1 + Om 1 = Om 1 * 2 := (Ordinal.mul_two _).symm
      _ < Om 1 * Om 1 := (mul_lt_mul_iff_right₀ rb_Om1_indec.pos).2
          ((natCast_lt_omega0 2).trans_le (omega0_le_of_isSuccLimit (Om_isSuccLimit one_ne_zero)))
  obtain ⟨hD3, hB3⟩ := Mv.mvB_opow (k := n) hD2 hne
  rw [hB2, hB1] at hB3
  rw [rd_u_eq]
  exact ⟨hD3, hB3⟩

/-- **`σ` keeps `Ω₁·Ω₁ ≤ |v|`** on its domain. -/
theorem rd_u_le_sig {n : ℕ} {v : Term} (hv : bcD S v) (h : Om 1 * Om 1 ≤ val S v) :
    Om 1 * Om 1 ≤ val S (bcSig (bcPre (n + 1)) bcPreW v) := by
  obtain ⟨hDu, hBu⟩ := rdB_u (S := S) (n := n)
  have hDv := Mv.mvD_of_term hv
  rw [← Mv.mvB_term (k := n) hv, ← hBu]
  exact not_lt.1 fun hlt => absurd ((Mv.mvB_lt_iff hDv hDu).1 hlt) (not_lt.2 h)

/-- **`σ` keeps `Ω₁·Ω₁ ∣ |r|`** on its domain. -/
theorem rd_dvd2_sig {n : ℕ} {r : Term} (hr : bcD S r) (h : Om 1 * Om 1 ∣ val S r) :
    Om 1 * Om 1 ∣ val S (bcSig (bcPre (n + 1)) bcPreW r) := by
  by_cases h0 : r = Term.zero
  · subst h0; rw [bcSig_zero]; exact dvd_zero _
  have hN' := bc_NF (k := n) hr
  have h0' : bcSig (bcPre (n + 1)) bcPreW r ≠ Term.zero := bcSig_ne_zero h0
  rw [rd_dvd_iff_last rd_u_indec hN' h0', rbLast_sig]
  exact rd_u_le_sig (rbLast_D hr) ((rd_dvd_iff_last rd_u_indec hr.1 h0).1 h)

/-- An `ε`-number above `Ω₁` is a multiple of `Ω₁·Ω₁`. -/
theorem rd_dvd_u_of_eps {p : Ordinal.{0}} (hp : ω ^ p = p) (h : Om 1 < p) : Om 1 * Om 1 ∣ p := by
  have hI : Indec p := inE_indec hp
  refine rd_dvd_u_of_indec hI ?_
  rw [rd_u_eq, ← hp]
  exact opow_le_opow_right omega0_pos (hI.add_lt h h).le

theorem rd_dvd2_OmW : Om 1 * Om 1 ∣ Om (ω : Ordinal.{0}) :=
  rd_dvd_u_of_eps (Low.opow_eq_self_of_SC (SC_Om omega0_pos.ne')) (Om_lt_Om.2 one_lt_omega0)

theorem rd_dvd2_Pp : Om 1 * Om 1 ∣ Nc.ncPp S :=
  rd_dvd_u_of_eps (Low.opow_eq_self_of_SC (Nc.ncPp_SC S)) rb_Om1_lt_Pp

theorem rd_dvd2_alpha (k : ℕ) : Om 1 * Om 1 ∣ bcAlpha S k :=
  dvd_add (dvd_add rd_dvd2_OmW rd_dvd2_OmW) (dvd_mul_of_dvd_left rd_dvd2_Pp _)

theorem rd_dvd2_alphaW : Om 1 * Om 1 ∣ bcAlphaW S := by
  refine dvd_add (dvd_add rd_dvd2_OmW rd_dvd2_OmW) (rd_dvd_u_of_indec ?_ ?_)
  · exact indec_iff.2 ⟨(opow_pos _ omega0_pos).ne', isPrincipal_add_omega0_opow _⟩
  · rw [rd_u_eq]
    refine opow_le_opow_right omega0_pos (le_trans ?_ le_self_add)
    have hE : ω ^ Nc.ncPp S = Nc.ncPp S := Low.opow_eq_self_of_SC (Nc.ncPp_SC S)
    exact ((inE_indec hE).add_lt rb_Om1_lt_Pp rb_Om1_lt_Pp).le

/-- `u ∣ a + v ↔ u ∣ v` when `u ∣ a`. -/
theorem rd_dvd_add_left {u a v : Ordinal.{0}} (ha : u ∣ a) : u ∣ a + v ↔ u ∣ v := by
  obtain ⟨k, rfl⟩ := ha
  rw [Ordinal.dvd_iff_mod_eq_zero, Ordinal.dvd_iff_mod_eq_zero, Ordinal.mul_add_mod_self]

/-- **`Ω₁·Ω₁ ∣ B` gives `Ω₁·Ω₁ ∣ B'`** for `B = α_{n+1} + |r|`, `B' = α_ω + |σ r|`. -/
theorem rdB_dvd2 {n : ℕ} {B : Ordinal.{0}} {r : Term} (hr : bcD S r) (hB : B = bcAlpha S (n + 1) + val S r)
    (h : Om 1 * Om 1 ∣ B) : Om 1 * Om 1 ∣ bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) := by
  rw [hB, rd_dvd_add_left (rd_dvd2_alpha _)] at h
  rw [rd_dvd_add_left rd_dvd2_alphaW]
  exact rd_dvd2_sig hr h

/-- **`Ω₁·Ω₁ ∣ A_η`.** -/
theorem rd_dvd2_A (η : Ordinal.{0}) : Om 1 * Om 1 ∣ ConjT.Aη S η := by
  have h2 : Om 1 * Om 1 ∣ ConjT.th S :=
    rd_dvd_u_of_eps (Low.opow_eq_self_of_SC (ConjT.SC_th S)) Bt.Om1_lt_th
  exact dvd_add rd_dvd2_OmW (h2.mul_right η)

end Googology.Trans.PoR.InaccPsi.R2.Rd
