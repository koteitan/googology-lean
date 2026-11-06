import Googology.Trans.PoR.InaccPsi.R2.KsLow
import Googology.Trans.PoR.InaccPsi.R2.ZeBad
import Googology.Trans.PoR.InaccPsi.R2.GgFix

/-!
# Kt: THE CLOSURE WITHOUT THE COUNTABLE COLLAPSES (`Bt.HCl`): logarithm, difference, division, and the gap of towers

`HCl(a, Z)` (`Bt.HCl S a Z`) is `Cl(a, Z)` without the countable collapses `ψ_{Ω₁}(e)`; its countable members lie
below `Z` (`Bt.HCl_lt`).  These closure facts are those of `Cl(a, b)` (`Le.leLog_mem`, `Ta.taSub_mem`,
`Vb.vbC_rem`, `Vh.vhC_div`), by the same inductions.

* `ktHCl_log`, `ktHCl_sub` (**`x - y` for every `y`**), `ktHCl_rem`, `ktHCl_div` (**the division by `ω^p`**);
* `ktGap_mul`, `ktGap_opow`, `ktGap` (**THE GAP OF EVERY TOWER at `HCl(a, Z)` with the bound `Z`**: a member
  `e < t(Ω₁)` lies below `t(q + 1)` for some `q < Z`, once the bottom exponent of `t` is a member).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Ze Googology.Trans.PoR.InaccPsi.R2.Zx Googology.Trans.PoR.InaccPsi.R2.Ka

variable {S : InaccSeq.{0}} {a Z : Ordinal.{0}}

/-- **`HCl(a, Z)` is closed under `log_ω`.** -/
theorem ktHCl_log {x : Ordinal.{0}} (hx : HCl S a Z x) : HCl S a Z (log ω x) := by
  have fix : ∀ {p : Ordinal.{0}}, ω ^ p = p → HCl S a Z p → HCl S a Z (log ω p) := by
    intro p hpE hpC
    have : log ω p = p := by conv_lhs => rw [← hpE]; exact log_opow one_lt_omega0 _
    rw [this]; exact hpC
  induction hx with
  | small h => exact HCl.small ((log_le_self ω _).trans_lt h)
  | zero => rw [log_zero_right]; exact HCl.zero
  | inacc n => exact fix (Low.opow_eq_self_of_SC (SC_I (S := S) n)) (HCl.inacc n)
  | inaccW => exact fix (Low.opow_eq_self_of_SC (SC_Iw (S := S))) HCl.inaccW
  | @add x y _ _ ihx ihy =>
    rcases ggLog_add x y with e | e <;> rw [e]
    · exact ihx
    · exact ihy
  | @phi x y hx hy _ _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [veblen_zero_apply, log_opow one_lt_omega0]; exact hy
    · exact fix (gg_veblen_eps hx0) (HCl.phi hx hy)
  | @om x hx _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero, log_zero_right]; exact HCl.zero
    · exact fix (Low.opow_eq_self_of_SC (SC_Om hx0)) (HCl.om hx)
  | @coll π e hπ hπ1 hπC heC he _ _ =>
    exact fix (Low.opow_eq_self_of_SC (SC_psi hπ e)) (HCl.coll hπ hπ1 hπC heC he)

/-- **`x - y ∈ HCl(a, Z)` for every member `x` and every `y`.** -/
theorem ktHCl_sub : ∀ x, HCl S a Z x → ∀ y, HCl S a Z (x - y) := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx y
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Ordinal.sub_eq_zero_iff_le.2 zero_le]; exact HCl.zero
  obtain ⟨-, htail⟩ := zeHCl_lead_tail hx hx0
  have hdec : lead x + tail x = x := lead_add_tail hx0
  rcases lt_or_ge y (lead x) with hy | hy
  · have e : y + x = x := Ordinal.add_of_omega0_opow_le hy (lead_le hx0)
    rw [Ordinal.sub_eq_of_add_eq e]; exact hx
  · obtain ⟨y', rfl⟩ := exists_add_of_le hy
    have e : x - (lead x + y') = tail x - y' := by
      have h := Ordinal.add_sub_add_cancel (lead x) (tail x) y'
      rwa [hdec] at h
    rw [e]
    exact IH _ (tail_lt hx0) htail y'

/-- The rest after the leading block: `x mod ω^{log x}`. -/
theorem ktHCl_rem {x : Ordinal.{0}} (hx : HCl S a Z x) : HCl S a Z (x % ω ^ log ω x) := by
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
  have hdm : x = ω ^ log ω x * n + x % ω ^ log ω x := by
    rw [← hn]; exact (Ordinal.div_add_mod x _).symm
  have e : x - ω ^ log ω x * n = x % ω ^ log ω x := by
    have e0 := Ordinal.add_sub_cancel (ω ^ log ω x * n) (x % ω ^ log ω x)
    rwa [← hdm] at e0
  rw [← e]; exact ktHCl_sub x hx _

/-- **`HCl(a, Z)` is closed under the division by `ω^p`.** -/
theorem ktHCl_div : ∀ w, HCl S a Z w → ∀ p : Ordinal.{0},
    HCl S a Z (ω ^ p * (w / ω ^ p)) ∧ HCl S a Z (w % ω ^ p) ∧ (HCl S a Z p → HCl S a Z (w / ω ^ p)) := by
  intro w
  induction w using WellFoundedLT.induction with
  | ind w IH =>
  intro hw p
  rcases eq_or_ne w 0 with rfl | hw0
  · rw [Ordinal.zero_div, Ordinal.zero_mod, mul_zero]
    exact ⟨HCl.zero, HCl.zero, fun _ => HCl.zero⟩
  have hp0 : ω ^ p ≠ 0 := (opow_pos p omega0_pos).ne'
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt w one_lt_omega0)
  have hdm : w = ω ^ log ω w * n + w % ω ^ log ω w := by
    rw [← hn]; exact (Ordinal.div_add_mod w _).symm
  have he : HCl S a Z (log ω w) := ktHCl_log hw
  have hs : HCl S a Z (w % ω ^ log ω w) := ktHCl_rem hw
  have hsw : w % ω ^ log ω w < w :=
    (Ordinal.mod_lt w (opow_pos _ omega0_pos).ne').trans_le (opow_log_le_self ω hw0)
  rcases lt_or_ge (log ω w) p with hep | hpe
  · have hwp : w < ω ^ p :=
      (lt_opow_succ_log_self one_lt_omega0 w).trans_le
        (opow_le_opow_right omega0_pos (Order.succ_le_of_lt hep))
    rw [Ordinal.div_eq_zero_of_lt hwp, Ordinal.mod_eq_of_lt hwp, mul_zero]
    exact ⟨HCl.zero, hw, fun _ => HCl.zero⟩
  have hsplit : ω ^ log ω w = ω ^ p * ω ^ (log ω w - p) := by
    rw [← opow_add, Ordinal.add_sub_cancel_of_le hpe]
  have hw' : w = ω ^ p * (ω ^ (log ω w - p) * n) + w % ω ^ log ω w := by
    conv_lhs => rw [hdm]
    rw [hsplit, mul_assoc]
  have hdiv : w / ω ^ p = ω ^ (log ω w - p) * n + w % ω ^ log ω w / ω ^ p := by
    conv_lhs => rw [hw']
    rw [Ordinal.mul_add_div _ hp0]
  have hmod : w % ω ^ p = w % ω ^ log ω w % ω ^ p := by
    conv_lhs => rw [hw']
    rw [Ordinal.mul_add_mod_self]
  obtain ⟨i1, i2, i3⟩ := IH _ hsw hs p
  refine ⟨?_, ?_, ?_⟩
  · rw [hdiv, mul_add, ← mul_assoc, ← hsplit]
    exact HCl.add (ggHCl_mul_nat he.opow n) i1
  · rw [hmod]; exact i2
  · intro _
    rw [hdiv]
    exact HCl.add (ggHCl_mul_nat (ktHCl_sub _ he p).opow n) (i3 ‹_›)

/-- **The gap of `b + ω^m·x` at `HCl(a, Z)`** with the bound `Z`, once `m` is a member. -/
theorem ktGap_mul {b m : Ordinal.{0}} (hZ : SC Z) (hm : HCl S a Z m) :
    ZxGap (fun x => b + ω ^ m * x) {e | HCl S a Z e} Z := by
  intro e he hlt
  have hM0 : ω ^ m ≠ 0 := (opow_pos _ omega0_pos).ne'
  rcases lt_or_ge e b with h1 | h1
  · refine ⟨0, hZ.1, ?_⟩
    show e < b + ω ^ m * (0 + 1)
    rw [zero_add, mul_one]; exact h1.trans_le le_self_add
  · have hsub : e - b < ω ^ m * Om 1 := Ry.rySub_lt h1 hlt
    set q := (e - b) / ω ^ m with hq
    have hqC : HCl S a Z q := (ktHCl_div _ (ktHCl_sub e he b) m).2.2 hm
    have hq1 : q < Om 1 := (Ordinal.lt_mul_iff_div_lt hM0).1 hsub
    refine ⟨q, HCl_lt hZ hqC hq1, ?_⟩
    have e1 : e = b + (e - b) := (Ordinal.add_sub_cancel_of_le h1).symm
    show e < b + ω ^ m * (q + 1)
    rw [e1]
    have := Ordinal.lt_mul_succ_div (e - b) hM0
    rw [Order.succ_eq_add_one] at this
    exact (add_lt_add_iff_left b).2 this

/-- **The gap passes to `b + ω^{L(x)}`** at `HCl(a, Z)`. -/
theorem ktGap_opow {b : Ordinal.{0}} {L : Ordinal.{0} → Ordinal.{0}} (hZ : SC Z)
    (hg : ZxGap L {e | HCl S a Z e} Z) : ZxGap (fun x => b + ω ^ L x) {e | HCl S a Z e} Z := by
  intro e he hlt
  rcases lt_or_ge e b with h1 | h1
  · exact ⟨0, hZ.1, h1.trans_le le_self_add⟩
  · have hd : e - b < ω ^ L (Om 1) := Ry.rySub_lt h1 hlt
    have hdC : HCl S a Z (e - b) := ktHCl_sub e he b
    have e1 : e = b + (e - b) := (Ordinal.add_sub_cancel_of_le h1).symm
    rcases eq_or_ne (e - b) 0 with h0 | h0
    · refine ⟨0, hZ.1, ?_⟩
      show e < b + ω ^ L (0 + 1)
      rw [e1, h0, add_zero]
      exact lt_add_of_pos_right b (opow_pos _ omega0_pos)
    · have hlog : log ω (e - b) < L (Om 1) := (lt_opow_iff_log_lt one_lt_omega0 h0).1 hd
      obtain ⟨q, hq, hqe⟩ := hg _ (ktHCl_log hdC) hlog
      refine ⟨q, hq, ?_⟩
      show e < b + ω ^ L (q + 1)
      rw [e1]
      exact (add_lt_add_iff_left b).2 ((lt_opow_iff_log_lt one_lt_omega0 h0).2 hqe)

/-- **THE GAP OF EVERY TOWER at `HCl(a, Z)`** once its bottom exponent is a member. -/
theorem ktGap (hZ : SC Z) : ∀ t : KaT, HCl S a Z t.bm → ZxGap t.ev {e | HCl S a Z e} Z
  | KaT.base _ _, hm => ktGap_mul hZ hm
  | KaT.up _ t, hm => ktGap_opow hZ (ktGap hZ t hm)

end Googology.Trans.PoR.InaccPsi.R2.Kt

#print axioms Googology.Trans.PoR.InaccPsi.R2.Kt.ktHCl_div
#print axioms Googology.Trans.PoR.InaccPsi.R2.Kt.ktGap
