import Googology.Trans.PoR.InaccPsi.R2.ZmCg

/-!
# ZmCi: INVERSION FOR `TlCl` AT `ε`-NUMBERS AND THE GLOBAL GATE

* `zm_cl_eps` (**a code `c ∈ [E, ε_{E+1})` makes the `ε`-number `E` a code**, induction on the derivation);
* `zm_cl_veb1` (**`φ(1, b)` a code, not a fixed point of `φ(1, ·)` ⇒ `b` a code**);
* `zmHG_gate` (**a code `c < ζ_{B_Γ+1}` of `TlCl Z` has global gate below `Z`**, the gate of the index included).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zm

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Zb Googology.Trans.PoR.InaccPsi.R2.Zg Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Rh

variable {Z : Ordinal.{0}}

theorem zm_veb_pos_E {x y : Ordinal.{0}} (hx : x ≠ 0) : InE (veblen x y) := by
  have h := veblen_veblen_of_lt (pos_iff_ne_zero.2 hx) y
  rw [veblen_zero] at h
  exact h

/-- An `ε`-number in `[E, ε_{E+1})` is `E`. -/
theorem zm_eps_eq {E c : Ordinal.{0}} (hcE : InE c) (h1 : E ≤ c) (h2 : c < eN E) : c = E := by
  rcases h1.lt_or_eq with h | h
  · exact absurd (eN_le h hcE) (not_le.2 h2)
  · exact h.symm

/-- **A code in `[E, ε_{E+1})` makes `E` a code** (`E` an `ε`-number). -/
theorem zm_cl_eps : ∀ c, TlCl Z c → ∀ E, InE E → E ≤ c → c < eN E → TlCl Z E := by
  intro c hc
  induction hc with
  | small h => exact fun E _ h1 _ => TlCl.small (h1.trans_lt h)
  | om =>
    intro E hE h1 h2
    have e := zm_eps_eq Rj.rj_Om1_inE h1 h2
    rw [← e]; exact TlCl.om
  | @add x y hx hy ihx ihy =>
    intro E hE h1 h2
    rcases le_or_gt E y with hy' | hy'
    · exact ihy E hE hy' (lt_of_le_of_lt le_add_self h2)
    · rcases le_or_gt E x with hx' | hx'
      · exact ihx E hE hx' (lt_of_le_of_lt le_self_add h2)
      · exact absurd h1 (not_le.2 ((inE_indec hE).add_lt hx' hy'))
  | @phi x y hx hy ihx ihy =>
    intro E hE h1 h2
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [veblen_zero_apply] at h1 h2
      have hyE : E ≤ y := by
        by_contra hc; push Not at hc
        have : ω ^ y < ω ^ E := (opow_lt_opow_iff_right one_lt_omega0).2 hc
        rw [show ω ^ E = E from hE] at this
        exact absurd h1 (not_le.2 this)
      exact ihy E hE hyE (lt_of_le_of_lt (right_le_opow y one_lt_omega0) h2)
    · have e := zm_eps_eq (zm_veb_pos_E hx0) h1 h2
      rw [← e]; exact TlCl.phi hx hy
  | @atom β y hβ hy h ihβ ihy =>
    intro E hE h1 h2
    have e := zm_eps_eq (Low.opow_eq_self_of_SC (rhF_SC β y)) h1 h2
    rw [← e]; exact TlCl.atom hβ hy h

/-- **`φ(1, b)` a code, not a fixed point of `φ(1, ·)` ⇒ `b` a code.** -/
theorem zm_cl_veb1 : ∀ w, TlCl Z w → veblen 1 w ≠ w → ∀ b, veblen 1 b = w → TlCl Z b := by
  intro w hw
  induction hw with
  | small h => exact fun _ b hb => TlCl.small ((right_le_veblen 1 b).trans_lt (hb ▸ h))
  | om => exact fun hnf _ _ => absurd Gf.eps_Om1 hnf
  | @add x y hx hy ihx ihy =>
    intro hnf b hb
    have hE : InE (x + y) := by rw [← hb]; exact zm_veb_E b
    rcases lt_or_ge y (x + y) with hy' | hy'
    · rcases lt_or_ge x (x + y) with hx' | hx'
      · exact absurd ((inE_indec hE).add_lt hx' hy') (lt_irrefl _)
      · have e : x = x + y := le_antisymm le_self_add hx'
        rw [← e] at hnf hb
        exact ihx hnf b hb
    · have e : y = x + y := le_antisymm le_add_self hy'
      rw [← e] at hnf hb
      exact ihy hnf b hb
  | @phi x y hx hy ihx ihy =>
    intro hnf b hb
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [veblen_zero_apply] at hnf hb
      have hE : InE (ω ^ y) := by rw [← hb]; exact zm_veb_E b
      have e : y = ω ^ y := (isNormal_opow one_lt_omega0).strictMono.injective (by
        show ω ^ y = ω ^ (ω ^ y); exact hE.symm)
      rw [← e] at hnf hb
      exact ihy hnf b hb
    rcases eq_or_ne x 1 with rfl | hx1
    · rw [(isNormal_veblen 1).strictMono.injective hb]; exact hy
    · exfalso
      have h1x : 1 < x := lt_of_le_of_ne (one_le_iff_ne_zero.2 hx0) (Ne.symm hx1)
      exact hnf (veblen_veblen_of_lt h1x y)
  | @atom β y hβ hy h ihβ ihy =>
    intro hnf _ _
    exact absurd ((rhF_SC β y).veblen_right (lt_of_lt_of_le one_lt_omega0
      (omega0_lt_inE (Low.opow_eq_self_of_SC (rhF_SC β y))).le)) hnf

/-- **THE GLOBAL GATE BOUND**: a code `c < ζ_{B_Γ+1}` of `TlCl Z` (`Z ≤ Ω₁` strongly critical) has `zmHG c < Z`. -/
theorem zmHG_gate (hZ : SC Z) (hZ1 : Z ≤ Om1) : ∀ c, c < zmZ → TlCl Z c → zmHG c < Z := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcZ hC
  rcases lt_or_ge c tfBG with hcB | hcB
  · rw [zmHG_lt hcB]; exact zgGate hZ hZ1 hcB hC
  obtain ⟨b1, b2, b3⟩ := zm_bracket hcB hcZ
  set n := zmN c with hn
  have hEeq := zmBE_eq b1 b2
  set E := zmBE c with hEdef
  have hEE : InE E := by rw [hEeq]; exact zm_veb_E _
  have hEc : E ≤ c := hEeq ▸ b1
  have hcN : c < eN E := by rw [hEeq, Go.go_eN_veb, add_assoc]; exact b2
  have hEC : TlCl Z E := zm_cl_eps c hC E hEE hEc hcN
  -- the index
  have hnG : zmHG n < Z := by
    rcases eq_or_ne n 0 with h0 | h0
    · rw [h0, zmHG_zero]; exact hZ.1
    · have hBE : tfBG < E := by
        rw [hEeq]; conv_lhs => rw [← zm_BG_fix]
        exact (isNormal_veblen 1).strictMono (lt_add_of_pos_right _ (pos_iff_ne_zero.2 h0))
      have hnf : veblen 1 E ≠ E := zm_noFix hBE (hEc.trans_lt hcZ)
      have h1 := zm_cl_veb1 E hEC hnf (tfBG + n) hEeq.symm
      have h2 := (tlDec hZ _ h1).1 _ (zbBG_tl hZ.1) le_self_add
      rw [Ordinal.add_sub_cancel] at h2
      exact IH n b3 (b3.trans hcZ) h2
  -- the exponent, the digit and the rest
  obtain ⟨hk0, hd0, hdE, hrk, hdec⟩ := zm_dec hEE hEc
  have hko : log E c < c := zm_log_lt hEE hEc hcN
  have hro : c % E ^ log E c < c := zm_mod_lt hEE hEc
  have hdo : c / E ^ log E c < c := hdE.trans_le hEc
  set k := log E c with hkdef
  set d := c / E ^ k with hddef
  set r := c % E ^ k with hrdef
  have hEω : ω ^ E = E := hEE
  have hP : E ^ k = ω ^ (E * k) := zm_opow_eq hEE k
  have hlog : log ω c = E * k + log ω d := by
    rw [← hdec, hP]; exact log_opow_mul_add one_lt_omega0 hd0.ne' (hP ▸ hrk)
  have hlogC : TlCl Z (log ω c) := (tlDec hZ c hC).2
  have hld : log ω d < E := (log_le_self ω d).trans_lt hdE
  have hkC : TlCl Z k := by
    have h := (zm_cl_divOp hZ hEC (log ω c) hlogC).1
    rw [hlog, hEω, Ordinal.mul_add_div _ hEE.pos.ne', Ordinal.div_eq_zero_of_lt hld, add_zero] at h
    exact h
  have hPC : TlCl Z (E * k) := by
    have h := tl_cl_opow_mul hZ hEC _ hkC; rwa [hEω] at h
  obtain ⟨hdC, hrC⟩ := zm_cl_divOp hZ hPC c hC
  rw [← hP, ← hdec, Ordinal.mul_add_div _ (opow_pos _ hEE.pos).ne', Ordinal.div_eq_zero_of_lt hrk,
    add_zero] at hdC
  rw [← hP, ← hdec, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hrk] at hrC
  rw [zmHG_cnf hcB hcZ]
  exact max_lt hnG (max_lt (IH k hko (hko.trans hcZ) hkC)
    (max_lt (IH d hdo (hdo.trans hcZ) hdC) (IH r hro (hro.trans hcZ) hrC)))

end Googology.Trans.PoR.InaccPsi.R2.Zm
