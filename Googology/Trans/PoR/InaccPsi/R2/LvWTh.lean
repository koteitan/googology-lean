import Googology.Trans.PoR.InaccPsi.R2.LvWTm

/-!
# The exact `R₁⁺`-reaches at the levels `x·(k+1) + b` and of the top `ϑˣ(Ω₁·(x·ω))`

From `Lv.lv_lh_gen` (the reach at every level `x ≤ β < Ω₁`, `R2.LvTh`):

* `LvW.luL_eq` (`luL(a, x·(k+1) + b) = a·x + x + a·(x·k + b)`), `LvW.lh_th` (**the reach of
  `ϑˣ(Ω₁·(x·(k+1) + b) + η)`**);
* `LvW.luL_top` (`luL(a, x·ω) = a·ω^{x+1}`), `LvW.lh_top` (**the reach of the top: `a·ω^{x+1}`**);
* `LvW.th_facts`, `LvW.th_lt`, `LvW.th_le` (the facts and the monotonicity at a level `x·(k+1) + b`).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

namespace LvW

/-- The non-remainder part of the exact reach at the level `x·(k+1) + b`. -/
noncomputable def L (x : Ordinal.{0}) (k : ℕ) (b a : Ordinal.{0}) : Ordinal.{0} :=
  (a * x + x) + a * (x * (k : Ordinal.{0}) + b)

theorem natCast_succ_comm (k : ℕ) : (k : Ordinal.{0}) + 1 = 1 + (k : Ordinal.{0}) := by
  rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add, Nat.add_comm]

/-- `luL(a, x·(k+1) + b) = a·x + x + a·(x·k + b)` for an `ε`-number `x` and `b < x`. -/
theorem luL_eq {x a : Ordinal.{0}} (hx : InE x) (k : ℕ) {b : Ordinal.{0}} (hb : b < x) :
    Lu.luL a (lvwL x k b) = L x k b a := by
  have hx' : ω ^ x = x := hx
  have hxω : ω ≤ lvwL x k b := by
    unfold lvwL
    calc ω ≤ x := (Lu.lu_omega_lt_E hx).le
      _ = x * 1 := (mul_one x).symm
      _ ≤ x * ((k : Ordinal.{0}) + 1) := mul_le_mul_right le_add_self x
      _ ≤ _ := le_self_add
  have hk0 : (k : Ordinal.{0}) + 1 ≠ 0 := (lt_of_lt_of_le zero_lt_one le_add_self).ne'
  have hkω : (k : Ordinal.{0}) + 1 < ω := by exact_mod_cast natCast_lt_omega0 (k + 1)
  have hlog : log ω (lvwL x k b) = x := by
    have := log_opow_mul_add (b := ω) (u := x) (v := (k : Ordinal.{0}) + 1) (w := b) one_lt_omega0 hk0
      (by rw [hx']; exact hb)
    rw [hx', log_eq_zero hkω, add_zero] at this
    exact this
  have hsplit : lvwL x k b = x + (x * (k : Ordinal.{0}) + b) := by
    unfold lvwL
    rw [natCast_succ_comm, mul_add, mul_one, add_assoc]
  unfold Lu.luL L
  rw [if_neg (not_lt.2 hxω), hlog, hx', Lu.lu_lg_E hx, hsplit, Ordinal.add_sub_cancel]

/-- `luL(a, x·ω) = a·ω^{x+1}` for an `ε`-number `x`. -/
theorem luL_top {x a : Ordinal.{0}} (hx : InE x) : Lu.luL a (x * ω) = a * ω ^ (x + 1) := by
  have hx' : ω ^ x = x := hx
  have e : x * ω = ω ^ (x + 1) := by rw [opow_add, opow_one, hx']
  have hxω : ω ≤ x * ω := (Lu.lu_omega_lt_E hx).le.trans (Ordinal.le_mul_left x omega0_pos)
  have hlg : lg (x + 1) = 0 := by
    rw [Lu.lu_lg_add hx one_ne_zero (Lu.lu_one_lt_E hx)]
    simpa using lg_nat (n := 1) one_ne_zero
  unfold Lu.luL
  rw [if_neg (not_lt.2 hxω), e, log_opow one_lt_omega0, hlg, add_zero, Ordinal.sub_self, mul_zero, add_zero]

/-- The facts at a level `x·(k+1) + b`. -/
theorem th_facts {x b η : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (k : ℕ) (hb : b < x)
    (hη : η ∈ Tset x) (hη1 : η < Om1) :
    Om1 * lvwL x k b + η ∈ Tset x ∧ Om1 * lvwL x k b + η < OmTwo ∧
    vt x (Om1 * lvwL x k b + η) ∈ Tset x ∧ x < vt x (Om1 * lvwL x k b + η) ∧
    vt x (Om1 * lvwL x k b + η) < Om1 ∧ InE (vt x (Om1 * lvwL x k b + η)) ∧
    Indec (vt x (Om1 * lvwL x k b + η)) ∧ lvwL x k b < vt x (Om1 * lvwL x k b + η) ∧
    η < vt x (Om1 * lvwL x k b + η) := by
  obtain ⟨hLT, hxL, -, hL1⟩ := lvwL_facts hx hx1 (k := k) hb
  exact Lv.gen_facts hx hx1 hLT hxL hL1 hη hη1

/-- **The reach of `ϑˣ(Ω₁·(x·(k+1) + b) + η)`**: the block `L` and the remainder `ζ`. -/
theorem lh_th {x b η : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (k : ℕ) (hb : b < x)
    (hη : η ∈ Tset x) (hη1 : η < Om1) :
    IsLh1 (vt x (Om1 * lvwL x k b + η))
      (L x k b (vt x (Om1 * lvwL x k b + η)) + luZeta x (lvwL x k b) η) := by
  obtain ⟨hLT, hxL, -, hL1⟩ := lvwL_facts hx hx1 (k := k) hb
  have h := Lv.lv_lh_gen hx hx1 hLT hxL hL1 hη hη1
  rwa [luL_eq hx k hb] at h

/-- **The reach of the top**: `lh(ϑˣ(Ω₁·(x·ω))) = ϑˣ(Ω₁·(x·ω))·ω^{x+1}`. -/
theorem lh_top {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    IsLh1 (lvwTop x) (lvwTop x * ω ^ (x + 1)) := by
  obtain ⟨hwT, hw1⟩ := lvw_xw hx hx1
  have h := Lv.lv_lh_gen hx hx1 hwT (Ordinal.le_mul_left x omega0_pos) hw1 (mem_T_of_le hx hx1 zero_le)
    (Ordinal.omega_pos 1)
  rw [add_zero, Lu.lu_zeta_zero, add_zero, luL_top hx] at h
  exact h

/-- Strict monotonicity in the remainder at a level `x·(k+1) + b`. -/
theorem th_lt {x b σ η : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (k : ℕ) (hb : b < x)
    (hσ : σ ∈ Tset x) (hη : η ∈ Tset x) (hη1 : η < Om1) (hση : σ < η) :
    vt x (Om1 * lvwL x k b + σ) < vt x (Om1 * lvwL x k b + η) := by
  obtain ⟨hLT, hxL, -, hL1⟩ := lvwL_facts hx hx1 (k := k) hb
  exact lvVt_eta_lt hx hx1 hLT hxL hL1 hσ (hση.trans hη1) hη hη1 hση
    (hση.trans (th_facts hx hx1 k hb hη hη1).2.2.2.2.2.2.2.2)

theorem th_le {x b σ η : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (k : ℕ) (hb : b < x)
    (hσ : σ ∈ Tset x) (hη : η ∈ Tset x) (hη1 : η < Om1) (hση : σ ≤ η) :
    vt x (Om1 * lvwL x k b + σ) ≤ vt x (Om1 * lvwL x k b + η) := by
  rcases hση.lt_or_eq with h | rfl
  · exact (th_lt hx hx1 k hb hσ hη hη1 h).le
  · exact le_rfl

end LvW

end Googology.Trans.PoR.InaccPsi.R2
