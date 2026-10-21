import Googology.Trans.PoR.InaccPsi.R2.MxB
import Googology.Trans.PoR.InaccPsi.R2.LvTh

/-!
# `B_n` keeps the products `x·γ` for an ε-number `x`, the leading exponent `log_ω`, and the block `luL`

`B_n = Bc.bcB S n`; `luL a β = a·(1 + β)` for finite `β`, `a·ω^{b₁} + logend(b₁) + a·(β − ω^{b₁})` for infinite `β`,
`b₁ = log_ω β` (`Lu.luL`, the block of the `R₁⁺`-reach of `ϑᵗ(Ω₁·β + η)`).

* `mxB_eps` (`B_n x` is an ε-number when `x` is), `mxB_mul_opow` (**`B_n(x·ω^g) = B_n x·ω^{B_n g}`**), `mxB_mul`
  (**`B_n(x·γ) = B_n x·B_n γ`** for an ε-number `x`, `x·γ < L(ω)`, by induction on `γ = ω^g + r`);
* `mxB_log` (**`log_ω(B_n a) = B_n(log_ω a)`**), `mxB_sub_lead` (`B_n(a − ω^{log a}) = B_n a − ω^{log(B_n a)}`);
* `mxB_luL` (**`B_n(luL x a) = luL(B_n x, B_n a)`** for an ε-number `x` and `1 ≤ a < x`, `x·x < L(ω)`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Mx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw

variable {S : InaccSeq.{0}}

/-- `B_n x` is an ε-number when `x < L(ω)` is. -/
theorem mxB_eps {n : ℕ} {x : Ordinal.{0}} (hx : InE x) (hxL : x < Nc.ncL S ω) : InE (Bc.bcB S n x) := by
  have h := Tp.tpOpowB (S := S) (n := n) (a := x) (by unfold InE at hx; rw [hx]; exact hxL)
  unfold InE at hx ⊢; rw [hx] at h; exact h.symm

/-- **`B_n(x·ω^g) = B_n x·ω^{B_n g}`** for an ε-number `x` with `x·ω^g < L(ω)`. -/
theorem mxB_mul_opow {n : ℕ} {x g : Ordinal.{0}} (hx : InE x) (hL : x * ω ^ g < Nc.ncL S ω) :
    Bc.bcB S n (x * ω ^ g) = Bc.bcB S n x * ω ^ Bc.bcB S n g := by
  have hx' : ω ^ x = x := hx
  have e : x * ω ^ g = ω ^ (x + g) := by rw [opow_add, hx']
  have hxL : x < Nc.ncL S ω :=
    lt_of_le_of_lt (le_mul_left x (opow_pos g omega0_pos)) hL
  have hgL : g < Nc.ncL S ω := by
    refine lt_of_le_of_lt ?_ hL
    calc g ≤ ω ^ g := right_le_opow g one_lt_omega0
      _ ≤ x * ω ^ g := le_mul_right _ (lt_of_lt_of_le zero_lt_one (by
          rw [← hx']; exact Order.one_le_iff_ne_zero.2 (opow_pos x omega0_pos).ne'))
  have hBE : ω ^ Bc.bcB S n x = Bc.bcB S n x := mxB_eps (n := n) hx hxL
  rw [e, Tp.tpOpowB (by rw [← e]; exact hL), Bc.bcB_add hxL hgL, opow_add, hBE]

/-- **`B_n(x·γ) = B_n x·B_n γ`** for an ε-number `x` and `x·γ < L(ω)`. -/
theorem mxB_mul {n : ℕ} {x : Ordinal.{0}} (hx : InE x) :
    ∀ γ, x * γ < Nc.ncL S ω → Bc.bcB S n (x * γ) = Bc.bcB S n x * Bc.bcB S n γ := by
  have hx0 : 0 < x := by
    have hx' : ω ^ x = x := hx
    rw [← hx']; exact opow_pos x omega0_pos
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hL
  rcases eq_or_ne γ 0 with rfl | hγ0
  · rw [mul_zero, Bc.bcB_zero, mul_zero]
  set g := log ω γ with hg
  have hlead : ω ^ g ≤ γ := opow_log_le_self ω hγ0
  have hγlt : γ < ω ^ g * ω := by rw [← opow_succ, hg]; exact lt_opow_succ_log_self one_lt_omega0 γ
  set r := γ - ω ^ g with hr
  have hdec : ω ^ g + r = γ := Ordinal.add_sub_cancel_of_le hlead
  have hrγ : r < γ := by
    refine lt_of_le_of_ne (by rw [← hdec]; exact le_add_self) fun e => ?_
    have h' : ω ^ g + γ = γ := by
      calc ω ^ g + γ = ω ^ g + r := by rw [e]
        _ = γ := hdec
    have := Ordinal.add_eq_right_iff_mul_omega0_le.1 h'
    exact absurd (lt_of_lt_of_le hγlt this) (lt_irrefl _)
  have hγL : γ < Nc.ncL S ω := lt_of_le_of_lt (le_mul_right γ hx0) hL
  have h1 : x * ω ^ g ≤ x * γ := mul_le_mul_right hlead x
  have h2 : x * r ≤ x * γ := mul_le_mul_right hrγ.le x
  have hgL : ω ^ g < Nc.ncL S ω := lt_of_le_of_lt hlead hγL
  have hrL : r < Nc.ncL S ω := hrγ.trans hγL
  calc Bc.bcB S n (x * γ) = Bc.bcB S n (x * ω ^ g + x * r) := by rw [← mul_add, hdec]
    _ = Bc.bcB S n (x * ω ^ g) + Bc.bcB S n (x * r) :=
        Bc.bcB_add (lt_of_le_of_lt h1 hL) (lt_of_le_of_lt h2 hL)
    _ = Bc.bcB S n x * ω ^ Bc.bcB S n g + Bc.bcB S n x * Bc.bcB S n r := by
        rw [mxB_mul_opow hx (lt_of_le_of_lt h1 hL), IH r hrγ (lt_of_le_of_lt h2 hL)]
    _ = Bc.bcB S n x * Bc.bcB S n γ := by
        rw [← mul_add, ← Tp.tpOpowB hgL, ← Bc.bcB_add hgL hrL, hdec]

/-- **`log_ω(B_n a) = B_n(log_ω a)`** for `0 < a < L(ω)`. -/
theorem mxB_log {n : ℕ} {a : Ordinal.{0}} (ha0 : a ≠ 0) (haL : a < Nc.ncL S ω) :
    log ω (Bc.bcB S n a) = Bc.bcB S n (log ω a) := by
  set g := log ω a with hg
  have hlead : ω ^ g ≤ a := opow_log_le_self ω ha0
  have hgL' : ω ^ g < Nc.ncL S ω := lt_of_le_of_lt hlead haL
  have hgL : g < Nc.ncL S ω := lt_of_le_of_lt (right_le_opow g one_lt_omega0) hgL'
  -- `a < ω^g·(m+1)` for a natural `m`
  have hpos : ω ^ g ≠ 0 := (opow_pos g omega0_pos).ne'
  have hq : a / ω ^ g < ω := div_opow_log_lt a one_lt_omega0
  obtain ⟨m, hm⟩ := lt_omega0.1 hq
  have ham : a < ω ^ g * ((m + 1 : ℕ) : Ordinal.{0}) := by
    have := lt_mul_succ_div a hpos
    rw [hm, succ_eq_add_one] at this
    exact_mod_cast this
  have hmL : ω ^ g * ((m + 1 : ℕ) : Ordinal.{0}) < Nc.ncL S ω := mw_mul_nat_lt hgL' _
  have hBa : Bc.bcB S n a < ω ^ Bc.bcB S n g * ((m + 1 : ℕ) : Ordinal.{0}) := by
    have := (Bc.bcB_lt_iff (k := n) haL hmL).2 ham
    rwa [mwB_mul_nat hgL', Tp.tpOpowB hgL'] at this
  have hBa0 : Bc.bcB S n a ≠ 0 := by
    intro h
    have := (Bc.bcB_lt_iff (k := n) (Lw.lw_L_SC S ω).1 haL).2 (pos_iff_ne_zero.2 ha0)
    rw [Bc.bcB_zero, h] at this
    exact lt_irrefl _ this
  refine (log_eq_iff one_lt_omega0 hBa0 _).2 ⟨?_, ?_⟩
  · rw [← Tp.tpOpowB hgL']; exact Tp.tpB_le haL hlead
  · refine hBa.trans_le ?_
    rw [opow_add, opow_one]
    exact mul_le_mul_right (natCast_lt_omega0 _).le _

/-- `B_n(a − ω^{log a}) = B_n a − ω^{log(B_n a)}` for `0 < a < L(ω)`. -/
theorem mxB_sub_lead {n : ℕ} {a : Ordinal.{0}} (ha0 : a ≠ 0) (haL : a < Nc.ncL S ω) :
    Bc.bcB S n (a - ω ^ log ω a) = Bc.bcB S n a - ω ^ log ω (Bc.bcB S n a) := by
  have hlead : ω ^ log ω a ≤ a := opow_log_le_self ω ha0
  have hgL' : ω ^ log ω a < Nc.ncL S ω := lt_of_le_of_lt hlead haL
  have hrL : a - ω ^ log ω a < Nc.ncL S ω := lt_of_le_of_lt (Ordinal.sub_le_self _ _) haL
  have e : Bc.bcB S n a = ω ^ Bc.bcB S n (log ω a) + Bc.bcB S n (a - ω ^ log ω a) := by
    conv_lhs => rw [← Ordinal.add_sub_cancel_of_le hlead]
    rw [Bc.bcB_add hgL' hrL, Tp.tpOpowB hgL']
  rw [mxB_log ha0 haL, e, Ordinal.add_sub_cancel]

/-- **`B_n(luL x a) = luL(B_n x, B_n a)`** for an ε-number `x < L(ω)` with `x·x < L(ω)` and `1 ≤ a < x`. -/
theorem mxB_luL {n : ℕ} {x a : Ordinal.{0}} (hx : InE x) (hxx : x * x < Nc.ncL S ω) (ha1 : 1 ≤ a)
    (hax : a < x) : Bc.bcB S n (Lu.luL x a) = Lu.luL (Bc.bcB S n x) (Bc.bcB S n a) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one (ha1.trans hax.le)
  have hxL : x < Nc.ncL S ω := lt_of_le_of_lt (le_mul_left x hx0) hxx
  have haL : a < Nc.ncL S ω := hax.trans hxL
  have hLp := (Lw.lw_L_SC S ω).isPrincipal
  rcases lt_or_ge a ω with haω | haω
  · obtain ⟨k, rfl⟩ := lt_omega0.1 haω
    have hk : (1 : Ordinal.{0}) + (k : Ordinal.{0}) = ((k + 1 : ℕ) : Ordinal.{0}) := by
      rw [← Nat.cast_one, ← Nat.cast_add, Nat.add_comm]
    rw [Lu.lu_luL_fin haω, mwB_nat, Lu.lu_luL_fin haω, hk, mwB_mul_nat hxL]
  · have ha0 : a ≠ 0 := (lt_of_lt_of_le omega0_pos haω).ne'
    have hBω : (ω : Ordinal.{0}) ≤ Bc.bcB S n a := by
      have := Tp.tpB_le (S := S) (n := n) haL haω
      rwa [mwB_omega] at this
    set g := log ω a with hg
    have hg1 : 1 ≤ g := one_le_iff_pos.2 (log_pos one_lt_omega0 ha0 haω)
    have hg0 : g ≠ 0 := (lt_of_lt_of_le zero_lt_one hg1).ne'
    have hlead : ω ^ g ≤ a := opow_log_le_self ω ha0
    have hgx : g < x := lt_of_le_of_lt (log_le_self ω a) hax
    have hgL : g < Nc.ncL S ω := hgx.trans hxL
    have hxg : x * ω ^ g < Nc.ncL S ω := by
      refine lt_of_le_of_lt (mul_le_mul_right (hlead.trans hax.le) x) hxx
    have hxr : x * (a - ω ^ g) < Nc.ncL S ω :=
      lt_of_le_of_lt (mul_le_mul_right ((Ordinal.sub_le_self _ _).trans hax.le) x) hxx
    have hlgL : lg g < Nc.ncL S ω := lt_of_le_of_lt (lg_le hg0) hgL
    rw [Lu.lu_luL_inf haω, Lu.lu_luL_inf hBω, ← hg, Bc.bcB_add (hLp hxg hlgL) hxr, Bc.bcB_add hxg hlgL,
      mxB_mul_opow hx hxg, ← Tp.tpLgB hg0 hgL, mxB_mul hx _ hxr, hg, mxB_sub_lead ha0 haL, mxB_log ha0 haL]

end Googology.Trans.PoR.InaccPsi.R2.Mx
