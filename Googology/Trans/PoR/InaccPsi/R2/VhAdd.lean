import Googology.Trans.PoR.InaccPsi.R2.VhDiv
import Googology.Trans.PoR.InaccPsi.R2.VeOm1

/-!
# The level shift `κ_λ` and the image `T` are additive; `T(W^g·d + r) = Ω^{T g}·Θ d + T r`

`κ = Vb.vbK S λ` (the level shift at `λ`), `T = Vb.vbT S λ` (its inverse), `E = Rx.RxE S W_λ` (the domain of `κ`),
`D = Vb.VbD S λ`, `Θ = gxTh ρ_λ (ldAtR λ)`, `W^g = Ω₂^g` (`leWe`), `Ω^g = Ω₁^g` (`leOe`).

* `vhE_add`, `vhE_opow`, `vhE_mulNat`, `vhE_omul` (`E` is closed under `+`, `ω^·`, `·n`, `ω^q·`);
* `vhK_cnf` (**`κ(ω^e·n + s) = ω^{κ e}·n + κ s` for every exponent `e`**, `s < ω^e`), `vhK_opow`;
* `vhK_add` (**`κ(x + y) = κ x + κ y` on `E`**), `vhK_omul` (**`κ(ω^q·v) = ω^{κ q}·κ v`**);
* `vhT_add` (**`T(x + y) = T x + T y` on `D`**), `vhT_cnfW` (**`T(W^g·d + r) = Ω^{T g}·Θ d + T r`** for
  `g, r ∈ D` and a code `d < Ω₂` of `H_λ`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rx
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ve

variable {S : InaccSeq.{0}}

section Dom

variable {T : Ordinal.{0}}

theorem vhE_add {x y : Ordinal.{0}} (hx : RxE S T x) (hy : RxE S T y) : RxE S T (x + y) :=
  ⟨RxN.add hx.1 hy.1, CSet.add_mem hx.2.1 hy.2.1, vbOmW_SC.isPrincipal hx.2.2 hy.2.2⟩

theorem vhE_opow {x : Ordinal.{0}} (hx : RxE S T x) : RxE S T (ω ^ x) := by
  refine ⟨RxN.opow hx.1, vhC_opow hx.2.1, ?_⟩
  have := vbOmW_SC.2 0 (Om_pos omega0_ne_zero) x hx.2.2; rwa [veblen_zero_apply] at this

theorem vhE_mulNat {x : Ordinal.{0}} (hx : RxE S T x) (n : ℕ) : RxE S T (x * n) :=
  ⟨RxN.mul_nat hx.1 n, ConjT.mul_nat_mem S hx.2.1 n,
    vbMulNat_lt vbOmW_SC.isPrincipal vbOmW_SC.1 hx.2.2 n⟩

/-- The Cantor normal form of a nonzero member: its parts are members. -/
theorem vhCnf {x : Ordinal.{0}} (hx : RxE S T x) (hx0 : x ≠ 0) :
    ∃ e s : Ordinal.{0}, ∃ n : ℕ, 1 ≤ n ∧ s < ω ^ e ∧ x = ω ^ e * n + s ∧ x < ω ^ Order.succ e ∧
      ω ^ e ≤ x ∧ RxE S T e ∧ RxE S T s ∧ s < x := by
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
  have hpos : (0 : Ordinal.{0}) < n := hn ▸ div_opow_log_pos ω hx0
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (by rintro rfl; exact lt_irrefl _ hpos)
  have hs : x % ω ^ log ω x < ω ^ log ω x := Ordinal.mod_lt x (opow_pos _ omega0_pos).ne'
  have hle : ω ^ log ω x ≤ x := opow_log_le_self ω hx0
  refine ⟨log ω x, x % ω ^ log ω x, n, hn1, hs, ?_, lt_opow_succ_log_self one_lt_omega0 x, hle,
    (rxE_log hx).1, (rxE_rem hx).1, hs.trans_le hle⟩
  rw [← hn]; exact (Ordinal.div_add_mod x _).symm

theorem vhE_omul : ∀ v, RxE S T v → ∀ q, RxE S T q → RxE S T (ω ^ q * v) := by
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv q hq
  rcases eq_or_ne v 0 with rfl | hv0
  · rw [mul_zero]; exact rxE_zero
  obtain ⟨e, s, n, -, -, hvd, -, -, heE, hsE, hsv⟩ := vhCnf hv hv0
  have e1 : ω ^ q * v = ω ^ (q + e) * n + ω ^ q * s := by
    rw [hvd, mul_add, ← mul_assoc, ← opow_add]
  rw [e1]
  exact vhE_add (vhE_mulNat (vhE_opow (vhE_add hq heE)) n) (IH s hsv hsE q hq)

end Dom

section Rst

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

theorem vhK_zero : vbK S l 0 = 0 := rxL_zero (vbZ hl hX).1

/-- **`κ(ω^e·n + s) = ω^{κ e}·n + κ s` for every exponent `e`** (`s < ω^e`, `n ≥ 1`). -/
theorem vhK_cnf {e s : Ordinal.{0}} (n : ℕ) (hn1 : 1 ≤ n) (he : RxE S (vbW S l) e)
    (hs : RxE S (vbW S l) s) (hse : s < ω ^ e) :
    vbK S l (ω ^ e * n + s) = ω ^ vbK S l e * n + vbK S l s := by
  by_cases h1 : Om 1 ≤ e
  · exact (vbK_cnf hl hX n hn1 he hs h1 hse).2
  push Not at h1
  have hO : Om1 = Om 1 := Br.Om1_eq
  have hSC : SC (Om 1 : Ordinal.{0}) := SC_Om one_ne_zero
  have hoe : ω ^ e < Om 1 := by
    have := hSC.2 0 hSC.1 e h1; rwa [veblen_zero_apply] at this
  have hon : ω ^ e * n < Om 1 := vbMulNat_lt hSC.isPrincipal hSC.1 hoe n
  have hsum : ω ^ e * n + s < Om 1 := hSC.isPrincipal hon (hse.trans hoe)
  have hoE : RxE S (vbW S l) (ω ^ e) := vhE_opow he
  have honE : RxE S (vbW S l) (ω ^ e * n) := vhE_mulNat hoE n
  rw [veK_small_add hl hX honE (hO ▸ hon) hs (hO ▸ (hse.trans hoe)) (vhE_add honE hs) (hO ▸ hsum),
    veK_small_mul_nat n hl hX hoE (hO ▸ hoe) honE (hO ▸ hon), veK_small_opow hl hX he (hO ▸ h1) hoE]

theorem vhK_opow {e : Ordinal.{0}} (he : RxE S (vbW S l) e) : vbK S l (ω ^ e) = ω ^ vbK S l e := by
  have h := vhK_cnf hl hX 1 le_rfl he rxE_zero (opow_pos e omega0_pos)
  rwa [Nat.cast_one, mul_one, add_zero, vhK_zero hl hX, add_zero, mul_one] at h

theorem vhK_lt_opow {s e : Ordinal.{0}} (hs : RxE S (vbW S l) s) (he : RxE S (vbW S l) e) (h : s < ω ^ e) :
    vbK S l s < ω ^ vbK S l e := by
  rw [← vhK_opow hl hX he]; exact vbK_mono hl hX hs (vhE_opow he) h

/-- **`κ(x + y) = κ x + κ y` on the domain of `κ`.** -/
theorem vhK_add : ∀ x, RxE S (vbW S l) x → ∀ y, RxE S (vbW S l) y →
    vbK S l (x + y) = vbK S l x + vbK S l y := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx y hy
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [zero_add, vhK_zero hl hX, zero_add]
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [add_zero, vhK_zero hl hX, add_zero]
  obtain ⟨e, s, n, hn1, hse, hxd, hxlt, -, heE, hsE, hsx⟩ := vhCnf hx hx0
  obtain ⟨b, t, k, hk1, htb, hyd, hylt, hyle, hbE, htE, -⟩ := vhCnf hy hy0
  have hKx : vbK S l x = ω ^ vbK S l e * n + vbK S l s :=
    (congrArg (vbK S l) hxd).trans (vhK_cnf hl hX n hn1 heE hsE hse)
  have hKy : vbK S l y = ω ^ vbK S l b * k + vbK S l t :=
    (congrArg (vbK S l) hyd).trans (vhK_cnf hl hX k hk1 hbE htE htb)
  have hk0 : (0 : Ordinal.{0}) < k := by exact_mod_cast hk1
  rcases lt_trichotomy b e with hbe | rfl | heb
  · -- `y < ω^e`
    have hye : y < ω ^ e := hylt.trans_le (opow_le_opow_right omega0_pos (Order.succ_le_of_lt hbe))
    have hsy : s + y < ω ^ e := isPrincipal_add_omega0_opow e hse hye
    have e1 : x + y = ω ^ e * n + (s + y) := by rw [hxd, add_assoc]
    rw [e1, vhK_cnf hl hX n hn1 heE (vhE_add hsE hy) hsy, IH s hsx hsE y hy, hKx, add_assoc]
  · -- same leading exponent
    have hab : s + ω ^ b * k = ω ^ b * k := Ordinal.add_absorp hse (Ordinal.le_mul_left _ hk0)
    have e1 : x + y = ω ^ b * ((n + k : ℕ) : Ordinal.{0}) + t := by
      rw [hxd, hyd, add_assoc, ← add_assoc s, hab, ← add_assoc, ← mul_add, Nat.cast_add]
    have hKs : vbK S l s < ω ^ vbK S l b := vhK_lt_opow hl hX hsE hbE hse
    have hab' : vbK S l s + ω ^ vbK S l b * k = ω ^ vbK S l b * k :=
      Ordinal.add_absorp hKs (Ordinal.le_mul_left _ hk0)
    rw [e1, vhK_cnf hl hX (n + k) (by omega) hbE htE htb, hKx, hKy, add_assoc, ← add_assoc (vbK S l s), hab',
      ← add_assoc, ← mul_add, Nat.cast_add]
  · -- `x < ω^b`
    have hxb : x < ω ^ b := hxlt.trans_le (opow_le_opow_right omega0_pos (Order.succ_le_of_lt heb))
    have e1 : x + y = y := Ordinal.add_absorp hxb hyle
    have hKxb : vbK S l x < ω ^ vbK S l b := vhK_lt_opow hl hX hx hbE hxb
    have hKyb : ω ^ vbK S l b ≤ vbK S l y := by
      rw [hKy]; exact (Ordinal.le_mul_left _ hk0).trans le_self_add
    rw [e1, Ordinal.add_absorp hKxb hKyb]

/-- **`κ(ω^q·v) = ω^{κ q}·κ v`.** -/
theorem vhK_omul : ∀ v, RxE S (vbW S l) v → ∀ q, RxE S (vbW S l) q →
    vbK S l (ω ^ q * v) = ω ^ vbK S l q * vbK S l v := by
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv q hq
  rcases eq_or_ne v 0 with rfl | hv0
  · rw [mul_zero, vhK_zero hl hX, mul_zero]
  obtain ⟨e, s, n, hn1, hse, hvd, -, -, heE, hsE, hsv⟩ := vhCnf hv hv0
  have e1 : ω ^ q * v = ω ^ (q + e) * n + ω ^ q * s := by
    rw [hvd, mul_add, ← mul_assoc, ← opow_add]
  have hlt : ω ^ q * s < ω ^ (q + e) := by
    rw [opow_add]; exact (mul_lt_mul_iff_right₀ (opow_pos q omega0_pos)).2 hse
  have hKv : vbK S l v = ω ^ vbK S l e * n + vbK S l s :=
    (congrArg (vbK S l) hvd).trans (vhK_cnf hl hX n hn1 heE hsE hse)
  rw [e1, vhK_cnf hl hX n hn1 (vhE_add hq heE) (vhE_omul s hsE q hq) hlt, vhK_add hl hX q hq e heE,
    IH s hsv hsE q hq, hKv, mul_add, ← mul_assoc, ← opow_add]

/-- **`T(x + y) = T x + T y` on `D`.** -/
theorem vhT_add {x y : Ordinal.{0}} (hx : VbD S l x) (hy : VbD S l y) :
    vbT S l (x + y) = vbT S l x + vbT S l y := by
  obtain ⟨hxE, hxK⟩ := vbT_eq hl hX hx
  obtain ⟨hyE, hyK⟩ := vbT_eq hl hX hy
  have h := vhK_add hl hX _ hxE _ hyE
  rw [hxK, hyK] at h
  rw [← h]; exact vbT_K hl hX (vhE_add hxE hyE)

/-- **`T(W^g·d + r) = Ω^{T g}·Θ d + T r`** for `g, r ∈ D` and a code `d < Ω₂` of `H_λ`. -/
theorem vhT_cnfW {g d r : Ordinal.{0}} (hg : VbD S l g) (hr : VbD S l r) (hdH : d ∈ cdHull S l)
    (hdW : d < Om (1 + 1)) :
    vbT S l (leWe g * d + r) = leOe (vbT S l g) * gxTh (upsilon l) (ldAtR S l) d + vbT S l r := by
  obtain ⟨hgE, hgK⟩ := vbT_eq hl hX hg
  obtain ⟨hrE, hrK⟩ := vbT_eq hl hX hr
  obtain ⟨hdE, hdK⟩ := vbCode_K hl hX hdW hdH
  have hΩE : RxE S (vbW S l) (Om 1) := by
    have h : RxE S (vbW S l) (Om ((1 : ℕ) : Ordinal.{0})) :=
      ⟨RxN.om (rxN_nat 1), rxC_Om_nat _ _ 1, Om_lt_Om.2 (natCast_lt_omega0 1)⟩
    rwa [Nat.cast_one] at h
  have hKΩ : vbK S l (Om 1) = Om (1 + 1) := by
    have h : vbK S l (Om ((1 : ℕ) : Ordinal.{0})) = Om (((1 : ℕ) : Ordinal.{0}) + 1) := rxL_Om le_rfl
    rwa [Nat.cast_one] at h
  have h1 : ω ^ Om (1 : Ordinal.{0}) = Om 1 := Bt.Om1_opow
  have h2 : ω ^ Om (1 + 1 : Ordinal.{0}) = Om (1 + 1) := gg_SC_eps ldOm2_SC
  set yg := vbT S l g
  set yr := vbT S l r
  set yd := gxTh (upsilon l) (ldAtR S l) d
  have hqE : RxE S (vbW S l) (Om 1 * yg) := by
    have h := vhE_omul yg hgE (Om 1) hΩE; rwa [h1] at h
  have hKq : vbK S l (Om 1 * yg) = Om (1 + 1) * g := by
    have h := vhK_omul hl hX yg hgE (Om 1) hΩE
    rwa [h1, hKΩ, h2, hgK] at h
  have hYE : RxE S (vbW S l) (leOe yg * yd + yr) := vhE_add (vhE_omul yd hdE _ hqE) hrE
  have hKY : vbK S l (leOe yg * yd + yr) = leWe g * d + r := by
    show vbK S l (ω ^ (Om 1 * yg) * yd + yr) = ω ^ (Om (1 + 1) * g) * d + r
    rw [vhK_add hl hX _ (vhE_omul yd hdE _ hqE) _ hrE, vhK_omul hl hX yd hdE _ hqE, hKq, hdK, hrK]
  rw [← hKY]; exact vbT_K hl hX hYE

end Rst

end Googology.Trans.PoR.InaccPsi.R2.Vh
