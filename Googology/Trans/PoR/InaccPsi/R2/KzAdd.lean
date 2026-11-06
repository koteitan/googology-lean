import Googology.Trans.PoR.InaccPsi.R2.KzLaw

/-!
# Kz: THE SUM LAWS BELOW A BOUND `K` (`Vh.VhAdd` on `RxEK` / `D_K`)

* `kzE_add hKB`, `kzE_opow hKB`, `kzE_mulNat hKB`, `kzCnf hKB`, `kzE_omul hKB` (the domain is closed under the arithmetic);
* `kzK_zero`, `kzK_cnf`, `kzK_opow`, `kzK_lt_opow`, `kzK_add` (**`κ(x + y) = κ x + κ y`**), `kzK_omul`,
  `kzT_add` (**`T_K(x + y) = T_K x + T_K y`**), `kzT_cnfW` (`T_K(W^g·d + r) = Ω^{T_K g}·Θ d + T_K r`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rx
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ve

  Googology.Trans.PoR.InaccPsi.R2.Kz

variable {S : InaccSeq.{0}}

section Dom

variable {T K : Ordinal.{0}} (hKB : KzB S K)

include hKB

theorem kzE_add {x y : Ordinal.{0}} (hx : RxEK S T K x) (hy : RxEK S T K y) : RxEK S T K (x + y) :=
  ⟨RxN.add hx.1 hy.1, CSet.add_mem hx.2.1 hy.2.1, hKB.sc.isPrincipal hx.2.2 hy.2.2⟩

theorem kzE_opow {x : Ordinal.{0}} (hx : RxEK S T K x) : RxEK S T K (ω ^ x) := by
  refine ⟨RxN.opow hx.1, Vh.vhC_opow hx.2.1, ?_⟩
  have := hKB.sc.2 0 hKB.sc.1 x hx.2.2; rwa [veblen_zero_apply] at this

theorem kzE_mulNat {x : Ordinal.{0}} (hx : RxEK S T K x) (n : ℕ) : RxEK S T K (x * n) :=
  ⟨RxN.mul_nat hx.1 n, ConjT.mul_nat_mem S hx.2.1 n,
    vbMulNat_lt hKB.sc.isPrincipal hKB.sc.1 hx.2.2 n⟩

/-- The Cantor normal form of a nonzero member: its parts are members. -/
theorem kzCnf {x : Ordinal.{0}} (hx : RxEK S T K x) (hx0 : x ≠ 0) :
    ∃ e s : Ordinal.{0}, ∃ n : ℕ, 1 ≤ n ∧ s < ω ^ e ∧ x = ω ^ e * n + s ∧ x < ω ^ Order.succ e ∧
      ω ^ e ≤ x ∧ RxEK S T K e ∧ RxEK S T K s ∧ s < x := by
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
  have hpos : (0 : Ordinal.{0}) < n := hn ▸ div_opow_log_pos ω hx0
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (by rintro rfl; exact lt_irrefl _ hpos)
  have hs : x % ω ^ log ω x < ω ^ log ω x := Ordinal.mod_lt x (opow_pos _ omega0_pos).ne'
  have hle : ω ^ log ω x ≤ x := opow_log_le_self ω hx0
  refine ⟨log ω x, x % ω ^ log ω x, n, hn1, hs, ?_, lt_opow_succ_log_self one_lt_omega0 x, hle,
    (kzE_log hx).1, (kzE_rem hx).1, hs.trans_le hle⟩
  rw [← hn]; exact (Ordinal.div_add_mod x _).symm

theorem kzE_omul : ∀ v, RxEK S T K v → ∀ q, RxEK S T K q → RxEK S T K (ω ^ q * v) := by
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv q hq
  rcases eq_or_ne v 0 with rfl | hv0
  · rw [mul_zero]; exact (kzE_zero hKB)
  obtain ⟨e, s, n, -, -, hvd, -, -, heE, hsE, hsv⟩ := kzCnf hKB hv hv0
  have e1 : ω ^ q * v = ω ^ (q + e) * n + ω ^ q * s := by
    rw [hvd, mul_add, ← mul_assoc, ← opow_add]
  rw [e1]
  exact kzE_add hKB (kzE_mulNat hKB (kzE_opow hKB (kzE_add hKB hq heE)) n) (IH s hsv hsE q hq)

end Dom

section Rst

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {K : Ordinal.{0}} (hKB : KzB S K)

include hl hX hKB

theorem kzK_zero : vbK S l 0 = 0 := rxL_zero (vbZ hl hX).1

/-- **`κ(ω^e·n + s) = ω^{κ e}·n + κ s` for every exponent `e`** (`s < ω^e`, `n ≥ 1`). -/
theorem kzK_cnf {e s : Ordinal.{0}} (n : ℕ) (hn1 : 1 ≤ n) (he : RxEK S (vbW S l) K e)
    (hs : RxEK S (vbW S l) K s) (hse : s < ω ^ e) :
    vbK S l (ω ^ e * n + s) = ω ^ vbK S l e * n + vbK S l s := by
  by_cases h1 : Om 1 ≤ e
  · exact (vbKK_cnf hl hX hKB n hn1 he hs h1 hse).2
  push Not at h1
  have hO : Om1 = Om 1 := Br.Om1_eq
  have hSC : SC (Om 1 : Ordinal.{0}) := SC_Om one_ne_zero
  have hoe : ω ^ e < Om 1 := by
    have := hSC.2 0 hSC.1 e h1; rwa [veblen_zero_apply] at this
  have hon : ω ^ e * n < Om 1 := vbMulNat_lt hSC.isPrincipal hSC.1 hoe n
  have hsum : ω ^ e * n + s < Om 1 := hSC.isPrincipal hon (hse.trans hoe)
  have hoE : RxEK S (vbW S l) K (ω ^ e) := kzE_opow hKB he
  have honE : RxEK S (vbW S l) K (ω ^ e * n) := kzE_mulNat hKB hoE n
  have toE : ∀ {x : Ordinal.{0}}, RxEK S (vbW S l) K x → x < Om 1 → RxE S (vbW S l) x := fun hx h =>
    ⟨hx.1, CSet.of_lt (h.trans (psiS_bounds (S := S) (Om ω) 1).1), h.trans (Om_lt_Om.2 one_lt_omega0)⟩
  have hsum' := kzE_add hKB honE hs
  rw [veK_small_add hl hX (toE honE hon) (hO ▸ hon) (toE hs (hse.trans hoe)) (hO ▸ (hse.trans hoe))
      (toE hsum' hsum) (hO ▸ hsum),
    veK_small_mul_nat n hl hX (toE hoE hoe) (hO ▸ hoe) (toE honE hon) (hO ▸ hon),
    veK_small_opow hl hX (toE he h1) (hO ▸ h1) (toE hoE hoe)]

theorem kzK_opow {e : Ordinal.{0}} (he : RxEK S (vbW S l) K e) : vbK S l (ω ^ e) = ω ^ vbK S l e := by
  have h := kzK_cnf hl hX hKB 1 le_rfl he (kzE_zero hKB) (opow_pos e omega0_pos)
  rwa [Nat.cast_one, mul_one, add_zero, kzK_zero hl hX hKB, add_zero, mul_one] at h

theorem kzK_lt_opow {s e : Ordinal.{0}} (hs : RxEK S (vbW S l) K s) (he : RxEK S (vbW S l) K e) (h : s < ω ^ e) :
    vbK S l s < ω ^ vbK S l e := by
  rw [← kzK_opow hl hX hKB he]; exact vbKK_mono hl hX hKB hs (kzE_opow hKB he) h

/-- **`κ(x + y) = κ x + κ y` on the domain of `κ`.** -/
theorem kzK_add : ∀ x, RxEK S (vbW S l) K x → ∀ y, RxEK S (vbW S l) K y →
    vbK S l (x + y) = vbK S l x + vbK S l y := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx y hy
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [zero_add, kzK_zero hl hX hKB, zero_add]
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [add_zero, kzK_zero hl hX hKB, add_zero]
  obtain ⟨e, s, n, hn1, hse, hxd, hxlt, -, heE, hsE, hsx⟩ := kzCnf hKB hx hx0
  obtain ⟨b, t, k, hk1, htb, hyd, hylt, hyle, hbE, htE, -⟩ := kzCnf hKB hy hy0
  have hKx : vbK S l x = ω ^ vbK S l e * n + vbK S l s :=
    (congrArg (vbK S l) hxd).trans (kzK_cnf hl hX hKB n hn1 heE hsE hse)
  have hKy : vbK S l y = ω ^ vbK S l b * k + vbK S l t :=
    (congrArg (vbK S l) hyd).trans (kzK_cnf hl hX hKB k hk1 hbE htE htb)
  have hk0 : (0 : Ordinal.{0}) < k := by exact_mod_cast hk1
  rcases lt_trichotomy b e with hbe | rfl | heb
  · -- `y < ω^e`
    have hye : y < ω ^ e := hylt.trans_le (opow_le_opow_right omega0_pos (Order.succ_le_of_lt hbe))
    have hsy : s + y < ω ^ e := isPrincipal_add_omega0_opow e hse hye
    have e1 : x + y = ω ^ e * n + (s + y) := by rw [hxd, add_assoc]
    rw [e1, kzK_cnf hl hX hKB n hn1 heE (kzE_add hKB hsE hy) hsy, IH s hsx hsE y hy, hKx, add_assoc]
  · -- same leading exponent
    have hab : s + ω ^ b * k = ω ^ b * k := Ordinal.add_absorp hse (Ordinal.le_mul_left _ hk0)
    have e1 : x + y = ω ^ b * ((n + k : ℕ) : Ordinal.{0}) + t := by
      rw [hxd, hyd, add_assoc, ← add_assoc s, hab, ← add_assoc, ← mul_add, Nat.cast_add]
    have hKs : vbK S l s < ω ^ vbK S l b := kzK_lt_opow hl hX hKB hsE hbE hse
    have hab' : vbK S l s + ω ^ vbK S l b * k = ω ^ vbK S l b * k :=
      Ordinal.add_absorp hKs (Ordinal.le_mul_left _ hk0)
    rw [e1, kzK_cnf hl hX hKB (n + k) (by omega) hbE htE htb, hKx, hKy, add_assoc, ← add_assoc (vbK S l s), hab',
      ← add_assoc, ← mul_add, Nat.cast_add]
  · -- `x < ω^b`
    have hxb : x < ω ^ b := hxlt.trans_le (opow_le_opow_right omega0_pos (Order.succ_le_of_lt heb))
    have e1 : x + y = y := Ordinal.add_absorp hxb hyle
    have hKxb : vbK S l x < ω ^ vbK S l b := kzK_lt_opow hl hX hKB hx hbE hxb
    have hKyb : ω ^ vbK S l b ≤ vbK S l y := by
      rw [hKy]; exact (Ordinal.le_mul_left _ hk0).trans le_self_add
    rw [e1, Ordinal.add_absorp hKxb hKyb]

/-- **`κ(ω^q·v) = ω^{κ q}·κ v`.** -/
theorem kzK_omul : ∀ v, RxEK S (vbW S l) K v → ∀ q, RxEK S (vbW S l) K q →
    vbK S l (ω ^ q * v) = ω ^ vbK S l q * vbK S l v := by
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv q hq
  rcases eq_or_ne v 0 with rfl | hv0
  · rw [mul_zero, kzK_zero hl hX hKB, mul_zero]
  obtain ⟨e, s, n, hn1, hse, hvd, -, -, heE, hsE, hsv⟩ := kzCnf hKB hv hv0
  have e1 : ω ^ q * v = ω ^ (q + e) * n + ω ^ q * s := by
    rw [hvd, mul_add, ← mul_assoc, ← opow_add]
  have hlt : ω ^ q * s < ω ^ (q + e) := by
    rw [opow_add]; exact (mul_lt_mul_iff_right₀ (opow_pos q omega0_pos)).2 hse
  have hKv : vbK S l v = ω ^ vbK S l e * n + vbK S l s :=
    (congrArg (vbK S l) hvd).trans (kzK_cnf hl hX hKB n hn1 heE hsE hse)
  rw [e1, kzK_cnf hl hX hKB n hn1 (kzE_add hKB hq heE) (kzE_omul hKB s hsE q hq) hlt, kzK_add hl hX hKB q hq e heE,
    IH s hsv hsE q hq, hKv, mul_add, ← mul_assoc, ← opow_add]

/-- **`T(x + y) = T x + T y` on `D`.** -/
theorem kzT_add {x y : Ordinal.{0}} (hx : VbDK S l K x) (hy : VbDK S l K y) :
    vbTK S l K (x + y) = vbTK S l K x + vbTK S l K y := by
  obtain ⟨hxE, hxK⟩ := vbTK_eq hl hX hKB hx
  obtain ⟨hyE, hyK⟩ := vbTK_eq hl hX hKB hy
  have h := kzK_add hl hX hKB _ hxE _ hyE
  rw [hxK, hyK] at h
  rw [← h]; exact vbTK_K hl hX hKB (kzE_add hKB hxE hyE)

/-- **`T(W^g·d + r) = Ω^{T g}·Θ d + T r`** for `g, r ∈ D` and a code `d < Ω₂` of `H_λ`. -/
theorem kzT_cnfW {g d r : Ordinal.{0}} (hg : VbDK S l K g) (hr : VbDK S l K r) (hdH : d ∈ cdHull S l)
    (hdW : d < Om (1 + 1)) :
    vbTK S l K (leWe g * d + r) = leOe (vbTK S l K g) * gxTh (upsilon l) (ldAtR S l) d + vbTK S l K r := by
  obtain ⟨hgE, hgK⟩ := vbTK_eq hl hX hKB hg
  obtain ⟨hrE, hrK⟩ := vbTK_eq hl hX hKB hr
  obtain ⟨hdE, hdK⟩ := vbCodeK hl hX hKB hdW hdH
  have hΩE : RxEK S (vbW S l) K (Om 1) := by
    have h : RxEK S (vbW S l) K (Om ((1 : ℕ) : Ordinal.{0})) :=
      ⟨RxN.om (rxN_nat 1), rxC_Om_nat _ _ 1, (Om_lt_Om.2 (natCast_lt_omega0 1)).trans_le hKB.ge⟩
    rwa [Nat.cast_one] at h
  have hKΩ : vbK S l (Om 1) = Om (1 + 1) := by
    have h : vbK S l (Om ((1 : ℕ) : Ordinal.{0})) = Om (((1 : ℕ) : Ordinal.{0}) + 1) := rxL_Om le_rfl
    rwa [Nat.cast_one] at h
  have h1 : ω ^ Om (1 : Ordinal.{0}) = Om 1 := Bt.Om1_opow
  have h2 : ω ^ Om (1 + 1 : Ordinal.{0}) = Om (1 + 1) := gg_SC_eps ldOm2_SC
  set yg := vbTK S l K g
  set yr := vbTK S l K r
  set yd := gxTh (upsilon l) (ldAtR S l) d
  have hqE : RxEK S (vbW S l) K (Om 1 * yg) := by
    have h := kzE_omul hKB yg hgE (Om 1) hΩE; rwa [h1] at h
  have hKq : vbK S l (Om 1 * yg) = Om (1 + 1) * g := by
    have h := kzK_omul hl hX hKB yg hgE (Om 1) hΩE
    rwa [h1, hKΩ, h2, hgK] at h
  have hYE : RxEK S (vbW S l) K (leOe yg * yd + yr) := kzE_add hKB (kzE_omul hKB yd hdE _ hqE) hrE
  have hKY : vbK S l (leOe yg * yd + yr) = leWe g * d + r := by
    show vbK S l (ω ^ (Om 1 * yg) * yd + yr) = ω ^ (Om (1 + 1) * g) * d + r
    rw [kzK_add hl hX hKB _ (kzE_omul hKB yd hdE _ hqE) _ hrE, kzK_omul hl hX hKB yd hdE _ hqE, hKq, hdK, hrK]
  rw [← hKY]; exact vbTK_K hl hX hKB hYE

/-- **`T_K(ω^e·n + s) = ω^{T_K e}·n + T_K s`** (`s < ω^e`, `n ≥ 1`). -/
theorem kzT_cnf {e s : Ordinal.{0}} (n : ℕ) (hn1 : 1 ≤ n) (he : VbDK S l K e) (hs : VbDK S l K s)
    (hse : s < ω ^ e) :
    vbTK S l K (ω ^ e * n + s) = ω ^ vbTK S l K e * n + vbTK S l K s := by
  obtain ⟨heE, heK⟩ := vbTK_eq hl hX hKB he
  obtain ⟨hsE, hsK⟩ := vbTK_eq hl hX hKB hs
  have hlt : vbTK S l K s < ω ^ vbTK S l K e :=
    (vbKK_lt_iff hl hX hKB hsE (kzE_opow hKB heE)).2 (by rw [hsK, kzK_opow hl hX hKB heE, heK]; exact hse)
  have hK : vbK S l (ω ^ vbTK S l K e * n + vbTK S l K s) = ω ^ e * n + s := by
    rw [kzK_cnf hl hX hKB n hn1 heE hsE hlt, heK, hsK]
  rw [← hK]; exact vbTK_K hl hX hKB (kzE_add hKB (kzE_mulNat hKB (kzE_opow hKB heE) n) hsE)

end Rst

end Googology.Trans.PoR.InaccPsi.R2.Kz
