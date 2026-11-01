import Googology.Trans.PoR.InaccPsi.R2.XrTop
import Googology.Trans.PoR.InaccPsi.R2.XrCof

/-!
# The first jump of `B_n`: `p = L(n+1)·2`

Notation as in `R2.XrTop`: `c_n = L(n+1)`, `B_n = Bc.bcB S n`, `ρ_λ = υ_λ`, `δ_λ = υ_{λ+ω+1}`,
`K_λ = Cd.cdK λ`, `k_λ = Cd.cdk λ`.

`B_n` fixes `[0, c_n)` and sends `c_n` to `L(ω)`, so it jumps at `c_n`, and the first jump above `c_n` is at
`p = c_n·2`:

* `xwFirst_val`: `B_n(c_n·2) = L(ω)·2`;
* `xwFirst_below`: every `q < c_n·2` has `B_n q < L(ω) + c_n`; so the jump gap is `[L(ω) + c_n, L(ω)·2)`,
  nonempty (`xwFirst_gap_ne`);
* `xwFirst_noIndec`: the gap contains no indecomposable ordinal, hence no `υ`-point;
* `xwFirst_noK`: for every window `(n, λ, λ')`, no point of `K_{λ'}` lies below `L(ω)·2` (`ρ_{λ'} = B_n ρ_λ`,
  `ρ_λ` is strongly critical above `c_n`): the closed points of `λ'` are NOT unbounded in this gap;
* `xwFirst_far`: but `c_n·2 < δ_λ·ω` for every window, so `p = c_n·2` is never a far index: the leaf
  `Xr.XrKCofGap` asks nothing there (`xwFirst_kcof_vac`);
* `xwFirst_noChain`: every chain point (`Xr.XrPt`) is `> c_n·2`, so the cofinality hypothesis of `Xr.XrJump`
  fails at `s = c_n·2` (`xwFirst_jump_vac`).

No new axiom; no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- `y < y·ω` for `0 < y`. -/
theorem xw_lt_mulw {y : Ordinal.{0}} (hy : 0 < y) : y < y * ω := by
  calc y = y * 1 := (mul_one y).symm
    _ < y * ω := (mul_lt_mul_iff_right₀ hy).2 one_lt_omega0

/-- `a·2 = a + a` for ordinals. -/
theorem xw_mul2 (a : Ordinal.{0}) : a * 2 = a + a := by
  rw [show (2 : Ordinal.{0}) = 1 + 1 from one_add_one_eq_two.symm, mul_add, mul_one]

/-- `0 < c_n`. -/
theorem xw_c_pos (n : ℕ) : 0 < Bc.bcC S n :=
  lt_of_lt_of_le omega0_pos (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)).le

/-- `L(ω+1) < Ω₁` (no hypothesis). -/
theorem xwL_lt_Om1 : Nc.ncL S (ω + 1) < Om1 := by
  rw [Br.Om1_eq, Lw.lw_L_eq]; exact Nm.Pv_lt_Om1 S _

/-- A range restart has an indecomposable (strongly critical) `ρ_λ`. -/
theorem xwUps_indec {l : Ordinal.{0}} (hl : CdRange S l) : Indec (upsilon l) := by
  have hl0 : l ≠ 0 := by
    have h0 : (0 : Ordinal.{0}) < cdB0 := lt_of_lt_of_le (mul_pos omega0_pos omega0_pos) le_add_self
    exact (h0.trans_le hl.2.1).ne'
  have hX : upsilon l < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq]; exact hl.2.2.1
  have hSC := Mv.mvUps_SC (S := S) hl0 hX
  exact indec_iff.2 ⟨(lt_of_lt_of_le omega0_pos (Lw.lw_omega_lt_SC hSC).le).ne', SC.isPrincipal hSC⟩

/-- An indecomposable ordinal above `c_n` is above `c_n·2`. -/
theorem xw_indec_gt2 {n : ℕ} {x : Ordinal.{0}} (hx : Indec x) (h : Bc.bcC S n < x) :
    Bc.bcC S n * 2 < x := by
  rw [xw_mul2]; exact (indec_iff.1 hx).2 h h

/-! ## The first jump -/

/-- **`B_n(c_n·2) = L(ω)·2`.** -/
theorem xwFirst_val (n : ℕ) : Bc.bcB S n (Bc.bcC S n * 2) = Nc.ncL S ω * 2 := by
  have h3 : Bc.bcB S n (Bc.bcC S n) = Nc.ncL S ω := Bc.bcB_base n
  rw [xw_mul2, xw_mul2, Bc.bcB_add (Bc.bcC_lt S n) (Bc.bcC_lt S n), h3]

/-- **Below `c_n·2`, `B_n` stays below `L(ω) + c_n`.** -/
theorem xwFirst_below (n : ℕ) : ∀ q < Bc.bcC S n * 2, Bc.bcB S n q < Nc.ncL S ω + Bc.bcC S n := by
  intro q hq
  rcases lt_or_ge q (Bc.bcC S n) with hqc | hqc
  · rw [Bc.bcB_fixN n q hqc]; exact hqc.trans_le le_add_self
  · obtain ⟨r, rfl⟩ := exists_add_of_le hqc
    rw [xw_mul2] at hq
    have hr : r < Bc.bcC S n := (add_lt_add_iff_left _).1 hq
    have h3 : Bc.bcB S n (Bc.bcC S n) = Nc.ncL S ω := Bc.bcB_base n
    rw [Bc.bcB_add (Bc.bcC_lt S n) (hr.trans (Bc.bcC_lt S n)), h3, Bc.bcB_fixN n r hr]
    exact (add_lt_add_iff_left _).2 hr

/-- The first gap `[L(ω) + c_n, L(ω)·2)` is nonempty. -/
theorem xwFirst_gap_ne (n : ℕ) : Nc.ncL S ω + Bc.bcC S n < Nc.ncL S ω * 2 := by
  rw [xw_mul2]; exact (add_lt_add_iff_left _).2 (Bc.bcC_lt S n)

/-- **No indecomposable ordinal (so no `υ`-point) lies in the first gap.** -/
theorem xwFirst_noIndec (n : ℕ) {x : Ordinal.{0}} (h1 : Nc.ncL S ω + Bc.bcC S n ≤ x)
    (h2 : x < Nc.ncL S ω * 2) : ¬ Indec x := by
  intro hx
  have hLx : Nc.ncL S ω < x := (lt_add_of_pos_right _ (xw_c_pos n)).trans_le h1
  have : Nc.ncL S ω + Nc.ncL S ω < x := (indec_iff.1 hx).2 hLx hLx
  rw [xw_mul2] at h2
  exact lt_asymm this h2

/-- **`c_n·2 < δ_λ·ω` at every window**: `p = c_n·2` is never a far index. -/
theorem xwFirst_far {n : ℕ} {l l' : Ordinal.{0}} (hW : R2Skel.SkEX.SkWin S n l l') :
    Bc.bcC S n * 2 < cdDelta l * ω := by
  obtain ⟨-, h1, -, -, -, -⟩ := hW
  have hcδ : Bc.bcC S n ≤ cdDelta l := (h1.trans (cdRho_lt_delta l)).le
  calc Bc.bcC S n * 2 < Bc.bcC S n * ω :=
        (mul_lt_mul_iff_right₀ (xw_c_pos n)).2 (by exact_mod_cast natCast_lt_omega0 2)
    _ ≤ cdDelta l * ω := mul_le_mul_left hcδ ω

/-- **No closed point of an image window lies below `L(ω)·2`**: the closed points of `λ'` are not unbounded in the
first gap. -/
theorem xwFirst_noK {n : ℕ} {l l' : Ordinal.{0}} (hW : R2Skel.SkEX.SkWin S n l l') :
    ∀ y ∈ cdK l', Nc.ncL S ω * 2 < y := by
  obtain ⟨hR, h1, hr, -, hB, -⟩ := hW
  have hρ2 : Bc.bcC S n * 2 < upsilon l := xw_indec_gt2 (xwUps_indec hR) h1
  have hρL : upsilon l < Nc.ncL S ω :=
    ((cdRho_lt_delta l).trans ((cdR_ge S l).trans_lt hr)).trans (Bc.bcC_lt S (n + 1))
  have hB2 : Nc.ncL S ω * 2 < upsilon l' := by
    rw [← xwFirst_val n, ← hB]; exact (Bc.bcB_lt_iff (hρ2.trans hρL) hρL).2 hρ2
  intro y hy
  have hδy : cdDelta l' ≤ y := by rcases hy with h | h; exact h.1; exact h.2
  exact hB2.trans ((cdRho_lt_delta l').trans_le hδy)

/-- **The leaf `Xr.XrKCofGap` asks nothing at `p = c_n·2`**: its hypothesis `δ_λ·ω ≤ p` fails. -/
theorem xwFirst_kcof_vac {n : ℕ} {l l' : Ordinal.{0}} (hW : R2Skel.SkEX.SkWin S n l l') :
    ¬ cdDelta l * ω ≤ Bc.bcC S n * 2 :=
  not_le.2 (xwFirst_far hW)

/-- **Every chain point lies above `c_n·2`.** -/
theorem xwFirst_noChain {n : ℕ} {R R' x : Ordinal.{0}} (hx : Xr.XrPt S n R R' x) : Bc.bcC S n * 2 < x := by
  obtain ⟨μ, -, hμ, h1, rfl, -⟩ := hx
  exact xw_indec_gt2 (xwUps_indec hμ) h1

/-- **The leaf `Xr.XrJump` asks nothing at `s = c_n·2`**: no chain point is cofinal below it. -/
theorem xwFirst_jump_vac {n : ℕ} {R R' : Ordinal.{0}} :
    ¬ ∀ x < Bc.bcC S n * 2, ∃ y, x < y ∧ y < Bc.bcC S n * 2 ∧ Xr.XrPt S n R R' y := by
  intro h
  have hc2 : Bc.bcC S n < Bc.bcC S n * 2 := by
    rw [xw_mul2]; exact lt_add_of_pos_right _ (xw_c_pos n)
  obtain ⟨y, -, hy2, hy⟩ := h _ hc2
  exact lt_asymm (xwFirst_noChain hy) hy2

/-- **REFUTE-FIRST record at the first jump**, all in one statement. -/
theorem xwFirst (n : ℕ) :
    Bc.bcB S n (Bc.bcC S n * 2) = Nc.ncL S ω * 2 ∧
    (∀ q < Bc.bcC S n * 2, Bc.bcB S n q < Nc.ncL S ω + Bc.bcC S n) ∧
    Nc.ncL S ω + Bc.bcC S n < Nc.ncL S ω * 2 ∧
    (∀ x, Nc.ncL S ω + Bc.bcC S n ≤ x → x < Nc.ncL S ω * 2 → ¬ Indec x) ∧
    (∀ l l', R2Skel.SkEX.SkWin S n l l' →
      Bc.bcC S n * 2 < cdDelta l * ω ∧ ∀ y ∈ cdK l', Nc.ncL S ω * 2 < y) ∧
    (∀ R R' : Ordinal.{0}, ¬ ∀ x < Bc.bcC S n * 2, ∃ y, x < y ∧ y < Bc.bcC S n * 2 ∧ Xr.XrPt S n R R' y) :=
  ⟨xwFirst_val n, xwFirst_below n, xwFirst_gap_ne n, fun _ h1 h2 => xwFirst_noIndec n h1 h2,
    fun _ _ hW => ⟨xwFirst_far hW, xwFirst_noK hW⟩, fun _ _ => xwFirst_jump_vac⟩

end Googology.Trans.PoR.InaccPsi.R2.Xw
