import Googology.Trans.PoR.InaccPsi.R2.WhLeaf

/-!
# WhRefute: THE SHAPE LEAF WITH NATURAL-NUMBER EXPONENTS IS FALSE

In the shapes `P + Ω₁^{e+1}`, `P + Ω₁^e` (`e` a limit) and `P + Ω₁^e·c` written without a type for `e`, the
exponent elaborates as a natural number (`Monoid.npow`).  With `e : ℕ` the five shapes do not cover the level
`Ω₁^ω` (`Ω₁ ≤ Ω₁^ω`, `Ω₁ ∣ Ω₁^ω`, `Ω₁^ω < ε_{Ω₁+1}`): `Ω₁^ω` is additively principal, so it is no sum `P + X` with
`0 < X < Ω₁^ω`, and no natural number is a successor limit.  So the shape statement must ask `e : Ordinal`
(`Wh.whShape` proves that version).

* `wh_no_split` (an additively principal `W` is no `P + X`, `0 < X < W`), `whW` (`Ω₁^ω`), `whW_lev`;
* `whShapeNat_false` (**THE SHAPE STATEMENT WITH `e : ℕ` IS FALSE**, witness `Ω₁^ω`).

No new axiom.  New definition: `whW`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gl

/-- **An additively principal `W` is no sum `P + X` with `0 < X < W`.** -/
theorem wh_no_split {W P X : Ordinal.{0}} (hW : IsPrincipal (· + ·) W) (hX0 : 0 < X) (hXW : X < W) :
    P + X ≠ W := by
  intro h
  rcases lt_or_ge P W with hP | hP
  · exact (hW hP hXW).ne h
  · exact (hP.trans_lt (lt_add_of_pos_right P hX0)).ne' h

/-- The witness `Ω₁^ω`. -/
noncomputable def whW : Ordinal.{0} := Om1 ^ (ω : Ordinal.{0})

theorem whW_principal : IsPrincipal (· + ·) whW := by
  unfold whW; rw [Om1_pow_eq]; exact isPrincipal_add_omega0_opow _

theorem wh_npow_eq (n : ℕ) : Om1 ^ n = Om1 ^ ((n : ℕ) : Ordinal.{0}) := (opow_natCast Om1 n).symm

theorem wh_npow_lt_W (n : ℕ) : Om1 ^ n < whW := by
  rw [wh_npow_eq]; exact (opow_lt_opow_iff_right wh_one_lt_Om1).2 (natCast_lt_omega0 n)

theorem wh_npow_pos (n : ℕ) : 0 < Om1 ^ n := by rw [wh_npow_eq]; exact opow_pos _ wh_Om1_pos

/-- **`Ω₁^ω` is a level**: `Ω₁ ≤ Ω₁^ω`, `Ω₁ ∣ Ω₁^ω`, `Ω₁^ω < ε_{Ω₁+1}`. -/
theorem whW_lev : Om1 ≤ whW ∧ Om1 ∣ whW ∧ whW < gfE := by
  refine ⟨?_, ?_, Om1_pow_lt_eW ((omega0_lt_inE gl_Om1_E).trans Om1_lt_eW)⟩
  · calc Om1 = Om1 ^ (1 : Ordinal.{0}) := (opow_one _).symm
    _ ≤ whW := opow_le_opow_right wh_Om1_pos one_lt_omega0.le
  · have := opow_dvd_opow Om1 (one_lt_omega0.le : (1 : Ordinal.{0}) ≤ ω)
    rwa [opow_one] at this

/-- **THE SHAPE STATEMENT WITH NATURAL-NUMBER EXPONENTS IS FALSE** (witness `Ω₁^ω`).  This is the statement of the
skeleton leaf `skShape` as it elaborates (`e : ℕ` in the last three shapes). -/
theorem whShapeNat_false : ¬ ∀ ℓ : Ordinal.{0}, (Om1 ≤ ℓ ∧ Om1 ∣ ℓ ∧ ℓ < gfE) →
    ℓ = Om1 ∨ (∃ ℓ', (Om1 ≤ ℓ' ∧ Om1 ∣ ℓ' ∧ ℓ' < gfE) ∧ ℓ = ℓ' + Om1) ∨
      (∃ (P : Ordinal.{0}) (e : ℕ), 1 ≤ e ∧ Om1 ^ (e + 1) ∣ P ∧ ℓ = P + Om1 ^ (e + 1)) ∨
      (∃ (P : Ordinal.{0}) (e : ℕ), IsSuccLimit e ∧ Om1 ^ e ∣ P ∧ ℓ = P + Om1 ^ e) ∨
      (∃ (P : Ordinal.{0}) (e : ℕ) (c : Ordinal.{0}), 1 ≤ e ∧ IsSuccLimit c ∧ c < Om1 ∧ Om1 ^ (e + 1) ∣ P ∧
        ℓ = P + Om1 ^ e * c) := by
  intro h
  have hP := whW_principal
  have hOW : Om1 < whW := by
    have := wh_npow_lt_W 1; rwa [pow_one] at this
  rcases h whW whW_lev with h1 | ⟨ℓ', _, h2⟩ | ⟨P, e, _, _, h3⟩ | ⟨P, e, h4, _, _⟩ | ⟨P, e, c, _, hc, hcO, _, h5⟩
  · exact hOW.ne' h1
  · exact wh_no_split hP wh_Om1_pos hOW h2.symm
  · exact wh_no_split hP (wh_npow_pos _) (wh_npow_lt_W _) h3.symm
  · exact Order.not_isSuccLimit (a := e) h4
  · have hc0 : 0 < c := hc.bot_lt
    have hlt : Om1 ^ e * c < whW := by
      calc Om1 ^ e * c < Om1 ^ e * Om1 := mul_lt_mul_of_pos_left hcO (wh_npow_pos e)
      _ = Om1 ^ (e + 1) := (pow_succ _ _).symm
      _ < whW := wh_npow_lt_W _
    exact wh_no_split hP (mul_pos (wh_npow_pos e) hc0) hlt h5.symm

end Googology.Trans.PoR.InaccPsi.R2.Wh
