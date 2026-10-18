import Googology.Trans.PoR.InaccPsi.R2.CvNamed
import Googology.Trans.PoR.InaccPsi.R2.LhSk

/-!
# The clause `≤₁` of a realizer map, reduced to reaches

`le1` is `≤₁` of `R₂^C`, `le1R` that of `R₁⁺`, `r(λ) = cdR S λ`.  The realizer maps of `Rl.RlReal`
must keep `≤₁` on their domain.  Three reductions of that clause for one pair `y < y'`:

* `rlD1_of_reach` (**at a point with an exact reach**): if `r` is the exact reach of `y`, `r'` that of
  `D(y)`, `D(y) ≤ D(y')`, and `y' ≤ r → D(y') ≤ r'`, then `y ≤₁ y' → D(y) ≤₁ D(y')`;
* `rlD1_rst` (**at a restart**): `y = ρ_λ` with UPPER at `λ`, `D(y) = ρ_{λ'}` with LOWER at `λ'`, and
  `y' ≤ r(λ) → D(y') ≤ r(λ')` (the EQ-type clause);
* `rlD1_nonups` (**at a non-`υ`-point below `ν_C`**): `≤₁` is `≤₁` of `R₁⁺` at both ends
  (`Lh.lhSk_le1`), so the clause is `y ≤₁ y'` in `R₁⁺` `→ D(y) ≤₁ D(y')` in `R₁⁺`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rl

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

/-- **The clause `≤₁` at a point with an exact reach.** -/
theorem rlD1_of_reach {D : Ordinal.{0} → Ordinal.{0}} {y y' r r' : Ordinal.{0}}
    (hr : IsReach R2C y r) (hr' : IsReach R2C (D y) r') (hmono : D y ≤ D y')
    (hb : y' ≤ r → D y' ≤ r') (h : le1 y y') : le1 (D y) (D y') :=
  le1_of_le_of_le1 hmono (hb (hr.2 y' h)) hr'.1

variable {S : InaccSeq.{0}}

/-- **The clause `≤₁` at a restart**: UPPER at `λ`, LOWER at `λ'`, `D(ρ_λ) = ρ_{λ'}`. -/
theorem rlD1_rst {D : Ordinal.{0} → Ordinal.{0}} {l l' y' : Ordinal.{0}}
    (hU : CdUpper S l) (hL : CdLower S l') (hD : D (upsilon l) = upsilon l')
    (hmono : D (upsilon l) ≤ D y') (hb : y' ≤ cdR S l → D y' ≤ cdR S l')
    (h : le1 (upsilon l) y') : le1 (D (upsilon l)) (D y') := by
  have hy' : y' ≤ cdR S l := cdUpper_iff.1 hU y' h
  have hl : le1 (upsilon l') (cdR S l') := hL
  rw [hD] at hmono ⊢
  exact le1_of_le_of_le1 hmono (hb hy') hl

/-- **The clause `≤₁` at a non-`υ`-point below `ν_C`** reduces to `R₁⁺`. -/
theorem rlD1_nonups {D : Ordinal.{0} → Ordinal.{0}} {y y' : Ordinal.{0}}
    (hy : y < nuC) (hU : ¬ UpsPt y) (hDy : D y < nuC) (hDU : ¬ UpsPt (D y))
    (h1R : le1R y y' → le1R (D y) (D y')) (h : le1 y y') : le1 (D y) (D y') :=
  (Lh.lhSk_le1 hDy hDU _).2 (h1R ((Lh.lhSk_le1 hy hU _).1 h))

end Googology.Trans.PoR.InaccPsi.R2.Rl
