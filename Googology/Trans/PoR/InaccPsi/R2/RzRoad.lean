import Googology.Trans.PoR.InaccPsi.R2.RzLow
import Googology.Trans.PoR.InaccPsi.R2.CdNu

/-!
# The road to `ν_C = L(ω+1)` with the initial part of ENUM-REACH proved

The road theorems of `R2.CdNu` (`cdRoad`, `cdRoad_cap`, `cdLow`) with the hypotheses LOWER, UPPER, the cap of
the values, CAP-0 and CAP-1 replaced by what is left of them after `R2.RzLow`: they are now asked only at the
restarts `λ` of the range with `Λ_B⁺ ≤ λ` or `λ = υ_λ` (`Λ_B⁺ = rzLam`, the frontier of `R2.RzSpec`); UPPER at
the other restarts `λ < Λ_B⁺` of the range is the ordinal inequality `VzOrec(λ) ≤ c(λ)`.

* `rzLow` (**`L(ω) ≤ ν_C`** from CAP at the restarts of levels 1 and 2 below `L(ω)` with `Λ_B⁺ ≤ λ` or
  `λ = υ_λ`);
* `rzRoad` (**the whole road**): UPPER on the range, LOWER and the cap of the value at the restarts of the range
  with `Λ_B⁺ ≤ λ` or `λ = υ_λ`, (CL), EQ, TC at the other points, (EMB₂) give `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`,
  `L(ω) <₂ L(ω+1)`, (P), (Q), `lh(L(ω)) = lh(L(n+1)) = L(ω+1)`;
* `rzRoad_rest`: the same with UPPER asked only at those restarts, and `VzOrec(λ) ≤ c(λ)` at the others;
* `rzRoad_cap`: the same from CAP-0 and CAP-1 at those restarts, (CL), (TC), (EMB₂).

No new axiom, no new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- The restarts not covered by `R2.RzLow`. -/
def RzRest (l : Ordinal.{0}) : Prop := rzLam ≤ l ∨ upsilon l = l

/-- **`L(ω) ≤ ν_C`** from CAP at the restarts of levels 1 and 2 below `L(ω)` not covered by `R2.RzLow`. -/
theorem rzLow
    (h0 : ∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < cdMstar S → RzRest l → CdCapAt S l)
    (h1 : ∀ l, IsRestartIdx l → cdB0 ≤ l → cdMstar S ≤ upsilon l → upsilon l < Nc.ncL S ω →
      cdCode S l < Nc.ncPp S → RzRest l → CdCapAt S l) :
    Nc.ncL S ω ≤ nuC :=
  cdLow (rzCAP0_of_rest h0) (rzCAP1_of_rest h1)

/-- **The road with the initial part of ENUM-REACH proved.** -/
theorem rzRoad (hU : CdUPPER S) (hL : ∀ l, CdRange S l → RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → RzRest l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  cdRoad hU (rzLOWER_of_rest hL) (rzCapV_of_rest hV) hC hEQ hrest hB2

/-- **The road with UPPER asked only where `R2.RzLow` does not decide it.** -/
theorem rzRoad_rest (hU : ∀ l, CdRange S l → RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → RzRest l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rzRoad (rzUPPER_of_rest hU hO) hL hV hC hEQ hrest hB2

/-- **The road from the caps** at the restarts not covered by `R2.RzLow`, (CL), (TC), (EMB₂). -/
theorem rzRoad_cap
    (h0 : ∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < cdMstar S → RzRest l → CdCapAt S l)
    (h1 : ∀ l, IsRestartIdx l → cdB0 ≤ l → cdMstar S ≤ upsilon l → upsilon l < Nc.ncL S ω →
      cdCode S l < Nc.ncPp S → RzRest l → CdCapAt S l)
    (hC : CdCL S) (hTC : CdTC S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  cdRoad_cap (rzCAP0_of_rest h0) (rzCAP1_of_rest h1) hC hTC hB2

end Googology.Trans.PoR.InaccPsi.R2.Rz
