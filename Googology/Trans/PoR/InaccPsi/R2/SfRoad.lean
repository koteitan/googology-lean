import Googology.Trans.PoR.InaccPsi.R2.SfRst

/-!
# The road with the shift proved

`L(ξ) = Nc.ncL S ξ`, `B_n = Bc.bcB S n`; ROAD is the conclusion of `Tp.tpRoad` (EQ, (TC), (EMB₂), `T`,
(CL), CROSS, (C1), `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), and the reaches
`lh(L(ω)) = lh(L(n+1)) = L(ω+1)`).

* `sfRoad` (**`Tp.tpRoad` without `TpShift`**, which `Sf.sfShiftAll` proves): UPPER, `O(λ) ≤ c(λ)`,
  LOWER and CapV at the restarts of `Tp.tpRoad`, `CxNamed`, the `R₁⁺`-reach transport at the
  ε-numbers off `υ` (`TpLhEps`) and the reach equation (`TpEQall`) give ROAD.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cx

variable {S : InaccSeq.{0}}

/-- **The road with the shift proved.** -/
theorem sfRoad (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hN : CxNamed S) (hlh : Tp.TpLhEps S) (hq : Tp.TpEQall S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  Tp.tpRoad hU hO hL hV hN sfShiftAll hlh hq

end Googology.Trans.PoR.InaccPsi.R2.Sf
