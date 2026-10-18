import Googology.Trans.PoR.InaccPsi.R2.MvLong

/-!
# The road without `SfKMove`, with the long codes needed only under `L(ω+1) ≤ ν_C`

`L(ξ) = Nc.ncL S ξ`, `B_n = Bc.bcB S n`; ROAD is the conclusion of `Tp.tpRoad` (EQ, (TC), (EMB₂), `T`,
(CL), CROSS, (C1), `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), and the reaches
`lh(L(ω)) = lh(L(n+1)) = L(ω+1)`).

Inside `Tp.tpRoad` the hypotheses UPPER, CapV and `CxNamed` already give `L(ω) ≤ ν_C` (`Cd.cdLow_enum`) and
then `L(ω+1) ≤ ν_C` (`Cx.cxNu_succ_of_CL`) before the reach equation is used; so the reach equation is only
needed under `L(ω+1) ≤ ν_C`, where `Mv.mvKMove` proves its short-code half.

* `mvNu` (**`L(ω+1) ≤ ν_C` from the hypotheses of the road**: UPPER, `O ≤ c`, CapV, `CxNamed`);
* `mvRoad`: UPPER, `O(λ) ≤ c(λ)`, LOWER, CapV (as in `Sf.sfRoad_min`), `CxNamed`, `SfLhTMove`, and
  `L(ω+1) ≤ ν_C → SfEQlong` give ROAD (**`SfKMove` is no longer a hypothesis**);
* `mvRoad_th`: the same with `L(ω+1) ≤ ν_C → SfEQlong` replaced by `MvThLong` (the reading of the long codes
  below `δ_λ`) and `L(ω+1) ≤ ν_C → MvEQbig`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Mv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cx

variable {S : InaccSeq.{0}}

/-- **`L(ω+1) ≤ ν_C` from the hypotheses of the road.** -/
theorem mvNu (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hN : CxNamed S) : Nc.ncL S (ω + 1) ≤ nuC := by
  have hU' : CdUPPER S := Rz.rzUPPER_of_rest hU hO
  have hlow : Nc.ncL S ω ≤ nuC := cdLow_enum hU' (Rz.rzCapV_of_rest hV)
  obtain ⟨-, hC, hT⟩ := cxNamed_out hN
  exact cxNu_succ_of_CL hlow hC hT

/-- **The road without `SfKMove`.** -/
theorem mvRoad (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hN : CxNamed S) (hlh : Sf.SfLhTMove S)
    (hlong : Nc.ncL S (ω + 1) ≤ nuC → Sf.SfEQlong S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hν := mvNu hU hO hV hN
  exact Sf.sfRoad_min hU hO hL hV hN hlh (mvKMove hν) (hlong hν)

/-- **The road with the long codes split at `δ_λ`.** -/
theorem mvRoad_th (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hN : CxNamed S) (hlh : Sf.SfLhTMove S) (hth : MvThLong S)
    (hbig : Nc.ncL S (ω + 1) ≤ nuC → MvEQbig S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  mvRoad hU hO hL hV hN hlh fun hν => mvEQlong hν hth (hbig hν)

end Googology.Trans.PoR.InaccPsi.R2.Mv
