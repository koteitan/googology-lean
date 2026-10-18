import Googology.Trans.PoR.InaccPsi.R2.TpOpow
import Googology.Trans.PoR.InaccPsi.R2.TpPv
import Googology.Trans.PoR.InaccPsi.R2.TpEQ

/-!
# The road with the base change above `L(n+1)` reduced to the shift, the `R₁⁺`-reach at ε and EQ^all

`L(ξ) = Nc.ncL S ξ`, `B_n = Bc.bcB S n`, `T`: `L(ω) ≤₁ L(ω+1)`.

* `tpFront` (**`cxRoad_front` without `CxUpsRestTop` and `CxStdPairTop`**): both follow from
  `L(ω) ≤ ν_C` (from UPPER and CapV, `cdLow_enum`) and `L(ω+1) ≤ ν_C` (from (CL), `T`), by SKEL⁺ below
  `ν_C` (`tpUpsRest`, `tpStdPair`);
* `tpRoad` (**`cxRoad_rz` with `CxEQtop`, `CxTCtopOff`, `CxUpsRestTop`, `CxStdMoveTop`, `CxStdPairTop`
  replaced**): UPPER, `O(λ) ≤ c(λ)`, LOWER, CapV at the restarts of `cxRoad_rz`, `CxNamed`, the shift
  `TpShift`, the `R₁⁺`-reach transport at the ε-numbers off `υ` `TpLhEps`, and the reach equation
  `TpEQall` give EQ, (TC), (EMB₂), `T`, (CL), CROSS, (C1) and every conclusion of `cdRoad`;
* `tpRoad_steps`: the same with the three local steps `TpShiftSteps` in place of `TpShift`;
  `tpRoad_pv`: the same with (S1) `TpRstMove`, the step in the names `TpPvStep`, (S3) `TpLimMove`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cx

variable {S : InaccSeq.{0}}

/-- **`cxRoad_front` without `CxUpsRestTop` and `CxStdPairTop`.** -/
theorem tpFront (hU : CdUPPER S) (hL : CdLOWER S)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CdCapV S l)
    (hEQ : CxEQtop S) (htop : CxTCtopOff S) (hN : CxNamed S) (hmove : CxStdMoveTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hlow : Nc.ncL S ω ≤ nuC := cdLow_enum hU hV
  obtain ⟨-, hC, hT⟩ := cxNamed_out hN
  have hν : Nc.ncL S (ω + 1) ≤ nuC := cxNu_succ_of_CL hlow hC hT
  exact cxRoad_front hU hL hV hEQ htop (tpUpsRestTop hlow) hN hmove (tpStdPairTop hν)

/-- **The road with the base change above `L(n+1)` reduced** to the shift, the `R₁⁺`-reach transport
at the ε-numbers off `υ` and the reach equation EQ^all. -/
theorem tpRoad (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hN : CxNamed S) (hsh : TpShift S) (hlh : TpLhEps S) (hq : TpEQall S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hU' : CdUPPER S := Rz.rzUPPER_of_rest hU hO
  have hL' : CdLOWER S := Rz.rzLOWER_of_rest hL
  have hV' := Rz.rzCapV_of_rest hV
  have hlow : Nc.ncL S ω ≤ nuC := cdLow_enum hU' hV'
  obtain ⟨-, hC, hT⟩ := cxNamed_out hN
  have hν : Nc.ncL S (ω + 1) ≤ nuC := cxNu_succ_of_CL hlow hC hT
  exact cxRoad_named hU' hL' hV' (tpEQtop (tpRstMove_of_shift hsh) hq)
    (tpTCtop hV' hC hν hsh (tpLhMove_of_prin (tpLhPrin_of_eps hlh)))
    (tpUpsRest hlow) hN (tpStdMove hsh) (tpStdPair hν)

/-- **The same with the three local steps of the shift.** -/
theorem tpRoad_steps (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hN : CxNamed S) (hst : TpShiftSteps S) (hlh : TpLhEps S) (hq : TpEQall S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  tpRoad hU hO hL hV hN (tpShift_of_steps hst) hlh hq

/-- **The same with (S1), the step in the names, and (S3).** -/
theorem tpRoad_pv (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hN : CxNamed S) (h1 : TpRstMove S) (h2 : TpPvStep S) (h3 : TpLimMove S) (hlh : TpLhEps S)
    (hq : TpEQall S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  tpRoad hU hO hL hV hN (tpShift_of_pv h1 h2 h3) hlh hq

end Googology.Trans.PoR.InaccPsi.R2.Tp
