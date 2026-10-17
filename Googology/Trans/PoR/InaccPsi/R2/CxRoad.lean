import Googology.Trans.PoR.InaccPsi.R2.CxTop
import Googology.Trans.PoR.InaccPsi.R2.RzRoad

/-!
# The road to `ν_C = L(ω+1)` with (CL), CROSS, (C1) derived

`L(ξ) = Nc.ncL S ξ`, `T`: `L(ω) ≤₁ L(ω+1)` (`CxT`), `m* = L(0)`.

* `cxRoad` (**`cdRoad` without (CL)**): UPPER, LOWER, CapV below `L(ω)`, EQ, TCrest, (EMB₂) give `T`,
  (CL), CROSS, (C1) and every conclusion of `cdRoad` (`ν_C = L(ω+1)`, `L(ω) <₂ L(ω+1)`, (P), (Q),
  `lh(L(ω)) = lh(L(n+1)) = L(ω+1)`); `cxRoad_cap`: the same from CAP-0, CAP-1, (TC), (EMB₂);
* `CxNamed S` (**the crossing relations at the named restarts**): `m* ≤₁ L(1)`, (CL), `T`;
  `cxNamed_out`: with them `m* ≤₁ L(ω+1)`; `cxNamed_of_lower`: `CxNamed` from LOWER at `m*`, `L(n+1)`,
  `L(ω)` with predicted values `≥ L(1)`, `≥ L(n+2)`, `≥ L(ω+1)`;
* `cxRoad_named` (**the road with EQ, TC, EMB₂ reduced**): UPPER, LOWER, CapV below `L(ω)`, `CxEQtop`
  (EQ above `L(n+1)`), `CxTCtop` (TCrest on `(L(n+1), L(n+2))`), `CxUpsRest` (the non-restart
  `υ`-points below `L(n+1)`), `CxNamed`, `CxStdMove`, `CxStdPair` give (EQ), (TC), (EMB₂), (CL), `T`
  and every conclusion of `cdRoad`;
* `cxRoad_front`: the same with `CxTCtopOff`, `CxUpsRestTop`, `CxStdMoveTop`, `CxStdPairTop` (the
  hypotheses only at the points not settled by `R2.CxTop`);
* `cxRoad_rz`: `cxRoad_front` with LOWER and CapV asked only at the restarts `Rz.RzRest`
  (`Λ_B⁺ ≤ λ` or `υ_λ = λ`), and UPPER only there plus `O(λ) ≤ c(λ)` at the others
  (`Rz.rzUPPER_of_rest`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Cx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **The road without (CL)**: (CL), `T`, CROSS and (C1) follow from TC (`cdTC_of_enum`) and (EMB₂). -/
theorem cxRoad (hU : CdUPPER S) (hL : CdLOWER S)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CdCapV S l)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hTC := cdTC_of_enum hU hL hEQ hrest
  have hC := cxCL hTC hB2
  exact ⟨cxT hTC hB2, hC, cxCROSS_of_CL hC, cdC1_of_CL hC, cdRoad hU hL hV hC hEQ hrest hB2⟩

/-- **The road from the caps without (CL)**: CAP-0, CAP-1 below `L(ω)`, (TC) and (EMB₂). -/
theorem cxRoad_cap (h0 : CdCAP0 S) (h1 : CdCAP1 S (Nc.ncL S ω)) (hTC : CdTC S) (hB2 : CdEMB2 S) :
    CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hC := cxCL hTC hB2
  exact ⟨cxT hTC hB2, hC, cxCROSS_of_CL hC, cdC1_of_CL hC, cdRoad_cap h0 h1 hC hTC hB2⟩

/-- **The crossing relations at the named restarts**: `m* ≤₁ L(1)`, (CL) `L(n+1) ≤₁ L(n+2)` for every `n`,
and `T`: `L(ω) ≤₁ L(ω+1)`. -/
def CxNamed (S : InaccSeq.{0}) : Prop :=
  le1 (Nc.ncL S 0) (Nc.ncL S 1) ∧ CdCL S ∧ CxT S

/-- **The crossing relations give `m* ≤₁ L(ω+1)`.** -/
theorem cxNamed_out (h : CxNamed S) :
    le1 (Nc.ncL S 0) (Nc.ncL S (ω + 1)) ∧ CdCL S ∧ CxT S := by
  obtain ⟨h0, hC, hT⟩ := h
  have h1 : le1 (Nc.ncL S 1) (Nc.ncL S (ω + 1)) := by
    simpa using ((Pp.ppP_of_cross hC hT).2 0).2
  exact ⟨le1_trans h0 h1, hC, hT⟩

/-- **The crossing relations from LOWER at the named restarts**: LOWER at `m*` with `r(λ) ≥ L(1)`, at
every `L(n+1)` with `r(λ) ≥ L(n+2)`, and at `L(ω)` with `r(λ) ≥ L(ω+1)`.  (These restarts lie outside the
range of ENUM-REACH: their codes are `P'`, `P'`, `P'+1`.  At `L(ω)` the hypothesis can only hold if
`r(λ) ≤ L(ω+1)`, since (Q) excludes `L(ω) ≤₁ L(ω+1)+1`.) -/
theorem cxNamed_of_lower
    (h0 : ∃ l, upsilon l = Nc.ncL S 0 ∧ CdLower S l ∧ Nc.ncL S 1 ≤ cdR S l)
    (hn : ∀ n : ℕ, ∃ l, upsilon l = Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ∧ CdLower S l ∧
      Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) ≤ cdR S l)
    (hw : ∃ l, upsilon l = Nc.ncL S ω ∧ CdLower S l ∧ Nc.ncL S (ω + 1) ≤ cdR S l) :
    CxNamed S := by
  obtain ⟨l0, hl0, hL0, hr0⟩ := h0
  obtain ⟨lw, hlw, hLw, hrw⟩ := hw
  refine ⟨?_, cxCL_of_lower hn, cxT_of_lower hlw hLw hrw⟩
  have h1 : le1 (upsilon l0) (cdR S l0) := hL0
  rw [hl0] at h1
  exact le1_of_le_of_le1 (Pp.ppL_mono zero_le) hr0 h1

/-- **The road with EQ, TC and (EMB₂) reduced** to EQ above `L(n+1)`, TCrest on `(L(n+1), L(n+2))`, the
non-restart `υ`-points below `L(n+1)`, the crossing relations at the named restarts, and the standard
pairs. -/
theorem cxRoad_named (hU : CdUPPER S) (hL : CdLOWER S)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CdCapV S l)
    (hEQ : CxEQtop S) (htop : CxTCtop S) (hups : CxUpsRest S) (hN : CxNamed S)
    (hmove : CxStdMove S) (hstd : CxStdPair S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hlow : Nc.ncL S ω ≤ nuC := cdLow_enum hU hV
  obtain ⟨hm, hC, hT⟩ := cxNamed_out hN
  have hEQ' : CdEQ S := cxEQ_of_top hV hEQ
  have hrest : CdTCrest S := cxTCrest_of (cxTC_below hU hL hV hlow hC hT hm hups) hT hC htop
  have hB2 : CdEMB2 S := cxEMB2_of_CL hlow hC hT hmove hstd
  exact ⟨hEQ', cdTC_of_enum hU hL hEQ' hrest, hB2, hT, hC, cxCROSS_of_CL hC, cdC1_of_CL hC,
    cdRoad hU hL hV hC hEQ' hrest hB2⟩

/-- **The road with the hypotheses only where `R2.CxTop` does not settle them.** -/
theorem cxRoad_front (hU : CdUPPER S) (hL : CdLOWER S)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CdCapV S l)
    (hEQ : CxEQtop S) (htop : CxTCtopOff S) (hups : CxUpsRestTop S) (hN : CxNamed S)
    (hmove : CxStdMoveTop S) (hstd : CxStdPairTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  cxRoad_named hU hL hV hEQ (cxTCtop_of hV htop) (cxUpsRest_of_top hups) hN
    (cxStdMove_of_top hmove) (cxStdPair_of_top hstd)

/-- **The reduced road with the initial part of ENUM-REACH proved** (`R2.RzLow`): LOWER and CapV only at
the restarts `Rz.RzRest`; UPPER only there, plus `O(λ) ≤ c(λ)` at the restarts `λ < Λ_B⁺` with
`λ < υ_λ`. -/
theorem cxRoad_rz (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hEQ : CxEQtop S) (htop : CxTCtopOff S) (hups : CxUpsRestTop S) (hN : CxNamed S)
    (hmove : CxStdMoveTop S) (hstd : CxStdPairTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  cxRoad_front (Rz.rzUPPER_of_rest hU hO) (Rz.rzLOWER_of_rest hL) (Rz.rzCapV_of_rest hV) hEQ htop
    hups hN hmove hstd

end Googology.Trans.PoR.InaccPsi.R2.Cx
