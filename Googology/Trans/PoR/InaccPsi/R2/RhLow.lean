import Googology.Trans.PoR.InaccPsi.R2.RdWin
import Googology.Trans.PoR.InaccPsi.R2.LpLx
import Googology.Trans.PoR.InaccPsi.R2.LpTow
import Googology.Trans.PoR.InaccPsi.R2.RhBase

/-!
# (TC) and (EMB₂) below the new bound `U₃ = υ(ι(Γ_{Ω₁+2})) = P(Γ_{Ω₁+2})`

`L(ξ) = Nc.ncL S ξ`, `c_n = L(n+1)` (`Bc.bcC`), `B_n = Bc.bcB S n`, `Γ' = Γ_{Ω₁+2}` (`Lg.lgGam'`),
`U″ = υ(Λ⁺(lxZ))` (`Rd.rdZ_low`), `U₃ = υ(sup_n Λ⁺(lpSys lpZB n)) = υ(ι(Γ')) = P(Γ')` (`Lp.lpZ_famLoc`),
`U_T = υ(sup_k Λ⁺(lpTK k))` (the tower of `Lp.lpTowFam`, not yet located against `L(0)`).

* `rhG_low` (**every point below `U₃` has an `R₂^C`-reach below `L(0)`**, `Rb.rbFam_low` on the ladder
  `Lp.lpFam lpZB` with `P(Γ') < L(0)`), `rhG_gt` (`U″ < U₃`), `rhG_UPPER`, `rhG_LOWER`, `rhG_capV`, `rhG_nu`
  (UPPER, LOWER, the cap and **`L(ω) ≤ ν_C`** from their parts at `λ ≥ ι(Γ')`, with ENUM-REACH and CapV below `ι(Γ')`,
  `Lp.lpZEnum`, `Lp.lpZ_capV`);
* `rhRoadG` (**the road `Lp.lpZRoad` with TCrest and (EMB₂) asked only at left ends `x ≥ U₃`**), `rhRoadG_CL`
  ((TC) in place of TCrest, (CL) derived), `rhRoadG_rst` (**(TC) and (EMB₂) asked only at the left ends
  `x ∈ [U₃, L(n+2))` with no reach below `L(n+1)` that are restart points or lie in `[L(n+1), L(n+2))`**),
  `rhRoadG_rst2` (TCrest in place of (TC)), `rhRoadG_nu` (**(TC) asked only at the restart left ends in
  `[U₃, L(n+2))` and at `L(n+1)`, (EMB₂) dropped, under `L(ω+1) ≤ ν_C` and `Rh.RhLhTopG`**: a reduction);
* `rhTow_low` (**below `U_T` every point has a reach below `L(0)`, once `U_T ≤ L(0)`**), `rhTow_gt` (`U₃ < U_T`),
  `rhRoadTow` (the road `Lp.lpTowRoad` with TCrest and (EMB₂) asked only at `x ≥ U_T`, under `U_T ≤ L(0)`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Tq
  Googology.Trans.PoR.InaccPsi.R2.Rb Googology.Trans.PoR.InaccPsi.R2.Lx Googology.Trans.PoR.InaccPsi.R2.Lp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Rd

variable {S : InaccSeq.{0}}

/-- `υ(ι(Γ')) = P(Γ')`. -/
theorem rhG_ups : upsilon (iota S lgGam') = Pv S lgGam' := by
  have h := (lpZ_famLoc (S := S)).2.1
  rwa [(lpZ_famLoc (S := S)).1] at h

/-- **Every point below `U₃ = P(Γ_{Ω₁+2})` has an `R₂^C`-reach below `L(0)`.** -/
theorem rhG_low : TqLow S (Pv S lgGam') := by
  have h := rbFam_low (S := S) (lpFam lpZB)
    (by rw [(lpZ_famLoc (S := S)).2.1]; exact (lpZ_famLoc (S := S)).2.2.le)
  rwa [(lpZ_famLoc (S := S)).2.1] at h

/-- **`U″ < U₃`**: the new bound lies above the bound `U″ = υ(Λ⁺(lxZ))` of `Rd.rdZ_low`. -/
theorem rhG_gt (S : InaccSeq.{0}) : upsilon (xtB1 lxZ.sys) < Pv S lgGam' := by
  rw [← rhG_ups]
  obtain ⟨h1, -, h3, -⟩ := lpZ_fr_order (S := S) 0
  exact upsilon_normal.strictMono (h1.trans h3)

/-- **UPPER everywhere** from UPPER at `λ ≥ ι(Γ')`. -/
theorem rhG_UPPER (hU : ∀ l, CdRange S l → iota S lgGam' ≤ l → CdUpper S l) : CdUPPER S := fun l hr => by
  rcases lt_or_ge l (iota S lgGam') with h | h
  · exact (lpZEnum hr h).1
  · exact hU l hr h

/-- **LOWER everywhere** from LOWER at `λ ≥ ι(Γ')`. -/
theorem rhG_LOWER (hL : ∀ l, CdRange S l → iota S lgGam' ≤ l → CdLower S l) : CdLOWER S := fun l hr => by
  rcases lt_or_ge l (iota S lgGam') with h | h
  · exact (lpZEnum hr h).2
  · exact hL l hr h

/-- **The cap of the values everywhere** from the cap outside `ι(Γ')`. -/
theorem rhG_capV (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (iota S lgGam') l → CdCapV S l) :
    ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CdCapV S l := fun l hr hX => by
  rcases xtOut_or (iota S lgGam') l with h | ⟨hlB, hfix⟩
  · exact hV l hr hX h
  · exact lpZ_capV hr hlB hfix

/-- **`L(ω) ≤ ν_C`** from UPPER at `λ ≥ ι(Γ')` and the cap of the values outside `ι(Γ')`. -/
theorem rhG_nu (hU : ∀ l, CdRange S l → iota S lgGam' ≤ l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (iota S lgGam') l → CdCapV S l) :
    Nc.ncL S ω ≤ nuC :=
  cdLow_enum (rhG_UPPER hU) (rhG_capV hV)

/-- **The road `Lp.lpZRoad` with TCrest and (EMB₂) asked only at left ends `x ≥ U₃ = P(Γ')`.** -/
theorem rhRoadG (hU : ∀ l, CdRange S l → iota S lgGam' ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S lgGam' ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (iota S lgGam') l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : TqTCrestUp S (Pv S lgGam')) (hB2 : TqEMB2Rest S (Pv S lgGam')) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  lpZRoad hU hL hV hC hEQ (tqTCrest_of rhG_low hrest) (tqEMB2_of rhG_low hB2)

/-- **The road with (TC) and (EMB₂) asked only at left ends `x ≥ U₃` with no reach below `L(n+1)`**, (CL) derived. -/
theorem rhRoadG_CL (hU : ∀ l, CdRange S l → iota S lgGam' ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S lgGam' ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (iota S lgGam') l → CdCapV S l)
    (hEQ : CdEQ S) (htc : TqTCRest S (Pv S lgGam')) (hB2 : TqEMB2Rest S (Pv S lgGam')) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hTC : CdTC S := tqTC_of rhG_low htc
  have hE : CdEMB2 S := tqEMB2_of rhG_low hB2
  have hC : CdCL S := Cx.cxCL hTC hE
  exact ⟨hTC, hE, hC, (Cx.cxC1 hTC hE).1, rhRoadG hU hL hV hC hEQ (tqTCrestUp_of htc) hB2⟩

/-- **The road with (TC) and (EMB₂) asked only at the left ends `x ∈ [U₃, L(n+2))` with no reach below `L(n+1)` that
are restart points or lie in `[L(n+1), L(n+2))`**, (CL) derived. -/
theorem rhRoadG_rst (hU : ∀ l, CdRange S l → iota S lgGam' ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S lgGam' ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (iota S lgGam') l → CdCapV S l)
    (hEQ : CdEQ S) (htc : RbTCRst S (Pv S lgGam')) (hB2 : RbEMB2Rst S (Pv S lgGam')) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  have hν := rhG_nu hU hV
  rhRoadG_CL hU hL hV hEQ (rbTCRest_of hν htc) (rbEMB2Rest_of hν hB2)

/-- **The road with TCrest and (EMB₂) asked only at the left ends `x ∈ [U₃, L(n+2))` with no reach below `L(n+1)` that
are restart points or lie in `[L(n+1), L(n+2))`** (TCrest also not at the restarts of the range with
`r(λ) < L(n+2)`); (TC) from ENUM-REACH and EQ, (CL) derived. -/
theorem rhRoadG_rst2 (hU : ∀ l, CdRange S l → iota S lgGam' ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S lgGam' ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (iota S lgGam') l → CdCapV S l)
    (hEQ : CdEQ S) (hrest : RbTCrestRst S (Pv S lgGam')) (hB2 : RbEMB2Rst S (Pv S lgGam')) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hν := rhG_nu hU hV
  have hTCr : CdTCrest S := tqTCrest_of rhG_low (rbTCrestUp_of hν hrest)
  have hE : CdEMB2 S := tqEMB2_of rhG_low (rbEMB2Rest_of hν hB2)
  have hTC : CdTC S := cdTC_of_enum (rhG_UPPER hU) (rhG_LOWER hL) hEQ hTCr
  have hC : CdCL S := Cx.cxCL hTC hE
  exact ⟨hTC, hE, hC, (Cx.cxC1 hTC hE).1, lpZRoad hU hL hV hC hEQ hTCr hE⟩

/-- **The road `rhRoadG_rst` with (EMB₂) dropped and (TC) asked only at the restart left ends in `[U₃, L(n+2))` and
at `L(n+1)`**, under the extra hypotheses `L(ω+1) ≤ ν_C` and `Rh.RhLhTopG` (a reduction: `L(ω+1) ≤ ν_C` is one half
of the conclusion). -/
theorem rhRoadG_nu (hU : ∀ l, CdRange S l → iota S lgGam' ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S lgGam' ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (iota S lgGam') l → CdCapV S l)
    (hEQ : CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC) (hlh : RhLhTopG S) (htc : RdTCRst2 S (Pv S lgGam')) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rhRoadG_rst hU hL hV hEQ (rdTCRst_of hν (rdLhTopFix2_of_W (rhLhTopW_of_G hlh)) htc) (rdEMB2Rst_of hν _)

/-! ## The tower: below `U_T`, once `U_T ≤ L(0)` -/

/-- **Every point below `U_T = υ(sup_k Λ⁺(lpTK k))` has an `R₂^C`-reach below `L(0)`**, once `U_T ≤ L(0)`. -/
theorem rhTow_low (hloc : upsilon lpTowFam.famSup ≤ Nc.ncL S 0) : TqLow S (upsilon lpTowFam.famSup) :=
  rbFam_low lpTowFam hloc

/-- **`U₃ < U_T`.** -/
theorem rhTow_gt (S : InaccSeq.{0}) : Pv S lgGam' < upsilon lpTowFam.famSup := by
  rw [← rhG_ups]
  obtain ⟨h1, h2⟩ := lpTow_gt (S := S)
  exact upsilon_normal.strictMono (h1.trans h2)

/-- **The road `Lp.lpTowRoad` with TCrest and (EMB₂) asked only at left ends `x ≥ U_T`**, once `U_T ≤ L(0)`. -/
theorem rhRoadTow (hloc : upsilon lpTowFam.famSup ≤ Nc.ncL S 0)
    (hU : ∀ l, CdRange S l → lpTowFam.famSup ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → lpTowFam.famSup ≤ l → CdLower S l)
    (hT : ∀ k l, CdRange S l → iota S lgGam' ≤ l → l < xtB1 (lpTK k).sys → upsilon l = l →
      cdTheta S l (cdCode S l) = xtOrec (lpTK k).sys l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut lpTowFam.famSup l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : TqTCrestUp S (upsilon lpTowFam.famSup))
    (hB2 : TqEMB2Rest S (upsilon lpTowFam.famSup)) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  lpTowRoad hU hL hT hV hC hEQ (tqTCrest_of (rhTow_low hloc) hrest) (tqEMB2_of (rhTow_low hloc) hB2)

end Googology.Trans.PoR.InaccPsi.R2.Rh
