import Googology.Trans.PoR.InaccPsi.R2.RhLow
import Googology.Trans.PoR.InaccPsi.R2.GaTow

/-!
# (TC) and (EMB₂) below the bound `U_T = υ(ι(Γ_{Ω₁+ω})) = P(Γ_{Ω₁+ω})`, unconditionally

`L(ξ) = Nc.ncL S ξ`, `c_n = L(n+1)`, `Γ' = Γ_{Ω₁+2}` (`Lg.lgGam'`), `Γ_{Ω₁+ω}` (`Ga.gaW`), `U₃ = P(Γ')` (the bound of
`Rh.rhG_low`), `U_T = υ(sup_k Λ⁺(lpTK k)) = υ(ι(Γ_{Ω₁+ω})) = P(Γ_{Ω₁+ω})` (`Ga.gaTowSup`).

* `riTow_low` (**every point below `U_T = P(Γ_{Ω₁+ω})` has an `R₂^C`-reach below `L(0)`**: `Rh.rhTow_low` with its
  hypothesis `U_T ≤ L(0)` supplied by `Ga.gaTowSup`), `riTow_gt` (`U₃ < U_T`);
* `riTow_UPPER`, `riTow_LOWER`, `riTow_capV`, `riTow_nu` (UPPER, LOWER, the cap and **`L(ω) ≤ ν_C`** from their parts
  at `λ ≥ ι(Γ_{Ω₁+ω})`, with ENUM-REACH and CapV below `ι(Γ_{Ω₁+ω})`, `Ga.gaTowEnum`, `Ga.gaTowCapV`);
* `riRoadTow` (**the road `Ga.gaTowRoad` with TCrest and (EMB₂) asked only at left ends `x ≥ U_T`**), `riRoadTow_CL`
  ((TC) in place of TCrest, (CL) derived), `riRoadTow_rst` (**(TC) and (EMB₂) asked only at the left ends `x ∈ [U_T,
  L(n+2))` with no reach below `L(n+1)` that are restart points or lie in `[L(n+1), L(n+2))`**), `riRoadTow_rst2`
  (TCrest in place of (TC)), `riRoadTow_nu` (**(TC) asked only at the restart left ends in `[U_T, L(n+2))` and at
  `L(n+1)`, (EMB₂) dropped, under `L(ω+1) ≤ ν_C` and `Rh.RhLhTopG`**: a reduction).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ri

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Tq
  Googology.Trans.PoR.InaccPsi.R2.Rb Googology.Trans.PoR.InaccPsi.R2.Lx Googology.Trans.PoR.InaccPsi.R2.Lp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Rd
  Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Ga

variable {S : InaccSeq.{0}}

/-- **Every point below `U_T = P(Γ_{Ω₁+ω})` has an `R₂^C`-reach below `L(0)`**, unconditionally. -/
theorem riTow_low : TqLow S (Pv S gaW) := by
  have h := rhTow_low (S := S) (by rw [(gaTowSup (S := S)).2.1]; exact (gaTowSup (S := S)).2.2.le)
  rwa [(gaTowSup (S := S)).2.1] at h

/-- **`U₃ < U_T`**: the new bound `P(Γ_{Ω₁+ω})` lies above the bound `P(Γ_{Ω₁+2})` of `Rh.rhG_low`. -/
theorem riTow_gt (S : InaccSeq.{0}) : Pv S lgGam' < Pv S gaW := by
  have h := rhTow_gt S
  rwa [(gaTowSup (S := S)).2.1] at h

/-- **UPPER everywhere** from UPPER at `λ ≥ ι(Γ_{Ω₁+ω})`. -/
theorem riTow_UPPER (hU : ∀ l, CdRange S l → iota S gaW ≤ l → CdUpper S l) : CdUPPER S := fun l hr => by
  rcases lt_or_ge l (iota S gaW) with h | h
  · exact (gaTowEnum hr h).1
  · exact hU l hr h

/-- **LOWER everywhere** from LOWER at `λ ≥ ι(Γ_{Ω₁+ω})`. -/
theorem riTow_LOWER (hL : ∀ l, CdRange S l → iota S gaW ≤ l → CdLower S l) : CdLOWER S := fun l hr => by
  rcases lt_or_ge l (iota S gaW) with h | h
  · exact (gaTowEnum hr h).2
  · exact hL l hr h

/-- **The cap of the values everywhere** from the cap at `λ ≥ ι(Γ_{Ω₁+ω})`. -/
theorem riTow_capV (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gaW ≤ l → CdCapV S l) :
    ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CdCapV S l := fun l hr hX => by
  rcases lt_or_ge l (iota S gaW) with h | h
  · exact gaTowCapV hr h
  · exact hV l hr hX h

/-- **`L(ω) ≤ ν_C`** from UPPER and the cap of the values at `λ ≥ ι(Γ_{Ω₁+ω})`. -/
theorem riTow_nu (hU : ∀ l, CdRange S l → iota S gaW ≤ l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gaW ≤ l → CdCapV S l) :
    Nc.ncL S ω ≤ nuC :=
  cdLow_enum (riTow_UPPER hU) (riTow_capV hV)

/-- **The road `Ga.gaTowRoad` with TCrest and (EMB₂) asked only at left ends `x ≥ U_T = P(Γ_{Ω₁+ω})`.** -/
theorem riRoadTow (hU : ∀ l, CdRange S l → iota S gaW ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S gaW ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gaW ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : TqTCrestUp S (Pv S gaW)) (hB2 : TqEMB2Rest S (Pv S gaW)) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  gaTowRoad hU hL hV hC hEQ (tqTCrest_of riTow_low hrest) (tqEMB2_of riTow_low hB2)

/-- **The road with (TC) and (EMB₂) asked only at left ends `x ≥ U_T` with no reach below `L(n+1)`**, (CL)
derived. -/
theorem riRoadTow_CL (hU : ∀ l, CdRange S l → iota S gaW ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S gaW ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gaW ≤ l → CdCapV S l)
    (hEQ : CdEQ S) (htc : TqTCRest S (Pv S gaW)) (hB2 : TqEMB2Rest S (Pv S gaW)) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hTC : CdTC S := tqTC_of riTow_low htc
  have hE : CdEMB2 S := tqEMB2_of riTow_low hB2
  have hC : CdCL S := Cx.cxCL hTC hE
  exact ⟨hTC, hE, hC, (Cx.cxC1 hTC hE).1, riRoadTow hU hL hV hC hEQ (tqTCrestUp_of htc) hB2⟩

/-- **The road with (TC) and (EMB₂) asked only at the left ends `x ∈ [U_T, L(n+2))` with no reach below `L(n+1)`
that are restart points or lie in `[L(n+1), L(n+2))`**, (CL) derived. -/
theorem riRoadTow_rst (hU : ∀ l, CdRange S l → iota S gaW ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S gaW ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gaW ≤ l → CdCapV S l)
    (hEQ : CdEQ S) (htc : RbTCRst S (Pv S gaW)) (hB2 : RbEMB2Rst S (Pv S gaW)) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  have hν := riTow_nu hU hV
  riRoadTow_CL hU hL hV hEQ (rbTCRest_of hν htc) (rbEMB2Rest_of hν hB2)

/-- **The road with TCrest and (EMB₂) asked only at the left ends `x ∈ [U_T, L(n+2))` with no reach below `L(n+1)`
that are restart points or lie in `[L(n+1), L(n+2))`**; (TC) from ENUM-REACH and EQ, (CL) derived. -/
theorem riRoadTow_rst2 (hU : ∀ l, CdRange S l → iota S gaW ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S gaW ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gaW ≤ l → CdCapV S l)
    (hEQ : CdEQ S) (hrest : RbTCrestRst S (Pv S gaW)) (hB2 : RbEMB2Rst S (Pv S gaW)) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hν := riTow_nu hU hV
  have hTCr : CdTCrest S := tqTCrest_of riTow_low (rbTCrestUp_of hν hrest)
  have hE : CdEMB2 S := tqEMB2_of riTow_low (rbEMB2Rest_of hν hB2)
  have hTC : CdTC S := cdTC_of_enum (riTow_UPPER hU) (riTow_LOWER hL) hEQ hTCr
  have hC : CdCL S := Cx.cxCL hTC hE
  exact ⟨hTC, hE, hC, (Cx.cxC1 hTC hE).1, gaTowRoad hU hL hV hC hEQ hTCr hE⟩

/-- **The road `riRoadTow_rst` with (EMB₂) dropped and (TC) asked only at the restart left ends in `[U_T, L(n+2))`
and at `L(n+1)`**, under the extra hypotheses `L(ω+1) ≤ ν_C` and `Rh.RhLhTopG` (a reduction). -/
theorem riRoadTow_nu (hU : ∀ l, CdRange S l → iota S gaW ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S gaW ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gaW ≤ l → CdCapV S l)
    (hEQ : CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC) (hlh : RhLhTopG S) (htc : RdTCRst2 S (Pv S gaW)) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  riRoadTow_rst hU hL hV hEQ (rdTCRst_of hν (rdLhTopFix2_of_W (rhLhTopW_of_G hlh)) htc) (rdEMB2Rst_of hν _)

end Googology.Trans.PoR.InaccPsi.R2.Ri
