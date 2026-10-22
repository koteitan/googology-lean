import Googology.Trans.PoR.InaccPsi.R2.RiRoad
import Googology.Trans.PoR.InaccPsi.R2.GbWLoc

/-!
# (TC) and (EMB₂) below the bound `U_G = υ(ι(Γ_{Ω₁+ω·2})) = P(Γ_{Ω₁+ω·2})`, unconditionally

`L(ξ) = Nc.ncL S ξ`, `c_n = L(n+1)`, `Γ_{Ω₁+ω}` (`Ga.gaW`), `Γ_{Ω₁+ω·2}` (`Gb.gbV`), `U_T = P(Γ_{Ω₁+ω})` (the bound
of `Ri.riTow_low`), `U_G = υ(sup_k Λ⁺(gbTK k)) = υ(ι(Γ_{Ω₁+ω·2})) = P(Γ_{Ω₁+ω·2})` (`Gb.gbTowSup`).

* `rjTow_low` (**every point below `U_G = P(Γ_{Ω₁+ω·2})` has an `R₂^C`-reach below `L(0)`**: `Rb.rbFam_low` on the
  second tower `Gb.gbTowFam`, with `U_G < L(0)` from `Gb.gbTowSup`), `rjTow_gt` (`U_T < U_G`);
* `rjTow_UPPER`, `rjTow_LOWER`, `rjTow_capV`, `rjTow_nu` (UPPER, LOWER, the cap and **`L(ω) ≤ ν_C`** from their parts
  at `λ ≥ ι(Γ_{Ω₁+ω·2})`, with ENUM-REACH and CapV below `ι(Γ_{Ω₁+ω·2})`, `Gb.gbTowEnum`, `Gb.gbTowCapV`);
* `rjRoadTow` (**the road `Gb.gbTowRoadL` with TCrest and (EMB₂) asked only at left ends `x ≥ U_G`**),
  `rjRoadTow_CL` ((TC) in place of TCrest, (CL) derived), `rjRoadTow_rst` (**(TC) and (EMB₂) asked only at the left
  ends `x ∈ [U_G, L(n+2))` with no reach below `L(n+1)` that are restart points or lie in `[L(n+1), L(n+2))`**),
  `rjRoadTow_rst2` (TCrest in place of (TC)), `rjRoadTow_nuH` (**(TC) asked only at the restart left ends in
  `[U_G, L(n+2))` and at `L(n+1)`, (EMB₂) dropped, under `L(ω+1) ≤ ν_C` and `Ri.RiLhTopH`**: a reduction);
* `rjTC_L_iff` (**given `T` (`L(ω) ≤₁ L(ω+1)`), (TC) at the named left end `x = L(n+1)` is `L(n+1) ≤₁ L(n+2)`**,
  i.e. the `n`-th clause of (CL)).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Tq
  Googology.Trans.PoR.InaccPsi.R2.Rb Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gb

variable {S : InaccSeq.{0}}

/-- **Every point below `U_G = P(Γ_{Ω₁+ω·2})` has an `R₂^C`-reach below `L(0)`**, unconditionally. -/
theorem rjTow_low : TqLow S (Pv S gbV) := by
  have h := rbFam_low (S := S) gbTowFam (by rw [(gbTowSup (S := S)).2.1]; exact (gbTowSup (S := S)).2.2.le)
  rwa [(gbTowSup (S := S)).2.1] at h

/-- **`U_T < U_G`**: the new bound `P(Γ_{Ω₁+ω·2})` lies above the bound `P(Γ_{Ω₁+ω})` of `Ri.riTow_low`. -/
theorem rjTow_gt (S : InaccSeq.{0}) : Pv S gaW < Pv S gbV := by
  obtain ⟨o1, o2, o3, o4, -⟩ := gbTow_order (S := S)
  have h : iota S gaW < iota S gbV := by
    rw [← (gbTowSup (S := S)).1]; exact ((o1.trans o2).trans o3).trans o4
  have := upsilon_normal.strictMono h
  rwa [ups_iota S, ups_iota S] at this

/-- **UPPER everywhere** from UPPER at `λ ≥ ι(Γ_{Ω₁+ω·2})`. -/
theorem rjTow_UPPER (hU : ∀ l, CdRange S l → iota S gbV ≤ l → CdUpper S l) : CdUPPER S := fun l hr => by
  rcases lt_or_ge l (iota S gbV) with h | h
  · exact (gbTowEnum hr h).1
  · exact hU l hr h

/-- **LOWER everywhere** from LOWER at `λ ≥ ι(Γ_{Ω₁+ω·2})`. -/
theorem rjTow_LOWER (hL : ∀ l, CdRange S l → iota S gbV ≤ l → CdLower S l) : CdLOWER S := fun l hr => by
  rcases lt_or_ge l (iota S gbV) with h | h
  · exact (gbTowEnum hr h).2
  · exact hL l hr h

/-- **The cap of the values everywhere** from the cap at `λ ≥ ι(Γ_{Ω₁+ω·2})`. -/
theorem rjTow_capV (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gbV ≤ l → CdCapV S l) :
    ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CdCapV S l := fun l hr hX => by
  rcases lt_or_ge l (iota S gbV) with h | h
  · exact gbTowCapV hr h
  · exact hV l hr hX h

/-- **`L(ω) ≤ ν_C`** from UPPER and the cap of the values at `λ ≥ ι(Γ_{Ω₁+ω·2})`. -/
theorem rjTow_nu (hU : ∀ l, CdRange S l → iota S gbV ≤ l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gbV ≤ l → CdCapV S l) :
    Nc.ncL S ω ≤ nuC :=
  cdLow_enum (rjTow_UPPER hU) (rjTow_capV hV)

/-- **The road `Gb.gbTowRoadL` with TCrest and (EMB₂) asked only at left ends `x ≥ U_G = P(Γ_{Ω₁+ω·2})`.** -/
theorem rjRoadTow (hU : ∀ l, CdRange S l → iota S gbV ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S gbV ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gbV ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : TqTCrestUp S (Pv S gbV)) (hB2 : TqEMB2Rest S (Pv S gbV)) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  gbTowRoadL hU hL hV hC hEQ (tqTCrest_of rjTow_low hrest) (tqEMB2_of rjTow_low hB2)

/-- **The road with (TC) and (EMB₂) asked only at left ends `x ≥ U_G` with no reach below `L(n+1)`**, (CL)
derived. -/
theorem rjRoadTow_CL (hU : ∀ l, CdRange S l → iota S gbV ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S gbV ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gbV ≤ l → CdCapV S l)
    (hEQ : CdEQ S) (htc : TqTCRest S (Pv S gbV)) (hB2 : TqEMB2Rest S (Pv S gbV)) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hTC : CdTC S := tqTC_of rjTow_low htc
  have hE : CdEMB2 S := tqEMB2_of rjTow_low hB2
  have hC : CdCL S := Cx.cxCL hTC hE
  exact ⟨hTC, hE, hC, (Cx.cxC1 hTC hE).1, rjRoadTow hU hL hV hC hEQ (tqTCrestUp_of htc) hB2⟩

/-- **The road with (TC) and (EMB₂) asked only at the left ends `x ∈ [U_G, L(n+2))` with no reach below `L(n+1)`
that are restart points or lie in `[L(n+1), L(n+2))`**, (CL) derived. -/
theorem rjRoadTow_rst (hU : ∀ l, CdRange S l → iota S gbV ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S gbV ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gbV ≤ l → CdCapV S l)
    (hEQ : CdEQ S) (htc : RbTCRst S (Pv S gbV)) (hB2 : RbEMB2Rst S (Pv S gbV)) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  have hν := rjTow_nu hU hV
  rjRoadTow_CL hU hL hV hEQ (rbTCRest_of hν htc) (rbEMB2Rest_of hν hB2)

/-- **The road with TCrest and (EMB₂) asked only at the left ends `x ∈ [U_G, L(n+2))` with no reach below `L(n+1)`
that are restart points or lie in `[L(n+1), L(n+2))`**; (TC) from ENUM-REACH and EQ, (CL) derived. -/
theorem rjRoadTow_rst2 (hU : ∀ l, CdRange S l → iota S gbV ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S gbV ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gbV ≤ l → CdCapV S l)
    (hEQ : CdEQ S) (hrest : RbTCrestRst S (Pv S gbV)) (hB2 : RbEMB2Rst S (Pv S gbV)) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hν := rjTow_nu hU hV
  have hTCr : CdTCrest S := tqTCrest_of rjTow_low (rbTCrestUp_of hν hrest)
  have hE : CdEMB2 S := tqEMB2_of rjTow_low (rbEMB2Rest_of hν hB2)
  have hTC : CdTC S := cdTC_of_enum (rjTow_UPPER hU) (rjTow_LOWER hL) hEQ hTCr
  have hC : CdCL S := Cx.cxCL hTC hE
  exact ⟨hTC, hE, hC, (Cx.cxC1 hTC hE).1, gbTowRoadL hU hL hV hC hEQ hTCr hE⟩

/-- **The road `rjRoadTow_rst` with (EMB₂) dropped and (TC) asked only at the restart left ends in `[U_G, L(n+2))`
and at `L(n+1)`**, `U_G = P(Γ_{Ω₁+ω·2})`, under `L(ω+1) ≤ ν_C` and `Ri.RiLhTopH` (a reduction: `L(ω+1) ≤ ν_C` is
half of the conclusion). -/
theorem rjRoadTow_nuH (hU : ∀ l, CdRange S l → iota S gbV ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S gbV ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gbV ≤ l → CdCapV S l)
    (hEQ : CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC) (hlh : Ri.RiLhTopH S) (htc : RdTCRst2 S (Pv S gbV)) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rjRoadTow_rst hU hL hV hEQ
    (rdTCRst_of hν (rdLhTopFix2_of_W (rhLhTopW_of_G (Ri.riLhTopG_of_H hlh))) htc) (rdEMB2Rst_of hν _)

/-- **(TC) at the named left end `x = L(n+1)`, given `T` (`L(ω) ≤₁ L(ω+1)`)**: it holds iff `L(n+1) ≤₁ L(n+2)`, the
`n`-th clause of (CL); so the left end `L(n+1)` of `Rd.RdTCRst2` asks exactly (CL) at `n`. -/
theorem rjTC_L_iff (hT : Cx.CxT S) (n : ℕ) :
    CdTCAt S n (Bc.bcC S n) ↔ le1 (Bc.bcC S n) (Bc.bcC S (n + 1)) := Cx.cxTCAt_L_iff hT n

end Googology.Trans.PoR.InaccPsi.R2.Rj
