import Googology.Trans.PoR.InaccPsi.R2.RjTop
import Googology.Trans.PoR.InaccPsi.R2.GcTowLoc

/-!
# (TC) and (EMB₂) below the bound `U_C = υ(ι(Γ_{Ω₁+ε₀})) = P(Γ_{Ω₁+ε₀})`, unconditionally

`L(ξ) = Nc.ncL S ξ`, `c_n = L(n+1)`, `Γ_{Ω₁+ω·2}` (`Gb.gbV`), `Γ_{Ω₁+ε₀}` (`Gc.gcV`), `U_G = P(Γ_{Ω₁+ω·2})` (the bound
of `Rj.rjTow_low`), `U_C = υ(sup_n Λ⁺(gcB (gcSeq n))) = υ(ι(Γ_{Ω₁+ε₀})) = P(Γ_{Ω₁+ε₀})` (`Gc.gcFamSup`).

* `rkTow_low` (**every point below `U_C = P(Γ_{Ω₁+ε₀})` has an `R₂^C`-reach below `L(0)`**: `Rb.rbFam_low` on the
  transfinite tower `Gc.gcFam`, with `U_C < L(0)` from `Gc.gcFamSup`), `rkTow_gt` (`U_G < U_C`);
* `rkTow_UPPER`, `rkTow_LOWER`, `rkTow_capV`, `rkTow_nu` (UPPER, LOWER, the cap and **`L(ω) ≤ ν_C`** from their parts
  at `λ ≥ ι(Γ_{Ω₁+ε₀})`, with ENUM-REACH and CapV below `ι(Γ_{Ω₁+ε₀})`, `Gc.gcEnum`, `Gc.gcCapV`);
* `rkRoadTow` (**the road `Gc.gcRoad` with TCrest and (EMB₂) asked only at left ends `x ≥ U_C`**),
  `rkRoadTow_CL` ((TC) in place of TCrest, (CL) derived), `rkRoadTow_rst` (**(TC) and (EMB₂) asked only at the left
  ends `x ∈ [U_C, L(n+2))` with no reach below `L(n+1)` that are restart points or lie in `[L(n+1), L(n+2))`**),
  `rkRoadTow_rst2` (TCrest in place of (TC)), `rkRoadTow_nuH` (**(TC) asked only at the restart left ends in
  `[U_C, L(n+2))` and at `L(n+1)`, (EMB₂) dropped, under `L(ω+1) ≤ ν_C` and `Ri.RiLhTopH`**: a reduction),
  `rkRoadTow_nuJ` (the same with `Rj.RjVtMove`, `Rj.RjLhTopOut` in place of `Ri.RiLhTopH`);
* `rkTC_L` (**given `T`, (TC) at the named left ends `x = L(n+1)` for every `n` is (CL)**), `rkTCRst2_iff`
  (**given `T`, `Rd.RdTCRst2 S U_C` is equivalent to (CL) together with (TC) at the restart left ends in
  `[U_C, L(n+2))`**: the two parts of the one remaining TC hypothesis, stated separately).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Tq
  Googology.Trans.PoR.InaccPsi.R2.Rb Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Gc

variable {S : InaccSeq.{0}}

/-- **Every point below `U_C = P(Γ_{Ω₁+ε₀})` has an `R₂^C`-reach below `L(0)`**, unconditionally. -/
theorem rkTow_low : TqLow S (Pv S gcV) := by
  have h := rbFam_low (S := S) gcFam (by rw [(gcFamSup (S := S)).2.1]; exact (gcFamSup (S := S)).2.2.le)
  rwa [(gcFamSup (S := S)).2.1] at h

/-- **`U_G < U_C`**: the new bound `P(Γ_{Ω₁+ε₀})` lies above the bound `P(Γ_{Ω₁+ω·2})` of `Rj.rjTow_low`. -/
theorem rkTow_gt (S : InaccSeq.{0}) : Pv S Gb.gbV < Pv S gcV := by
  have h : iota S Gb.gbV < iota S gcV := gc_beyond_gb
  have := upsilon_normal.strictMono h
  rwa [ups_iota S, ups_iota S] at this

/-- **UPPER everywhere** from UPPER at `λ ≥ ι(Γ_{Ω₁+ε₀})`. -/
theorem rkTow_UPPER (hU : ∀ l, CdRange S l → iota S gcV ≤ l → CdUpper S l) : CdUPPER S := fun l hr => by
  rcases lt_or_ge l (iota S gcV) with h | h
  · exact (gcEnum hr h).1
  · exact hU l hr h

/-- **LOWER everywhere** from LOWER at `λ ≥ ι(Γ_{Ω₁+ε₀})`. -/
theorem rkTow_LOWER (hL : ∀ l, CdRange S l → iota S gcV ≤ l → CdLower S l) : CdLOWER S := fun l hr => by
  rcases lt_or_ge l (iota S gcV) with h | h
  · exact (gcEnum hr h).2
  · exact hL l hr h

/-- **The cap of the values everywhere** from the cap at `λ ≥ ι(Γ_{Ω₁+ε₀})`. -/
theorem rkTow_capV (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gcV ≤ l → CdCapV S l) :
    ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CdCapV S l := fun l hr hX => by
  rcases lt_or_ge l (iota S gcV) with h | h
  · exact gcCapV hr h
  · exact hV l hr hX h

/-- **`L(ω) ≤ ν_C`** from UPPER and the cap of the values at `λ ≥ ι(Γ_{Ω₁+ε₀})`. -/
theorem rkTow_nu (hU : ∀ l, CdRange S l → iota S gcV ≤ l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gcV ≤ l → CdCapV S l) :
    Nc.ncL S ω ≤ nuC :=
  cdLow_enum (rkTow_UPPER hU) (rkTow_capV hV)

/-- **The road `Gc.gcRoad` with TCrest and (EMB₂) asked only at left ends `x ≥ U_C = P(Γ_{Ω₁+ε₀})`.** -/
theorem rkRoadTow (hU : ∀ l, CdRange S l → iota S gcV ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S gcV ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gcV ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : TqTCrestUp S (Pv S gcV)) (hB2 : TqEMB2Rest S (Pv S gcV)) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  gcRoad hU hL hV hC hEQ (tqTCrest_of rkTow_low hrest) (tqEMB2_of rkTow_low hB2)

/-- **The road with (TC) and (EMB₂) asked only at left ends `x ≥ U_C` with no reach below `L(n+1)`**, (CL)
derived. -/
theorem rkRoadTow_CL (hU : ∀ l, CdRange S l → iota S gcV ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S gcV ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gcV ≤ l → CdCapV S l)
    (hEQ : CdEQ S) (htc : TqTCRest S (Pv S gcV)) (hB2 : TqEMB2Rest S (Pv S gcV)) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hTC : CdTC S := tqTC_of rkTow_low htc
  have hE : CdEMB2 S := tqEMB2_of rkTow_low hB2
  have hC : CdCL S := Cx.cxCL hTC hE
  exact ⟨hTC, hE, hC, (Cx.cxC1 hTC hE).1, rkRoadTow hU hL hV hC hEQ (tqTCrestUp_of htc) hB2⟩

/-- **The road with (TC) and (EMB₂) asked only at the left ends `x ∈ [U_C, L(n+2))` with no reach below `L(n+1)`
that are restart points or lie in `[L(n+1), L(n+2))`**, (CL) derived. -/
theorem rkRoadTow_rst (hU : ∀ l, CdRange S l → iota S gcV ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S gcV ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gcV ≤ l → CdCapV S l)
    (hEQ : CdEQ S) (htc : RbTCRst S (Pv S gcV)) (hB2 : RbEMB2Rst S (Pv S gcV)) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  have hν := rkTow_nu hU hV
  rkRoadTow_CL hU hL hV hEQ (rbTCRest_of hν htc) (rbEMB2Rest_of hν hB2)

/-- **The road with TCrest and (EMB₂) asked only at the left ends `x ∈ [U_C, L(n+2))` with no reach below `L(n+1)`
that are restart points or lie in `[L(n+1), L(n+2))`**; (TC) from ENUM-REACH and EQ, (CL) derived. -/
theorem rkRoadTow_rst2 (hU : ∀ l, CdRange S l → iota S gcV ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S gcV ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gcV ≤ l → CdCapV S l)
    (hEQ : CdEQ S) (hrest : RbTCrestRst S (Pv S gcV)) (hB2 : RbEMB2Rst S (Pv S gcV)) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hν := rkTow_nu hU hV
  have hTCr : CdTCrest S := tqTCrest_of rkTow_low (rbTCrestUp_of hν hrest)
  have hE : CdEMB2 S := tqEMB2_of rkTow_low (rbEMB2Rest_of hν hB2)
  have hTC : CdTC S := cdTC_of_enum (rkTow_UPPER hU) (rkTow_LOWER hL) hEQ hTCr
  have hC : CdCL S := Cx.cxCL hTC hE
  exact ⟨hTC, hE, hC, (Cx.cxC1 hTC hE).1, gcRoad hU hL hV hC hEQ hTCr hE⟩

/-- **The road `rkRoadTow_rst` with (EMB₂) dropped and (TC) asked only at the restart left ends in `[U_C, L(n+2))`
and at `L(n+1)`**, `U_C = P(Γ_{Ω₁+ε₀})`, under `L(ω+1) ≤ ν_C` and `Ri.RiLhTopH` (a reduction: `L(ω+1) ≤ ν_C` is
half of the conclusion). -/
theorem rkRoadTow_nuH (hU : ∀ l, CdRange S l → iota S gcV ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S gcV ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gcV ≤ l → CdCapV S l)
    (hEQ : CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC) (hlh : Ri.RiLhTopH S) (htc : RdTCRst2 S (Pv S gcV)) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rkRoadTow_rst hU hL hV hEQ
    (rdTCRst_of hν (rdLhTopFix2_of_W (rhLhTopW_of_G (Ri.riLhTopG_of_H hlh))) htc) (rdEMB2Rst_of hν _)

/-- **The road `rkRoadTow_nuH` with `Rj.RjVtMove` and `Rj.RjLhTopOut` in place of `Ri.RiLhTopH`.** -/
theorem rkRoadTow_nuJ (hU : ∀ l, CdRange S l → iota S gcV ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S gcV ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gcV ≤ l → CdCapV S l)
    (hEQ : CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC) (hmv : Rj.RjVtMove S) (hout : Rj.RjLhTopOut S)
    (htc : RdTCRst2 S (Pv S gcV)) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rkRoadTow_nuH hU hL hV hEQ hν (Rj.riLhTopH_of_rj hmv hout) htc

/-- **(TC) at the named left ends `x = L(n+1)`, given `T`**: (TC) holds at every `L(n+1)` iff (CL) holds, i.e.
`L(n+1) ≤₁ L(n+2)` for every `n`. -/
theorem rkTC_L (hT : Cx.CxT S) :
    (∀ n : ℕ, CdTCAt S n (Bc.bcC S n)) ↔ ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1)) :=
  ⟨fun h n => (Rj.rjTC_L_iff hT n).1 (h n), fun h n => (Rj.rjTC_L_iff hT n).2 (h n)⟩

/-- The restart part of `Rd.RdTCRst2 S U`: (TC) at the restart left ends `x = υ_l ∈ [U, L(n+2))` with no reach below
`L(n+1)`. -/
def RkTCRstOnly (S : InaccSeq.{0}) (U : Ordinal.{0}) : Prop :=
  ∀ n : ℕ, ∀ x < Bc.bcC S (n + 1), U ≤ x → (¬ ∃ r < Bc.bcC S n, IsReach R2C x r) →
    (∃ l, IsRestartIdx l ∧ x = upsilon l) → CdTCAt S n x

/-- **`Rd.RdTCRst2 S U_C` splits, given `T`, into (TC) at the restart left ends in `[U_C, L(n+2))` and the named
left ends `x = L(n+1)`, the latter being (CL)** (`L(n+1) ≥ L(0) > U_C`). -/
theorem rkTCRst2_iff (hT : Cx.CxT S) :
    RdTCRst2 S (Pv S gcV) ↔ RkTCRstOnly S (Pv S gcV) ∧ ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1)) := by
  constructor
  · intro h
    refine ⟨fun n x hx hU hr hrst => h n x hx hU hr (Or.inr hrst), fun n => ?_⟩
    refine (Rj.rjTC_L_iff hT n).1 ?_
    by_cases hr : ∃ r < Bc.bcC S n, IsReach R2C (Bc.bcC S n) r
    · obtain ⟨r, hr, hR⟩ := hr
      exact absurd ((hR.2 _ (le1_refl _)).trans_lt hr) (lt_irrefl _)
    · have hX : Bc.bcC S n < Bc.bcC S (n + 1) := Cx.cxC_lt n
      have hU : Pv S gcV ≤ Bc.bcC S n :=
        ((gcFamSup (S := S)).2.2.trans_le (Ph.phL_chain (S := S) n).1).le
      exact h n _ hX hU hr (Or.inl rfl)
  · rintro ⟨hrst, hcl⟩ n x hx hU hr hcase
    rcases hcase with rfl | hR
    · exact (Rj.rjTC_L_iff hT n).2 (hcl n)
    · exact hrst n x hx hU hr hR

/-- **The road `rkRoadTow_nuJ` with the two parts of the TC hypothesis separated**: (TC) only at the restart left
ends in `[U_C, L(n+2))`, (CL), and `T`. -/
theorem rkRoadTow_nuJ2 (hU : ∀ l, CdRange S l → iota S gcV ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S gcV ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gcV ≤ l → CdCapV S l)
    (hEQ : CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC) (hmv : Rj.RjVtMove S) (hout : Rj.RjLhTopOut S)
    (hT : Cx.CxT S) (hrst : RkTCRstOnly S (Pv S gcV)) (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rkRoadTow_nuJ hU hL hV hEQ hν hmv hout ((rkTCRst2_iff hT).2 ⟨hrst, hcl⟩)

end Googology.Trans.PoR.InaccPsi.R2.Rk
