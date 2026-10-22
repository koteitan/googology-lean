import Googology.Trans.PoR.InaccPsi.R2.RbLow
import Googology.Trans.PoR.InaccPsi.R2.LxZF

/-!
# (TC) and (EMB₂) below the newest frontier `U″ = υ(Λ⁺(lxZ))`

`L(ξ) = Nc.ncL S ξ`, `c_n = L(n+1)` (`Bc.bcC`), `B_n = Bc.bcB S n`, `U′ = υ(sup_n Λ⁺(lqBN n))` (`Rb.rbB_low`),
`U″ = υ(Λ⁺(lxZ)) = P(ε_{Γ_{Ω₁+1}+Ω₁}·ω)` (`Lx.lxZ_loc`), and `U′ < U″ < L(0)` (`Lx.lxZ_fr_order`,
`Lx.lxBN_lt_K1`).

* `rdZ_low` (**every point below `U″` has an `R₂^C`-reach below `L(0)`**: the block specification of `lxZ` is an
  `OffSpecGen` up to `Λ⁺(lxZ)`, `Tq.tqLow_spec`), `rdZ_low_gt` (`U′ < U″`, so the new bound is above the old one);
* `rdZ_UPPER`, `rdZ_LOWER`, `rdZ_nu` (**`L(ω) ≤ ν_C`** from UPPER at `λ ≥ Λ⁺(lxZ)` and the cap of the values outside
  `Λ⁺(lxZ)`);
* `rdRoadZ` (**the road `Lx.lxZRoad` with TCrest and (EMB₂) asked only at left ends `x ≥ U″`**), `rdRoadZ_CL`
  (the same with (TC) in place of TCrest, (CL) derived);
* `rdRoadZ_rst` (**(TC) and (EMB₂) asked only at the left ends `x ∈ [U″, L(n+2))` with no reach below `L(n+1)` that
  are restart points or lie in `[L(n+1), L(n+2))`**, (CL) derived), `rdRoadZ_rst2` (**TCrest in place of (TC)**,
  also not at the restarts `ρ_λ` of the range with `r(λ) < L(n+2)`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Tq
  Googology.Trans.PoR.InaccPsi.R2.Rb Googology.Trans.PoR.InaccPsi.R2.Lx

variable {S : InaccSeq.{0}}

/-- **Every point below `U″ = υ(Λ⁺(lxZ))` has an `R₂^C`-reach below `L(0)`.** -/
theorem rdZ_low : TqLow S (upsilon (xtB1 lxZ.sys)) :=
  tqLow_spec (xtSpec1 lxZ.topPkg) (lxZ_fr_order (S := S) 0).2.1.le

/-- **`U′ < U″`**: the new bound lies above the bound `U′ = υ(sup_n Λ⁺(lqBN n))` of `Rb.rbB_low`. -/
theorem rdZ_low_gt (S : InaccSeq.{0}) : upsilon lqFamB.famSup < upsilon (xtB1 lxZ.sys) := by
  refine upsilon_normal.strictMono ?_
  exact ((lxBN_lt_K1 S).trans (lxFam.famBd_lt 1)).trans (lxFam_lt_Z S)

/-- **UPPER everywhere** from UPPER at `λ ≥ Λ⁺(lxZ)`. -/
theorem rdZ_UPPER (hU : ∀ l, CdRange S l → xtB1 lxZ.sys ≤ l → CdUpper S l) : CdUPPER S :=
  xtUPPER3 (xtSpec1 lxZ.topPkg) lxZ_nonfix hU (fun _ hr hlB hfix => lxZT_fix hr hlB hfix)

/-- **LOWER everywhere** from LOWER at `λ ≥ Λ⁺(lxZ)`. -/
theorem rdZ_LOWER (hL : ∀ l, CdRange S l → xtB1 lxZ.sys ≤ l → CdLower S l) : CdLOWER S :=
  xtLOWER3 (xtSpec1 lxZ.topPkg) lxZ_nonfix hL (fun _ hr hlB hfix => lxZT_fix hr hlB hfix)

/-- **`L(ω) ≤ ν_C`** from UPPER at `λ ≥ Λ⁺(lxZ)` and the cap of the values outside `Λ⁺(lxZ)`. -/
theorem rdZ_nu (hU : ∀ l, CdRange S l → xtB1 lxZ.sys ≤ l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lxZ.sys) l → CdCapV S l) :
    Nc.ncL S ω ≤ nuC :=
  cdLow_enum (rdZ_UPPER hU) (xtCapV (xtSpec1 lxZ.topPkg) lxZ_nonfix hV)

/-- **The road `Lx.lxZRoad` with TCrest and (EMB₂) asked only at left ends `x ≥ U″`.** -/
theorem rdRoadZ (hU : ∀ l, CdRange S l → xtB1 lxZ.sys ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 lxZ.sys ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lxZ.sys) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : TqTCrestUp S (upsilon (xtB1 lxZ.sys)))
    (hB2 : TqEMB2Rest S (upsilon (xtB1 lxZ.sys))) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  lxZRoad hU hL hV hC hEQ (tqTCrest_of rdZ_low hrest) (tqEMB2_of rdZ_low hB2)

/-- **The road with (TC) and (EMB₂) asked only at left ends `x ≥ U″` with no reach below `L(n+1)`**, (CL) derived. -/
theorem rdRoadZ_CL (hU : ∀ l, CdRange S l → xtB1 lxZ.sys ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 lxZ.sys ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lxZ.sys) l → CdCapV S l)
    (hEQ : CdEQ S) (htc : TqTCRest S (upsilon (xtB1 lxZ.sys)))
    (hB2 : TqEMB2Rest S (upsilon (xtB1 lxZ.sys))) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hTC : CdTC S := tqTC_of rdZ_low htc
  have hE : CdEMB2 S := tqEMB2_of rdZ_low hB2
  have hC : CdCL S := Cx.cxCL hTC hE
  exact ⟨hTC, hE, hC, (Cx.cxC1 hTC hE).1, rdRoadZ hU hL hV hC hEQ (tqTCrestUp_of htc) hB2⟩

/-- **The road with (TC) and (EMB₂) asked only at the left ends `x ∈ [U″, L(n+2))` with no reach below `L(n+1)` that
are restart points or lie in `[L(n+1), L(n+2))`**, (CL) derived. -/
theorem rdRoadZ_rst (hU : ∀ l, CdRange S l → xtB1 lxZ.sys ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 lxZ.sys ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lxZ.sys) l → CdCapV S l)
    (hEQ : CdEQ S) (htc : RbTCRst S (upsilon (xtB1 lxZ.sys)))
    (hB2 : RbEMB2Rst S (upsilon (xtB1 lxZ.sys))) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  have hν := rdZ_nu hU hV
  rdRoadZ_CL hU hL hV hEQ (rbTCRest_of hν htc) (rbEMB2Rest_of hν hB2)

/-- **The road with TCrest and (EMB₂) asked only at the left ends `x ∈ [U″, L(n+2))` with no reach below `L(n+1)` that
are restart points or lie in `[L(n+1), L(n+2))`** (TCrest also not at the restarts of the range with
`r(λ) < L(n+2)`); (TC) from ENUM-REACH and EQ (`cdTC_of_enum`), (CL) derived. -/
theorem rdRoadZ_rst2 (hU : ∀ l, CdRange S l → xtB1 lxZ.sys ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 lxZ.sys ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lxZ.sys) l → CdCapV S l)
    (hEQ : CdEQ S) (hrest : RbTCrestRst S (upsilon (xtB1 lxZ.sys)))
    (hB2 : RbEMB2Rst S (upsilon (xtB1 lxZ.sys))) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hν := rdZ_nu hU hV
  have hTCr : CdTCrest S := tqTCrest_of rdZ_low (rbTCrestUp_of hν hrest)
  have hE : CdEMB2 S := tqEMB2_of rdZ_low (rbEMB2Rest_of hν hB2)
  have hTC : CdTC S := cdTC_of_enum (rdZ_UPPER hU) (rdZ_LOWER hL) hEQ hTCr
  have hC : CdCL S := Cx.cxCL hTC hE
  exact ⟨hTC, hE, hC, (Cx.cxC1 hTC hE).1, lxZRoad hU hL hV hC hEQ hTCr hE⟩

end Googology.Trans.PoR.InaccPsi.R2.Rd
