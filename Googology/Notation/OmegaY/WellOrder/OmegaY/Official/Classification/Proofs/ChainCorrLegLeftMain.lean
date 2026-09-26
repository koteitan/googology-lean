/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/ChainCorrLegLeftMain.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrLegLeftLookup
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrLegLeftItems

set_option backward.do.legacy false

/-!
# The chain-correspondence route without `LegBelowTop`, `StartLeg` and `StartJump`

The summary theorems of the repaired route (`ChainCorrLegLeft*.lean`). Every former use of the
false `LegBelowTop` or of the numerically false `StartLeg` is replaced by the statement
`LiftLegRight` about `M(s)` alone (`ChainCorrLegLeftItems.lean`), and `StartJump` is proved where
it is used (`LegLeft.startJumpGe`).

* `wellFounded_of_local_lift`: replaces `Inner.wellFounded_of_local`.
* `wellFounded_of_cut_lift`: replaces `CutParts.wellFounded_of_cut_final`.
* `wellFounded_of_open_lift`: the same with `StepInner` replaced by its open parts
  (`stepInner_of_legLeft`, which replaces `InnerLookup.stepInner_of_open`).

These theorems still take `CopyOrder`, which is false (`CopyShapeMAFalse.lean`), and `StartCopy`,
which fails numerically (`StartRootPartsGapTopFalse.lean`); neither is a use of `StartLeg`.
`StepInner` (a hypothesis of `wellFounded_of_cut_lift`, and the conclusion of the parts in
`wellFounded_of_local_lift`) and `LegGapTop` (a hypothesis of `wellFounded_of_open_lift`) also
fail numerically on `(1,3,8,10,15,8)[1]` (`notes/05-large-value-audit.md`).
`ChainCorrLegLeftRoutes.lean` and `ChainCorrLegLeftJump.lean` give the region route without
`CopyOrder` (`wellFounded_of_lift_inner`).
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr.Inner ChainCorr.InnerLookup

/-- **Replaces `Inner.wellFounded_of_local`**: the local statements of `StepInner`,
`LiftLegRight`, the block profile and the two remaining start statements. -/
theorem wellFounded_of_local_lift (hrec : Dimension.BlockReconstruction) (hNext : NextCopy)
    (hLeft : LeftCopy) (hJump : JumpCopy) (hClean : CleanStep) (hCP : CleanParent)
    (hLift : LiftLegRight) (hA : CopyOrder) (hB : CopyEmitted) (hCopy : StartCopy)
    (hRoot : StartRoot) (hKB : RegionCutBoundary) (hKI : RegionCutInner) : WellFounded Step :=
  wellFounded_of_lift hrec (stepInner_of_parts hNext hLeft hJump hClean hCP) hLift hA hB hCopy
    hRoot hKB hKI

/-- **Replaces `CutParts.wellFounded_of_cut_final`.** -/
theorem wellFounded_of_cut_lift (hrec : Dimension.BlockReconstruction) (hStep : StepInner)
    (hLift : LiftLegRight) (hCopy : StartCopy) (hRoot : StartRoot)
    (hA : ChainCorr.CopyOrder) (hB : ChainCorr.CopyEmitted)
    (hC2 : ChainCorr.CopyFirst) (hBC : ChainCorr.BoundaryChain)
    (hBump : CutParts.CutBump) (hLeg : CutParts.CutLegLookup) (hLow : CutParts.CutRunLow)
    (hHigh : CutParts.CutRunHigh) (hOR : CutParts.CutOriginReach) (hJT : CutParts.CutJumpTop) :
    WellFounded Step :=
  wellFounded_of_cut_legLeft hrec hStep (plainLegLeftRow_of_lift hLift) hCopy hRoot hA hB hC2 hBC
    hBump hLeg hLow hHigh hOR hJT

/-- **Well-foundedness from the open statements of the chain-correspondence route**, without
`LegBelowTop`, `StartLeg`, `StartJump` and `StepInner`. -/
theorem wellFounded_of_open_lift (hrec : Dimension.BlockReconstruction)
    (hLift : LiftLegRight) (hCopy : StartCopy) (hRoot : StartRoot)
    (hA : ChainCorr.CopyOrder) (hB : ChainCorr.CopyEmitted) (hB' : Inner.CopyEmitted)
    (hC2 : ChainCorr.CopyFirst) (hC2' : Inner.CopyFirst) (hBC : ChainCorr.BoundaryChain)
    (hG : LegGapTop) (hO : LegOriginReach) (hCN : Inner.CleanNext) (hCL : Inner.CleanLookup)
    (hCP : Inner.CleanParent)
    (hBump : CutParts.CutBump) (hLeg : CutParts.CutLegLookup) (hLow : CutParts.CutRunLow)
    (hHigh : CutParts.CutRunHigh) (hOR : CutParts.CutOriginReach) (hJT : CutParts.CutJumpTop) :
    WellFounded Step :=
  wellFounded_of_open_legLeft hrec (plainLegLeftRow_of_lift hLift) hCopy hRoot hA hB hB' hC2 hC2'
    hBC hG hO hCN hCL hCP hBump hLeg hLow hHigh hOR hJT

end OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft.wellFounded_of_local_lift
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft.wellFounded_of_cut_lift
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft.wellFounded_of_open_lift
