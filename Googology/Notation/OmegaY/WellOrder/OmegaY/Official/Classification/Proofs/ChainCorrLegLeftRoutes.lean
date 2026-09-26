/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/ChainCorrLegLeftRoutes.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrLegLeftMain

set_option backward.do.legacy false

/-!
# The remaining top-level routes without `StartLeg`

`StartLeg` (`ChainCorrRegions.lean`) is false numerically, and `LegBelowTop`, from which it was
derived, is false (`LegBelowTopFalse.lean`). `ChainCorrLegLeft*.lean` replace it by
`startLeg_split` (proved) and the open `PlainLegLeftRow`, itself reduced to `LiftLegRight` (about
`M(s)` alone). This file gives the replacements of the remaining top-level theorems that passed
`StartLeg` through:

| old theorem (file) | replacement |
|---|---|
| `wellFounded_of_chains` (`ChainCorrRegions`) | `wellFounded_of_legLeft_ge` |
| `wellFounded_of_all_chains` (`ChainCorrCut`) | `wellFounded_of_all_chains_legLeft` |
| `wellFounded_of_chains_cut` (`ChainCorrCutLeg`) | `wellFounded_of_chains_cut_legLeft` |
| `CutParts.wellFounded_of_cut_parts` (`CutPartsStep`) | `wellFounded_of_cut_parts_legLeft` |
| `CutParts.wellFounded_of_cut_rest` (`CutPartsGen`) | `wellFounded_of_cut_rest_legLeft` |
| `CutParts.wellFounded_of_cut_final` (`CutPartsTop`) | `wellFounded_of_cut_final_legLeft` |
| `Inner.wellFounded_of_local` (`ChainCorrStepInner`) | `wellFounded_of_local_legLeft` |
| `LegJump.startLeg_startJump` (`ChainCorrStartLegJump`) | `startLeg_split`, `startJump_of_legLeft` |
| `InnerLookup.legLookup_left` (`StepInnerLookupLeg`) | `legLookup_left_of_row` |

## `StartJumpGe` as a hypothesis

`startJumpGe` (`ChainCorrLegLeft.lean`) proves `StartJumpGe` from the block profile `CopyOrder`,
`CopyEmitted`. But `CopyOrder` is false (`CopyShapeMAFalse.lean`, `s = (1,3,6,13,15,13)`), so
that derivation gives nothing. The theorems here take `StartJumpGe` itself as the hypothesis
(open; `StartJump` for legs at or right of `c_r`). It holds numerically on every input tested,
including the inputs where `CopyOrder` fails (`reference/official/startleg-left.cjs`, count
`StartJumpGe`; see `ChainCorrLegLeft.lean`).

The route through the cut statements (`CutParts.cut_statements*`) and through `LegLookup`
(`legLookup_inner`) still uses `CopyOrder`; that is not a use of `StartLeg` and is not repaired
here.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr.Inner ChainCorr.InnerLookup

/-- **Replaces `wellFounded_of_chains`**, with `StartLeg` replaced by `PlainLegLeftRow` and
`StartJump` by `StartJumpGe` (no `CopyOrder`). -/
theorem wellFounded_of_legLeft_ge (hrec : Dimension.BlockReconstruction) (hStep : StepInner)
    (hRow : PlainLegLeftRow) (hJ : StartJumpGe) (hCopy : StartCopy) (hRoot : StartRoot)
    (hKB : RegionCutBoundary) (hKI : RegionCutInner) : WellFounded Step :=
  wellFounded_of_regions hrec ControlProof.controlDominates
    (regionUpper_of_legLeft hStep hRow hJ hCopy hRoot)
    (regionPlainBoundary_of_legLeft hStep hRow hJ hCopy hRoot)
    (regionPlainInner_of_legLeft hStep hRow hJ hCopy hRoot)
    (regionCleanBoundary_of_legLeft hStep hRow hJ hCopy hRoot)
    (regionCleanInner_of_legLeft hStep hRow hJ hCopy hRoot) hKB hKI

/-- The same with `PlainLegLeftRow` replaced by `LiftLegRight` (about `M(s)` alone). -/
theorem wellFounded_of_lift_ge (hrec : Dimension.BlockReconstruction) (hStep : StepInner)
    (hLift : LiftLegRight) (hJ : StartJumpGe) (hCopy : StartCopy) (hRoot : StartRoot)
    (hKB : RegionCutBoundary) (hKI : RegionCutInner) : WellFounded Step :=
  wellFounded_of_legLeft_ge hrec hStep (plainLegLeftRow_of_lift hLift) hJ hCopy hRoot hKB hKI

/-- **Replaces `wellFounded_of_all_chains`** (`ChainCorrCut.lean`). -/
theorem wellFounded_of_all_chains_legLeft (hrec : Dimension.BlockReconstruction)
    (hStep : StepInner) (hRow : PlainLegLeftRow) (hJ : StartJumpGe) (hCopy : StartCopy)
    (hRoot : StartRoot) (hCut : StepCut) (hCLeg : CutLeg) (hCJump : CutJump)
    (hCCopy : CutStartCopy) (hCRoot : CutStartRoot) : WellFounded Step :=
  wellFounded_of_legLeft_ge hrec hStep hRow hJ hCopy hRoot
    (regionCutBoundary_of_chains hStep hCut hCLeg hCJump hCCopy hCRoot)
    (regionCutInner_of_chains hStep hCut hCLeg hCJump hCCopy hCRoot)

/-- **Replaces `wellFounded_of_chains_cut`** (`ChainCorrCutLeg.lean`; `CutLeg` is proved). -/
theorem wellFounded_of_chains_cut_legLeft (hrec : Dimension.BlockReconstruction)
    (hStep : StepInner) (hRow : PlainLegLeftRow) (hJ : StartJumpGe) (hCopy : StartCopy)
    (hRoot : StartRoot) (hCut : StepCut) (hCJump : CutJump) (hCCopy : CutStartCopy)
    (hCRoot : CutStartRoot) : WellFounded Step :=
  wellFounded_of_all_chains_legLeft hrec hStep hRow hJ hCopy hRoot hCut cutLeg hCJump hCCopy
    hCRoot

/-- **Replaces `CutParts.wellFounded_of_cut_parts`** (`CutPartsStep.lean`). -/
theorem wellFounded_of_cut_parts_legLeft (hrec : Dimension.BlockReconstruction)
    (hStep : StepInner) (hRow : PlainLegLeftRow) (hJ : StartJumpGe) (hCopy : StartCopy)
    (hRoot : StartRoot) (hA : ChainCorr.CopyOrder) (hC2 : ChainCorr.CopyFirst)
    (hBC : ChainCorr.BoundaryChain)
    (hPa : CutParts.CutPaRow) (hGen : CutParts.CutGenReach) (hTop : CutParts.CutTopLookup)
    (hLow : CutParts.CutRunLow) (hHigh : CutParts.CutRunHigh)
    (hOR : CutParts.CutOriginReach) (hJT : CutParts.CutJumpTop) : WellFounded Step := by
  obtain ⟨h1, h2, h3, h4⟩ :=
    CutParts.cut_statements hStep hA hC2 hBC hPa hGen hTop hLow hHigh hOR hJT
  exact wellFounded_of_chains_cut_legLeft hrec hStep hRow hJ hCopy hRoot h1 h2 h3 h4

/-- **Replaces `CutParts.wellFounded_of_cut_rest`** (`CutPartsGen.lean`; `CutPaRow` and
`CutGenReach` are proved). -/
theorem wellFounded_of_cut_rest_legLeft (hrec : Dimension.BlockReconstruction)
    (hStep : StepInner) (hRow : PlainLegLeftRow) (hJ : StartJumpGe) (hCopy : StartCopy)
    (hRoot : StartRoot) (hA : ChainCorr.CopyOrder) (hC2 : ChainCorr.CopyFirst)
    (hBC : ChainCorr.BoundaryChain)
    (hTop : CutParts.CutTopLookup) (hLow : CutParts.CutRunLow) (hHigh : CutParts.CutRunHigh)
    (hOR : CutParts.CutOriginReach) (hJT : CutParts.CutJumpTop) : WellFounded Step :=
  wellFounded_of_cut_parts_legLeft hrec hStep hRow hJ hCopy hRoot hA hC2 hBC CutParts.cutPaRow
    CutParts.cutGenReach hTop hLow hHigh hOR hJT

/-- **Replaces `CutParts.wellFounded_of_cut_final`** (`CutPartsTop.lean`), with `StartJumpGe`
as a hypothesis (`wellFounded_of_cut_legLeft` derives it from `CopyOrder`, `CopyEmitted`). -/
theorem wellFounded_of_cut_final_legLeft (hrec : Dimension.BlockReconstruction)
    (hStep : StepInner) (hRow : PlainLegLeftRow) (hJ : StartJumpGe) (hCopy : StartCopy)
    (hRoot : StartRoot) (hA : ChainCorr.CopyOrder) (hB : ChainCorr.CopyEmitted)
    (hC2 : ChainCorr.CopyFirst)
    (hBC : ChainCorr.BoundaryChain) (hBump : CutParts.CutBump) (hLeg : CutParts.CutLegLookup)
    (hLow : CutParts.CutRunLow) (hHigh : CutParts.CutRunHigh)
    (hOR : CutParts.CutOriginReach) (hJT : CutParts.CutJumpTop) : WellFounded Step := by
  obtain ⟨h1, h2, h3, h4⟩ :=
    CutParts.cut_statements_final hStep hA hB hC2 hBC hBump hLeg hLow hHigh hOR hJT
  exact wellFounded_of_chains_cut_legLeft hrec hStep hRow hJ hCopy hRoot h1 h2 h3 h4

/-- **Replaces `Inner.wellFounded_of_local`** (`ChainCorrStepInner.lean`), with `StartJumpGe` as
a hypothesis (no `CopyOrder`; compare `wellFounded_of_local_lift`). -/
theorem wellFounded_of_local_legLeft (hrec : Dimension.BlockReconstruction) (hNext : NextCopy)
    (hLeft : LeftCopy) (hJump : JumpCopy) (hClean : CleanStep) (hCP : CleanParent)
    (hRow : PlainLegLeftRow) (hJ : StartJumpGe) (hCopy : StartCopy) (hRoot : StartRoot)
    (hKB : RegionCutBoundary) (hKI : RegionCutInner) : WellFounded Step :=
  wellFounded_of_legLeft_ge hrec (stepInner_of_parts hNext hLeft hJump hClean hCP) hRow hJ hCopy
    hRoot hKB hKI

/-- **Replaces `LegJump.startLeg_startJump`**: the split of the leg (proved) and `StartJump`
from `PlainLegLeftRow` and the block profile. -/
theorem startLegSplit_startJump (hRow : PlainLegLeftRow) (hA : ChainCorr.CopyOrder)
    (hB : ChainCorr.CopyEmitted) :
    (∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
      ∀ j (hj : j < es.length),
      ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
        ¬ (es[j].2.isUpper = true ∧ l.column < ρ.cr) →
        ρ.cr ≤ l.column ∨ ((∃ r, es[j].2 = .plain r) ∧ l.column < ρ.cr)) ∧ StartJump :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ hS _ hj _ _ _ _ _ _ _ _ hL hnot => startLeg_split hS hj hL hnot,
    startJump_of_legLeft hRow hA hB⟩

end OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft.wellFounded_of_legLeft_ge
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft.wellFounded_of_lift_ge
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft.wellFounded_of_all_chains_legLeft
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft.wellFounded_of_chains_cut_legLeft
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft.wellFounded_of_cut_parts_legLeft
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft.wellFounded_of_cut_rest_legLeft
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft.wellFounded_of_cut_final_legLeft
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft.wellFounded_of_local_legLeft
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft.startLegSplit_startJump
