/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/LowerChainMain.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.LowerChain
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.LiftLegRightProof
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.LegRowMatchInnerMain

set_option backward.do.legacy false

/-!
# `KeyLeRest` from the shared chain correspondence, with the proved leg statements

`LowerChain.keyLeRest_of_lower` takes `LeftStart` (legs left of `c_r`) and `StartJumpGe` (the
jump of the output key template) as hypotheses. Both are proved in other files:

* `LeftStart` follows from `LeftRow` (`Skip.leftStart_of_row`), which is the statement
  `LegLeft.PlainLegLeftRow` proved as `Recon.LowerPB.LiftLegPf.plainLegLeftRow`
  (`LiftLegRightProof.lean`, from `LiftLegRight`, a fact about `M(s)` alone);
* `StartJumpGe` is `LegLeft.StartJumpGe`, proved as `CopyShape.InnerRow.startJumpGe`
  (`LegRowMatchInnerMain.lean`).

So `KeyLeRest` follows from the two shared statements `TopStep`, `TopStart` and the seven
statements used only by `KeyLeRest`: `NonTopStep`, `StartRelNT`, `StartRootNT`, `StepCut`,
`CutJump`, `CutStartCopyNT`, `CutStartRootNT` (`keyLeRest_of_lower_main`).
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.LowerChain

open Canonical Reserve Official Descent Classification Proofs

theorem leftStart_holds : Skip.LeftStart :=
  Skip.leftStart_of_row Recon.LowerPB.LiftLegPf.plainLegLeftRow

theorem startJumpGe_holds : Skip.StartJumpGe := CopyShape.InnerRow.startJumpGe

/-- **`Control.KeyLeRest` from the shared family and the statements used only by it.** -/
theorem keyLeRest_of_lower_main (hTS : TopStep) (hTSt : TopStart) (hNS : NonTopStep)
    (hRel : StartRelNT) (hRoot : StartRootNT) (hCut : StepCut) (hCJump : CutJump)
    (hCCopy : CutStartCopyNT) (hCRoot : CutStartRootNT) : KeyLeRest :=
  keyLeRest_of_lower hTS hTSt hNS hRel hRoot leftStart_holds startJumpGe_holds hCut hCJump
    hCCopy hCRoot

/-- The same with the old statements `StartRoot`, `CutStartCopy`, `CutStartRoot`
(`ChainCorrRegions.lean`, `ChainCorrCut.lean`), which hold on the large-value inputs. -/
theorem keyLeRest_of_lower_old (hTS : TopStep) (hTSt : TopStart) (hNS : NonTopStep)
    (hRel : StartRelNT) (hRoot : StartRoot) (hCut : StepCut) (hCJump : CutJump)
    (hCCopy : CutStartCopy) (hCRoot : CutStartRoot) : KeyLeRest :=
  keyLeRest_of_lower_main hTS hTSt hNS hRel (startRootNT_of_startRoot hRoot) hCut hCJump
    (cutStartCopyNT_of_cutStartCopy hCCopy) (cutStartRootNT_of_cutStartRoot hCRoot)

/-- **Well-foundedness of the official expansion** from the reconstruction and the statements
of `keyLeRest_of_lower_main`. -/
theorem wellFounded_of_lower_main (hrec : Dimension.BlockReconstruction) (hTS : TopStep)
    (hTSt : TopStart) (hNS : NonTopStep) (hRel : StartRelNT) (hRoot : StartRootNT)
    (hCut : StepCut) (hCJump : CutJump) (hCCopy : CutStartCopyNT) (hCRoot : CutStartRootNT) :
    WellFounded Step :=
  wellFounded_of_block hrec ControlProof.controlDominates
    (keyLeRest_of_lower_main hTS hTSt hNS hRel hRoot hCut hCJump hCCopy hCRoot)

end OmegaY.Official.Classification.Proofs.ChainCorr.LowerChain

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LowerChain.leftStart_holds
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LowerChain.startJumpGe_holds
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LowerChain.keyLeRest_of_lower_main
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LowerChain.keyLeRest_of_lower_old
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LowerChain.wellFounded_of_lower_main
