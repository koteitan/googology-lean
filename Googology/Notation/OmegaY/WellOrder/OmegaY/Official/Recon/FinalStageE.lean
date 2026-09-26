/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/FinalStageE.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossUpperQAssembly
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CCLAssembly
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TSQFinal
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.SRTMain
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.P3TMain

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# Stage E: the final assembly

`WellFounded Descent.Step` (no infinite chain of official ω-Y expansions; `Descent.Step t s`
says that `t` is an expansion `s[n]` of the non-empty sequence `s`) from exactly the five open
statements of `PLAN.md`:

| hypothesis | definition |
|---|---|
| `RootValueIn` | `Recon.TSQ.RVP.RootValueIn` (`Classification/Proofs/TSQRootValueX0.lean`) |
| `PaONoGapHi` | `Recon.CrossUpperQ.PaONoGapHi` (`Recon/CrossUpperQ.lean`) |
| `CutRightTopHi` | `Recon.CrossUpperQ.CutRightTopHi` (`Recon/CrossUpperQ.lean`) |
| `SeamChainX` | `Recon.CrossUpperQ.SeamChainX` (`Recon/CrossUpperQAssembly.lean`) |
| `QRootRowGe` | `Recon.CrossUpperQ.QRootRowGe` (`Recon/CrossUpperQAssembly.lean`) |

No other hypothesis is used. The proved results that are plugged in:

* `TopStep` (`topStep_final`): `TopStepLoRoot` (`SRT.topStepLoRoot`, from the proved
  `CutParentNT`, `StepRootTop`) and `TopStepLoJump` (`LRC.jumpLawHolds`, `lowExpCopy`);
* `TopStart'` from `RootValueIn` (`TSQ.topStart'_of_cutParent_rootValueIn` with
  `CPN.cutParentNT`): `TopStartLoRootW` from `CutParentNT`, `StartRootTopUp`
  (`BTL.startRootTopUp`), `TopStartPaOUp` from `RootValueIn`, `TopStartCutRight`
  (`TSQ.topStartCutRight`);
* `BoundaryChain` (`CPN.boundaryChain`), `CutJumpRootRow`, `CutRunTop` (`P3T`);
* `RootPass IsPlain` (`CCL.rootPass_plain_of` with `CutParentNT`), `LexImg IsPlain`,
  `LexImg IsClean` (`CCL.lexImg_plain_final`, `CCL.lexImg_clean_final`, from `copyCountLe`);
* `CrossLexFor IsUpper` from `TopStep`, `TopStart'` and the four statements `SeamChainX`,
  `QRootRowGe`, `PaONoGapHi`, `CutRightTopHi` (`CrossUpperQ.crossLexFor_upper_of_chain`);
* the rest of the reconstruction and package 3 (`TopStartFixAssembly.wellFounded_of_stageC'`,
  `CrossUpperQ.wellFounded_of_stageC_QX`), ending in `ControlProof.wellFounded_of_block_keys`.

The two hypotheses of `ControlProof.wellFounded_of_block_keys` are also given separately
(`blockReconstruction_of_stageE`, `keyLeRest_of_stageE`). Of the five statements,
`RootValueIn` is used only for `TopStart'`; the other four only for `CrossLexFor IsUpper`.
-/

namespace OmegaY.Official.Recon.FinalStageE

open Classification.Proofs.ChainCorr.LowerChain (TopStep)
open Classification.Proofs.ChainCorr.TopStartFix (TopStart')

/-- **The five remaining open statements, in one `Prop`.** -/
def FinalOpen : Prop :=
  TSQ.RVP.RootValueIn ∧ CrossUpperQ.PaONoGapHi ∧ CrossUpperQ.CutRightTopHi ∧
    CrossUpperQ.SeamChainX ∧ CrossUpperQ.QRootRowGe

/-- **`TopStep` holds** (no hypothesis). -/
theorem topStep_final : TopStep :=
  TopChain.topStep_of_parts TopChain.Seam.SRT.topStepLoRoot
    (TopChain.topStepLoJump_of_jumpLaw LRC.jumpLawHolds TopChain.lowExpCopy)

/-- **`TopStart'` from `RootValueIn`.** -/
theorem topStart'_final (hRV : TSQ.RVP.RootValueIn) : TopStart' :=
  TSQ.topStart'_of_cutParent_rootValueIn TopChain.Seam.CPN.cutParentNT hRV

/-- **`CrossLexFor IsUpper` from the five open statements.** -/
theorem crossLexFor_upper_final (hRV : TSQ.RVP.RootValueIn) (hPG : CrossUpperQ.PaONoGapHi)
    (hCR : CrossUpperQ.CutRightTopHi) (hSC : CrossUpperQ.SeamChainX)
    (hRG : CrossUpperQ.QRootRowGe) : CrossLexFor IsUpper :=
  CrossUpperQ.crossLexFor_upper_of_chain topStep_final (topStart'_final hRV) hSC hRG hPG hCR

/-- **`BlockReconstruction` from the five open statements.** -/
theorem blockReconstruction_of_stageE (hRV : TSQ.RVP.RootValueIn)
    (hPG : CrossUpperQ.PaONoGapHi) (hCR : CrossUpperQ.CutRightTopHi)
    (hSC : CrossUpperQ.SeamChainX) (hRG : CrossUpperQ.QRootRowGe) :
    Dimension.BlockReconstruction :=
  blockReconstruction_of_reconstructionHolds
    (TopStartFixAssembly.reconstructionHolds_of_stageC' topStep_final (topStart'_final hRV)
      (CCL.rootPass_plain_of topStep_final (topStart'_final hRV) TopChain.Seam.CPN.cutParentNT)
      CCL.lexImg_plain_final CCL.lexImg_clean_final
      (crossLexFor_upper_final hRV hPG hCR hSC hRG))

/-- **`KeyLeRest` from the five open statements.** -/
theorem keyLeRest_of_stageE (hRV : TSQ.RVP.RootValueIn)
    (hPG : CrossUpperQ.PaONoGapHi) (hCR : CrossUpperQ.CutRightTopHi)
    (hSC : CrossUpperQ.SeamChainX) (hRG : CrossUpperQ.QRootRowGe) :
    Classification.KeyLeRest :=
  Classification.Proofs.ChainCorr.TopStartFix.keyLeRest_pkg3' topStep_final (topStart'_final hRV)
    (Classification.Proofs.ChainCorr.NonTop.nonTopStep_of_reconstruction
      (blockReconstruction_of_stageE hRV hPG hCR hSC hRG))
    Classification.Proofs.ChainCorr.NonTop.startRelNT
    Classification.Proofs.ChainCorr.NonTop.startRootNT TopChain.Seam.CPN.boundaryChain
    Classification.Proofs.P3T.cutJumpRootRow Classification.Proofs.P3T.cutRunTop

/-- **Well-foundedness of the official ω-Y expansion from the five open statements.** -/
theorem wellFounded_of_stageE (hRV : TSQ.RVP.RootValueIn)
    (hPG : CrossUpperQ.PaONoGapHi) (hCR : CrossUpperQ.CutRightTopHi)
    (hSC : CrossUpperQ.SeamChainX) (hRG : CrossUpperQ.QRootRowGe) :
    WellFounded Descent.Step :=
  CrossUpperQ.wellFounded_of_stageC_QX TopChain.Seam.SRT.topStepLoRoot
    (TSQ.topStartLoRootW_of_cutParent TopChain.Seam.CPN.cutParentNT) TSQ.BTL.startRootTopUp
    (TSQ.RVP.topStartPaOUp_of_rootValueIn hRV) TSQ.topStartCutRight
    TopChain.Seam.CPN.boundaryChain Classification.Proofs.P3T.cutJumpRootRow
    Classification.Proofs.P3T.cutRunTop
    (CCL.rootPass_plain_of topStep_final (topStart'_final hRV) TopChain.Seam.CPN.cutParentNT)
    CCL.lexImg_plain_final CCL.lexImg_clean_final hSC hRG hPG hCR

/-- **The same through `ControlProof.wellFounded_of_block_keys` directly.** -/
theorem wellFounded_of_stageE' (hRV : TSQ.RVP.RootValueIn)
    (hPG : CrossUpperQ.PaONoGapHi) (hCR : CrossUpperQ.CutRightTopHi)
    (hSC : CrossUpperQ.SeamChainX) (hRG : CrossUpperQ.QRootRowGe) :
    WellFounded Descent.Step :=
  Classification.ControlProof.wellFounded_of_block_keys
    (blockReconstruction_of_stageE hRV hPG hCR hSC hRG)
    (keyLeRest_of_stageE hRV hPG hCR hSC hRG)

/-- **Well-foundedness from `FinalOpen`.** -/
theorem wellFounded_of_finalOpen (h : FinalOpen) : WellFounded Descent.Step :=
  wellFounded_of_stageE h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

/-- **No infinite chain of expansions**, from `FinalOpen`: there is no sequence
`f 0, f 1, f 2, …` with `f (k+1)` an expansion of `f k` for every `k`. -/
theorem no_infinite_expansion_of_finalOpen (h : FinalOpen) (f : Nat → List Nat) :
    ¬ ∀ k, Descent.Step (f (k + 1)) (f k) := by
  intro hf
  have key : ∀ x, ∀ k, f k = x → False := by
    intro x
    induction x using (wellFounded_of_finalOpen h).induction with
    | _ x ih =>
      intro k hk
      exact ih (f (k + 1)) (hk ▸ hf k) (k + 1) rfl
  exact key (f 0) 0 rfl

end OmegaY.Official.Recon.FinalStageE

#print axioms OmegaY.Official.Recon.FinalStageE.topStep_final
#print axioms OmegaY.Official.Recon.FinalStageE.topStart'_final
#print axioms OmegaY.Official.Recon.FinalStageE.crossLexFor_upper_final
#print axioms OmegaY.Official.Recon.FinalStageE.blockReconstruction_of_stageE
#print axioms OmegaY.Official.Recon.FinalStageE.keyLeRest_of_stageE
#print axioms OmegaY.Official.Recon.FinalStageE.wellFounded_of_stageE
#print axioms OmegaY.Official.Recon.FinalStageE.wellFounded_of_stageE'
#print axioms OmegaY.Official.Recon.FinalStageE.wellFounded_of_finalOpen
#print axioms OmegaY.Official.Recon.FinalStageE.no_infinite_expansion_of_finalOpen
