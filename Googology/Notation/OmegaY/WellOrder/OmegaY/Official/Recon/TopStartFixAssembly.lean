/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/TopStartFixAssembly.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LRCJump
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CutPredBoundary
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.PBStageBFinal
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossKinds
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RowLawColumn
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.FirstEmit
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.Reduction
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.NonTopRecon
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.Pkg3Main
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ControlDominates
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeFound
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TopStartFixPaO
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.TopStartFixRecon

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# `WellFounded Step` with the corrected start `TopStart'`

The same assembly as the final assembly of stage C, with the false `TopStart` (and its false
cases `TopStartLoRoot`, `TopStartLoRight`) replaced by the corrected `TopStart'` and its open
cases (`TopStartFixParts.lean`), and with `CrossLexFor IsUpper` as an open hypothesis: its old
reduction (`SeamLastPosHolds`, `InnerHolds` from `CopyQLower`) is broken, since `CopyQLower` and
`InnerHolds` are false for `(1,21,5,20,30,23,20)[1]` (`TopStartFixRecon.lean`), while
`CrossLexFor IsUpper` itself holds there and on the large-value samples.

| hypothesis | meaning |
|---|---|
| `TopStepLoRoot` | `TopChainMain.lean`, unchanged |
| `TopStartLoRootW` | `l = c_r`: column of `pe` and the chain clause |
| `StartRootTopUp` | `l = c_r`, `o⁺` above `o` below `row t`: the clause on the node above `pa` |
| `TopStartPaOUp` | `l > c_r`, `u` not a gap copy, `pa` at the row of `o`, `o⁺` below `row t`: `TopNode pe pa` |
| `TopStartCutRight` | `l > c_r`, `u` a gap copy: `Rel pe pa`, and `TopNode pe pa` when `o⁺` is below `row t` |
| `BoundaryChain`, `CutJumpRootRow`, `CutRunTop` | package 3, unchanged |
| `RootPass IsPlain`, `LexImg IsPlain`, `LexImg IsClean` | package 4, unchanged |
| `CrossLexFor IsUpper` | the upper kind of the cross case of the parent chain (`CrossKinds.lean`) |

* `reconstructionHolds_of_stageC' : TopStep → TopStart' → RootPass IsPlain → LexImg IsPlain →
  LexImg IsClean → CrossLexFor IsUpper → ReconstructionHolds`;
* `wellFounded_of_topStart' : TopStepLoRoot → TopStart' → BoundaryChain → CutJumpRootRow →
  CutRunTop → RootPass IsPlain → LexImg IsPlain → LexImg IsClean → CrossLexFor IsUpper →
  WellFounded Step`;
* `wellFounded_of_stageC'`: the same with `TopStart'` from its four open cases;
* `wellFounded_of_stageC_noGap`: the same with `PaONoGap` in place of `TopStartPaOUp`.
-/

namespace OmegaY.Official.Recon.TopStartFixAssembly

open Classification.Proofs.ChainCorr.LowerChain (TopStep)
open Classification.Proofs.ChainCorr.TopStartFix (TopStart')

/-- **`ReconstructionHolds` from `TopStep`, `TopStart'` and package 4.** -/
theorem reconstructionHolds_of_stageC' (hTS : TopStep) (hTSt : TopStart')
    (hRP : CrossPlainPos.RootPass IsPlain) (hLP : CrossPlainPos.LexImg IsPlain)
    (hLC : CrossPlainPos.LexImg IsClean) (hU : CrossLexFor IsUpper) :
    Reconstruction.ReconstructionHolds := by
  have hP : CrossLexFor IsPlain := TopStartFixRecon.crossLexFor_plain_pk4' hTS hTSt hRP hLP
  have hC : CrossLexFor IsClean := TopStartFixRecon.crossLexFor_clean_pk4' hTS hTSt hLC
  have hCh : ChainHolds :=
    chainHolds_of_three LowerPB.StageB.parentBelowHolds hP hC CutPredMD.cutPredHolds hU
  exact reconstructionHolds_of_rowLaw_chain (RowLaw.rowLawHolds_of_jumpLaw LRC.jumpLawHolds) hCh

/-- **Well-foundedness from `TopStepLoRoot`, `TopStart'` and packages 3 and 4.** -/
theorem wellFounded_of_topStart'
    (hSR : TopChain.TopStepLoRoot)
    (hTSt : TopStart')
    (hB : Classification.Proofs.ChainCorr.BoundaryChain)
    (hCJR : Classification.Proofs.ChainCorr.Pkg3.CutJumpRootRow)
    (hCRT : Classification.Proofs.ChainCorr.Pkg3.CutRunTop)
    (hRP : CrossPlainPos.RootPass IsPlain)
    (hLP : CrossPlainPos.LexImg IsPlain)
    (hLC : CrossPlainPos.LexImg IsClean)
    (hU : CrossLexFor IsUpper) :
    WellFounded Descent.Step := by
  have hTS : TopStep := TopChain.topStep_of_parts hSR
    (TopChain.topStepLoJump_of_jumpLaw LRC.jumpLawHolds TopChain.lowExpCopy)
  have hBR : Dimension.BlockReconstruction :=
    blockReconstruction_of_reconstructionHolds
      (reconstructionHolds_of_stageC' hTS hTSt hRP hLP hLC hU)
  have hK : Classification.KeyLeRest :=
    Classification.Proofs.ChainCorr.TopStartFix.keyLeRest_pkg3' hTS hTSt
      (Classification.Proofs.ChainCorr.NonTop.nonTopStep_of_reconstruction hBR)
      Classification.Proofs.ChainCorr.NonTop.startRelNT
      Classification.Proofs.ChainCorr.NonTop.startRootNT hB hCJR hCRT
  exact Classification.ControlProof.wellFounded_of_block_keys hBR hK

/-- **Well-foundedness of the official ω-Y expansion from the corrected stage-C statements.** -/
theorem wellFounded_of_stageC'
    (hSR : TopChain.TopStepLoRoot)
    (hTRW : TopStartFixParts.TopStartLoRootW)
    (hTRU : TopStartFixParts.StartRootTopUp)
    (hPaO : TopStartFixParts.TopStartPaOUp)
    (hCutR : TopStartFixParts.TopStartCutRight)
    (hB : Classification.Proofs.ChainCorr.BoundaryChain)
    (hCJR : Classification.Proofs.ChainCorr.Pkg3.CutJumpRootRow)
    (hCRT : Classification.Proofs.ChainCorr.Pkg3.CutRunTop)
    (hRP : CrossPlainPos.RootPass IsPlain)
    (hLP : CrossPlainPos.LexImg IsPlain)
    (hLC : CrossPlainPos.LexImg IsClean)
    (hU : CrossLexFor IsUpper) :
    WellFounded Descent.Step :=
  wellFounded_of_topStart' hSR (TopStartFixParts.topStart'_of_parts4 hTRW hTRU hPaO hCutR) hB
    hCJR hCRT hRP hLP hLC hU

/-- **The same with `PaONoGap` for `TopStartPaOUp`** (`TopStartFixPaO.lean`). -/
theorem wellFounded_of_stageC_noGap
    (hSR : TopChain.TopStepLoRoot)
    (hTRW : TopStartFixParts.TopStartLoRootW)
    (hTRU : TopStartFixParts.StartRootTopUp)
    (hNG : TopStartFixParts.PaONoGap)
    (hCutR : TopStartFixParts.TopStartCutRight)
    (hB : Classification.Proofs.ChainCorr.BoundaryChain)
    (hCJR : Classification.Proofs.ChainCorr.Pkg3.CutJumpRootRow)
    (hCRT : Classification.Proofs.ChainCorr.Pkg3.CutRunTop)
    (hRP : CrossPlainPos.RootPass IsPlain)
    (hLP : CrossPlainPos.LexImg IsPlain)
    (hLC : CrossPlainPos.LexImg IsClean)
    (hU : CrossLexFor IsUpper) :
    WellFounded Descent.Step :=
  wellFounded_of_stageC' hSR hTRW hTRU (TopStartFixParts.topStartPaOUp_of_noGap hNG) hCutR hB
    hCJR hCRT hRP hLP hLC hU

end OmegaY.Official.Recon.TopStartFixAssembly

#print axioms OmegaY.Official.Recon.TopStartFixAssembly.reconstructionHolds_of_stageC'
#print axioms OmegaY.Official.Recon.TopStartFixAssembly.wellFounded_of_topStart'
#print axioms OmegaY.Official.Recon.TopStartFixAssembly.wellFounded_of_stageC'
#print axioms OmegaY.Official.Recon.TopStartFixAssembly.wellFounded_of_stageC_noGap
