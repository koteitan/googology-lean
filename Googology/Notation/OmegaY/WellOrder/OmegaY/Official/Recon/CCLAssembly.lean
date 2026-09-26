/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CCLAssembly.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CCLMain
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.TopStartFixAssembly
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.P3TMain

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# The assembly with package 4 discharged (`CCL`)

`TopStartFixAssembly.wellFounded_of_stageC'` takes `RootPass IsPlain`, `LexImg IsPlain` and
`LexImg IsClean` as hypotheses. `LexImg IsPlain` and `LexImg IsClean` are proved
(`CCLMain.lean`, from `copyCountLe`), and `RootPass IsPlain` follows from `TopStep`, `TopStart'`
and the open stage-D statement `CutParentNT` (`rootPass_plain_of`). With the proved
`CutJumpRootRow`, `CutRunTop` (`P3T*.lean`) and the reductions of `SeamCut.lean`
(`BoundaryChain` from `CutParentNT`, `TopStepLoRoot` from `CutParentNT` and `StepRootTop`):

* `wellFounded_of_stageD : CutParentNT → StepRootTop → TopStartLoRootW → StartRootTopUp →
  TopStartPaOUp → TopStartCutRight → CrossLexFor IsUpper → WellFounded Step`.

All seven hypotheses are open statements of stage D (`PLAN.md`).
-/

namespace OmegaY.Official.Recon.CCL

open Classification.Proofs.ChainCorr.LowerChain (TopStep)
open Classification.Proofs.ChainCorr.TopStartFix (TopStart')
open TopChain.Seam (CutParentNT StepRootTop)

/-- **Well-foundedness of the official ω-Y expansion from the open stage-D statements.** -/
theorem wellFounded_of_stageD
    (hCP : CutParentNT) (hSRT : StepRootTop)
    (hTRW : TopStartFixParts.TopStartLoRootW)
    (hTRU : TopStartFixParts.StartRootTopUp)
    (hPaO : TopStartFixParts.TopStartPaOUp)
    (hCutR : TopStartFixParts.TopStartCutRight)
    (hU : CrossLexFor IsUpper) :
    WellFounded Descent.Step := by
  have hSR : TopChain.TopStepLoRoot := TopChain.Seam.topStepLoRoot_of_cutParent hCP hSRT
  have hTS : TopStep := TopChain.topStep_of_parts hSR
    (TopChain.topStepLoJump_of_jumpLaw LRC.jumpLawHolds TopChain.lowExpCopy)
  have hTSt : TopStart' := TopStartFixParts.topStart'_of_parts4 hTRW hTRU hPaO hCutR
  exact TopStartFixAssembly.wellFounded_of_stageC' hSR hTRW hTRU hPaO hCutR
    (TopChain.Seam.boundaryChain_of_cutParent hCP) Classification.Proofs.P3T.cutJumpRootRow
    Classification.Proofs.P3T.cutRunTop (rootPass_plain_of hTS hTSt hCP) lexImg_plain_final
    lexImg_clean_final hU

end OmegaY.Official.Recon.CCL

#print axioms OmegaY.Official.Recon.CCL.wellFounded_of_stageD
