/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CrossUpperWAssembly.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossUpperWSim
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.TopStartFixAssembly

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# The assembly with `CrossLexFor IsUpper` from `CopyQLowerW`

`TopStartFixAssembly.wellFounded_of_stageC'` takes `CrossLexFor IsUpper` as an open hypothesis.
Here it is replaced by the weak start `CopyQLowerW` (`CrossUpperWSim.lean`), with `TopStep`
from `TopStepLoRoot` as in that assembly.
-/

namespace OmegaY.Official.Recon.CrossUpperW

/-- **`CrossLexFor IsUpper` from `TopStepLoRoot` and `CopyQLowerW`.** -/
theorem crossLexFor_upper_of_stepLoRoot (hSR : TopChain.TopStepLoRoot) (hQW : CopyQLowerW) :
    CrossLexFor IsUpper :=
  crossLexFor_upper_of_W
    (TopChain.topStep_of_parts hSR
      (TopChain.topStepLoJump_of_jumpLaw LRC.jumpLawHolds TopChain.lowExpCopy)) hQW

/-- **Well-foundedness of the official ω-Y expansion**, with `CrossLexFor IsUpper` replaced
by `CopyQLowerW`. -/
theorem wellFounded_of_stageC_W
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
    (hQW : CopyQLowerW) :
    WellFounded Descent.Step :=
  TopStartFixAssembly.wellFounded_of_stageC' hSR hTRW hTRU hPaO hCutR hB hCJR hCRT hRP hLP hLC
    (crossLexFor_upper_of_stepLoRoot hSR hQW)

end OmegaY.Official.Recon.CrossUpperW

#print axioms OmegaY.Official.Recon.CrossUpperW.crossLexFor_upper_of_stepLoRoot
#print axioms OmegaY.Official.Recon.CrossUpperW.wellFounded_of_stageC_W
