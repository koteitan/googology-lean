/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/RPLFix.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RPLLexMain
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.TopStartFixRecon

set_option backward.do.legacy false

/-!
# The results of `RPLRoot.lean` and `RPLLexMain.lean` with the corrected start `TopStart'`

`LowerChain.TopStart` is false (`TopStartLoRightFalse.lean`); the corrected start `TopStart'`
(`TopStartFix.lean`) gives `QStand` (`qStand_of_topStart'`, `TopStartFixRecon.lean`), which is all
that `RootPass IsPlain` uses of the start.

* `rootPass_plain_fix : TopStep → TopStart' → SeamStep → SeamStart → RootPass IsPlain`;
* `crossLexFor_plain_fix : TopStep → TopStart' → SeamStep → SeamStart → CopyCountLe →
  CrossLexFor IsPlain`;
* `crossLexFor_clean_fix : TopStep → TopStart' → CopyCountLe → CrossLexFor IsClean`.
-/

namespace OmegaY.Official.Recon.RPLLex

open Canonical Expansion Geometry Frame Classification
open Classification.Proofs.ChainCorr.LowerChain (TopStep)
open Classification.Proofs.ChainCorr.TopStartFix (TopStart')

/-- **`RootPass IsPlain`** from `TopStep`, the corrected `TopStart'` and the seam statements. -/
theorem rootPass_plain_fix (hTS : TopStep) (hTSt : TopStart') (hSS : RPLRoot.SeamStep)
    (hSt : RPLRoot.SeamStart) : CrossPlainPos.RootPass IsPlain :=
  RPLRoot.rootPass_plain_of_qStand (LowerChainRecon.copyStepLower_of_topStep hTS)
    (TopStartFixRecon.qStand_of_topStart' hTSt (CrossPlainPos.belowSrc_plain Pk4.emitBelow_plain)
      CrossPlain.isPlain_notUpper)
    hSS hSt

/-- **`CrossLexFor IsPlain`** with `TopStart'`. -/
theorem crossLexFor_plain_fix (hTS : TopStep) (hTSt : TopStart') (hSS : RPLRoot.SeamStep)
    (hSt : RPLRoot.SeamStart) (hCC : CopyCountLe) : CrossLexFor IsPlain :=
  TopStartFixRecon.crossLexFor_plain_pk4' hTS hTSt (rootPass_plain_fix hTS hTSt hSS hSt)
    (lexImg_plain hCC)

/-- **`CrossLexFor IsClean`** with `TopStart'`. -/
theorem crossLexFor_clean_fix (hTS : TopStep) (hTSt : TopStart') (hCC : CopyCountLe) :
    CrossLexFor IsClean :=
  TopStartFixRecon.crossLexFor_clean_pk4' hTS hTSt (lexImg_clean hCC)

end OmegaY.Official.Recon.RPLLex

#print axioms OmegaY.Official.Recon.RPLLex.rootPass_plain_fix
#print axioms OmegaY.Official.Recon.RPLLex.crossLexFor_plain_fix
#print axioms OmegaY.Official.Recon.RPLLex.crossLexFor_clean_fix
