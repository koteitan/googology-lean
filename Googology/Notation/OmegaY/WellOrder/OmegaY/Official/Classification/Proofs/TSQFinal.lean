/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/TSQFinal.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TSQMain
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TSQRootValueParts
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TSQBiTopMain
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TSQCutGapMain
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TSQRootValueX0

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# `TopStart'` from `CutParentNT` and `RootValueIn` (`TSQ`)

The four parts of `TopStart'` (`TopStartFixParts.topStart'_of_parts4`):

| part | status | file |
|---|---|---|
| `TopStartLoRootW` | from `CutParentNT` (stage-D statement, another package) | `TSQRoot.lean` |
| `StartRootTopUp` | **proved** (`BiTopLow` proved) | `TSQBiTop*.lean`, `TSQRootTop.lean` |
| `TopStartPaOUp` | from `RootValueIn` (open, about `M(s)` alone) | `TSQRootValue*.lean`, `TSQAscUp.lean`, `TSQPaO.lean` |
| `TopStartCutRight` | **proved** (`CutTopGap` proved) | `TSQCutGap*.lean`, `TSQCutRight.lean` |

`RootValueIn` is `RootValue` in its one remaining case: the row `C` of `o` is not the bottom row
(its finite coefficient is `0`), the root column has a node `g⁺` above `g = (c_r, C)` below `τ`,
and `o` is strictly left of the last column `x₀`. The other cases of `RootValue` are proved
(`RVP.rootValue_of_hi`, `RVP.rootValueHi_of_in`).

* `topStart'_of_cutParent_rootValueHi : CutParentNT → RootValueHi → TopStart'`;
* `topStart'_of_cutParent_rootValueIn : CutParentNT → RootValueIn → TopStart'`.
-/

namespace OmegaY.Official.Recon.TSQ

/-- **`TopStartCutRight` holds.** -/
theorem topStartCutRight : TopStartFixParts.TopStartCutRight :=
  topStartCutRight_of_gap CTG.cutTopGap

/-- **`TopStart'` from `CutParentNT` and `RootValueHi`.** -/
theorem topStart'_of_cutParent_rootValueHi (hCP : Recon.TopChain.Seam.CutParentNT)
    (hRV : RVP.RootValueHi) : Classification.Proofs.ChainCorr.TopStartFix.TopStart' :=
  TopStartFixParts.topStart'_of_parts4 (topStartLoRootW_of_cutParent hCP) BTL.startRootTopUp
    (RVP.topStartPaOUp_of_rootValueHi hRV) topStartCutRight

/-- **`TopStart'` from `CutParentNT` and `RootValueIn`.** -/
theorem topStart'_of_cutParent_rootValueIn (hCP : Recon.TopChain.Seam.CutParentNT)
    (hRV : RVP.RootValueIn) : Classification.Proofs.ChainCorr.TopStartFix.TopStart' :=
  topStart'_of_cutParent_rootValueHi hCP (RVP.rootValueHi_of_in hRV)

end OmegaY.Official.Recon.TSQ

#print axioms OmegaY.Official.Recon.TSQ.BTL.biTopLow
#print axioms OmegaY.Official.Recon.TSQ.BTL.startRootTopUp
#print axioms OmegaY.Official.Recon.TSQ.CTG.cutTopGap
#print axioms OmegaY.Official.Recon.TSQ.topStartCutRight
#print axioms OmegaY.Official.Recon.TSQ.RVP.rootValue_of_hi
#print axioms OmegaY.Official.Recon.TSQ.topStart'_of_cutParent_rootValueHi
#print axioms OmegaY.Official.Recon.TSQ.RVP.rootValueHi_of_in
#print axioms OmegaY.Official.Recon.TSQ.topStart'_of_cutParent_rootValueIn
