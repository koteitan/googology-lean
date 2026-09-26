/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/TSQMain.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TSQRoot
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TSQPaO
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TSQRootTop
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TSQAscUp

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# `TopStart'` from four named statements (`TSQ`)

`TopStartFixParts.topStart'_of_parts4` builds `TopStart'` from the four open parts
`TopStartLoRootW`, `StartRootTopUp`, `TopStartPaOUp`, `TopStartCutRight`. Each is reduced here:

| part | from | file |
|---|---|---|
| `TopStartLoRootW` | `Seam.CutParentNT` (open, another package) | `TSQRoot.lean` |
| `StartRootTopUp` | `BiTopLow` (open) | `TSQRootTop.lean` |
| `TopStartPaOUp` | `AscUp` (about `M(s)` alone), from `RootValue` (open, about `M(s)` alone) | `TSQPaO.lean`, `TSQAscUp.lean` |
| `TopStartCutRight` | `CutTopGap` (open) | `TSQCutRight.lean` |

* `topStart'_of_TSQ : CutParentNT → BiTopLow → AscUp → CutTopGap → TopStart'`;
* `topStart'_of_TSQ' : CutParentNT → BiTopLow → RootValue → CutTopGap → TopStart'`.
-/

namespace OmegaY.Official.Recon.TSQ

/-- **`TopStart'` from `CutParentNT`, `BiTopLow`, `AscUp`, `CutTopGap`.** -/
theorem topStart'_of_TSQ (hCP : Recon.TopChain.Seam.CutParentNT) (hB : BiTopLow) (hA : AscUp)
    (hG : CutTopGap) : Classification.Proofs.ChainCorr.TopStartFix.TopStart' :=
  TopStartFixParts.topStart'_of_parts4 (topStartLoRootW_of_cutParent hCP)
    (startRootTopUp_of_biTopLow hB) (topStartPaOUp_of_ascUp hA) (topStartCutRight_of_gap hG)

/-- **`TopStart'` from `CutParentNT`, `BiTopLow`, `RootValue`, `CutTopGap`.** -/
theorem topStart'_of_TSQ' (hCP : Recon.TopChain.Seam.CutParentNT) (hB : BiTopLow)
    (hR : RootValue) (hG : CutTopGap) : Classification.Proofs.ChainCorr.TopStartFix.TopStart' :=
  topStart'_of_TSQ hCP hB (ascUp_of_rootValue hR) hG

end OmegaY.Official.Recon.TSQ

#print axioms OmegaY.Official.Recon.TSQ.topStart'_of_TSQ
#print axioms OmegaY.Official.Recon.TSQ.topStart'_of_TSQ'
