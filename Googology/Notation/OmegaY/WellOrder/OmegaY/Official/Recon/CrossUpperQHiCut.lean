/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CrossUpperQHiCut.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossUpperQ
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TSQFinal

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# `CutRightTopHi` holds

`CutRightTopHi` (`CrossUpperQ.lean`): the top copy `u` (block `i ≥ 1`) of an origin `o` below `τ`
is a gap copy, the leg `l` of `o` is right of `c_r`, and the node `o⁺` above `o` is at a row
`≥ τ`. Then `pe = hAM_R(φ(l), row u)` is the top copy of `pa = hAM_M(l, row o)` (`TopNode`).

The proved `TSQ.topNode_cutRight` (`TSQCutRight.lean`) gives `TopNode pe pa` from `CutTopGap`
in the setting of `TopStartCutRight` without any hypothesis on the node above `o`, and
`CutTopGap` is proved (`TSQ.CTG.cutTopGap`, `TSQCutGapMain.lean`). The hypothesis
`HasAboveHi` is not used.

Result: `cutRightTopHi : CutRightTopHi`.
-/

namespace OmegaY.Official.Recon.CrossUpperQ.QHi

/-- **`CutRightTopHi` holds.** -/
theorem cutRightTopHi : CutRightTopHi := by
  intro s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv hl hpa hpe
    hlo hlr hcut _
  exact OmegaY.Official.Recon.TSQ.topNode_cutRight OmegaY.Official.Recon.TSQ.CTG.cutTopGap hrun
    hTop hi0 hin hx hes hj htop hcu hcv hl hpa hpe hlo hlr hcut

end OmegaY.Official.Recon.CrossUpperQ.QHi

#print axioms OmegaY.Official.Recon.CrossUpperQ.QHi.cutRightTopHi
