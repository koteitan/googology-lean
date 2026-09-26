/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/LRCJump.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LRCBnd

set_option backward.do.legacy false

/-!
# The jump law holds

`LowerRowsCopy` (`lowerRowsCopy_holds`, `LRCCopy.lean`) and `LowerRowsBoundary`
(`lowerRowsBoundary_holds`, `LRCBnd.lean`) are proved, so `jumpLawHolds_of_lowerRowsCases`
(`JumpLawLowerLeftDone.lean`) gives the jump law `RowLaw.JumpLawHolds` with no open hypothesis.
-/

namespace OmegaY.Official.Recon.LRC

/-- **The jump law of the output.** -/
theorem jumpLawHolds : RowLaw.JumpLawHolds :=
  LowerLeftDone.jumpLawHolds_of_lowerRowsCases lowerRowsCopy_holds lowerRowsBoundary_holds

end OmegaY.Official.Recon.LRC

#check (OmegaY.Official.Recon.LRC.lowerRowsCopy_holds :
  OmegaY.Official.Recon.JumpLawLower.LowerRowsCopy)
#check (OmegaY.Official.Recon.LRC.lowerRowsBoundary_holds :
  OmegaY.Official.Recon.JumpLawLower.LowerRowsBoundary)
#print axioms OmegaY.Official.Recon.LRC.lowerRowsCopy_holds
#print axioms OmegaY.Official.Recon.LRC.lowerRowsBoundary_holds
#print axioms OmegaY.Official.Recon.LRC.jumpLawHolds
