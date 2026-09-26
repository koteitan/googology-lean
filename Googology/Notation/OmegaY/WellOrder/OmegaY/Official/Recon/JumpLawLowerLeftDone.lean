/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/JumpLawLowerLeftDone.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawLowerLeftProof
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.LiftLegRightProof

set_option backward.do.legacy false

/-!
# `LowerPairsLeft` holds

`LowerPairsLeft` (`JumpLawLowerLeft.lean`: the jump law for the lower pairs of a column of block
`i ≥ 1` whose upper node has its leg in a column `l < c_r`) follows from `LiftLegRight`
(`lowerPairsLeft_of_lift`, `JumpLawLowerLeftProof.lean`), and `LiftLegRight` is proved
(`liftLegRight`, `Classification/Proofs/LiftLegRightProof.lean`). So `LowerPairsLeft` has no open
hypothesis, and the jump law needs only the two row laws `LowerRowsCopy` and `LowerRowsBoundary`:

  `lowerPairsLeft_holds : LowerPairsLeft`
  `jumpLawHolds_of_lowerRowsCases : LowerRowsCopy → LowerRowsBoundary → JumpLawHolds`
-/

namespace OmegaY.Official.Recon.LowerLeftDone

open Canonical Expansion Dimension RowLaw JumpLaw JumpLawLower JumpLawLowerLeft

/-- **`LowerPairsLeft` holds.** -/
theorem lowerPairsLeft_holds : LowerPairsLeft :=
  LowerLeftProof.lowerPairsLeft_of_lift LowerPB.LiftLegPf.liftLegRight

/-- **The jump law from the two row laws of the lower part.** -/
theorem jumpLawHolds_of_lowerRowsCases (hC : LowerRowsCopy) (hB : LowerRowsBoundary) :
    RowLaw.JumpLawHolds :=
  jumpLawHolds_of_lowerCases_left hC hB lowerPairsLeft_holds

end OmegaY.Official.Recon.LowerLeftDone

#print axioms OmegaY.Official.Recon.LowerLeftDone.lowerPairsLeft_holds
#print axioms OmegaY.Official.Recon.LowerLeftDone.jumpLawHolds_of_lowerRowsCases
