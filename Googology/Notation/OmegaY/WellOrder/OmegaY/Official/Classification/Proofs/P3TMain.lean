/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/P3TMain.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.P3TRootRow

set_option backward.do.legacy false

/-!
# Package 3 without its row facts (`P3T`)

The two open row facts of package 3 are proved: `CutJumpRootRow` (`P3TRootRow.lean`) and
`CutRunTop` (`P3TRunTop.lean`). So:

* `cutJump`: `CutJump` holds (`Pkg3.cutJump_of_rows`, `Pkg3.cutJumpRun_of_top`);
* `package3_of`: the four gap-copy statements of package 3 from `TopStep`, `NonTopStep` and
  `BoundaryChain` alone;
* `keyLeRest_of`: `KeyLeRest` from the statements of packages 1 and 2 and `BoundaryChain`.
  **Warning:** its hypothesis `TopStart` is false (PLAN.md; counterexample
  `(1,20,15,23,3,10,28,22)[1]`), so `keyLeRest_of` is vacuous. Use `cutJumpRootRow` and
  `cutRunTop` to discharge the hypotheses `CutJumpRootRow`, `CutRunTop` of the `TopStart'` route.
-/

namespace OmegaY.Official.Classification.Proofs.P3T

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr ChainCorr.CutParts ChainCorr.LowerChain ChainCorr.Pkg3

/-- **`CutJump` holds.** -/
theorem cutJump : CutJump :=
  cutJump_of_rows cutJumpRootRow (cutJumpRun_of_top cutRunTop)

/-- **The four gap-copy statements of package 3**, from `TopStep`, `NonTopStep` and
`BoundaryChain`. -/
theorem package3_of (hTS : TopStep) (hNS : NonTopStep) (hB : BoundaryChain) :
    StepCut ∧ CutJump ∧ CutStartCopyNT ∧ CutStartRootNT :=
  package3 hTS hNS hB cutJumpRootRow cutRunTop

/-- **`KeyLeRest`** from the statements of packages 1 and 2 and `BoundaryChain`.
**Vacuous:** the hypothesis `TopStart` is false; do not use this theorem in the final assembly. -/
theorem keyLeRest_of (hTS : TopStep) (hTSt : TopStart) (hNS : NonTopStep)
    (hRel : StartRelNT) (hRootNT : StartRootNT) (hB : BoundaryChain) : KeyLeRest :=
  keyLeRest_pkg3 hTS hTSt hNS hRel hRootNT hB cutJumpRootRow cutRunTop

end OmegaY.Official.Classification.Proofs.P3T

#print axioms OmegaY.Official.Classification.Proofs.P3T.cutJump
#print axioms OmegaY.Official.Classification.Proofs.P3T.package3_of
#print axioms OmegaY.Official.Classification.Proofs.P3T.keyLeRest_of
