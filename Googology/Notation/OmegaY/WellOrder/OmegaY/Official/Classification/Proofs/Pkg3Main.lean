/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/Pkg3Main.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.Pkg3Run
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.LowerChainMain

set_option backward.do.legacy false

/-!
# Package 3: the gap-copy statements of `KeyLeRest`

The four statements `StepCut`, `CutJump` (`ChainCorrCut.lean`), `CutStartCopyNT`,
`CutStartRootNT` (`LowerChain.lean`):

* `CutStartCopyNT`: **proved** (`cutStartCopyNT`, from `CutParts.cutStartCopy'`).
* `CutStartRootNT` from `BoundaryChain` (`ChainCorrStartRoot.lean`, open, numerically true on the
  large-value audit of notes/05): `cutStartRootNT_of_boundaryChain` (the argument of
  `CutParts.cutStartRoot_of_parts` with the proved `SRFixPa.cutOriginReach`).
* `CutJump` from the two row facts `CutJumpRootRow`, `CutJumpRun` (`Pkg3Jump.lean`, open, new);
  `CutJumpRun` from `CutRunTop` (`Pkg3Run.lean`, open, new: the dual of the proved `CutRunLow`).
* `StepCut` from `TopStep`, `NonTopStep` (stage B), `CutStartRootNT` and `CutJump`
  (`Pkg3StepCut.lean`).

`package3`: all four from `TopStep`, `NonTopStep`, `BoundaryChain`, `CutJumpRootRow`,
`CutRunTop`. `keyLeRest_pkg3`: `KeyLeRest` from these and the statements of packages 1 and 2.

## Numerical tests (`reference/official/pkg3-rows.cjs`, the rule of `omegay-trace.cjs`)

`n = 1, 2, 3` (an input is not expanded for a larger `n` once its output has more than 800
nodes or a column with more than 80 nodes). Counts are gap copies (`CutJumpRootRow`,
`CutJumpRun`: those with `pe` strictly below `u`). No failure anywhere.

| sample | expansions | `CutJump` | `CutJumpRootRow` | `CutJumpRun` | `CutRunTop` |
|---|---:|---:|---:|---:|---:|
| all legal, length `≤ 6`, entries `≤ 12` | 723113 | 3841063 | 1933614 | 95767 | 285607 |
| `legbelowtop-bad64.json`, `known-counterexamples.json` | 243 | 3012 | 290 | 0 | 838 |
| random, length `≤ 8`, entries `≤ 20` (`--random 20000,8,20,11`) | 36260 | 436189 | 251082 | 17018 | 43746 |
| random, length `≤ 8`, entries `≤ 30` (`4000,8,30,17`, `M(s)` `≤ 100` nodes) | 7602 | 112112 | 69686 | 5242 | 10929 |
| random, length `≤ 7`, entries `≤ 40` (`3000,7,40,5`, `M(s)` `≤ 60` nodes) | 3852 | 50647 | 31466 | 3327 | 6254 |
| random, length `≤ 7`, entries `≤ 40` (`1500,7,40,23`, `M(s)` `≤ 200` nodes) | 2695 | 57066 | 37031 | 6042 | 8728 |

`BoundaryChain` has no failure on the samples A–F and K of notes/05-large-value-audit.md.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.Pkg3

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr.CutParts ChainCorr.LowerChain

/-- **`CutStartRootNT` from `BoundaryChain`.** -/
theorem cutStartRootNT_of_boundaryChain (hB : BoundaryChain) : CutStartRootNT :=
  cutStartRootNT_of_cutStartRoot (cutStartRoot_of_parts hB SRFixPa.cutOriginReach)

/-- **The four gap-copy statements of package 3.** -/
theorem package3 (hTS : TopStep) (hNS : NonTopStep) (hB : BoundaryChain)
    (hRoot : CutJumpRootRow) (hTop : CutRunTop) :
    StepCut ∧ CutJump ∧ CutStartCopyNT ∧ CutStartRootNT := by
  have hCR := cutStartRootNT_of_boundaryChain hB
  have hCJ := cutJump_of_rows hRoot (cutJumpRun_of_top hTop)
  exact ⟨stepCut_of_lower hTS hNS hCR hCJ, hCJ, cutStartCopyNT, hCR⟩

/-- **`KeyLeRest`** from the statements of packages 1 and 2 and the open statements of
package 3. -/
theorem keyLeRest_pkg3 (hTS : TopStep) (hTSt : TopStart) (hNS : NonTopStep)
    (hRel : StartRelNT) (hRootNT : StartRootNT) (hB : BoundaryChain)
    (hRoot : CutJumpRootRow) (hTop : CutRunTop) : KeyLeRest := by
  obtain ⟨h1, h2, h3, h4⟩ := package3 hTS hNS hB hRoot hTop
  exact keyLeRest_of_lower_main hTS hTSt hNS hRel hRootNT h1 h2 h3 h4

end OmegaY.Official.Classification.Proofs.ChainCorr.Pkg3

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Pkg3.cutStartCopyNT
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Pkg3.stepCut_of_lower
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Pkg3.cutJump_of_rows
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Pkg3.cutJumpRun_of_top
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Pkg3.cutStartRootNT_of_boundaryChain
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Pkg3.package3
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Pkg3.keyLeRest_pkg3
