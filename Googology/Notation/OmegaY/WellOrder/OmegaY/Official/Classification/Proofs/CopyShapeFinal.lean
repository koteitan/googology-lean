/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CopyShapeFinal.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeOrderLegProof

set_option backward.do.legacy false

/-!
# The shape of copied columns: the final statements

This file only collects the proved statements about the copied columns of a block `i ≥ 1`
(stage A of `PLAN.md`), each restated by its type, with no hypothesis.

| statement | proof | file |
|---|---|---|
| `Recon.LowerPB.Emitted` | `Found.emitted` | `CopyShapeFound.lean` |
| `ChainCorr.CopyEmitted` | `NoMA.copyEmitted` | `CopyShapeNoMA.lean` |
| `ChainCorr.CopyFirst` | `NoMA.copyFirst` | `CopyShapeNoMA.lean` |
| `ChainCorr.Inner.CopyEmitted` | `NoMA.inner_copyEmitted` | `CopyShapeNoMA.lean` |
| `ChainCorr.Inner.CopyFirst` | `NoMA.inner_copyFirst` | `CopyShapeNoMA.lean` |
| `CopyShape.MHHolds` (MH) | `MHProof.mhHolds` | `CopyShapeMH.lean` |
| MH for every block context | `Found.mhBlock` | `CopyShapeFound.lean` |
| `NoMA.CopyOrderSame` | `NoMA.copyOrderSame` | `CopyShapeNoMA.lean` |
| `NoMA.CopyOrderLeg` (for the false `CopyOrder`) | `ProfileLeg.copyOrderLeg` | `CopyShapeOrderLegProof.lean` |
| `ProfileLeg.NonCutOrderLeg` (for the false `NonCutOrder`) | `ProfileLeg.nonCutOrderLeg` | `CopyShapeProfileLegOrder.lean` |
| `ProfileLeg.CutBetweenLeg` (for the false `CutBetween`) | `ProfileLeg.cutBetweenLeg` | `CopyShapeProfileLegCut.lean` |
| a column and a leg column ascend together below the node | `AscLeg.ascLeg`, `AscLeg.ascLegLe` | `CopyShapeAscLeg.lean` |
| the row of a non-cut lower copy (`Ψ`) | `ProfileLeg.lowerT_formula` | `CopyShapeProfileLegOrder.lean` |
| where a lower gap copy lies (`Ψ`) | `ProfileLeg.lowerT_cut` | `CopyShapeCutForm.lean` |

The users of the false `NonCutOrder`, `CutBetween` (`LowerPB.sameRow`, `LowerPB.legOrder`) are
restated without them in `CopyShapeProfileLeg.lean`: `ProfileLeg.sameRowLeg nonCutOrderLeg`
needs only `LowerPB.CutLeg`, and `ProfileLeg.legOrderLeg nonCutOrderLeg cutBetweenLeg` needs
only `LowerPB.CutOrder` (both open, not part of this stage).

(MA) is false (`CopyShapeMAFalse.lean`), and so are `CopyOrder`, `NonCutOrder`, `CutBetween`;
none of them is used.
-/

namespace OmegaY.Official.Classification.Proofs.CopyShape.Final

open Classification Proofs

theorem emitted : Recon.LowerPB.Emitted := Found.emitted
theorem copyEmitted : ChainCorr.CopyEmitted := NoMA.copyEmitted
theorem copyFirst : ChainCorr.CopyFirst := NoMA.copyFirst
theorem inner_copyEmitted : ChainCorr.Inner.CopyEmitted := NoMA.inner_copyEmitted
theorem inner_copyFirst : ChainCorr.Inner.CopyFirst := NoMA.inner_copyFirst
theorem mhHolds : MHHolds := MHProof.mhHolds
theorem copyOrderSame : NoMA.CopyOrderSame := NoMA.copyOrderSame
theorem copyOrderLeg : NoMA.CopyOrderLeg := ProfileLeg.copyOrderLeg
theorem nonCutOrderLeg : ProfileLeg.NonCutOrderLeg := ProfileLeg.nonCutOrderLeg
theorem cutBetweenLeg : ProfileLeg.CutBetweenLeg := ProfileLeg.cutBetweenLeg

end OmegaY.Official.Classification.Proofs.CopyShape.Final

#print axioms OmegaY.Official.Classification.Proofs.CopyShape.Final.emitted
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.Final.copyEmitted
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.Final.copyFirst
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.Final.inner_copyEmitted
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.Final.inner_copyFirst
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.Final.mhHolds
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.Final.copyOrderSame
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.Final.copyOrderLeg
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.Final.nonCutOrderLeg
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.Final.cutBetweenLeg
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.AscLeg.ascLeg
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.AscLeg.ascLegLe
