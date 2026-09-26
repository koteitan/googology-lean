/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/PBStageBFinal.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.PBStageBBndSim

set_option backward.do.legacy false

/-!
# Stage B: `LowerParentBelowHolds` (summary)

The results of stage B for the lower part of the parent chain, with the statements as they are
worded in `ParentBelow.lean` and `ParentBelowLowerProfile.lean`:

* `LowerParentBelowHolds` and `ParentBelowHolds` hold (no hypothesis).
* Of the parts of `Profile7`: `CutOrder`, `CutLeg`, `Lift` hold; `Emitted` (`CopyShape.Found`),
  `NonCutOrderLeg`, `CutBetweenLeg` (`CopyShapeProfileLeg*.lean`) were proved before;
  **`Boundary` is false** (root column `0`, `(1,3)[1]`; checked by `#guard`), and its form for
  `c_r ≥ 1`, `BoundaryPos`, holds.
* New statements on the way, all proved: `GenLeg` (about `M(s)`), `RootShadowOut`,
  `RootShadowZero`, `BoundaryPos`.
-/

namespace OmegaY.Official.Recon.LowerPB.StageB

theorem final_lowerParentBelowHolds : OmegaY.Official.Recon.LowerParentBelowHolds :=
  lowerParentBelowHolds

theorem final_parentBelowHolds : OmegaY.Official.Recon.ParentBelowHolds := parentBelowHolds

theorem final_cutOrder : OmegaY.Official.Recon.LowerPB.CutOrder :=
  Classification.Proofs.CopyShape.PBStageB.cutOrder

theorem final_cutLeg : OmegaY.Official.Recon.LowerPB.CutLeg :=
  Classification.Proofs.CopyShape.PBStageB.cutLeg

theorem final_lift : OmegaY.Official.Recon.LowerPB.Lift :=
  Classification.Proofs.CopyShape.PBStageB.lift

theorem final_genLeg : Classification.Proofs.CopyShape.PBStageB.GenLeg :=
  Classification.Proofs.CopyShape.PBStageB.genLeg

theorem final_boundaryPos : BoundaryPos := boundaryPos

theorem final_rootShadowOut : RootShadowOut := rootShadowOut

theorem final_not_boundary (hc : bndCheck = true) : ¬ OmegaY.Official.Recon.LowerPB.Boundary :=
  not_boundary_of_check hc

end OmegaY.Official.Recon.LowerPB.StageB

#print axioms OmegaY.Official.Recon.LowerPB.StageB.final_lowerParentBelowHolds
#print axioms OmegaY.Official.Recon.LowerPB.StageB.final_parentBelowHolds
#print axioms OmegaY.Official.Recon.LowerPB.StageB.final_cutOrder
#print axioms OmegaY.Official.Recon.LowerPB.StageB.final_cutLeg
#print axioms OmegaY.Official.Recon.LowerPB.StageB.final_lift
#print axioms OmegaY.Official.Recon.LowerPB.StageB.final_genLeg
#print axioms OmegaY.Official.Recon.LowerPB.StageB.final_boundaryPos
#print axioms OmegaY.Official.Recon.LowerPB.StageB.final_rootShadowOut
#print axioms OmegaY.Official.Recon.LowerPB.StageB.final_not_boundary
