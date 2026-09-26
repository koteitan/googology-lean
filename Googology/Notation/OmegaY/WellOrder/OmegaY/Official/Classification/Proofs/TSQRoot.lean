/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/TSQRoot.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TopStartFixParts
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.SeamCut

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# `TopStartLoRootW` from `CutParentNT` (`TSQ`)

`TopStartLoRootW` (`TopStartFixParts.lean`): for the top copy `u` of an origin `o` below `row t`
whose leg is the root column `c_r`, `StandW pe pa`, i.e. `col pe = c_r + w·i` and the chain
clause (the scale-`jump(pa, b)` chain of `R` from `pe` reaches the raw parent `b` of `pa`).

* the column clause: `pe` is looked up in the column `φ(c_r) = c_r + w·i`;
* the chain clause: `pe` is a lower node of the boundary column `B_i` whose origin `ν` (a node
  of `x₀` below `τ`) has `hAM(c_r, row ν) = pa` (`Seam.startRootLookup`, proved), so the chain of
  `M(s)` from `ν` reaches the step `pa → b` (`SRX0.x0Reach`, proved) and `BoundaryChainD` carries
  it to the chain of `pe` (`Seam.reach_of_lookup`). `BoundaryChainD` follows from `StepCutNT`
  (`Seam.boundaryChainD_of_cut`), which follows from `CutParentNT` (`Seam.stepCutNT_of_parent`).

Results:

* `topStartLoRootW_of_boundary : BoundaryChainD → TopStartLoRootW`;
* `topStartLoRootW_of_cutParent : CutParentNT → TopStartLoRootW`.
-/

namespace OmegaY.Official.Recon.TSQ

open Canonical Expansion Classification
open Classification.Proofs.ChainCorr (cutOrigin)
open Recon.TopChain.Seam (BoundaryChainD CutParentNT)

/-- **`TopStartLoRootW` from `BoundaryChainD`.** -/
theorem topStartLoRootW_of_boundary (hB : BoundaryChainD) :
    TopStartFixParts.TopStartLoRootW := by
  intro s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv hl hpa
    hpe hlo he
  have hpac : pa.column = root.column := by
    rw [(Classification.Proofs.ChainCorr.highestAtMost_spec hpa).1, he]
  refine ⟨fun h => absurd hpac (by omega), fun _ => ⟨?_, ?_⟩, fun h => absurd hpac (by omega)⟩
  · rw [(Classification.Proofs.ChainCorr.highestAtMost_spec hpe).1, he,
      Classification.Proofs.ChainCorr.mapColumn_of_ge (le_refl _)]
  · obtain ⟨esB, k, hk, hesB, hpeq, cν, hcν, hνc, hν1, hνt, hpa'⟩ :=
      Recon.TopChain.Seam.startRootLookup s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop
        cu cv l pe pa hcu hcv hl hpa hpe hlo he
    rw [hpeq]
    exact Recon.TopChain.Seam.reach_of_lookup hB hrun hTop hi0 hin hk hesB hcν hνc hν1 hνt hpa'

/-- **`TopStartLoRootW` from `CutParentNT`.** -/
theorem topStartLoRootW_of_cutParent (hCP : CutParentNT) : TopStartFixParts.TopStartLoRootW :=
  topStartLoRootW_of_boundary
    (Recon.TopChain.Seam.boundaryChainD_of_cut (Recon.TopChain.Seam.stepCutNT_of_parent hCP))

end OmegaY.Official.Recon.TSQ

#print axioms OmegaY.Official.Recon.TSQ.topStartLoRootW_of_boundary
#print axioms OmegaY.Official.Recon.TSQ.topStartLoRootW_of_cutParent
