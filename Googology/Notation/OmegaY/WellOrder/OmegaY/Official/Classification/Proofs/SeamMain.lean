/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/SeamMain.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.SeamStepB0
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.NonTopMain

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# The seam: the three targets from the open steps

Proved: `StepBlock0` (`stepBlock0`), `StepUpper` (`stepUpper`), `StepTop` (`stepTop`),
`StepRootLookup`, `StartRootLookup` (`stepRootLookup`, `startRootLookup`), the jump bound of
`TopStepLoRoot` (`topStepLoJumpAll`).

Open (numerically checked, see the report):

* `StepX0Top`: the step from a lower top copy in the copy of `x₀` of a block `i ≥ 1`;
* `StepCleanNT`: the step from a clean copy (`b = 0`) that is not the top copy;
* `StepCutNT`: the step from a gap copy that is not the top copy;
* `StepRootTop`, `StartRootTop`: the second clause of `Stand` (the node above the stand-in).

`StepNonTop` follows from `StepCleanNT` and `StepCutNT` (a copy that is not the top copy and not
a gap copy is a clean copy, `NonTop.clean_of_not_isTopAt`), `StepX0` from these and `StepX0Top`.
-/

namespace OmegaY.Official.Recon.TopChain.Seam

open Canonical Expansion Geometry Frame Classification
open Classification.Proofs.ChainCorr (MStep cutOrigin blockEmits)
open Classification.Proofs (ScaleReach)
open Classification.Proofs.ChainCorr.LowerChain (IsTopAt)

/-- (open) The step for a lower top copy of the copy of `x₀` in a block `i ≥ 1`. -/
def StepX0Top : Prop :=
  ∀ s n R M t root i es j, NodeData s n R M t root i (M.size - 1) es j → 0 < i →
    ∀ hj : j < es.length, es[j].2.isUpper = false → IsTopAt es j →
    StepOK R M n t root ⟨M.size - 1 + (M.size - 1 - root.column) * i, j + 1⟩ es[j].2.src

/-- (open) The step for a clean copy (`b = 0`) of a block `i ≥ 1` that is not the top copy. -/
def StepCleanNT : Prop :=
  ∀ s n R M t root i x es j, NodeData s n R M t root i x es j → 0 < i →
    ∀ hj : j < es.length, ∀ a, es[j].2 = .clean a false → ¬ IsTopAt es j →
    StepOK R M n t root ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ es[j].2.src

/-- (open) The step for a gap copy of a block `i ≥ 1` that is not the top copy. -/
def StepCutNT : Prop :=
  ∀ s n R M t root i x es j, NodeData s n R M t root i x es j → 0 < i →
    ∀ hj : j < es.length, cutOrigin es[j].2 = true → ¬ IsTopAt es j →
    StepOK R M n t root ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ es[j].2.src

theorem nonTop_split (hC : StepCleanNT) (hG : StepCutNT) {s : List Nat} {n : Nat}
    {R M : Mountain} {t : Cell} {root : Ref} {i x : Nat} {es : List (Emit × Origin)} {j : Nat}
    (hD : NodeData s n R M t root i x es j) (hi0 : 0 < i) (hj : j < es.length)
    (hnt : ¬ IsTopAt es j) :
    StepOK R M n t root ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ es[j].2.src := by
  cases hcut : cutOrigin es[j].2
  · obtain ⟨a, ha⟩ := Classification.Proofs.ChainCorr.NonTop.clean_of_not_isTopAt
      (ctx := ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
        (x + (M.size - 1 - root.column) * i))
      (build_valid_of_success hD.2.1.build) hD.2.2.2.1 hj hcut hnt
    exact hC s n R M t root i x es j hD hi0 hj a ha hnt
  · exact hG s n R M t root i x es j hD hi0 hj hcut hnt

theorem stepNonTop_of (hC : StepCleanNT) (hG : StepCutNT) : StepNonTop := by
  intro s n R M t root i x es j hD hi0 _ hj _ hnt
  exact nonTop_split hC hG hD hi0 hj hnt

theorem stepX0_of (hT : StepX0Top) (hC : StepCleanNT) (hG : StepCutNT) : StepX0 := by
  intro s n R M t root i es j hD hi0 hj hup
  by_cases htop : IsTopAt es j
  · exact hT s n R M t root i es j hD hi0 hj hup htop
  · exact nonTop_split hC hG hD hi0 hj htop

/-- **`BoundaryChainD` from the open steps.** -/
theorem boundaryChainD_of_open (hT : StepX0Top) (hC : StepCleanNT) (hG : StepCutNT) :
    BoundaryChainD :=
  boundaryChainD_of_cases stepBlock0 stepUpper stepTop (stepNonTop_of hC hG) (stepX0_of hT hC hG)

/-- **`BoundaryChain` from the open steps.** -/
theorem boundaryChain_of_open (hT : StepX0Top) (hC : StepCleanNT) (hG : StepCutNT) :
    Classification.Proofs.ChainCorr.BoundaryChain :=
  boundaryChain_of_diag (boundaryChainD_of_open hT hC hG)

/-- **`TopStepLoRoot` from the open steps and `StepRootTop`.** -/
theorem topStepLoRoot_of_open (hT : StepX0Top) (hC : StepCleanNT) (hG : StepCutNT)
    (hR : StepRootTop) : TopStepLoRoot :=
  topStepLoRoot_of_parts (boundaryChainD_of_open hT hC hG) stepRootLookup hR

/-- **`TopStartLoRoot` from the open steps and `StartRootTop`.** -/
theorem topStartLoRoot_of_open (hT : StepX0Top) (hC : StepCleanNT) (hG : StepCutNT)
    (hR : StartRootTop) : TopStartLoRoot :=
  topStartLoRoot_of_parts (boundaryChainD_of_open hT hC hG) startRootLookup hR

end OmegaY.Official.Recon.TopChain.Seam

#print axioms OmegaY.Official.Recon.TopChain.Seam.boundaryChain_of_open
#print axioms OmegaY.Official.Recon.TopChain.Seam.topStepLoRoot_of_open
#print axioms OmegaY.Official.Recon.TopChain.Seam.topStartLoRoot_of_open
