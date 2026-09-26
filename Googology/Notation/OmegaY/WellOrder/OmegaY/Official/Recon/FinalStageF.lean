/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/FinalStageF.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossUpperNMain
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TopStartW2Key

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# Stage F: the final assembly (no open hypothesis)

`WellFounded Descent.Step`: there is no infinite chain of official ω-Y expansions
(`Descent.Step t s` says that `t` is an expansion `s[n]` of the non-empty sequence `s`).

After stage F the list of open statements is **empty**:

| statement of `FinalStageE` / stage F | status |
|---|---|
| `RootValueIn` | false; no longer used: `TopStart'` is replaced by `TopStart''` (**proved**, `TopStartW2.topStart''_holds`) |
| `PaONoGapHi` | false; no longer used: `CopyQLowerW` is replaced by `CopyQLowerN` (**proved**, `CrossUpperNStart.lean`) |
| `CutRightTopHi` | proved (`CrossUpperQHiCut.lean`); used inside `NoEndRightHi` through `TSQ.topNode_cutRight` |
| `SeamChainX`, `QRootRowGe` | proved (`SCXMain.lean`) |
| `CrossLexFor IsUpper` (the one hypothesis of `TopStartW2F.wellFounded_of_stageF`) | **proved** (`CrossUpperW.CUN.crossLexFor_upper_final`, `CrossUpperNMain.lean`) |

The pieces plugged in:

* `TopStep` (`FinalStageE.topStep_final`), `TopStart''` (`TopStartW2.topStart''_holds`);
* `CrossLexFor IsPlain`, `CrossLexFor IsClean` (`TopStartW2R.crossLexFor_plain''`,
  `crossLexFor_clean''` with the proved `NoEndRight`);
* `CrossLexFor IsUpper` (`CrossUpperW.CUN.crossLexFor_upper_final`: `CopyQLowerN`,
  `NoEndRightHi`, `NonTopPass`, `NonTopRootHi`, all proved);
* `ParentBelowHolds`, `CutPredHolds`, `JumpLawHolds`, hence `ChainHolds`, `RowLawHolds`,
  `ReconstructionHolds` and `BlockReconstruction`;
* `KeyLeRest` (`TopStartW2Key.keyLeRest_pkg3''`, with `NonTopStep` from the reconstruction);
* `ControlProof.wellFounded_of_block_keys`.

The same assembly as `TopStartW2Final.lean` (`TopStartW2F.wellFounded_of_stageF`), written out
here with the proved `CrossLexFor IsUpper` in place of its hypothesis.
-/

namespace OmegaY.Official.Recon.FinalStageF

/-- **`CrossLexFor IsUpper` holds.** -/
theorem crossLexFor_upper : CrossLexFor IsUpper := CrossUpperW.CUN.crossLexFor_upper_final

/-- **`CrossLexFor IsPlain` holds.** -/
theorem crossLexFor_plain : CrossLexFor IsPlain :=
  TopStartW2R.crossLexFor_plain'' TSQ.W2.noEndRight_plain

/-- **`CrossLexFor IsClean` holds.** -/
theorem crossLexFor_clean : CrossLexFor IsClean :=
  TopStartW2R.crossLexFor_clean'' TSQ.W2.noEndRight_clean

/-- **The parent chains hold.** -/
theorem chainHolds : ChainHolds :=
  chainHolds_of_three LowerPB.StageB.parentBelowHolds crossLexFor_plain crossLexFor_clean
    CutPredMD.cutPredHolds crossLexFor_upper

/-- **The reconstruction holds.** -/
theorem reconstructionHolds : Reconstruction.ReconstructionHolds :=
  reconstructionHolds_of_rowLaw_chain (RowLaw.rowLawHolds_of_jumpLaw LRC.jumpLawHolds) chainHolds

/-- **`BlockReconstruction` holds.** -/
theorem blockReconstruction : Dimension.BlockReconstruction :=
  blockReconstruction_of_reconstructionHolds reconstructionHolds

/-- **`KeyLeRest` holds.** -/
theorem keyLeRest : Classification.KeyLeRest :=
  Classification.Proofs.ChainCorr.TopStartW2Key.keyLeRest_pkg3'' FinalStageE.topStep_final
    TopStartW2.topStart''_holds
    (Classification.Proofs.ChainCorr.NonTop.nonTopStep_of_reconstruction blockReconstruction)
    Classification.Proofs.ChainCorr.NonTop.startRelNT
    Classification.Proofs.ChainCorr.NonTop.startRootNT TopChain.Seam.CPN.boundaryChain
    Classification.Proofs.P3T.cutJumpRootRow Classification.Proofs.P3T.cutRunTop

/-- **Well-foundedness of the official ω-Y expansion** (no hypothesis). -/
theorem wellFounded_step : WellFounded Descent.Step :=
  Classification.ControlProof.wellFounded_of_block_keys blockReconstruction keyLeRest

/-- **No infinite chain of expansions**: there is no sequence `f 0, f 1, f 2, …` with `f (k+1)`
an expansion of `f k` for every `k`. -/
theorem no_infinite_expansion (f : Nat → List Nat) : ¬ ∀ k, Descent.Step (f (k + 1)) (f k) := by
  intro hf
  have key : ∀ x, ∀ k, f k = x → False := by
    intro x
    induction x using wellFounded_step.induction with
    | _ x ih =>
      intro k hk
      exact ih (f (k + 1)) (hk ▸ hf k) (k + 1) rfl
  exact key (f 0) 0 rfl

end OmegaY.Official.Recon.FinalStageF

#print axioms OmegaY.Official.Recon.FinalStageF.crossLexFor_upper
#print axioms OmegaY.Official.Recon.FinalStageF.crossLexFor_plain
#print axioms OmegaY.Official.Recon.FinalStageF.crossLexFor_clean
#print axioms OmegaY.Official.Recon.FinalStageF.chainHolds
#print axioms OmegaY.Official.Recon.FinalStageF.reconstructionHolds
#print axioms OmegaY.Official.Recon.FinalStageF.blockReconstruction
#print axioms OmegaY.Official.Recon.FinalStageF.keyLeRest
#print axioms OmegaY.Official.Recon.FinalStageF.wellFounded_step
#print axioms OmegaY.Official.Recon.FinalStageF.no_infinite_expansion
