/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/ChainCorrLegLeftJump.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrLegLeftRoutes

set_option backward.do.legacy false

/-!
# `StartJumpGe` without `CopyOrder`

`startJumpGe` (`ChainCorrLegLeft.lean`) proves `StartJumpGe` from the block profile `CopyOrder`,
`CopyEmitted`, which is used only for legs right of `c_r` (`LegJump.legRowMatch_inner`). But
`CopyOrder` is false (`CopyShapeMAFalse.lean`). This file isolates what is used:

* `LegRowMatchInner` (open, new): for a region node `u` of block `i ≥ 1` whose origin `o` is not a
  gap copy and has its leg `l` right of `c_r`, if the column `l` of `M(s)` has a real node at the
  row of `o`, the output column `l + w·i` has a real node at the row of `u`. This is the case
  `l > c_r` of `LegJump.LegRowMatch`.
* `startJumpGe_of_inner : LegRowMatchInner → StartJumpGe` (**proved**): the case `l = c_r` is
  `legRowMatchRoot` (proved) and the step bound is `stepJumpLe` (proved).
* `wellFounded_of_lift_inner`: well-foundedness with `StartLeg` replaced by `LiftLegRight` and
  `StartJump` by `LegRowMatchInner`.

## Numerical tests (`reference/official/startleg-left.cjs`, count `LegRowMatchInner`)

| sample | nodes | failures |
|---|---:|---:|
| the 64 inputs where `LegBelowTop` fails, `n = 1,2,3` | 432 | 0 |
| 8 counterexample inputs of other statements (`CopyOrder`, `GapTop`, `NonCutOrder`, `LegBelowTop`), `n = 1,2,3` | 72 | 0 |
| legal, length ≤ 6, entries ≤ 12, `n = 1` (all 248831 sequences) | 169576 | 0 |
| legal, length ≤ 6, entries ≤ 12, `n = 2` (first 186608 sequences) | 314306 | 0 |
| random, length ≤ 6, entries ≤ 20 (`--random 100000,6,20,41`, `n = 1`) | 33961 | 0 |
| random, length ≤ 7, entries ≤ 20 (`--random 50000,7,20,7`, `n = 1,2`, first 2980 sequences) | 7538 | 0 |
| random, length ≤ 8, entries ≤ 30 (`--random 50000,8,30,17`, `n = 1`, first 19500 sequences) | 23926 | 0 |
| random, length ≤ 10, entries ≤ 40 (`--random 50000,10,40,23`, `n = 1`, first 4588 sequences) | 7964 | 0 |

(Skipped inputs as in `ChainCorrLegLeft.lean`.) `StartJumpGe` itself: see the table of
`ChainCorrLegLeft.lean` (no failure in about 7.7 million nodes).

## What is not repaired here

`StartCopy`, a hypothesis of every well-foundedness theorem of this route, fails numerically on
`(1,3,8,10,13,8)[1]` (`StartRootPartsGapTopFalse.lean`; 6 nodes). This is not a use of
`StartLeg`; it is left to the `StartCopy` / `GapTop` work.

`StepInner`, also a hypothesis of every well-foundedness theorem of this route (directly, or
through its parts), fails numerically as well: `reference/official/chain-corr.cjs` reports
3 failures of the case `m' > c_r` on `(1,3,8,10,15,8)[1]` (`X = 8`, `v = 3`, `k = 1, 2, 3`;
`notes/05-large-value-audit.md`). So `wellFounded_of_lift_inner` has two hypotheses that are
false numerically, `StepInner` and `StartCopy`; the other six hypotheses showed no failure in any
test.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr.LegJump

/-- (open) **The leg row matches for legs right of `c_r`** (the case `l > c_r` of
`LegJump.LegRowMatch`). -/
def LegRowMatchInner : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = false →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      ρ.cr < l.column → SameRow M l.column cv.row → SameRow R ref.column cu.row

theorem legRowMatchInner_of_profile (hA : ChainCorr.CopyOrder) (hB : ChainCorr.CopyEmitted) :
    LegRowMatchInner :=
  legRowMatch_inner hA hB

/-- `LegRowMatch` for legs at or right of `c_r`, from `LegRowMatchInner`. -/
theorem legRowMatchGe_of_inner (hIn : LegRowMatchInner) :
    ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = false →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      ¬ (es[j].2.isUpper = true ∧ l.column < ρ.cr) → ρ.cr ≤ l.column →
      SameRow M l.column cv.row → SameRow R ref.column cu.row := by
  intro s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL hnot hcr hsm
  rcases Nat.lt_or_eq_of_le hcr with h | h
  · exact hIn s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL h hsm
  · exact legRowMatchRoot s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL
      hnot h.symm hsm

/-- **`StartJumpGe` from `LegRowMatchInner`** (the proof of `startJumpGe`, without the block
profile). -/
theorem startJumpGe_of_inner (hIn : LegRowMatchInner) : StartJumpGe := by
  intro s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe cpa hL hnot hcr
  have hVR := build_valid_of_success hS.canon
  by_cases hsm : SameRow M l.column cv.row
  · have hsr := legRowMatchGe_of_inner hIn s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe
      pa cpe cpa hL hnot hcr hsm
    rw [jump_highest_zero hVR hL.hpe hL.hcpe hsr]
    exact Nat.zero_le _
  · obtain ⟨_, hidx, _⟩ := emitsT_good hS.emits es[j] (List.getElem_mem hj)
    obtain ⟨k, cvd, hk, hcvd, hRHS⟩ := jump_highest_step hS.splice.build hL.hcv (by omega)
      hL.hl hL.hpa hL.hcpa hsm
    rw [hRHS]
    by_cases hsr : SameRow R ref.column cu.row
    · rw [jump_highest_zero hVR hL.hpe hL.hcpe hsr]
      exact Nat.zero_le _
    · obtain ⟨k', cd, hk', hcd, hLHS⟩ := jump_highest_step hS.canon hL.hcu (by simp)
        hL.href hL.hpe hL.hcpe hsr
      simp only at hk' hcd
      rw [hLHS]
      have hj' : j = k' + 1 := by omega
      subst hj'
      exact stepJumpLe s n D M out ρ R t X x i es hS (k' + 1) hj hcut cu cv ref l pe pa cpe cpa
        hL hnot hsm (by omega) cd cvd hcd (by rw [hk]; simpa using hcvd)

/-- **All of `StartJump`** from `PlainLegLeftRow` and `LegRowMatchInner` (replaces
`LegJump.startJump_of_open` and `startJump_of_legLeft`; no `StartLeg`, no `CopyOrder`). -/
theorem startJump_of_inner (hRow : PlainLegLeftRow) (hIn : LegRowMatchInner) : StartJump := by
  intro s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe cpa hL hnot
  rcases startLeg_split hS hj hL hnot with hcr | ⟨⟨r, ho⟩, hlt⟩
  · exact startJumpGe_of_inner hIn s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe
      cpa hL hnot hcr
  · obtain ⟨hrow, _, hcc⟩ := legLeft_same hRow hS hj hL ho hlt
    rw [hrow, hcc]

/-- **Well-foundedness without `StartLeg`, `StartJump` and `CopyOrder` on the region route**:
`wellFounded_of_chains` with `StartLeg` replaced by `LiftLegRight` (about `M(s)` alone) and
`StartJump` by `LegRowMatchInner`. -/
theorem wellFounded_of_lift_inner (hrec : Dimension.BlockReconstruction) (hStep : StepInner)
    (hLift : LiftLegRight) (hIn : LegRowMatchInner) (hCopy : StartCopy) (hRoot : StartRoot)
    (hKB : RegionCutBoundary) (hKI : RegionCutInner) : WellFounded Step :=
  wellFounded_of_lift_ge hrec hStep hLift (startJumpGe_of_inner hIn) hCopy hRoot hKB hKI

end OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft.legRowMatchGe_of_inner
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft.startJumpGe_of_inner
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft.startJump_of_inner
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft.wellFounded_of_lift_inner
