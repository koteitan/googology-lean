/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CopyShapeOrderLeg.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrStartCopy

set_option backward.do.legacy false

/-!
# `CopyOrder` is false; the two forms its users need

`ChainCorr.CopyOrder` (`ChainCorrStartCopy.lean`) compares non-cut emits of any two columns
`y`, `y'` of a block `i ≥ 1`. It is false (`CopyShapeMAFalse.lean`): for
`s = (1,3,6,13,15,13)`, `n = 1`, block `1`, the node `(3,ω)` is copied to row `ω·2` and the node
`(4,ω)` to row `ω`. The column `4` does not ascend in the region `[0, ω²)` although it has the
node `(4,ω)` above the root top `(2,2)` (this is where (MA) fails), so `(4,ω)` keeps its row,
while `(3,ω)` is lifted.

Every use of `CopyOrder` in the project compares two emits in one of two shapes:

* **the same column** (`CutPartsTop.lean`, `CutPartsStart.lean`): `CopyOrderSame`, proved in
  `CopyShapeNoMA.lean` (`copyOrderSame`), with no hypothesis;
* **a column `y` and the leg column `l` of the origin `v` of the emit of `y`**
  (`ChainCorrStartCopy.lean`, `StepInnerLookupLeg.lean`, `LegParts*.lean`,
  `StartRootPartsCutTop.lean`, `ChainCorrStartLegJump.lean`; there `l = cv.left.column` or
  `pa.column` with `pa` the highest node of `l` at or below `v`, and `cr < l`): this is
  `CopyOrderLeg` below. It is proved in `CopyShapeOrderLegProof.lean`
  (`ProfileLeg.copyOrderLeg`, no hypothesis).

In the counterexample the failing pairs are not of the second shape: the left end of `(4,ω)` is
`(0,0)`, left of `c_r = 2`.

## Numerical evidence for `CopyOrderLeg`

`reference/official/copy-order-leg.cjs` (check `COlegcol`: for each non-cut emit `e` of a block
column `y` with origin `u`, the leg column `l` of `u` (the left end of `u`, or `y - 1` for a
bottom node) when `l` is a block column, and every non-cut emit `f` of `l`: the rows of `e` and
`f` compare like the rows of their origins). The counts are in the report of this task; no
failure was found, while the unrestricted `CopyOrder` (`COpairs`) fails on the counterexample.
-/

namespace OmegaY.Official.Classification.Proofs.CopyShape.NoMA

open Canonical Reserve Official Descent Classification Proofs

/-- **(proved: `ProfileLeg.copyOrderLeg`)** `CopyOrder` between a column `y` and the leg column `l` of the origin of an emit
of `y`: the rows of a non-cut emit of `y` whose origin has its left end in column `l`, and of any
non-cut emit of `l`, compare like the rows of their origins. -/
def CopyOrderLeg : Prop :=
  ∀ s n D M out ρ R t, ChainCorr.SpliceData s n D M out ρ R t → ∀ i, 0 < i → i < n + 1 →
    ∀ y l es es', y ∈ blockColumns ρ.cr ρ.x0 n i → l ∈ blockColumns ρ.cr ρ.x0 n i →
      ChainCorr.blockEmits M R ρ.cr ρ.x0 (official t.row) i y = .ok es →
      ChainCorr.blockEmits M R ρ.cr ρ.x0 (official t.row) i l = .ok es' →
      ∀ k (hk : k < es.length) k' (hk' : k' < es'.length),
        ChainCorr.cutOrigin es[k].2 = false → ChainCorr.cutOrigin es'[k'].2 = false →
        ∀ (c c' : Cell) (lr : Ref), cell? M es[k].2.src = some c →
          cell? M es'[k'].2.src = some c' → c.left = some lr → lr.column = l →
          (c.row < c'.row → es[k].1.row < es'[k'].1.row) ∧
            (c.row = c'.row → es[k].1.row = es'[k'].1.row) ∧
            (c'.row < c.row → es'[k'].1.row < es[k].1.row)

/-- `CopyOrder` gives both forms (so they are weakenings of the false statement). -/
theorem copyOrderLeg_of_copyOrder (h : ChainCorr.CopyOrder) : CopyOrderLeg := by
  intro s n D M out ρ R t hS i hi0 hi y l es es' hy hl hes hes' k hk k' hk' hnc hnc' c c' lr
    hc hc' _ _
  have h1 := h s n D M out ρ R t hS i hi0 hi y l es es' hy hl hes hes' k hk k' hk' hnc hnc' c c'
    hc hc'
  have h2 := h s n D M out ρ R t hS i hi0 hi l y es' es hl hy hes' hes k' hk' k hk hnc' hnc c' c
    hc' hc
  exact ⟨h1.1, h1.2, h2.1⟩

end OmegaY.Official.Classification.Proofs.CopyShape.NoMA

#print axioms OmegaY.Official.Classification.Proofs.CopyShape.NoMA.copyOrderLeg_of_copyOrder
