/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CrossUpperSimLow.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossUpperSimTop

set_option backward.do.legacy false

/-!
# `CopyStepLower` for a node below the top of the lower part

`CopyStepLower` (`CrossUpperSimDefs.lean`) is about the top copy `Z` of a node `z` of an inner
column `y` with `row z < τ`, and the stored parent `a` of the node `z⁺` above `z`. It splits by
the row of `z⁺`:

* `row z⁺ ≥ τ` (**proved from `CopyTop`**, `copyStepLower_top`): then `z` is the highest node
  of `y` below `τ`, so `Z` is the highest node of `y + w·i` below `τ` (`CopyTop`), the node
  `Z⁺` above it is the copy of `z⁺` at the same row (the upper part), and its stored parent
  is the highest node below that row in the column `f(col a)`: it stands for `a` by
  `cp_of_highest`;
* `row z⁺ < τ` (**open**, `CopyStepLow`).

`crossLexFor_upper_of_low : Emitted → CopyQLower → CopyStepLow → CrossLexFor IsUpper`.

## What is open

`SeamLastPosHolds` and `InnerHolds` follow from three statements (`seamLastPos_of_low`,
`inner_of_low`):

* `LowerPB.Emitted` (`ParentBelowLowerProfile.lean`, shared with `LowerParentBelowHolds`);
* `CopyQLower` (`CrossUpperSimDefs.lean`);
* `CopyStepLow` (this file).

## Numerical tests (`reference/official/cross-upper-sim.cjs`)

Counts of checked cases; there is no failure in any row. `Emitted` is checked only on the
columns that exist. Inputs are sequences `(1, a₁, …)`; "per input" runs give each input 20 s,
and the inputs that ran out of time are listed as skipped.

| sample | `n` | `Emitted` | `CopyTop` | `CopyQLower` | `CopyStepLower`, `z⁺ ≥ τ` (proved from `CopyTop`) and `CopyStepLow` |
|---|---|---:|---:|---:|---:|
| length ≤ 6, entries ≤ 12 (248831 inputs) | 1, 2 | — | 1558028 | 1400936 | 3183195 |
| the 64 inputs where `LegBelowTop` fails | 1, 2, 3 | 4080 | 1092 | 660 | 2832 |
| `(1,3,6,13,15,13)`, `(1,3,10,12,18,10)`, `(1,2,4,10,11,14,10)`, `(1,4,8,25,27,15)` | 1, 2, 3 | 285 | 72 | 42 | 198 |
| 1500 random, length ≤ 7, entries ≤ 40 (5 skipped) | 1 | 18465 | 3034 | 2597 | 18028 |
| 1500 random, length ≤ 6, entries ≤ 20 (12 skipped) | 2 | 24042 | 5743 | 5269 | 16448 |

The first row ran before `Emitted` was added to the script. `reference/official/cross-upper.cjs`
(the goal statements themselves) gives no failure on length ≤ 6, entries ≤ 12, `n = 1`
(70279 `InnerHolds` nodes), and on the two random samples above (565 `InnerHolds` and 220
`SeamLastPosHolds` nodes).
-/

namespace OmegaY.Official.Recon.CrossUpperSim

open Canonical Expansion Geometry Frame Classification
open CrossUpper
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index
  upper_eq_of_index)

/-- **Open.** `CopyStepLower` when the node `z⁺` above `z` is below `τ`. -/
def CopyStepLow : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i : Nat),
    Official.expandDiagram s n = .ok R → Top s M t root → 1 ≤ i → i ≤ n →
    ∀ (Z : (Frame.ofMountain R).Node) (z z' a : (Frame.ofMountain M).Node),
      root.column < z.1.val → z.1.val < M.size - 1 →
      Z.1.val = z.1.val + (M.size - 1 - root.column) * i →
      (Frame.ofMountain M).upper z = some z' → (Frame.ofMountain M).height z' < t.row →
      TopCopy s n R M Z z →
      (Frame.ofMountain M).rawParent z = some a →
      ∃ A, (Frame.ofMountain R).rawParent Z = some A ∧ Cp s n R M t root i A a

/-- **`CopyStepLower` when `z⁺` is at or above `τ`.** -/
theorem copyStepLower_top (hCT : CopyTop) {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell}
    {root : Ref} {i : Nat} (hrun : Official.expandDiagram s n = .ok R) (hTop : Top s M t root)
    (hi1 : 1 ≤ i) (hin : i ≤ n) {Z : (Frame.ofMountain R).Node}
    {z z' a : (Frame.ofMountain M).Node} (hg : root.column < z.1.val)
    (hzx : z.1.val < M.size - 1) (hZc : Z.1.val = z.1.val + (M.size - 1 - root.column) * i)
    (hzτ : (Frame.ofMountain M).height z < t.row) (hzu : (Frame.ofMountain M).upper z = some z')
    (hθ : t.row ≤ (Frame.ofMountain M).height z') (hTC : TopCopy s n R M Z z)
    (hraw : (Frame.ofMountain M).rawParent z = some a) :
    ∃ A, (Frame.ofMountain R).rawParent Z = some A ∧ Cp s n R M t root i A a := by
  have hcr := hTop.lt
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  have E := env_of hrun hTop Z.1.isLt (by rw [hZc]; omega)
  have hG := E.G
  have hF := E.FR
  have ht1 := tau_gt_one hTop
  have hz : Real z := real_of_upper_gt hG hzu (lt_of_lt_of_le ht1 hθ)
  obtain ⟨hz'1, hz'2⟩ := upper_spec hzu
  -- `z` is the highest node of its column below `τ`, so `Z` is that of its column
  have hTz : TopBelow (Frame.ofMountain M) t.row z := topBelow_of_upper hG hzτ hzu hθ
  have h0 : 0 < (Frame.ofMountain R).length Z.1 := by have := Z.2.isLt; omega
  obtain ⟨T, hTc1, hT⟩ := exists_highestIn (Frame.ofMountain R) (· < t.row) Z.1 h0 (by
    have := hF.phantom Z.1 h0
    change ((Frame.ofMountain R).cells Z.1 ⟨0, h0⟩).row < t.row
    rw [this]
    exact lt_of_lt_of_le Row.zero_lt_one (le_of_lt ht1))
  have hmem := mem_blockColumns_of_inner (n := n) (i := i) (by omega) (by omega) hg hzx
  have hTC' : TopCopy s n R M T z := hCT s n R M t root i z.1.val hrun hTop hi1 hmem T z
    (by rw [hTc1]; exact hZc) rfl hT hTz
  have hTe : T = Z := TopCopy.unique hTC' hTC hTc1
  subst hTe
  -- the node above `Z` copies `z⁺`
  have Cz := upperCopy_inner E hg hzx hi1 (by rw [← hZc]; exact T.1.isLt)
  obtain ⟨Z', hZu, hZ'h⟩ := highestIn_upperCopy_upper hG hF Cz
    (fun r r' h1 h2 => lt_of_le_of_lt h1 h2) (fun r hr => hr) rfl hZc hTz hT hzu hθ
  obtain ⟨hZ'1, _⟩ := upper_spec hZu
  obtain ⟨A, hA, hAc⟩ := rawParent_of_upperCopy hF Cz hzu hZu (by rw [hz'1]) (by rw [hZ'1, hZc])
    hθ hZ'h hraw
  have hZr : Real T := real_of_upper_gt hF hZu (by rw [hZ'h]; exact lt_of_lt_of_le ht1 hθ)
  have hAR := highestIn_of_hb (E.HB T hZr) hZu hA
  rw [hZ'h] at hAR
  have haM : HighestIn (Frame.ofMountain M) (· < (Frame.ofMountain M).height z') a :=
    highestIn_of_hb (hbAt_of_normal E.NM hz) hzu hraw
  have har : Real a :=
    real_of_value_pos hG (P_value hG ((E.NM.rawParent_eq_P hz).symm.trans hraw)).1
  have haz : a.1.val < z.1.val := rawParent_column_lt hG hraw
  exact ⟨A, hA, cp_of_highest E hCT hi1 hin (fun r r' h1 h2 => lt_of_le_of_lt h1 h2)
    (fun r hr => lt_of_lt_of_le hr hθ) har (by omega) hAc haM hAR⟩

/-- **`CopyStepLower` from `CopyTop` and `CopyStepLow`.** -/
theorem copyStepLower_of_low (hCT : CopyTop) (hLow : CopyStepLow) : CopyStepLower := by
  intro s n R M t root i hrun hTop hi1 hin Z z a hg hzx hZc hzτ hTC hraw
  obtain ⟨z', hzu, _⟩ := rawParent_spec hraw
  by_cases hθ : t.row ≤ (Frame.ofMountain M).height z'
  · exact copyStepLower_top hCT hrun hTop hi1 hin hg hzx hZc hzτ hzu hθ hTC hraw
  · exact hLow s n R M t root i hrun hTop hi1 hin Z z z' a hg hzx hZc hzu (lt_of_not_ge hθ) hTC
      hraw

/-- **`CrossLexFor IsUpper` from `Emitted`, `CopyQLower` and `CopyStepLow`.** -/
theorem crossLexFor_upper_of_low (hE : LowerPB.Emitted) (hQL : CopyQLower)
    (hLow : CopyStepLow) : CrossLexFor IsUpper :=
  crossLexFor_upper_of_emitted hE hQL (copyStepLower_of_low (copyTop_of_emitted hE) hLow)

/-- **`SeamLastPosHolds` from `Emitted`, `CopyQLower` and `CopyStepLow`.** -/
theorem seamLastPos_of_low (hE : LowerPB.Emitted) (hQL : CopyQLower) (hLow : CopyStepLow) :
    SeamLastPosHolds :=
  seamLastPos_of_emitted hE hQL (copyStepLower_of_low (copyTop_of_emitted hE) hLow)

/-- **`InnerHolds` from `Emitted`, `CopyQLower` and `CopyStepLow`.** -/
theorem inner_of_low (hE : LowerPB.Emitted) (hQL : CopyQLower) (hLow : CopyStepLow) :
    InnerHolds :=
  inner_of_emitted hE hQL (copyStepLower_of_low (copyTop_of_emitted hE) hLow)

end OmegaY.Official.Recon.CrossUpperSim

#print axioms OmegaY.Official.Recon.CrossUpperSim.copyStepLower_of_low
#print axioms OmegaY.Official.Recon.CrossUpperSim.seamLastPos_of_low
#print axioms OmegaY.Official.Recon.CrossUpperSim.inner_of_low
#print axioms OmegaY.Official.Recon.CrossUpperSim.crossLexFor_upper_of_low
