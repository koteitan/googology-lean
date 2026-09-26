/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/JumpLawLowerLeft.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawLowerSplit

set_option backward.do.legacy false

/-!
# The lower pairs without `LowerLegGe`

`lowerPairsHolds_of_rows` (`JumpLawLower.lean`) uses `LowerLegGe` (every node of the lower part
of a column of block `i ≥ 1` has a leg `l ≥ c_r`), which was derived from the false
`LegBelowTop` (`lowerLegGe_of_legBelowTop`). `LowerLegGe` is false as well: on the 64 legal
sequences of length `≤ 6` with entries `≤ 12` where `LegBelowTop` fails, 402 nodes of the lower
part of block `i ≥ 1` (all with a plain origin) have their leg in a column `l < c_r`
(`reference/official/startleg-left.cjs`; for example `(1,3,9,11,9)[1]`, column `6`, row `ω`,
leg column `0`, `c_r = 1`).

This file splits `LowerPairsHolds` by the leg:

* `LowerPairsGe` (`l ≥ c_r`): **proved** from `LowerRowsHolds` (`lowerPairsGe_of_rows`, the
  argument of `lowerPairsHolds_of_rows`: the leg column `Y = l + w·i` is a new column).
* `LowerPairsLeft` (`l < c_r`, open, new): the leg column `Y = l` is an old column shared with
  `M(s)`. Numerically the upper node keeps the row `θ` of its (plain) origin `o` and `Y` reads
  the parent `p` of `o`, but the node `λ` below it usually does not have the row of the node
  below `o` (366 of the 402 cases), so this case needs more than the rows of `M(s)`.

Results: `lowerPairsHolds_of_split : LowerPairsGe → LowerPairsLeft → LowerPairsHolds` and
`jumpLawHolds_of_rows_left : LowerRowsHolds → LowerPairsLeft → JumpLawHolds` (replaces
`jumpLawHolds_of_lowerRows` and `jumpLawHolds_of_legBelowTop_lowerRows`), and
`jumpLawHolds_of_lowerCases_left : LowerRowsCopy → LowerRowsBoundary → LowerPairsLeft →
JumpLawHolds` (replaces `jumpLawHolds_of_lowerCases`).

## Numerical tests (`reference/official/startleg-left.cjs`, `LowerPairsLeft`)

| sample | pairs with `l < c_r` | failures |
|---|---:|---:|
| the 64 inputs where `LegBelowTop` fails, `n = 1,2,3` | 402 | 0 |
| legal, length ≤ 6, entries ≤ 12, `n = 1` (all 248831 sequences) | 67 | 0 |
| 8 inputs refuting other statements (`CopyOrder`, `GapTop`, `NonCutOrder`, `LegBelowTop`), `n = 1,2,3` | 30 | 0 |
| legal, length ≤ 6, entries ≤ 12, `n = 2` (first 186608 sequences) | 116 | 0 |
| random, length ≤ 6, entries ≤ 20 (`--random 100000,6,20,41`, `n = 1`) | 43 | 0 |
| random, length ≤ 8, entries ≤ 30 (`--random 50000,8,30,17`, `n = 1`, first 19500 sequences) | 67 | 0 |
| random, length ≤ 10, entries ≤ 40 (`--random 50000,10,40,23`, `n = 1`, first 4588 sequences) | 29 | 0 |

(The inputs and the skipped outputs are listed in
`Classification/Proofs/ChainCorrLegLeft.lean`.)
-/

namespace OmegaY.Official.Recon.JumpLawLowerLeft

open Canonical Expansion Dimension RowLaw JumpLaw JumpLawLower

/-- The jump law for the lower pairs whose upper node has its leg at or right of `c_r`. -/
def LowerPairsGe : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i x : Nat),
    NewColumn s n R M t root i x → 1 ≤ i →
    ∀ vs us, LowerRun (colCtx M R root i x) (official t.row) vs →
      UpperRun (colCtx M R root i x) (official t.row) us →
      ∀ col, assemble (colCtx M R root i x) (vs.flatten ++ us) = .ok col →
      ∀ k (hk : k + 1 < (vs.flatten ++ us).length) (l e : Nat) (p : Row),
        k + 1 < vs.flatten.length →
        (vs.flatten ++ us)[k + 1].leftColumn = some l →
        (vs.flatten ++ us)[k + 1].row = Row.bump (vs.flatten ++ us)[k].row e →
        HighestBelow (rowsOf R (legCol (colCtx M R root i x) l)) (vs.flatten ++ us)[k + 1].row p →
        root.column ≤ l →
        Row.jump (vs.flatten ++ us)[k].row p = e

/-- (open) **The jump law for the lower pairs whose upper node has its leg left of `c_r`.** -/
def LowerPairsLeft : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i x : Nat),
    NewColumn s n R M t root i x → 1 ≤ i →
    ∀ vs us, LowerRun (colCtx M R root i x) (official t.row) vs →
      UpperRun (colCtx M R root i x) (official t.row) us →
      ∀ col, assemble (colCtx M R root i x) (vs.flatten ++ us) = .ok col →
      ∀ k (hk : k + 1 < (vs.flatten ++ us).length) (l e : Nat) (p : Row),
        k + 1 < vs.flatten.length →
        (vs.flatten ++ us)[k + 1].leftColumn = some l →
        (vs.flatten ++ us)[k + 1].row = Row.bump (vs.flatten ++ us)[k].row e →
        HighestBelow (rowsOf R (legCol (colCtx M R root i x) l)) (vs.flatten ++ us)[k + 1].row p →
        l < root.column →
        Row.jump (vs.flatten ++ us)[k].row p = e

/-- **The lower pairs with a leg at or right of `c_r`** from `LowerRowsHolds` (the proof of
`lowerPairsHolds_of_rows`, with the leg bound as a hypothesis instead of `LowerLegGe`). -/
theorem lowerPairsGe_of_rows (hR : LowerRowsHolds) : LowerPairsGe := by
  intro s n R M t root i x hNC hi vs us hvs hus col hasm k hk l e p hkL hleft hθ hHB hcl
  have hctx := hNC.runCtx
  set τ := official t.row with hτ
  set E := vs.flatten ++ us with hE
  set w := M.size - 1 - root.column with hw
  have hL := lower_lt hctx hvs
  have hsorted := assemble_sorted hasm
  have hmemk1 : E[k + 1] ∈ vs.flatten := getElem_mem_left hk hkL
  have hmemk : E[k] ∈ vs.flatten := getElem_mem_left (by omega) (by omega)
  have hθτ : E[k + 1].row < τ := hL _ hmemk1
  -- the item of `X`
  obtain ⟨J, LJ, hJ, hLJ, hlamJ, hlamin⟩ := item_of_lambda hctx hvs hmemk (e := e)
    (by rw [← hθ]; exact hθτ)
  have hbJ : Row.bump E[k].row e = Row.bump J.target e := by
    simpa using bump_of_inRegion hlamin
  have hmax : ∀ em ∈ vs.flatten, inRegion (e + 1) J.target em.row = true → em.row ≤ E[k].row := by
    intro em hem hin
    apply le_of_consecutive hsorted hk (List.mem_append_left _ hem)
    rw [hθ, hbJ]
    simpa using lt_bump_of_inRegion hin
  have hP : LowerPair s n R M t root i x E[k].row E[k + 1].row l e J :=
    ⟨hNC, hi, ⟨vs, us, col, hvs, hus, hasm, k, hk, hkL, rfl, rfl, hleft, ⟨LJ, hLJ, hlamJ⟩, hmax⟩,
      hθ, hJ, hlamin⟩
  -- the column `Y`
  have hcr := hNC.top.lt
  have hlegY : legCol (colCtx M R root i x) l = l + w * i := by
    unfold legCol
    rw [if_pos (show (colCtx M R root i x).rootColumn ≤ l from hcl)]
    rfl
  have hYs : l + w * i < R.size := by
    obtain ⟨em, hem, _⟩ := List.mem_map.mp hHB.1
    rw [hlegY] at hem
    by_contra hn
    rw [realNodes_eq_nil hn] at hem
    cases hem
  have hwi : w ≤ w * i := Nat.le_mul_of_pos_right w hi
  have hY0 : M.size - 1 ≤ l + w * i := by omega
  obtain ⟨i', x', hNC', hY⟩ := newColumn_at hNC hY0 hYs
  obtain ⟨vsY, usY, colY, hvsY, husY, hasmY, hrowsY⟩ := hNC'.emits
  obtain ⟨⟨em0, hem0, hem0in⟩, hslot⟩ :=
    hR s n R M t root i x E[k].row E[k + 1].row l e J hP i' x' hNC' (by rw [hlegY]; exact hY) vsY hvsY
  -- the rows of `Y`
  rw [hlegY, hY, hrowsY] at hHB
  have hz : ZeroBelow e J.target := by
    obtain ⟨_, hJOK, _⟩ := inTree_facts hctx hvs hJ
    simpa using hJOK.target
  have hsup : Row.bump J.target e = E[k + 1].row := by
    rw [hθ, hbJ]
  have hem0lt : em0.row < E[k + 1].row := by
    rw [← hsup]
    have := lt_bump_of_inRegion hem0in
    simpa using this
  have hpge : em0.row ≤ p :=
    hHB.2.2 _ (List.mem_map.mpr ⟨em0, List.mem_append_left _ hem0, rfl⟩) hem0lt
  have hpin : inRegion (e + 1) J.target p = true := by
    apply inRegion_of_between
    · exact (base_le_of_inRegion (by simpa using hz) hem0in).trans hpge
    · simpa [hsup] using hHB.2.1
  -- the node of `p`
  obtain ⟨emp, hemp, hemprow⟩ := List.mem_map.mp hHB.1
  have hempL : emp ∈ vsY.flatten := by
    rcases List.mem_append.mp hemp with h | h
    · exact h
    · obtain ⟨hU1, _⟩ := upper_facts husY
      obtain ⟨_, _, _, hτ', _⟩ := hU1 emp h
      exfalso
      have := hHB.2.1
      rw [← hemprow] at this
      exact absurd (hτ'.trans_lt (this.trans hθτ)) (lt_irrefl _)
  -- the jump
  apply jump_eq_of_coeffs
  · intro q hq
    rw [inRegion_iff'.mp hlamin q (by omega), inRegion_iff'.mp hpin q (by omega)]
  · intro he
    obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := ⟨e - 1, by omega⟩
    have h1 := hslot emp hempL (by rw [hemprow]; exact hpin) d rfl
    rw [hemprow] at h1
    have h2 : E[k].row.coeff d = (vs.flatten ++ us)[k].row.coeff d := rfl
    simp only [Nat.add_sub_cancel]
    omega

/-- **`LowerPairsHolds` from the two cases of the leg.** -/
theorem lowerPairsHolds_of_split (hGe : LowerPairsGe) (hLeft : LowerPairsLeft) :
    LowerPairsHolds := by
  intro s n R M t root i x hNC hi vs us hvs hus col hasm k hk l e p hkL hleft hθ hHB
  by_cases hcl : root.column ≤ l
  · exact hGe s n R M t root i x hNC hi vs us hvs hus col hasm k hk l e p hkL hleft hθ hHB hcl
  · exact hLeft s n R M t root i x hNC hi vs us hvs hus col hasm k hk l e p hkL hleft hθ hHB
      (by omega)

/-- **The jump law without `LowerLegGe`** (replaces `jumpLawHolds_of_lowerRows`). -/
theorem jumpLawHolds_of_rows_left (hR : LowerRowsHolds) (hLeft : LowerPairsLeft) :
    RowLaw.JumpLawHolds :=
  jumpLawHolds_of_lowerPairs (lowerPairsHolds_of_split (lowerPairsGe_of_rows hR) hLeft)

/-- **The jump law from the two cases of `LowerRowsHolds` and `LowerPairsLeft`** (replaces
`jumpLawHolds_of_lowerCases`, which used `LegBelowTop`). -/
theorem jumpLawHolds_of_lowerCases_left (hC : LowerRowsCopy) (hB : LowerRowsBoundary)
    (hLeft : LowerPairsLeft) : RowLaw.JumpLawHolds :=
  jumpLawHolds_of_rows_left (lowerRows_of_split hC hB) hLeft

end OmegaY.Official.Recon.JumpLawLowerLeft

#print axioms OmegaY.Official.Recon.JumpLawLowerLeft.lowerPairsGe_of_rows
#print axioms OmegaY.Official.Recon.JumpLawLowerLeft.lowerPairsHolds_of_split
#print axioms OmegaY.Official.Recon.JumpLawLowerLeft.jumpLawHolds_of_rows_left
#print axioms OmegaY.Official.Recon.JumpLawLowerLeft.jumpLawHolds_of_lowerCases_left
