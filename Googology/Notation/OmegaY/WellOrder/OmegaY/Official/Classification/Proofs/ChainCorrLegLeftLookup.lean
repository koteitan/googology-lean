/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/ChainCorrLegLeftLookup.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrLegLeft
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StepInnerLookupLeg
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CutPartsTop

set_option backward.do.legacy false

/-!
# `LegLookup`, `StepInner` and well-foundedness without `LegBelowTop`

`InnerLookup.legLookup_left` (`StepInnerLookupLeg.lean`) used the false `LegBelowTop` to rule
out a plain origin of `v⁺` whose leg `pa` is left of `c_r`. Such origins occur (they are the
nodes where `StartLeg` fails). With `PlainLegLeftRow` (`ChainCorrLegLeft.lean`) a plain copy
with its leg left of `c_r` keeps its row, exactly like an upper copy (`upper_row`); the rest of
the proof of `legLookup_left` is unchanged: both raw parents are the highest nodes of the shared
column `col pa` strictly below the same row.

## Results

* `legLookup_left_of_row : PlainLegLeftRow → … → rawParent R v = some pa` (replaces
  `legLookup_left`).
* `legLookup_of_legLeft`, `stepInner_of_legLeft`: `LegLookup` and `StepInner` with
  `LegBelowTop` replaced by `PlainLegLeftRow`.
* `wellFounded_of_cut_legLeft`: the replacement of `CutParts.wellFounded_of_cut_final`, with
  `StartLeg` replaced by `PlainLegLeftRow` and `StartJump` removed (proved where it is used,
  `LegLeft.startJumpGe`).
* `wellFounded_of_open_legLeft`: the same with `StepInner` replaced by its open parts
  (`stepInner_of_legLeft`).

## Numerical tests

`reference/official/startleg-left.cjs` (counts: region nodes of block `i ≥ 1` whose origin is not a
gap copy and has its leg left of `c_r`; every such origin was plain; columns: `PlainLegLeftRow`,
`pe = pa`, `StartJump`, the root bound at every scale). No failure:

| sample | expansions | nodes | failures |
|---|---:|---:|---:|
| the 64 inputs of length ≤ 6, entries ≤ 12 where `LegBelowTop` fails, `n = 1,2,3` | 192 | 402 | 0 |
| legal, length ≤ 6, entries ≤ 12, `n = 1` (all 248831 sequences) | 248831 | 67 | 0 |
| legal, length ≤ 6, entries ≤ 12, `n = 2` (first 186608 sequences, 50-minute budget) | 186130 | 116 | 0 |
| random, length ≤ 6, entries ≤ 20 (`--random 100000,6,20,41`, `n = 1`) | 44201 | 43 | 0 |
| random, length ≤ 8, entries ≤ 30 (`--random 50000,8,30,17`, `n = 1`, first 19500 sequences) | 19476 | 67 | 0 |
| random, length ≤ 10, entries ≤ 40 (`--random 50000,10,40,23`, `n = 1`, first 4588 sequences) | 4555 | 29 | 0 |

In every case the origin was plain and the leg column had no node at the row of the origin
(details and skipped inputs: `ChainCorrLegLeft.lean`).

`CopyOrder`, a hypothesis of `legLookup_of_legLeft` (through `legLookup_inner`) and of the cut
statements, is false (`CopyShapeMAFalse.lean`); this file does not repair that. `LegGapTop`, a hypothesis of
`legLookup_of_legLeft`, and `StepInner`, the conclusion of `stepInner_of_legLeft` and a
hypothesis of `wellFounded_of_cut_legLeft`, fail numerically on `(1,3,8,10,15,8)[1]`
(`notes/05-large-value-audit.md`).
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr.Inner ChainCorr.InnerLookup

/-- **`pa` left of `cr`: the raw parent of `v` is `pa`** (replaces `legLookup_left`, without
`LegBelowTop`). The origin of `v⁺` is upper or plain (a copy of the root row has its leg at or
right of `cr`); in both cases `row v⁺ = row m⁺` (`upper_row`, `PlainLegLeftRow`). -/
theorem legLookup_left_of_row (hRow : PlainLegLeftRow) {s : List Nat} {n D : Nat}
    {M : Mountain} {out : List Nat} {ρ : Root} {R : Mountain} {col : Column} {t : Cell}
    (hS : Setting s n D M out ρ R col t) {i : Nat} (hi0 : 0 < i) (hi : i < n + 1) {v m : Ref}
    (hup : CopyNode M R n ρ.cr ρ.x0 (official t.row) i (up v) (up m))
    {pa : Ref} (hpa : rawParent M m = some pa) (hlt : pa.column < ρ.cr) :
    rawParent R v = some pa := by
  obtain ⟨_, _, _, _, _, hcrx, hinv⟩ := spliceCase_data hS.splice hS.run
  obtain ⟨o', hvo', hsrc', _⟩ := copyAt_of_copyNode hup
  obtain ⟨cu, ref, co, l, hcu, hrefl, hco, hl, hrefc⟩ := copyAt_left hS hi0 hi hvo'
  rw [hsrc'] at hco
  obtain ⟨c, hc, hcl⟩ := rawParent_eq_some.mp hpa
  have hcc : c = co := Option.some.inj (hc.symm.trans hco)
  subst hcc
  have hll : pa = l := Option.some.inj (hcl.symm.trans hl)
  subst hll
  have hraw : rawParent R v = some ref := rawParent_eq_some.mpr ⟨cu, hcu, hrefl⟩
  -- the row of `v⁺` is the row of `m⁺`
  have hvo'' := hvo'
  obtain ⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, ho⟩ := hvo''
  have hSite := site_of_copyAt hS hi0 hi hcy hyx hyb hvc hes
  have hrow : cu.row = c.row := by
    cases o' with
    | upper r =>
        simp only [Origin.src] at hsrc'
        subst hsrc'
        exact upper_row hS hi0 hi hvo' hcu hco
    | plain r =>
        simp only [Origin.src] at hsrc'
        subst hsrc'
        have hcu' : cell? R ⟨(up v).column, j + 1⟩ = some cu := by
          rw [← hvi]; exact hcu
        exact hRow s n D M out ρ R t _ y i es hSite j hj (up m) ho cu c pa hcu' hco hcl hlt
    | clean r b =>
        exfalso
        simp only [Origin.src] at hsrc'
        subst hsrc'
        obtain ⟨C, cs, hcs, ref', cl', hn, hr⟩ :=
          emitsT_cleanAsc hes es[j] (List.getElem_mem hj) (up m) b ho
        simp only [ctxAt] at hcs hn hr
        obtain ⟨_, _, hcscell, _⟩ := Classification.nodeAt_spec hcs
        have hcs' : cs = c := Option.some.inj (hcscell.symm.trans hco)
        subst hcs'
        have h := leg_of_ascension hS.splice.build hcy hn hr hcs hl
        omega
  -- both raw parents are the highest nodes strictly below the upper nodes
  obtain ⟨cpe, hcpe, hlt1, hmax1⟩ :=
    canonical_rawParent_highest_below (build_success_legal hS.canon) hS.canon (u := v) hcu hraw
  obtain ⟨cpa, hcpa, hlt2, hmax2⟩ :=
    canonical_rawParent_highest_below (build_success_legal hS.splice.build) hS.splice.build
      (u := m) hco hpa
  have hrefcol : ref.column = pa.column := by rw [hrefc, mapColumn_of_lt hlt]
  have hA := hinv.1
  have hi1 : ref.index ≤ pa.index := by
    apply hmax2 ref.index cpe
    · have h1 : (⟨pa.column, ref.index⟩ : Ref) = ref := ref_eq_of hrefcol.symm rfl
      rw [h1, ← cell?_agree hA (by omega)]
      exact hcpe
    · rw [← hrow]; exact hlt1
  have hi2 : pa.index ≤ ref.index := by
    apply hmax1 pa.index cpa
    · have h1 : (⟨ref.column, pa.index⟩ : Ref) = pa := ref_eq_of hrefcol rfl
      rw [h1, cell?_agree hA (by omega)]
      exact hcpa
    · rw [hrow]; exact hlt2
  have href : ref = pa := ref_eq_of hrefcol (le_antisymm hi1 hi2)
  rw [← href]
  exact hraw

/-- **`LegLookup` without `LegBelowTop`.** -/
theorem legLookup_of_legLeft (hA : ChainCorr.CopyOrder) (hB : Inner.CopyEmitted)
    (hC2 : Inner.CopyFirst) (hRow : PlainLegLeftRow) (hG : LegGapTop)
    (hBC : ChainCorr.BoundaryChain) (hO : LegOriginReach) : Inner.LegLookup := by
  intro s n D M out ρ R col t hS i hi0 hi v m hvm hup pa hpa cv hcv
  obtain ⟨pe, hraw, _, hpe⟩ := legLookup_common hS hi0 hi hvm hup hpa hcv
  refine ⟨pe, hpe, fun hlt => ?_, fun heq => ?_, fun hlt => ?_⟩
  · have h := legLookup_left_of_row hRow hS hi0 hi hup hpa hlt
    exact Option.some.inj (hraw.symm.trans h)
  · exact legLookup_root hBC hO hS hi0 hi hvm hup hpa heq hraw hpe
  · rw [mapColumn_of_ge (le_of_lt hlt)] at hpe
    exact legLookup_inner hA hB hC2 hG hS hi0 hi hvm hup hpa hlt hcv hpe

/-- **`StepInner` without `LegBelowTop`** (replaces `InnerLookup.stepInner_of_open`). -/
theorem stepInner_of_legLeft (hA : ChainCorr.CopyOrder) (hB : Inner.CopyEmitted)
    (hC2 : Inner.CopyFirst) (hRow : PlainLegLeftRow) (hG : LegGapTop)
    (hBC : ChainCorr.BoundaryChain) (hO : LegOriginReach) (hCN : Inner.CleanNext)
    (hCL : Inner.CleanLookup) (hCP : Inner.CleanParent) : StepInner :=
  Inner.stepInner_of_rest hB hC2 (legLookup_of_legLeft hA hB hC2 hRow hG hBC hO)
    (bumpCopyLower_of_copyFirst hC2) hCN hCL hCP

/-! ## Well-foundedness -/

/-- **Well-foundedness of the official expansion without `StartLeg` and `StartJump`** (replaces
`CutParts.wellFounded_of_cut_final`). -/
theorem wellFounded_of_cut_legLeft (hrec : Dimension.BlockReconstruction) (hStep : StepInner)
    (hRow : PlainLegLeftRow) (hCopy : StartCopy) (hRoot : StartRoot)
    (hA : ChainCorr.CopyOrder) (hB : ChainCorr.CopyEmitted)
    (hC2 : ChainCorr.CopyFirst) (hBC : ChainCorr.BoundaryChain)
    (hBump : CutParts.CutBump) (hLeg : CutParts.CutLegLookup) (hLow : CutParts.CutRunLow)
    (hHigh : CutParts.CutRunHigh) (hOR : CutParts.CutOriginReach) (hJT : CutParts.CutJumpTop) :
    WellFounded Step := by
  obtain ⟨h1, h2, h3, h4⟩ :=
    CutParts.cut_statements_final hStep hA hB hC2 hBC hBump hLeg hLow hHigh hOR hJT
  exact wellFounded_of_legLeft hrec hStep hRow hA hB hCopy hRoot
    (regionCutBoundary_of_chains' hStep h1 h2 h3 h4) (regionCutInner_of_chains' hStep h1 h2 h3 h4)

/-- **Well-foundedness of the official expansion from the open statements, without the false
`LegBelowTop` / `StartLeg`.** `StepInner` is replaced by its parts (`stepInner_of_legLeft`). -/
theorem wellFounded_of_open_legLeft (hrec : Dimension.BlockReconstruction)
    (hRow : PlainLegLeftRow) (hCopy : StartCopy) (hRoot : StartRoot)
    (hA : ChainCorr.CopyOrder) (hB : ChainCorr.CopyEmitted) (hB' : Inner.CopyEmitted)
    (hC2 : ChainCorr.CopyFirst) (hC2' : Inner.CopyFirst) (hBC : ChainCorr.BoundaryChain)
    (hG : LegGapTop)
    (hO : LegOriginReach) (hCN : Inner.CleanNext) (hCL : Inner.CleanLookup)
    (hCP : Inner.CleanParent)
    (hBump : CutParts.CutBump) (hLeg : CutParts.CutLegLookup) (hLow : CutParts.CutRunLow)
    (hHigh : CutParts.CutRunHigh) (hOR : CutParts.CutOriginReach) (hJT : CutParts.CutJumpTop) :
    WellFounded Step :=
  wellFounded_of_cut_legLeft hrec
    (stepInner_of_legLeft hA hB' hC2' hRow hG hBC hO hCN hCL hCP) hRow hCopy hRoot hA hB hC2
    hBC hBump hLeg hLow hHigh hOR hJT

end OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft.legLookup_left_of_row
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft.legLookup_of_legLeft
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft.stepInner_of_legLeft
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft.wellFounded_of_cut_legLeft
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft.wellFounded_of_open_legLeft
