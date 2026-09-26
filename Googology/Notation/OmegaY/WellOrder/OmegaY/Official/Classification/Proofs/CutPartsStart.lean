/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CutPartsStart.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrCutLeg
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrStartRoot
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrCopyMono
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrStepInner

set_option backward.do.legacy false

/-!
# The three start statements of the gap-copy regions

`ChainCorrCut.lean` reduces the two gap-copy regions (`RegionCutBoundary`, `RegionCutInner`)
to `StepInner` and five statements about gap copies. `CutLeg` is proved
(`ChainCorrCutLeg.lean`). This file reduces three of the other four to smaller statements:

* `CutStartCopy` (for a leg `l > cr`, the node `pe` is the gap copy of `pa`) follows from the
  column profile of `ChainCorrStartCopy.lean` (`CopyOrder`, `CopyFirst`; `CopyMono` is proved)
  and two statements about the run of gap copies of `pa` in the copy of the column `l`:
  `CutRunLow` (the run starts at or below the row of `u`) and `CutRunHigh` (the non-cut copies of
  the nodes above `pa` lie above the row of `u`): `cutStartCopy_of_parts`.
* `CutStartRoot` (for the leg `cr`) follows from `BoundaryChain` (`ChainCorrStartRoot.lean`, the
  same statement as for `StartRoot`) and `CutOriginReach` (the chain of `M(s)` from the origin
  of `pe` reaches the next node of the chain of `pa`): `cutStartRoot_of_parts`.
* `CutJump` holds trivially when `pe` is at the row of `u` (the jump is `0`); the rest is
  `CutJumpTop`: `cutJump_of_top`.

`CutPaRow` (the node `pa` is at the row of the origin, so `d_a = 0`) is stated here, used by
the reduction of `StepCut` (`CutPartsStep.lean`) and proved in `CutPartsPaRow.lean`.

All declarations are in the namespace `ChainCorr.CutParts`.

## Notation

For a gap copy `u = (X, j + 1)` (origin `o = (x, C)`, `.clean o true`) of block `i ≥ 1`: `l` is
the leg of `o`, `pa` the highest node of the column `l` of `M(s)` at or below `C`, `pe` the
highest node of the output column `φ(l)` at or below the row of `u` (the parents of the key
templates of the two leg atoms, `Legs`).

## Numerical tests

`reference/official/cut-parts.cjs` (counts: gap copies, and node-scale pairs for
`CutOriginReach`). No failure.

| sample | expansions | `CutPaRow` | `CutRunLow`, `CutRunHigh` | `CutOriginReach` | `CutJumpTop` (used / same row) |
|---|---:|---:|---:|---:|---:|
| standard S1–S3, S6, `n = 1,2,3` | 39090 | 925614 | 579105 | 408748 | 107406 / 818208 |
| legal, length ≤ 6, entries ≤ 6 | 23325 | 225731 | 127549 | 0 (no case) | 53588 / 172143 |
| legal, length ≤ 5, entries ≤ 8 | 12285 | 467536 | 304226 | 1118 | 147565 / 319971 |
| random legal (`--random 20000,10,10,7`) | 37926 | 3941178 | 2960694 | 10298 | 1218235 / 2722943 |
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.CutParts

open Canonical Reserve Official Descent Classification Proofs

/-! ## The statements -/

/-- The node `pa` is at the row of the origin of a gap copy (proved: `cutPaRow`,
`CutPartsPaRow.lean`). -/
def CutPaRow : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = true →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      cpa.row = cv.row

/-- (open) For a leg `l > cr`, the copy of the column `l` in block `i` has a gap copy of `pa`
at or below the row of `u`. -/
def CutRunLow : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = true →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      ρ.cr < l.column →
      ∀ esl, blockEmits M R ρ.cr ρ.x0 (official t.row) i l.column = .ok esl →
        ∃ k, ∃ hk : k < esl.length, esl[k].2 = .clean pa true ∧ esl[k].1.row ≤ es[j].1.row

/-- (open) For a leg `l > cr`, every non-cut emit of the copy of the column `l` in block `i`
whose origin is above `pa` lies above the row of `u`. -/
def CutRunHigh : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = true →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      ρ.cr < l.column →
      ∀ esl, blockEmits M R ρ.cr ρ.x0 (official t.row) i l.column = .ok esl →
      ∀ k (hk : k < esl.length), cutOrigin esl[k].2 = false →
      ∀ c, cell? M esl[k].2.src = some c → cpa.row < c.row → es[j].1.row < esl[k].1.row

/-- (open) For the leg `cr`, the chain of `M(s)` from the origin of `pe` reaches the next node
of the chain of `pa` (`OriginReach` for gap copies). -/
def CutOriginReach : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = true →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      l.column = ρ.cr →
      ∀ esB, blockEmits M R ρ.cr ρ.x0 (official t.row) (i - 1) ρ.x0 = .ok esB →
      ∀ k (hk : k < esB.length), pe.index = k + 1 →
      ∀ kk m'', Row.jump cv.row cpa.row ≤ kk → MStep M kk pa m'' →
        ScaleReach M kk esB[k].2.src m''

/-- (open) `CutJump` when `pe` is not at the row of `u`. -/
def CutJumpTop : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = true →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      cpe.row ≠ cu.row →
      Row.jump cu.row cpe.row ≤ Row.jump cv.row cpa.row ∨
      ∃ k', Row.jump cu.row cpe.row ≤ k' ∧ Row.jump cv.row cpa.row ≤ k' ∧ k' ≤ D ∧
        (root R k' pe).column < mapColumn ρ.cr ((ρ.x0 - ρ.cr) * i) (root M k' pa).column

/-! ## `CutJump` -/

/-- **`CutJump` from `CutJumpTop`.** -/
theorem cutJump_of_top (h : CutJumpTop) : CutJump := by
  intro s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe cpa hL
  by_cases hr : cpe.row = cu.row
  · left
    rw [hr, Row.jump_self]
    exact Nat.zero_le _
  · exact h s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe cpa hL hr

/-! ## `CutStartRoot` -/

/-- **`CutStartRoot` from `BoundaryChain` and `CutOriginReach`.** -/
theorem cutStartRoot_of_parts (hB : BoundaryChain) (hO : CutOriginReach) : CutStartRoot := by
  intro s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL heq kk m'' hk _ hst
  have hdat := hS.data
  obtain ⟨col', t', hcol', ht', _, hcrx, hinv⟩ := spliceCase_data hS.splice hS.run
  have htt : t' = t := by
    obtain ⟨col, hcol, ht⟩ := hS.last
    have : col' = col := Option.some.inj (hcol'.symm.trans hcol)
    subst this
    exact Option.some.inj (ht'.symm.trans ht)
  subst t'
  have hipos := hS.iPos
  -- the leg column is the boundary column `B`
  have himg := leg_image hS hj hL
  rw [heq, mapColumn_of_ge (le_refl _), boundary_eq hcrx hipos] at himg
  obtain ⟨hpecol, hpe0, colB, hcolB, hpeB, _, _⟩ := highestAtMost_spec hL.hpe
  obtain ⟨hBsz, _⟩ := column_of_getElem? hcolB
  have hB0 : ρ.x0 ≤ ref.column := by rw [himg]; omega
  obtain ⟨i', x', hi', hx', hBeq, hcopyB⟩ := hinv.2.2 ref.column hBsz hB0
  obtain ⟨hii, hxx⟩ := block_unique_boundary hcrx hx' (by rw [← himg]; exact hBeq)
  subst i' x'
  have hcolB' : R[ref.column]? = some R[ref.column] := Array.getElem?_eq_getElem hBsz
  have hcc : colB = R[ref.column] := Option.some.inj (hcolB.symm.trans hcolB')
  obtain ⟨esB, hesB, _⟩ := copyColumn_emitsT hcopyB
  obtain ⟨hszB, _⟩ := cells_of_copy hcolB' hcopyB hesB
  have hbl : blockEmits M R ρ.cr ρ.x0 (official t.row) (i - 1) ρ.x0 = .ok esB := by
    have h' : ρ.x0 + (ρ.x0 - ρ.cr) * (i - 1) = ref.column := himg.symm
    simp only [blockEmits, h']
    exact hesB
  have hksl : pe.index - 1 < esB.length := by
    have : pe.index < colB.size := hpeB
    rw [hcc, hszB] at this
    omega
  have hpeidx : pe.index = pe.index - 1 + 1 := by omega
  have hreachM := hO s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL heq esB
    hbl (pe.index - 1) hksl hpeidx kk m'' hk hst
  have hpacol : pa.column = ρ.cr := by
    rw [(highestAtMost_spec hL.hpa).1, heq]
  have hm'' : m''.column < ρ.cr := hpacol ▸ hst.column_lt
  have hreachR := hB s n D M out ρ R t hdat i hipos hS.iLt esB hbl (pe.index - 1) hksl kk m''
    hm'' hreachM
  have hpe : pe = ⟨ρ.x0 + (ρ.x0 - ρ.cr) * (i - 1), pe.index - 1 + 1⟩ :=
    ref_eq_of (by rw [hpecol, himg]) hpeidx
  rw [hpe]
  exact hreachR

/-! ## `CutStartCopy` -/

/-- **`CutStartCopy` from the profile of a block and the run of gap copies of `pa`.** -/
theorem cutStartCopy_of_parts (hA : CopyOrder) (hC2 : CopyFirst) (hLow : CutRunLow)
    (hHigh : CutRunHigh) : CutStartCopy := by
  intro s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe cpa hL hlt
  have hdat := hS.data
  have hV := build_valid_of_success hS.splice.build
  have hVR := build_valid_of_success hS.canon
  obtain ⟨col', t', hcol', ht', _, hcrx, hinv⟩ := spliceCase_data hS.splice hS.run
  have htt : t' = t := by
    obtain ⟨col, hcol, ht⟩ := hS.last
    have : col' = col := Option.some.inj (hcol'.symm.trans hcol)
    subst this
    exact Option.some.inj (ht'.symm.trans ht)
  subst t'
  obtain ⟨hcx, hxx⟩ := mem_blockColumns_pos hS.xMem hS.iPos
  have hipos := hS.iPos
  -- the leg column of the origin
  have himg := leg_image hS hj hL
  rw [mapColumn_of_ge (le_of_lt hlt)] at himg
  obtain ⟨hsrc, _, _, _, _⟩ := emitsT_good hS.emits es[j] (List.getElem_mem hj)
  have hly : l.column < es[j].2.src.column := left_lt_of_valid hV hL.hcv hL.hl
  have hsrcle : es[j].2.src.column ≤ ρ.x0 := by
    rw [hsrc]
    split
    · exact upperColumn_le hcrx.le hxx
    · exact hxx
  have hyx : l.column < ρ.x0 := by omega
  have hymem : l.column ∈ blockColumns ρ.cr ρ.x0 n i := by
    unfold blockColumns
    rw [if_neg (by omega)]
    simp only [List.mem_range'_1]
    split <;> omega
  -- the column `L = l + w·i` of the output
  obtain ⟨hpecol, hpe0, colL, hcolL, hpeL, hperow, hpemax⟩ := highestAtMost_spec hL.hpe
  have hL0 : ρ.x0 ≤ ref.column := by
    rw [himg]
    have : ρ.x0 - ρ.cr ≤ (ρ.x0 - ρ.cr) * i := Nat.le_mul_of_pos_right _ hipos
    omega
  obtain ⟨hLsz, _⟩ := column_of_getElem? hcolL
  obtain ⟨i', x', hi', hx', hLeq, hcopyL⟩ := hinv.2.2 ref.column hLsz hL0
  obtain ⟨hii, hxy⟩ := blockCol_unique_inner hcrx hlt hyx hipos hx' (by rw [← himg]; exact hLeq)
  subst i' x'
  have hcolL' : R[ref.column]? = some R[ref.column] := Array.getElem?_eq_getElem hLsz
  have hcc : colL = R[ref.column] := Option.some.inj (hcolL.symm.trans hcolL')
  obtain ⟨esl, hesl, _⟩ := copyColumn_emitsT hcopyL
  obtain ⟨hszL, hcellsL⟩ := cells_of_copy hcolL' hcopyL hesl
  have hbl : blockEmits M R ρ.cr ρ.x0 (official t.row) i l.column = .ok esl := by
    have h' : l.column + (ρ.x0 - ρ.cr) * i = ref.column := himg.symm
    simp only [blockEmits, h']
    exact hesl
  -- the row of the node `u`
  obtain ⟨cX, hRX, hcopyX⟩ := hS.copy
  obtain ⟨_, hcellsX⟩ := cells_of_copy hRX hcopyX hS.emits
  obtain ⟨cellu, hcellu, hrowu⟩ := hcellsX j hj
  have hrowcu : cu.row = stored es[j].1.row := by
    rw [Option.some.inj (hL.hcu.symm.trans hcellu)]
    exact hrowu
  -- the index of `pe`
  have hksl : pe.index - 1 < esl.length := by
    have : pe.index < colL.size := hpeL
    rw [hcc, hszL] at this
    omega
  have hpeidx : pe.index = (pe.index - 1) + 1 := by omega
  have hrowL : ∀ k (hk : k < esl.length) (hk' : k + 1 < colL.size),
      (colL[k + 1]'hk').row = stored esl[k].1.row := by
    intro k hk hk'
    obtain ⟨cell, hcell, hrow⟩ := hcellsL k hk
    obtain ⟨col', hcol', hp', hcell'⟩ := cell?_column hcell
    simp only at hcol' hp' hcell'
    have : col' = colL := Option.some.inj (hcol'.symm.trans hcolL)
    subst this
    rw [hcell', hrow]
  have hle_ks : ∀ k (hk : k < esl.length), esl[k].1.row ≤ es[j].1.row → k ≤ pe.index - 1 := by
    intro k hk hrk
    have hk' : k + 1 < colL.size := by rw [hcc, hszL]; omega
    have h1 := hpemax (k + 1) hk' (by omega) (by
      rw [hrowL k hk hk', hrowcu]
      exact stored_mono hrk)
    omega
  have hks_le : esl[pe.index - 1].1.row ≤ es[j].1.row := by
    have h1 : (colL[pe.index]'hpeL).row ≤ cu.row := hperow
    have hk' : pe.index - 1 + 1 < colL.size := by omega
    have h2 := hrowL (pe.index - 1) hksl hk'
    have h3 : (colL[pe.index]'hpeL) = (colL[pe.index - 1 + 1]'hk') := by
      congr 1
    rw [h3, h2, hrowcu] at h1
    exact stored_le_iff.mp h1
  have hmonoL : ∀ k k' (hk : k < esl.length) (hk' : k' < esl.length), k ≤ k' →
      esl[k].1.row ≤ esl[k'].1.row := by
    intro k k' hk hk' hkk
    rcases Nat.lt_or_eq_of_le hkk with h | h
    · obtain ⟨c1, hc1, hr1⟩ := hcellsL k hk
      obtain ⟨c2, hc2, hr2⟩ := hcellsL k' hk'
      have := cell_row_lt hVR hc1 hc2 (by omega)
      rw [hr1, hr2] at this
      exact le_of_lt (stored_lt_iff.mp this)
    · subst h
      exact le_refl _
  have hstrictL : ∀ k k' (hk : k < esl.length) (hk' : k' < esl.length), k < k' →
      esl[k].1.row < esl[k'].1.row := by
    intro k k' hk hk' hkk
    obtain ⟨c1, hc1, hr1⟩ := hcellsL k hk
    obtain ⟨c2, hc2, hr2⟩ := hcellsL k' hk'
    have := cell_row_lt hVR hc1 hc2 (by omega)
    rw [hr1, hr2] at this
    exact stored_lt_iff.mp this
  -- the node `pa` of `M(s)`
  obtain ⟨hpacol, hpa0, colY, hcolY, hpaY, hparow, hpamax⟩ := highestAtMost_spec hL.hpa
  -- the gap copy of `pa` at or below the row of `u` (`CutRunLow`)
  obtain ⟨kg, hkg, hkgo, hkgrow⟩ :=
    hLow s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe cpa hL hlt esl hbl
  have hkgsrc : esl[kg].2.src = pa := by rw [hkgo]; rfl
  have hkgcut : cutOrigin esl[kg].2 = true := by rw [hkgo]; rfl
  have hkg_le : kg ≤ pe.index - 1 := hle_ks kg hkg hkgrow
  have hcpag : cell? M esl[kg].2.src = some cpa := by rw [hkgsrc]; exact hL.hcpa
  -- the origin `ν` of the emit at `pe.index - 1`
  obtain ⟨hνcol, hν1, cν, hcν⟩ := src_of_inner (ne_of_lt hyx) hbl (pe.index - 1) hksl
  have hmono := copyMono s n D M out ρ R t hdat i hipos hS.iLt l.column esl hlt hyx hbl kg
    (pe.index - 1) hkg hksl hkg_le cpa cν hcpag hcν
  -- the first emit of an origin
  have first : ∀ k (hk : k < esl.length), ∃ k0, ∃ hk0 : k0 < esl.length, k0 ≤ k ∧
      esl[k0].2.src = esl[k].2.src ∧ cutOrigin esl[k0].2 = false := by
    intro k hk
    classical
    have hex : ∃ k', ∃ hk' : k' < esl.length, esl[k'].2.src = esl[k].2.src := ⟨k, hk, rfl⟩
    obtain ⟨hk0l, hk0src⟩ := Nat.find_spec hex
    have hmin : ∀ k' (hk' : k' < esl.length), k' < Nat.find hex →
        esl[k'].2.src ≠ esl[Nat.find hex].2.src := by
      intro k' hk' hlt' heq'
      exact Nat.find_min hex hlt' ⟨hk', heq'.trans hk0src⟩
    refine ⟨Nat.find hex, hk0l, ?_, hk0src, ?_⟩
    · by_contra hn
      exact Nat.find_min hex (by omega : k < Nat.find hex) ⟨hk, rfl⟩
    · exact hC2 s n D M out ρ R t hdat i hipos hS.iLt l.column esl hlt hyx hbl (Nat.find hex)
        hk0l hmin
  -- the origin row of the emit at `pe.index - 1` is the row of `pa` (`CutRunHigh`)
  have hνrow : cν.row = cpa.row := by
    refine le_antisymm ?_ hmono
    by_contra hn
    have hgt : cpa.row < cν.row := lt_of_not_ge hn
    obtain ⟨k0, hk0, hk0le, hk0src, hk0nc⟩ := first (pe.index - 1) hksl
    have hc0 : cell? M esl[k0].2.src = some cν := by rw [hk0src]; exact hcν
    have h1 := hHigh s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe cpa hL hlt esl
      hbl k0 hk0 hk0nc cν hc0 hgt
    have h2 := hmonoL k0 (pe.index - 1) hk0 hksl hk0le
    exact absurd (lt_of_lt_of_le h1 (le_trans h2 hks_le)) (lt_irrefl _)
  -- so the origin is `pa`
  have hνpa : esl[pe.index - 1].2.src = pa :=
    Inner.cell?_eq_of_index hV (by rw [hνcol, hpacol]) hcν hL.hcpa hνrow
  -- and it is a gap copy
  have hcutk : cutOrigin esl[pe.index - 1].2 = true := by
    cases hc : cutOrigin esl[pe.index - 1].2
    · exfalso
      have hne : kg ≠ pe.index - 1 := by
        intro h
        subst h
        rw [hkgcut] at hc
        cases hc
      obtain ⟨k1, hk1, hk1le, hk1src, hk1nc⟩ := first kg hkg
      have hk1ne : k1 ≠ kg := by
        intro h
        subst h
        rw [hkgcut] at hk1nc
        cases hk1nc
      have hc1 : cell? M esl[k1].2.src = some cpa := by rw [hk1src]; exact hcpag
      have hck : cell? M esl[pe.index - 1].2.src = some cpa := by rw [hνpa]; exact hL.hcpa
      have hA' := hA s n D M out ρ R t hdat i hipos hS.iLt l.column l.column esl esl hymem hymem
        hbl hbl k1 hk1 (pe.index - 1) hksl hk1nc hc cpa cpa hc1 hck
      have hrow := hA'.2 rfl
      have := hstrictL k1 (pe.index - 1) hk1 hksl (by omega)
      rw [hrow] at this
      exact lt_irrefl _ this
    · rfl
  exact ⟨l.column, esl, pe.index - 1, hlt, hyx, hymem, by rw [hpecol, himg], hpeidx,
    by rw [hpecol]; exact hesl, hksl, hνpa, hcutk⟩

end OmegaY.Official.Classification.Proofs.ChainCorr.CutParts

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.CutParts.cutJump_of_top
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.CutParts.cutStartRoot_of_parts
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.CutParts.cutStartCopy_of_parts
