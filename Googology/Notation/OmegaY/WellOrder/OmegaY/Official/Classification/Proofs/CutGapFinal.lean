/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CutGapFinal.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CutGapRunLow
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CutGapFG
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeNoMA
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CutGapAdj
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CutGapPaLookup

set_option backward.do.legacy false

/-!
# The gap-copy statements without (MA) (`CutGap`)

(MA) and `ChainCorr.CopyOrder` are false (`CopyShapeMAFalse.lean`). This file closes what the
earlier reductions of the gap-copy regions derived from them:

* `cutRunLow` (**proved**): `CutRunLow` from `legOrder` (`CutGapLegOrder.lean`), `fgHolds`
  (`CutGapFG.lean`) and `CopyShape.NoMA.copyEmitted` (`CopyShapeNoMA.lean`, proved there
  without (MA)).
* `cutRunHigh` (**proved**, `CutGapLegOrder.lean`).
* `cutStartCopy'` (**proved**): `ChainCorr.CutStartCopy`. The argument of
  `CutParts.cutStartCopy_of_parts` used `CopyOrder` only for two emits of one column; that case
  is `CopyShape.NoMA.copyOrderSame` (proved).
* `topNext'` (**proved**) and `cutTopLookup_of_bump_leg`: `CutTopLookup` from `CutBump` and
  `CutLegLookup` alone (the argument of `CutParts.cutTopLookup_of_parts`, with `CopyOrder`
  replaced by `copyOrderSame`, and `CopyEmitted`, `CopyFirst` by the proved ones).
* `cutBump` (**proved**, `CutGapAdj.lean`), so `cutTopLookup_of_leg`: `CutTopLookup` from
  `CutLegLookup` alone.
* `cutOriginReach` (**proved**, `CutGapPaLookup.lean`, from `CutPaLookup` and `X0Reach`).
* `cut_statements_noMA`: the four gap-copy statements of `ChainCorrCut.lean` from `StepInner`,
  `BoundaryChain` and the two open statements `CutLegLookup`, `CutJumpTop`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace OmegaY.Official.Classification.Proofs.CutGap

/-- **`CutRunLow` holds.** -/
theorem cutRunLow : ChainCorr.CutParts.CutRunLow :=
  cutRunLow_of_facts CopyShape.NoMA.copyEmitted fgHolds

end OmegaY.Official.Classification.Proofs.CutGap

namespace OmegaY.Official.Classification.Proofs.ChainCorr.CutParts

open Canonical Reserve Official Descent Classification Proofs

/-- **`CutStartCopy` holds.** -/
theorem cutStartCopy' : CutStartCopy := by
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
    CutGap.cutRunLow s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe cpa hL hlt esl hbl
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
    · exact CopyShape.NoMA.copyFirst s n D M out ρ R t hdat i hipos hS.iLt l.column esl hlt hyx hbl (Nat.find hex)
        hk0l hmin
  -- the origin row of the emit at `pe.index - 1` is the row of `pa` (`CutRunHigh`)
  have hνrow : cν.row = cpa.row := by
    refine le_antisymm ?_ hmono
    by_contra hn
    have hgt : cpa.row < cν.row := lt_of_not_ge hn
    obtain ⟨k0, hk0, hk0le, hk0src, hk0nc⟩ := first (pe.index - 1) hksl
    have hc0 : cell? M esl[k0].2.src = some cν := by rw [hk0src]; exact hcν
    have h1 := CutGap.cutRunHigh s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe cpa hL hlt esl
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
      have hA' := CopyShape.NoMA.copyOrderSame s n D M out ρ R t hdat i hipos hS.iLt l.column esl
        hymem hbl k1 hk1 (pe.index - 1) hksl hk1nc hc cpa cpa hc1 hck
      have hrow := hA'.2 rfl
      have := hstrictL k1 (pe.index - 1) hk1 hksl (by omega)
      rw [hrow] at this
      exact lt_irrefl _ this
    · rfl
  exact ⟨l.column, esl, pe.index - 1, hlt, hyx, hymem, by rw [hpecol, himg], hpeidx,
    by rw [hpecol]; exact hesl, hksl, hνpa, hcutk⟩


theorem topNext'
    {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} {X x i : Nat} {es : List (Emit × Origin)}
    (hS : Site s n D M out ρ R t X x i es) (hx : x < ρ.x0) {j : Nat} (hj : j < es.length)
    (hcut : cutOrigin es[j].2 = true)
    (hnot : ∀ hj' : j + 1 < es.length, es[j + 1].2 ≠ es[j].2)
    {c : Cell} (hc : cell? M (Inner.up es[j].2.src) = some c) :
    ∃ hj1 : j + 1 < es.length, es[j + 1].2.src = Inner.up es[j].2.src ∧
      cutOrigin es[j + 1].2 = false := by
  have hdat := hS.data
  have hV := build_valid_of_success hS.splice.build
  have hVR := build_valid_of_success hS.canon
  obtain ⟨hcx, _⟩ := mem_blockColumns_pos hS.xMem hS.iPos
  have hipos := hS.iPos
  have hbl : blockEmits M R ρ.cr ρ.x0 (official t.row) i x = .ok es := by
    simp only [blockEmits, ← hS.Xeq]
    exact hS.emits
  obtain ⟨cX, hRX, hcopyX⟩ := hS.copy
  obtain ⟨_, hcellsX⟩ := cells_of_copy hRX hcopyX hS.emits
  have hstrict : ∀ k k' (hk : k < es.length) (hk' : k' < es.length), k < k' →
      es[k].1.row < es[k'].1.row := by
    intro k k' hk hk' hkk
    obtain ⟨c1, hc1, hr1⟩ := hcellsX k hk
    obtain ⟨c2, hc2, hr2⟩ := hcellsX k' hk'
    have := cell_row_lt hVR hc1 hc2 (by omega)
    rw [hr1, hr2] at this
    exact stored_lt_iff.mp this
  -- the origin of the gap copy
  obtain ⟨hoc, ho1, cm, hcm⟩ := src_of_inner (ne_of_lt hx) hbl j hj
  set o := es[j].2.src with ho
  have hup : (Inner.up o).column = x := by simp [Inner.up, hoc]
  have hlt_row : cm.row < c.row := by
    have h1 : cell? M ⟨x, o.index⟩ = some cm := by rw [← hoc]; exact hcm
    have h2 : cell? M ⟨x, o.index + 1⟩ = some c := by rw [← hoc]; exact hc
    exact cell_row_lt hV h1 h2 (by omega)
  -- the non-cut copy of `m⁺`
  obtain ⟨k', hk', hk'src, hk'nc⟩ := CopyShape.NoMA.copyEmitted s n D M out ρ R t hdat i hipos hS.iLt x es hcx hx hbl
    (Inner.up o) c hup (by simp [Inner.up]) hc
  have hck' : cell? M es[k'].2.src = some c := by rw [hk'src]; exact hc
  have hjk : j < k' := by
    by_contra hn
    have := copyMono s n D M out ρ R t hdat i hipos hS.iLt x es hcx hx hbl k' j hk' hj (by omega)
      c cm hck' hcm
    exact absurd hlt_row (not_lt.mpr this)
  have hj1 : j + 1 < es.length := by omega
  -- the origin `ν` of the emit `j + 1`
  obtain ⟨hνc, hν1, cν, hcν⟩ := src_of_inner (ne_of_lt hx) hbl (j + 1) hj1
  have hm1 := copyMono s n D M out ρ R t hdat i hipos hS.iLt x es hcx hx hbl j (j + 1) hj hj1
    (by omega) cm cν hcm hcν
  have hm2 := copyMono s n D M out ρ R t hdat i hipos hS.iLt x es hcx hx hbl (j + 1) k' hj1 hk'
    (by omega) cν c hcν hck'
  have hν' : cell? M ⟨x, es[j + 1].2.src.index⟩ = some cν := by rw [← hνc]; exact hcν
  have ho' : cell? M ⟨x, o.index⟩ = some cm := by rw [← hoc]; exact hcm
  have hu' : cell? M ⟨x, o.index + 1⟩ = some c := by rw [← hoc]; exact hc
  have hi1 := cell_index_le hV ho' hν' hm1
  have hi2 := cell_index_le hV hν' hu' hm2
  -- the first emit of an origin is non-cut
  have first : ∀ k (hk : k < es.length), ∃ k0, ∃ hk0 : k0 < es.length, k0 ≤ k ∧
      es[k0].2.src = es[k].2.src ∧ cutOrigin es[k0].2 = false := by
    intro k hk
    classical
    have hex : ∃ k1, ∃ hk1 : k1 < es.length, es[k1].2.src = es[k].2.src := ⟨k, hk, rfl⟩
    obtain ⟨hk0l, hk0src⟩ := Nat.find_spec hex
    have hmin : ∀ k1 (hk1 : k1 < es.length), k1 < Nat.find hex →
        es[k1].2.src ≠ es[Nat.find hex].2.src := by
      intro k1 hk1 hlt' heq'
      exact Nat.find_min hex hlt' ⟨hk1, heq'.trans hk0src⟩
    refine ⟨Nat.find hex, hk0l, ?_, hk0src, ?_⟩
    · by_contra hn
      exact Nat.find_min hex (by omega : k < Nat.find hex) ⟨hk, rfl⟩
    · exact CopyShape.NoMA.copyFirst s n D M out ρ R t hdat i hipos hS.iLt x es hcx hx hbl (Nat.find hex) hk0l hmin
  rcases Nat.lt_or_eq_of_le hi1 with hlt | heq
  · -- the origin of the emit `j + 1` is `m⁺`
    have hidx : es[j + 1].2.src.index = o.index + 1 := by omega
    have hνu : es[j + 1].2.src = Inner.up o :=
      ref_eq_of (by rw [hνc, hup]) (by simp [Inner.up, hidx])
    refine ⟨hj1, hνu, ?_⟩
    -- it is the first emit of `m⁺`
    obtain ⟨k0, hk0, hk0le, hk0src, hk0nc⟩ := first (j + 1) hj1
    rcases Nat.lt_or_eq_of_le hk0le with hlt0 | heq0
    · exfalso
      have hc0 : cell? M es[k0].2.src = some c := by rw [hk0src, hνu]; exact hc
      have := copyMono s n D M out ρ R t hdat i hipos hS.iLt x es hcx hx hbl k0 j hk0 hj
        (by omega) c cm hc0 hcm
      exact absurd hlt_row (not_lt.mpr this)
    · subst heq0
      exact hk0nc
  · -- the origin of the emit `j + 1` would be `m`: impossible
    exfalso
    have hνo : es[j + 1].2.src = o := ref_eq_of (by rw [hνc, hoc]) heq.symm
    have hne := hnot hj1
    have hnc : cutOrigin es[j + 1].2 = false := by
      cases hcj : cutOrigin es[j + 1].2
      · rfl
      · exfalso
        apply hne
        have h1 : ∃ r, es[j + 1].2 = .clean r true := by
          generalize es[j + 1].2 = o' at hcj
          cases o' with
          | clean r b => cases b <;> simp_all [cutOrigin]
          | plain r => simp [cutOrigin] at hcj
          | upper r => simp [cutOrigin] at hcj
        have h2 : ∃ r, es[j].2 = .clean r true := by
          generalize es[j].2 = o' at hcut
          cases o' with
          | clean r b => cases b <;> simp_all [cutOrigin]
          | plain r => simp [cutOrigin] at hcut
          | upper r => simp [cutOrigin] at hcut
        obtain ⟨r1, h1⟩ := h1
        obtain ⟨r2, h2⟩ := h2
        have hr1 : es[j + 1].2.src = r1 := by rw [h1]; rfl
        have hr2 : es[j].2.src = r2 := by rw [h2]; rfl
        rw [h1, h2]
        have : r1 = r2 := by rw [← hr1, ← hr2, hνo]
        rw [this]
    obtain ⟨k0, hk0, hk0le, hk0src, hk0nc⟩ := first j hj
    have hc0 : cell? M es[k0].2.src = some cm := by rw [hk0src]; exact hcm
    have hc1 : cell? M es[j + 1].2.src = some cm := by rw [hνo]; exact hcm
    have hA' := CopyShape.NoMA.copyOrderSame s n D M out ρ R t hdat i hipos hS.iLt x es hS.xMem hbl
      k0 hk0 (j + 1) hj1 hk0nc hnc cm cm hc0 hc1
    have := hstrict k0 (j + 1) hk0 hj1 (by omega)
    rw [hA'.2 rfl] at this
    exact lt_irrefl _ this

/-! ## The reduction -/

/-- **`CutTopLookup` from the block profile, `CutBump` and `CutLegLookup`.** -/
theorem cutTopLookup_of_bump_leg (hBump : CutBump) (hLeg : CutLegLookup) : CutTopLookup := by
  intro s n D M out ρ R t X x i es hS hx j hj hcut hnot m' hm'
  have hV := build_valid_of_success hS.splice.build
  have hVR := build_valid_of_success hS.canon
  obtain ⟨col, hSet⟩ := setting_of_site hS
  obtain ⟨hcx, _⟩ := mem_blockColumns_pos hS.xMem hS.iPos
  obtain ⟨c, hc, hcl⟩ := Inner.rawParent_eq_some.mp hm'
  obtain ⟨hj1, hsrc1, hnc1⟩ := topNext' hS hx hj hcut hnot hc
  -- the node above the gap copy is a copy of `m⁺`
  have hupat : Inner.CopyAt M R n ρ.cr ρ.x0 (official t.row) i ⟨X, j + 1 + 1⟩ es[j + 1].2 :=
    ⟨x, es, j + 1, hcx, hx, hS.xMem, hS.Xeq, rfl, hS.emits, hj1, rfl⟩
  obtain ⟨cu', ref', co, l', hcu', href', hco, hl', hrefc'⟩ :=
    Inner.copyAt_left hSet hS.iPos hS.iLt hupat
  rw [hsrc1] at hco
  have hcoc : co = c := Option.some.inj (hco.symm.trans hc)
  subst co
  have hll : l' = m' := Option.some.inj (hl'.symm.trans hcl)
  subst l'
  have hraw : rawParent R ⟨X, j + 1⟩ = some ref' :=
    Inner.rawParent_eq_some.mpr ⟨cu', hcu', href'⟩
  obtain ⟨⟨cv, hcv⟩, ⟨cpe, hcpe⟩, _⟩ := Inner.rawParent_cells hVR hraw
  have hham := Inner.canon_rawParent_hAM hS.canon (by simp) hcv hraw
  rw [hrefc'] at hham
  obtain ⟨pe, hpe, hlow, hroot, hcopy⟩ :=
    hLeg s n D M out ρ R t X x i es hS hx j hj hcut hj1 hsrc1 hnc1 m' hm' cv hcv
  have hpr : pe = ref' := Option.some.inj (hpe.symm.trans hham)
  subst pe
  refine ⟨ref', hraw, ?_, hlow, fun h => ⟨?_, hroot h⟩, hcopy⟩
  · -- the jump, by the row law of both mountains
    intro cu cm cpe' cm' hcu hcm hcpe' hcm'
    have hcuv : cu = cv := Option.some.inj (hcu.symm.trans hcv)
    subst cu
    have hcp : cpe' = cpe := Option.some.inj (hcpe'.symm.trans hcpe)
    subst cpe'
    obtain ⟨_, ho1, _⟩ := emitsT_good hS.emits es[j] (List.getElem_mem hj)
    have hb := hBump s n D M out ρ R t X x i es hS hx j hj hcut hj1 hsrc1 hnc1 cv cu' cm c hcv
      hcu' hcm hc
    have hR := Inner.jump_up_of_rowLaw hS.canon (r := ⟨X, j + 1⟩) (by simp) hcv hcu' href' hcpe
    have hM := Inner.jump_up_of_rowLaw hS.splice.build (by omega) hcm hc hcl hcm'
    omega
  · rw [Inner.highestAtMost_column hham, h, mapColumn_of_ge (le_refl _)]

/-- **`CutTopLookup` from `CutLegLookup`** (`CutBump` is proved). -/
theorem cutTopLookup_of_leg (hLeg : CutLegLookup) : CutTopLookup :=
  cutTopLookup_of_bump_leg CutGap.cutBump hLeg

/-- **The four gap-copy statements** from `StepInner`, `BoundaryChain` and the two open
statements `CutLegLookup`, `CutJumpTop`. -/
theorem cut_statements_noMA (hStep : StepInner) (hBC : BoundaryChain) (hLeg : CutLegLookup)
    (hJT : CutJumpTop) :
    StepCut ∧ CutJump ∧ CutStartCopy ∧ CutStartRoot := by
  have hRoot := cutStartRoot_of_parts hBC SRFixPa.cutOriginReach
  have hJump := cutJump_of_top hJT
  exact ⟨stepCut_of_rest hStep cutStartCopy' hRoot hJump (cutTopLookup_of_leg hLeg),
    hJump, cutStartCopy', hRoot⟩

end OmegaY.Official.Classification.Proofs.ChainCorr.CutParts

#print axioms OmegaY.Official.Classification.Proofs.CutGap.cutRunLow
#print axioms OmegaY.Official.Classification.Proofs.CutGap.cutRunHigh
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.CutParts.cutStartCopy'
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.CutParts.topNext'
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.CutParts.cutTopLookup_of_bump_leg
#print axioms OmegaY.Official.Classification.Proofs.CutGap.cutBump
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.CutParts.cutTopLookup_of_leg
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.SRFixPa.cutOriginReach
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.CutParts.cut_statements_noMA
