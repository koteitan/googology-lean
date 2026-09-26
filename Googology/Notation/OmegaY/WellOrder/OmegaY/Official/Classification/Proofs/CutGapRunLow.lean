/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CutGapRunLow.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CutGapLegOrder

set_option backward.do.legacy false

/-!
# `CutRunLow` (`CutGap`)

`CutRunLow` (`CutPartsStart.lean`): for a gap copy `u` of the origin `o = (x, C)` in block
`i ≥ 1` whose leg `l` is right of `cr`, the copy of the column `l` in block `i` has a gap copy of
`pa = (l, C)` at or below the row of `u`.

## The argument (`cutRunLow_of_facts`)

* `C` is the row of the root top `ρ` of its level-2 region, `C` lies in a first item of level
  at least 2, and `x` passes the ascension test of `C` (`emitsT_cleanTop`, `emitsT_cleanAsc`).
  By `ascLeg` the leg column `l` passes the same test: `l` ascends at `ρ`.
* The column `l` has a non-cut copy `v` of `pa` (`CopyEmitted`). It is not an upper copy
  (`C < τ`), and not a plain copy: a plain copy of `C` comes from a first item of level 1 (but
  `C` lies in one of level at least 2) or from a column that does not ascend at `ρ`
  (`emitsT_plainAsc`). So `v` is a clean copy.
* After a clean copy comes a gap copy of the same origin one row up (`emitsT_firstGap`, given
  `FactFG`).
* `v` lies below `u` (`legOrder`, `CutGapLegOrder.lean`, the case `σ = C`), so the row after `v`
  is at most the row of `u`.

`cutRunLow_of_facts`: `CutRunLow` from `CopyEmitted` and `FactFG`. Both are proved
(`CopyShape.NoMA.copyEmitted` in `CopyShapeNoMA.lean`, `fgHolds` in `CutGapFG.lean`); the
unconditional `cutRunLow` is in `CutGapFinal.lean`. (MA), which is false, is not used.
-/

set_option linter.unusedSimpArgs false

namespace OmegaY.Official.Classification.Proofs.CutGap

open Canonical Reserve Official Descent Classification Proofs CopyShape
open ChainCorr ChainCorr.CutParts

/-- The origin row of an upper emit is at least `τ`. -/
theorem emitsT_upperRow {ctx : Context} {τ : Row} {es : List (Emit × Origin)}
    (h : emitsT ctx τ = .ok es) :
    ∀ p ∈ es, ∀ r, p.2 = .upper r → ∀ c0 : Cell, cell? ctx.source r = some c0 →
      τ ≤ official c0.row := by
  unfold emitsT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i lower hlower
    split at h
    · cases h
    · rename_i us hus
      cases h
      intro p hp r hpr c0 hc0
      rcases List.mem_append.mp hp with hp | hp
      · exfalso
        unfold lowerT at hlower
        simp only [bind, Except.bind, pure, Except.pure] at hlower
        split at hlower
        · cases hlower
        · rename_i outs houts
          cases hlower
          obtain ⟨l, hl, hpl⟩ := List.mem_flatten.mp hp
          obtain ⟨q, hq, hqo⟩ := mem_of_mapM houts hl
          have hO := (ChainCorr.Inner.runItemT_order ctx q.1 q.2 l hqo
            (fun C hC => by
              obtain ⟨k, j, _, _, hk⟩ := Recon.RowLaw.mem_lowerItems hq
              rw [hk] at hC
              cases hC)).2 p hpl
          rcases hO.1 with h1 | h1 <;> rw [hpr] at h1 <;> cases h1
      · unfold upperT at hus
        obtain ⟨q, hq, hqp⟩ := mem_of_mapM hus hp
        obtain ⟨h1, _⟩ := upper_emit hqp
        rw [h1] at hpr
        cases hpr
        rw [List.mem_filter] at hq
        obtain ⟨_, _, hqc⟩ := mem_realNodes hq.1
        rw [hqc] at hc0
        cases hc0
        simpa using hq.2

theorem ascends_of_reach {ctx : Context} {ρr : Ref} {ρc : Cell} {ref : Ref} {cl : Cell}
    (hn : nodeAt ctx.source ctx.x (referenceRow (official ρc.row)) = some (ref, cl))
    (hr : reachesRoot ctx.source ctx.rootColumn (ctx.x + 1) ref = .ok true) :
    ascends ctx (some (ρr, ρc)) = .ok true := by
  unfold ascends
  simp only [hn]
  exact hr

theorem bump_zero_le {a b : Row} (h : a < b) : Row.bump a 0 ≤ b :=
  (Row.bump_mono_exponent a (Nat.zero_le _)).trans (Row.bump_last_le h)

/-- **`CutRunLow` from MA, MH and `FactFG`.** -/
theorem cutRunLow_of_facts (hCE : ChainCorr.CopyEmitted) (hFG : FGHolds) : CutRunLow := by
  intro s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe cpa hL hlt esl hbl
  have hb := hS.splice.build
  have hV := build_valid_of_success hb
  have hdat := hS.data
  have hipos := hS.iPos
  obtain ⟨hcx, hxx⟩ := mem_blockColumns_pos hS.xMem hS.iPos
  obtain ⟨col', t', hcol', ht', _, hcrx, _⟩ := spliceCase_data hS.splice hS.run
  -- the gap copy and its origin
  have ho : ∃ r, es[j].2 = .clean r true := by
    generalize es[j].2 = o at hcut
    cases o with
    | clean r b => cases b <;> simp_all [cutOrigin]
    | plain r => simp [cutOrigin] at hcut
    | upper r => simp [cutOrigin] at hcut
  obtain ⟨r, ho⟩ := ho
  have hsrc : es[j].2.src = r := by rw [ho]; rfl
  have hcv : cell? M r = some cv := by rw [← hsrc]; exact hL.hcv
  -- the leg column is a copied column of the block
  obtain ⟨hsrcc, hidx, _, _, _⟩ := emitsT_good hS.emits es[j] (List.getElem_mem hj)
  have hly : l.column < es[j].2.src.column := left_lt_of_valid hV hL.hcv hL.hl
  have hsrcle : es[j].2.src.column ≤ ρ.x0 := by
    rw [hsrcc]
    split
    · exact upperColumn_le hcrx.le hxx
    · exact hxx
  have hyx : l.column < ρ.x0 := by omega
  have hymem : l.column ∈ blockColumns ρ.cr ρ.x0 n i := by
    unfold blockColumns
    rw [if_neg (by omega)]
    simp only [List.mem_range'_1]
    split <;> omega
  have hesx : blockEmits M R ρ.cr ρ.x0 (official t.row) i x = .ok es := by
    simp only [blockEmits, ← hS.Xeq]
    exact hS.emits
  -- `C` is the row of the root top of its level-2 region; `x` passes its ascension test
  obtain ⟨⟨qx, hqx, hqx2, hqxin⟩, ρr, ρc, hρ, hρrow⟩ :=
    emitsT_cleanTop hS.emits es[j] (List.getElem_mem hj) r true ho cv hcv
  obtain ⟨C', cs', hcs', refx, clx, hnx, hrx⟩ :=
    emitsT_cleanAsc hS.emits es[j] (List.getElem_mem hj) r true ho
  simp only [ctxAt] at hρ hcs' hnx hrx hqx
  obtain ⟨hrcol, _, hcscell, hcsrow⟩ := Classification.nodeAt_spec hcs'
  have hcsv : cs' = cv := Option.some.inj (hcscell.symm.trans hcv)
  rw [hcsv] at hcs' hcsrow
  have hrcolx : r.column = x := hrcol
  -- the leg column passes the same test: it ascends at `ρ`
  obtain ⟨refl, cll, hnl, hrl⟩ := ascLeg hb hcx hnx hrx hcs' hL.hl hlt
  have hascl : ascends (ctxAt M R l.column i ρ.cr (ρ.x0 - ρ.cr) ρ.x0
      (l.column + (ρ.x0 - ρ.cr) * i)) (some (ρr, ρc)) = .ok true := by
    apply ascends_of_reach (ref := refl) (cl := cll)
    · simp only [ctxAt]
      rw [hρrow, hcsrow]
      exact hnl
    · simpa [ctxAt] using hrl
  -- the node `pa` of the leg column at the row `C`
  have hparow := cutPaRow s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe cpa hL
  obtain ⟨hpacol, hpa0, _⟩ := highestAtMost_spec hL.hpa
  -- its non-cut copy in the leg column
  obtain ⟨k0, hk0, hk0src, hk0nc⟩ := hCE s n D M out ρ R t hdat i hipos
    hS.iLt l.column esl hlt hyx hbl pa cpa hpacol (by omega) hL.hcpa
  have hcpa' : cell? M esl[k0].2.src = some cpa := by rw [hk0src]; exact hL.hcpa
  have hCτ : official cv.row < official t.row := by
    have := (lowerItems_below (official t.row) _ hqx).1 _ hqxin
    exact this
  -- it is a clean copy
  have hclean : esl[k0].2 = .clean pa false := by
    have hlowl := emitsT_plainAsc (ctx := ctxAt M R l.column i ρ.cr (ρ.x0 - ρ.cr) ρ.x0
      (l.column + (ρ.x0 - ρ.cr) * i)) (τ := official t.row) hbl
    have hupl := emitsT_upperRow (ctx := ctxAt M R l.column i ρ.cr (ρ.x0 - ρ.cr) ρ.x0
      (l.column + (ρ.x0 - ρ.cr) * i)) (τ := official t.row) hbl
    generalize hE : esl[k0].2 = o at hk0src hk0nc
    cases o with
    | clean r' b =>
        cases b
        · have : r' = pa := hk0src
          rw [this]
        · simp [cutOrigin] at hk0nc
    | upper r' =>
        exfalso
        have hr' : r' = pa := hk0src
        rw [hr'] at hE
        have := hupl esl[k0] (List.getElem_mem hk0) pa hE cpa hL.hcpa
        rw [hparow] at this
        exact absurd hCτ (not_lt.mpr this)
    | plain r' =>
        exfalso
        have hr' : r' = pa := hk0src
        rw [hr'] at hE
        rcases hlowl esl[k0] (List.getElem_mem hk0) pa hE cpa hL.hcpa with
          ⟨q1, hq1, hq11, hq1in⟩ | hP
        · have hq1in' : inRegion q1.1 q1.2.source (official cv.row) = true := by
            rw [← hparow]; exact hq1in
          have := Recon.JumpLaw.lowerItems_eq_of_common hqx hq1 hqxin hq1in'
          rw [this] at hqx2
          omega
        · have hρ' : topIn M ρ.cr 2 (official cpa.row) = some (ρr, ρc) := by
            rw [hparow]; exact hρ
          have hρrow' : official ρc.row = official cpa.row := by rw [hparow]; exact hρrow
          have hf : ascends (ctxAt M R l.column i ρ.cr (ρ.x0 - ρ.cr) ρ.x0
              (l.column + (ρ.x0 - ρ.cr) * i)) (some (ρr, ρc)) = .ok false :=
            hP pa hE cpa hL.hcpa ρr ρc hρ' hρrow'
          rw [hascl] at hf
          cases hf
  -- the gap copy after it
  have hFGl := hFG s n D M out ρ R t hdat i hipos hS.iLt l.column hymem
  have hMDl := mdHolds s n D M out ρ R t hdat i hipos hS.iLt l.column hymem
  obtain ⟨q, hq, hqo, hqrow⟩ := emitsT_firstGap _ _ hV (show 1 ≤ i from hipos) hMDl hFGl hbl
    esl[k0] (List.getElem_mem hk0) pa hclean
  -- the clean copy lies below `u`
  have hord := (legOrder hS hj hcut hL.hcv hL.hl hlt hbl esl[k0] (List.getElem_mem hk0) hk0nc cv
    cpa hL.hcv hcpa').1 (by rw [hparow])
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hq
  exact ⟨k, hk, hqo, by rw [hqrow]; exact bump_zero_le hord⟩

end OmegaY.Official.Classification.Proofs.CutGap

#print axioms OmegaY.Official.Classification.Proofs.CutGap.ascLeg
#print axioms OmegaY.Official.Classification.Proofs.CutGap.emitsT_firstGap
#print axioms OmegaY.Official.Classification.Proofs.CutGap.cutRunLow_of_facts
