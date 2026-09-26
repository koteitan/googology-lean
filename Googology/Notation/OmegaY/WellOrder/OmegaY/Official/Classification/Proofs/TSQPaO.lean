/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/TSQPaO.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TSQCutRight
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TopStartFixPaO
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CutGapFG
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CutGapLeg

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# `PaONoGap` from an ascension statement about `M(s)` (`TSQ`)

`PaONoGap` (`TopStartFixPaO.lean`): the top copy `u` of `o = (x, C)` is not a gap copy, the leg
`l` of `o` is right of `c_r`, `pa = hAM(l, C)` is at the row `C`, and `o` has a node `o⁺` above it
below `row t`. Then no emit of the copied column `l` (block `i`) whose origin is `pa` is a gap
copy. With `topStartPaOUp_of_noGap` this gives `TopStartPaOUp`.

## The reduction

Suppose the column `l` has a gap copy of `pa`. Then

* `C` lies in a first item of level `≥ 2`, and `C` is the row of the top `ρ` of the root column in
  the level-2 region of `C` (`CutGap.emitsT_cleanTop`);
* the column `l` passed the ascension test of `C` (`ChainCorr.emitsT_cleanAsc`);
* so the column `x` passes it too: this is the open statement `AscUp` about `M(s)` alone
  (the converse direction `x ⇒ l` is `CutGap.ascLeg`; `AscUp` needs the node `o⁺`: without it the
  statement fails, the counterexamples `(1,20,15,23,3,10,28,22)`, `(1,22,3,10,10,28,27)`).

Now `u` is a copy of `o`:

* a plain copy: then `C` lies in a first item of level `1`, or `x` does not ascend at `ρ`
  (`CutGap.emitsT_plainAsc`). The first contradicts the first point (the first items are
  disjoint, `JumpLaw.lowerItems_eq_of_common`), the second `AscUp`;
* a clean copy with `b = 0`: then a gap copy of `o` follows it (`CutGap.emitsT_firstGap`, with
  `FactFG` in the diagram, `factFG_diag`), so `u` is not the top copy;
* a gap copy or an upper copy: excluded by the hypotheses.

Results: `paONoGap_of_ascUp : AscUp → PaONoGap`, `topStartPaOUp_of_ascUp : AscUp → TopStartPaOUp`.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.NonTop.SeamD.TSQ

open Canonical Reserve Official Descent Classification Proofs
open Recon Recon.RowLaw
open ChainCorr.Inner ChainCorr.Inner.Clean ChainCorr.Inner.CleanRoot
open Geometry

open CopyShape CopyShape.Found in
/-- **`FactFG` for every context of a block `1 ≤ i ≤ n`** of a run (the diagram form of
`CutGap.fgHolds`). -/
theorem factFG_diag {s : List Nat} {n : Nat} {R : Mountain}
    (hrun : Official.expandDiagram s n = .ok R) {M : Mountain} {t : Cell} {root : Ref}
    (hTop : Recon.Top s M t root) {i : Nat} (hi1 : 1 ≤ i) (hin : i ≤ n) {ctx : Context}
    (hB : LowerPB.BCtx M R root.column (M.size - 1) i ctx) (hcx : root.column < ctx.x) :
    CutGap.FactFG ctx (official t.row) := by
  intro it C hRe hC hcb csRef cs g hnd hgen
  have hblk : 1 ≤ ctx.block := by rw [hB.block]; exact hi1
  have hV : MountainValid ctx.source := by
    rw [hB.source]; exact build_valid_of_success hTop.build
  obtain ⟨_, _, _, _, hBasic⟩ := Recon.run_basic hrun
  have hVR : MountainValid R := hBasic.valid
  have hst := MHProof.reach_clean_eq hV hblk hRe hC hcb
  have hbel := (reach_below hRe).1
  have hbd : ctx.boundary = root.column + (M.size - 1 - root.column) * i := by
    unfold Context.boundary
    rw [hB.root, hB.width, hB.block]
  have hg1 : 1 ≤ g := by
    obtain ⟨hcol, _, _, _⟩ := Classification.nodeAt_spec hnd
    have hlt : ctx.rootColumn < csRef.column := by
      have hcol' : csRef.column = ctx.x := hcol
      rw [hcol', hB.root]; exact hcx
    exact CutGap.generations_pos hlt hgen
  suffices hs : heightOf 2 (topIn ctx.source ctx.rootColumn 2 it.source) ≤
      heightOf 2 (topIn ctx.result ctx.boundary 2 it.target) by omega
  rw [hbd, topIn_congr hB.bnd, hB.source, hB.root]
  cases hρ : topIn M root.column 2 it.source with
  | none => exact Nat.zero_le _
  | some p =>
      obtain ⟨ρr, ρc⟩ := p
      obtain ⟨hρmem, hρreg, _⟩ := Recon.RowLaw.topIn_spec hρ
      have hlt : official ρc.row < official t.row := hbel _ hρreg
      obtain ⟨col, hcol, htc⟩ := top_col hTop
      have hBR := Recon.CutPredMD.boundaryRootRowsHolds s n R hrun M col t root hTop.build hcol
        htc hTop.left hTop.lt i hi1
      obtain ⟨q0, hq0, hq0row⟩ := hBR (boundary_lt hrun hTop hi1 hin) (ρr, ρc) hρmem hlt
      have hq0reg : inRegion 2 it.target (official q0.2.row) = true := by
        rw [← hst, hq0row]; exact hρreg
      cases hq : topIn R (root.column + (M.size - 1 - root.column) * i) 2 it.target with
      | none =>
          have := Recon.RowLaw.topIn_none hq q0 hq0
          rw [hq0reg] at this
          cases this
      | some qq =>
          obtain ⟨hqmem, hqreg, hqmax⟩ := Recon.RowLaw.topIn_spec hq
          have hidx := hqmax q0 hq0 hq0reg
          have hle : q0.2.row ≤ qq.2.row := MHProof.row_le_of_index hVR hq0 hqmem hidx
          obtain ⟨_, hq01, hq0cell⟩ := Classification.mem_realNodes hq0
          have h1 : (1 : Row) ≤ q0.2.row := Classification.one_le_row hVR hq0cell hq01
          have hco := Recon.RowLaw.coeff_le_of_inRegion hq0reg hqreg (Recon.official_mono h1 hle)
          rw [hq0row] at hco
          obtain ⟨qr, qc⟩ := qq
          show (official ρc.row).coeff 0 ≤ (official qc.row).coeff 0
          exact hco

end OmegaY.Official.Classification.Proofs.ChainCorr.NonTop.SeamD.TSQ

namespace OmegaY.Official.Recon.TSQ

open Canonical Expansion Geometry Frame Classification
open CrossUpperSim CrossUpper
open Classification.Proofs.ChainCorr (MStep cutOrigin CopyNode)
open Classification.Proofs.ChainCorr.LowerChain (CopyOf TopNode Stand Rel above IsTopAt)
open Classification.Proofs.ChainCorr.TopStartFix (HasAboveLow)
open TopChain

/-! ## The open statement (about `M(s)` alone) -/

/-- **Open (about `M(s)` alone).** Let `o = (x, k)` (`c_r < x ≤ x₀`, `row o < row t`) have its leg
`l` right of `c_r`, a node of `l` at the row `C` of `o`, a node `o⁺` above it below `row t`, and let
the root column have a node at the row `C`. If the column `l` passes the ascension test of `C`
(the in-row parents from the node of `l` at the reference row of `C` reach the column `c_r`
exactly), so does the column `x`. -/
def AscUp : Prop :=
  ∀ (s : List Nat) (M : Mountain) (t : Cell) (root : Ref), Recon.Top s M t root →
    ∀ (x k : Nat) (co : Cell) (l : Ref), root.column < x → x ≤ M.size - 1 → 1 ≤ k →
      Reserve.cell? M ⟨x, k⟩ = some co → co.row < t.row → co.left = some l →
      root.column < l.column →
      (∃ pa cpa, Reserve.highestAtMost M l.column co.row = some pa ∧
        Reserve.cell? M pa = some cpa ∧ cpa.row = co.row) →
      (∃ c', Reserve.cell? M ⟨x, k + 1⟩ = some c' ∧ c'.row < t.row) →
      (∃ g cg, g.column = root.column ∧ 1 ≤ g.index ∧ Reserve.cell? M g = some cg ∧
        cg.row = co.row) →
      ∀ ref' cl', nodeAt M l.column (referenceRow (official co.row)) = some (ref', cl') →
        reachesRoot M root.column (l.column + 1) ref' = .ok true →
      ∃ ref cl, nodeAt M x (referenceRow (official co.row)) = some (ref, cl) ∧
        reachesRoot M root.column (x + 1) ref = .ok true

/-! ## The reduction -/

/-- **`PaONoGap` from `AscUp`.** -/
theorem paONoGap_of_ascUp (hA : AscUp) : TopStartFixParts.PaONoGap := by
  intro s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv hl hpa hpe
    hlo hlr hnc hpao hab es' hes' j' hj' hsrc'
  cases hcut' : cutOrigin es'[j'].2
  · rfl
  exfalso
  have hi1 : 1 ≤ i := hi0
  have hcr := hTop.lt
  have hb := hTop.build
  have hVM := build_valid_of_success hb
  obtain ⟨hxg, hxl⟩ := mem_blockColumns hcr hx
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  have hXR : x + (M.size - 1 - root.column) * i < R.size := by
    unfold Reserve.cell? at hcu
    cases hc : R[x + (M.size - 1 - root.column) * i]? with
    | none => rw [hc] at hcu; cases hcu
    | some _ => exact (Array.getElem?_eq_some_iff.mp hc).1
  have E := env_of hrun hTop hXR (by omega)
  obtain ⟨lo, us, hD⟩ := colData_block E hi1 hin hx hXR
  have hee : es = lo ++ us := Except.ok.inj (hes.symm.trans hD.emitsT)
  subst hee
  set ctx := ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
    (x + (M.size - 1 - root.column) * i) with hctx
  -- the gap copy of `pa` in the column `l`
  have ho' : es'[j'].2 = .clean pa true := by
    have := origin_of_cut hcut'
    rw [hsrc'] at this
    exact this
  obtain ⟨cp, hcp, hcprow⟩ := hpao
  have hmem' : es'[j'] ∈ es' := List.getElem_mem hj'
  obtain ⟨⟨q2, hq2, hq2lvl, hq2reg⟩, ρr, ρc, hρ, hρrow⟩ :=
    Classification.Proofs.CutGap.emitsT_cleanTop hes' es'[j'] hmem' pa true ho' cp hcp
  simp only [ctxAt] at hρ
  obtain ⟨C, cs, hcs, ref', cl', hn', hr'⟩ :=
    Classification.Proofs.ChainCorr.emitsT_cleanAsc hes' es'[j'] hmem' pa true ho'
  simp only [ctxAt] at hcs hn' hr'
  obtain ⟨_, hpa1, hcscell, hcsrow⟩ := Classification.nodeAt_spec hcs
  simp only at hpa1 hcscell hcsrow
  have hcsp : cs = cp := Option.some.inj (hcscell.symm.trans hcp)
  subst hcsp
  -- the origin `o` of `u`
  have hjlo : j < lo.length := lower_index hD hj hcv hlo
  have hlj : (lo ++ us)[j] = lo[j] := List.getElem_append_left hjlo
  have hmemlo : lo[j] ∈ lo := List.getElem_mem _
  obtain ⟨k, cv', hsk, hk1, hcvk, _⟩ := LowerPB.lowerT_src hD.hlo hmemlo
  have hcv2 : Reserve.cell? M lo[j].2.src = some cv := by rw [← hlj]; exact hcv
  rw [hsk] at hcv2
  have hcvv : cv = cv' := Option.some.inj (hcv2.symm.trans hcvk)
  subst hcvv
  have hup : lo[j].2.isUpper = false := (LowerPB.lowerT_good hD.hlo lo[j] hmemlo).2
  -- `x` passes the ascension test of `C`
  have hcv1 : (1 : Row) ≤ cv.row := LowerPB.cell_row_one_le hVM hcvk hk1
  have hCo : C = official cv.row := by rw [← hcsrow, hcprow]
  have hρrow' : official ρc.row = C := by rw [hρrow, hcprow, hCo]
  obtain ⟨hρmem, _, _⟩ := Recon.RowLaw.topIn_spec hρ
  obtain ⟨hρc, hρ1, hρcell⟩ := Classification.mem_realNodes hρmem
  simp only at hρc hρ1 hρcell
  have hρ1r : (1 : Row) ≤ ρc.row := Classification.one_le_row hVM hρcell hρ1
  have hρcv : ρc.row = cv.row :=
    Classification.Proofs.ChainCorr.CutParts.official_inj' hρ1r hcv1 (by rw [hρrow', hCo])
  have hascX := hA s M t root hTop x k cv l hxg hxl hk1 hcvk hlo hl hlr
    ⟨pa, cs, hpa, hcp, hcprow⟩
    (by obtain ⟨c', hc', hc'r⟩ := hab; rw [hlj, hsk] at hc'; exact ⟨c', hc', hc'r⟩)
    ⟨ρr, ρc, hρc, hρ1, hρcell, hρcv⟩ ref' cl' (by rw [← hCo]; exact hn') hr'
  obtain ⟨ref, cl, hn, hr⟩ := hascX
  have hascends : ascends ctx (some (ρr, ρc)) = .ok true := by
    rw [hctx]
    unfold ascends
    simp only [ctxAt]
    rw [hρrow', hCo, hn]
    exact hr
  have hρ' : topIn ctx.source ctx.rootColumn 2 (official cv.row) = some (ρr, ρc) := by
    rw [hctx]; simp only [ctxAt]; rw [← hcprow]; exact hρ
  have hρrow'' : official ρc.row = official cv.row := by rw [hρrow', hCo]
  -- the kind of `u`
  cases hk : lo[j].2 with
  | upper r => rw [hk] at hup; cases hup
  | clean r bb =>
    cases bb
    · -- a clean copy with `b = 0` is followed by a gap copy of its origin
      have hblk : 1 ≤ ctx.block := hi1
      have hMD := Proofs.CopyShape.Found.factMD_of_bctx hTop hD.bctx
      have hFG := Classification.Proofs.ChainCorr.NonTop.SeamD.TSQ.factFG_diag hrun hTop hi1 hin
        hD.bctx hxg
      have hFirst := Classification.Proofs.CutGap.emitsT_firstGap ctx (official t.row) hVM hblk
        hMD hFG hes
      obtain ⟨q, hq, hqo, hqrow⟩ := hFirst lo[j] (by rw [← hlj]; exact List.getElem_mem hj) r hk
      obtain ⟨jq, hjq, hjqe⟩ := List.getElem_of_mem hq
      have hjj : j < jq := by
        rcases Nat.lt_trichotomy jq j with h | h | h
        · have h1 := List.pairwise_iff_getElem.mp hD.sorted jq j (by simpa using hjq)
            (by simpa using hj) h
          simp only [List.getElem_map] at h1
          rw [hjqe, hqrow, hlj] at h1
          exact absurd (lt_trans h1 (Row.lt_bump _ 0)) (lt_irrefl _)
        · have he : (lo ++ us)[jq] = (lo ++ us)[j] := by simp [h]
          have := Row.lt_bump lo[j].1.row 0
          rw [← hqrow, ← hjqe, he, hlj] at this
          exact (lt_irrefl _ this).elim
        · exact h
      have := htop jq hjq hj hjj
      apply this
      rw [hjqe, hqo, hlj, hk]
      rfl
    · -- a gap copy: excluded
      have : cutOrigin (lo ++ us)[j].2 = true := by rw [hlj, hk]; rfl
      rw [hnc] at this
      cases this
  | plain r =>
    have hsr : r = ⟨ctx.x, k⟩ := by
      have := hsk
      rw [hk] at this
      exact this
    rcases Classification.Proofs.CutGap.emitsT_plainAsc hes lo[j]
        (by rw [← hlj]; exact List.getElem_mem hj) r hk cv (by rw [hsr]; exact hcvk) with
      ⟨q1, hq1, hq1lvl, hq1reg⟩ | hpl
    · -- `C` in a first item of level `1` and in one of level `≥ 2`
      have hreg2 : inRegion q2.1 q2.2.source (official cv.row) = true := by
        rw [← hcprow]; exact hq2reg
      have heq := Recon.JumpLaw.lowerItems_eq_of_common hq1 hq2 hq1reg hreg2
      rw [heq] at hq1lvl
      omega
    · have hf := hpl r hk cv (by rw [hsr]; exact hcvk) ρr ρc hρ' hρrow''
      rw [hascends] at hf
      cases hf

/-- **`TopStartPaOUp` from `AscUp`.** -/
theorem topStartPaOUp_of_ascUp (hA : AscUp) : TopStartFixParts.TopStartPaOUp :=
  TopStartFixParts.topStartPaOUp_of_noGap (paONoGap_of_ascUp hA)

end OmegaY.Official.Recon.TSQ

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.NonTop.SeamD.TSQ.factFG_diag
#print axioms OmegaY.Official.Recon.TSQ.paONoGap_of_ascUp
#print axioms OmegaY.Official.Recon.TSQ.topStartPaOUp_of_ascUp
