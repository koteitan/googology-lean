/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CPNBase.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.SeamCut
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.P3TRunTop
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CutGapFG
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.Pkg3Run

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# Tools for `CutParentNT` in the diagram (`CPN`)

Diagram forms (no canonicity of the output) of three facts used for the stored parent of a gap
copy:

* `gapBetween`: in a traced column whose emits satisfy `NNC` (a non-gap emit does not repeat an
  earlier origin), every emit strictly after a clean copy of `pa` (gap or not) and at or before a
  gap copy of `pa` is a gap copy of `pa` (the argument of `Pkg3.gap_between`).
* `factFG_of_bctx`: `FactFG` for every context of a block `1 ≤ i ≤ n` (the argument of
  `CopyShape.Found.factMH_of_bctx` in the strong form `h_ρ ≤ h_q`, and `g ≥ 1`).
* `genStep_of_clean`: the origin `m` of a clean copy (any flag `b`) has a generation step
  `m → b` with `c_r ≤ col b` (the argument of `SeamD.chainX_first_stepD`, which states it for
  `b = 0` only).
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.NonTop.SeamD.CPN

open Canonical Reserve Official Descent Classification Proofs
open Recon Recon.RowLaw
open ChainCorr.Inner ChainCorr.Inner.Clean ChainCorr.Inner.CleanRoot
open Geometry

/-! ## Contiguity -/

/-- **Contiguity** (diagram form of `Pkg3.gap_between`, with any clean copy of `pa` as the lower
end). -/
theorem gapBetween {ctx : Context} {τ : Row} (hV : MountainValid ctx.source)
    {es : List (Emit × Origin)} (hes : emitsT ctx τ = .ok es)
    (hnnc : es.Pairwise CopyShape.NoMA.NNC) {pa : Ref} {ba : Bool}
    {a b c : Nat} (ha : a < es.length) (hc : c < es.length) (hab : a < b) (hbc : b ≤ c)
    (hea : es[a].2 = .clean pa ba) (hec : es[c].2 = .clean pa true) :
    ∃ hb : b < es.length, es[b].2 = .clean pa true := by
  have hb : b < es.length := by omega
  refine ⟨hb, ?_⟩
  have hpw := ChainCorr.CopyMonoProof.emitsT_mono hV hes
  obtain ⟨hsa, hia, cpa, hcpa, _⟩ := emitsT_good hes es[a] (List.getElem_mem ha)
  obtain ⟨hsb, hib, cb, hcb, _⟩ := emitsT_good hes es[b] (List.getElem_mem hb)
  have hsrca : es[a].2.src = pa := by rw [hea]; rfl
  have hsrcc : es[c].2.src = pa := by rw [hec]; rfl
  have hua : es[a].2.isUpper = false := by rw [hea]; rfl
  rw [hua] at hsa
  simp only [Bool.false_eq_true, if_false] at hsa
  rw [hsrca] at hcpa hia hsa
  have h1 : official cpa.row ≤ official cb.row :=
    List.pairwise_iff_getElem.mp hpw a b ha hb hab cpa cb (by rw [hsrca]; exact hcpa) hcb
  have h2 : official cb.row ≤ official cpa.row := by
    rcases Nat.lt_or_eq_of_le hbc with hlt | heq
    · exact List.pairwise_iff_getElem.mp hpw b c hb hc hlt cb cpa hcb (by rw [hsrcc]; exact hcpa)
    · subst heq
      rw [hsrcc] at hcb
      rw [Option.some.inj (hcb.symm.trans hcpa)]
  have hoff : official cb.row = official cpa.row := le_antisymm h2 h1
  have hlow : es[b].2.isUpper = false := by
    cases hu : es[b].2.isUpper
    · rfl
    · exfalso
      obtain ⟨c0, hc0, hlt0⟩ := emitsT_lower_below hes es[a] (List.getElem_mem ha)
        (by rw [hea]; rfl)
      rw [hsrca, hcpa] at hc0
      cases hc0
      have hup : ∃ r, es[b].2 = .upper r := by
        revert hu
        cases es[b].2 with
        | upper r => intro _; exact ⟨r, rfl⟩
        | plain r => simp [Origin.isUpper]
        | clean r b' => simp [Origin.isUpper]
      obtain ⟨r, hr⟩ := hup
      have hsr : es[b].2.src = r := by rw [hr]; rfl
      have hge := CutGap.emitsT_upperRow hes es[b] (List.getElem_mem hb) r hr cb
        (by rw [← hsr]; exact hcb)
      rw [hoff] at hge
      exact absurd hge (not_le.mpr hlt0)
  rw [hlow] at hsb
  simp only [Bool.false_eq_true, if_false] at hsb
  have hrow : cb.row = cpa.row := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact absurd hoff (ne_of_lt (Recon.official_strictMono (one_le_row hV hcb hib) hlt))
    · exact absurd hoff (ne_of_gt (Recon.official_strictMono (one_le_row hV hcpa hia) hgt))
  have hsrcb : es[b].2.src = pa :=
    Inner.cell?_eq_of_index hV (by rw [hsb, ← hsa]) hcb hcpa hrow
  have hn := List.pairwise_iff_getElem.mp hnnc a b ha hb hab
  have hcutb : ChainCorr.cutOrigin es[b].2 = true := by
    cases hcb' : ChainCorr.cutOrigin es[b].2
    · exact absurd (by rw [hsrca, hsrcb]) (hn hcb')
    · rfl
  exact Pkg3.origin_clean_of_cut hsrcb hcutb

/-! ## `FactFG` in the diagram -/

open CopyShape CopyShape.Found in
/-- **`FactFG` for every context of a block `1 ≤ i ≤ n`** of a run. -/
theorem factFG_of_bctx {s : List Nat} {n : Nat} {R : Mountain}
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
  -- `g ≥ 1`
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

/-! ## The generation step of a clean copy -/

open Geometry.Frame in
/-- **The first step of the generation chain of a clean copy, any flag** (the argument of
`chainX_first_stepD`). -/
theorem genStep_of_clean {s : List Nat} {M : Mountain} {t : Cell} {root : Ref}
    (hTop : Recon.Top s M t root) {n : Nat} {R : Mountain} {i : Nat}
    {v a : Ref} {bb : Bool}
    (hva : CopyAtX M R n root.column (M.size - 1) (official t.row) i v (.clean a bb)) :
    ∃ b, GenStep M root.column a b ∧ root.column ≤ b.column := by
  obtain ⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, ho⟩ := hva
  have hes' : emitsT (ctxAt M R y i root.column ((M.size - 1) - root.column) (M.size - 1) (y + ((M.size - 1) - root.column) * i))
      (official t.row) = .ok es := by rw [← hvc]; exact hes
  obtain ⟨C, cs, hcs, ⟨ref, cl, hn, hr⟩, hroot⟩ :=
    emitsT_cleanRoot hes' es[j] (List.getElem_mem hj) a bb ho
  simp only [ctxAt] at hcs hn hr hroot
  have hb := hTop.build
  have hN := build_normal_of_success hb
  have hO := hN.toOrdered
  obtain ⟨hac, ha1, hacell, harow⟩ := Classification.nodeAt_spec hcs
  simp only at hac ha1 hacell harow
  by_cases h0 : 0 < C.coeff 0
  · have hZC := Recon.RowLaw.referenceRow_bump h0
    obtain ⟨hrc, hr1, hrcell, hrrow⟩ := Classification.nodeAt_spec hn
    simp only at hrc hr1 hrcell hrrow
    obtain ⟨cu, hcu, hofu, g, hg, hgc⟩ :=
      chain_to_root hb hZC hroot (y + 1) ref cl hrcell hr1 hrrow (by rw [hrc]; exact hcy) hr
    have hupa : up ref = a := by
      obtain ⟨hmem, _⟩ := Recon.RowLaw.nodeAt_spec hcs
      have hupmem : (up ref, cu) ∈ realNodes M y := by
        rw [mem_realNodes_iff]
        unfold cell? at hcu
        cases hcolr : M[ref.column]? with
        | none => simp [up, hcolr] at hcu
        | some colr =>
            simp only [up, hcolr, Option.bind_eq_bind, Option.bind_some] at hcu
            refine ⟨colr, ref.index, by rw [← hrc]; exact hcolr, hcu, ?_⟩
            simp [up, hrc]
      have := ChainCorr.realNodes_eq_of_official (build_valid_of_success hb) hupmem hmem
        (by simp only; rw [hofu, harow])
      exact congrArg Prod.fst this
    rw [hupa] at hg
    exact first_step_of_chain hg (le_of_eq hgc.symm)
  · have hZ : referenceRow C = C := by
      unfold referenceRow
      rw [if_neg h0]
    rw [hZ, hcs] at hn
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
    obtain ⟨q, hw, hqcr⟩ := ChainCorr.weakParent_of_reachesRoot (by rw [hac]; exact hcy) hr
    obtain ⟨col', cell, upper, parentCell, hcol, hcell, hup, hleft, hpc, hprow⟩ :=
      Recon.RowLaw.weakParent_some hw
    have hraw : Reserve.rawParent M a = some q := by
      simp only [Reserve.rawParent, hcol, Option.bind_eq_bind, Option.bind_some, hup, hleft]
    have hcellr : cell? M a = some cell := by simp [cell?, hcol, hcell]
    have hcc : cell = cs := Option.some.inj (hcellr.symm.trans hacell)
    subst hcc
    have hqc : cell? M q = some parentCell := by
      obtain ⟨column, h1, h2⟩ := cellAt_ok_iff.mp hpc
      simp [cell?, h1, h2]
    obtain ⟨na, hna, hnacell⟩ := ControlProof.node_of_cell? hacell
    have hareal : Frame.Real na := by
      show 0 < na.2.val
      have : na.2.val = a.index := by rw [← hna]; rfl
      omega
    obtain ⟨nq, hPa, hnq⟩ := P_of_rawParent hN hareal (hna ▸ hraw)
    obtain ⟨q0, hQ0, hit0⟩ := (P_iff hO).mp hPa
    have hnqcell : (Frame.ofMountain M).cell nq = parentCell := by
      have := ControlProof.cell?_ref nq
      rw [hnq, hqc] at this
      exact (Option.some.inj this).symm
    have hh : (Frame.ofMountain M).height nq = (Frame.ofMountain M).height na := by
      show ((Frame.ofMountain M).cell nq).row = ((Frame.ofMountain M).cell na).row
      rw [hnqcell, hnacell, hprow]
    have hc : root.column ≤ nq.1.val := by
      have : nq.1.val = q.column := by rw [← hnq]; rfl
      omega
    have hch := inrow_hit (cr := root.column) hO hit0 na hareal hQ0 hh hc
    rw [hna] at hch
    exact first_step_of_chain hch hc

/-! ## The non-gap copy of the next generation (diagram) -/

open CutGap in
/-- **The non-gap copy of `b` in the column `φ(l)`** (the part of `lookupInnerXD` that finds it),
for a clean copy of `a` with any flag. -/
theorem nonGapCopy {s : List Nat} {n : Nat} {M : Mountain} {R : Mountain} {t : Cell}
    {root : Ref} (E : CrossUpperSim.Env s n R M t root) {i : Nat} (hi0 : 0 < i) (hi : i < n + 1)
    {v a : Ref} {bb : Bool}
    (hva : CopyAtX M R n root.column (M.size - 1) (official t.row) i v (.clean a bb))
    {b : Ref} (hab : GenStep M root.column a b) (hlb : root.column < b.column) :
    ∃ lol usl, LowerPB.ColData s n R M t root (b.column + (M.size - 1 - root.column) * i) i
        b.column lol usl ∧
      ∃ k0, ∃ hk0 : k0 < (lol ++ usl).length, (lol ++ usl)[k0].2 = .clean b false ∧
        ∃ ca, cell? M a = some ca ∧ ChainCorr.SRCmp.RootRow M root.column (official ca.row) ∧
          (lol ++ usl)[k0].1.row = official ca.row := by
  have hb := E.top.build
  have hV := build_valid_of_success hb
  have hVR := validR E.run
  have hva' := hva
  obtain ⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, ho⟩ := hva'
  have hes' : emitsT (ctxAt M R y i root.column ((M.size - 1) - root.column) (M.size - 1) (y + ((M.size - 1) - root.column) * i))
      (official t.row) = .ok es := by rw [← hvc]; exact hes
  -- the step `a → b`
  obtain ⟨_, hb1, ca, cb, l, hca, hl, hbl, hcb, hbrow⟩ := hab
  have hlcr : root.column < l.column := by rw [← hbl]; exact hlb
  -- the copied row `C` of `v`: the row of `a`, ascension test of `y`
  obtain ⟨C, cs, hcs, ⟨refx, clx, hnx, hrx⟩, hroot⟩ :=
    emitsT_cleanRoot hes' es[j] (List.getElem_mem hj) a bb ho
  simp only [ctxAt] at hcs hnx hrx hroot
  obtain ⟨hac, ha1, hacell, harow⟩ := Classification.nodeAt_spec hcs
  simp only at hac ha1 hacell harow
  have hcsa : cs = ca := Option.some.inj (hacell.symm.trans hca)
  subst hcsa
  -- `C` is the row of the root top of its level-2 region, in a first item of level `≥ 2`
  obtain ⟨⟨qx, hqx, hqx2, hqxin⟩, ρr, ρc, hρ, hρrow⟩ :=
    emitsT_cleanTop hes' es[j] (List.getElem_mem hj) a bb ho cs hacell
  simp only [ctxAt] at hρ
  -- the leg column ascends at `ρ`
  have hyl : l.column < y := by
    have := left_lt_of_valid hV hacell hl
    rw [hac] at this
    exact this
  obtain ⟨refl, cll, hnl, hrl⟩ := ascLeg hb hcy (by rw [← harow] at hnx; exact hnx) hrx
    (by rw [← harow] at hcs; exact hcs) hl hlcr
  have hascl : ascends (ctxAt M R l.column i root.column ((M.size - 1) - root.column) (M.size - 1)
      (l.column + ((M.size - 1) - root.column) * i)) (some (ρr, ρc)) = .ok true := by
    apply ascends_of_reach (ref := refl) (cl := cll)
    · simp only [ctxAt]
      rw [hρrow]
      exact hnl
    · simpa [ctxAt] using hrl
  -- the emits of the column `l`
  have hlx : l.column < M.size - 1 := by omega
  have hlmem : l.column ∈ blockColumns root.column (M.size - 1) n i :=
    CrossUpperSim.mem_blockColumns_of_inner hi0 hi hlcr hlx
  obtain ⟨_, _, _, _, hq0, ⟨hvc0, _, _, hXRv⟩, _, _, _, _⟩ := copyAtX_cellD E hi0 hi hva
  have hXRl : l.column + (M.size - 1 - root.column) * i < R.size := by omega
  obtain ⟨lol, usl, hDl⟩ := Recon.TopChain.colData_block E hi0 (by omega) hlmem hXRl
  have hXRy : y + (M.size - 1 - root.column) * i < R.size := by omega
  obtain ⟨loy, usy, hDy⟩ := Recon.TopChain.colData_block E hi0 (by omega) hyb hXRy
  have hesl := hDl.emitsT
  -- the non-cut emit of `b` in the column `l`
  obtain ⟨k0, hk0, hk0src, hk0nc⟩ : ∃ k0, ∃ hk0 : k0 < (lol ++ usl).length, (lol ++ usl)[k0].2.src = b ∧
      cutOrigin (lol ++ usl)[k0].2 = false := by
    have hCτ0 : official cs.row < official t.row :=
      (lowerItems_below (official t.row) _ hqx).1 _ hqxin
    have hbcell : cell? M ⟨(ctxAt M R l.column i root.column (M.size - 1 - root.column)
        (M.size - 1) (l.column + (M.size - 1 - root.column) * i)).x, b.index⟩ = some cb := by
      simp only [ctxAt]; rw [← hbl]; exact hcb
    obtain ⟨e, he, hecut, hesrc⟩ := CopyShape.Final.emitted s n R E.run M t root E.top i hi0
      (by omega) _ hDl.bctx hDl.xgt lol hDl.hlo b.index cb hb1 hbcell
      (by rw [hbrow]; exact hCτ0)
    obtain ⟨m, hm, hme⟩ := List.getElem_of_mem he
    refine ⟨m, by rw [List.length_append]; omega, ?_, ?_⟩
    · rw [List.getElem_append_left hm, hme, hesrc]
      simp only [ctxAt]; rw [← hbl]
    · rw [List.getElem_append_left hm, hme, ← CopyShape.Found.cutO_eq]; exact hecut
  have hCτ : official cs.row < official t.row :=
    (lowerItems_below (official t.row) _ hqx).1 _ hqxin
  have hbC : official cb.row = official cs.row := by rw [hbrow]
  have hclean : (lol ++ usl)[k0].2 = .clean b false := by
    have hlowl := emitsT_plainAsc (ctx := ctxAt M R l.column i root.column ((M.size - 1) - root.column) (M.size - 1)
      (l.column + ((M.size - 1) - root.column) * i)) (τ := official t.row) hesl
    have hupl := emitsT_upperRow (ctx := ctxAt M R l.column i root.column ((M.size - 1) - root.column) (M.size - 1)
      (l.column + ((M.size - 1) - root.column) * i)) (τ := official t.row) hesl
    generalize hE : (lol ++ usl)[k0].2 = o at hk0src hk0nc
    cases o with
    | clean r' bb =>
        cases bb
        · have : r' = b := hk0src
          rw [this]
        · simp [cutOrigin] at hk0nc
    | upper r' =>
        exfalso
        have hr' : r' = b := hk0src
        rw [hr'] at hE
        have := hupl (lol ++ usl)[k0] (List.getElem_mem hk0) b hE cb hcb
        rw [hbC] at this
        exact absurd hCτ (not_lt.mpr this)
    | plain r' =>
        exfalso
        have hr' : r' = b := hk0src
        rw [hr'] at hE
        rcases hlowl (lol ++ usl)[k0] (List.getElem_mem hk0) b hE cb hcb with
          ⟨q1, hq1, hq11, hq1in⟩ | hP
        · have hq1in' : inRegion q1.1 q1.2.source (official cs.row) = true := by
            rw [← hbC]; exact hq1in
          have := Recon.JumpLaw.lowerItems_eq_of_common hqx hq1 hqxin hq1in'
          rw [this] at hqx2
          omega
        · have hρ' : topIn M root.column 2 (official cb.row) = some (ρr, ρc) := by
            rw [hbC]; exact hρ
          have hρrow' : official ρc.row = official cb.row := by rw [hbC]; exact hρrow
          have hf : ascends (ctxAt M R l.column i root.column ((M.size - 1) - root.column) (M.size - 1)
              (l.column + ((M.size - 1) - root.column) * i)) (some (ρr, ρc)) = .ok false :=
            hP b hE cb hcb ρr ρc hρ' hρrow'
          rw [hascl] at hf
          cases hf
  -- the copy node of `b`
  let v2 : Ref := ⟨l.column + ((M.size - 1) - root.column) * i, k0 + 1⟩
  have hv2 : CopyAt M R n root.column (M.size - 1) (official t.row) i v2 (.clean b false) :=
    ⟨l.column, (lol ++ usl), k0, hlcr, by omega, hlmem, rfl, rfl, hesl, hk0, hclean⟩
  -- both copies keep the row `C`
  have hRR : ChainCorr.SRCmp.RootRow M root.column (official cs.row) :=
    ⟨(ρr, ρc), (topIn_spec hρ).1, hρrow⟩
  have hrowv2 : (lol ++ usl)[k0].1.row = official cs.row := by
    have hcmp := Recon.TopChain.Seam.ecmp_of_colData hDl (lol ++ usl)[k0] (List.getElem_mem hk0) cb
      (by rw [hclean]; exact hcb) (official cs.row) hRR
    rw [hclean] at hcmp
    exact ((hcmp.1 rfl).2.1 hbC.symm)
  have hbl' : b.column = l.column := hbl
  rw [hbl']
  exact ⟨lol, usl, hDl, k0, hk0, hclean, cs, hacell, hRR, hrowv2⟩

end OmegaY.Official.Classification.Proofs.ChainCorr.NonTop.SeamD.CPN

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.NonTop.SeamD.CPN.gapBetween
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.NonTop.SeamD.CPN.factFG_of_bctx
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.NonTop.SeamD.CPN.genStep_of_clean
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.NonTop.SeamD.CPN.nonGapCopy
