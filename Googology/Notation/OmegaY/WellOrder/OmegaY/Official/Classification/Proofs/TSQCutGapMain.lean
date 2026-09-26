/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/TSQCutGapMain.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TSQCutGapStep
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.Pk4Legs

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# `CutTopGap` holds (`TSQ`)

`CutTopGap` (`TSQCutRight.lean`): the top copy `u` (block `i ≥ 1`) of `o = (x, C)` is a gap copy,
the leg `l` of `o` is right of `c_r`, and `pa = (l, C)`. Every gap copy of `pa` in the copied
column `l` (block `i`) is at or below `u`.

## The proof

Let `q` be a gap copy of `pa` in the tree of `l`, emitted by a level-1 item `A₁` (a copy of the
root row `C` with a cut bottom, target `row q`). Follow the path of `A₁` from its first item in
the tree of `l`, and simulate it in the tree of `x` (`simR_chain`, then `stepR` for the last
step): the two columns agree on the ascension at root tops below `C` (`ascLeg`), `x` ascends at
`C` (it has the gap copy `u`), and `x` has one more generation of `C` than `l` (`gen_step`), so
the tree of `x` has every child that the tree of `l` has (`AnchR`). At level `1` the similar
item is `A₁` itself (an item with a cut bottom is not similar to another one), and in the tree
of `x` it emits a copy of `o` at `row q`. So `row q ≤ row u` (`u` is the top copy of `o`).

`cutTopGap : CutTopGap`; with `TSQ.topStartCutRight_of_gap`, `topStartCutRight`.
-/

namespace OmegaY.Official.Recon.TSQ.CTG

open Canonical Expansion Dimension Recon.RowLaw Recon.JumpLaw Recon.JumpLawLower Recon.LRC
open Classification Classification.Proofs.ChainCorr Reserve
open Recon.TopChain

/-- A traced emit of an item lies in the output of a level-1 descendant. -/
theorem emit_path {ctx : Context} : ∀ d K TK, runItemT ctx (d + 1) K = .ok TK →
    ∀ q ∈ TK, ∃ A1 T1, Desc ctx (d + 1) K 1 A1 ∧ runItemT ctx 1 A1 = .ok T1 ∧ q ∈ T1
  | 0, K, TK, h, q, hq => ⟨K, TK, .refl _ _, h, hq⟩
  | d + 1, K, TK, h, q, hq => by
    obtain ⟨cs, outs, hcs, hF, rfl⟩ := runItemT_children h
    obtain ⟨L', hL', hqL'⟩ := List.mem_flatten.mp hq
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hL'
    obtain ⟨hlen, hget⟩ := forall₂_getElem hF
    have hm' : m < cs.length := by omega
    obtain ⟨A1, T1, hD, h1, hq1⟩ := emit_path d cs[m] outs[m] (hget m hm' hm) q hqL'
    exact ⟨A1, T1, .step hcs (List.getElem_mem hm') hD, h1, hq1⟩

/-- A column of a block `1 ≤ i ≤ n` is a column of the output (as `CCL.col_lt_size`). -/
theorem col_lt_size' {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (hrun : Official.expandDiagram s n = .ok R) (hTop : Recon.Top s M t root) {i x : Nat}
    (hi0 : 0 < i) (hin : i ≤ n) (hxb : x ∈ blockColumns root.column (M.size - 1) n i) :
    x + (M.size - 1 - root.column) * i < R.size := by
  have hcr := hTop.lt
  obtain ⟨hxg, hxl⟩ := Recon.mem_blockColumns hcr hxb
  have hsz := Classification.Proofs.CopyShape.Found.run_size hrun hTop (by omega)
  set W := M.size - 1 - root.column with hW
  have hWpos : 0 < W := by omega
  rw [hsz, Nat.mul_comm n W]
  rcases Nat.lt_or_eq_of_le hin with hlt | heq
  · have : W * i < W * n := (Nat.mul_lt_mul_left hWpos).mpr hlt
    have : W * i + W ≤ W * n := by
      have h2 : W * (i + 1) ≤ W * n := Nat.mul_le_mul_left W hlt
      rw [Nat.mul_succ] at h2; exact h2
    omega
  · subst heq
    have hx0 : x < M.size - 1 := by
      unfold blockColumns at hxb
      rw [if_neg (by omega), if_neg (by omega)] at hxb
      rw [List.mem_range'_1] at hxb
      omega
    omega

/-- **`CutTopGap` holds.** -/
theorem cutTopGap : TSQ.CutTopGap := by
  intro s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cv l pa hcv hl hpa hlo hlr hcut
    es' hes' j' hj' hq'
  have hi1 : 1 ≤ i := hi0
  have hcr := hTop.lt
  have hb := hTop.build
  have hVM := build_valid_of_success hb
  obtain ⟨hxg, hxl⟩ := Recon.mem_blockColumns hcr hx
  have hXR := col_lt_size' hrun hTop hi0 hin hx
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  have E := CrossUpperSim.env_of hrun hTop hXR (by omega)
  have hFR := E.FR
  obtain ⟨lo, us, hD⟩ := colData_block E hi1 hin hx hXR
  have hee : es = lo ++ us := Except.ok.inj (hes.symm.trans hD.emitsT)
  subst hee
  have hjlo : j < lo.length := TSQ.lower_index hD hj hcv hlo
  have hlj : (lo ++ us)[j] = lo[j] := List.getElem_append_left hjlo
  obtain ⟨k, cv', hsk, hk1, hcvk, _⟩ := LowerPB.lowerT_src hD.hlo (List.getElem_mem hjlo)
  have hcv2 : Reserve.cell? M lo[j].2.src = some cv := by rw [← hlj]; exact hcv
  rw [hsk] at hcv2
  have hcvv : cv = cv' := Option.some.inj (hcv2.symm.trans hcvk)
  subst hcvv
  have hxk : Reserve.cell? M ⟨x, k⟩ = some cv := hcvk
  have hsrcj : (lo ++ us)[j].2.src = ⟨x, k⟩ := by rw [hlj]; exact hsk
  -- the leg column
  have hlx : l.column < x := LowerPB.left_lt hVM hxk hl
  have hlc0 : l.column < M.size - 1 := by omega
  have hLR : l.column + (M.size - 1 - root.column) * i < R.size := by omega
  obtain ⟨lo', us', hD'⟩ := colData_inner E hi1 hin hlr hlc0 hLR
  have hee' : es' = lo' ++ us' := Except.ok.inj (hes'.symm.trans hD'.emitsT)
  subst hee'
  have hNCx := TSQ.nc_of_colData' E hi1 hD
  have hNCl := TSQ.nc_of_colData' E hi1 hD'
  have hCS : Recon.LRC.CS s n R M t root i x l.column := ⟨hNCx, hNCl, hi1, hlr, hlx⟩
  -- `pa` is at the row of `o`
  obtain ⟨hpc, hpa1, col, hcol, hp, _, _⟩ := Classification.Proofs.ChainCorr.highestAtMost_spec hpa
  have hcpa : Reserve.cell? M pa = some col[pa.index] := by
    simp only [Reserve.cell?, hpc, hcol, Option.bind_eq_bind, Option.bind_some]
    exact Array.getElem?_eq_getElem hp
  set cpa := col[pa.index] with hcpadef
  have ho := TSQ.origin_of_cut hcut
  have hrowpa : cpa.row = cv.row :=
    Classification.Proofs.ChainCorr.CutParts.TSQ.paRow_diag hb hxg hes hj ho hcv hl hpa hcpa
  have hpac : pa.column = l.column := hpc
  -- the gap copy `q` of `pa` is lower, in the tree of `l`
  have hq'src : (lo' ++ us')[j'].2.src = pa := by rw [hq']; rfl
  have hcq : Reserve.cell? M (lo' ++ us')[j'].2.src = some cpa := by rw [hq'src]; exact hcpa
  have hj'lo : j' < lo'.length := TSQ.lower_index hD' hj' hcq (by rw [hrowpa]; exact hlo)
  obtain ⟨outsX, houtsX, hloX⟩ := BTL.lowerT_outs hD.hlo
  obtain ⟨outsL, houtsL, hloL⟩ := BTL.lowerT_outs hD'.hlo
  have hqmem : (lo' ++ us')[j'] ∈ outsL.flatten := by
    rw [List.getElem_append_left hj'lo, ← hloL]; exact List.getElem_mem _
  set qq := (lo' ++ us')[j'] with hqq
  have rL := hNCl.runCtx
  have rX := hNCx.runCtx
  have hblk : (colCtx M R root i l.column).block ≠ 0 := by show i ≠ 0; omega
  have pr : Pair (colCtx M R root i l.column) (colCtx M R root i x) :=
    ⟨rfl, rfl, rfl, rfl, fun d T => by rw [colCtx_bnd hNCx, colCtx_bnd hNCl], hblk⟩
  -- the anchor, roles exchanged
  have hu : ((⟨x, k⟩ : Ref), cv) ∈ realNodes M x :=
    Classification.Proofs.CopyShape.mem_realNodes_of_cell' hxk hk1
  have H := anch_of hCS hu (Classification.Proofs.P3T.leftColumn_of_left hl)
  have hascC := Recon.Pk4.emitsT_cleanAsc hes (lo ++ us)[j] (List.getElem_mem hj)
    (by rw [ho]; rfl) cv (by rw [hsrcj]; exact hxk)
  obtain ⟨dC, SC, ρC, hρC, hρCrow, hascXC⟩ := hascC
  have H' : AnchR (colCtx M R root i l.column) (colCtx M R root i x) (official cv.row) := by
    refine ⟨fun d S ρr ρc hρ hlt => (H.eq d S ρr ρc hρ hlt).symm, ?_, ?_⟩
    · intro d S ρr ρc hρ hle hasc
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact (H.eq d S ρr ρc hρ hlt).mpr hasc
      · rw [Classification.Proofs.P3T.ascends_row (r' := ρC.1) (cl' := ρC.2)
          (heq.trans hρCrow.symm)]
        exact hascXC
    · intro refx cx gx refy cy gy hnx hgx hny hgy
      have := H.gen refy cy gy refx cx gx hny hgy hnx hgx
      omega
  -- the path of `q` in the tree of `l`
  obtain ⟨L', hL', hqL'⟩ := List.mem_flatten.mp hqmem
  obtain ⟨aF, haF, rfl⟩ := List.getElem_of_mem hL'
  obtain ⟨hlenL, hallL⟩ := mapM_except_spec _ _ _ houtsL
  have haF' : aF < (lowerItems (official t.row)).length := by omega
  set FI := (lowerItems (official t.row))[aF] with hFI
  have hFmem : FI ∈ lowerItems (official t.row) := List.getElem_mem haF'
  have hrunF := hallL aF haF' haF
  obtain ⟨_, _, hF1, _⟩ := lower_itemOK (ctx := colCtx M R root i l.column) hFmem
  obtain ⟨dF, hdF⟩ : ∃ dF, FI.1 = dF + 1 := ⟨FI.1 - 1, by omega⟩
  rw [hdF] at hrunF
  obtain ⟨A1, T1, hDA1, hT1, hqT1⟩ := emit_path dF FI.2 _ hrunF _ hqL'
  rw [← hdF] at hDA1
  obtain ⟨C', cs1, hC', hn1, hcb1, hrow1⟩ :=
    Classification.Proofs.P3T.levelOne_clean hT1 hqT1 hq'
  obtain ⟨hn1m, hn1r⟩ := RowLaw.nodeAt_spec hn1
  obtain ⟨_, _, hcs1cell⟩ := Classification.mem_realNodes hn1m
  have hcs1 : cs1 = cpa := Option.some.inj (hcs1cell.symm.trans hcpa)
  subst hcs1
  have hC'v : C' = official cv.row := by rw [← hn1r, hrowpa]
  -- the level of the first item is at least `2`
  have hF2 : 1 < FI.1 := by
    by_contra hn
    have h1 : FI.1 = 1 := by omega
    rw [h1] at hDA1
    have := desc_eq hDA1
    have hcl := Inner.lowerItems_clean _ _ hFmem
    rw [this, hC'] at hcl
    cases hcl
  obtain ⟨P2, cs2, hDP2, hcs2, hA1m⟩ := desc_parent hDA1 hF2
  obtain ⟨m, hm, hm2⟩ := List.getElem_of_mem hA1m
  -- the region facts
  have hA1T : InTree (colCtx M R root i l.column) (official t.row) 1 A1 := ⟨FI, hFmem, hDA1⟩
  have hP2T : InTree (colCtx M R root i l.column) (official t.row) (0 + 1 + 1) P2 :=
    ⟨FI, hFmem, hDP2⟩
  have hqA1 : inRegion 1 A1.target qq.1.row = true := by
    rw [hrow1]; exact Classification.inRegion_self 1 _
  have hqP2 : inRegion (0 + 2) P2.target qq.1.row = true := by
    obtain ⟨_, hP2OK⟩ := LowerLeftProof.inTree_itemOK rL hP2T
    rw [← hm2] at hqA1
    exact region_sub_of_child rL hP2OK hcs2 hm hqA1
  have hqmem' : qq ∈ outsL.flatten := hqmem
  have hEOK : ∀ d A, Desc (colCtx M R root i l.column) FI.1 FI.2 d A → 0 + 2 ≤ d →
      inRegion d A.target qq.1.row = true →
      Inner.EmitOK (colCtx M R root i l.column).source (colCtx M R root i l.column).rootColumn d A
        qq := fun d A hD _ hin => eok_of_tree rL houtsL hqmem' ⟨FI, hFmem, hD⟩ hin
  have hY : ∀ d B, Desc (colCtx M R root i x) FI.1 FI.2 (d + 2) B →
      ∃ csY, childItems (colCtx M R root i x) (d + 2) B = .ok csY := by
    intro d B hD
    obtain ⟨TB, hTB, _⟩ := tinTree rX houtsX ⟨FI, hFmem, hD⟩
    obtain ⟨csY, _, hcsY, _⟩ := runItemT_children hTB
    exact ⟨csY, hcsY⟩
  have hin' : i ≤ n := hin
  have hFMDL := Classification.Proofs.CopyShape.Found.factMD_of_bctx hTop (colCtx_bctx hNCl)
  have hFMDX := Classification.Proofs.CopyShape.Found.factMD_of_bctx hTop (colCtx_bctx hNCx)
  have hFMHX := Classification.Proofs.CopyShape.Found.factMH_of_bctx hrun hTop hi1 hin'
    (colCtx_bctx hNCx)
  have hMDX : ∀ d A r cl, Desc (colCtx M R root i l.column) FI.1 FI.2 (d + 2) A →
      topIn (colCtx M R root i l.column).source (colCtx M R root i l.column).rootColumn (d + 2)
        A.source = some (r, cl) →
      ascends (colCtx M R root i l.column) (some (r, cl)) = .ok true →
      height (d + 2) (official cl.row) < heightOf (d + 2) (topIn
        (colCtx M R root i l.column).source (colCtx M R root i l.column).lastColumn (d + 2)
        A.source) :=
    fun d A r cl hD hρ hasc => hFMDL d A (reach_of_inTree ⟨FI, hFmem, hD⟩) r cl hρ hasc
  have hMDY : ∀ d B r cl, Desc (colCtx M R root i x) FI.1 FI.2 (d + 2) B →
      topIn (colCtx M R root i l.column).source (colCtx M R root i l.column).rootColumn (d + 2)
        B.source = some (r, cl) →
      ascends (colCtx M R root i x) (some (r, cl)) = .ok true →
      height (d + 2) (official cl.row) < heightOf (d + 2) (topIn
        (colCtx M R root i l.column).source (colCtx M R root i l.column).lastColumn (d + 2)
        B.source) :=
    fun d B r cl hD hρ hasc => hFMDX d B (reach_of_inTree ⟨FI, hFmem, hD⟩) r cl hρ hasc
  have hMHY : ∀ d B, Desc (colCtx M R root i x) FI.1 FI.2 (d + 2) B →
      ∀ C r cl csRef csc g, B.clean = some C → B.cutBottom = false →
      topIn (colCtx M R root i l.column).source (colCtx M R root i l.column).rootColumn (d + 2)
        B.source = some (r, cl) →
      nodeAt (colCtx M R root i l.column).source (colCtx M R root i x).x C = some (csRef, csc) →
      generations (colCtx M R root i l.column).source (colCtx M R root i l.column).rootColumn C
        ((colCtx M R root i x).x + 1) csRef csc 0 = .ok g →
      height (d + 2) (official cl.row) ≤
        heightOf (d + 2) (topIn (colCtx M R root i l.column).result
          (colCtx M R root i l.column).boundary (d + 2) B.target) + g := by
    intro d B hD C r cl csRef csc g hC hcb hρ hn hg
    have := hFMHX d B C (reach_of_inTree ⟨FI, hFmem, hD⟩) hC hcb csRef csc g hn hg
    have hρ' : topIn (colCtx M R root i x).source (colCtx M R root i x).rootColumn (d + 2)
        B.source = some (r, cl) := hρ
    rw [hρ', pr.bnd] at this
    exact this
  have hcθ : Reserve.cell? (colCtx M R root i l.column).source qq.2.src = some cpa := hcq
  have hθa : official cpa.row = official cv.row := by rw [hrowpa]
  have hwq : ((⟨x, k⟩ : Ref), cv) ∈ realNodes (colCtx M R root i l.column).source
      (colCtx M R root i x).x := hu
  obtain ⟨B2, hDB2, hsim2⟩ := simR_chain pr rL hFmem hb H' hcθ hθa (lam := qq.1.row) (e := 0)
    hEOK hY hwq (fun _ _ => rfl) hMDX hMDY hMHY (FI.1 - 2) 2 P2 (by omega) hDP2 le_rfl hqP2
  -- the last step, to level `1`
  obtain ⟨csX2, hcsX2⟩ := hY 0 B2 hDB2
  obtain ⟨ax2, hax2⟩ : ∃ ax, topIn (colCtx M R root i l.column).source
      (colCtx M R root i l.column).x (0 + 2) P2.source = some ax := by
    cases h : topIn (colCtx M R root i l.column).source (colCtx M R root i l.column).x (0 + 2)
      P2.source with
    | none =>
      have := childItems_none hcs2 h
      rw [this] at hm; simp at hm
    | some ax => exact ⟨ax, rfl⟩
  have hEA := hEOK (0 + 2) P2 hDP2 le_rfl hqP2
  have hEc : Inner.EmitOK (colCtx M R root i l.column).source
      (colCtx M R root i l.column).rootColumn (0 + 1) cs2[m] qq := by
    rw [hm2]; exact eok_of_tree rL houtsL hqmem' hA1T hqA1
  obtain ⟨hA1src, _⟩ := eok_parts hEc hcθ
  have hw : inRegion (0 + 1) cs2[m].source (official cv.row) = true := by
    rw [← hθa]; exact hA1src
  obtain ⟨hmX, hsim1, _⟩ := stepR pr hb H' hcθ hθa hsim2 hcs2 hcsX2 hax2 (j := m) (j' := m)
    le_rfl (by omega) hm hEA hEc hwq hw (hMDX 0 P2 · · hDP2)
    (fun r cl hρ hasc => by
      have hBs := hsim2.source
      have := hMDY 0 B2 r cl hDB2 (by rw [hBs]; exact hρ) hasc
      rw [hBs] at this; exact this) (hMHY 0 B2 hDB2)
  -- the similar item at level `1` is `A₁`
  have hXA1 : csX2[m] = A1 := by
    rcases hsim1 with h | h | h
    · rw [← h, hm2]
    · exfalso
      obtain ⟨hcl, _⟩ := h
      rw [hm2, hC'] at hcl; cases hcl
    · exfalso
      obtain ⟨_, _, _, _, hcbA, _⟩ := h
      rw [hm2, hcb1] at hcbA; cases hcbA
  have hA1X : InTree (colCtx M R root i x) (official t.row) 1 A1 := by
    rw [← hXA1]
    exact ⟨FI, hFmem, LowerLeftProof.desc_snoc hDB2 hcsX2 (List.getElem_mem hmX)⟩
  obtain ⟨TX1, hTX1, hsubX, _, _⟩ := tinTree rX houtsX hA1X
  -- the copy of `o` emitted by `A₁` in the tree of `x`
  have hA1s : A1.source = official cv.row := by
    have h := hw
    rw [hm2] at h
    apply Row.ext
    intro r
    exact ((inRegion_iff'.mp h) r (by omega)).symm
  have hno : nodeAt M x (official cv.row) = some (⟨x, k⟩, cv) :=
    Classification.Proofs.CutGap.nodeAt_of_cell hVM hxk hk1
  obtain ⟨e, he, hesrc, herow⟩ := BTL.levelOne_clean_emit hTX1 (oRef := ⟨x, k⟩) (cv := cv)
    (by show nodeAt M x A1.source = _; rw [hA1s]; exact hno) hC'
    (by show nodeAt M x C' = _; rw [hC'v]; exact hno)
  have heX := hsubX e he
  have helo : e ∈ lo := by rw [hloX]; exact heX
  -- `e` is at or below the top copy `u`
  obtain ⟨je, hje, hjee⟩ := List.getElem_of_mem helo
  have hjej : je ≤ j := by
    by_contra hn
    have hje' : je < (lo ++ us).length := by rw [List.length_append]; omega
    have := htop je hje' hj (by omega)
    rw [List.getElem_append_left hje, hjee, hesrc, hsrcj] at this
    exact this rfl
  have hk : j + 1 < (R[x + (M.size - 1 - root.column) * i]'hXR).size := by
    have := hD.size; rw [this, List.length_append]; omega
  have hk2 : je + 1 < (R[x + (M.size - 1 - root.column) * i]'hXR).size := by omega
  obtain ⟨_, hrow, _⟩ := hD.node hk (by omega)
  obtain ⟨_, hrow2, _⟩ := hD.node hk2 (by omega)
  have hmono := (hFR.rows_strict ⟨x + (M.size - 1 - root.column) * i, hXR⟩).monotone
    (show (⟨je + 1, hk2⟩ : Fin _) ≤ ⟨j + 1, hk⟩ from by show je + 1 ≤ j + 1; omega)
  change (R[x + (M.size - 1 - root.column) * i]'hXR)[je + 1].row ≤
    (R[x + (M.size - 1 - root.column) * i]'hXR)[j + 1].row at hmono
  rw [hrow, hrow2] at hmono
  simp only [Nat.add_sub_cancel] at hmono
  rw [List.getElem_append_left hje, hjee] at hmono
  have hle := Classification.Proofs.ChainCorr.stored_le_iff.mp hmono
  show qq.1.row ≤ (lo ++ us)[j].1.row
  rw [hrow1, ← herow]
  exact hle

end OmegaY.Official.Recon.TSQ.CTG

#print axioms OmegaY.Official.Recon.TSQ.CTG.cutTopGap
