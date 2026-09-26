/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CPNMain.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CPNBase

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# `CutParentNT` holds (`CPN`)

`CutParentNT` (`SeamCut.lean`): for a gap copy `u = (X, j+1)` (`X = x + w·i`, `i ≥ 1`) of
`m = (x, C)` that is not the top copy of `m` in its column, the stored parent `u₁` of `u` (the left
end of the node `u⁺` above `u`) is in the boundary column `B_i` (and the generation step of `m`
goes to the root column), or it is a gap copy, not the top copy, of the next generation `b` of `m`.

## The argument

* The emit `j + 1` is a gap copy of `m`: the top copy `j' > j` of `m` is a gap copy (a non-gap
  emit does not repeat an earlier origin, `NNC`), and contiguity (`CPN.gapBetween`) fills the
  emits between. So `u⁺` is a copy of `m` with the leg `l` of `m`, and `u₁` is the highest node of
  the column `φ(l)` below the row of `u⁺` (`CrossUpperSim.highestIn_of_hb`).
* The generation step `m → b` of the clean copy (`CPN.genStep_of_clean`) ends at `c_r` or right
  of it. At `c_r`, `φ(l) = B_i`.
* Right of `c_r`, the column `Y = φ(l)` holds:
  - the non-gap copy `k₀` of `b`, at the root row `C` (`CPN.nonGapCopy`);
  - the gap copy `k_g` of `b` right after it, at the row `bump C 0` (`CutGap.emitsT_firstGap`, with
    `FactFG` in the diagram, `CPN.factFG_of_bctx`); `bump C 0 ≤ row u < row u⁺`, since the gap copy
    `u` is above the root row `C`;
  - a gap copy `k_K` of `b` at a row `≥ row u⁺` (`P3T.run_top_core`, applied to `u⁺`).
  So `u₁ = (Y, e + 1)` with `k_g ≤ e < k_K`, and contiguity makes `e` a gap copy of `b`; `k_K`
  above it shows that it is not the top copy.
-/

namespace OmegaY.Official.Recon.TopChain.Seam.CPN

open Canonical Expansion Geometry Frame Classification
open Classification.Proofs.ChainCorr (MStep cutOrigin blockEmits)
open Classification.Proofs.ChainCorr.Inner (GenStep)
open Classification.Proofs.ChainCorr.LowerChain (IsTopAt)
open CrossUpperSim CrossUpper

private theorem emit_lt {X i x : Nat} {lo us : List (Emit × Origin)}
    {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (hD : LowerPB.ColData s n R M t root X i x lo us) {a b : Nat}
    (ha : a < (lo ++ us).length) (hb : b < (lo ++ us).length) (hab : a < b) :
    ((lo ++ us)[a]).1.row < ((lo ++ us)[b]).1.row := by
  have := List.pairwise_iff_getElem.mp hD.sorted a b (by simp only [List.length_map]; exact ha)
    (by simp only [List.length_map]; exact hb) hab
  simpa only [List.getElem_map] using this

/-- `NNC` for the emits of a column of a block `1 ≤ i ≤ n`. -/
private theorem nnc_of_colData {X i x : Nat} {lo us : List (Emit × Origin)}
    {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (hD : LowerPB.ColData s n R M t root X i x lo us) (hi1 : 1 ≤ i) :
    (lo ++ us).Pairwise Classification.Proofs.CopyShape.NoMA.NNC := by
  have hTop := hD.top
  have hVM := build_valid_of_success hTop.build
  have hin : i ≤ n := hD.iln
  exact (Proofs.CopyShape.NoMA.emitsT_shapeW
    (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X) (official t.row) R
    (root.column + (M.size - 1 - root.column) * i) (by exact hVM) (by exact hi1)
    (fun d T => by
      have hb := hD.bctx
      have : (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X).boundary =
          root.column + (M.size - 1 - root.column) * i := rfl
      rw [this]
      exact Proofs.CopyShape.Found.topIn_congr hb.bnd)
    (Proofs.CopyShape.Found.factMD_of_bctx hTop hD.bctx)
    (Proofs.CopyShape.Found.factMH_of_bctx hD.run hTop hi1 hin hD.bctx) hD.emitsT).1

/-- A new column from its column data. -/
private theorem nc_of_colData {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (E : Env s n R M t root) {i x : Nat} {lo us : List (Emit × Origin)} (hi1 : 1 ≤ i)
    (hD : LowerPB.ColData s n R M t root (x + (M.size - 1 - root.column) * i) i x lo us) :
    JumpLaw.NewColumn s n R M t root i x := by
  have hcr := E.top.lt
  obtain ⟨hxg, hxl⟩ := mem_blockColumns hcr hD.xb
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  have hXR := hD.XR
  obtain ⟨i', x', hi', hx', hXeq, hcopy⟩ := E.CI.2.2 (x + (M.size - 1 - root.column) * i) hXR
    (by omega)
  obtain ⟨hii, hxx⟩ := Classification.Proofs.ChainCorr.NonTop.blockX_unique hcr hxg hxl hx'
    hXeq (by omega)
  subst hii hxx
  have hn0 : n ≠ 0 := by have := hD.iln; omega
  exact ⟨E.run, E.top, hn0, E.CI, hi', hD.xb, hXR, ⟨_, Array.getElem?_eq_getElem hXR, hcopy⟩⟩

/-- **`CutParentNT` holds.** -/
theorem cutParentNT : CutParentNT := by
  intro s n R M t root i x es j hD hi0 hj hcut hnt u1 hru
  have hin := hD.le_n hi0
  have hD0 := hD
  obtain ⟨hrun, hTop, hx, hes, _, _⟩ := hD0
  obtain ⟨E, lo, us, hDc, hee⟩ := colData_of_node hD
  subst hee
  have hcr := hTop.lt
  have hVM := build_valid_of_success hTop.build
  have hVR := Classification.Proofs.ChainCorr.NonTop.SeamD.validR hrun
  have hF := E.FR
  obtain ⟨hxg, hxl⟩ := mem_blockColumns hcr hx
  have hi : i < n + 1 := by omega
  -- the top copy above `u` is a gap copy
  have hnt' := hnt
  unfold IsTopAt at hnt'
  push Not at hnt'
  obtain ⟨j', hj', _, hjj, hsrcT⟩ := hnt'
  have hnnc := nnc_of_colData hDc hi0
  have hoj : ((lo ++ us)[j]).2 = .clean ((lo ++ us)[j]).2.src true :=
    Classification.Proofs.ChainCorr.Pkg3.origin_clean_of_cut rfl hcut
  have hcutT : cutOrigin ((lo ++ us)[j']).2 = true := by
    cases h : cutOrigin ((lo ++ us)[j']).2
    · exact absurd hsrcT.symm (List.pairwise_iff_getElem.mp hnnc j j' hj hj' hjj h)
    · rfl
  have hoT : ((lo ++ us)[j']).2 = .clean ((lo ++ us)[j]).2.src true :=
    Classification.Proofs.ChainCorr.Pkg3.origin_clean_of_cut hsrcT hcutT
  -- the emit `j + 1` is a gap copy of `m`
  obtain ⟨hj1, hoj1⟩ := Classification.Proofs.ChainCorr.NonTop.SeamD.CPN.gapBetween
    (ctx := ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
      (x + (M.size - 1 - root.column) * i)) hVM hes hnnc hj hj' (Nat.lt_succ_self j)
    (by omega) hoj hoT
  set m := ((lo ++ us)[j]).2.src with hm
  have hva0 : Classification.Proofs.ChainCorr.NonTop.CopyAtX M R n root.column (M.size - 1)
      (official t.row) i ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ (.clean m true) :=
    ⟨x, lo ++ us, j, hxg, hxl, hx, rfl, rfl, hes, hj, hoj⟩
  have hva1 : Classification.Proofs.ChainCorr.NonTop.CopyAtX M R n root.column (M.size - 1)
      (official t.row) i ⟨x + (M.size - 1 - root.column) * i, j + 1 + 1⟩ (.clean m true) :=
    ⟨x, lo ++ us, j + 1, hxg, hxl, hx, rfl, rfl, hes, hj1, hoj1⟩
  -- the left end of `u⁺` is `u₁`
  obtain ⟨cu1, ref1, co, l, hcu1, hrefl, hco, hl, hrefc⟩ :=
    Classification.Proofs.ChainCorr.NonTop.SeamD.copyAtX_leftD E hi0 hi hva1
  change Reserve.cell? M m = some co at hco
  obtain ⟨cu', hcu', hleft⟩ := Classification.Proofs.ChainCorr.Inner.rawParent_eq_some.mp hru
  have hup : Classification.Proofs.ChainCorr.Inner.up
      (⟨x + (M.size - 1 - root.column) * i, j + 1⟩ : Ref) =
      ⟨x + (M.size - 1 - root.column) * i, j + 1 + 1⟩ := rfl
  rw [hup] at hcu'
  have ecu : cu1 = cu' := Option.some.inj (hcu1.symm.trans hcu')
  subst ecu
  have hu1 : u1 = ref1 := Option.some.inj (hleft.symm.trans hrefl)
  subst hu1
  -- the generation step of `m`
  obtain ⟨b, hgs, hbge⟩ := Classification.Proofs.ChainCorr.NonTop.SeamD.CPN.genStep_of_clean hTop
    hva0
  have hgs' := hgs
  obtain ⟨hmc, hb1, ca, cb, l', hca, hl', hbl, hcb, hbrow⟩ := hgs'
  have eca : co = ca := Option.some.inj (hco.symm.trans hca)
  subst eca
  have el : l = l' := Option.some.inj (hl.symm.trans hl')
  subst el
  rcases Nat.lt_or_eq_of_le hbge with hlt | heq
  swap
  · -- the leg is the root column
    refine Or.inl ⟨?_, b, hgs, heq.symm⟩
    rw [hrefc, ← hbl, ← heq, Classification.Proofs.ChainCorr.mapColumn_of_ge (le_refl _)]
  -- the leg is right of the root column
  right
  have hlcr : root.column < b.column := hlt
  have hbx : b.column < x := by
    have := Classification.left_lt_of_valid hVM hca hl
    rw [hbl]
    have hmx : m.column = x := by
      obtain ⟨hsc, _⟩ := emitsT_good hes (lo ++ us)[j] (List.getElem_mem hj)
      rw [hoj] at hsc
      simpa [ctxAt, Origin.isUpper, Origin.src] using hsc
    omega
  have hu1c : u1.column = b.column + (M.size - 1 - root.column) * i := by
    rw [hrefc, ← hbl, Classification.Proofs.ChainCorr.mapColumn_of_ge (le_of_lt hlcr)]
  -- the non-gap copy of `b` in `Y = φ(l)`
  obtain ⟨lol, usl, hDl, k0, hk0, hk0c, co', hca', hRR, hk0row⟩ :=
    Classification.Proofs.ChainCorr.NonTop.SeamD.CPN.nonGapCopy E hi0 hi hva0 hgs hlcr
  have eca' : co = co' := Option.some.inj (hca.symm.trans hca')
  subst eca'
  have hnnl := nnc_of_colData hDl hi0
  -- the gap copy right after it
  have hFG := Classification.Proofs.ChainCorr.NonTop.SeamD.CPN.factFG_of_bctx hrun hTop hi0 hin
    hDl.bctx (by exact hlcr)
  have hMD := Proofs.CopyShape.Found.factMD_of_bctx hTop hDl.bctx
  obtain ⟨qg, hqg, hqgo, hqgrow⟩ := Classification.Proofs.CutGap.emitsT_firstGap _ _
    (by exact hVM) (by exact hi0) hMD hFG hDl.emitsT (lol ++ usl)[k0] (List.getElem_mem hk0) b
    hk0c
  obtain ⟨kg, hkg, hkgq⟩ := List.getElem_of_mem hqg
  rw [← hkgq] at hqgo hqgrow
  -- rows: `bump C 0 ≤ row u < row u⁺`
  have hECj := ecmp_of_colData hDc _ (List.getElem_mem hj) co (by rw [← hm]; exact hca)
  have hCu : official co.row < ((lo ++ us)[j]).1.row :=
    ((hECj _ hRR).2 hcut).1 le_rfl
  have huu1 : ((lo ++ us)[j]).1.row < ((lo ++ us)[j + 1]).1.row :=
    emit_lt hDc hj hj1 (Nat.lt_succ_self j)
  have hgu1 : ((lol ++ usl)[kg]).1.row < ((lo ++ us)[j + 1]).1.row := by
    rw [hqgrow, hk0row]
    exact lt_of_le_of_lt (Classification.Proofs.CutGap.bump_zero_le hCu) huu1
  have hk0kg : k0 < kg := by
    by_contra hn
    rcases Nat.lt_or_eq_of_le (not_lt.mp hn) with h' | h'
    · have := emit_lt hDl hkg hk0 h'
      rw [hqgrow] at this
      exact absurd (lt_trans this (Row.lt_bump _ 0)) (lt_irrefl _)
    · subst h'
      have := Row.lt_bump ((lol ++ usl)[kg]).1.row 0
      rw [← hqgrow] at this
      exact lt_irrefl _ this
  -- a gap copy of `b` at or above `u⁺`
  have hNCx := nc_of_colData E hi0 hDc
  have hNCl := nc_of_colData E hi0 hDl
  have hCS : Recon.LRC.CS s n R M t root i x b.column := ⟨hNCx, hNCl, hi0, hlcr, hbx⟩
  obtain ⟨outsX, usX, hoX, hesXe, hupX⟩ := Classification.Proofs.P3T.lower_of_emits hDc.emitsT
  obtain ⟨outsY, usY, hoY, hesYe, _⟩ := Classification.Proofs.P3T.lower_of_emits hDl.emitsT
  have hpX : (lo ++ us)[j + 1] ∈ outsX.flatten := by
    have hmem : (lo ++ us)[j + 1] ∈ outsX.flatten ++ usX := by
      rw [← hesXe]; exact List.getElem_mem hj1
    rcases List.mem_append.mp hmem with h | h
    · exact h
    · exact absurd (hupX _ h) (by rw [hoj1]; simp [Origin.isUpper])
  have hmx : (m, co) ∈ realNodes M x := by
    obtain ⟨hsc, hs1, _⟩ := emitsT_good hes (lo ++ us)[j] (List.getElem_mem hj)
    have := Classification.Proofs.CopyShape.mem_realNodes_of_cell' hca hs1
    have hmc' : m.column = x := by
      rw [hoj] at hsc
      simpa [ctxAt, Origin.isUpper, Origin.src] using hsc
    rw [hmc'] at this
    exact this
  have hbmem : (b, cb) ∈ realNodes M b.column :=
    Classification.Proofs.CopyShape.mem_realNodes_of_cell' hcb hb1
  obtain ⟨qK, hqK, hqKo, hqKrow⟩ := Classification.Proofs.P3T.run_top_core hCS hoX hoY hpX
    hoj1 hmx (by rw [hbl]; exact Classification.Proofs.P3T.leftColumn_of_left hl) hbmem
    (by rw [hbrow])
  have hqKm : qK ∈ lol ++ usl := by rw [hesYe]; exact List.mem_append_left _ hqK
  obtain ⟨kK, hkK, hkKq⟩ := List.getElem_of_mem hqKm
  rw [← hkKq] at hqKo hqKrow
  -- the frame nodes of `u`, `u⁺`, `u₁`
  have hjl : j < (lo ++ us).length := hj
  obtain ⟨c0, hc0, _, _⟩ := colCell hDc hjl
  obtain ⟨c1, hc1, hc1row, _⟩ := colCell hDc hj1
  have ec1 : cu1 = c1 := Option.some.inj (hcu1.symm.trans hc1)
  subst ec1
  obtain ⟨UN, hUN, _⟩ := LowerChainRecon.node_of_cell hc0
  obtain ⟨VN, hVN, hVNc⟩ := LowerChainRecon.node_of_cell hc1
  obtain ⟨cq, hcq, _⟩ := Classification.Proofs.ChainCorr.Inner.left_cell hVR hc1 hrefl
  obtain ⟨AN, hAN, _⟩ := LowerChainRecon.node_of_cell hcq
  have hV1 : VN.1 = UN.1 := Fin.ext (by
    have h1 := congrArg Ref.column hVN; have h2 := congrArg Ref.column hUN
    simp [Frame.ref] at h1 h2; omega)
  have huu : (Frame.ofMountain R).upper UN = some VN :=
    Classification.ControlProof.upper_eq_of_index hV1.symm (by
      have h1 := congrArg Ref.index hVN; have h2 := congrArg Ref.index hUN
      simp [Frame.ref] at h1 h2; omega)
  have hUr : Real UN := by
    show 0 < UN.2.val
    have := congrArg Ref.index hUN; simp [Frame.ref] at this; omega
  have hAraw : (Frame.ofMountain R).rawParent UN = some AN :=
    Geometry.Frame.rawParent_eq_of_upper_left huu (by rw [hVNc, hAN]; exact hrefl)
  have hAH := CrossUpperSim.highestIn_of_hb (E.HB UN hUr) huu hAraw
  have hVh : (Frame.ofMountain R).height VN = stored ((lo ++ us)[j + 1]).1.row := by
    change ((Frame.ofMountain R).cell VN).row = _; rw [hVNc, hc1row]
  have hANcol : AN.1.val = b.column + (M.size - 1 - root.column) * i := by
    have := congrArg Ref.column hAN; simp [Frame.ref] at this; omega
  -- the gap copy `k_g` is at or below `u₁`
  obtain ⟨cG, hcG, hcGrow, _⟩ := colCell hDl hkg
  obtain ⟨GN, hGN, hGNc⟩ := LowerChainRecon.node_of_cell hcG
  have hGA : GN.1 = AN.1 := Fin.ext (by
    have := congrArg Ref.column hGN; simp [Frame.ref] at this; omega)
  have hGi : GN.2.val = kg + 1 := by
    have := congrArg Ref.index hGN; simp [Frame.ref] at this; omega
  have hGle : GN.2.val ≤ AN.2.val := hAH.2 GN hGA (by
    change ((Frame.ofMountain R).cell GN).row < _
    rw [hGNc, hcGrow, hVh]
    exact Recon.stored_strictMono hgu1)
  -- `u₁` is below the gap copy `k_K`
  obtain ⟨cK, hcK, hcKrow, _⟩ := colCell hDl hkK
  obtain ⟨KN, hKN, hKNc⟩ := LowerChainRecon.node_of_cell hcK
  have hKA : KN.1 = AN.1 := Fin.ext (by
    have := congrArg Ref.column hKN; simp [Frame.ref] at this; omega)
  have hKi : KN.2.val = kK + 1 := by
    have := congrArg Ref.index hKN; simp [Frame.ref] at this; omega
  have hAK : AN.2.val < KN.2.val := by
    by_contra hn
    have h1 := Classification.ControlProof.height_le_of_index hF hKA (not_lt.mp hn)
    have h2 : (Frame.ofMountain R).height VN ≤ (Frame.ofMountain R).height KN := by
      change _ ≤ ((Frame.ofMountain R).cell KN).row
      rw [hKNc, hcKrow, hVh]
      exact Classification.Proofs.ChainCorr.stored_le_iff.mpr hqKrow
    exact absurd (lt_of_lt_of_le hAH.1 (le_trans h2 h1)) (lt_irrefl _)
  -- `u₁` is a gap copy of `b`, not the top copy
  have he1 : 1 ≤ AN.2.val := by omega
  have hel : AN.2.val - 1 < (lol ++ usl).length := by omega
  obtain ⟨hebl, heb⟩ := Classification.Proofs.ChainCorr.NonTop.SeamD.CPN.gapBetween
    (ctx := ctxAt M R b.column i root.column (M.size - 1 - root.column) (M.size - 1)
      (b.column + (M.size - 1 - root.column) * i)) hVM hDl.emitsT hnnl hk0 hkK
    (a := k0) (b := AN.2.val - 1) (by omega) (by omega) hk0c hqKo
  have hu1eq : u1 = ⟨b.column + (M.size - 1 - root.column) * i, AN.2.val - 1 + 1⟩ := by
    rw [← hAN]; simp only [Frame.ref, hANcol]; congr 1; omega
  obtain ⟨cE, hcE, _, _⟩ := colCell hDl hel
  refine ⟨b.column, lol ++ usl, AN.2.val - 1, ⟨hrun, hTop, hDl.xb, hDl.emitsT, ⟨cE, hcE⟩, hel⟩,
    hu1eq, hel, by rw [heb]; rfl, ?_, by rw [heb]; exact hgs⟩
  intro htop
  exact htop kK hkK hel (by omega) (by rw [heb, hqKo])

/-- **`StepCutNT` holds.** -/
theorem stepCutNT : StepCutNT := stepCutNT_of_parent cutParentNT

/-- **`BoundaryChainD` holds.** -/
theorem boundaryChainD : BoundaryChainD := boundaryChainD_of_cut stepCutNT

/-- **`BoundaryChain` holds.** -/
theorem boundaryChain : Classification.Proofs.ChainCorr.BoundaryChain :=
  boundaryChain_of_cutParent cutParentNT

/-- **`TopStepLoRoot` from `StepRootTop`.** -/
theorem topStepLoRoot_of_stepRootTop (hR : StepRootTop) : TopStepLoRoot :=
  topStepLoRoot_of_cutParent cutParentNT hR

end OmegaY.Official.Recon.TopChain.Seam.CPN

#print axioms OmegaY.Official.Recon.TopChain.Seam.CPN.cutParentNT
#print axioms OmegaY.Official.Recon.TopChain.Seam.CPN.stepCutNT
#print axioms OmegaY.Official.Recon.TopChain.Seam.CPN.boundaryChainD
#print axioms OmegaY.Official.Recon.TopChain.Seam.CPN.boundaryChain
#print axioms OmegaY.Official.Recon.TopChain.Seam.CPN.topStepLoRoot_of_stepRootTop
