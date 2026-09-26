/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/SeamCleanStep.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.SeamClean

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# The step from a clean copy (`StepCleanNT`)

For a clean copy `Q` (`b = 0`) of `a = (x, C)` in a block `i ≥ 1`, the first step `a → m'` of the
chain of `M(s)` lands on the generation chain of `a` in the row `C`, or passes the end
`g = (c_r, C)` of that chain and its step `g → g₁` (`cleanParentReachD`). The output chain from
`Q` walks at scale `0` along the clean copies of the generation chain to the boundary node `P` of
`B_i` at the row of `Q` (`walkXD`). A clean copy of a node `m'` of the chain reaches what the
chain of `m'` reaches (induction); the node `P` is a copy of a node `ν` of `x₀` at the row `C`
(`boundary_lookup`: the copies keep their place among the root rows), whose chain reaches the
steps of `g` (`SRX0.x0Reach`).
-/

namespace OmegaY.Official.Recon.TopChain.Seam

open Canonical Expansion Geometry Frame Classification
open Classification.Proofs.ChainCorr (MStep cutOrigin blockEmits)
open Classification.Proofs.ChainCorr.Inner (GenStep)
open Classification.Proofs (ScaleReach)
open Classification.Proofs.ChainCorr.LowerChain (IsTopAt)

/-- A generation chain moves left. -/
theorem genChain_col_lt {M : Mountain} (hV : MountainValid M) {cr : Nat} {a b : Ref}
    (h : Relation.TransGen (GenStep M cr) a b) : b.column < a.column := by
  induction h with
  | single hab =>
      obtain ⟨_, _, ca, cb, l, hca, hl, hbl, _, _⟩ := hab
      rw [hbl]; exact left_lt_of_valid hV hca hl
  | tail _ hbc ih =>
      obtain ⟨_, _, ca, cb, l, hca, hl, hbl, _, _⟩ := hbc
      have := left_lt_of_valid hV hca hl
      omega

section Run

variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}

/-- **The boundary node at a root row.** A node `P` of `B_i` at the row of a node `g` of the root
column below `τ` is a lower copy of a node `ν` of `x₀` with `hAM(c_r, row ν) = g`. -/
theorem boundary_lookup (E : CrossUpperSim.Env s n R M t root) {i : Nat} (hi0 : 0 < i)
    (hin : i ≤ n) {P : Ref} {cP : Cell}
    (hPc : P.column = root.column + (M.size - 1 - root.column) * i)
    (hcP : Reserve.cell? R P = some cP) (hcP1 : (1 : Row) ≤ cP.row) {g : Ref} {cg : Cell} (hgc : g.column = root.column)
    (hg1 : 1 ≤ g.index) (hcg : Reserve.cell? M g = some cg)
    (hrow : official cP.row = official cg.row) (hτ : official cg.row < official t.row) :
    ∃ esB k, ∃ hk : k < esB.length,
      blockEmits M R root.column (M.size - 1) (official t.row) (i - 1) (M.size - 1) = .ok esB ∧
      P = ⟨M.size - 1 + (M.size - 1 - root.column) * (i - 1), k + 1⟩ ∧
      ∃ cν, Reserve.cell? M esB[k].2.src = some cν ∧ esB[k].2.src.column = M.size - 1 ∧
        1 ≤ esB[k].2.src.index ∧ cν.row < t.row ∧
        Reserve.highestAtMost M root.column cν.row = some g := by
  have hTop := E.top
  have hcr := hTop.lt
  have hVM := build_valid_of_success hTop.build
  have hVR := Classification.Proofs.ChainCorr.NonTop.SeamD.validR E.run
  have hBeq := Classification.Proofs.ChainCorr.boundary_eq hcr hi0
  obtain ⟨loB, usB, hDB⟩ := colData_x0 E (m := i - 1) (by omega)
  obtain ⟨PN, hPN, hPNc⟩ := LowerChainRecon.node_of_cell hcP
  have hPNcol : PN.1.val = M.size - 1 + (M.size - 1 - root.column) * (i - 1) := by
    have := congrArg Ref.column hPN; simp [Frame.ref] at this; omega
  have hcg1 : (1 : Row) ≤ cg.row := Classification.one_le_row hVM hcg hg1
  have hPr : Real PN := CrossUpper.real_of_one_le hVR.toOrdered (by
    change (1 : Row) ≤ ((Frame.ofMountain R).cell PN).row; rw [hPNc]; exact hcP1)
  obtain ⟨hPk, hProw⟩ := node_row hDB hPNcol hPr
  have hProw' : ((loB ++ usB)[PN.2.val - 1]).1.row = official cg.row := by
    have h1 : (Frame.ofMountain R).height PN = cP.row := by
      change ((Frame.ofMountain R).cell PN).row = _; rw [hPNc]
    rw [hProw] at h1
    rw [← hrow, ← h1, JumpLaw.official_stored]
  have hPlo : PN.2.val - 1 < loB.length := lower_of_row hDB hPk (by rw [hProw']; exact hτ)
  have hfe : (loB ++ usB)[PN.2.val - 1] = loB[PN.2.val - 1] := List.getElem_append_left hPlo
  have hfmem : loB[PN.2.val - 1] ∈ loB := List.getElem_mem _
  obtain ⟨⟨_, _, _, _, _⟩, hfup⟩ := LowerPB.lowerT_good hDB.hlo _ hfmem
  obtain ⟨km, cν, hfsrc, hkm1, hcν, _⟩ := LowerPB.lowerT_src hDB.hlo hfmem
  have hfsrc' : ((loB ++ usB)[PN.2.val - 1]).2.src = ⟨M.size - 1, km⟩ := by
    rw [hfe, hfsrc]; rfl
  have hcν' : Reserve.cell? M ((loB ++ usB)[PN.2.val - 1]).2.src = some cν := by
    rw [hfsrc']; exact hcν
  have hcν1 : (1 : Row) ≤ cν.row := LowerPB.cell_row_one_le hVM hcν hkm1
  have hντ : official cν.row < official t.row := by
    obtain ⟨c', hc', hlt'⟩ := Classification.Proofs.ChainCorr.SRParts.lower_src_lt hDB.emitsT hPk
      (by rw [hfe]; exact hfup)
    have : c' = cν := by
      have h2 : Reserve.cell? M ((loB ++ usB)[PN.2.val - 1]).2.src = some c' := by
        simpa [ctxAt] using hc'
      exact Option.some.inj (h2.symm.trans hcν')
    rw [← this]; exact hlt'
  -- the origin row is the root row
  have hRg := rootRow_of_cell (root := root) hcg hg1 hgc
  have H := (ecmp_of_colData hDB _ (List.getElem_mem hPk)) cν hcν' _ hRg
  rw [hProw'] at H
  have hσ : official cν.row = official cg.row := by
    cases hcut : cutOrigin ((loB ++ usB)[PN.2.val - 1]).2
    · obtain ⟨h1, _, h3⟩ := H.1 hcut
      rcases lt_trichotomy (official cg.row) (official cν.row) with hlt | heq | hgt
      · exact absurd (h1 hlt) (lt_irrefl _)
      · exact heq.symm
      · exact absurd (h3 hgt) (lt_irrefl _)
    · obtain ⟨h1, h2⟩ := H.2 hcut
      rcases le_or_gt (official cg.row) (official cν.row) with hle | hlt
      · exact absurd (h1 hle) (lt_irrefl _)
      · exact absurd (h2 hlt) (lt_irrefl _)
  have hνg : cν.row = cg.row :=
    Classification.Proofs.ChainCorr.Inner.Clean.official_inj' hcν1 hcg1 hσ
  refine ⟨loB ++ usB, PN.2.val - 1, hPk, ?_, ?_, cν, hcν', ?_, ?_, ?_, ?_⟩
  · show emitsT _ _ = _
    exact hDB.emitsT
  · have hPr' : 0 < PN.2.val := hPr
    rw [← hPN]; simp only [Frame.ref, hPNcol]; congr 1; omega
  · rw [hfsrc']
  · rw [hfsrc']; exact hkm1
  · exact row_lt_of_official hTop.row_one_le hντ
  · rw [hνg, ← hgc]
    exact Classification.Proofs.ChainCorr.Inner.CleanRoot.hAM_self hVM (by omega) hcg

end Run

/-- **`StepCleanNT` holds.** -/
theorem stepCleanNT : StepCleanNT := by
  intro s n R M t root i x es j hD hi0 hj a ha _ IH k μ hμ hr
  have hin := hD.le_n hi0
  have hD0 := hD
  obtain ⟨hrun, hTop, hx, hes, ⟨cQ, hcQ⟩, _⟩ := hD0
  have hcr := hTop.lt
  have hVM := build_valid_of_success hTop.build
  obtain ⟨hxg, hxl⟩ := mem_blockColumns hcr hx
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi0
  have hXR : x + (M.size - 1 - root.column) * i < R.size := by
    obtain ⟨col, hcol, _⟩ := Classification.Proofs.ChainCorr.cell?_column hcQ
    exact (Array.getElem?_eq_some_iff.mp hcol).1
  have E := CrossUpperSim.env_of hrun hTop hXR (by omega)
  have hva : Classification.Proofs.ChainCorr.NonTop.CopyAtX M R n root.column (M.size - 1)
      (official t.row) i ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ (.clean a false) :=
    ⟨x, es, j, hxg, hxl, hx, rfl, rfl, hes, hj, ha⟩
  have hsrc : es[j].2.src = a := by rw [ha]; rfl
  rw [hsrc] at hr
  -- the source
  obtain ⟨hsc, hs1, ca, hca, _⟩ := emitsT_good hes es[j] (List.getElem_mem hj)
  rw [hsrc] at hsc hs1 hca
  have hup : es[j].2.isUpper = false := by rw [ha]; rfl
  rw [hup] at hsc
  have hac : a.column = x := by simpa [ctxAt] using hsc
  have hne : a ≠ μ := by intro h; rw [← h] at hμ; omega
  obtain ⟨m', hst, hrest⟩ := Classification.Proofs.ChainCorr.SRParts.reach_head hr hne
  have hcp := Classification.Proofs.ChainCorr.NonTop.SeamD.cleanParentReachD hTop hva hst
  obtain ⟨cv, hcv, _, hall⟩ := Classification.Proofs.ChainCorr.NonTop.SeamD.walkXD E hi0
    (by omega) a.column ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ a rfl hva
  have hcvQ : cv = cQ := Option.some.inj (hcv.symm.trans hcQ)
  subst hcvQ
  have hVR := Classification.Proofs.ChainCorr.NonTop.SeamD.validR hrun
  have hcv1 : (1 : Row) ≤ cv.row := Classification.one_le_row hVR hcv (by simp)
  -- the row of `Q`
  obtain ⟨y1, es1, j1, hj1, ho1, ⟨hvc1, hcy1, hyx1, _⟩, hyb1, hvi1, hes1, cv', hcv', hcvrow, _⟩ :=
    Classification.Proofs.ChainCorr.NonTop.SeamD.copyAtX_cellD E hi0 (by omega) hva
  have hy1 : y1 = x := by
    have := Classification.Proofs.ChainCorr.NonTop.blockX_unique (x' := x) (i' := i) hcr hcy1
      hyx1 hx (by rw [← hvc1]) hi0
    exact this.2.symm
  subst y1
  have hee1 : es1 = es := by
    have h2 := hes1
    simp only at h2
    exact Except.ok.inj (h2.symm.trans hes)
  subst es1
  have hjj : j1 = j := by simp at hvi1; omega
  subst j1
  have hcve : cv' = cv := Option.some.inj (hcv'.symm.trans hcv)
  subst cv'
  have hlowτ : official ca.row < official t.row := by
    obtain ⟨c', hc', hlt'⟩ := Classification.Proofs.ChainCorr.SRParts.lower_src_lt hes hj hup
    have h2 : Reserve.cell? M es[j].2.src = some c' := by simpa [ctxAt] using hc'
    rw [hsrc] at h2
    have : c' = ca := Option.some.inj (h2.symm.trans hca)
    rw [← this]; exact hlt'
  -- the boundary node at the row of `Q`
  have hbnd : ∀ g g1, Relation.ReflTransGen (GenStep M root.column) a g →
      g.column = root.column → MStep M k g g1 → ScaleReach M k g1 μ →
      ScaleReach R k ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ μ := by
    intro g g1 hag hgc hgg1 hg1μ
    obtain ⟨_, _, h3⟩ := hall g hag
    obtain ⟨P, cP, hQP, hPc, hcP, hProw⟩ := h3 hgc
    have hga : g ≠ a := by intro h; rw [h] at hgc; omega
    have hag' : Relation.TransGen (GenStep M root.column) a g := by
      rcases Relation.ReflTransGen.cases_head hag with h | ⟨b, hab, hbg⟩
      · exact absurd h.symm hga
      · exact Relation.TransGen.head' hab hbg
    obtain ⟨cg, hcg, hcgrow⟩ :=
      Classification.Proofs.ChainCorr.Inner.Clean.chain_row hag' ca hca
    have hg1 : 1 ≤ g.index := by
      cases hag' with
      | single h => exact h.2.1
      | tail _ h => exact h.2.1
    -- the row of `Q` is the row `C` of `a`
    have hRg := rootRow_of_cell (root := root) hcg hg1 hgc
    obtain ⟨loq, usq, hDq⟩ := colData_block E hi0 hin hx hXR
    have heq : es = loq ++ usq := Except.ok.inj (hes.symm.trans hDq.emitsT)
    have hmemj : es[j] ∈ loq ++ usq := by rw [← heq]; exact List.getElem_mem hj
    have H := (ecmp_of_colData hDq es[j] hmemj) ca (by rw [hsrc]; exact hca) _ hRg
    have hcut : cutOrigin es[j].2 = false := by rw [ha]; rfl
    have hrowj : es[j].1.row = official ca.row := by
      have := (H.1 hcut).2.1 (by rw [hcgrow])
      rw [this, hcgrow]
    have hrowP : official cP.row = official cg.row := by
      rw [hProw, hcvrow, JumpLaw.official_stored, hrowj, hcgrow]
    have hcP1 : (1 : Row) ≤ cP.row := by rw [hProw]; exact hcv1
    obtain ⟨esB, k0, hk0, hesB, hPeq, cν, hcν, hνc, hν1, hνt, hpa⟩ :=
      boundary_lookup E hi0 hin hPc hcP hcP1 hgc hg1 hcg hrowP (by rw [hcgrow]; exact hlowτ)
    have hνg1 := Classification.Proofs.ChainCorr.SRX0.x0Reach s M t root hTop _ cν hνc hν1 hcν
      hνt g hpa k g1 hgg1
    have hO : OrigAt M R n root.column (M.size - 1) (official t.row) P esB[k0].2.src := by
      refine ⟨i - 1, M.size - 1, esB, k0, x0_mem_block' hcr (by omega), by rw [hPeq],
        by rw [hPeq], ?_, ⟨_, hcP⟩, hk0, rfl⟩
      rw [hPeq]
      unfold blockEmits at hesB
      exact hesB
    have hPQ : P.column < (⟨x + (M.size - 1 - root.column) * i, j + 1⟩ : Ref).column := by
      rw [hPc]; simp only; omega
    have hPμ := IH P _ hPQ hO k μ hμ (Classification.Proofs.ChainCorr.ScaleReach.trans hνg1 hg1μ)
    exact Classification.Proofs.ChainCorr.ScaleReach.trans
      (Classification.Proofs.ChainCorr.reach_mono hQP (Nat.zero_le _)) hPμ
  rcases hcp with hA | ⟨g, g1, hag, hgc, hgg1, hg1m'⟩
  · obtain ⟨hcrm, h2, _⟩ := hall m' hA.to_reflTransGen
    rcases Nat.lt_or_eq_of_le hcrm with hlt | heq
    · -- a clean copy of `m'`
      obtain ⟨v', hQv', hv'c⟩ := h2 hlt
      have hm'a := genChain_col_lt hVM hA
      obtain ⟨y2, es2, j2, hj2, ho2, ⟨hvc2, hcy2, hyx2, _⟩, hyb2, hvi2, hes2, cv2, hcv2, _⟩ :=
        Classification.Proofs.ChainCorr.NonTop.SeamD.copyAtX_cellD E hi0 (by omega) hv'c
      have hy2 : y2 = m'.column := by
        obtain ⟨hsc2, _⟩ := emitsT_good hes2 es2[j2] (List.getElem_mem hj2)
        rw [ho2] at hsc2
        simp [ctxAt, Origin.isUpper, Origin.src] at hsc2
        omega
      have hO : OrigAt M R n root.column (M.size - 1) (official t.row) v' m' :=
        ⟨i, y2, es2, j2, hyb2, hvc2, hvi2, hes2, ⟨cv2, hcv2⟩, hj2, by rw [ho2]; rfl⟩
      have hvQ : v'.column < (⟨x + (M.size - 1 - root.column) * i, j + 1⟩ : Ref).column := by
        rw [hvc2]; simp only; omega
      exact Classification.Proofs.ChainCorr.ScaleReach.trans
        (Classification.Proofs.ChainCorr.reach_mono hQv' (Nat.zero_le _))
        (IH v' m' hvQ hO k μ hμ hrest)
    · -- `m'` is the end `(c_r, C)` of the chain
      have hne' : m' ≠ μ := by intro h; rw [← h] at hμ; omega
      obtain ⟨g1, hm'g1, hg1μ⟩ := Classification.Proofs.ChainCorr.SRParts.reach_head hrest hne'
      exact hbnd m' g1 hA.to_reflTransGen heq.symm hm'g1 hg1μ
  · exact hbnd g g1 hag.to_reflTransGen hgc hgg1
      (Classification.Proofs.ChainCorr.ScaleReach.trans hg1m' hrest)

end OmegaY.Official.Recon.TopChain.Seam

#print axioms OmegaY.Official.Recon.TopChain.Seam.stepCleanNT
