/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CrossUpperNRoot.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.TopStartW2NoEnd
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.SCXMain

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# The chain of a non-top copy reaches the node above the root (`NonTopRootHi`, proved)

Notation: `w = x₀ - c_r`, `X_j = c_r + w·j`. A **non-top copy** `Z` of `z`
(`TopStartW2R.NonTopCopy`) is a non-gap copy (`CopyNode`) of a node `z` right of `c_r` in an
inner column of block `i ≥ 1` that is not the top copy of `z`.

`NonTopRootHi`: if the chain of stored parents of `M(s)` from `z` passes a node `c` of `c_r`
whose upper node `c⁺` is at a row `≥ τ`, the chain of `R` from `Z` reaches a node whose upper
node is at the row of `c⁺` in a column `X_j`.

## Proof

* The emit of `Z` is not the top emit of `z`, so it is a clean copy `clean z false`
  (`NonTop.clean_of_not_isTopAt`; the gap flag is false since `z` has a raw parent).
* The walk from a clean copy (`SeamD.walkXD`, proved): the generation chain of `z` ends at a
  node `g` of `c_r` at the row of `z` (`Inner.Clean.chain_row`), and the chain of `R` from `Z`
  reaches (at scale `0`) a node `P` of the column `X_i` at the row of `Z`, which is the row of
  `z` (as in `Pass.pstepCleanNT`).
* `c = g` (`SeamPass.eq_of_row`), so `row P = row c < τ`.
* If `P` is the highest node of `X_i` below `τ`, its upper node has the row of `c⁺`
  (`X_i` is an upper copy of `c_r`, `highestIn_upperCopy_upper`); otherwise `P⁺` is below `τ`
  and the proved `SeamChainX` (`SCX.seamChainX`) gives the chain from `P`.

## Numerical check (timeout 60 s)

Scratch harness `cuq2/nt2.cjs` (from `cuw7.cjs`): the sample files `known-counterexamples`,
`legbelowtop-bad64`, `tsq-counterexamples` with `(1,21,5,20,59,20)`, `(1,4,18,56,18)`
(`n = 1, 2, 3`), and all legal sequences of length `≤ 6` with entries `≤ 8` (`n = 1, 2`):
48 and 231 instances, no failure (all non-top copies are clean copies; `j = 0` in every
instance: the chain passes `c` itself).
-/

namespace OmegaY.Official.Recon.TopChain.Seam.Pass.CUN

open Canonical Expansion Geometry Frame Classification
open CrossUpperSim CrossUpper
open Classification.Proofs.ChainCorr (MStep cutOrigin blockEmits CopyNode)
open Classification.Proofs.ChainCorr.Inner (GenStep)
open Classification.Proofs (ScaleReach)
open Classification.Proofs.ChainCorr.LowerChain (IsTopAt above)
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index
  upper_eq_of_index)
open LowerChainRecon (node_of_cell ref_inj reserve_rawParent_of_frame frame_rawParent_of_reserve)
open Recon.SeamPass (Reach Reach.refl Reach.trans eq_of_row)

/-- **(proved: `nonTopRootHi_holds`).** The chain of `R` from a non-top non-gap copy `Z` of `z`
(right of `c_r`, block `i ≥ 1`) reaches a node whose upper node is at the row of `c⁺` in a column
`c_r + w·j`, for every node `c` of `c_r` on the chain of stored parents of `M(s)` from `z` whose
upper node `c⁺` is at a row `≥ τ`. -/
def NonTopRootHi : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i : Nat),
    Official.expandDiagram s n = .ok R → Top s M t root → 1 ≤ i → i ≤ n →
    ∀ (Z : (Frame.ofMountain R).Node) (z c c' : (Frame.ofMountain M).Node),
      TopStartW2R.NonTopCopy s n R M t root i Z z → RawChain (Frame.ofMountain M) z c →
      c.1.val = root.column → (Frame.ofMountain M).upper c = some c' →
      t.row ≤ (Frame.ofMountain M).height c' →
      ∃ Z' Z'' j, RawChain (Frame.ofMountain R) Z Z' ∧
        (Frame.ofMountain R).upper Z' = some Z'' ∧
        Z''.1.val = root.column + (M.size - 1 - root.column) * j ∧
        (Frame.ofMountain R).height Z'' = (Frame.ofMountain M).height c'

/-- **`NonTopRootHi` holds.** -/
theorem nonTopRootHi_holds : NonTopRootHi := by
  intro s n R M t root i hrun hTop hi1 hin Z z c c' hnt hzc hcc hcu hθ
  obtain ⟨hzg, hzx, hCN, hnTC⟩ := hnt
  obtain ⟨y, es, j, hcy, hyx, hyb, hZc, hZi, hes, hj, hsrc, hcor⟩ := hCN
  have hZc' : Z.1.val = y + (M.size - 1 - root.column) * i := hZc
  have hZi' : Z.2.val = j + 1 := hZi
  have hcr := hTop.lt
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  have hXR : y + (M.size - 1 - root.column) * i < R.size := by rw [← hZc']; exact Z.1.isLt
  have E := env_of hrun hTop hXR (by omega)
  have hG := E.G
  have hF := E.FR
  have hVM := build_valid_of_success hTop.build
  have ht1 := tau_gt_one hTop
  have hi0 : 0 < i := hi1
  -- the emit of `Z` is a clean copy of `z`
  have hesZ : emitsT (ctxAt M R y i root.column (M.size - 1 - root.column) (M.size - 1)
      Z.1.val) (Official.official t.row) = .ok es := hes
  have hes0 : emitsT (ctxAt M R y i root.column (M.size - 1 - root.column) (M.size - 1)
      (y + (M.size - 1 - root.column) * i)) (Official.official t.row) = .ok es := by
    rw [← hZc']; exact hesZ
  have hnIT : ¬ IsTopAt es j := fun hIT =>
    hnTC (RPLRoot.topCopy_of_isTopAt E hi1 hyb hZc' hesZ hZi' hj hsrc hIT)
  have hzne : Frame.ref z ≠ Frame.ref c := by
    intro h
    have := congrArg Ref.column h
    simp only [Frame.ref] at this
    omega
  have hraw : Reserve.rawParent M (Frame.ref z) ≠ none := by
    cases hzc with
    | here => exact absurd rfl hzne
    | step hr _ => rw [reserve_rawParent_of_frame hr]; simp
  have hcut : cutOrigin es[j].2 = false := by
    rcases hcor with h | h
    · exact h
    · exact absurd h hraw
  obtain ⟨a, ha⟩ := Classification.Proofs.ChainCorr.NonTop.clean_of_not_isTopAt
    (ctx := ctxAt M R y i root.column (M.size - 1 - root.column) (M.size - 1)
      (y + (M.size - 1 - root.column) * i)) hVM hes0 hj hcut hnIT
  have haz : a = Frame.ref z := by
    have : es[j].2.src = a := by rw [ha]; rfl
    rw [← this, hsrc]
  subst haz
  have hva : Classification.Proofs.ChainCorr.NonTop.CopyAtX M R n root.column (M.size - 1)
      (official t.row) i (Frame.ref Z) (.clean (Frame.ref z) false) :=
    ⟨y, es, j, hcy, hyx.le, hyb, hZc, hZi, hes, hj, ha⟩
  -- the source
  obtain ⟨hsc, hs1, ca, hca, _⟩ := emitsT_good hes0 es[j] (List.getElem_mem hj)
  rw [hsrc] at hs1 hca
  have hup : es[j].2.isUpper = false := by rw [ha]; rfl
  -- the walk
  obtain ⟨cv, hcv, ⟨g, hag, hgc⟩, hall⟩ := Classification.Proofs.ChainCorr.NonTop.SeamD.walkXD E
    hi0 (by omega) (Frame.ref z).column (Frame.ref Z) (Frame.ref z) rfl hva
  have hVR := Classification.Proofs.ChainCorr.NonTop.SeamD.validR hrun
  have hcv1 : (1 : Row) ≤ cv.row := Classification.one_le_row hVR hcv (by
    simp only [Frame.ref]; omega)
  have hlowτ : official ca.row < official t.row := by
    obtain ⟨c'', hc'', hlt'⟩ := Classification.Proofs.ChainCorr.SRParts.lower_src_lt hes0 hj hup
    have h2 : Reserve.cell? M es[j].2.src = some c'' := by simpa [ctxAt] using hc''
    rw [hsrc] at h2
    have : c'' = ca := Option.some.inj (h2.symm.trans hca)
    rw [← this]; exact hlt'
  obtain ⟨cg, hcg, hcgrow⟩ := Classification.Proofs.ChainCorr.Inner.Clean.chain_row hag ca hca
  obtain ⟨_, _, h3⟩ := hall g hag.to_reflTransGen
  obtain ⟨P, cP, hZP, hPc, hcP, hProw⟩ := h3 hgc
  have hg1 : 1 ≤ g.index := by
    cases hag with
    | single h => exact h.2.1
    | tail _ h => exact h.2.1
  -- the row of `Z` is the row of `z`
  have hRg := rootRow_of_cell (root := root) hcg hg1 hgc
  obtain ⟨loq, usq, hDq⟩ := colData_block E hi0 hin hyb hXR
  have heq : es = loq ++ usq := Except.ok.inj (hes0.symm.trans hDq.emitsT)
  have hmemj : es[j] ∈ loq ++ usq := by rw [← heq]; exact List.getElem_mem hj
  have H := (ecmp_of_colData hDq es[j] hmemj) ca (by rw [hsrc]; exact hca) _ hRg
  have hrowj : es[j].1.row = official ca.row := by
    have := (H.1 hcut).2.1 (by rw [hcgrow])
    rw [this, hcgrow]
  obtain ⟨y1, es1, j1, hj1, _, ⟨hvc1, hcy1, hyx1, _⟩, _, hvi1, hes1, cv', hcv', hcvrow, _⟩ :=
    Classification.Proofs.ChainCorr.NonTop.SeamD.copyAtX_cellD E hi0 (by omega) hva
  have hy1 : y1 = y := by
    have := Classification.Proofs.ChainCorr.NonTop.blockX_unique (x' := y) (i' := i) hcr hcy1
      hyx1 hyb (by rw [← hvc1]; simp only [Frame.ref]; exact hZc') hi0
    exact this.2.symm
  subst y1
  have hee1 : es1 = es := by
    have h2 := hes1
    rw [show (Frame.ref Z).column = y + (M.size - 1 - root.column) * i from hZc'] at h2
    exact Except.ok.inj (h2.symm.trans hes0)
  subst es1
  have hjj : j1 = j := by
    have : (Frame.ref Z).index = j1 + 1 := hvi1
    simp only [Frame.ref] at this
    omega
  subst j1
  have hcve : cv' = cv := Option.some.inj (hcv'.symm.trans hcv)
  subst cv'
  have hrowP : official cP.row = official cg.row := by
    rw [hProw, hcvrow, JumpLaw.official_stored, hrowj, hcgrow]
  have hcP1 : (1 : Row) ≤ cP.row := by rw [hProw]; exact hcv1
  have hcg1 : (1 : Row) ≤ cg.row := by
    have := Classification.one_le_row hVM hcg hg1
    exact this
  have hPg : cP.row = cg.row :=
    Classification.Proofs.ChainCorr.CutParts.official_inj' hcP1 hcg1 hrowP
  -- `c` is `g`
  have hreach : Reach M (Frame.ref z) (Frame.ref c) := TopStartW2R.reach_of_rawChain hG hzc
  have hcg' : Frame.ref c = g := eq_of_row hTop hreach hzne hs1
    (by rw [hgc]; simp only [Frame.ref]; exact hcc.symm) hca hcg hcgrow
  have hcgc : cg = (Frame.ofMountain M).cell c := by
    have := LowerChainRecon.cell?_ref c
    rw [hcg'] at this
    exact Option.some.inj (hcg.symm.trans this)
  subst hcgc
  have hcτ : (Frame.ofMountain M).height c < t.row := by
    show ((Frame.ofMountain M).cell c).row < t.row
    rw [hcgrow]
    by_contra hn
    push Not at hn
    exact absurd (official_mono hTop.row_one_le hn) (not_le.mpr hlowτ)
  -- the node `P`
  obtain ⟨PN, hPN, hPNc⟩ := node_of_cell hcP
  obtain ⟨B, hB, hZB⟩ := LowerChainRecon.rawChain_of_scaleReach hZP Z rfl
  have hBP : B = PN := ref_inj (hB.trans hPN.symm)
  subst hBP
  have hPc' : B.1.val = root.column + (M.size - 1 - root.column) * i := by
    have := congrArg Ref.column hB
    simp only [Frame.ref] at this
    rw [this, hPc]
  have hBh : (Frame.ofMountain R).height B = (Frame.ofMountain M).height c := by
    show ((Frame.ofMountain R).cell B).row = ((Frame.ofMountain M).cell c).row
    rw [hPNc, hPg]
  have hBτ : (Frame.ofMountain R).height B < t.row := by rw [hBh]; exact hcτ
  have hcr' : Real c := real_of_upper_gt hG hcu (lt_of_lt_of_le ht1 hθ)
  have hBr : Real B := by
    unfold Real
    by_contra h0
    have h0' : B.2.val = 0 := by omega
    have hph := hF.phantom B.1 (by have := B.2.isLt; omega)
    have hBe : B = ⟨B.1, ⟨0, by have := B.2.isLt; omega⟩⟩ := node_eq_of_index rfl h0'
    have : (Frame.ofMountain R).height B = 0 := by
      rw [hBe]
      unfold Frame.height Frame.cell
      rw [hph]
      rfl
    have h1 : (1 : Row) ≤ (Frame.ofMountain R).height B := by
      show (1 : Row) ≤ ((Frame.ofMountain R).cell B).row
      rw [hPNc]; exact hcP1
    rw [this] at h1
    exact absurd (lt_of_lt_of_le Row.zero_lt_one h1) (lt_irrefl _)
  have hTc : TopBelow (Frame.ofMountain M) t.row c := topBelow_of_upper hG hcτ hcu hθ
  by_cases hTB : TopBelow (Frame.ofMountain R) t.row B
  · have C0 := upperCopy_root hTop E.CI hF (i := i) (by rw [← hPc']; exact B.1.isLt)
    obtain ⟨B', hBu, hBh'⟩ := highestIn_upperCopy_upper hG hF C0 (P := (· < t.row))
      (fun r r' h1 h2 => lt_of_le_of_lt h1 h2) (fun _ h => h) hcc hPc' hTc hTB hcu hθ
    exact ⟨B, B', i, hZB, hBu, by rw [(upper_spec hBu).1]; exact hPc', hBh'⟩
  · have hex : ∃ v : (Frame.ofMountain R).Node, v.1 = B.1 ∧
        (Frame.ofMountain R).height v < t.row ∧ B.2.val < v.2.val := by
      by_contra hn
      apply hTB
      refine ⟨hBτ, fun v hv hvl => ?_⟩
      by_contra hlt
      exact hn ⟨v, hv, hvl, by omega⟩
    obtain ⟨v, hv, hvl, hvi⟩ := hex
    have hl : (Frame.ofMountain R).length v.1 = (Frame.ofMountain R).length B.1 := by rw [hv]
    have hlen : B.2.val + 1 < (Frame.ofMountain R).length B.1 := by
      have := v.2.isLt
      omega
    let B' : (Frame.ofMountain R).Node := ⟨B.1, ⟨B.2.val + 1, hlen⟩⟩
    have hBu : (Frame.ofMountain R).upper B = some B' := upper_eq_of_index rfl rfl
    have hB'τ : (Frame.ofMountain R).height B' < t.row :=
      lt_of_le_of_lt (height_le_of_index hF hv.symm (by show B.2.val + 1 ≤ v.2.val; omega)) hvl
    obtain ⟨Z', Z'', j', h1, h2, h3, h4⟩ := SCX.seamChainX s n R M t root hrun hTop i hi1 B B' c c'
      hPc' hBr hcc hcτ hcu hθ (le_of_eq hBh.symm) hBu hB'τ
    exact ⟨Z', Z'', j', CrossUpperSim.rawChain_trans hZB h1, h2, h3, h4⟩

end OmegaY.Official.Recon.TopChain.Seam.Pass.CUN

#print axioms OmegaY.Official.Recon.TopChain.Seam.Pass.CUN.nonTopRootHi_holds
