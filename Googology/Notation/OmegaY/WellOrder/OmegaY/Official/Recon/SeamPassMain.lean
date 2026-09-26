/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/SeamPassMain.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.SeamPassSteps

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# `SeamStep` and `SeamStart` from `CutParentNT`

`SeamStep` and `SeamStart` are the open statements of `Recon/RPLRoot.lean` (used there for
`RootPass IsPlain`). Both follow from `PassOK` for every node of a new column
(`SeamPassSteps.lean`), which needs only the open stage-C statement `CutParentNT`
(`Classification/Proofs/SeamCut.lean`, the stored parent of a gap copy that is not the top copy).

* `SeamStep`: the chain of `M(s)` from `z` passes its raw parent `a` (in `c_r`, `a⁺` below `τ`);
  `PassOK` at the top copy `Z` of `z` gives a chain of `R` from `Z` through `a`, and its first
  step is the stored parent `A` of `Z`.
* `SeamStart`: the candidate `pe = Q U` is the lookup node of `B_i` (`startRootLookup`, proved),
  a lower copy of a node `ν` of `x₀` with `hAM(c_r, row ν) = pa`; the chain of `M(s)` from `ν`
  passes `pa` (`x0Pass`), and `PassOK` at `pe` gives the chain of `R` from `pe` through `pa`.

## Results

* `passOK_all : CutParentNT → ∀ Q o, OrigAt Q o → PassOK Q o`
* `seamStep_of_cutParent : CutParentNT → RPLRoot.SeamStep`
* `seamStart_of_cutParent : CutParentNT → RPLRoot.SeamStart`
-/

namespace OmegaY.Official.Recon.TopChain.Seam.Pass

open Canonical Expansion Geometry Frame Classification
open CrossUpperSim CrossUpper
open Classification.Proofs.ChainCorr (MStep cutOrigin blockEmits)
open Classification.Proofs.ChainCorr.Inner (GenStep)
open Classification.Proofs (ScaleReach)
open Classification.Proofs.ChainCorr.LowerChain (TopNode above IsTopAt)
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index
  upper_eq_of_index)
open LowerChainRecon (node_of_cell reserve_rawParent_of_frame frame_rawParent_of_reserve)
open Recon.SeamPass (Reach Reach.refl Reach.trans Reach.old ub_ref ub_below eq_of_row)
open Recon.SeamPass.X0 (x0Pass)

/-! ## `PassOK` everywhere -/

/-- **Every step**, from `CutParentNT`. -/
theorem pstep_all (hCP : CutParentNT) {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell}
    {root : Ref} (hrun : Official.expandDiagram s n = .ok R) (hTop : Recon.Top s M t root) :
    ∀ Q o, OrigAt M R n root.column (M.size - 1) (official t.row) Q o →
      PStepOK R M n t root Q o := by
  intro Q o hQ
  obtain ⟨i, x, es, j, hx, hQc, hQi, hes, hcell, hj, ho⟩ := hQ
  have hQ : Q = ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ := by
    cases Q; simp only at hQc hQi; subst hQc hQi; rfl
  subst hQ ho
  simp only at hes
  have hD : NodeData s n R M t root i x es j := ⟨hrun, hTop, hx, hes, hcell, hj⟩
  have hnontop : 0 < i → ¬ IsTopAt es j →
      PStepOK R M n t root ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ es[j].2.src := by
    intro hi0 hnt
    cases hcut : cutOrigin es[j].2
    · obtain ⟨a, ha⟩ := Classification.Proofs.ChainCorr.NonTop.clean_of_not_isTopAt
        (ctx := ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
          (x + (M.size - 1 - root.column) * i))
        (build_valid_of_success hTop.build) hes hj hcut hnt
      exact pstepCleanNT hD hi0 hj a ha
    · exact pstepCutNT hCP hD hi0 hj hcut hnt
  rcases Nat.eq_zero_or_pos i with hi0 | hi0
  · subst hi0
    exact pstepBlock0 hD hj
  cases hup : es[j].2.isUpper
  · have hcr := hTop.lt
    obtain ⟨_, hxl⟩ := mem_blockColumns hcr hx
    by_cases htop : IsTopAt es j
    · rcases Nat.lt_or_eq_of_le hxl with hlt | heq
      · exact pstepTop hD hi0 hlt hj hup htop
      · subst heq
        exact pstepX0Top hD hi0 hj hup htop
    · exact hnontop hi0 htop
  · exact pstepUpper hD hj hup

/-- **`PassOK` for every node of a new column**, from `CutParentNT`. -/
theorem passOK_all (hCP : CutParentNT) {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell}
    {root : Ref} (hrun : Official.expandDiagram s n = .ok R) (hTop : Recon.Top s M t root) :
    ∀ Q o, OrigAt M R n root.column (M.size - 1) (official t.row) Q o →
      PassOK R M t root Q o :=
  passOK_of_step (pstep_all hCP hrun hTop)

/-! ## Tools -/

/-- A top copy is the top emit of its source. -/
theorem isTopAt_of_topCopy {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (E : Env s n R M t root) {i y : Nat} (hi1 : 1 ≤ i)
    (hyb : y ∈ blockColumns root.column (M.size - 1) n i) {U : (Frame.ofMountain R).Node}
    (hUc : U.1.val = y + (M.size - 1 - root.column) * i) {z : (Frame.ofMountain M).Node}
    (hTC : TopCopy s n R M U z) {es : List (Emit × Origin)}
    (hes : emitsT (ctxAt M R y i root.column (M.size - 1 - root.column) (M.size - 1) U.1.val)
      (official t.row) = .ok es) (hj : U.2.val - 1 < es.length)
    (hsrc : es[U.2.val - 1].2.src = Frame.ref z) : IsTopAt es (U.2.val - 1) := by
  intro j' hj' _ hjj' hsrc'
  rw [hsrc] at hsrc'
  have hU1 := hTC.1.1
  have hlen : j' + 1 < (Frame.ofMountain R).length U.1 := by
    obtain ⟨es2, em2, colX, hes2, hRX, hasm, _⟩ :=
      LowerChainRecon.originAt_unpack2 E.top hyb hUc hTC.1.2.choose_spec.1
    obtain rfl : es2 = es := Except.ok.inj (hes2.symm.trans hes)
    obtain ⟨hsz, _⟩ := Classification.assemble_spec hasm
    have hRU : R[U.1.val]? = some R[U.1.val] := Array.getElem?_eq_getElem U.1.isLt
    rw [hRX] at hRU
    have hcol : colX = R[U.1.val] := Option.some.inj hRU
    change j' + 1 < R[U.1.val].size
    rw [← hcol, hsz, List.length_map]
    omega
  let Z' : (Frame.ofMountain R).Node := ⟨U.1, ⟨j' + 1, hlen⟩⟩
  have hZ'r : Real Z' := by show 0 < j' + 1; omega
  obtain ⟨hj'', ho'⟩ := LowerChainRecon.originAt_of_emits E hi1 hyb (Z := Z') hUc hZ'r hes
  apply hTC.2 Z' rfl (show U.2.val < j' + 1 by omega)
  refine ⟨by show 1 ≤ j' + 1; omega, _, ho', ?_⟩
  simpa [Z'] using hsrc'

/-- `OrigAt` of a copy. -/
theorem origAt_of_isCopy {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (hTop : Recon.Top s M t root) {i y : Nat}
    (hyb : y ∈ blockColumns root.column (M.size - 1) n i) {U : (Frame.ofMountain R).Node}
    (hUc : U.1.val = y + (M.size - 1 - root.column) * i) {z : (Frame.ofMountain M).Node}
    (hC : IsCopy s n R M U z) :
    OrigAt M R n root.column (M.size - 1) (official t.row) (Frame.ref U) (Frame.ref z) := by
  obtain ⟨hU1, o, ho, hsrc⟩ := hC
  obtain ⟨es, em, hes, hjo⟩ := LowerChainRecon.originAt_unpack' hTop hyb hUc ho
  have hjl : U.2.val - 1 < es.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hjo
    cases hjo
  have hej : es[U.2.val - 1] = (em, o) := by
    rw [List.getElem?_eq_getElem hjl] at hjo
    exact Option.some.inj hjo
  refine ⟨i, y, es, U.2.val - 1, hyb, hUc, ?_, ?_, ⟨_, LowerChainRecon.cell?_ref U⟩, hjl, ?_⟩
  · show U.2.val = U.2.val - 1 + 1; omega
  · show emitsT _ _ = _; exact hes
  · rw [hej]; exact hsrc

/-- The chain of `R` from a reference to a reference, as a chain of nodes. -/
theorem rawChain_of_reach {R : Mountain} {A : (Frame.ofMountain R).Node} {q : Ref}
    (h : Reach R (Frame.ref A) q) :
    ∃ c, RawChain (Frame.ofMountain R) A c ∧ c.1.val = q.column ∧ c.2.val = q.index := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨B, hB, hch⟩ := LowerChainRecon.rawChain_of_scaleReach hk A rfl
  refine ⟨B, hch, ?_, ?_⟩
  · rw [← hB]; rfl
  · rw [← hB]; rfl

/-! ## `SeamStep` and `SeamStart` -/

/-- **`SeamStep` from `CutParentNT`.** -/
theorem seamStep_of_cutParent (hCP : CutParentNT) : RPLRoot.SeamStep := by
  intro s n R M t root i hrun hTop hi1 hin Z z a a' hzg hzl hZc hzτ hTC hraw hac hau haτ A hA
  have hcr := hTop.lt
  have hyb : z.1.val ∈ blockColumns root.column (M.size - 1) n i :=
    mem_blockColumns_of_inner (by omega) (by omega) hzg hzl
  have hO := origAt_of_isCopy hTop hyb hZc hTC.1
  have hP := passOK_all hCP hrun hTop _ _ hO
  -- the chain of `M(s)` from `z` passes `a`
  have hza : Reach M (Frame.ref z) (Frame.ref a) := by
    have hr := reserve_rawParent_of_frame hraw
    exact ⟨_, ScaleReach.step hr (LowerChainRecon.cell?_ref z) (LowerChainRecon.cell?_ref a)
      le_rfl (by simp only [Frame.ref]; omega) (ScaleReach.refl _)⟩
  have hca' : Reserve.cell? M (above (Frame.ref a)) = some ((Frame.ofMountain M).cell a') := by
    rw [← LowerChainRecon.above_of_upper hau]; exact LowerChainRecon.cell?_ref a'
  have hRZ := hP (Frame.ref a) hac _ hca' haτ hza
  -- its first step is `A`
  have hne : Frame.ref Z ≠ Frame.ref a := by
    intro h
    have := congrArg Ref.column h
    simp only [Frame.ref] at this
    omega
  obtain ⟨p', k, hst, hrest⟩ := hRZ.head hne
  have hp' : p' = Frame.ref A := Option.some.inj (hst.1.symm.trans (reserve_rawParent_of_frame hA))
  rw [hp'] at hrest
  obtain ⟨c, hc, hc1, hc2⟩ := rawChain_of_reach hrest
  exact ⟨c, hc, hc1, hc2⟩

/-- **`SeamStart` from `CutParentNT`.** -/
theorem seamStart_of_cutParent (hCP : CutParentNT) : RPLRoot.SeamStart := by
  intro s n R M t root i y hrun hTop hi1 hyb U pe z pa pa' hUc hzy hz hzτ hTC hQz hpac hpau hpaτ
    hQU
  have hcr := hTop.lt
  obtain ⟨hyg, hyl⟩ := mem_blockColumns hcr hyb
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ (by omega)
  have E := env_of hrun hTop U.1.isLt (by rw [hUc]; omega)
  have hG := E.G
  have hF := E.FR
  have hin : i ≤ n := block_le E hyg hyl (by rw [← hUc]; exact U.1.isLt) (by rw [← hUc]; omega)
  -- the emits of the column of `U`
  obtain ⟨hU1, o, ho, hsrc⟩ := hTC.1
  obtain ⟨es, em, colX, hes, hRX, hasm, hjo⟩ := LowerChainRecon.originAt_unpack2 hTop hyb hUc ho
  have hjl : U.2.val - 1 < es.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hjo
    cases hjo
  have hej : es[U.2.val - 1] = (em, o) := by
    rw [List.getElem?_eq_getElem hjl] at hjo
    exact Option.some.inj hjo
  have hsrcz : es[U.2.val - 1].2.src = Frame.ref z := by rw [hej]; exact hsrc
  have hIT := isTopAt_of_topCopy E hi1 hyb hUc hTC hes hjl hsrcz
  have hes' : emitsT (ctxAt M R y i root.column (M.size - 1 - root.column) (M.size - 1)
      (y + (M.size - 1 - root.column) * i)) (official t.row) = .ok es := by rw [← hUc]; exact hes
  -- the leg of `z` and the candidates
  obtain ⟨left, hleft, _⟩ := Frame.Q_spec hG hQz
  have hcz : Reserve.cell? M es[U.2.val - 1].2.src = some ((Frame.ofMountain M).cell z) := by
    rw [hsrcz]; exact LowerChainRecon.cell?_ref z
  obtain ⟨cu, ref, hcu, href, hrefc⟩ :=
    LowerChainRecon.leg_image_run hTop hi1 hyb hUc hes hRX hasm hjl hcz hleft
  have hcuU : Reserve.cell? R ⟨U.1.val, U.2.val - 1 + 1⟩ = some ((Frame.ofMountain R).cell U) := by
    have := LowerChainRecon.cell?_ref U
    rwa [show (Frame.ref U : Ref) = ⟨U.1.val, U.2.val - 1 + 1⟩ by
      simp only [Frame.ref]; congr 1; omega] at this
  obtain rfl : cu = (Frame.ofMountain R).cell U := Option.some.inj (hcu.symm.trans hcuU)
  have hUr : Real U := by show 0 < U.2.val; omega
  have hpa := LowerChainRecon.Q_eq_highestAtMost hG hz hQz hleft
  have hpe := LowerChainRecon.Q_eq_highestAtMost hF hUr hQU href
  rw [hrefc] at hpe
  have hlc : (Frame.ref left).column = root.column := by
    obtain ⟨h1, _⟩ := Classification.Proofs.ChainCorr.highestAtMost_spec hpa
    rw [← h1]; exact hpac
  -- the lookup
  obtain ⟨esB, k0, hk0, hesB, hpeq, cν, hcν, hνc, hν1, hνt, hpaν⟩ :=
    startRootLookup s n R M t root i y hrun hTop (by omega) hin hyb es hes' (U.2.val - 1) hjl hIT
      ((Frame.ofMountain R).cell U) ((Frame.ofMountain M).cell z) (Frame.ref left) (Frame.ref pe)
      (Frame.ref pa) (by rw [← hUc]; exact hcuU) hcz hleft hpa hpe hzτ hlc
  have hνpa := x0Pass hTop _ cν hνc hν1 hcν hνt (Frame.ref pa) hpaν
  have hO : OrigAt M R n root.column (M.size - 1) (official t.row) (Frame.ref pe)
      esB[k0].2.src := by
    refine ⟨i - 1, M.size - 1, esB, k0, x0_mem_block' hcr (by omega), by rw [hpeq],
      by rw [hpeq], ?_, ⟨_, LowerChainRecon.cell?_ref pe⟩, hk0, rfl⟩
    rw [hpeq]
    unfold blockEmits at hesB
    exact hesB
  have hca' : Reserve.cell? M (above (Frame.ref pa)) = some ((Frame.ofMountain M).cell pa') := by
    rw [← LowerChainRecon.above_of_upper hpau]; exact LowerChainRecon.cell?_ref pa'
  have hR := passOK_all hCP hrun hTop _ _ hO (Frame.ref pa) hpac _ hca' hpaτ hνpa
  obtain ⟨c, hc, hc1, hc2⟩ := rawChain_of_reach hR
  exact ⟨c, hc, hc1, hc2⟩

end OmegaY.Official.Recon.TopChain.Seam.Pass

#print axioms OmegaY.Official.Recon.TopChain.Seam.Pass.passOK_all
#print axioms OmegaY.Official.Recon.TopChain.Seam.Pass.seamStep_of_cutParent
#print axioms OmegaY.Official.Recon.TopChain.Seam.Pass.seamStart_of_cutParent
