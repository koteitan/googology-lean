/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/SeamStepTop.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.SeamChain

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# The step from a top copy of an inner column (`StepTop`) and from an upper emit (`StepUpper`)

* `topNode_of_isTopAt`: the emit `j` of an inner column of block `i ≥ 1` that is the top copy of
  its source (`IsTopAt`) is a `TopNode`.
* `stepTop : StepTop`: the step from `Z` is the step `Z → A` of `TopStep` (`topStepHi` above `τ`,
  `lo_core` with `lo_left`, `lo_right` below `τ`), and when the stored parent `a` of `z` is in the
  root column, `A` is a node of the boundary column whose origin looks up `a`
  (`stepRootLookup`), so the chain of `A` (induction) reaches the steps of `a` (`SRX0.x0Reach`).
* `stepUpper : StepUpper`: for an inner column by `topNode_upper` and `topStepHi`; for the copy of
  `x₀` (its upper part copies the root column) by `stand_of_highest` in block `i + 1`.
-/

namespace OmegaY.Official.Recon.TopChain.Seam

open Canonical Expansion Geometry Frame Classification
open CrossUpperSim CrossUpper
open Classification.Proofs.ChainCorr (MStep cutOrigin blockEmits)
open Classification.Proofs (ScaleReach)
open Classification.Proofs.ChainCorr.LowerChain (CopyOf TopNode Stand TopStep TopStart above
  IsTopAt)
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index)
open LowerChainRecon (node_of_cell ref_inj reserve_rawParent_of_frame frame_rawParent_of_reserve)

/-! ## Tools -/

/-- One step of `R` in front of a chain. -/
theorem reach_cons {R : Mountain} {k kz : Nat} {Q A μ : Ref} (hst : MStep R kz Q A) (hk : kz ≤ k)
    (h : ScaleReach R k A μ) : ScaleReach R k Q μ := by
  obtain ⟨hpar, c, cq, hc, hcq, hj, hlt⟩ := hst
  exact ScaleReach.step hpar hc hcq (le_trans hj hk) hlt h

/-- A chain of `M` left of `x₀` is a chain of `R`. -/
theorem reach_old {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (hrun : Official.expandDiagram s n = .ok R) (hTop : Recon.Top s M t root) {k : Nat}
    {p q : Ref} (h : ScaleReach M k p q) (hp : p.column < M.size - 1) : ScaleReach R k p q := by
  obtain ⟨M', hM', _, hI, _⟩ := run_basic hrun
  obtain rfl : M = M' := Except.ok.inj (hTop.build.symm.trans hM')
  exact Classification.Proofs.ChainCorr.SRParts.reach_transfer (fun c hc => (hI.2.1 c hc).symm)
    h hp

/-- The `OrigAt` of a `TopNode`, with a cell. -/
theorem origAt_of_topNode {M R : Mountain} {n cr x0 : Nat} {τ θ : Row} {i : Nat} {A a : Ref}
    (h : TopNode M R n cr x0 τ θ i A a) (hc : ∃ c, Reserve.cell? R A = some c) :
    OrigAt M R n cr x0 τ A a := by
  obtain ⟨⟨y, es, j, _, _, hyb, hv, hidx, hes, hj, hsrc⟩, _, _⟩ := h
  exact ⟨i, y, es, j, hyb, hv, hidx, hes, hc, hj, hsrc⟩

/-- **A top copy of an inner column is a `TopNode`.** -/
theorem topNode_of_isTopAt {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    {i x : Nat} {es : List (Emit × Origin)} {j : Nat}
    (hD : NodeData s n R M t root i x es j) (hi0 : 0 < i) (hxl : x < M.size - 1)
    (hj : j < es.length) (htop : IsTopAt es j) :
    TopNode M R n root.column (M.size - 1) (official t.row) t.row i
      ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ es[j].2.src := by
  obtain ⟨hrun, hTop, hx, hes, ⟨cQ, hcQ⟩, _⟩ := hD
  have hcr := hTop.lt
  obtain ⟨hxg, _⟩ := mem_blockColumns hcr hx
  have hVM := build_valid_of_success hTop.build
  refine ⟨⟨x, es, j, hxg, hxl, hx, rfl, rfl, hes, hj, rfl⟩, ?_, ?_⟩
  · rintro v' hv'c hv'i _ ⟨y', es', j', _, _, _, hv', hidx', hes', hj', hsrc'⟩
    have hy : y' = x := by
      have : v'.column = x + (M.size - 1 - root.column) * i := hv'c
      omega
    subst hy
    rw [hv'c] at hes'
    have hee : es' = es := Except.ok.inj (hes'.symm.trans hes)
    subst hee
    have hjj : j < j' := by simp only at hv'i; omega
    exact htop j' hj' hj hjj hsrc'
  · intro cm cv hcm hcv hθ
    obtain ⟨_, hsrc1, _⟩ := emitsT_good hes es[j] (List.getElem_mem hj)
    have hcm1 : (1 : Row) ≤ cm.row := Classification.one_le_row hVM hcm hsrc1
    cases hup : es[j].2.isUpper
    · exfalso
      obtain ⟨c', hc', hlt'⟩ := Classification.Proofs.ChainCorr.SRParts.lower_src_lt hes hj hup
      have hc'' : Reserve.cell? M es[j].2.src = some c' := by simpa [ctxAt] using hc'
      have hcc : c' = cm := Option.some.inj (hc''.symm.trans hcm)
      subst hcc
      exact absurd (official_mono hTop.row_one_le hθ) (not_le.mpr hlt')
    · -- an upper emit keeps the row of its source
      have hXR : x + (M.size - 1 - root.column) * i < R.size := by
        obtain ⟨col, hcol, _⟩ := Classification.Proofs.ChainCorr.cell?_column hcQ
        exact (Array.getElem?_eq_some_iff.mp hcol).1
      have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
        Nat.le_mul_of_pos_right _ hi0
      have E := CrossUpperSim.env_of hrun hTop hXR (by omega)
      have hin : i ≤ n := by
        by_contra hn
        have hn0 : n ≠ 0 := by
          intro h0
          subst h0
          have hRs : R.size = M.size - 1 := by
            obtain ⟨M', hM', hcases⟩ := Reconstruction.expandDiagram_cases hrun
            obtain rfl : M' = M := Except.ok.inj (hM'.symm.trans hTop.build)
            rcases hcases with ⟨_, rfl⟩ | ⟨_, _, _, _, _, ⟨_, rfl⟩ | ⟨_, h0, _⟩⟩
            · omega
            · simp
            · exact absurd rfl h0
          omega
        have hRs := Proofs.CopyShape.Found.run_size hrun hTop hn0
        have h1 : (M.size - 1 - root.column) * (n + 1) ≤ (M.size - 1 - root.column) * i :=
          Nat.mul_le_mul_left _ (by omega)
        rw [Nat.mul_succ] at h1
        have h2 : n * (M.size - 1 - root.column) = (M.size - 1 - root.column) * n := Nat.mul_comm _ _
        omega
      obtain ⟨lo, us, hDc⟩ := colData_block E hi0 hin hx hXR
      have hee : es = lo ++ us := Except.ok.inj (hes.symm.trans hDc.emitsT)
      subst hee
      have hjus : lo.length ≤ j := by
        by_contra hn
        have hjl : j < lo.length := by omega
        have := ((LowerPB.lowerT_good hDc.hlo) _ (List.getElem_mem hjl)).2
        have hE : (lo ++ us)[j] = lo[j] := List.getElem_append_left hjl
        rw [← hE, hup] at this
        cases this
      have hmem : (lo ++ us)[j] ∈ us := by
        rw [List.getElem_append_right hjus]; exact List.getElem_mem _
      obtain ⟨k2, c2, _, hc2, hup2, hrow2, _, _⟩ := (LowerPB.upperT_spec hDc.hus).1 _ hmem
      have hs2 : ((lo ++ us)[j]).2.src = ⟨upperColumn (ctxAt M R x i root.column
          (M.size - 1 - root.column) (M.size - 1) (x + (M.size - 1 - root.column) * i)), k2⟩ := by
        rw [hup2]; rfl
      rw [hs2] at hcm
      have hc2' : Reserve.cell? M ⟨upperColumn (ctxAt M R x i root.column
          (M.size - 1 - root.column) (M.size - 1) (x + (M.size - 1 - root.column) * i)), k2⟩ =
          some c2 := by simpa [ctxAt] using hc2
      have hcc : c2 = cm := Option.some.inj (hc2'.symm.trans hcm)
      subst hcc
      -- the cell of the node
      have hk : j + 1 < (R[x + (M.size - 1 - root.column) * i]'hXR).size := by
        rw [hDc.size]; omega
      obtain ⟨_, hrowQ, _⟩ := hDc.node hk (by omega)
      have hcv' : cv = (R[x + (M.size - 1 - root.column) * i]'hXR)[j + 1] := by
        have : Reserve.cell? R ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ =
            some ((R[x + (M.size - 1 - root.column) * i]'hXR)[j + 1]) := by
          simp only [Reserve.cell?, Array.getElem?_eq_getElem hXR, Option.bind_eq_bind,
            Option.bind_some]
          exact Array.getElem?_eq_getElem hk
        exact Option.some.inj (hcv.symm.trans this)
      rw [hcv', hrowQ]
      simp only [Nat.add_sub_cancel]
      rw [hrow2]
      exact Classification.stored_official hcm1

theorem x0_mem_block' {cr x0 n m : Nat} (hcr : cr < x0) (hm : m < n) :
    x0 ∈ blockColumns cr x0 n m := by
  unfold blockColumns
  split
  · simp
  · simp only [List.mem_range'_1]
    omega

/-- The block of a node of a new column is at most `n`. -/
theorem NodeData.le_n {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    {i x : Nat} {es : List (Emit × Origin)} {j : Nat}
    (hD : NodeData s n R M t root i x es j) (hi0 : 0 < i) : i ≤ n := by
  obtain ⟨hrun, hTop, hx, _, ⟨cQ, hcQ⟩, _⟩ := hD
  have hcr := hTop.lt
  obtain ⟨hxg, _⟩ := mem_blockColumns hcr hx
  have hXR : x + (M.size - 1 - root.column) * i < R.size := by
    obtain ⟨col, hcol, _⟩ := Classification.Proofs.ChainCorr.cell?_column hcQ
    exact (Array.getElem?_eq_some_iff.mp hcol).1
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi0
  by_contra hn
  have hn0 : n ≠ 0 := by
    intro h0
    subst h0
    have hRs : R.size = M.size - 1 := by
      obtain ⟨M', hM', hcases⟩ := Reconstruction.expandDiagram_cases hrun
      obtain rfl : M' = M := Except.ok.inj (hM'.symm.trans hTop.build)
      rcases hcases with ⟨_, rfl⟩ | ⟨_, _, _, _, _, ⟨_, rfl⟩ | ⟨_, h0, _⟩⟩
      · omega
      · simp
      · exact absurd rfl h0
    omega
  have hRs := Proofs.CopyShape.Found.run_size hrun hTop hn0
  have h1 : (M.size - 1 - root.column) * (n + 1) ≤ (M.size - 1 - root.column) * i :=
    Nat.mul_le_mul_left _ (by omega)
  rw [Nat.mul_succ] at h1
  have h2 : n * (M.size - 1 - root.column) = (M.size - 1 - root.column) * n := Nat.mul_comm _ _
  omega

/-- The chain of a stand-in reaches what the chain of `a` reaches left of `c_r`. -/
theorem reach_of_stand {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (hrun : Official.expandDiagram s n = .ok R) (hTop : Recon.Top s M t root) {i : Nat}
    {Q A a μ : Ref} {k : Nat}
    (IH : ∀ Q' o', Q'.column < Q.column →
      OrigAt M R n root.column (M.size - 1) (official t.row) Q' o' →
      ChainOK R M root.column Q' o')
    (hA : Stand M R n root.column (M.size - 1) (official t.row) t.row i A a)
    (hAc : ∃ c, Reserve.cell? R A = some c) (hAQ : A.column < Q.column)
    (hμ : μ.column < root.column) (har : ScaleReach M k a μ) : ScaleReach R k A μ := by
  have hcr := hTop.lt
  rcases Nat.lt_trichotomy a.column root.column with hl | he | hg
  · rw [hA.1 hl]
    exact reach_old hrun hTop har (by omega)
  · have hne : a ≠ μ := by intro h; subst h; omega
    obtain ⟨b, hab, hbμ⟩ := Classification.Proofs.ChainCorr.SRParts.reach_head har hne
    obtain ⟨hraw, ca, cb, hca, hcb, hj, hlt⟩ := hab
    have h1 := (hA.2.1 he).2.2 b ca cb hraw hca hcb
    exact Classification.Proofs.ChainCorr.ScaleReach.trans (Classification.Proofs.ChainCorr.reach_mono h1 hj)
      (reach_old hrun hTop hbμ (by omega))
  · exact IH A a hAQ (origAt_of_topNode (hA.2.2 hg) hAc) k μ hμ har

/-- **`StepTop` holds.** -/
theorem stepTop : StepTop := by
  intro s n R M t root i x es j hD hi0 hxl hj hup htop IH k μ hμ hr
  have hin := hD.le_n hi0
  have hTN := topNode_of_isTopAt hD hi0 hxl hj htop
  obtain ⟨hrun, hTop, hx, hes, _, _⟩ := hD
  have hcr := hTop.lt
  obtain ⟨hxg, _⟩ := mem_blockColumns hcr hx
  have hzc : es[j].2.src.column = x := by
    obtain ⟨h1, _⟩ := emitsT_good hes es[j] (List.getElem_mem hj)
    rw [hup] at h1; simpa [ctxAt] using h1
  have hne : es[j].2.src ≠ μ := by intro h; rw [← h] at hμ; omega
  obtain ⟨a, hza, har⟩ := Classification.Proofs.ChainCorr.SRParts.reach_head hr hne
  obtain ⟨hraw, cz, ca, hcz, hca, hjz, _⟩ := hza
  by_cases hθ : ∃ c', Reserve.cell? M (above es[j].2.src) = some c' ∧ t.row ≤ c'.row
  · obtain ⟨A, hst, hstand⟩ := topStepHi hrun hTop hi0 hin hTN hraw hcz hca hθ
    have hAc : ∃ c, Reserve.cell? R A = some c := by
      obtain ⟨_, _, cA, _, hcA, _, _⟩ := hst; exact ⟨cA, hcA⟩
    exact reach_cons hst hjz (reach_of_stand hrun hTop IH hstand hAc hst.column_lt hμ har)
  have hlo : ∀ c', Reserve.cell? M (above es[j].2.src) = some c' → c'.row < t.row := by
    intro c' hc'
    by_contra hn
    exact hθ ⟨c', hc', le_of_not_gt hn⟩
  obtain ⟨ZN, VN, A, zN, z'N, aN, lo, us, jz, hZ, hz, ha, C⟩ :=
    lo_core hrun hTop hi0 hin hTN hraw hcz hca hlo
  have hAraw : Reserve.rawParent R ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ =
      some (Frame.ref A) := by
    rw [← hZ]; exact reserve_rawParent_of_frame C.Araw
  have hcZ : Reserve.cell? R ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ =
      some ((Frame.ofMountain R).cell ZN) := by
    rw [← hZ]; exact LowerChainRecon.cell?_ref ZN
  have hcA := LowerChainRecon.cell?_ref A
  have hlt : (Frame.ref A).column < (⟨x + (M.size - 1 - root.column) * i, j + 1⟩ : Ref).column := by
    rw [← hZ]; exact rawParent_column_lt C.E.FR C.Araw
  have hst : MStep R (Row.jump cz.row ca.row) ⟨x + (M.size - 1 - root.column) * i, j + 1⟩
      (Frame.ref A) :=
    ⟨hAraw, _, _, hcZ, hcA, topStepLoJumpAll s n R M t root i hrun hTop hi0 hin _ _ hTN a cz ca
      hraw hcz hca hlo _ _ _ hAraw hcZ hcA, hlt⟩
  refine reach_cons hst hjz ?_
  rcases Nat.lt_trichotomy aN.1.val root.column with hl | he | hg
  · obtain ⟨hAa, _⟩ := lo_left C hl
    rw [hAa, ha]
    exact reach_old hrun hTop har (by rw [← ha]; simp only [Frame.ref]; omega)
  · -- the root column: the lookup, `X0Reach` and the induction at `A`
    have he' : a.column = root.column := by rw [← ha]; exact he
    obtain ⟨esB, k0, hk0, hesB, hAeq, cν, hcν, hνc, hν1, hνt, hpa⟩ :=
      stepRootLookup s n R M t root i hrun hTop hi0 hin _ _ hTN a cz ca hraw hcz hca hlo he' _
        hAraw
    have hne' : a ≠ μ := by intro h; rw [← h] at hμ; omega
    obtain ⟨b, hab, hbμ⟩ := Classification.Proofs.ChainCorr.SRParts.reach_head har hne'
    have hνb := Classification.Proofs.ChainCorr.SRX0.x0Reach s M t root hTop _ cν hνc hν1 hcν hνt
      a hpa k b hab
    have hO : OrigAt M R n root.column (M.size - 1) (official t.row) (Frame.ref A)
        esB[k0].2.src := by
      refine ⟨i - 1, M.size - 1, esB, k0, x0_mem_block'
        hcr (by omega), by rw [hAeq], by rw [hAeq], ?_, ⟨_, hcA⟩, hk0, rfl⟩
      rw [hAeq]
      unfold blockEmits at hesB
      exact hesB
    exact IH _ _ hlt hO k μ hμ (Classification.Proofs.ChainCorr.ScaleReach.trans hνb hbμ)
  · have hTA := lo_right C hg
    rw [ha] at hTA
    exact IH _ _ hlt (origAt_of_topNode hTA ⟨_, hcA⟩) k μ hμ har

end OmegaY.Official.Recon.TopChain.Seam

#print axioms OmegaY.Official.Recon.TopChain.Seam.topNode_of_isTopAt
#print axioms OmegaY.Official.Recon.TopChain.Seam.stepTop
