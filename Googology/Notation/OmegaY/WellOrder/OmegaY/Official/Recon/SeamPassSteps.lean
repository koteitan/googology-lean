/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/SeamPassSteps.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.SeamPassBase
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.SeamX0
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.SeamCleanStep

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# The steps of `PassOK` (the chain of a copy passes a node of the root column)

With the notation of `SeamPassBase.lean`: `PassOK Q o` says that the chain of stored parents of
`R` from `Q` passes every node `μ` of `c_r` (with `μ⁺` below `τ`) that the chain of `M(s)` from
the origin `o` passes. As for `Seam.ChainOK` the proof is a strong induction on the column
(`passOK_of_step`), with one step for each kind of node:

* upper emits (any block) and lower emits whose origin has its upper node at or above `τ`:
  vacuous (`not_reach_high`, `ub_below`: the chain of an origin that passes `μ` stays below
  `μ⁺ < τ`);
* block `0`: the stored parent of the copy of `ν` is the raw parent of `ν` (the proof of
  `Seam.stepBlock0`);
* a lower top copy of an inner column, or of the copy of `x₀`: `lo_core` / `lo_coreX`; a stored
  parent right of `c_r` is a top copy (`lo_right`, `lo_rightX`), one in `c_r` is `μ` itself and
  its stand-in is the lookup node of `B_i` (`stepRootLookup`, `stepRootLookupX`), whose origin
  `ν` passes `μ` (`x0Pass`);
* a clean copy (`b = 0`) that is not the top copy: the walk `walkXD` to the boundary node at the
  row of the copy, the lookup `boundary_lookup` and `x0Pass`; `μ` is the end of the generation
  chain (`eq_of_row`);
* a gap copy that is not the top copy: `CutParentNT` (open, stage C), the lookup
  `cut_bnd_lookup` and `x0Pass`, along the generation chain (`cutPass`).
-/

namespace OmegaY.Official.Recon.TopChain.Seam.Pass

open Canonical Expansion Geometry Frame Classification
open CrossUpperSim CrossUpper
open Classification.Proofs.ChainCorr (MStep cutOrigin blockEmits)
open Classification.Proofs.ChainCorr.Inner (GenStep)
open Classification.Proofs (ScaleReach)
open Classification.Proofs.ChainCorr.LowerChain (CopyOf TopNode Stand TopStep TopStart above
  IsTopAt)
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index
  upper_eq_of_index)
open LowerChainRecon (node_of_cell ref_inj reserve_rawParent_of_frame frame_rawParent_of_reserve)
open Recon.SeamPass (Reach Reach.refl Reach.trans Reach.old ub_ref ub_below eq_of_row)
open Recon.SeamPass.X0 (x0Pass)

/-! ## The statement and the induction -/

/-- The chain of `R` from `Q` passes every node `μ` of `c_r` with `μ⁺` below `τ` that the chain
of `M(s)` from `o` passes. -/
def PassOK (R M : Mountain) (t : Cell) (root : Ref) (Q o : Ref) : Prop :=
  ∀ μ : Ref, μ.column = root.column → ∀ cμ', Reserve.cell? M (above μ) = some cμ' →
    cμ'.row < t.row → Reach M o μ → Reach R Q μ

/-- `PassOK` at `Q` from `PassOK` at the nodes of the columns left of `Q`. -/
def PStepOK (R M : Mountain) (n : Nat) (t : Cell) (root : Ref) (Q o : Ref) : Prop :=
  (∀ Q' o', Q'.column < Q.column →
    OrigAt M R n root.column (M.size - 1) (official t.row) Q' o' →
    PassOK R M t root Q' o') → PassOK R M t root Q o

/-- **`PassOK` for every node of a new column**, from the steps. -/
theorem passOK_of_step {R M : Mountain} {n : Nat} {t : Cell} {root : Ref}
    (hstep : ∀ Q o, OrigAt M R n root.column (M.size - 1) (official t.row) Q o →
      PStepOK R M n t root Q o) :
    ∀ Q o, OrigAt M R n root.column (M.size - 1) (official t.row) Q o →
      PassOK R M t root Q o := by
  intro Q
  induction h : Q.column using Nat.strong_induction_on generalizing Q with
  | _ X ih =>
    intro o hQ
    apply hstep Q o hQ
    intro Q' o' hlt hQ'
    exact ih Q'.column (by omega) Q' rfl o' hQ'

/-! ## Vacuous cases -/

/-- The chain of an origin at or above `τ` does not pass a node `μ` of `c_r` with `μ⁺` below
`τ`. -/
theorem not_reach_high {s : List Nat} {M : Mountain} {t : Cell} {root : Ref}
    (hTop : Recon.Top s M t root) {o μ : Ref} (hr : Reach M o μ) (ho1 : 1 ≤ o.index) {co : Cell}
    (hco : Reserve.cell? M o = some co) (hτ : t.row ≤ co.row) {cμ' : Cell}
    (hcμ' : Reserve.cell? M (above μ) = some cμ') (hμτ : cμ'.row < t.row) : False := by
  have hV : MountainValid M := build_valid_of_success hTop.build
  by_cases hne : o = μ
  · subst hne
    have h1 : Reserve.cell? M ⟨o.column, o.index⟩ = some co := hco
    have h2 : Reserve.cell? M ⟨o.column, o.index + 1⟩ = some cμ' := hcμ'
    have := Classification.Proofs.ChainCorr.cell_row_lt hV h1 h2 (by omega)
    exact absurd (lt_of_le_of_lt hτ (lt_trans this hμτ)) (lt_irrefl _)
  · obtain ⟨co2, _, hco2, _, hlt, _⟩ := ub_below hTop hr hne ho1 hcμ' hμτ
    obtain rfl : co2 = co := Option.some.inj (hco2.symm.trans hco)
    exact absurd (lt_of_le_of_lt hτ hlt) (lt_irrefl _)

/-- The step for an upper emit (any block): vacuous. -/
theorem pstepUpper {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} {i x : Nat}
    {es : List (Emit × Origin)} {j : Nat} (hD : NodeData s n R M t root i x es j)
    (hj : j < es.length) (hup : es[j].2.isUpper = true) :
    PStepOK R M n t root ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ es[j].2.src := by
  intro _ μ _ cμ' hcμ' hμτ hr
  obtain ⟨_, csrc, _, hcs, _, hτs, _, hs1, _⟩ := upper_data hD hj hup
  exact (not_reach_high hD.2.1 hr hs1 hcs hτs hcμ' hμτ).elim

/-! ## Block `0` -/

/-- **The step in block `0`.** -/
theorem pstepBlock0 {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} {x : Nat}
    {es : List (Emit × Origin)} {j : Nat} (hD : NodeData s n R M t root 0 x es j)
    (hj : j < es.length) :
    PStepOK R M n t root ⟨x + (M.size - 1 - root.column) * 0, j + 1⟩ es[j].2.src := by
  intro _ μ hμc cμ' hcμ' hμτ hr
  obtain ⟨E, lo, us, hDc, hee⟩ := colData_of_node hD
  have hD' := hD
  obtain ⟨hrun, hTop, hx, hes, ⟨cQ, hcQ⟩, _⟩ := hD'
  have hcr := hTop.lt
  have hVM := build_valid_of_success hTop.build
  have hG := E.G
  have hF := E.FR
  have hx0 : x = M.size - 1 := by simpa [blockColumns] using hx
  subst hx0
  have hXR := hDc.XR
  have hn1 : 1 ≤ n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    subst hn0
    have hRs : R.size = M.size - 1 := by
      obtain ⟨M', hM', hcases⟩ := Reconstruction.expandDiagram_cases hrun
      obtain rfl : M' = M := Except.ok.inj (hM'.symm.trans hTop.build)
      rcases hcases with ⟨hs, rfl⟩ | ⟨_, _, _, _, _, ⟨_, rfl⟩ | ⟨_, h0, _⟩⟩
      · subst hs
        have hb := hTop.build
        have h' : Canonical.build ([] : List Nat) = .ok #[] := rfl
        rw [h'] at hb
        have hM0 := Except.ok.inj hb
        have := hTop.lt
        rw [← hM0] at this
        simp at this
      · simp
      · exact absurd rfl h0
    simp only [Nat.mul_zero, Nat.add_zero] at hXR
    omega
  -- the frame node of `Q`
  obtain ⟨QN, hQN, hQNc⟩ := node_of_cell hcQ
  have hQNcol : QN.1.val = M.size - 1 + (M.size - 1 - root.column) * 0 := by
    have := congrArg Ref.column hQN; simpa [Frame.ref] using this
  have hQNi : QN.2.val = j + 1 := by
    have := congrArg Ref.index hQN; simpa [Frame.ref] using this
  have hQr : Real QN := by show 0 < QN.2.val; omega
  -- the source and its first step
  subst hee
  cases hup : (lo ++ us)[j].2.isUpper
  · -- a lower emit
    have hjl : j < lo.length := by
      by_contra hn
      have hmem : (lo ++ us)[j] ∈ us := by
        rw [List.getElem_append_right (by omega)]; exact List.getElem_mem _
      obtain ⟨_, _, _, _, hup2, _, _, _⟩ := (LowerPB.upperT_spec hDc.hus).1 _ hmem
      rw [hup2] at hup
      cases hup
    have hEj : (lo ++ us)[j] = lo[j] := List.getElem_append_left hjl
    obtain ⟨kν, cν, hsrc, hkν1, hcν, _⟩ := LowerPB.lowerT_src hDc.hlo (List.getElem_mem hjl)
    have hsrc' : (lo ++ us)[j].2.src = ⟨M.size - 1, kν⟩ := by rw [hEj, hsrc]; simp [ctxAt]
    have hcν' : Reserve.cell? M ⟨M.size - 1, kν⟩ = some cν := by simpa [ctxAt] using hcν
    have hrowν := hDc.block0_row rfl (List.getElem_mem hjl) (by rw [hsrc]; simpa [ctxAt] using hcν)
    rw [hsrc'] at hr
    have hne : (⟨M.size - 1, kν⟩ : Ref) ≠ μ := by intro h; rw [← h] at hμc; simp at hμc; omega
    obtain ⟨a, k1, hνa, har⟩ := hr.head hne
    have hac : a.column < M.size - 1 := by have := hνa.column_lt; simpa using this
    obtain ⟨hraw, cν2, ca, hcν2, hca, hjk, _⟩ := hνa
    have hcνe : cν2 = cν := Option.some.inj (hcν2.symm.trans hcν')
    rw [hcνe] at hjk
    obtain ⟨cp, hcp, hcpl⟩ := Classification.Proofs.ChainCorr.Inner.rawParent_eq_some.mp hraw
    have hcp' : Reserve.cell? M ⟨M.size - 1, kν + 1⟩ = some cp := hcp
    have hcν1 : (1 : Row) ≤ cν.row := Classification.one_le_row hVM hcν' hkν1
    have hνp : cν.row < cp.row := Classification.Proofs.ChainCorr.cell_row_lt hVM hcν' hcp' (by omega)
    -- the cell of `Q` has the row of `ν`
    have hQrow : cQ.row = cν.row := by
      have hk : j + 1 < (R[M.size - 1 + (M.size - 1 - root.column) * 0]'hXR).size := by
        rw [hDc.size]; omega
      obtain ⟨_, hrowQ, _⟩ := hDc.node hk (by omega)
      have : cQ = (R[M.size - 1 + (M.size - 1 - root.column) * 0]'hXR)[j + 1] := by
        have h2 : Reserve.cell? R ⟨M.size - 1 + (M.size - 1 - root.column) * 0, j + 1⟩ =
            some ((R[M.size - 1 + (M.size - 1 - root.column) * 0]'hXR)[j + 1]) := by
          simp only [Reserve.cell?, Array.getElem?_eq_getElem hXR, Option.bind_eq_bind,
            Option.bind_some]
          exact Array.getElem?_eq_getElem hk
        exact Option.some.inj (hcQ.symm.trans h2)
      rw [this, hrowQ]
      simp only [Nat.add_sub_cancel]
      rw [hEj, ← hrowν]
      exact Classification.stored_official hcν1
    -- the frame nodes of `ν`, `ν⁺`, `a`
    obtain ⟨νN, hνN, hνNc⟩ := node_of_cell hcν'
    obtain ⟨pN, hpN, hpNc⟩ := node_of_cell hcp'
    obtain ⟨aN, haN, haNc⟩ := node_of_cell hca
    have hνN1 : νN.1.val = M.size - 1 := by
      have := congrArg Ref.column hνN; simpa [Frame.ref] using this
    have hpN1 : pN.1 = νN.1 := Fin.ext (by
      have := congrArg Ref.column hpN; simp [Frame.ref] at this; omega)
    have hνNi : νN.2.val = kν := by have := congrArg Ref.index hνN; simpa [Frame.ref] using this
    have hpNi : pN.2.val = kν + 1 := by
      have := congrArg Ref.index hpN; simpa [Frame.ref] using this
    have hνr : Real νN := by show 0 < νN.2.val; omega
    have hνu : (Frame.ofMountain M).upper νN = some pN := upper_eq_of_index hpN1.symm (by omega)
    have hraw' : (Frame.ofMountain M).rawParent νN = some aN :=
      rawParent_eq_of_upper_left hνu (by rw [hpNc, haN]; exact hcpl)
    have haH : HighestIn (Frame.ofMountain M) (· < (Frame.ofMountain M).height pN) aN :=
      highestIn_of_hb (hbAt_of_normal E.NM hνr) hνu hraw'
    by_cases hcase : cp.row < t.row
    · -- `ν⁺` is below `τ`: the next emit is its copy
      have hτp : official cp.row < official t.row :=
        official_strictMono (le_trans hcν1 hνp.le) hcase
      obtain ⟨f, hf, hfsrc⟩ := hDc.emitted0 rfl (show 1 ≤ kν + 1 by omega) (by simpa using hcp')
        hτp
      obtain ⟨m, hm, hme⟩ := List.getElem_of_mem hf
      have hrowf := hDc.block0_row rfl hf (by rw [hfsrc]; simpa [ctxAt] using hcp')
      have hsorted := hDc.sorted
      have hrowlt : ∀ a b (ha : a < lo.length) (hb : b < lo.length), a < b →
          lo[a].1.row < lo[b].1.row := by
        intro a b ha hb hab
        have := List.pairwise_iff_getElem.mp hsorted a b (by simp; omega) (by simp; omega) hab
        simp only [List.getElem_map] at this
        rwa [List.getElem_append_left ha, List.getElem_append_left hb] at this
      have hoff : official cν.row < official cp.row := official_strictMono hcν1 hνp
      have hjm : j < m := by
        by_contra hn
        rcases Nat.lt_or_eq_of_le (not_lt.mp hn) with hlt | heq
        · have := hrowlt m j hm hjl hlt
          rw [hme, ← hrowf, ← hrowν] at this
          exact absurd (lt_trans this hoff) (lt_irrefl _)
        · subst heq
          have h5 : lo[m].2.src = ⟨M.size - 1, kν + 1⟩ := by rw [hme]; exact hfsrc
          rw [hsrc] at h5
          simp [ctxAt] at h5
      have hj1 : j + 1 < lo.length := by omega
      obtain ⟨k', c', hsrc2, hk'1, hc', hleg⟩ := LowerPB.lowerT_src hDc.hlo (List.getElem_mem hj1)
      have hc'' : Reserve.cell? M ⟨M.size - 1, k'⟩ = some c' := by simpa [ctxAt] using hc'
      have hrow2 := hDc.block0_row rfl (List.getElem_mem hj1) (by rw [hsrc2]; exact hc')
      have h1 : official cν.row < official c'.row := by
        rw [hrowν, hrow2]; exact hrowlt j (j + 1) hjl hj1 (by omega)
      have h2 : official c'.row ≤ official cp.row := by
        rw [hrow2, hrowf, ← hme]
        rcases Nat.lt_or_eq_of_le (show j + 1 ≤ m by omega) with hlt | heq
        · exact (hrowlt _ _ hj1 hm hlt).le
        · subst heq; exact le_rfl
      have hc'1 : (1 : Row) ≤ c'.row := Classification.one_le_row hVM hc'' hk'1
      have hk'a := idx_lt_of_row_lt hVM hcν' hc'' (row_lt_of_official hc'1 h1)
      have hk'b : k' ≤ kν + 1 := by
        by_contra hn
        have := Classification.Proofs.ChainCorr.cell_row_lt hVM hcp' hc'' (by omega)
        exact absurd (official_strictMono (le_trans hcν1 hνp.le) this) (not_lt.mpr h2)
      have hk' : k' = kν + 1 := by omega
      subst hk'
      obtain rfl : c' = cp := Option.some.inj (hc''.symm.trans hcp')
      -- the leg of the next emit is the column of `a`
      have hlegc : lo[j + 1].1.leftColumn = some a.column := by
        rcases hleg with ⟨l, hl, hlc⟩ | ⟨_, h0⟩
        · rw [hcpl] at hl
          obtain rfl := Option.some.inj hl
          exact hlc
        · exact absurd hoff (by rw [h0]; exact not_lt_of_ge (Row.zero_le _))
      -- the node above `Q`
      have hk2 : j + 2 < (R[M.size - 1 + (M.size - 1 - root.column) * 0]'hXR).size := by
        rw [hDc.size, List.length_append]; omega
      obtain ⟨hk', hrow, ref, hrefl, hrefc⟩ := hDc.node hk2 (by omega)
      have hj21 : (lo ++ us)[j + 2 - 1]'hk' = lo[j + 1] := by
        simp [List.getElem_append_left hj1]
      rw [hj21] at hrow hrefc
      have hVlen : j + 2 < (Frame.ofMountain R).length QN.1 := by
        change j + 2 < R[QN.1.val].size
        simp only [hQNcol]
        exact hk2
      let VN : (Frame.ofMountain R).Node := ⟨QN.1, ⟨j + 2, hVlen⟩⟩
      have hVu : (Frame.ofMountain R).upper QN = some VN :=
        upper_eq_of_index rfl (by simp [VN]; omega)
      have hVcell : (Frame.ofMountain R).cell VN =
          (R[M.size - 1 + (M.size - 1 - root.column) * 0]'hXR)[j + 2] := by
        change R[QN.1.val][j + 2] = _
        simp only [hQNcol]
      obtain ⟨AN, hAl, _, _⟩ := hF.stored_valid VN ref (by rw [hVcell]; exact hrefl)
      have hAr : Frame.ref AN = ref := lookup_spec hAl
      have hAraw : (Frame.ofMountain R).rawParent QN = some AN :=
        rawParent_eq_of_upper_left hVu (by rw [hVcell, hAr]; exact hrefl)
      have hAH := highestIn_of_hb (E.HB QN hQr) hVu hAraw
      have hVh : (Frame.ofMountain R).height VN = (Frame.ofMountain M).height pN := by
        change ((Frame.ofMountain R).cell VN).row = ((Frame.ofMountain M).cell pN).row
        rw [hVcell, hrow, hpNc, ← hrow2]
        exact Classification.stored_official (le_trans hcν1 hνp.le)
      rw [hVh] at hAH
      have haNc1 : aN.1.val = a.column := by
        have := congrArg Ref.column haN; simpa [Frame.ref] using this
      have hAc : AN.1.val = a.column := by
        have h3 : AN.1.val = ref.column := by rw [← hAr]; rfl
        rw [h3, hrefc]
        simp [legColumn, hlegc, ctxAt]
      have hh := highestIn_twin (E.agree _ hac) hAc haNc1 hAH haH
      have hAa : Frame.ref AN = Frame.ref aN := ref_eq_of_twin E (by omega) (by rw [hAc, haNc1]) hh
      rw [haN] at hAa
      have hQraw : Reserve.rawParent R ⟨M.size - 1 + (M.size - 1 - root.column) * 0, j + 1⟩ =
          some a := by
        rw [← hQN, ← hAa]; exact reserve_rawParent_of_frame hAraw
      have hcaR : Reserve.cell? R a = some ca := by
        rw [LowerChainRecon.cell_agree E.agree hac]; exact hca
      exact Reach.trans ⟨k1, ScaleReach.step hQraw hcQ hcaR (by rw [hQrow]; exact hjk)
        (by simp only; omega) (ScaleReach.refl _)⟩ (Reach.old hrun hTop har hac)
    · exfalso
      obtain ⟨_, co', _, hco', _, hτ'⟩ := ub_below hTop hr hne (by simp only; omega) hcμ' hμτ
      have hco'' : Reserve.cell? M ⟨M.size - 1, kν + 1⟩ = some co' := hco'
      rw [hcp'] at hco''
      obtain rfl := Option.some.inj hco''
      exact hcase hτ'
  · obtain ⟨_, csrc, _, hcs, _, hτs, _, hs1, _⟩ := upper_data hD hj hup
    exact (not_reach_high hTop hr hs1 hcs hτs hcμ' hμτ).elim


/-! ## Lower top copies -/

/-- The origin of a lower emit of a block `i ≥ 1` has its upper node below `τ` when its chain
passes `μ`. -/
theorem lo_of_pass {s : List Nat} {M : Mountain} {t : Cell} {root : Ref}
    (hTop : Recon.Top s M t root) {o μ : Ref} (hr : Reach M o μ) (hne : o ≠ μ) (ho1 : 1 ≤ o.index)
    {cμ' : Cell} (hcμ' : Reserve.cell? M (above μ) = some cμ') (hμτ : cμ'.row < t.row) :
    ∀ c', Reserve.cell? M (above o) = some c' → c'.row < t.row := by
  obtain ⟨_, co', _, hco', _, hτ'⟩ := ub_below hTop hr hne ho1 hcμ' hμτ
  intro c' hc'
  rw [hco'] at hc'
  rw [← Option.some.inj hc']
  exact hτ'

/-- **The step for a lower top copy of an inner column of a block `i ≥ 1`.** -/
theorem pstepTop {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} {i x : Nat}
    {es : List (Emit × Origin)} {j : Nat} (hD : NodeData s n R M t root i x es j) (hi0 : 0 < i)
    (hxl : x < M.size - 1) (hj : j < es.length) (hup : es[j].2.isUpper = false)
    (htop : IsTopAt es j) :
    PStepOK R M n t root ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ es[j].2.src := by
  intro IH μ hμc cμ' hcμ' hμτ hr
  have hin := hD.le_n hi0
  have hTN := topNode_of_isTopAt hD hi0 hxl hj htop
  obtain ⟨hrun, hTop, hx, hes, _, _⟩ := hD
  have hcr := hTop.lt
  obtain ⟨hxg, _⟩ := mem_blockColumns hcr hx
  obtain ⟨hzc, hs1, _⟩ := emitsT_good hes es[j] (List.getElem_mem hj)
  rw [hup] at hzc
  have hzc' : es[j].2.src.column = x := by simpa [ctxAt] using hzc
  have hne : es[j].2.src ≠ μ := by intro h; rw [← h] at hμc; omega
  obtain ⟨a, k1, hza, har⟩ := hr.head hne
  obtain ⟨hraw, cz, ca, hcz, hca, _, _⟩ := hza
  have hlo := lo_of_pass hTop hr hne hs1 hcμ' hμτ
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
  have hQA : Reach R ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ (Frame.ref A) :=
    ⟨_, ScaleReach.step hAraw hcZ hcA le_rfl hlt (ScaleReach.refl _)⟩
  refine Reach.trans hQA ?_
  have haN : aN.1.val = a.column := by rw [← ha]; rfl
  rcases Nat.lt_trichotomy aN.1.val root.column with hl | he | hg
  · exfalso
    have := har.column_le
    omega
  · have he' : a.column = root.column := by rw [← haN]; exact he
    have haμ : a = μ := Recon.SeamPass.Reach.eq_of_column har (by rw [hμc, he'])
    obtain ⟨esB, k0, hk0, hesB, hAeq, cν, hcν, hνc, hν1, hνt, hpa⟩ :=
      stepRootLookup s n R M t root i hrun hTop hi0 hin _ _ hTN a cz ca hraw hcz hca hlo he' _
        hAraw
    have hνa := x0Pass hTop _ cν hνc hν1 hcν hνt a hpa
    have hO : OrigAt M R n root.column (M.size - 1) (official t.row) (Frame.ref A)
        esB[k0].2.src := by
      refine ⟨i - 1, M.size - 1, esB, k0, x0_mem_block'
        hcr (by omega), by rw [hAeq], by rw [hAeq], ?_, ⟨_, hcA⟩, hk0, rfl⟩
      rw [hAeq]
      unfold blockEmits at hesB
      exact hesB
    rw [← haμ]
    exact IH _ _ hlt hO a he' cμ' (by rw [haμ]; exact hcμ') hμτ hνa
  · have hTA := lo_right C hg
    rw [ha] at hTA
    exact IH _ _ hlt (origAt_of_topNode hTA ⟨_, hcA⟩) μ hμc cμ' hcμ' hμτ har

/-- **The step for a lower top copy of the copy of `x₀` in a block `i ≥ 1`.** -/
theorem pstepX0Top {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} {i : Nat}
    {es : List (Emit × Origin)} {j : Nat} (hD : NodeData s n R M t root i (M.size - 1) es j)
    (hi0 : 0 < i) (hj : j < es.length) (hup : es[j].2.isUpper = false) (htop : IsTopAt es j) :
    PStepOK R M n t root ⟨M.size - 1 + (M.size - 1 - root.column) * i, j + 1⟩ es[j].2.src := by
  intro IH μ hμc cμ' hcμ' hμτ hr
  have hin := hD.le_n hi0
  have hD0 := hD
  obtain ⟨hrun, hTop, hx, hes, _, _⟩ := hD0
  have hcr := hTop.lt
  obtain ⟨hzc, hs1, _⟩ := emitsT_good hes es[j] (List.getElem_mem hj)
  rw [hup] at hzc
  have hzc' : es[j].2.src.column = M.size - 1 := by simpa [ctxAt] using hzc
  have hne : es[j].2.src ≠ μ := by intro h; rw [← h] at hμc; omega
  obtain ⟨a, k1, hza, har⟩ := hr.head hne
  obtain ⟨hraw, cz, ca, hcz, hca, _, _⟩ := hza
  have hlo := lo_of_pass hTop hr hne hs1 hcμ' hμτ
  obtain ⟨ZN, VN, A, zN, z'N, aN, lo, us, hZ, hz, ha, C⟩ :=
    lo_coreX hD hi0 hj htop hraw hcz hca hlo
  have hAraw : Reserve.rawParent R ⟨M.size - 1 + (M.size - 1 - root.column) * i, j + 1⟩ =
      some (Frame.ref A) := by
    rw [← hZ]; exact reserve_rawParent_of_frame C.Araw
  have hcZ : Reserve.cell? R ⟨M.size - 1 + (M.size - 1 - root.column) * i, j + 1⟩ =
      some ((Frame.ofMountain R).cell ZN) := by
    rw [← hZ]; exact LowerChainRecon.cell?_ref ZN
  have hcA := LowerChainRecon.cell?_ref A
  have hlt : (Frame.ref A).column <
      (⟨M.size - 1 + (M.size - 1 - root.column) * i, j + 1⟩ : Ref).column := by
    rw [← hZ]; exact rawParent_column_lt C.E.FR C.Araw
  have hQA : Reach R ⟨M.size - 1 + (M.size - 1 - root.column) * i, j + 1⟩ (Frame.ref A) :=
    ⟨_, ScaleReach.step hAraw hcZ hcA le_rfl hlt (ScaleReach.refl _)⟩
  refine Reach.trans hQA ?_
  have haN : aN.1.val = a.column := by rw [← ha]; rfl
  rcases Nat.lt_trichotomy aN.1.val root.column with hl | he | hg
  · exfalso
    have := har.column_le
    omega
  · have he' : a.column = root.column := by rw [← haN]; exact he
    have haμ : a = μ := Recon.SeamPass.Reach.eq_of_column har (by rw [hμc, he'])
    obtain ⟨esB, k0, hk0, hesB, hAeq, cν, hcν, hνc, hν1, hνt, hpa⟩ := stepRootLookupX C he
    rw [ha] at hpa
    have hνa := x0Pass hTop _ cν hνc hν1 hcν hνt a hpa
    have hO : OrigAt M R n root.column (M.size - 1) (official t.row) (Frame.ref A)
        esB[k0].2.src := by
      refine ⟨i - 1, M.size - 1, esB, k0, x0_mem_block' hcr (by omega), by rw [hAeq],
        by rw [hAeq], ?_, ⟨_, hcA⟩, hk0, rfl⟩
      rw [hAeq]
      unfold blockEmits at hesB
      exact hesB
    rw [← haμ]
    exact IH _ _ hlt hO a he' cμ' (by rw [haμ]; exact hcμ') hμτ hνa
  · have hTA := lo_rightX C hg
    rw [ha] at hTA
    exact IH _ _ hlt (origAt_of_topNode hTA ⟨_, hcA⟩) μ hμc cμ' hcμ' hμτ har


/-! ## Clean copies that are not the top copy -/

/-- **The step for a clean copy (`b = 0`) of a block `i ≥ 1` that is not the top copy.** -/
theorem pstepCleanNT {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} {i x : Nat}
    {es : List (Emit × Origin)} {j : Nat} (hD : NodeData s n R M t root i x es j) (hi0 : 0 < i)
    (hj : j < es.length) (a : Ref) (ha : es[j].2 = .clean a false) :
    PStepOK R M n t root ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ es[j].2.src := by
  intro IH μ hμc cμ' hcμ' hμτ hr
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
  obtain ⟨cv, hcv, ⟨g, hag, hgc⟩, hall⟩ := Classification.Proofs.ChainCorr.NonTop.SeamD.walkXD E
    hi0 (by omega) a.column ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ a rfl hva
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
  -- `μ` is the end `g` of the generation chain
  have hne : a ≠ μ := by intro h; rw [← h] at hμc; omega
  obtain ⟨cg, hcg, hcgrow⟩ := Classification.Proofs.ChainCorr.Inner.Clean.chain_row hag ca hca
  have hμg : μ = g := eq_of_row hTop hr hne hs1 (by rw [hgc, hμc]) hca hcg hcgrow
  rw [hμg] at hcμ' ⊢
  obtain ⟨_, _, h3⟩ := hall g hag.to_reflTransGen
  obtain ⟨P, cP, hQP, hPc, hcP, hProw⟩ := h3 hgc
  have hg1 : 1 ≤ g.index := by
    cases hag with
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
  have hνg := x0Pass hTop _ cν hνc hν1 hcν hνt g hpa
  have hO : OrigAt M R n root.column (M.size - 1) (official t.row) P esB[k0].2.src := by
    refine ⟨i - 1, M.size - 1, esB, k0, x0_mem_block' hcr (by omega), by rw [hPeq],
      by rw [hPeq], ?_, ⟨_, hcP⟩, hk0, rfl⟩
    rw [hPeq]
    unfold blockEmits at hesB
    exact hesB
  have hPQ : P.column < (⟨x + (M.size - 1 - root.column) * i, j + 1⟩ : Ref).column := by
    rw [hPc]; simp only; omega
  exact Reach.trans ⟨0, hQP⟩ (IH P _ hPQ hO g hgc cμ' hcμ' hμτ hνg)


/-! ## Gap copies that are not the top copy (from `CutParentNT`) -/

/-- **The walk from a gap copy that is not the top copy** (from `CutParentNT`): the generation
chain of its origin ends at a node `g` of the root column, and the chain of `R` from the copy
passes `g` when `g⁺` is below `τ`. -/
theorem cutPass (hCP : CutParentNT) {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell}
    {root : Ref} (hrun : Official.expandDiagram s n = .ok R) (hTop : Recon.Top s M t root) :
    ∀ X i x es j, X = x + (M.size - 1 - root.column) * i → NodeData s n R M t root i x es j →
      0 < i → ∀ hj : j < es.length, cutOrigin es[j].2 = true → ¬ IsTopAt es j →
      (∀ Q' o', Q'.column < X → OrigAt M R n root.column (M.size - 1) (official t.row) Q' o' →
        PassOK R M t root Q' o') →
      ∃ g, Relation.ReflTransGen (GenStep M root.column) es[j].2.src g ∧
        g.column = root.column ∧
        ∀ cg', Reserve.cell? M (above g) = some cg' → cg'.row < t.row → Reach R ⟨X, j + 1⟩ g := by
  intro X
  induction X using Nat.strong_induction_on with
  | _ X ih =>
  intro i x es j hX hD hi0 hj hcut hnt IH
  subst hX
  have hin := hD.le_n hi0
  have hcr := hTop.lt
  have hVM := build_valid_of_success hTop.build
  have hU : Relator.RightUnique (GenStep M root.column) := fun _ _ _ h h' =>
    Classification.Proofs.ChainCorr.Inner.GenStep.unique hVM h h'
  obtain ⟨E, lo, us, hDc, hee⟩ := colData_of_node hD
  subst hee
  have hD0 := hD
  obtain ⟨_, _, hx, hes, ⟨cu, hcu⟩, _⟩ := hD0
  obtain ⟨hxg, hxl⟩ := mem_blockColumns hcr hx
  -- the top copy `T` above `u`
  have hnt' := hnt
  unfold IsTopAt at hnt'
  push Not at hnt'
  obtain ⟨j', hj', _, hjj, hsrcT⟩ := hnt'
  -- the source `m`, its cell and column
  obtain ⟨hsc, hs1, cm, hcm, _⟩ := emitsT_good hes (lo ++ us)[j] (List.getElem_mem hj)
  have hup : ((lo ++ us)[j]).2.isUpper = false := by
    cases h : ((lo ++ us)[j]).2 with
    | clean r b => rfl
    | plain r => rw [h] at hcut; simp [cutOrigin] at hcut
    | upper r => rw [h] at hcut; simp [cutOrigin] at hcut
  rw [hup] at hsc
  have hmc : ((lo ++ us)[j]).2.src.column = x := by simpa [ctxAt] using hsc
  -- the copy
  have hva : Classification.Proofs.ChainCorr.NonTop.CopyAtX M R n root.column (M.size - 1)
      (official t.row) i ⟨x + (M.size - 1 - root.column) * i, j + 1⟩
      (.clean ((lo ++ us)[j]).2.src true) := by
    refine ⟨x, lo ++ us, j, hxg, hxl, hx, rfl, rfl, hes, hj, ?_⟩
    cases h : ((lo ++ us)[j]).2 with
    | clean r b =>
        rw [h] at hcut
        cases b
        · simp [cutOrigin] at hcut
        · simp [h, Origin.src]
    | plain r => rw [h] at hcut; simp [cutOrigin] at hcut
    | upper r => rw [h] at hcut; simp [cutOrigin] at hcut
  -- the stored parent of `u`
  have hj1 : j + 1 < (lo ++ us).length := by omega
  have hk2 : j + 1 + 1 < (R[x + (M.size - 1 - root.column) * i]'hDc.XR).size := by
    rw [hDc.size]; omega
  obtain ⟨_, _, u1, hleft, _⟩ := hDc.node hk2 (by omega)
  obtain ⟨c1, hc1, _, _⟩ := colCell hDc hj1
  have hc1' : (R[x + (M.size - 1 - root.column) * i]'hDc.XR)[j + 1 + 1] = c1 := by
    have h2 : Reserve.cell? R ⟨x + (M.size - 1 - root.column) * i, j + 1 + 1⟩ =
        some ((R[x + (M.size - 1 - root.column) * i]'hDc.XR)[j + 1 + 1]) := by
      simp only [Reserve.cell?, Array.getElem?_eq_getElem hDc.XR, Option.bind_eq_bind,
        Option.bind_some]
      exact Array.getElem?_eq_getElem hk2
    exact Option.some.inj (h2.symm.trans hc1)
  rw [hc1'] at hleft
  have hru : Reserve.rawParent R ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ = some u1 :=
    Classification.Proofs.ChainCorr.Inner.rawParent_eq_some.mpr ⟨c1, hc1, hleft⟩
  have hVR := Classification.Proofs.ChainCorr.NonTop.SeamD.validR hrun
  obtain ⟨_, ⟨cu1, hcu1⟩, hu1lt⟩ := Classification.Proofs.ChainCorr.Inner.rawParent_cells hVR hru
  rcases hCP s n R M t root i x (lo ++ us) j hD hi0 hj hcut hnt u1 hru with
    ⟨hu1c, b, hmb, hbc⟩ | ⟨x', es', j', hD', hu1eq, hj'', hcut', hnt', hmb⟩
  · -- the stored parent is in the boundary column: `g = b`
    refine ⟨b, Relation.ReflTransGen.single hmb, hbc, fun cg' hcg' hgτ => ?_⟩
    obtain ⟨_, hb1, ca, cb, l, hca, hl, hbl, hcb, hbrow⟩ := hmb
    obtain ⟨esB, k0, hk0, hesB, hu1eqB, cν, hcν, hνc, hν1, hνt, hpa⟩ :=
      cut_bnd_lookup E hi0 hin hDc hj' hjj hcut hsrcT hbc hb1 hcb hca hbrow hru hu1c
    have hνb := x0Pass hTop _ cν hνc hν1 hcν hνt b hpa
    have hO : OrigAt M R n root.column (M.size - 1) (official t.row) u1 esB[k0].2.src := by
      refine ⟨i - 1, M.size - 1, esB, k0, x0_mem_block' hcr (by omega), by rw [hu1eqB],
        by rw [hu1eqB], ?_, ⟨cu1, hcu1⟩, hk0, rfl⟩
      rw [hu1eqB]
      unfold blockEmits at hesB
      exact hesB
    exact Reach.trans ⟨_, ScaleReach.step hru hcu hcu1 le_rfl hu1lt (ScaleReach.refl _)⟩
      (IH u1 _ hu1lt hO b hbc cg' hcg' hgτ hνb)
  · -- the stored parent is a gap copy of the next generation `b`
    have hlt' : x' + (M.size - 1 - root.column) * i < x + (M.size - 1 - root.column) * i := by
      have := hu1lt; rw [hu1eq] at this; exact this
    obtain ⟨g, hbg, hgc, hreach⟩ := ih _ hlt' i x' es' j' rfl hD' hi0 hj'' hcut' hnt'
      (fun Q' o' h hO => IH Q' o' (lt_trans h hlt') hO)
    refine ⟨g, Relation.ReflTransGen.head hmb hbg, hgc, fun cg' hcg' hgτ => ?_⟩
    have hR := hreach cg' hcg' hgτ
    rw [← hu1eq] at hR
    exact Reach.trans ⟨_, ScaleReach.step hru hcu hcu1 le_rfl hu1lt (ScaleReach.refl _)⟩ hR

/-- **The step for a gap copy that is not the top copy**, from `CutParentNT`. -/
theorem pstepCutNT (hCP : CutParentNT) {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell}
    {root : Ref} {i x : Nat} {es : List (Emit × Origin)} {j : Nat}
    (hD : NodeData s n R M t root i x es j) (hi0 : 0 < i) (hj : j < es.length)
    (hcut : cutOrigin es[j].2 = true) (hnt : ¬ IsTopAt es j) :
    PStepOK R M n t root ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ es[j].2.src := by
  intro IH μ hμc cμ' hcμ' hμτ hr
  have hD0 := hD
  obtain ⟨hrun, hTop, hx, hes, _, _⟩ := hD0
  have hcr := hTop.lt
  have hVM := build_valid_of_success hTop.build
  obtain ⟨hxg, _⟩ := mem_blockColumns hcr hx
  obtain ⟨g, hmg, hgc, hreach⟩ := cutPass hCP hrun hTop _ i x es j rfl hD hi0 hj hcut hnt IH
  obtain ⟨hsc, hs1, cm, hcm, _⟩ := emitsT_good hes es[j] (List.getElem_mem hj)
  have hup : es[j].2.isUpper = false := by
    cases h : es[j].2 with
    | clean r b => rfl
    | plain r => rw [h] at hcut; simp [cutOrigin] at hcut
    | upper r => rw [h] at hcut; simp [cutOrigin] at hcut
  rw [hup] at hsc
  have hmc : es[j].2.src.column = x := by simpa [ctxAt] using hsc
  have hne : es[j].2.src ≠ μ := by intro h; rw [← h] at hμc; omega
  have hmgT : Relation.TransGen (GenStep M root.column) es[j].2.src g := by
    rcases Relation.ReflTransGen.cases_head hmg with h | ⟨b, hab, hbg⟩
    · rw [← h] at hgc; omega
    · exact Relation.TransGen.head' hab hbg
  obtain ⟨cg, hcg, hcgrow⟩ := Classification.Proofs.ChainCorr.Inner.Clean.chain_row hmgT cm hcm
  have hμg : μ = g := eq_of_row hTop hr hne hs1 (by rw [hgc, hμc]) hcm hcg hcgrow
  rw [hμg] at hcμ' ⊢
  exact hreach cμ' hcμ' hμτ

end OmegaY.Official.Recon.TopChain.Seam.Pass
