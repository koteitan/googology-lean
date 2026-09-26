/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/SeamStepB0.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.SeamStepUpper

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# The step in block `0` (`StepBlock0`)

Block `0` makes the column `x₀` of the output: below `τ` the nodes of `x₀` at their rows with
their legs (`ColData.block0_row`, `ColData.emitted0`), at or above `τ` the nodes of `c_r`.

* upper emit: `stand_of_highest` in block `1`;
* lower emit of `ν` whose upper node `ν⁺` is below `τ`: the next emit is the copy of `ν⁺`, with
  the leg of `ν⁺`, so the stored parent of the copy of `ν` is the raw parent of `ν` (a node left of
  `x₀`, shared by `R` and `M`);
* lower emit of `ν` with `ν⁺ = t`: the node is the highest node of the column below `τ`, and
  `stand_of_highest` in block `1` gives the steps of the root.
-/

namespace OmegaY.Official.Recon.TopChain.Seam

open Canonical Expansion Geometry Frame Classification
open CrossUpperSim CrossUpper
open Classification.Proofs.ChainCorr (MStep cutOrigin blockEmits)
open Classification.Proofs (ScaleReach)
open Classification.Proofs.ChainCorr.LowerChain (CopyOf TopNode Stand TopStep TopStart above
  IsTopAt)
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index
  upper_eq_of_index)
open LowerChainRecon (node_of_cell ref_inj reserve_rawParent_of_frame frame_rawParent_of_reserve)

/-- In a valid mountain, a smaller row in a column is a smaller index. -/
theorem idx_lt_of_row_lt {M : Mountain} (hV : MountainValid M) {c a b : Nat} {x y : Cell}
    (hx : Reserve.cell? M ⟨c, a⟩ = some x) (hy : Reserve.cell? M ⟨c, b⟩ = some y)
    (h : x.row < y.row) : a < b := by
  by_contra hn
  rcases Nat.lt_or_eq_of_le (not_lt.mp hn) with hlt | heq
  · exact absurd (Classification.Proofs.ChainCorr.cell_row_lt hV hy hx hlt) (not_lt.mpr h.le)
  · subst heq
    rw [hx] at hy
    cases hy
    exact lt_irrefl _ h

/-- **`StepBlock0` holds.** -/
theorem stepBlock0 : StepBlock0 := by
  intro s n R M t root x es j hD hj IH k μ hμ hr
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
    have hne : (⟨M.size - 1, kν⟩ : Ref) ≠ μ := by intro h; rw [← h] at hμ; simp at hμ; omega
    obtain ⟨a, hνa, har⟩ := Classification.Proofs.ChainCorr.SRParts.reach_head hr hne
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
      exact ScaleReach.step hQraw hcQ hcaR (by rw [hQrow]; exact hjk)
        (by simp only; omega) (reach_old hrun hTop har hac)
    · -- `ν⁺` is the top `t`: the stored parent of `ν` is the root
      obtain ⟨colx, hcolx, htc⟩ := Proofs.CopyShape.Found.top_col hTop
      obtain ⟨hcs, hcol⟩ := Array.getElem?_eq_some_iff.mp hcolx
      obtain ⟨colp, hcolp, hkp, hcpe⟩ := Classification.Proofs.ChainCorr.cell?_column hcp'
      simp only at hcolp hkp hcpe
      obtain rfl : colp = colx := Option.some.inj (hcolp.symm.trans hcolx)
      have hne0 : colp.size ≠ 0 := by omega
      have htt : t = colp[colp.size - 1] := by
        rw [Array.back?_eq_getElem?] at htc
        rw [Array.getElem?_eq_getElem (by omega)] at htc
        exact (Option.some.inj htc).symm
      have hkt : kν + 1 = colp.size - 1 := by
        by_contra hne
        have hlt : kν + 1 < colp.size - 1 := by omega
        have hct : Reserve.cell? M ⟨M.size - 1, colp.size - 1⟩ = some t := by
          simp only [Reserve.cell?, hcolp, Option.bind_eq_bind, Option.bind_some]
          rw [htt]; exact Array.getElem?_eq_getElem (by omega)
        exact hcase (Classification.Proofs.ChainCorr.cell_row_lt hVM hcp' hct hlt)
      have hcpt : cp = t := by rw [← hcpe, htt]; simp only [hkt]
      subst hcpt
      have haroot : a = root := Option.some.inj (hcpl.symm.trans hTop.left)
      have hacr : a.column = root.column := by rw [haroot]
      have haN1 : aN.1.val = root.column := by
        have := congrArg Ref.column haN; simp [Frame.ref] at this; omega
      have hpNh : (Frame.ofMountain M).height pN = cp.row := by
        change ((Frame.ofMountain M).cell pN).row = _; rw [hpNc]
      rw [hpNh] at haH
      have hQh : (Frame.ofMountain R).height QN = cν.row := by
        change ((Frame.ofMountain R).cell QN).row = _; rw [hQNc, hQrow]
      have hA : HighestIn (Frame.ofMountain R) (· < cp.row) QN := by
        refine ⟨by rw [hQh]; exact hνp, fun v hv hvlt => ?_⟩
        by_contra hn
        have hv1 : 1 ≤ v.2.val := by omega
        have hvc : v.1.val = M.size - 1 + (M.size - 1 - root.column) * 0 := by rw [hv]; exact hQNcol
        obtain ⟨hvk, hvrow⟩ := node_row hDc hvc hv1
        have hlt1 : ((lo ++ us)[v.2.val - 1]).1.row < official cp.row := by
          rw [hvrow] at hvlt
          exact LowerPB.official_lt_of_stored_lt hvlt hTop.row_one_le
        have hvlo : v.2.val - 1 < lo.length := lower_of_row hDc hvk hlt1
        have hEv : (lo ++ us)[v.2.val - 1] = lo[v.2.val - 1] := List.getElem_append_left hvlo
        rw [hEv] at hlt1
        obtain ⟨kv, cv, hsv, hkv1, hcv, _⟩ := LowerPB.lowerT_src hDc.hlo (List.getElem_mem hvlo)
        have hcv' : Reserve.cell? M ⟨M.size - 1, kv⟩ = some cv := by simpa [ctxAt] using hcv
        have hrv := hDc.block0_row rfl (List.getElem_mem hvlo) (by rw [hsv]; exact hcv)
        have hcv1 : (1 : Row) ≤ cv.row := Classification.one_le_row hVM hcv' hkv1
        have hkvle : kv ≤ kν := by
          by_contra hn2
          rcases Nat.lt_or_eq_of_le (show kν + 1 ≤ kv by omega) with h3 | h3
          · have hkvs : kv < colp.size := by
              obtain ⟨col4, hcol4, h4, _⟩ := Classification.Proofs.ChainCorr.cell?_column hcv'
              simp only at hcol4 h4
              have : col4 = colp := Option.some.inj (hcol4.symm.trans hcolp)
              rw [this] at h4
              exact h4
            omega
          · subst h3
            obtain rfl : cv = cp := Option.some.inj (hcv'.symm.trans hcp')
            rw [hrv] at hlt1
            exact lt_irrefl _ hlt1
        have hrle : lo[v.2.val - 1].1.row ≤ lo[j].1.row := by
          rw [← hrv, ← hrowν]
          apply official_mono hcv1
          rcases Nat.lt_or_eq_of_le hkvle with h3 | h3
          · exact (Classification.Proofs.ChainCorr.cell_row_lt hVM hcv' hcν' h3).le
          · subst h3; rw [hcv'] at hcν'; cases hcν'; exact le_rfl
        have hji : j < v.2.val - 1 := by omega
        have := List.pairwise_iff_getElem.mp hDc.sorted j (v.2.val - 1) (by simp; omega)
          (by simp; omega) hji
        simp only [List.getElem_map] at this
        rw [List.getElem_append_left hjl, List.getElem_append_left hvlo] at this
        exact absurd hrle (not_le.mpr this)
      have hStand := stand_of_highest E (i := 1) le_rfl hn1 (P := (· < cp.row))
        (fun r r' h1 h2 => lt_of_le_of_lt h1 h2) (fun r hr => hr)
        (real_of_value_pos hG (P_value hG ((E.NM.rawParent_eq_P hνr).symm.trans hraw')).1)
        (by omega) (by rw [shiftCol_of_le (le_of_eq haN1.symm), haN1, hQNcol]; simp; omega) haH hA
      rw [hQN, haN] at hStand
      have hne' : a ≠ μ := by intro h; subst h; omega
      obtain ⟨b, hab, hbμ⟩ := Classification.Proofs.ChainCorr.SRParts.reach_head har hne'
      have hbc : b.column < root.column := by rw [← hacr]; exact hab.column_lt
      obtain ⟨hraw2, ca2, cb, hca2, hcb, hj2, hlt2⟩ := hab
      have h1 := (hStand.2.1 hacr).2.2 b ca2 cb hraw2 hca2 hcb
      exact Classification.Proofs.ChainCorr.ScaleReach.trans
        (Classification.Proofs.ChainCorr.reach_mono h1 hj2) (reach_old hrun hTop hbμ (by omega))
  · -- an upper emit: a node of `c_r` at or above `τ`
    obtain ⟨cQ', csrc, hcQ', hcs, hrowQ, hτs, hsc, hs1, _⟩ := upper_data hD hj hup
    obtain rfl : cQ' = cQ := Option.some.inj (hcQ'.symm.trans hcQ)
    simp only [if_true] at hsc
    have hne : (lo ++ us)[j].2.src ≠ μ := by intro h; rw [← h] at hμ; omega
    obtain ⟨a, hza, har⟩ := Classification.Proofs.ChainCorr.SRParts.reach_head hr hne
    obtain ⟨cN, hcN, hcNc⟩ := node_of_cell hcs
    have hcN1 : cN.1.val = root.column := by
      have := congrArg Ref.column hcN; simp only [Frame.ref] at this; omega
    have hcNr : Real cN := by
      show 0 < cN.2.val
      have := congrArg Ref.index hcN; simp only [Frame.ref] at this; omega
    have hQc : QN.1.val = shiftCol root.column (M.size - 1 - root.column) 1 cN.1.val := by
      rw [shiftCol_of_le (le_of_eq hcN1.symm), hcN1, hQNcol]; simp; omega
    have hh : (Frame.ofMountain R).height QN = (Frame.ofMountain M).height cN := by
      change ((Frame.ofMountain R).cell QN).row = ((Frame.ofMountain M).cell cN).row
      rw [hQNc, hcNc, hrowQ]
    have hθc : t.row ≤ (Frame.ofMountain M).height cN := by
      change t.row ≤ ((Frame.ofMountain M).cell cN).row; rw [hcNc]; exact hτs
    have hStand := stand_of_highest E (i := 1) le_rfl hn1
      (P := fun r => r ≤ (Frame.ofMountain M).height cN) (fun r r' h1 h2 => le_trans h1 h2)
      (fun r hr => le_of_lt (lt_of_lt_of_le hr hθc)) hcNr (by omega) hQc
      ⟨le_rfl, fun v hv hle => by
        by_contra hn
        exact absurd hle (not_le.mpr (height_lt_of_index hG hv.symm (by omega)))⟩
      ⟨le_of_eq hh, fun v hv hle => by
        by_contra hn
        have := height_lt_of_index hF hv.symm (show QN.2.val < v.2.val by omega)
        rw [hh] at this
        exact absurd hle (not_le.mpr this)⟩
    rw [hcN, hQN] at hStand
    have hac : a.column < root.column := by rw [← hsc]; exact hza.column_lt
    obtain ⟨hraw, ca', cb, hca', hcb, hj', _⟩ := hza
    have h1 := (hStand.2.1 hsc).2.2 a ca' cb hraw hca' hcb
    exact Classification.Proofs.ChainCorr.ScaleReach.trans
      (Classification.Proofs.ChainCorr.reach_mono h1 hj') (reach_old hrun hTop har (by omega))


end OmegaY.Official.Recon.TopChain.Seam

#print axioms OmegaY.Official.Recon.TopChain.Seam.stepBlock0
