/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/SeamStepUpper.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
Port change: in `upper_data` the line `by_cases hxx : x = M.size - 1 <;> simp [hxx]` is removed, because the `simp only` before it already closes the goal in Lean 4.30.0.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.SeamStepTop

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# The step from an upper emit (`StepUpper`)

An upper emit of a block `i ≥ 1` keeps the row of its source (a node of `x` at or above `τ`, or of
`c_r` for the copy of `x₀`) and is the only copy of it in its column.

* inner column: `topNode_of_isTopAt` and `topStepHi`;
* the copy of `x₀` (the column `c_r + w·(i + 1)`): `stand_of_highest` in block `i + 1` with the
  property "row at most the row of the source".
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

/-- The column data of the column of a node. -/
theorem colData_of_node {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    {i x : Nat} {es : List (Emit × Origin)} {j : Nat}
    (hD : NodeData s n R M t root i x es j) :
    ∃ (E : Env s n R M t root) (lo us : List (Emit × Origin)),
      LowerPB.ColData s n R M t root (x + (M.size - 1 - root.column) * i) i x lo us ∧
      es = lo ++ us := by
  have hD' := hD
  obtain ⟨hrun, hTop, hx, hes, ⟨cQ, hcQ⟩, _⟩ := hD'
  have hcr := hTop.lt
  obtain ⟨hxg, hxl⟩ := mem_blockColumns hcr hx
  have hXR : x + (M.size - 1 - root.column) * i < R.size := by
    obtain ⟨col, hcol, _⟩ := Classification.Proofs.ChainCorr.cell?_column hcQ
    exact (Array.getElem?_eq_some_iff.mp hcol).1
  have hX0 : M.size - 1 ≤ x + (M.size - 1 - root.column) * i := by
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0
      have : x = M.size - 1 := by simpa [blockColumns] using hx
      omega
    · have := Nat.le_mul_of_pos_right (M.size - 1 - root.column) h0
      omega
  have E := CrossUpperSim.env_of hrun hTop hXR hX0
  rcases Nat.eq_zero_or_pos i with hi0 | hi0
  · subst hi0
    have hx0 : x = M.size - 1 := by simpa [blockColumns] using hx
    subst hx0
    have hn : 0 < n := by
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
    obtain ⟨lo, us, hDc⟩ := colData_x0 E (m := 0) hn
    exact ⟨E, lo, us, hDc, Except.ok.inj (hes.symm.trans hDc.emitsT)⟩
  · obtain ⟨lo, us, hDc⟩ := colData_block E hi0 (hD.le_n hi0) hx hXR
    exact ⟨E, lo, us, hDc, Except.ok.inj (hes.symm.trans hDc.emitsT)⟩

/-- **The data of an upper emit**: its source is a node of the upper column at or above `τ`, the
node keeps its row, and it is the top copy of its source. -/
theorem upper_data {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    {i x : Nat} {es : List (Emit × Origin)} {j : Nat}
    (hD : NodeData s n R M t root i x es j) (hj : j < es.length)
    (hup : es[j].2.isUpper = true) :
    ∃ cQ csrc, Reserve.cell? R ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ = some cQ ∧
      Reserve.cell? M es[j].2.src = some csrc ∧ cQ.row = csrc.row ∧ t.row ≤ csrc.row ∧
      es[j].2.src.column = (if x = M.size - 1 then root.column else x) ∧
      1 ≤ es[j].2.src.index ∧ IsTopAt es j := by
  obtain ⟨E, lo, us, hDc, hee⟩ := colData_of_node hD
  subst hee
  have hTop := E.top
  have hVM := build_valid_of_success hTop.build
  have hjus : lo.length ≤ j := by
    by_contra hn
    have hjl : j < lo.length := by omega
    have := ((LowerPB.lowerT_good hDc.hlo) _ (List.getElem_mem hjl)).2
    have hE : (lo ++ us)[j] = lo[j] := List.getElem_append_left hjl
    rw [← hE, hup] at this
    cases this
  have hmem : (lo ++ us)[j] ∈ us := by
    rw [List.getElem_append_right hjus]; exact List.getElem_mem _
  obtain ⟨k2, c2, hk2, hc2, hup2, hrow2, hτ2, _⟩ := (LowerPB.upperT_spec hDc.hus).1 _ hmem
  have hs2 : ((lo ++ us)[j]).2.src = ⟨upperColumn (ctxAt M R x i root.column
      (M.size - 1 - root.column) (M.size - 1) (x + (M.size - 1 - root.column) * i)), k2⟩ := by
    rw [hup2]; rfl
  have hc2' : Reserve.cell? M ((lo ++ us)[j]).2.src = some c2 := by
    rw [hs2]; simpa [ctxAt] using hc2
  have hc21 : (1 : Row) ≤ c2.row := Classification.one_le_row hVM hc2' (by rw [hs2]; exact hk2)
  have hk : j + 1 < (R[x + (M.size - 1 - root.column) * i]'hDc.XR).size := by
    rw [hDc.size]; omega
  obtain ⟨_, hrowQ, _⟩ := hDc.node hk (by omega)
  refine ⟨(R[x + (M.size - 1 - root.column) * i]'hDc.XR)[j + 1], c2, ?_, hc2', ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Reserve.cell?, Array.getElem?_eq_getElem hDc.XR, Option.bind_eq_bind,
      Option.bind_some]
    exact Array.getElem?_eq_getElem hk
  · rw [hrowQ]
    simp only [Nat.add_sub_cancel]
    rw [hrow2]
    exact Classification.stored_official hc21
  · exact le_of_official_le hc21 hτ2
  · rw [hs2]
    simp only [upperColumn, ctxAt]
  · rw [hs2]; exact hk2
  · intro j' hj' _ hjj heq
    have hj'us : lo.length ≤ j' := by omega
    have hmem' : (lo ++ us)[j'] ∈ us := by
      rw [List.getElem_append_right hj'us]; exact List.getElem_mem _
    obtain ⟨k3, c3, _, hc3, hup3, hrow3, _, _⟩ := (LowerPB.upperT_spec hDc.hus).1 _ hmem'
    have hs3 : ((lo ++ us)[j']).2.src = ⟨upperColumn (ctxAt M R x i root.column
        (M.size - 1 - root.column) (M.size - 1) (x + (M.size - 1 - root.column) * i)), k3⟩ := by
      rw [hup3]; rfl
    have hc3' : Reserve.cell? M ((lo ++ us)[j']).2.src = some c3 := by
      rw [hs3]; simpa [ctxAt] using hc3
    rw [heq] at hc3'
    have hcc : c3 = c2 := Option.some.inj (hc3'.symm.trans hc2')
    subst hcc
    have hsorted := List.pairwise_iff_getElem.mp hDc.sorted j j' (by simpa using hj)
      (by simpa using hj') hjj
    simp only [List.getElem_map] at hsorted
    rw [hrow2, hrow3] at hsorted
    exact lt_irrefl _ hsorted

/-- **`StepUpper` holds.** -/
theorem stepUpper : StepUpper := by
  intro s n R M t root i x es j hD hi0 hj hup IH k μ hμ hr
  have hin := hD.le_n hi0
  obtain ⟨cQ, csrc, hcQ, hcs, hrowQ, hτs, hsc, hs1, htop⟩ := upper_data hD hj hup
  have hD' := hD
  obtain ⟨hrun, hTop, hx, hes, _, _⟩ := hD'
  have hcr := hTop.lt
  have hVM := build_valid_of_success hTop.build
  obtain ⟨hxg, hxl⟩ := mem_blockColumns hcr hx
  have hne : es[j].2.src ≠ μ := by
    intro h
    rw [← h] at hμ
    rw [hsc] at hμ
    split at hμ <;> omega
  obtain ⟨a, hza, har⟩ := Classification.Proofs.ChainCorr.SRParts.reach_head hr hne
  rcases Nat.lt_or_eq_of_le hxl with hlt | heq
  · -- an inner column
    have hTN := topNode_of_isTopAt hD hi0 hlt hj htop
    obtain ⟨hraw, cz, ca, hcz, hca, hjz, _⟩ := hza
    have hθ : ∃ c', Reserve.cell? M (above es[j].2.src) = some c' ∧ t.row ≤ c'.row := by
      obtain ⟨c', hc', _⟩ := Classification.Proofs.ChainCorr.Inner.rawParent_eq_some.mp hraw
      refine ⟨c', hc', ?_⟩
      have hcz' : cz = csrc := Option.some.inj (hcz.symm.trans hcs)
      subst hcz'
      have h1 : Reserve.cell? M ⟨es[j].2.src.column, es[j].2.src.index⟩ = some cz := hcz
      have h2 : Reserve.cell? M ⟨es[j].2.src.column, es[j].2.src.index + 1⟩ = some c' := hc'
      exact le_of_lt (lt_of_le_of_lt hτs (Classification.Proofs.ChainCorr.cell_row_lt hVM h1 h2
        (by omega)))
    obtain ⟨A, hst, hstand⟩ := topStepHi hrun hTop hi0 hin hTN hraw hcz hca hθ
    have hAc : ∃ c, Reserve.cell? R A = some c := by
      obtain ⟨_, _, cA, _, hcA, _, _⟩ := hst; exact ⟨cA, hcA⟩
    exact reach_cons hst hjz (reach_of_stand hrun hTop IH hstand hAc hst.column_lt hμ har)
  · -- the copy of `x₀`: its upper part copies the root column
    subst heq
    have hin' : i + 1 ≤ n := by
      unfold blockColumns at hx
      rw [if_neg (by omega)] at hx
      simp only [List.mem_range'_1] at hx
      split at hx <;> omega
    have hXR : M.size - 1 + (M.size - 1 - root.column) * i < R.size := by
      obtain ⟨col, hcol, _⟩ := Classification.Proofs.ChainCorr.cell?_column hcQ
      exact (Array.getElem?_eq_some_iff.mp hcol).1
    have E := CrossUpperSim.env_of hrun hTop hXR (by omega)
    have hG := E.G
    have hF := E.FR
    simp only [if_true] at hsc
    obtain ⟨cN, hcN, hcNc⟩ := node_of_cell hcs
    obtain ⟨QN, hQN, hQNc⟩ := node_of_cell hcQ
    have hcN1 : cN.1.val = root.column := by
      have := congrArg Ref.column hcN; simp only [Frame.ref] at this; omega
    have hcNr : Real cN := by
      show 0 < cN.2.val
      have := congrArg Ref.index hcN; simp only [Frame.ref] at this; omega
    have hQc : QN.1.val = shiftCol root.column (M.size - 1 - root.column) (i + 1) cN.1.val := by
      rw [shiftCol_of_le (le_of_eq hcN1.symm), hcN1]
      have := congrArg Ref.column hQN; simp only [Frame.ref] at this
      rw [this, Nat.mul_succ]; omega
    have hh : (Frame.ofMountain R).height QN = (Frame.ofMountain M).height cN := by
      change ((Frame.ofMountain R).cell QN).row = ((Frame.ofMountain M).cell cN).row
      rw [hQNc, hcNc, hrowQ]
    have hθc : t.row ≤ (Frame.ofMountain M).height cN := by
      change t.row ≤ ((Frame.ofMountain M).cell cN).row; rw [hcNc]; exact hτs
    have hStand := stand_of_highest E (i := i + 1) (by omega) hin'
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
    have hsrc : es[j].2.src.column = root.column := hsc
    have hac : a.column < root.column := by rw [← hsrc]; exact hza.column_lt
    obtain ⟨hraw, ca', cb, hca', hcb, hj', _⟩ := hza
    have h1 := (hStand.2.1 hsrc).2.2 a ca' cb hraw hca' hcb
    exact Classification.Proofs.ChainCorr.ScaleReach.trans
      (Classification.Proofs.ChainCorr.reach_mono h1 hj') (reach_old hrun hTop har (by omega))

end OmegaY.Official.Recon.TopChain.Seam

#print axioms OmegaY.Official.Recon.TopChain.Seam.stepUpper
