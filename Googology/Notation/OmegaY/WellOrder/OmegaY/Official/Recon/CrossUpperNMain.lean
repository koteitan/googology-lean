/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CrossUpperNMain.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossUpperNStart
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossUpperNEnd
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossUpperNRoot

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# `CrossLexFor IsUpper` holds (with the weakened start `CopyQLowerN`)

`CrossUpperWSim.lean` proves `CrossLexFor IsUpper` from `TopStep` and the weak start
`CopyQLowerW`, which is numerically false (`(1,21,5,20,59,20)[1]`). Here the reduction is rebuilt
over the weaker start `CopyQLowerN` (`CrossUpperNStart.lean`, **proved**): the candidate may also
be a non-top non-gap copy (`TopStartW2R.NonTopCopy`) of `a = Q_M(z)` when `a` is right of `c_r`.

A non-top start does not step along the chain of `M(s)`; it goes to the end directly:

* the seam (`z` the node below the top of `x₀`, `SeamLastPosW`): the chain of `M(s)` from `a`
  enters `c_r` at the root; its last node before the root is right of `c_r`, against
  `NoEndRightHi` (**proved**, `CrossUpperNEnd.lean`), so a non-top start does not occur;
* an inner column (`InnerHoldsW`): the end `c_M` (stored parent `π(N)`) is at or left of `c_r`
  (`NoEndRightHi`). Left of `c_r` the chain of `R` from `Q u` passes `c_M` itself
  (`TopStartW2R.nonTopPass_holds`, proved) and the node above it is the old node `c_M⁺`
  (`CrossPlainPos.old_end`); in `c_r` it reaches a node whose upper node is at the row of `c_M⁺`
  in a column `c_r + w·j` (`NonTopRootHi`, **proved**, `CrossUpperNRoot.lean`).

The Cw start is handled exactly as before (`cpw_chain`, `cpw_end`).

## Results

* `seamLastPosW_of_simN : CopyTop → CopyQLowerN → CopyStepLower → SeamLastPosW`;
* `innerW_of_simN : CopyTop → CopyQLowerN → CopyStepLower → InnerHoldsW`;
* **`crossLexFor_upper_final : CrossLexFor IsUpper`** (no hypothesis: `Emitted`, `TopStep`,
  `CopyQLowerN`, `NoEndRightHi`, `NonTopPass`, `NonTopRootHi` are proved).
-/

namespace OmegaY.Official.Recon.CrossUpperW.CUN

open Canonical Expansion Geometry Frame Classification
open CrossUpper CrossUpperSim
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index
  upper_eq_of_index)

/-- A chain from `a` to `c ≠ a` has a last node `d` whose stored parent is `c`. -/
theorem rawChain_pred {F : Frame} {a c : F.Node} (h : RawChain F a c) (hne : a ≠ c) :
    ∃ d, RawChain F a d ∧ F.rawParent d = some c := by
  induction h with
  | here => exact absurd rfl hne
  | @step a b c hraw _ ih =>
    by_cases hbc : b = c
    · subst hbc
      exact ⟨a, .here a, hraw⟩
    · obtain ⟨d, hd, hdc⟩ := ih hbc
      exact ⟨d, .step hraw hd, hdc⟩

/-- **`SeamLastPosW` from the weakened start `CopyQLowerN`.** A non-top start is impossible
here (`NoEndRightHi`). -/
theorem seamLastPosW_of_simN (hCT : CopyTop) (hQL : CrossUpperQ.CUN.CopyQLowerN)
    (hSL : CopyStepLower) : SeamLastPosW := by
  intro s n R M t root i hrun hTop hi1 hmem u p q up hu1 hu hU hup hτup hraw hq hcol
  have hcr := hTop.lt
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  have E := env_of hrun hTop u.1.isLt (by rw [hu1]; exact Nat.le_add_right _ _)
  have hG := E.G
  have hF := E.FR
  have hNM := E.NM
  have ht1 := tau_gt_one hTop
  -- `i < n`
  have hin : i < n := by
    unfold blockColumns at hmem
    rw [if_neg (by omega)] at hmem
    simp only [List.mem_range'_1] at hmem
    split at hmem
    · assumption
    · omega
  -- the top `t` of `x₀` and the node `t⁻` below it
  have hx0 : M.size - 1 < M.size := by omega
  obtain ⟨colx, hcolx, htop⟩ : ∃ colx, M[M.size - 1]? = some colx ∧ colx.back? = some t := by
    have h := hTop.top
    cases hc : M[M.size - 1]? with
    | none => rw [hc] at h; cases h
    | some colx => rw [hc] at h; exact ⟨colx, rfl, h⟩
  obtain ⟨_, hcolxe⟩ := Array.getElem?_eq_some_iff.mp hcolx
  subst hcolxe
  rw [Array.back?_eq_getElem?] at htop
  obtain ⟨htl, htc⟩ := Array.getElem?_eq_some_iff.mp htop
  let tN : (Frame.ofMountain M).Node := ⟨⟨M.size - 1, hx0⟩, ⟨M[M.size - 1].size - 1, htl⟩⟩
  have htNc : (Frame.ofMountain M).cell tN = t := htc
  have htNh : (Frame.ofMountain M).height tN = t.row := by
    change ((Frame.ofMountain M).cell tN).row = _
    rw [htNc]
  have htN2 : 2 ≤ tN.2.val := two_le_index hG (by rw [htNh]; exact ht1)
  let pM : (Frame.ofMountain M).Node := ⟨tN.1, ⟨tN.2.val - 1, by have := tN.2.isLt; omega⟩⟩
  have hpMu : (Frame.ofMountain M).upper pM = some tN :=
    upper_eq_of_index rfl (by simp [pM]; omega)
  have hpMr : Real pM := by show 0 < tN.2.val - 1; omega
  have hpMh : (Frame.ofMountain M).height pM < t.row := by
    rw [← htNh]
    exact height_lt_of_index hG rfl (by simp [pM]; omega)
  have hTpM : TopBelow (Frame.ofMountain M) t.row pM :=
    topBelow_of_upper hG hpMh hpMu (le_of_eq htNh.symm)
  have hTu : TopBelow (Frame.ofMountain R) t.row u := topBelow_of_upper hF hU hup hτup
  -- `u` is the top copy of `t⁻`, and `Q u` stands for `Q t⁻`
  have hTC := hCT s n R M t root i (M.size - 1) hrun hTop hi1 hmem u pM hu1 rfl hTu hTpM
  obtain ⟨a, A, hQa, hQA, hCA⟩ := hQL s n R M t root i (M.size - 1) hrun hTop hi1 hmem u pM tN
    hu1 rfl hpMr hpMh hpMu (le_of_eq htNh.symm) hTC
  rw [hq] at hQA
  obtain rfl := Option.some.inj hQA
  -- the root and the chain of `M(s)` from `Q t⁻` to it
  have htl' : ((Frame.ofMountain M).cell tN).left = some root := by rw [htNc]; exact hTop.left
  obtain ⟨rootN, hrl, _, _⟩ := hG.stored_valid tN root htl'
  have hrr : Frame.ref rootN = root := lookup_spec hrl
  have hrawp : (Frame.ofMountain M).rawParent pM = some rootN :=
    rawParent_eq_of_upper_left hpMu (by rw [hrr]; exact htl')
  have hrootc : rootN.1.val = root.column := by rw [← hrr]; rfl
  obtain ⟨hr1, hr2⟩ := hbAt_of_normal hNM hpMr tN rootN hpMu hrawp
  rw [htNh] at hr1
  have hPp : (Frame.ofMountain M).P pM = some rootN := (hNM.rawParent_eq_P hpMr).symm.trans hrawp
  obtain ⟨qM, hqM, hit⟩ := (P_iff hG).mp hPp
  have hqa : qM = a := Option.some.inj (hqM.symm.trans hQa)
  rw [hqa] at hit
  have har : Real a := Q_real hG hpMr hQa
  have hchain := ParentPath.rawChain hNM (hit.parentPath hG (hG.real_positive _ har)) har
  have hax : a.1.val < M.size - 1 := Q_column_lt hG hQa
  -- a non-top start is impossible: the chain of `M(s)` from `a` enters `c_r` at the root
  rcases hCA with hCA | hnt
  swap
  · exfalso
    have hac : root.column < a.1.val := hnt.1
    have hne : a ≠ rootN := fun h => by rw [h] at hac; omega
    obtain ⟨d, had, hdr⟩ := rawChain_pred hchain hne
    have hdle := TSQ.W2.CUN.noEndRightHi_holds s n R M t root i (M.size - 1) hrun hTop hi1 hmem
      u _ pM tN a hu1 rfl hpMr hpMh hpMu (le_of_eq htNh.symm) hTC hQa hq hnt rootN d hrawp had hdr
    have := rawParent_column_lt hG hdr
    omega
  -- the chain of `R`
  obtain ⟨C, hCch, hCC⟩ := cpw_chain E hCT hSL hi1 hin.le hchain har hax hCA
  have hCcol := hCC.column
  rw [hrootc, shiftCol_of_le le_rfl] at hCcol
  -- the node `r⁺` above the root
  have hXeq : root.column + (M.size - 1 - root.column) * (i + 1) =
      M.size - 1 + (M.size - 1 - root.column) * i := by
    rw [Nat.mul_succ]
    generalize (M.size - 1 - root.column) * i = P
    omega
  obtain ⟨hup1, hup2⟩ := upper_spec hup
  have hupc : up.1.val = root.column + (M.size - 1 - root.column) * (i + 1) := by
    rw [hXeq, hup1, hu1]
  have C0 := upperCopy_root E.top E.CI E.FR (i := i + 1) (by rw [← hupc]; exact up.1.isLt)
  obtain ⟨N, hNc, hNh⟩ := C0.bwd up hupc hτup
  have hrNc : rootN.1 = N.1 := Fin.ext (by rw [hrootc, hNc])
  have hrN : rootN.2.val < N.2.val :=
    index_lt_of_height_lt hG hrNc (by rw [hNh]; exact lt_of_lt_of_le hr1 hτup)
  have hlenr : rootN.2.val + 1 < (Frame.ofMountain M).length rootN.1 := by
    have := N.2.isLt
    have hl : (Frame.ofMountain M).length N.1 = (Frame.ofMountain M).length rootN.1 := by
      rw [hrNc]
    omega
  let rp : (Frame.ofMountain M).Node := ⟨rootN.1, ⟨rootN.2.val + 1, hlenr⟩⟩
  have hru : (Frame.ofMountain M).upper rootN = some rp := upper_eq_of_index rfl rfl
  have hrpτ : t.row ≤ (Frame.ofMountain M).height rp := by
    by_contra hlt
    have := hr2 rp rfl (by rw [htNh]; exact lt_of_not_ge hlt)
    simp [rp] at this
  have hrpup : (Frame.ofMountain M).height rp = (Frame.ofMountain R).height up := by
    apply le_antisymm
    · rw [← hNh]
      exact height_le_of_index hG hrNc (by simp [rp]; omega)
    · obtain ⟨Zr, hZrc, hZrh⟩ := C0.fwd rp (by simp [rp, hrootc]) hrpτ
      have hZu : u.1 = Zr.1 := Fin.ext (by rw [hZrc, ← hupc, hup1])
      have hi2 := index_lt_of_height_lt hF hZu (by rw [hZrh]; exact lt_of_lt_of_le hU hrpτ)
      rw [← hZrh]
      exact height_le_of_index hF (hup1.trans hZu) (by omega)
  -- the node above `C`
  have hrx : rootN.1.val < M.size - 1 := by omega
  obtain ⟨C0, C', hC0, hC'u, hC'c, hC'h⟩ := cpw_end E hCT hi1 hin.le hrx hCC hru hrpτ
  rcases hC'c with h | ⟨_, j, hj⟩
  · exact ⟨C0, C', i, rawChain_trans hCch hC0, hC'u,
      by rw [h, hrootc, shiftCol_of_le le_rfl], by rw [hC'h, hrpup]⟩
  · exact ⟨C0, C', j, rawChain_trans hCch hC0, hC'u, hj, by rw [hC'h, hrpup]⟩

/-- **`InnerHoldsW` from the weakened start `CopyQLowerN`.** After a non-top start the chain of
`M(s)` ends at or left of `c_r` (`NoEndRightHi`); left of `c_r` the chain of `R` passes the end
itself (`NonTopPass`), in `c_r` it reaches a copy of the node above it (`NonTopRootHi`). -/
theorem innerW_of_simN (hCT : CopyTop) (hQL : CrossUpperQ.CUN.CopyQLowerN)
    (hSL : CopyStepLower) : InnerHoldsW := by
  intro s n R M t root i x hrun hTop hxb hxx0 u p q up n0 N np qM hu1 hu hup hτup hraw hq
    hcol hN1 hNh hn0N hn0raw hqM
  have hcr := hTop.lt
  obtain ⟨hxgt, hxle⟩ := mem_blockColumns hcr hxb
  have hxlt : x < M.size - 1 := lt_of_le_of_ne hxle hxx0
  have hi1 : 1 ≤ i := by
    by_contra h
    have : i = 0 := by omega
    subst this
    simp [blockColumns] at hxb
    exact hxx0 hxb
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  have hX0 : M.size - 1 ≤ x + (M.size - 1 - root.column) * i := by
    generalize (M.size - 1 - root.column) * i = P at hwi ⊢
    omega
  have hXR : x + (M.size - 1 - root.column) * i < R.size := by rw [← hu1]; exact u.1.isLt
  have E := env_of hrun hTop hXR hX0
  have hG := E.G
  have hF := E.FR
  have hNM := E.NM
  have ht1 := tau_gt_one hTop
  have hin : i ≤ n := block_le E hxgt hxle hXR hX0
  have C0 := upperCopy_inner E hxgt hxlt hi1 hXR
  obtain ⟨hup1, hup2⟩ := upper_spec hup
  have hNτ : t.row ≤ (Frame.ofMountain M).height N := by rw [hNh]; exact hτup
  obtain ⟨hN1', hN2'⟩ := upper_spec hn0N
  have hN2 := two_le_index hG (lt_of_lt_of_le ht1 hNτ)
  have hn0r : Real n0 := by unfold Real; omega
  have hn0c : n0.1.val = x := by rw [← hN1', hN1]
  have hqMr : Real qM := Q_real hG hn0r hqM
  have hqMx : qM.1.val < M.size - 1 := by
    have := Q_column_lt hG hqM
    omega
  -- `Q u` stands for `Q n₀`
  have hstart : Cw s n R M t root i q qM ∨ (TopStartW2R.NonTopCopy s n R M t root i q qM ∧
      TopCopy s n R M u n0 ∧ (Frame.ofMountain M).height n0 < t.row) := by
    by_cases hU : t.row ≤ (Frame.ofMountain R).height u
    · -- `u` is in the upper part: it copies `n₀`
      obtain ⟨n', hn'c, hn'h⟩ := C0.bwd u hu1 hU
      have hn'N : n'.1 = N.1 := Fin.ext (by rw [hn'c, hN1])
      have hn'lt : (Frame.ofMountain M).height n' < (Frame.ofMountain M).height N := by
        rw [hn'h, hNh]
        exact height_lt_of_index hF hup1.symm (by omega)
      have hi' := index_lt_of_height_lt hG hn'N hn'lt
      have hlen' : n'.2.val + 1 < (Frame.ofMountain M).length n'.1 := by
        have hl : (Frame.ofMountain M).length N.1 = (Frame.ofMountain M).length n'.1 := by
          rw [hn'N]
        have := N.2.isLt
        omega
      let n'' : (Frame.ofMountain M).Node := ⟨n'.1, ⟨n'.2.val + 1, hlen'⟩⟩
      have hn'u : (Frame.ofMountain M).upper n' = some n'' := upper_eq_of_index rfl rfl
      obtain ⟨Z', hZu, _, hZh⟩ := C0.upper hG hF hn'c hu1 (by rw [hn'h]; exact hU)
        hn'h.symm hn'u
      rw [hup] at hZu
      obtain rfl := Option.some.inj hZu
      have hn''N : n'' = N := node_eq_of_height hG hn'N (by rw [← hZh, hNh])
      have hn'n0 : n' = n0 := by
        apply node_eq_of_index (hn'N.trans hN1')
        have := congrArg (fun z : (Frame.ofMountain M).Node => z.2.val) hn''N
        simp only [n''] at this
        omega
      subst hn'n0
      -- the column of `Q u`
      obtain ⟨LM, hLM, _, _, hqLM, _⟩ := Q_spec hG hqM
      obtain ⟨L, hL, _, _, hqL, _⟩ := Q_spec hF hq
      obtain ⟨Bref, hBl, hBc⟩ := C0.par n' u (Frame.ref LM) hn'c hu1 (by rw [hn'h]; exact hU)
        hn'h.symm hLM
      have hBL : Bref = Frame.ref L := Option.some.inj (hBl.symm.trans hL)
      have hqcol : q.1.val = shiftCol root.column (M.size - 1 - root.column) i qM.1.val := by
        rw [hqL, hqLM]
        have e : L.1.val = Bref.column := by rw [hBL]; rfl
        rw [e, hBc]
        rfl
      have hqR := highestIn_of_Q hF hq
      rw [← hn'h] at hqR
      exact Or.inl <| cw_of_cp <| cp_of_highest E hCT hi1 hin (fun r r' h1 h2 => h1.trans h2)
        (fun r hr => hr.le.trans (by rw [hn'h]; exact hU)) hqMr hqMx hqcol
        (highestIn_of_Q hG hqM) hqR
    · -- `u` is the highest node of `X` below `τ`
      have hUl : (Frame.ofMountain R).height u < t.row := lt_of_not_ge hU
      have hTu : TopBelow (Frame.ofMountain R) t.row u := topBelow_of_upper hF hUl hup hτup
      have hn0τ : (Frame.ofMountain M).height n0 < t.row := by
        by_contra hn
        obtain ⟨W, hWc, hWh⟩ := C0.fwd n0 hn0c (le_of_not_gt hn)
        have hWup : W.1 = up.1 := Fin.ext (by rw [hWc, hup1, hu1])
        have h1 : W.2.val < up.2.val := index_lt_of_height_lt hF hWup (by
          rw [hWh, ← hNh]
          exact height_lt_of_index hG hN1'.symm (by omega))
        have h2 : (Frame.ofMountain R).height W ≤ (Frame.ofMountain R).height u :=
          height_le_of_index hF (hWup.trans hup1) (by omega)
        rw [hWh] at h2
        exact hn (lt_of_le_of_lt h2 hUl)
      have hTn0 : TopBelow (Frame.ofMountain M) t.row n0 :=
        topBelow_of_upper hG hn0τ hn0N hNτ
      have hTC := hCT s n R M t root i x hrun hTop hi1 hxb u n0 hu1 hn0c hTu hTn0
      obtain ⟨a, A, hQa, hQA, hCA⟩ := hQL s n R M t root i x hrun hTop hi1 hxb u n0 N hu1 hn0c
        hn0r hn0τ hn0N hNτ hTC
      rw [hq] at hQA
      rw [hqM] at hQa
      obtain rfl := Option.some.inj hQA
      obtain rfl := Option.some.inj hQa
      rcases hCA with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hTC, hn0τ⟩
  -- the column of `p`
  obtain ⟨up', hup', hpl⟩ := rawParent_spec hraw
  rw [hup] at hup'
  obtain rfl := Option.some.inj hup'
  obtain ⟨N', hn0N', hNl⟩ := rawParent_spec hn0raw
  rw [hn0N] at hn0N'
  obtain rfl := Option.some.inj hn0N'
  obtain ⟨Aref, hA, hAc⟩ := C0.par N up (Frame.ref np) hN1 (by rw [hup1]; exact hu1) hNτ
    hNh.symm hNl
  have hAp : Aref = Frame.ref p := Option.some.inj (hA.symm.trans hpl)
  have hpcol : p.1.val = shiftCol root.column (M.size - 1 - root.column) i np.1.val := by
    have e : p.1.val = Aref.column := by rw [hAp]; rfl
    rw [e, hAc]
    rfl
  have hqcolS : q.1.val = shiftCol root.column (M.size - 1 - root.column) i qM.1.val := by
    rcases hstart with h | ⟨h, _⟩
    · exact h.column
    · exact CrossUpperQ.CUN.CwN.column (Or.inr h)
  have hne : qM ≠ np := by
    intro h
    apply hcol
    apply Fin.ext
    rw [hqcolS, hpcol, h]
  -- the chain of `M(s)` and its match in `R`
  obtain ⟨cM, cMp, hchM, hcMraw, hcMu, hhN, _, _⟩ := normal_crossLex hNM hn0r hn0N hn0raw hqM hne
  have hcMx : cM.1.val < M.size - 1 := lt_of_le_of_lt (hchM.column_le hG) hqMx
  rcases hstart with hstart | ⟨hnt, hTCu, hn0τ⟩
  swap
  · -- a non-top start: the end is at or left of `c_r`
    have hle := TSQ.W2.CUN.noEndRightHi_holds s n R M t root i x hrun hTop hi1 hxb u q n0 N qM hu1
      hn0c hn0r hn0τ hn0N hNτ hTCu hqM hq hnt np cM hn0raw hchM hcMraw
    rcases Nat.lt_or_eq_of_le hle with hlt | heqc
    · obtain ⟨c, hqc, hc1, hc2⟩ := TopStartW2R.nonTopPass_holds s n R M t root i hrun hTop hi1 hin
        q qM cM hnt hchM (Or.inl hlt)
      obtain ⟨cp, hcu, hcp1, _, hcph⟩ := CrossPlainPos.old_end E hcMx hc1 hc2 hcMu
      refine ⟨cM, c, cp, hchM, hcMraw, hqc, hcu, Or.inl ?_, by rw [hcph, ← hhN, hNh]⟩
      rw [hcp1, shiftCol_of_lt hlt]
      exact congrArg Fin.val (upper_spec hcMu).1
    · obtain ⟨Z', Z'', j, h1, h2, h3, h4⟩ := TopChain.Seam.Pass.CUN.nonTopRootHi_holds s n R M t
        root i hrun hTop hi1 hin q qM cM cMp hnt hchM heqc hcMu (by rw [← hhN]; exact hNτ)
      exact ⟨cM, Z', Z'', hchM, hcMraw, h1, h2, Or.inr ⟨heqc, j, h3⟩, by rw [h4, ← hhN, hNh]⟩
  obtain ⟨C, hCch, hCC⟩ := cpw_chain E hCT hSL hi1 hin hchM hqMr hqMx hstart
  obtain ⟨C0, C', hC0, hCu, hC'c, hC'h⟩ :=
    cpw_end E hCT hi1 hin hcMx hCC hcMu (by rw [← hhN]; exact hNτ)
  exact ⟨cM, C0, C', hchM, hcMraw, rawChain_trans hCch hC0, hCu, hC'c,
    by rw [hC'h, ← hhN, hNh]⟩




/-- **`CrossLexFor IsUpper` from `TopStep` and the weakened start `CopyQLowerN`.** -/
theorem crossLexFor_upper_of_N (hTS : Classification.Proofs.ChainCorr.LowerChain.TopStep)
    (hQN : CrossUpperQ.CUN.CopyQLowerN) : CrossLexFor IsUpper :=
  crossLexFor_upper_W
    (seamLastPosW_of_simN (copyTop_of_emitted Classification.Proofs.CopyShape.Final.emitted) hQN
      (LowerChainRecon.copyStepLower_of_topStep hTS))
    (innerW_of_simN (copyTop_of_emitted Classification.Proofs.CopyShape.Final.emitted) hQN
      (LowerChainRecon.copyStepLower_of_topStep hTS))

/-- **`CrossLexFor IsUpper` holds.** -/
theorem crossLexFor_upper_final : CrossLexFor IsUpper :=
  crossLexFor_upper_of_N FinalStageE.topStep_final CrossUpperQ.CUN.copyQLowerN_holds

end OmegaY.Official.Recon.CrossUpperW.CUN

#print axioms OmegaY.Official.Recon.CrossUpperW.CUN.rawChain_pred
#print axioms OmegaY.Official.Recon.CrossUpperW.CUN.seamLastPosW_of_simN
#print axioms OmegaY.Official.Recon.CrossUpperW.CUN.innerW_of_simN
#print axioms OmegaY.Official.Recon.CrossUpperW.CUN.crossLexFor_upper_of_N
#print axioms OmegaY.Official.Recon.CrossUpperW.CUN.crossLexFor_upper_final
