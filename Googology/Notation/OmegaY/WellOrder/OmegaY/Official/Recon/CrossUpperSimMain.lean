/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CrossUpperSimMain.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossUpperSimStep

set_option backward.do.legacy false

/-!
# `SeamLastPosHolds` and `InnerHolds` from the copies of one block

The two open statements of `CrossLexFor IsUpper` (`CrossUpper.lean`, `CrossUpperSeam.lean`)
follow from the local statements of `CrossUpperSimDefs.lean`:

* `seamLastPos_of_sim : CopyTop → CopyQLower → CopyStepLower → SeamLastPosHolds`;
* `inner_of_sim : CopyTop → CopyQLower → CopyStepLower → InnerHolds`;
* `crossLexFor_upper_of_sim`: `CrossLexFor IsUpper` from the three statements.

## The seam (`seamLastPos_of_sim`)

`u` is the highest node below `τ` of the copy `X = x₀ + w·i` of `x₀` (`i ≥ 1`). By `CopyTop`
it is the top copy of the node `t⁻` below the top `t` of `x₀`, so by `CopyQLower`,
`Q u` stands for `Q t⁻` (`Cp`). In `M(s)` the stored parent of `t⁻` is the root `r`, reached
from `Q t⁻` by a chain of stored parents (the canonical search). The chain is matched in `R`
from `Q u` (`cp_chain`) up to a node `C` with `Cp i C r`; since `r⁺` is at a row `≥ τ`, the node
above `C` is in the column `c_r + w·i` at the row of `r⁺`, which is the row of `u⁺`.

## The inner copies (`inner_of_sim`)

`u⁺` copies a node `N` of an inner column `x` at a row `≥ τ`, `n₀` is the node below `N`.
`Q u` stands for `Q n₀`: by `CopyTop` and `CopyQLower` when `row u < τ`; when `row u ≥ τ`, `u`
copies `n₀` in the upper part and `Q u` is the highest node at or below `row u` of the column
`f(col Q n₀)` (`cp_of_highest`). Then `Q n₀ ≠ π(N)` (else `Q u` would be in the column of `p`),
the source mountain gives the chain from `Q n₀` to `c_M` (`normal_crossLex`), it is matched in
`R` (`cp_chain`), and `cp_end` places the node above its last node.
-/

namespace OmegaY.Official.Recon.CrossUpperSim

open Canonical Expansion Geometry Frame Classification
open CrossUpper
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index
  upper_eq_of_index)

/-- A node above the bottom row has index at least `2`. -/
theorem two_le_index {F : Frame} (hF : F.Ordered) {v : F.Node} (h : (1 : Row) < F.height v) :
    2 ≤ v.2.val := by
  have hr : Real v := real_of_one_le hF h.le
  by_contra hn
  have h1 : v.2.val = 1 := by unfold Real at hr; omega
  have hlen : 1 < F.length v.1 := by have := v.2.isLt; omega
  have hb := hF.bottom_row v.1 hlen
  have e : F.height v = 1 := by
    change (F.cells v.1 v.2).row = 1
    rw [show v.2 = ⟨1, hlen⟩ from Fin.ext h1]
    exact hb
  rw [e] at h
  exact lt_irrefl _ h

/-- The highest node below `τ` of a column, from the node above it. -/
theorem topBelow_of_upper {F : Frame} (hF : F.Ordered) {θ : Row} {u up : F.Node}
    (hu : F.height u < θ) (hup : F.upper u = some up) (hθ : θ ≤ F.height up) :
    TopBelow F θ u := by
  refine ⟨hu, fun v hv hvl => ?_⟩
  obtain ⟨hup1, hup2⟩ := upper_spec hup
  by_contra hn
  have hle : F.height up ≤ F.height v := height_le_of_index hF (hup1.trans hv.symm) (by omega)
  exact absurd (lt_of_le_of_lt (hθ.trans hle) hvl) (lt_irrefl _)

/-! ## The seam -/

/-- **`SeamLastPosHolds` from the local statements.** -/
theorem seamLastPos_of_sim (hCT : CopyTop) (hQL : CopyQLower) (hSL : CopyStepLower) :
    SeamLastPosHolds := by
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
  -- the chain of `R`
  obtain ⟨C, hCch, hCC⟩ := cp_chain E hCT hSL hi1 hin.le hchain har hax hCA
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
  rcases hCC with ⟨hl, _⟩ | ⟨_, _, hupC, _⟩ | ⟨hg, _⟩
  · omega
  · obtain ⟨cp, hCu, hcph⟩ := hupC rp hru hrpτ
    refine ⟨C, cp, hCch, hCu, ?_, by rw [hcph, hrpup]⟩
    rw [(upper_spec hCu).1, hCcol]
  · omega

/-! ## The inner copies -/

/-- **`InnerHolds` from the local statements.** -/
theorem inner_of_sim (hCT : CopyTop) (hQL : CopyQLower) (hSL : CopyStepLower) :
    InnerHolds := by
  intro s n R M t root i x hrun hTop hxb hxx0 u p q up n0 N np qM hu1 hu hup hτup hraw hq
    hcol hN1 hNh hn0N hn0raw hqM _
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
  have hstart : Cp s n R M t root i q qM := by
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
      exact cp_of_highest E hCT hi1 hin (fun r r' h1 h2 => h1.trans h2)
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
      exact hCA
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
  have hne : qM ≠ np := by
    intro h
    apply hcol
    apply Fin.ext
    rw [hstart.column, hpcol, h]
  -- the chain of `M(s)` and its match in `R`
  obtain ⟨cM, cMp, hchM, hcMraw, hcMu, hhN, _, _⟩ := normal_crossLex hNM hn0r hn0N hn0raw hqM hne
  obtain ⟨C, hCch, hCC⟩ := cp_chain E hCT hSL hi1 hin hchM hqMr hqMx hstart
  have hcMx : cM.1.val < M.size - 1 := lt_of_le_of_lt (hchM.column_le hG) hqMx
  obtain ⟨C', hCu, hC'c, hC'h⟩ := cp_end E hCT hi1 hin hcMx hCC hcMu (by rw [← hhN]; exact hNτ)
  exact ⟨cM, C, C', hchM, hcMraw, hCch, hCu, hC'c, by rw [hC'h, ← hhN, hNh]⟩

/-! ## The main theorems -/

/-- **`SeamLastHolds` from the local statements.** -/
theorem seamLastHolds_of_sim (hCT : CopyTop) (hQL : CopyQLower) (hSL : CopyStepLower) :
    SeamLastHolds :=
  seamLastHolds_of_pos (seamLastPos_of_sim hCT hQL hSL)

/-- **`CrossLexFor IsUpper` from the local statements.** -/
theorem crossLexFor_upper_of_sim (hCT : CopyTop) (hQL : CopyQLower) (hSL : CopyStepLower) :
    CrossLexFor IsUpper :=
  crossLexFor_upper_of_pos (seamLastPos_of_sim hCT hQL hSL) (inner_of_sim hCT hQL hSL)

end OmegaY.Official.Recon.CrossUpperSim

#print axioms OmegaY.Official.Recon.CrossUpperSim.seamLastPos_of_sim
#print axioms OmegaY.Official.Recon.CrossUpperSim.inner_of_sim
#print axioms OmegaY.Official.Recon.CrossUpperSim.crossLexFor_upper_of_sim
