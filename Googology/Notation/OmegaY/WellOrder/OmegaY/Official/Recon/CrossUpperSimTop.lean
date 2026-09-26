/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CrossUpperSimTop.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossUpperSimMain
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.ParentBelowLowerCols
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrCopyMono

set_option backward.do.legacy false

/-!
# `CopyTop` from `Emitted`

`CopyTop` (`CrossUpperSimDefs.lean`) says: in a column `X = y + w·i` of a block `i ≥ 1`, the
highest node below `τ` is the top copy of the highest node `z` below `τ` of the column `y` of
`M(s)`. This file derives it from the open statement `LowerPB.Emitted`
(`ParentBelowLowerProfile.lean`: in the copy of `y > c_r`, every node of `y` below `τ` is the
origin of a lower copy) and the proved monotonicity of origins (`lowerT_mono`,
`ChainCorrCopyMono.lean`):

* the lower copies of `X` come first and are below `τ`, the upper copies are at or above `τ`,
  so the highest node of `X` below `τ` is made by the last lower copy;
* the origin rows of the lower copies do not decrease, and `z` is the origin of some lower
  copy (`Emitted`), so the origin of the last lower copy is at or above `z`; it is a node of
  `y` below `τ`, hence it is `z`;
* the nodes above it are upper copies, whose origins are at rows `≥ τ`, so none is a copy of
  `z`.

`crossLexFor_upper_of_emitted : Emitted → CopyQLower → CopyStepLower → CrossLexFor IsUpper`.
-/

namespace OmegaY.Official.Recon.CrossUpperSim

open Canonical Expansion Geometry Frame Classification
open CrossUpper
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index
  upper_eq_of_index)

theorem cell?_ref' {M : Mountain} (u : (Frame.ofMountain M).Node) :
    Reserve.cell? M (Frame.ref u) = some ((Frame.ofMountain M).cell u) := by
  rcases u with ⟨c, i⟩
  have hc : c.val < M.size := c.isLt
  have hi : i.val < M[c.val].size := i.isLt
  simp only [Reserve.cell?, Frame.ref, Frame.cell, Frame.ofMountain, Array.getElem?_eq_getElem hc,
    Option.bind_eq_bind, Option.bind_some, Array.getElem?_eq_getElem hi]

theorem official_le_of_le {a b : Row} (ha : (1 : Row) ≤ a) (h : a ≤ b) :
    Official.official a ≤ Official.official b := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact (official_strictMono ha h).le
  · exact le_rfl

theorem lt_of_official_lt {a b : Row} (hb : (1 : Row) ≤ b)
    (h : Official.official a < Official.official b) : a < b := by
  by_contra hn
  exact absurd h (not_lt.mpr (official_le_of_le hb (le_of_not_gt hn)))

theorem le_of_official_le {a b : Row} (hb : (1 : Row) ≤ b)
    (h : Official.official a ≤ Official.official b) : a ≤ b := by
  by_contra hn
  exact absurd h (not_le.mpr (official_strictMono hb (lt_of_not_ge hn)))

/-- The column of `M(s)` and its top. -/
theorem top_col {s : List Nat} {M : Mountain} {t : Cell} {root : Ref} (hTop : Top s M t root) :
    ∃ col, M[M.size - 1]? = some col ∧ col.back? = some t := by
  have h := hTop.top
  cases hc : M[M.size - 1]? with
  | none => rw [hc] at h; cases h
  | some col => rw [hc] at h; exact ⟨col, rfl, h⟩

/-- **`CopyTop` from `Emitted`.** -/
theorem copyTop_of_emitted (hE : LowerPB.Emitted) : CopyTop := by
  intro s n R M t root i y hrun hTop hi1 hy U z hU1 hz1 hTU hTz
  have hcr := hTop.lt
  obtain ⟨hyg, hyl⟩ := mem_blockColumns hcr hy
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  have hX0 : M.size - 1 ≤ U.1.val := by rw [hU1]; omega
  have E := env_of hrun hTop U.1.isLt hX0
  have hG := E.G
  have hF := E.FR
  have ht1 := tau_gt_one hTop
  have hVM := build_valid_of_success hTop.build
  obtain ⟨M', hM', _, hI, _⟩ := run_basic hrun
  obtain rfl : M = M' := Except.ok.inj (hTop.build.symm.trans hM')
  -- the column `X` as a `ColData`
  obtain ⟨i', x', lo, us, hD⟩ := LowerPB.colData hrun hTop E.CI hI U.1.isLt hX0
  have hx'g := hD.xgt
  have hx'l := hD.xle
  obtain ⟨hxx, hii⟩ := decomp_eq (w := M.size - 1 - root.column) (a := y - root.column - 1)
    (b := x' - root.column - 1) (i := i) (j := i') (by omega) (by omega) (by
      have h1 := hD.Xeq
      rw [hU1] at h1
      generalize (M.size - 1 - root.column) * i = P at h1 ⊢
      generalize (M.size - 1 - root.column) * i' = Q at h1 ⊢
      omega)
  obtain rfl : x' = y := by omega
  subst hii
  -- the copy call
  obtain ⟨i'', x'', _, hx''b, hXeq'', hcopy⟩ := E.CI.2.2 U.1.val U.1.isLt hX0
  have hx''g := (mem_blockColumns hcr hx''b).1
  have hx''l := (mem_blockColumns hcr hx''b).2
  obtain ⟨hxx'', hii''⟩ := decomp_eq (w := M.size - 1 - root.column) (a := x' - root.column - 1)
    (b := x'' - root.column - 1) (i := i) (j := i'') (by omega) (by omega) (by
      have h1 := hXeq''
      rw [hU1] at h1
      generalize (M.size - 1 - root.column) * i = P at h1 ⊢
      generalize (M.size - 1 - root.column) * i'' = Q at h1 ⊢
      omega)
  have hx''x : x' = x'' := by omega
  subst hx''x
  subst hii''
  -- the node `z`
  have hzr : 1 ≤ z.2.val := by
    by_contra h0
    have hlen : 1 < (Frame.ofMountain M).length z.1 := by
      have := hG.length_ge_two z.1
      omega
    have hb := hG.bottom_row z.1 hlen
    have := hTz.2 ⟨z.1, ⟨1, hlen⟩⟩ rfl (by
      change ((Frame.ofMountain M).cells z.1 ⟨1, hlen⟩).row < _
      rw [hb]
      exact ht1)
    simp at this
    omega
  have hzc : Reserve.cell? M ⟨x', z.2.val⟩ = some ((Frame.ofMountain M).cell z) := by
    have := cell?_ref' z
    rw [show (Frame.ref z : Ref) = ⟨x', z.2.val⟩ by simp [Frame.ref, hz1]] at this
    exact this
  have hz1r : (1 : Row) ≤ (Frame.ofMountain M).height z := one_le_height hG hzr
  have hτz : Official.official ((Frame.ofMountain M).cell z).row < Official.official t.row :=
    official_strictMono hz1r hTz.1
  obtain ⟨e, he, _, hesrc⟩ := hE s n R hrun M t root hTop i hi1 hD.iln _ hD.bctx hD.xgt lo
    hD.hlo z.2.val _ hzr hzc hτz
  change e.2.src = ⟨x', z.2.val⟩ at hesrc
  -- the index of `U`
  have hsize := hD.size
  have hlo_lt := hD.lo_lt
  have hus_ge := hD.us_ge
  have hsτ : Official.stored (Official.official t.row) = t.row :=
    Classification.stored_official (le_of_lt ht1)
  have hLpos : 0 < lo.length := List.length_pos_of_mem he
  have hUL : U.2.val = lo.length := by
    apply le_antisymm
    · by_contra hn
      have hk : U.2.val < (R[U.1.val]'hD.XR).size := U.2.isLt
      obtain ⟨hk', hrow, _⟩ := hD.node hk (by omega)
      have hmem : (lo ++ us)[U.2.val - 1] ∈ us := by
        rw [List.getElem_append_right (by omega)]
        exact List.getElem_mem _
      have h1 := CrossUpper.stored_mono (hus_ge _ hmem)
      rw [hsτ, ← hrow] at h1
      exact absurd hTU.1 (not_lt.mpr h1)
    · have hk : lo.length < (R[U.1.val]'hD.XR).size := by
        rw [hsize, List.length_append]
        omega
      obtain ⟨hk', hrow, _⟩ := hD.node hk (by omega)
      have hmem : (lo ++ us)[lo.length - 1] ∈ lo := by
        rw [List.getElem_append_left (by omega)]
        exact List.getElem_mem _
      have h1 := stored_strictMono (hlo_lt _ hmem)
      rw [hsτ, ← hrow] at h1
      exact hTU.2 ⟨U.1, ⟨lo.length, hk⟩⟩ rfl h1
  -- the last lower copy is a copy of `z`
  have hlast : lo.length - 1 < lo.length := by omega
  have hflast : lo[lo.length - 1].2.src = Frame.ref z := by
    obtain ⟨k, cv, hsrc, hk1, hcv, _⟩ := LowerPB.lowerT_src hD.hlo (List.getElem_mem hlast)
    change lo[lo.length - 1].2.src = ⟨x', k⟩ at hsrc
    change Reserve.cell? M ⟨x', k⟩ = some cv at hcv
    obtain ⟨hpw, hbelow⟩ := Proofs.ChainCorr.CopyMonoProof.lowerT_mono hD.hlo
    obtain ⟨cv', hcv', hcvτ⟩ := hbelow _ (List.getElem_mem hlast)
    rw [hsrc] at hcv'
    have hcc : cv' = cv := Option.some.inj (hcv'.symm.trans hcv)
    rw [hcc] at hcvτ hcv'
    obtain ⟨colv, hcolv, hcvv⟩ := Classification.cell?_spec hcv
    have hkx : k < (Frame.ofMountain M).length ⟨x', by omega⟩ := by
      obtain ⟨hks, _⟩ := Array.getElem?_eq_some_iff.mp hcvv
      obtain ⟨hcs, hce⟩ := Array.getElem?_eq_some_iff.mp hcolv
      change k < M[x'].size
      simp only at hce
      rw [hce]
      exact hks
    let v : (Frame.ofMountain M).Node := ⟨⟨x', by omega⟩, ⟨k, hkx⟩⟩
    have hvc : (Frame.ofMountain M).cell v = cv := by
      have := cell?_ref' v
      simp only [Frame.ref, v] at this
      exact Option.some.inj (this.symm.trans hcv)
    have hv1 : (1 : Row) ≤ (Frame.ofMountain M).height v := one_le_height hG (by
      show 0 < k
      omega)
    have hvτ : (Frame.ofMountain M).height v < t.row := by
      apply lt_of_official_lt (le_of_lt ht1)
      change Official.official ((Frame.ofMountain M).cell v).row < _
      rw [hvc]
      exact hcvτ
    have hvz : v.1 = z.1 := Fin.ext (by simp [v, hz1])
    have hkz : k ≤ z.2.val := hTz.2 v hvz hvτ
    -- the origin row of the last copy is at least the row of `z`
    obtain ⟨m, hm, hme⟩ := List.getElem_of_mem he
    have hzv : (Frame.ofMountain M).height z ≤ (Frame.ofMountain M).height v := by
      apply le_of_official_le hv1
      change Official.official ((Frame.ofMountain M).cell z).row ≤
        Official.official ((Frame.ofMountain M).cell v).row
      rw [hvc]
      rcases Nat.lt_or_ge m (lo.length - 1) with hml | hml
      · have hole := List.pairwise_iff_getElem.mp hpw m (lo.length - 1) hm hlast hml
        exact hole _ _ (by rw [hme, hesrc]; exact hzc) (by rw [hsrc]; exact hcv)
      · have hmeq : m = lo.length - 1 := by omega
        subst hmeq
        have : (⟨x', k⟩ : Ref) = ⟨x', z.2.val⟩ := by rw [← hsrc, hme, hesrc]
        have hkz' : k = z.2.val := by simp at this; exact this
        rw [hkz'] at hcv
        rw [Option.some.inj (hzc.symm.trans hcv)]
    have hkz2 : k = z.2.val := by
      by_contra hne
      have hlt : (Frame.ofMountain M).height v < (Frame.ofMountain M).height z :=
        height_lt_of_index hG hvz (by simp [v]; omega)
      exact absurd (lt_of_lt_of_le hlt hzv) (lt_irrefl _)
    rw [hsrc]
    simp [Frame.ref, hz1, hkz2]
  -- `OriginAt` data
  obtain ⟨col, hcol, htc⟩ := top_col hTop
  have hes := hD.emitsT
  have hUlt : U.2.val - 1 < (lo ++ us).length := by rw [List.length_append]; omega
  have hUo : OriginAt s n R U.1.val (U.2.val - 1) ((lo ++ us)[U.2.val - 1]'hUlt).2 := by
    refine ⟨M, col, t, root, x', i, lo ++ us, ((lo ++ us)[U.2.val - 1]'hUlt).1, hTop.build, hcol,
      htc, hTop.left, hcr, hy, hD.Xeq, hes,
      ⟨R[U.1.val]'hD.XR, Array.getElem?_eq_getElem hD.XR, hcopy, hD.asm⟩, ?_⟩
    rw [List.getElem?_eq_getElem hUlt]
  have hUsrc : ((lo ++ us)[U.2.val - 1]'hUlt).2.src = Frame.ref z := by
    rw [List.getElem_append_left (by omega)]
    simp only [hUL]
    exact hflast
  refine ⟨⟨by omega, _, hUo, hUsrc⟩, ?_⟩
  -- no node above `U` is a copy of `z`
  rintro Z' hZ'1 hZ'2 ⟨hZ'r, o, ho, hosrc⟩
  obtain ⟨M2, col2, t2, root2, x2, i2, es2, em2, hM2, hcol2, ht2, hroot2, _, hx2b, hX2, hes2, _,
    hj2⟩ := ho
  obtain rfl : M = M2 := Except.ok.inj (hTop.build.symm.trans hM2)
  obtain rfl : col = col2 := Option.some.inj (hcol.symm.trans hcol2)
  obtain rfl : t = t2 := Option.some.inj (htc.symm.trans ht2)
  obtain rfl : root = root2 := Option.some.inj (hTop.left.symm.trans hroot2)
  have hx2g := (mem_blockColumns hcr hx2b).1
  have hx2l := (mem_blockColumns hcr hx2b).2
  have hZX : Z'.1.val = U.1.val := by rw [hZ'1]
  obtain ⟨_, hii2⟩ := decomp_eq (w := M.size - 1 - root.column) (a := x' - root.column - 1)
    (b := x2 - root.column - 1) (i := i) (j := i2) (by omega) (by omega) (by
      have h1 := hX2
      rw [hZX, hU1] at h1
      generalize (M.size - 1 - root.column) * i = P at h1 ⊢
      generalize (M.size - 1 - root.column) * i2 = Q at h1 ⊢
      omega)
  subst hii2
  obtain rfl : x2 = x' := by
    have h1 := hX2
    rw [hZX, hU1] at h1
    omega
  rw [hZX] at hes2
  have hee : es2 = lo ++ us := Except.ok.inj (hes2.symm.trans hes)
  subst hee
  have hj : Z'.2.val - 1 < (lo ++ us).length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hj2
    cases hj2
  rw [List.getElem?_eq_getElem hj] at hj2
  have hoe : o = ((lo ++ us)[Z'.2.val - 1]).2 := by rw [Option.some.inj hj2]
  have hmem : (lo ++ us)[Z'.2.val - 1] ∈ us := by
    rw [List.getElem_append_right (by omega)]
    exact List.getElem_mem _
  obtain ⟨k, c, _, hc, hup, _, hτc, _⟩ := (LowerPB.upperT_spec hD.hus).1 _ hmem
  rw [← hoe] at hup
  rw [hup] at hosrc
  simp only [Origin.src] at hosrc
  rw [hosrc] at hc
  have hcz := Option.some.inj ((cell?_ref' z).symm.trans hc)
  rw [hcz] at hτz
  exact absurd hτz (not_lt.mpr hτc)

/-- **`CrossLexFor IsUpper` from `Emitted`, `CopyQLower` and `CopyStepLower`.** -/
theorem crossLexFor_upper_of_emitted (hE : LowerPB.Emitted) (hQL : CopyQLower)
    (hSL : CopyStepLower) : CrossLexFor IsUpper :=
  crossLexFor_upper_of_sim (copyTop_of_emitted hE) hQL hSL

/-- `SeamLastPosHolds` from `Emitted`, `CopyQLower` and `CopyStepLower`. -/
theorem seamLastPos_of_emitted (hE : LowerPB.Emitted) (hQL : CopyQLower)
    (hSL : CopyStepLower) : SeamLastPosHolds :=
  seamLastPos_of_sim (copyTop_of_emitted hE) hQL hSL

/-- `InnerHolds` from `Emitted`, `CopyQLower` and `CopyStepLower`. -/
theorem inner_of_emitted (hE : LowerPB.Emitted) (hQL : CopyQLower) (hSL : CopyStepLower) :
    InnerHolds :=
  inner_of_sim (copyTop_of_emitted hE) hQL hSL

end OmegaY.Official.Recon.CrossUpperSim

#print axioms OmegaY.Official.Recon.CrossUpperSim.copyTop_of_emitted
#print axioms OmegaY.Official.Recon.CrossUpperSim.crossLexFor_upper_of_emitted
