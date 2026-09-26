/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/PBStageBRootPos.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.PBStageBRoot

set_option backward.do.legacy false

/-!
# `RootShadowOut` from `BoundaryPos` for `c_r ≥ 1` (stage B)

For a root column `c_r ≥ 1`, `RootShadowOut` follows from `BoundaryPos` (the hypothetical copy
of `c_r` in block `i` runs and emits every row below `τ` of the boundary column) and `CutLeg`, by
the comparison of the copy of `x` with the copy of its leg column `c_r` (`legOrderLeg`,
`sameRowLeg`): `rootShadowOut_of_boundaryPos`. The root column `0` is `RootShadowZero`.
-/

namespace OmegaY.Official.Recon.LowerPB.StageB

open Canonical Expansion Geometry Frame Classification Reserve
open Classification.Proofs Classification.Proofs.CopyShape.ProfileLeg

/-- **`RootShadowOut` from `CutLeg`, `BoundaryPos` and `RootShadowZero`.** -/
theorem rootShadowOut_of_boundaryPos (hCL : CutLeg) (hBP : BoundaryPos) (hZ : RootShadowZero) :
    RootShadowOut := by
  intro s n R M t root X i x lo us hD hi1 e he hlc q hq hqR kz hkz hkz1 hzτ hze
  by_cases h0 : root.column = 0
  · exact hZ s n R M t root X i x lo us hD hi1 h0 e he hlc q hq hqR kz hkz hkz1 hzτ hze
  have hcr1 : 1 ≤ root.column := Nat.pos_of_ne_zero h0
  have hVM := build_valid_of_success hD.top.build
  have hxg := hD.xgt
  obtain ⟨es, hes, hall⟩ := hBP s n R hD.run M t root hD.top hcr1 i hi1 hD.iln
  subst hq
  obtain ⟨e', he', hrow'⟩ := hall hqR kz hkz hkz1 hzτ
  have hBK := bctx_root M R root.column (M.size - 1) i (le_of_lt hD.top.lt)
  obtain ⟨c', hc', hc'τ⟩ := lowerT_below hes e' he'
  change cell? M e'.2.src = some c' at hc'
  have hlt' : e'.1.row < e.1.row := by rw [hrow']; exact hze
  rcases List.mem_append.mp he with hel | heu
  · obtain ⟨k, co, hsrc, hk, hco, hleft⟩ := lowerT_src hD.hlo hel
    change cell? M ⟨x, k⟩ = some co at hco
    obtain ⟨l, hl, hlc2⟩ : ∃ l : Ref, co.left = some l ∧ e.1.leftColumn = some l.column := by
      rcases hleft with h | ⟨hn, _⟩
      · exact h
      · rw [hn] at hlc; cases hlc
    have hlr : l.column = root.column := by
      rw [hlc2] at hlc; exact Option.some.inj hlc
    have hle := legOrderLeg nonCutOrderLeg cutBetweenLeg CopyShape.PBStageB.cutOrder hD.run
      hD.top hi1 hD.iln hD.bctx hBK hxg hD.hlo hes hel hk hsrc hco hl hlr he' hc' hlt'
    obtain ⟨f, hf, hfr⟩ := sameRowLeg nonCutOrderLeg hCL hD.run hD.top hi1 hD.iln hD.bctx hBK
      hxg hk hco hl hlr hD.hlo hes he' hc' hle
    exact ⟨f, hf, hfr.trans hrow'⟩
  · obtain ⟨k, c, hk, hc, _, hrow, hτc, l, hl, hlc2⟩ := (upperT_spec hD.hus).1 e heu
    rw [upperColumn_ctxAt] at hc
    have hlr : l.column = root.column := by
      rw [hlc2] at hlc; exact Option.some.inj hlc
    have hxx : x ≠ M.size - 1 := by
      intro hx0
      rw [if_pos hx0] at hc
      have := left_lt hVM hc hl
      omega
    rw [if_neg hxx] at hc
    have hc1 := cell_row_one_le hVM hc hk
    have hcc : c'.row < c.row := row_lt_of_official hc1 (lt_of_lt_of_le hc'τ hτc)
    obtain ⟨f, hf, hfr⟩ := sameRowLeg nonCutOrderLeg hCL hD.run hD.top hi1 hD.iln hD.bctx hBK
      hxg hk hc hl hlr hD.hlo hes he' hc' (Or.inl hcc)
    exact ⟨f, hf, hfr.trans hrow'⟩

/-- **`LowerParentBelowHolds` from `GenLeg`, `BoundaryPos` and `RootShadowZero`.** -/
theorem lowerParentBelowHolds_of_boundaryPos (hG : CopyShape.PBStageB.GenLeg)
    (hBP : BoundaryPos) (hZ : RootShadowZero) : LowerParentBelowHolds :=
  lowerParentBelowHolds_of_genLeg hG
    (rootShadowOut_of_boundaryPos (CopyShape.PBStageB.cutLeg_of_genLeg hG) hBP hZ)

end OmegaY.Official.Recon.LowerPB.StageB

#print axioms OmegaY.Official.Recon.LowerPB.StageB.rootShadowOut_of_boundaryPos
#print axioms OmegaY.Official.Recon.LowerPB.StageB.lowerParentBelowHolds_of_boundaryPos
