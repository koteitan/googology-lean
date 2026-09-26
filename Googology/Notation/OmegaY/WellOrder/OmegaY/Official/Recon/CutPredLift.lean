/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CutPredLift.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CutPredMain
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CutPredFloor
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RootCut
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RowLawSource

set_option backward.do.legacy false

/-!
# The positive lift (fact MD): `LiftPosHolds`

For a region `S` of level `d ≥ 3` below the top row `τ` of the last column `x₀`, with
`ρ = top_S(c_r)` and `κ = top_S(x₀)`: `h_ρ < h_κ` (`liftPosHolds`). So the lift
`Δ = (h_κ - h_ρ)·i` of case 2 is positive for `i ≠ 0`. The hypotheses of `LiftPos` on the
column `x` (a node on the row of `ρ`, ascension) are not used.

## Proof

Let `a = row ρ` and `D = d - 2 ≥ 1` (the height is the coefficient `D`). The region is below
`τ`, so `bump a D ≤ τ`. By `last_column_rise` (`CutPredFloor.lean`), `x₀` has a node `y`
with `bump a D ≤ row y` that agrees with `a` above `D`: `y` is in the region and its
coefficient `D` is at least `a_D + 1`. The top `κ` of `x₀` in the region is not below `y`.

`last_column_rise` rests on `last_parent_floor`: the parent of a node `q` of `x₀` below the top
is not below any row of `c_r` that is at most `row q`. Then the step of `x₀` out of
`[a, bump a D)` has exponent at most `D`, so it lands in `[bump a D, bump a (D + 1))`.

Numerically (`reference/official/cut-pred.cjs`) the strict inequality holds at every level
`d ≥ 2`, with or without the hypotheses on `x`.
-/

namespace OmegaY.Official.Recon.CutPredMD

open Canonical Official Classification Expansion Geometry Frame

theorem coeff_le_of_le_agree {x y : Row} {D : Nat} (h : x ≤ y)
    (hag : ∀ k, D < k → x.coeff k = y.coeff k) : x.coeff D ≤ y.coeff D := by
  by_contra hn
  have hlt : y < x := Row.lt_iff.mpr ⟨D, fun j hj => (hag j hj).symm, by omega⟩
  exact absurd h (not_le.mpr hlt)

/-- **Fact MD.** -/
theorem liftPosHolds : LiftPosHolds := by
  intro s M col t root hM hcol ht hroot hcr ctx hsrc hrc hlc _ _ d S r cl hd _ hlow hrho _ _
  obtain ⟨k, hk, hSk, hSup⟩ := hlow
  have hτ : official t.row ≠ 0 := by
    intro h0
    rw [h0] at hSk
    simp at hSk
  have hTop : Recon.Top s M t root :=
    ⟨hM, by simp [hcol, ht], hτ, hroot, hcr⟩
  obtain ⟨middle, last, _, hlast, p, hinit, htop, hroot'⟩ := hTop.preparation
  subst hinit
  subst htop
  subst hroot'
  obtain ⟨g⟩ := p.root_geometry hlast
  have hNormal := build_normal_of_success p.initial_build
  -- the node `ρ`
  rw [hsrc, hrc] at hrho
  obtain ⟨hmem, hin, _⟩ := RowLaw.topIn_spec hrho
  obtain ⟨w, hwcol, hwreal, _, hwcell⟩ := frameNode_of_realNodes hmem
  have hRootCol : g.rootNode.1.val = p.root.column := congrArg Ref.column g.root_ref
  have hwc : w.1 = g.rootNode.1 := Fin.ext (hwcol.trans hRootCol.symm)
  have hwh : (Frame.ofMountain p.initial).height w = cl.row := congrArg Cell.row hwcell
  have htoprow : (Frame.ofMountain p.initial).height g.topNode = p.lastTop.row :=
    congrArg Cell.row g.top_cell
  set a := cl.row with ha
  set D := d - 2 with hD
  have hD1 : 1 ≤ D := by omega
  -- the region in stored rows
  have hinR : ∀ k', d - 1 ≤ k' → a.coeff k' = S.coeff k' := by
    intro k' hk'
    rw [← coeff_official_pos a (by omega)]
    exact (Recon.inRegion_iff d S (official a)).mp hin k' hk'
  have hτk : ∀ k', 1 ≤ k' → p.lastTop.row.coeff k' = (official p.lastTop.row).coeff k' :=
    fun k' hk' => (coeff_official_pos _ hk').symm
  have hak : a.coeff k < p.lastTop.row.coeff k := by
    rw [hinR k hk, hτk k (by omega)]
    exact hSk
  have hup : ∀ k', k < k' → a.coeff k' = p.lastTop.row.coeff k' := by
    intro k' hk'
    rw [hinR k' (by omega), hτk k' (by omega)]
    exact hSup k' hk'
  have hcap : Row.bump a D ≤ p.lastTop.row := by
    have hjump : Row.jump a p.lastTop.row = k + 1 :=
      Row.jump_eq_succ_of_last (Nat.ne_of_lt hak) hup
    have h1 := Row.bump_last_le (Row.lt_iff.mpr ⟨k, hup, hak⟩)
    rw [hjump, Nat.add_sub_cancel] at h1
    exact (Row.bump_mono_exponent a (show D ≤ k by omega)).trans h1
  -- a node of the last column in the region, high enough
  obtain ⟨y, hyc, hyr, hyb, hyag⟩ := last_column_rise hNormal g.lower_parent g.lower_upper
    hwc hwreal (D := D) (by rw [hwh, htoprow]; exact hcap)
  rw [hwh] at hyb hyag
  have hymem := realNodes_of_frameNode y hyr
  have hsize := Canonical.build_size p.initial_build
  have hycol : y.1.val = p.initial.size - 1 := by
    rw [hyc, g.lower_column, hsize]
    simp
  rw [hycol] at hymem
  have hyin : inRegion d S (official ((Frame.ofMountain p.initial).cell y).row) = true := by
    rw [Recon.inRegion_iff]
    intro k' hk'
    rw [coeff_official_pos _ (by omega)]
    change ((Frame.ofMountain p.initial).height y).coeff k' = S.coeff k'
    rw [hyag k' (by omega), hinR k' hk']
  obtain ⟨κ, hκ⟩ := filter_last_exists (P := fun q => inRegion d S (official q.2.row)) hymem hyin
  have hκ' : topIn p.initial (p.initial.size - 1) d S = some κ := hκ
  obtain ⟨_, hκin, _⟩ := RowLaw.topIn_spec hκ'
  have hmax := RowLaw.topIn_row_max p.initial_build hκ' hymem hyin
  -- compare the heights
  rw [hlc, hsrc, hκ']
  change (official a).coeff (d - 2) < (official κ.2.row).coeff (d - 2)
  rw [← hD, coeff_official_pos _ hD1]
  have hy1 : a.coeff D + 1 ≤ ((Frame.ofMountain p.initial).height y).coeff D := by
    have := coeff_le_of_le_agree hyb (fun k' hk' => by
      rw [Row.coeff_bump_high hk', hyag k' hk'])
    rwa [Row.coeff_bump_at] at this
  have hy2 : (official ((Frame.ofMountain p.initial).cell y).row).coeff D ≤
      (official κ.2.row).coeff D := by
    apply coeff_le_of_le_agree hmax
    intro k' hk'
    rw [(Recon.inRegion_iff d S _).mp hyin k' (by omega),
      (Recon.inRegion_iff d S _).mp hκin k' (by omega)]
  rw [coeff_official_pos _ hD1] at hy2
  change a.coeff D < (official κ.2.row).coeff D
  have : ((Frame.ofMountain p.initial).height y).coeff D =
      ((Frame.ofMountain p.initial).cell y).row.coeff D := rfl
  omega

/-- **`CutPredHolds` from `CleanGapHolds`.** -/
theorem cutPredHolds_of_cleanGap (hC : CleanGapHolds) : CutPredHolds :=
  cutPredHolds_of_facts liftPosHolds hC

end OmegaY.Official.Recon.CutPredMD

#print axioms OmegaY.Official.Recon.CutPredMD.liftPosHolds
#print axioms OmegaY.Official.Recon.CutPredMD.cutPredHolds_of_cleanGap
