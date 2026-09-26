/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/LRCFinal.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LRCStep

set_option backward.do.legacy false

/-!
# The rows form from an item of `Y` with the target of `J`

`rows_of_item`: if the tree of the column read for the leg has an item `J'` with the target of
`J`, a node of its source column in its source region, and (for `e ≥ 1`) fewer children than
`J`, then the rows conclusion `RowsConclusion J λ e` holds for that column. (The argument of
`lowerRows_of_J` and `lowerJ_of_fewer`, for one given column.)
-/

namespace OmegaY.Official.Recon.LRC

open Canonical Expansion Dimension RowLaw JumpLaw JumpLawLower
open Classification Classification.Proofs.ChainCorr

theorem rows_of_item {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    {i x : Nat} {lam θ : Row} {l e : Nat} {J : Item}
    (hP : LowerPair s n R M t root i x lam θ l e J) {i' y : Nat}
    (hNC' : NewColumn s n R M t root i' y) {J' : Item}
    (hJ' : InTree (colCtx M R root i' y) (official t.row) (e + 1) J')
    (htgt : J'.target = J.target)
    (hHas : Has (colCtx M R root i' y) (e + 1) J'.source)
    (hfew : ∀ d, e = d + 1 → ∀ cs cs', childItems (colCtx M R root i x) (d + 2) J = .ok cs →
      childItems (colCtx M R root i' y) (d + 2) J' = .ok cs' → cs'.length < cs.length) :
    ∀ vsY, LowerRun (colCtx M R root i' y) (official t.row) vsY → RowsConclusion J lam e vsY := by
  intro vsY hvsY
  have hctxY := hNC'.runCtx
  obtain ⟨_, hJ'OK, LB, hLB, hLBsub, hLBback⟩ := inTree_facts hctxY hvsY hJ'
  have hgood := runItem_good hctxY (e + 1) (by omega) J' hJ'OK LB hLB
  rw [htgt] at hLBback hgood
  refine ⟨?_, ?_⟩
  · obtain ⟨em0, hem0⟩ := List.exists_mem_of_ne_nil LB (hgood.2.mp hHas)
    exact ⟨em0, hLBsub em0 hem0, hgood.1.2.1 em0 hem0⟩
  · intro em hem hin d hd
    subst hd
    have hemB := hLBback em hem hin
    obtain ⟨cs', outs, hcs', _, _⟩ := runItem_children hLB
    have h1 := run_coeff_lt hctxY hJ'OK hLB hcs' em hemB
    obtain ⟨vs, us, col, hvs, _, _, k, hk, hkL, _, _, _, ⟨LJ, hLJ, _⟩, _⟩ := hP.run
    obtain ⟨cs, outsX, hcs, _, _⟩ := runItem_children hLJ
    have h2 := lam_height hP hcs
    have h3 := hfew d rfl cs cs' hcs hcs'
    omega

end OmegaY.Official.Recon.LRC
