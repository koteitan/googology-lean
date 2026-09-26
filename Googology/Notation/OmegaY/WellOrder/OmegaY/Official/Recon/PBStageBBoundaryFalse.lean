/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/PBStageBBoundaryFalse.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.ParentBelowLowerProfile

set_option backward.do.legacy false

/-!
# `Boundary` is false (root column `0`)

`Boundary` (`ParentBelowLowerProfile.lean`) asks that the hypothetical copy of the root column
`c_r` in a block `i ≥ 1` runs without error (`∃ es, lowerT … = .ok es`) and emits every row
below `τ` of the boundary column `c_r + w·i`. When `c_r = 0` the copy fails: the root column
`0` has only its bottom node (the first entry is `1`), and that node has no left end
(`BottomLegs`: the bottom of column `0` has `left = none`). The copy of the bottom row is a
clean copy of the root row `0` (as in every copied column), and `levelOneT` then calls
`leftColumn` on the bottom node of column `0`, which is an error.

The smallest example is `s = (1,3)`, `n = 1`, `i = 1` (`c_r = 0`, `x₀ = 1`). `bndCheck` evaluates
the rule on it; it is checked by `#guard` (compiled evaluation: `List.mergeSort` in
`Expansion.finish` does not reduce in the kernel), as `legCheck` in
`ParentBelowLowerLeg.lean`. `not_boundary_of_check` turns the check into a refutation of
`Boundary`.

For `c_r ≥ 1` the statement holds (`BoundaryPos`, proved as `boundaryPos` in
`PBStageBBndSim.lean`).
-/

namespace OmegaY.Official.Recon.LowerPB.StageB

open Canonical Expansion Geometry Frame Classification Reserve

open Official in
/-- The hypothetical copy of the root column `0` of `(1,3)[1]` in block `1` fails. -/
def bndCheck : Bool :=
  match Canonical.build [1, 3], Official.expandDiagram [1, 3] 1 with
  | .ok M, .ok R =>
    match (M[M.size - 1]?).bind Array.back? with
    | some t =>
      match t.left with
      | some root =>
        decide (root.column < M.size - 1) && decide (official t.row ≠ 0) &&
          match lowerT ⟨M, R, root.column, 1, root.column, M.size - 1 - root.column,
              M.size - 1⟩ (official t.row) with
          | .ok _ => false
          | .error _ => true
      | none => false
    | none => false
  | _, _ => false

-- Compiled evaluation, not a kernel proof.
#guard bndCheck

open Official in
/-- **`Boundary` fails if `bndCheck` holds** (it does, by the `#guard` above). -/
theorem not_boundary_of_check (hc : bndCheck = true) : ¬ Boundary := by
  intro h
  unfold bndCheck at hc
  split at hc
  · rename_i M R hb hR
    split at hc
    · rename_i t ht
      split at hc
      · rename_i root hl
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨⟨hlt, hreal⟩, hc⟩ := hc
        split at hc
        · cases hc
        · rename_i err herr
          have hTop : Top [1, 3] M t root := ⟨hb, ht, hreal, hl, hlt⟩
          obtain ⟨es, hes, _⟩ := h [1, 3] 1 R hR M t root hTop 1 (le_refl _) (le_refl _)
          rw [hes] at herr
          cases herr
      · cases hc
    · cases hc
  · cases hc

end OmegaY.Official.Recon.LowerPB.StageB

#print axioms OmegaY.Official.Recon.LowerPB.StageB.not_boundary_of_check
