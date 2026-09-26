/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/SourceStopping.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/SourceStopping.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.FrozenSource

set_option backward.do.legacy false

/-! The contour's numerical stopping test cannot fire before a genuine
source-column top. This fact is about frozen source cells, not new copies. -/

namespace OmegaY.Expansion

open Canonical

def NoPrematureOne (nodes : Column) : Prop :=
  ∀ index current upper, nodes[index]? = some current → nodes[index + 1]? = some upper →
    current.value ≠ 1

theorem build_source_no_premature_one {values : List Nat} {mountain : Mountain}
    (hBuild : Canonical.build values = .ok mountain) {sourceColumn : Nat} {nodes : Column}
    (hColumn : mountain[sourceColumn]? = some nodes) : NoPrematureOne nodes := by
  obtain ⟨hc, hNodes⟩ := Array.getElem?_eq_some_iff.mp hColumn
  have hValid : ColumnValid mountain sourceColumn nodes :=
    hNodes ▸ build_valid_of_success hBuild sourceColumn hc
  intro index current upper hCurrent hUpper
  by_cases hZero : index = 0
  · have hCurrentZero : nodes[0]? = some current := by simpa only [hZero] using hCurrent
    have he : current = phantom := Option.some.inj (hCurrentZero.symm.trans hValid.phantom)
    simp [he, phantom]
  · have hSteps : ColumnSteps mountain sourceColumn nodes :=
      hNodes ▸ build_steps hBuild sourceColumn hc
    have hLarge := (hSteps index current upper hCurrent hUpper (by omega)).1
    omega

end OmegaY.Expansion

#print axioms OmegaY.Expansion.build_source_no_premature_one
