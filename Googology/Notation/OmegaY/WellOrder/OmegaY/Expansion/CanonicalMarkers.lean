/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/CanonicalMarkers.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/CanonicalMarkers.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.BottomLegs
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Normal
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.WeakGeometry

set_option backward.do.legacy false

/-! The complete auxiliary row-zero marker chain for actual canonical build
outputs.  Its concrete bottom legs and its ordered geometry are conclusions
of the builder theorems, not additional hypotheses. -/

namespace OmegaY.Expansion

open Canonical

theorem build_phantomChain {values : List Nat} {mountain : Mountain}
    (hLegal : Legal values) (hBuild : build values = .ok mountain) :
    PhantomChain mountain := by
  apply phantomChain_of_ordered (build_normal_of_legal hLegal hBuild).toOrdered
  intro c hi hpos
  simpa only [if_neg (Nat.ne_of_gt hpos)] using build_bottom_left hBuild c hi

theorem build_phantom_reachable {values : List Nat} {mountain : Mountain}
    (hLegal : Legal values) (hBuild : build values = .ok mountain)
    {rootColumn currentColumn : Nat} (hle : rootColumn ≤ currentColumn)
    (hc : currentColumn < mountain.size) :
    ForwardWeakPath mountain ⟨rootColumn, 0⟩ ⟨currentColumn, 0⟩ :=
  (build_phantomChain hLegal hBuild).reachable hle hc

theorem build_phantom_weakReaches {values : List Nat} {mountain : Mountain}
    (hLegal : Legal values) (hBuild : build values = .ok mountain)
    {rootColumn currentColumn : Nat} (hle : rootColumn ≤ currentColumn)
    (hc : currentColumn < mountain.size) :
    weakReaches mountain ⟨rootColumn, 0⟩ (currentColumn + 1) ⟨currentColumn, 0⟩ = .ok true :=
  (build_phantomChain hLegal hBuild).weakReaches hle hc

end OmegaY.Expansion

#print axioms OmegaY.Expansion.build_phantomChain
#print axioms OmegaY.Expansion.build_phantom_reachable
#print axioms OmegaY.Expansion.build_phantom_weakReaches
