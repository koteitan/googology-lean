/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Canonical/RowShadow.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Canonical/RowShadow.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.RowShadow
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Normal

set_option backward.do.legacy false

/-! Same-row ancestry for the actual canonical builder and its parent search. -/

namespace OmegaY.Canonical

open Geometry

theorem build_P_rowShadow {values : List Nat} {mountain : Mountain}
    (hLegal : Legal values) (hBuild : build values = .ok mountain)
    {u p : (Frame.ofMountain mountain).Node}
    (hp : (Frame.ofMountain mountain).P u = some p) :
    Frame.RowShadow (Frame.ofMountain mountain) u p :=
  Frame.P_rowShadow (build_normal_of_legal hLegal hBuild) hp

theorem build_findParent_rowShadow {values : List Nat} {mountain : Mountain}
    (hLegal : Legal values) (hBuild : build values = .ok mountain)
    {u p : (Frame.ofMountain mountain).Node}
    (hp : findParent mountain (Frame.ref u) = .ok (Frame.ref p)) :
    Frame.RowShadow (Frame.ofMountain mountain) u p := by
  have hNormal := build_normal_of_legal hLegal hBuild
  exact Frame.P_rowShadow hNormal
    ((Executable.findParent_ref_iff hNormal.toOrdered u p).mp hp)

#print axioms build_findParent_rowShadow

end OmegaY.Canonical
