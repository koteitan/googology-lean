/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Canonical/RowSupport.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Canonical/RowSupport.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.RowSupport
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Normal

set_option backward.do.legacy false

/-!
# Row support in actual successful legal-input builds

The local normality certificate is supplied by the actual construction
theorem. The final two corollaries also use the established equivalence of
the executable searches with Frame.Q and Frame.P.
-/

namespace OmegaY.Canonical

open Geometry

theorem build_Q_rowsBelow {values : List Nat} {mountain : Mountain}
    (hLegal : Legal values) (hBuild : build values = .ok mountain)
    {u q : (Frame.ofMountain mountain).Node} (hu : Frame.Real u)
    (hQ : (Frame.ofMountain mountain).Q u = some q) :
    (Frame.ofMountain mountain).rowsBelow q ⊆ (Frame.ofMountain mountain).rowsBelow u :=
  Frame.Q_rowsBelow (build_normal_of_legal hLegal hBuild) hu hQ

theorem build_P_rowsBelow {values : List Nat} {mountain : Mountain}
    (hLegal : Legal values) (hBuild : build values = .ok mountain)
    {u p : (Frame.ofMountain mountain).Node}
    (hP : (Frame.ofMountain mountain).P u = some p) :
    (Frame.ofMountain mountain).rowsBelow p ⊆ (Frame.ofMountain mountain).rowsBelow u :=
  Frame.P_rowsBelow (build_normal_of_legal hLegal hBuild) hP

theorem build_nextCandidate_rowsBelow {values : List Nat} {mountain : Mountain}
    (hLegal : Legal values) (hBuild : build values = .ok mountain)
    {u q : (Frame.ofMountain mountain).Node} (hu : Frame.Real u)
    (hNext : nextCandidate mountain (Frame.ref u) = .ok (Frame.ref q)) :
    (Frame.ofMountain mountain).rowsBelow q ⊆ (Frame.ofMountain mountain).rowsBelow u := by
  have hNormal := build_normal_of_legal hLegal hBuild
  exact Frame.Q_rowsBelow hNormal hu
    ((Executable.nextCandidate_ref_iff hNormal.toOrdered u q).mp hNext)

theorem build_findParent_rowsBelow {values : List Nat} {mountain : Mountain}
    (hLegal : Legal values) (hBuild : build values = .ok mountain)
    {u p : (Frame.ofMountain mountain).Node}
    (hParent : findParent mountain (Frame.ref u) = .ok (Frame.ref p)) :
    (Frame.ofMountain mountain).rowsBelow p ⊆ (Frame.ofMountain mountain).rowsBelow u := by
  have hNormal := build_normal_of_legal hLegal hBuild
  exact Frame.P_rowsBelow hNormal
    ((Executable.findParent_ref_iff hNormal.toOrdered u p).mp hParent)

/-- Explicit actual-node witnesses for the row-set inclusion. Row equality
does not assert equality of values or of stored/numerical parents. -/
theorem build_findParent_row_witness {values : List Nat} {mountain : Mountain}
    (hLegal : Legal values) (hBuild : build values = .ok mountain)
    {u p w : (Frame.ofMountain mountain).Node}
    (hParent : findParent mountain (Frame.ref u) = .ok (Frame.ref p))
    (hwReal : Frame.Real w) (hwColumn : w.1 = p.1)
    (hwHeight : (Frame.ofMountain mountain).height w ≤ (Frame.ofMountain mountain).height p) :
    ∃ v : (Frame.ofMountain mountain).Node,
      Frame.Real v ∧ v.1 = u.1 ∧
      (Frame.ofMountain mountain).height v ≤ (Frame.ofMountain mountain).height u ∧
      (Frame.ofMountain mountain).height v = (Frame.ofMountain mountain).height w := by
  have hOrdered := (build_normal_of_legal hLegal hBuild).toOrdered
  have hIn := (Frame.mem_rowsBelow_iff_height hOrdered).mpr
    ⟨w, hwReal, hwColumn, hwHeight, rfl⟩
  exact (Frame.mem_rowsBelow_iff_height hOrdered).mp
    (build_findParent_rowsBelow hLegal hBuild hParent hIn)

#print axioms build_nextCandidate_rowsBelow
#print axioms build_findParent_rowsBelow
#print axioms build_findParent_row_witness

end OmegaY.Canonical
