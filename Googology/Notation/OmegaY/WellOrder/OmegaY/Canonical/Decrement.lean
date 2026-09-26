/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Canonical/Decrement.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Canonical/Decrement.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Normal
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.Decrement

set_option backward.do.legacy false

/-! The local decrement search and exact seam for actual legal-input builds.
The executable fixed-threshold search uses precisely its column-derived fuel.
The complete comparison of the original and decremented builds is not yet
asserted here. -/

namespace OmegaY.Canonical

open Geometry

theorem build_decrement_search {values : List Nat} {mountain : Mountain}
    (hLegal : Legal values) (hBuild : build values = .ok mountain)
    {u p : (Frame.ofMountain mountain).Node} {b : Nat}
    (hb : 1 < b) (hu : (Frame.ofMountain mountain).value u = b + 1)
    (hp : findParent mountain (Frame.ref u) = .ok (Frame.ref p)) :
    ∃ r : (Frame.ofMountain mountain).Node,
      findParentAux mountain b u.1.val (Frame.ref u) = .ok (Frame.ref r) ∧
      ((r = p ∧ (Frame.ofMountain mountain).value p < b) ∨
        ((Frame.ofMountain mountain).value p = b ∧
          findParent mountain (Frame.ref p) = .ok (Frame.ref r))) := by
  have hN := build_normal_of_legal hLegal hBuild
  have hP := (Executable.findParent_ref_iff hN.toOrdered u p).mp hp
  obtain ⟨r, hs, casesP⟩ := Frame.decrement_search hN hb hu hP
  have hoption := Executable.findParentAux_toOption hN.toOrdered b u.1.val u
  rw [hs, Option.map_some] at hoption
  have hrun : findParentAux mountain b u.1.val (Frame.ref u) = .ok (Frame.ref r) := by
    cases he : findParentAux mountain b u.1.val (Frame.ref u) with
    | error e => simp [he, Except.toOption] at hoption
    | ok found => simpa [he, Except.toOption] using hoption
  refine ⟨r, hrun, ?_⟩
  rcases casesP with hs | ⟨heq, hparent⟩
  · exact Or.inl hs
  · exact Or.inr ⟨heq, (Executable.findParent_ref_iff hN.toOrdered p r).mpr hparent⟩

theorem build_decrement_seam_cell {values : List Nat} {mountain : Mountain}
    (hLegal : Legal values) (hBuild : build values = .ok mountain)
    {u p r pplus : (Frame.ofMountain mountain).Node}
    (hp : findParent mountain (Frame.ref u) = .ok (Frame.ref p))
    (hr : findParent mountain (Frame.ref p) = .ok (Frame.ref r))
    (hplus : (Frame.ofMountain mountain).upper p = some pplus) :
    (⟨Row.B ((Frame.ofMountain mountain).height u) ((Frame.ofMountain mountain).height r),
      (Frame.ofMountain mountain).value p - (Frame.ofMountain mountain).value r,
      some (Frame.ref r)⟩ : Cell) = (Frame.ofMountain mountain).cell pplus := by
  have hN := build_normal_of_legal hLegal hBuild
  exact Frame.decrement_seam_cell hN
    ((Executable.findParent_ref_iff hN.toOrdered u p).mp hp)
    ((Executable.findParent_ref_iff hN.toOrdered p r).mp hr) hplus

end OmegaY.Canonical

#print axioms OmegaY.Canonical.build_decrement_search
#print axioms OmegaY.Canonical.build_decrement_seam_cell
