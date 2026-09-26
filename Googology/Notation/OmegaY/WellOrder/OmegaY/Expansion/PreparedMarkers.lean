/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/PreparedMarkers.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/PreparedMarkers.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Domain
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.Preparation
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.CanonicalMarkers
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.MarkerCompleteness
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.MarkerOrder

set_option backward.do.legacy false

/-! Readiness facts for the actual prepared marker array. No additional
legality, successful enumeration, or phantom-chain hypothesis is needed:
the Preparation record already contains the two actual build equations.
These facts concern the initial reduced mountain, not arbitrary copies. -/

namespace OmegaY.Expansion

open Canonical

theorem Preparation.reduced_normal {front : List Nat} {last : Nat}
    (p : Preparation front last) : (Geometry.Frame.ofMountain p.reduced).Normal :=
  build_normal_of_success p.reduced_build

theorem Preparation.root_valid {front : List Nat} {last : Nat}
    (p : Preparation front last) : ValidRef p.reduced p.root :=
  ⟨p.rootCell, cellAt_ok_iff.mp p.restored_root⟩

theorem Preparation.marker_iff {front : List Nat} {last : Nat}
    (p : Preparation front last) {bucket : Nat} {entry : Ref} :
    BucketMem p.marked bucket entry ↔ MarkerSpec p.reduced p.root bucket entry :=
  markers_member_iff
    (weakLocal_of_ordered p.reduced_valid.toOrdered p.reduced_valid.left_sources)
    p.root_valid p.markers_built

theorem Preparation.phantom_marker {front : List Nat} {last : Nat}
    (p : Preparation front last) {column : Nat}
    (hright : p.root.column < column) (hc : column < p.reduced.size) :
    BucketMem p.marked column ⟨column, 0⟩ :=
  markers_phantom_mem
    (weakLocal_of_ordered p.reduced_valid.toOrdered p.reduced_valid.left_sources)
    p.root_valid p.markers_built
    (build_phantomChain (build_success_legal p.reduced_build) p.reduced_build) hright hc

theorem Preparation.markers_ordered {front : List Nat} {last : Nat}
    (p : Preparation front last) (bucket : Nat) :
    (p.marked[bucket]?.getD []).Pairwise (fun a b => b.index < a.index) ∧
      (p.marked[bucket]?.getD []).Nodup := by
  have hlocal := weakLocal_of_ordered p.reduced_valid.toOrdered p.reduced_valid.left_sources
  exact ⟨markers_bucket_strict_index p.reduced_valid.toOrdered hlocal
      p.root_valid p.markers_built bucket,
    markers_bucket_nodup p.reduced_valid.toOrdered hlocal
      p.root_valid p.markers_built bucket⟩

/-- The marker traversal in every right-hand source column ends at its
phantom. This includes order, not only the phantom's membership. -/
theorem Preparation.markers_last_phantom {front : List Nat} {last : Nat}
    (p : Preparation front last) {column : Nat}
    (hright : p.root.column < column) (hc : column < p.reduced.size) :
    (p.marked[column]?.getD []).getLast? = some ⟨column, 0⟩ := by
  have hmem := p.phantom_marker hright hc
  have horder := (p.markers_ordered column).1
  change (⟨column, 0⟩ : Ref) ∈ p.marked[column]?.getD [] at hmem
  obtain ⟨frontRefs, tailRefs, he, _⟩ := List.eq_append_cons_of_mem hmem
  rw [he] at horder ⊢
  have htail : tailRefs = [] := by
    have hrest := (List.pairwise_append.mp horder).2.1
    have hsmall := (List.pairwise_cons.mp hrest).1
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro entry hentry
    have hneg := hsmall entry hentry
    exact Nat.not_lt_zero entry.index hneg
  simp [htail]

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.marker_iff
#print axioms OmegaY.Expansion.Preparation.phantom_marker
#print axioms OmegaY.Expansion.Preparation.markers_last_phantom
