/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/PreparedBoundaries.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/PreparedBoundaries.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.RootGeometry
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ReducedRootSupport
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.BoundarySelection

set_option backward.do.legacy false

/-! The actual initial boundary list and its successful reference selection.
Its formula is the expression used by expandDiagram after reading the original
root column. The statements concern the initial decremented mountain only. -/

namespace OmegaY.Expansion

open Canonical

def Preparation.boundaries {front : List Nat} {last : Nat}
    (p : Preparation front last) : List Row :=
  p.lastTop.row ::
    (((p.initial[p.root.column]?.getD #[]).toList.take (p.root.index + 1)).reverse.filterMap
      fun cell => if cell.row = 0 then none else some cell.row)

/-- Using the actual successful column read gives precisely the boundary
expression occurring in the executable expansion branch. -/
theorem Preparation.boundaries_of_column {front : List Nat} {last : Nat}
    (p : Preparation front last) {rootColumn : Column}
    (hColumn : p.initial[p.root.column]? = some rootColumn) :
    p.boundaries = p.lastTop.row ::
      ((rootColumn.toList.take (p.root.index + 1)).reverse.filterMap
        fun cell => if cell.row = 0 then none else some cell.row) := by
  simp only [Preparation.boundaries, hColumn, Option.getD_some]

theorem Preparation.boundaries_positive {front : List Nat} {last : Nat}
    (p : Preparation front last) (hlast : 1 < last) :
    ∀ row ∈ p.boundaries, 0 < row := by
  intro row hrow
  rcases List.mem_cons.mp hrow with he | htail
  · subst row
    exact lt_trans Row.zero_lt_one (p.top_row_gt_one hlast)
  · obtain ⟨cell, _hmem, hmap⟩ := List.mem_filterMap.mp htail
    by_cases hz : cell.row = 0
    · simp [hz] at hmap
    · have he : cell.row = row := by simpa [hz] using hmap
      subst row
      exact lt_of_le_of_ne (Row.zero_le cell.row) (Ne.symm hz)

theorem Preparation.reduced_last_exists {front : List Nat} {last : Nat}
    (p : Preparation front last) : p.reduced.size - 1 < p.reduced.size := by
  have hs := build_size p.reduced_build
  simp only [List.length_append, List.length_singleton] at hs
  omega

/-- The first copy block's entire reference-selection map succeeds, with an
exact pairing between its boundary list and the actual selected references. -/
theorem Preparation.initial_references {front : List Nat} {last : Nat}
    (p : Preparation front last) (hlast : 1 < last) :
    ∃ references,
      p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references ∧
      List.Forall₂ (fun ceiling ref => below p.reduced (p.reduced.size - 1) ceiling = .ok ref)
        p.boundaries references :=
  boundary_references_total p.reduced_valid p.reduced_last_exists p.boundaries
    (p.boundaries_positive hlast)

/-- The exact support transferred into the reduced boundary column prevents
strict-below selection from falling beneath a supplied real root-prefix row. -/
theorem Preparation.reference_above_root_row {front : List Nat} {last : Nat}
    (p : Preparation front last) (hlast : 1 < last)
    (w : (Geometry.Frame.ofMountain p.initial).Node) (hwReal : Geometry.Frame.Real w)
    (hwColumn : w.1.val = p.root.column)
    (hwRow : (Geometry.Frame.ofMountain p.initial).height w ≤ p.rootCell.row)
    {ceiling : Row} (hCeiling : (Geometry.Frame.ofMountain p.initial).height w < ceiling) :
    ∃ (found : Ref) (foundCell : Cell),
      below p.reduced (p.reduced.size - 1) ceiling = .ok found ∧
      Canonical.cellAt p.reduced found = .ok foundCell ∧
      (Geometry.Frame.ofMountain p.initial).height w ≤ foundCell.row ∧
      foundCell.row < ceiling := by
  obtain ⟨v, _hvReal, hvColumn, hvRow⟩ := p.reduced_root_row_support hlast w hwReal hwColumn hwRow
  have hLast : front.length = p.reduced.size - 1 := by
    have hs := build_size p.reduced_build
    simp only [List.length_append, List.length_singleton] at hs
    omega
  have hBound : ((Geometry.Frame.ofMountain p.reduced).cell v).row < ceiling :=
    hvRow.trans_lt hCeiling
  obtain ⟨found, foundCell, hFound, hRead, _hColumn, hAbove, hBelow⟩ :=
    below_between p.reduced_valid (cellAt_of_frame_node p.reduced v) hBound
  have hFoundColumn : (Geometry.Frame.ref v).column = p.reduced.size - 1 :=
    hvColumn.trans hLast
  refine ⟨found, foundCell, ?_, hRead, ?_, hBelow⟩
  · simpa only [hFoundColumn] using hFound
  · change (Geometry.Frame.ofMountain p.reduced).height v ≤ foundCell.row at hAbove
    simpa only [hvRow] using hAbove

/-- In particular the first reference, selected below the old top, is at
least as high as the actual root. This supplies a qualifying reference for
every initial marker whose row is at or below that root. -/
theorem Preparation.initial_reference_floor {front : List Nat} {last : Nat}
    (p : Preparation front last) (hlast : 1 < last) :
    ∃ (found : Ref) (foundCell : Cell),
      below p.reduced (p.reduced.size - 1) p.lastTop.row = .ok found ∧
      Canonical.cellAt p.reduced found = .ok foundCell ∧
      p.rootCell.row ≤ foundCell.row ∧ foundCell.row < p.lastTop.row := by
  obtain ⟨g⟩ := p.root_geometry hlast
  have hRootRow : (Geometry.Frame.ofMountain p.initial).height g.rootNode = p.rootCell.row :=
    congrArg Cell.row g.root_cell
  have hRootColumn : g.rootNode.1.val = p.root.column := congrArg Ref.column g.root_ref
  have h := p.reference_above_root_row hlast g.rootNode g.root_real hRootColumn hRootRow.le
    (hRootRow.trans_lt (p.root_row_lt_top hlast))
  simpa only [hRootRow] using h

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.boundaries_positive
#print axioms OmegaY.Expansion.Preparation.initial_references
#print axioms OmegaY.Expansion.Preparation.initial_reference_floor
