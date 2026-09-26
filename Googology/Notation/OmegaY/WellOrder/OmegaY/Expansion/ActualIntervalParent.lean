/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualIntervalParent.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/ActualIntervalParent.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ActualRootInterval
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.DynamicMovedParent

set_option backward.do.legacy false

/-!
# Parent selection from an actual reference-interval certificate

The source root and all interval controls are supplied by ActualRootInterval.
Parents at the root column are selected in the existing block boundary;
strict-right parents are selected in columns recovered from actual history.
This proves parent selection and its B row equation. It does not assert that
the current child column has already been copied or reconstructed.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- The root column has no other source node inside its actual reference
interval: any higher node would cross the proved root-upper barrier. -/
theorem ActualRootInterval.eq_root_of_inside_column
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start ambient : Mountain} {references : List Ref} {index : Nat} {sourceRow : Row}
    (a : ActualRootInterval p start ambient references index sourceRow)
    {node : (Frame.ofMountain p.reduced).Node}
    (hInside : Frame.RootInterval (Frame.ofMountain p.reduced) a.root
      (Row.bump sourceRow a.degree) node)
    (hColumn : node.1.val = p.root.column) : node = a.root := by
  have hOrdered := p.reduced_valid.toOrdered
  have hRootColumn : a.root.1.val = p.root.column := congrArg Ref.column a.root_ref
  have hRow : (Frame.ofMountain p.reduced).height node =
      (Frame.ofMountain p.reduced).height a.root := by
    apply le_antisymm _ hInside.2.1
    apply le_of_not_gt
    intro hAbove
    have hStrict := hInside.column_lt_of_height_lt hOrdered a.root_upper_barrier hAbove
    rw [hColumn, hRootColumn] at hStrict
    exact (lt_irrefl _) hStrict
  exact Frame.node_eq_of_column_height hOrdered (Fin.ext (hColumn.trans hRootColumn.symm)) hRow

/-- Every parent at or to the right of the bad-root column is selected at
its lifted row in the actual ambient mountain. The certificate discharges
root realness, positive degree, prefix membership, source upper barrier,
reference query, and the target cap; no current-child output is assumed. -/
theorem DynamicBlockState.actual_interval_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {index : Nat} {sourceRow : Row}
    (a : ActualRootInterval p start ambient references index sourceRow)
    (hRaised : sourceRow < a.target.row)
    {child parent childUpper : (Frame.ofMountain p.reduced).Node}
    (hChild : Frame.RootInterval (Frame.ofMountain p.reduced) a.root
      (Row.bump sourceRow a.degree) child)
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next)
    (hChildUpper : (Frame.ofMountain p.reduced).upper child = some childUpper)
    (hParentColumn : p.root.column ≤ parent.1.val) :
    ∃ (actualRef : Ref) (actualParent : Cell),
      actualRef.column = parent.1.val + block * (p.reduced.size - 1 - p.root.column) ∧
      below ambient (parent.1.val + block * (p.reduced.size - 1 - p.root.column))
        (Row.lift sourceRow a.target.row ((Frame.ofMountain p.reduced).height childUpper)) = .ok actualRef ∧
      Canonical.cellAt ambient actualRef = .ok actualParent ∧
      actualParent.row = Row.lift sourceRow a.target.row ((Frame.ofMountain p.reduced).height parent) ∧
      Row.lift sourceRow a.target.row ((Frame.ofMountain p.reduced).height childUpper) =
        Row.B (Row.lift sourceRow a.target.row ((Frame.ofMountain p.reduced).height child))
          actualParent.row := by
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  have hRootColumn : a.root.1.val = p.root.column := congrArg Ref.column a.root_ref
  have hRootIndex : a.root.2.val ≤ p.root.index :=
    (congrArg Ref.index a.root_ref).trans_le a.root_prefix
  have hDegree := a.raised_degree hRaised
  have hBarrier : ∀ upper, F.upper a.root = some upper →
      Row.bump (F.height a.root) a.degree ≤ F.height upper := by
    simpa only [F, a.root_row] using a.root_upper_barrier
  have hChildInside : Frame.RootInterval F a.root (Row.bump (F.height a.root) a.degree) child := by
    simpa only [F, a.root_row] using hChild
  have hParentInside : Frame.RootInterval F a.root (Row.bump sourceRow a.degree) parent := by
    have hInside := (Frame.root_interval_parent_iff_column hNormal a.root_real
      (Row.bump_strictMono_exponent _ hDegree) hBarrier hParent hChildInside).mpr
        (by rw [hRootColumn]; exact hParentColumn)
    simpa only [F, a.root_row] using hInside
  have hChildLow : sourceRow ≤ F.height child := by simpa only [F, a.root_row] using hChild.2.1
  have hParentLow : sourceRow ≤ F.height parent := by simpa only [F, a.root_row] using hParentInside.2.1
  have hSourceB : F.height childUpper = Row.B (F.height child) (F.height parent) :=
    (Frame.aboveHeight_of_upper hChildUpper).symm.trans (hNormal.above_row hParent)
  have hB : Row.lift sourceRow a.target.row (F.height childUpper) =
      Row.B (Row.lift sourceRow a.target.row (F.height child))
        (Row.lift sourceRow a.target.row (F.height parent)) := by
    rw [hSourceB]
    exact Row.lift_B hChildLow hParentLow
  rcases lt_or_eq_of_le hParentColumn with hStrict | hEqual
  · have hExecutable := (Executable.findParent_ref_iff hNormal.toOrdered child parent).mpr hParent
    have hTarget : referenceAt start references (F.height a.root) = .ok a.target.row := by
      simpa only [F, a.root_row] using a.start_query
    have hTargetCap : a.target.row < Row.bump (F.height a.root) a.degree := by
      simpa only [F, a.root_row] using a.target_below
    obtain ⟨newIndex, actualParent, hBelow, hRead, hRow⟩ :=
      s.below_moved_parent history hLast a.root_real hDegree hRootColumn hRootIndex hBarrier
        hExecutable hChildInside hChildColumn hChildUpper hStrict hTarget hTargetCap
    rw [a.root_row] at hBelow hRow
    exact ⟨⟨parent.1.val + block * (p.reduced.size - 1 - p.root.column), newIndex⟩,
      actualParent, rfl, hBelow, hRead, hRow,
      hB.trans (congrArg (Row.B (Row.lift sourceRow a.target.row (F.height child))) hRow.symm)⟩
  · have hParentEq : parent = a.root := a.eq_root_of_inside_column hParentInside hEqual.symm
    have hParentRow : F.height parent = sourceRow := by rw [hParentEq]; exact a.root_row
    obtain ⟨nodes, hNodes, hTargetRead⟩ := cellAt_ok_iff.mp a.target_ambient_read
    rw [a.reference_column] at hNodes
    have hSelect := (below_boundary_root_parent hNodes a.ambient_below hTargetRead
      a.target_lower hChildLow hChild.2.2).1
    have hCeiling : Row.lift sourceRow a.target.row (F.height childUpper) =
        Row.lift sourceRow a.target.row (Row.B (F.height child) sourceRow) := by
      rw [hSourceB, hParentRow]
    have hColumn : parent.1.val + block * (p.reduced.size - 1 - p.root.column) = start.size - 1 := by
      rw [← hEqual]
      exact s.boundary_copy_index
    have hRow : a.target.row = Row.lift sourceRow a.target.row (F.height parent) := by
      rw [hParentRow, Row.lift_at_root]
    refine ⟨a.reference, a.target, a.reference_column.trans hColumn.symm, ?_,
      a.target_ambient_read, hRow,
      hB.trans (congrArg (Row.B (Row.lift sourceRow a.target.row (F.height child))) hRow.symm)⟩
    rw [hColumn, hCeiling]
    exact hSelect

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ActualRootInterval.eq_root_of_inside_column
#print axioms OmegaY.Expansion.DynamicBlockState.actual_interval_parent
