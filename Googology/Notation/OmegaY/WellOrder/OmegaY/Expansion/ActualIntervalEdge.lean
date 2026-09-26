/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualIntervalEdge.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/ActualIntervalEdge.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ActualMovedEdge
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ActualFixedParent

set_option backward.do.legacy false

/-!
# Actual interval edges, with fixed and moved parents unified

The copied candidate's row and stored reference are obtained from the
executable copyEdge call. A separate interface transfers this geometry to
actual adjacent output reads when their copy/backfill provenance is given.
Adjacency provenance and the child's source-interval membership remain
explicit; numerical first-smaller recovery is not asserted here.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- Every successful call retains its requested row, irrespective of the
fixed/moved endpoint branch or of the source's numerical value. -/
theorem copyEdge_return_row {mountain : Mountain} {source : Ref} {shift rootColumn : Nat}
    {row : Row} {copied : Cell}
    (hRun : copyEdge mountain source shift rootColumn row = .ok copied) : copied.row = row := by
  cases hSource : lookup mountain source with
  | error error => simp [copyEdge, hSource] at hRun
  | ok sourceCell =>
    by_cases hZero : sourceCell.row = 0
    · have he : (⟨row, 0, none⟩ : Cell) = copied := by
        simpa [copyEdge, hSource, hZero] using hRun
      exact congrArg Cell.row he.symm
    · cases hLeft : leftOf sourceCell with
      | error error => simp [copyEdge, hSource, hZero, hLeft] at hRun
      | ok oldParent =>
        by_cases hFixed : oldParent.column < rootColumn
        · by_cases hDestination : oldParent.column < source.column + shift
          · have he : (⟨row, 0, some oldParent⟩ : Cell) = copied := by
              simpa [copyEdge, hSource, hZero, hLeft, hFixed, Nat.not_le_of_gt hDestination] using hRun
            exact congrArg Cell.row he.symm
          · simp [copyEdge, hSource, hZero, hLeft, hFixed, Nat.le_of_not_gt hDestination] at hRun
        · cases hBelow : below mountain (oldParent.column + shift) row with
          | error error => simp [copyEdge, hSource, hZero, hLeft, hFixed, hBelow] at hRun
          | ok parent =>
            by_cases hDestination : parent.column < source.column + shift
            · have he : (⟨row, 0, some parent⟩ : Cell) = copied := by
                simpa [copyEdge, hSource, hZero, hLeft, hFixed, hBelow, Nat.not_le_of_gt hDestination] using hRun
              exact congrArg Cell.row he.symm
            · simp [copyEdge, hSource, hZero, hLeft, hFixed, hBelow, Nat.le_of_not_gt hDestination] at hRun

/-- One actual source interval gives the exact executable edge for every
source numerical father, with the program's own column split retained. -/
theorem DynamicBlockState.copyEdge_interval_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {index : Nat} {sourceRow : Row}
    (a : ActualRootInterval p start ambient references index sourceRow)
    (hRaised : sourceRow < a.target.row)
    {child parent upper : (Frame.ofMountain p.reduced).Node}
    (hChild : Frame.RootInterval (Frame.ofMountain p.reduced) a.root
      (Row.bump sourceRow a.degree) child)
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next)
    (hUpper : (Frame.ofMountain p.reduced).upper child = some upper) :
    ∃ (copied : Cell) (actualRef : Ref) (actualParent : Cell),
      copyEdge ambient (Frame.ref upper) (block * (p.reduced.size - 1 - p.root.column)) p.root.column
        (Row.lift sourceRow a.target.row ((Frame.ofMountain p.reduced).height upper)) = .ok copied ∧
      copied.row = Row.lift sourceRow a.target.row ((Frame.ofMountain p.reduced).height upper) ∧
      copied.value = 0 ∧ copied.left = some actualRef ∧
      actualRef.column = (if parent.1.val < p.root.column then parent.1.val
        else parent.1.val + block * (p.reduced.size - 1 - p.root.column)) ∧
      Canonical.cellAt ambient actualRef = .ok actualParent ∧
      actualParent.row = (Frame.ofMountain p.reduced).intervalParentRow a.root a.target.row parent ∧
      copied.row = Row.B (Row.lift sourceRow a.target.row ((Frame.ofMountain p.reduced).height child))
        actualParent.row := by
  have hRootColumn : a.root.1.val = p.root.column := congrArg Ref.column a.root_ref
  by_cases hFixed : parent.1.val < p.root.column
  · have hNormal := build_normal_of_success p.reduced_build
    have hExecutable := (Executable.findParent_ref_iff hNormal.toOrdered child parent).mpr hParent
    obtain ⟨hCopy, hRead, hB, _⟩ := s.copyEdge_fixed_interval_parent a hRaised hExecutable hChild hUpper hFixed
    have hCopiedRow := copyEdge_return_row hCopy
    refine ⟨⟨(Frame.ofMountain p.reduced).height upper, 0, some (Frame.ref parent)⟩,
      Frame.ref parent, (Frame.ofMountain p.reduced).cell parent,
      hCopy, hCopiedRow, rfl, rfl, ?_, hRead, ?_, hB⟩
    · simp only [Frame.ref, if_pos hFixed]
    · simp only [Frame.intervalParentRow, hRootColumn, if_pos hFixed, Frame.height]
  · obtain ⟨copied, actualRef, actualParent, hCopy, hRow, hValue, hLeft, hColumn, hRead,
        hParentRow, hB⟩ := s.copyEdge_moved_interval_parent history hLast a hRaised hChild
          hParent hChildColumn hUpper (Nat.le_of_not_gt hFixed)
    exact ⟨copied, actualRef, actualParent, hCopy, hRow, hValue, hLeft,
      by simpa only [if_neg hFixed] using hColumn, hRead,
      by simpa only [Frame.intervalParentRow, hRootColumn, if_neg hFixed, a.root_row] using hParentRow,
      hB⟩

/-- Actual adjacent reads plus real copy/backfill shape provenance transfer
the exact stored-parent geometry to the returned mountain. The parent is
derived from copyEdge; no desired parent or first-smaller result is assumed. -/
theorem DynamicBlockState.returned_interval_edge
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {index : Nat} {sourceRow : Row}
    (a : ActualRootInterval p start ambient references index sourceRow)
    (hRaised : sourceRow < a.target.row)
    {child parent upper : (Frame.ofMountain p.reduced).Node}
    (hChild : Frame.RootInterval (Frame.ofMountain p.reduced) a.root
      (Row.bump sourceRow a.degree) child)
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next)
    (hUpper : (Frame.ofMountain p.reduced).upper child = some upper)
    {column : Column} {position : Nat} {lowerOutput upperOutput candidate : Cell}
    (hLowerRead : column[position]? = some lowerOutput)
    (hUpperRead : column[position + 1]? = some upperOutput)
    (hCopy : copyEdge ambient (Frame.ref upper) (block * (p.reduced.size - 1 - p.root.column)) p.root.column
      (Row.lift sourceRow a.target.row ((Frame.ofMountain p.reduced).height upper)) = .ok candidate)
    (hShape : SameShape candidate upperOutput)
    (hLowerRow : lowerOutput.row = Row.lift sourceRow a.target.row ((Frame.ofMountain p.reduced).height child)) :
    ∃ (actualRef : Ref) (actualParent : Cell),
      Canonical.cellAt (ambient.push column) ⟨ambient.size, position⟩ = .ok lowerOutput ∧
      Canonical.cellAt (ambient.push column) ⟨ambient.size, position + 1⟩ = .ok upperOutput ∧
      upperOutput.left = some actualRef ∧
      actualRef.column = (if parent.1.val < p.root.column then parent.1.val
        else parent.1.val + block * (p.reduced.size - 1 - p.root.column)) ∧
      Canonical.cellAt (ambient.push column) actualRef = .ok actualParent ∧
      actualParent.row = (Frame.ofMountain p.reduced).intervalParentRow a.root a.target.row parent ∧
      upperOutput.row = Row.B lowerOutput.row actualParent.row := by
  obtain ⟨copied, actualRef, actualParent, hActualCopy, _, _, hLeft, hColumn, hRead, hParentRow, hB⟩ :=
    s.copyEdge_interval_parent history hLast a hRaised hChild hParent hChildColumn hUpper
  have he : copied = candidate := Except.ok.inj (hActualCopy.symm.trans hCopy)
  subst copied
  obtain ⟨nodes, hNodes, hIndex⟩ := cellAt_ok_iff.mp hRead
  have hPushRead : Canonical.cellAt (ambient.push column) actualRef = .ok actualParent :=
    cellAt_ok_iff.mpr ⟨nodes, (PreservesColumns.push ambient column).column_read hNodes, hIndex⟩
  refine ⟨actualRef, actualParent,
    cellAt_ok_iff.mpr ⟨column, by simp, hLowerRead⟩,
    cellAt_ok_iff.mpr ⟨column, by simp, hUpperRead⟩,
    hShape.2.symm.trans hLeft, hColumn, hPushRead, hParentRow, ?_⟩
  rw [hLowerRow]
  exact hShape.1.symm.trans hB

end OmegaY.Expansion

#print axioms OmegaY.Expansion.copyEdge_return_row
#print axioms OmegaY.Expansion.DynamicBlockState.copyEdge_interval_parent
#print axioms OmegaY.Expansion.DynamicBlockState.returned_interval_edge
