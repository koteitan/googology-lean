/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/PreparedBoundaryParent.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/PreparedBoundaryParent.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.DynamicBlockState
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.BoundaryRootParent

set_option backward.do.legacy false

/-!
# Actual root-column parents at a dynamic block boundary

The reference map is the map selected in this block's start mountain.
Root-prefix support supplies its actual cap selection. Complete-column
preservation transports that very selection and cell to the current ambient
mountain. No success or existence assumption for a new target is needed.
-/

namespace OmegaY.Expansion

open Canonical

theorem DynamicBlockState.boundary_copy_index {front : List Nat} {last : Nat}
    {p : Preparation front last} {block : Nat} {start : Mountain} {references : List Ref}
    {next : Nat} {ambient : Mountain}
    (s : DynamicBlockState p block start references next ambient) :
    p.root.column + block * (p.reduced.size - 1 - p.root.column) = start.size - 1 := by
  have hSize := s.start_size
  omega

/-- Every actual original root-prefix row has a selected reference in the
current block boundary. Both its concrete read and the original cap search
are preserved in the current ambient mountain. -/
theorem DynamicBlockState.boundary_root_reference {front : List Nat} {last : Nat}
    {p : Preparation front last} {block : Nat} {start : Mountain} {references : List Ref}
    {next : Nat} {ambient : Mountain}
    (s : DynamicBlockState p block start references next ambient)
    (hLast : 1 < last) {nodes : Column}
    (hColumn : p.initial[p.root.column]? = some nodes)
    {index : Nat} {lower : Cell} (hLower : nodes[index]? = some lower)
    (hIndex : index ≤ p.root.index) :
    ∃ degree ref cell,
      ref.column = start.size - 1 ∧
      ref.column = p.root.column + block * (p.reduced.size - 1 - p.root.column) ∧
      Canonical.cellAt ambient ref = .ok cell ∧
      referenceAt ambient references lower.row = .ok cell.row ∧
      below ambient (start.size - 1) (Row.bump lower.row degree) = .ok ref ∧
      lower.row ≤ cell.row ∧ cell.row < Row.bump lower.row degree ∧
      Row.bump lower.row degree ≤ p.lastTop.row ∧
      ∀ higherIndex higherCell, index < higherIndex → higherIndex ≤ p.root.index →
        nodes[higherIndex]? = some higherCell → Row.bump lower.row degree ≤ higherCell.row := by
  obtain ⟨ceiling, degree, ref, cell, hPower, hTop, hBelow, hRead, hRefColumn,
      hReference, hLow, hHigh, hHigher⟩ :=
    RootRowsInColumn.root_interval s.boundary_rows s.start_valid hLast
      hColumn hLower hIndex s.reference_map
  obtain ⟨actualNodes, hActualNodes, hCell⟩ := cellAt_ok_iff.mp hRead
  have hAmbientRead : Canonical.cellAt ambient ref = .ok cell :=
    cellAt_ok_iff.mpr ⟨actualNodes, s.start_preserved.column_read hActualNodes, hCell⟩
  have hAmbientReference : referenceAt ambient references lower.row = .ok cell.row :=
    (s.referenceAt_preserved lower.row).trans hReference
  have hAmbientBelow : below ambient (start.size - 1) ceiling = .ok ref :=
    (s.start_preserved.below (RootRowsInColumn.column_lt s.boundary_rows) ceiling).trans hBelow
  refine ⟨degree, ref, cell, hRefColumn,
    hRefColumn.trans s.boundary_copy_index.symm, hAmbientRead, hAmbientReference,
    ?_, hLow, ?_, ?_, ?_⟩
  · simpa only [hPower] using hAmbientBelow
  · simpa only [hPower] using hHigh
  · simpa only [hPower] using hTop
  · simpa only [hPower] using hHigher

/-- A source parent at the root row is copied to the actual block boundary.
For every child row in this reference interval, the lifted upper row selects
the same concrete boundary reference and satisfies the transported B rule.
All choices are supplied by the actual preparation and dynamic block state. -/
theorem DynamicBlockState.boundary_root_parent {front : List Nat} {last : Nat}
    {p : Preparation front last} {block : Nat} {start : Mountain} {references : List Ref}
    {next : Nat} {ambient : Mountain}
    (s : DynamicBlockState p block start references next ambient)
    (hLast : 1 < last) {nodes : Column}
    (hColumn : p.initial[p.root.column]? = some nodes)
    {index : Nat} {lower : Cell} (hLower : nodes[index]? = some lower)
    (hIndex : index ≤ p.root.index) :
    ∃ degree ref cell,
      ref.column = start.size - 1 ∧
      ref.column = p.root.column + block * (p.reduced.size - 1 - p.root.column) ∧
      Canonical.cellAt ambient ref = .ok cell ∧
      referenceAt ambient references lower.row = .ok cell.row ∧
      below ambient (start.size - 1) (Row.bump lower.row degree) = .ok ref ∧
      lower.row ≤ cell.row ∧ cell.row < Row.bump lower.row degree ∧
      Row.bump lower.row degree ≤ p.lastTop.row ∧
      (∀ higherIndex higherCell, index < higherIndex → higherIndex ≤ p.root.index →
        nodes[higherIndex]? = some higherCell → Row.bump lower.row degree ≤ higherCell.row) ∧
      ∀ child, lower.row ≤ child → child < Row.bump lower.row degree →
        below ambient (start.size - 1)
          (Row.lift lower.row cell.row (Row.B child lower.row)) = .ok ref ∧
        Row.lift lower.row cell.row (Row.B child lower.row) =
          Row.B (Row.lift lower.row cell.row child) cell.row := by
  obtain ⟨degree, ref, cell, hRefColumn, hCopyColumn, hRead, hReference,
    hBelow, hLow, hHigh, hTop, hHigher⟩ :=
    s.boundary_root_reference hLast hColumn hLower hIndex
  refine ⟨degree, ref, cell, hRefColumn, hCopyColumn, hRead, hReference,
    hBelow, hLow, hHigh, hTop, hHigher, ?_⟩
  intro child hRootChild hChildCap
  obtain ⟨actualNodes, hActualNodes, hCell⟩ := cellAt_ok_iff.mp hRead
  rw [hRefColumn] at hActualNodes
  exact below_boundary_root_parent hActualNodes hBelow hCell hLow hRootChild hChildCap

#print axioms DynamicBlockState.boundary_copy_index
#print axioms DynamicBlockState.boundary_root_reference
#print axioms DynamicBlockState.boundary_root_parent

end OmegaY.Expansion
