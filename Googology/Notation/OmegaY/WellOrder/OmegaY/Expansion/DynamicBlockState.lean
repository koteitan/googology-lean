/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/DynamicBlockState.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/DynamicBlockState.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.BoundaryReferences
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ColumnCopyData

set_option backward.do.legacy false

/-! State inside an arbitrary copying block. The start mountain, its actual
last-column boundary, and its freshly selected reference map are fixed for
this block. Only columns already copied in this block supply inductive
output invariants; no completed-block execution is an assumption. -/

namespace OmegaY.Expansion

open Canonical

def DynamicCopiedMarkerRows {front : List Nat} {last : Nat} (p : Preparation front last)
    (start : Mountain) (references : List Ref) (sourceColumn : Nat) (column : Column) : Prop :=
  ∀ marker, BucketMem p.marked sourceColumn marker → ∀ current,
    Canonical.cellAt p.reduced marker = .ok current → ∀ target,
      referenceAt start references current.row = .ok target →
      (∃ (index : Nat) (cell : Cell), column[index]? = some cell ∧ cell.row = current.row) ∧
      (∃ (index : Nat) (cell : Cell), column[index]? = some cell ∧ cell.row = target)

structure DynamicBlockState {front : List Nat} {last : Nat} (p : Preparation front last)
    (block : Nat) (start : Mountain) (references : List Ref) (next : Nat)
    (ambient : Mountain) : Prop where
  base_preserved : PreservesColumns p.reduced start
  start_valid : MountainValid start
  start_size : start.size = p.root.column + 1 + block * (p.reduced.size - 1 - p.root.column)
  boundary_rows : RootRowsInColumn p start (start.size - 1)
  boundary_power : ∀ nodes, start[start.size - 1]? = some nodes → ColumnPowerSteps nodes
  reference_map : p.boundaries.mapM (below start (start.size - 1)) = .ok references
  start_preserved : PreservesColumns start ambient
  ambient_valid : MountainValid ambient
  size_eq : ambient.size = next + block * (p.reduced.size - 1 - p.root.column)
  next_lower : p.root.column < next
  next_upper : next ≤ p.reduced.size
  copied_columns : ∀ sourceColumn, p.root.column < sourceColumn → sourceColumn < next →
    ∃ column, ambient[sourceColumn + block * (p.reduced.size - 1 - p.root.column)]? = some column ∧
      ColumnPowerSteps column ∧ DynamicCopiedMarkerRows p start references sourceColumn column

theorem DynamicBlockState.init {front : List Nat} {last : Nat}
    {p : Preparation front last} {block : Nat} {start : Mountain}
    (hBase : PreservesColumns p.reduced start) (hValid : MountainValid start)
    (hSize : start.size = p.root.column + 1 + block * (p.reduced.size - 1 - p.root.column))
    (hRows : RootRowsInColumn p start (start.size - 1))
    (hPower : ∀ nodes, start[start.size - 1]? = some nodes → ColumnPowerSteps nodes)
    {references : List Ref}
    (hMap : p.boundaries.mapM (below start (start.size - 1)) = .ok references) :
    DynamicBlockState p block start references (p.root.column + 1) start := by
  have hBuildSize := build_size p.reduced_build
  simp only [List.length_append, List.length_singleton] at hBuildSize
  have hRoot := p.root_before_last
  exact {
    base_preserved := hBase
    start_valid := hValid
    start_size := hSize
    boundary_rows := hRows
    boundary_power := hPower
    reference_map := hMap
    start_preserved := fun _ _ => rfl
    ambient_valid := hValid
    size_eq := hSize
    next_lower := by omega
    next_upper := by omega
    copied_columns := by intro column hLower hUpper; omega }

/-- The actual map for this particular boundary mountain is constructed
here. It is not identified with a reference map from an earlier block. -/
theorem Preparation.dynamic_block_init {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {block : Nat} {start : Mountain}
    (hBase : PreservesColumns p.reduced start) (hValid : MountainValid start)
    (hSize : start.size = p.root.column + 1 + block * (p.reduced.size - 1 - p.root.column))
    (hRows : RootRowsInColumn p start (start.size - 1))
    (hPower : ∀ nodes, start[start.size - 1]? = some nodes → ColumnPowerSteps nodes) :
    ∃ references,
      p.boundaries.mapM (below start (start.size - 1)) = .ok references ∧
      DynamicBlockState p block start references (p.root.column + 1) start := by
  obtain ⟨references, hMap, _⟩ := hRows.references hValid hLast
  exact ⟨references, hMap, DynamicBlockState.init hBase hValid hSize hRows hPower hMap⟩

theorem DynamicBlockState.base_ambient {front : List Nat} {last : Nat}
    {p : Preparation front last} {block : Nat} {start : Mountain} {references : List Ref}
    {next : Nat} {ambient : Mountain} (s : DynamicBlockState p block start references next ambient) :
    PreservesColumns p.reduced ambient := s.base_preserved.trans s.start_preserved

theorem DynamicBlockState.referenceAt_preserved {front : List Nat} {last : Nat}
    {p : Preparation front last} {block : Nat} {start : Mountain} {references : List Ref}
    {next : Nat} {ambient : Mountain} (s : DynamicBlockState p block start references next ambient)
    (row : Row) : referenceAt ambient references row = referenceAt start references row :=
  s.start_preserved.referenceAt (RootRowsInColumn.references_valid s.boundary_rows s.reference_map) row

theorem DynamicBlockState.push {front : List Nat} {last : Nat}
    {p : Preparation front last} {block : Nat} {start : Mountain} {references : List Ref}
    {next : Nat} {ambient : Mountain} (s : DynamicBlockState p block start references next ambient)
    (hNext : next < p.reduced.size) {column : Column}
    (hValid : ColumnValid ambient ambient.size column) (hPower : ColumnPowerSteps column)
    (hRows : DynamicCopiedMarkerRows p start references next column) :
    DynamicBlockState p block start references (next + 1) (ambient.push column) := by
  refine {
    base_preserved := s.base_preserved
    start_valid := s.start_valid
    start_size := s.start_size
    boundary_rows := s.boundary_rows
    boundary_power := s.boundary_power
    reference_map := s.reference_map
    start_preserved := s.start_preserved.trans (PreservesColumns.push ambient column)
    ambient_valid := s.ambient_valid.push hValid
    size_eq := by simp only [Array.size_push, s.size_eq]; omega
    next_lower := by have := s.next_lower; omega
    next_upper := by omega
    copied_columns := ?_ }
  intro sourceColumn hLower hUpper
  by_cases he : sourceColumn = next
  · subst sourceColumn
    exact ⟨column, by rw [← s.size_eq]; simp, hPower, hRows⟩
  · have hPrevious : sourceColumn < next := by omega
    obtain ⟨oldColumn, hOldColumn, hOldPower, hOldRows⟩ := s.copied_columns sourceColumn hLower hPrevious
    exact ⟨oldColumn, (PreservesColumns.push ambient column).column_read hOldColumn,
      hOldPower, hOldRows⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.dynamic_block_init
#print axioms OmegaY.Expansion.DynamicBlockState.referenceAt_preserved
#print axioms OmegaY.Expansion.DynamicBlockState.push
