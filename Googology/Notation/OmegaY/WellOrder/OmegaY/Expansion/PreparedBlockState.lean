/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/PreparedBlockState.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/PreparedBlockState.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ColumnCopyData
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.PreparedExtension

set_option backward.do.legacy false

/-! A first-block invariant records only already available columns. Its
support witnesses are fresh reads in each copied column, and its reference
map is the fixed map selected at block start. No whole-block success is an
invariant field. -/

namespace OmegaY.Expansion

open Canonical

def CopiedMarkerRows {front : List Nat} {last : Nat} (p : Preparation front last)
    (references : List Ref) (sourceColumn : Nat) (column : Column) : Prop :=
  ∀ marker, BucketMem p.marked sourceColumn marker → ∀ current,
    Canonical.cellAt p.reduced marker = .ok current → ∀ target,
      referenceAt p.reduced references current.row = .ok target →
      (∃ (index : Nat) (cell : Cell), column[index]? = some cell ∧ cell.row = current.row) ∧
      (∃ (index : Nat) (cell : Cell), column[index]? = some cell ∧ cell.row = target)

structure PreparedBlockState {front : List Nat} {last : Nat} (p : Preparation front last)
    (references : List Ref) (next : Nat) (ambient : Mountain) : Prop where
  base_preserved : PreservesColumns p.reduced ambient
  ambient_valid : MountainValid ambient
  size_eq : ambient.size = next + (p.reduced.size - 1 - p.root.column)
  next_lower : p.root.column < next
  next_upper : next ≤ p.reduced.size
  copied_columns : ∀ sourceColumn, p.root.column < sourceColumn → sourceColumn < next →
    ∃ column, ambient[sourceColumn + (p.reduced.size - 1 - p.root.column)]? = some column ∧
      ColumnPowerSteps column ∧ CopiedMarkerRows p references sourceColumn column

theorem Preparation.initial_block_state {front : List Nat} {last : Nat}
    (p : Preparation front last) (references : List Ref) :
    PreparedBlockState p references (p.root.column + 1) p.reduced := by
  have hSize := build_size p.reduced_build
  simp only [List.length_append, List.length_singleton] at hSize
  have hRoot := p.root_before_last
  exact {
    base_preserved := fun _ _ => rfl
    ambient_valid := p.reduced_valid
    size_eq := by omega
    next_lower := by omega
    next_upper := by omega
    copied_columns := by intro column hLower hUpper; omega }

/-- A single verified output extends the invariant. Its validity, power
steps and row support are the local obligations supplied by the column
theorem; no execution of any later column is assumed. -/
theorem PreparedBlockState.push {front : List Nat} {last : Nat}
    {p : Preparation front last} {references : List Ref} {next : Nat} {ambient : Mountain}
    (s : PreparedBlockState p references next ambient) (hNext : next < p.reduced.size)
    {column : Column} (hValid : ColumnValid ambient ambient.size column)
    (hPower : ColumnPowerSteps column) (hRows : CopiedMarkerRows p references next column) :
    PreparedBlockState p references (next + 1) (ambient.push column) := by
  refine {
    base_preserved := s.base_preserved.trans (PreservesColumns.push ambient column)
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

#print axioms OmegaY.Expansion.Preparation.initial_block_state
#print axioms OmegaY.Expansion.PreparedBlockState.push
