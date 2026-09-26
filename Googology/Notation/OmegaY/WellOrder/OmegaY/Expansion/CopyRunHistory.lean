/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/CopyRunHistory.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/CopyRunHistory.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.BlockTotal

set_option backward.do.legacy false

/-!
# Actual prior-column executions retained through a block

Power steps and marker rows alone do not recover how an earlier column was
copied. This history records the real prior state and run for each earlier
column, together with preservation into the current mountain. It is built
by the actual indexed loop, not assumed of a completed output.
-/

namespace OmegaY.Expansion

open Canonical

def CopyRunHistory {front : List Nat} {last : Nat} (p : Preparation front last)
    (block : Nat) (start : Mountain) (references : List Ref) (next : Nat)
    (ambient : Mountain) : Prop :=
  ∀ sourceColumn, p.root.column < sourceColumn → sourceColumn < next →
    ∃ before column,
      DynamicBlockState p block start references sourceColumn before ∧
      copyColumn before p.marked references sourceColumn
        (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column ∧
      PreservesColumns (before.push column) ambient

theorem CopyRunHistory.initial {front : List Nat} {last : Nat} (p : Preparation front last)
    (block : Nat) (start : Mountain) (references : List Ref) :
    CopyRunHistory p block start references (p.root.column + 1) start := by
  intro sourceColumn hLower hUpper
  omega

theorem CopyRunHistory.push {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start : Mountain} {references : List Ref} {next : Nat} {ambient : Mountain}
    (history : CopyRunHistory p block start references next ambient)
    (state : DynamicBlockState p block start references next ambient) {column : Column}
    (hRun : copyColumn ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column) :
    CopyRunHistory p block start references (next + 1) (ambient.push column) := by
  intro sourceColumn hLower hUpper
  by_cases he : sourceColumn = next
  · subst sourceColumn
    exact ⟨ambient, column, state, hRun, fun _ _ => rfl⟩
  · obtain ⟨before, oldColumn, hState, hOldRun, hPreserve⟩ :=
      history sourceColumn hLower (by omega)
    exact ⟨before, oldColumn, hState, hOldRun, hPreserve.trans (PreservesColumns.push ambient column)⟩

/-- The stored actual run determines the current read at the shifted source
index. No later column's value or geometry is inspected. -/
theorem CopyRunHistory.column_read {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start : Mountain} {references : List Ref} {next : Nat} {ambient : Mountain}
    (history : CopyRunHistory p block start references next ambient)
    {sourceColumn : Nat} (hLower : p.root.column < sourceColumn) (hUpper : sourceColumn < next) :
    ∃ before column,
      DynamicBlockState p block start references sourceColumn before ∧
      copyColumn before p.marked references sourceColumn
        (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column ∧
      PreservesColumns (before.push column) ambient ∧
      ambient[sourceColumn + block * (p.reduced.size - 1 - p.root.column)]? = some column := by
  obtain ⟨before, column, hState, hRun, hPreserve⟩ := history sourceColumn hLower hUpper
  refine ⟨before, column, hState, hRun, hPreserve, ?_⟩
  rw [← hState.size_eq]
  exact hPreserve.column_read (by simp)

/-- Every finite actual block returns a full history of its previous column
executions. This proof follows the unchanged offset loop with fresh boundary
references; it does not assume successful copied-column witnesses. -/
theorem BlockReady.copyBlock_with_history {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start : Mountain} (ready : BlockReady p block start) (hLast : 1 < last) :
    ∃ result references,
      OmegaY.Expansion.copyBlock start p.marked p.boundaries p.root.column
        (p.reduced.size - 1 - p.root.column) block = .ok result ∧
      BlockReady p (block + 1) result ∧
      p.boundaries.mapM (below start (start.size - 1)) = .ok references ∧
      DynamicBlockState p block start references p.reduced.size result ∧
      CopyRunHistory p block start references p.reduced.size result := by
  let width := p.reduced.size - 1 - p.root.column
  have hSize := build_size p.reduced_build
  simp only [List.length_append, List.length_singleton] at hSize
  have hRoot := p.root_before_last
  obtain ⟨references, hMap, hInitial⟩ := p.dynamic_block_init hLast ready.base_preserved
    ready.valid ready.size_eq ready.boundary_rows ready.boundary_power
  let body : Nat → Mountain → Result (ForInStep Mountain) := fun offset ambient => do
    let sourceColumn := p.root.column + offset + 1
    if ambient.size ≠ sourceColumn + block * width then throw .misplacedFill
    let column ← copyColumn ambient p.marked references sourceColumn (block * width) p.root.column
    return .yield (ambient.push column)
  let P : Nat → Mountain → Prop := fun offset ambient =>
    DynamicBlockState p block start references (p.root.column + offset + 1) ambient ∧
      CopyRunHistory p block start references (p.root.column + offset + 1) ambient
  have hInit : P 0 start := by
    exact ⟨by simpa only [Nat.add_zero] using hInitial,
      by simpa only [Nat.add_zero] using CopyRunHistory.initial p block start references⟩
  have hStep : ∀ offset, offset < width → ∀ ambient, P offset ambient →
      ∃ next, body offset ambient = .ok (.yield next) ∧ P (offset + 1) next := by
    intro offset hOffset ambient hState
    have hNext : p.root.column + offset + 1 < p.reduced.size := by
      dsimp [width] at hOffset
      omega
    obtain ⟨column, hRun, _, _, _, _, hPush, _⟩ := hState.1.copy_next hLast hNext
    refine ⟨ambient.push column, ?_, ?_, ?_⟩
    · have hAmbientSize := hState.1.size_eq
      simp only [body, width, hAmbientSize, ne_eq, not_true_eq_false, ↓reduceIte, hRun]
      rfl
    · simpa only [Nat.add_assoc] using hPush
    · simpa only [Nat.add_assoc] using CopyRunHistory.push hState.2 hState.1 hRun
  obtain ⟨result, hRun, hFinal⟩ := forIn_range_indexed width start body P hInit hStep
  have hEnd : p.root.column + width + 1 = p.reduced.size := by dsimp [width]; omega
  have hResult : OmegaY.Expansion.copyBlock start p.marked p.boundaries p.root.column width block = .ok result := by
    unfold OmegaY.Expansion.copyBlock
    rw [hMap]
    change (forIn (List.range width) start body >>= pure) = .ok result
    rw [hRun]
    rfl
  obtain ⟨checked, hChecked, hReady⟩ := ready.copyBlock hLast
  have he : checked = result := Except.ok.inj (hChecked.symm.trans hResult)
  subst checked
  exact ⟨result, references, hResult, hReady, hMap,
    by simpa only [hEnd] using hFinal.1, by simpa only [hEnd] using hFinal.2⟩

#print axioms CopyRunHistory.push
#print axioms CopyRunHistory.column_read
#print axioms BlockReady.copyBlock_with_history

end OmegaY.Expansion
