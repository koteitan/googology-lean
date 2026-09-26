/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/BlockTotal.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/BlockTotal.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.DynamicBlockRun
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.IndexedLoop

set_option backward.do.legacy false

/-! Readiness for the next actual block depends only on the available
mountain. In particular its reference map is not carried from the preceding
block: that map is freshly constructed inside the next call. -/

namespace OmegaY.Expansion

open Canonical

structure BlockReady {front : List Nat} {last : Nat} (p : Preparation front last)
    (block : Nat) (mountain : Mountain) : Prop where
  base_preserved : PreservesColumns p.reduced mountain
  valid : MountainValid mountain
  size_eq : mountain.size = p.root.column + 1 + block * (p.reduced.size - 1 - p.root.column)
  boundary_rows : RootRowsInColumn p mountain (mountain.size - 1)
  boundary_power : ∀ nodes, mountain[mountain.size - 1]? = some nodes → ColumnPowerSteps nodes

theorem Preparation.initial_block_ready {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) : BlockReady p 1 p.reduced := by
  have hSize := build_size p.reduced_build
  simp only [List.length_append, List.length_singleton] at hSize
  have hRoot := p.root_before_last
  exact {
    base_preserved := fun _ _ => rfl
    valid := p.reduced_valid
    size_eq := by simp only [Nat.one_mul]; omega
    boundary_rows := p.reduced_root_rows hLast
    boundary_power := fun _ hRead => build_column_power_steps_of_read p.reduced_build hRead }

theorem BlockReady.copyBlock {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start : Mountain} (ready : BlockReady p block start) (hLast : 1 < last) :
    ∃ result,
      copyBlock start p.marked p.boundaries p.root.column
        (p.reduced.size - 1 - p.root.column) block = .ok result ∧
      BlockReady p (block + 1) result := by
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
      (p.root.column + offset + 1 = p.reduced.size →
        RootRowsInColumn p ambient (ambient.size - 1))
  have hInit : P 0 start := by
    refine ⟨by simpa only [Nat.add_zero] using hInitial, ?_⟩
    intro hEnd
    simp only [Nat.add_zero] at hEnd
    omega
  have hStep : ∀ offset, offset < width → ∀ ambient, P offset ambient →
      ∃ next, body offset ambient = .ok (.yield next) ∧ P (offset + 1) next := by
    intro offset hOffset ambient hState
    have hNext : p.root.column + offset + 1 < p.reduced.size := by
      dsimp [width] at hOffset
      omega
    obtain ⟨column, hRun, _, _, _, _, hPush, hRows⟩ := hState.1.copy_next hLast hNext
    refine ⟨ambient.push column, ?_, ?_, ?_⟩
    · have hAmbientSize := hState.1.size_eq
      simp only [body, width, hAmbientSize, ne_eq, not_true_eq_false, ↓reduceIte, hRun]
      rfl
    · simpa only [Nat.add_assoc] using hPush
    · intro hEnd
      have hFinal : p.root.column + offset + 1 = p.reduced.size - 1 := by omega
      intro nodes index source hNodes hSource hIndex
      simpa only [Array.size_push, Nat.add_sub_cancel] using hRows hFinal hNodes hSource hIndex
  obtain ⟨result, hRun, hFinal⟩ := forIn_range_indexed width start body P hInit hStep
  have hEnd : p.root.column + width + 1 = p.reduced.size := by dsimp [width]; omega
  have hFinalState : DynamicBlockState p block start references p.reduced.size result := by
    simpa only [hEnd] using hFinal.1
  have hRows : RootRowsInColumn p result (result.size - 1) := hFinal.2 hEnd
  refine ⟨result, ?_, ?_⟩
  · unfold OmegaY.Expansion.copyBlock
    rw [hMap]
    change (forIn (List.range width) start body >>= pure) = .ok result
    rw [hRun]
    rfl
  · refine {
      base_preserved := hFinalState.base_ambient
      valid := hFinalState.ambient_valid
      size_eq := ?_
      boundary_rows := hRows
      boundary_power := ?_ }
    · have hResultSize := hFinalState.size_eq
      rw [Nat.add_mul, Nat.one_mul]
      dsimp [width] at hEnd
      omega
    · intro nodes hNodes
      obtain ⟨lastColumn, hLastColumn, hPower, _⟩ :=
        hFinalState.copied_columns (p.reduced.size - 1) (by omega) (by omega)
      have hLastIndex : p.reduced.size - 1 + block * (p.reduced.size - 1 - p.root.column) =
          result.size - 1 := by have := hFinalState.size_eq; omega
      rw [hLastIndex] at hLastColumn
      have he : lastColumn = nodes := Option.some.inj (hLastColumn.symm.trans hNodes)
      simpa only [he] using hPower

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.initial_block_ready
#print axioms OmegaY.Expansion.BlockReady.copyBlock
