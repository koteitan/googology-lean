/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ExpansionPrepared.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/ExpansionPrepared.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.PreparedBoundaries

set_option backward.do.legacy false

/-! Exact reduction of the unchanged expansion program to its real outer
copy loop. Preparation supplies each build, top, root, restored-root, and
marker read. No successful block or outer-loop execution is assumed. -/

namespace OmegaY.Expansion

open Canonical

@[simp] private theorem prepared_bind_ok {α β : Type} (a : α) (f : α → Result β) :
    (Except.ok a >>= f) = f a := rfl
@[simp] private theorem prepared_pure_ok {α : Type} (a : α) :
    (pure a : Result α) = .ok a := rfl

theorem Preparation.expandDiagram_eq_blocks {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {copies : Nat} (hCopies : 0 < copies) :
    expandDiagram (front ++ [last]) copies =
      (do
        let result ← forIn (List.range copies) p.reduced (fun block ambient => do
          let next ← copyBlock ambient p.marked p.boundaries p.root.column
            (p.initial.size - 1 - p.root.column) (block + 1)
          pure (.yield next))
        pure result.pop) := by
  have hSize := build_size p.initial_build
  simp only [List.length_append, List.length_singleton] at hSize
  have hLastColumnIndex : p.initial.size - 1 = front.length := by omega
  obtain ⟨lastColumn, hLastColumn, hLastTop⟩ := Option.bind_eq_some_iff.mp p.initial_top
  obtain ⟨rootColumn, hRootColumn, _⟩ := cellAt_ok_iff.mp p.initial_root
  have hColumnRead : columnAt p.initial (p.initial.size - 1) = .ok lastColumn := by
    simp only [columnAt, hLastColumnIndex, hLastColumn]
  have hTopRead : top lastColumn = .ok p.lastTop := by simp only [top, hLastTop]
  have hRootColumnRead : columnAt p.initial p.root.column = .ok rootColumn := by
    simp only [columnAt, hRootColumn]
  have hRootRead : lookup p.initial p.root = .ok p.rootCell :=
    lookup_ok_iff.mpr (cellAt_ok_iff.mp p.initial_root)
  have hRestored : lookup p.reduced p.root = .ok p.rootCell :=
    lookup_ok_iff.mpr (cellAt_ok_iff.mp p.restored_root)
  have hRootBound : p.root.column < p.initial.size - 1 := by
    rw [hLastColumnIndex]
    exact p.root_before_last
  have hNonempty : (front ++ [last]).isEmpty = false := by simp
  have hGetLast : (front ++ [last]).getLast? = some last := by simp
  have hTake : (front ++ [last]).take ((front ++ [last]).length - 1) = front := by simp
  have hLastNe : last ≠ 1 := by omega
  have hCopiesNe : copies ≠ 0 := by omega
  simp only [expandDiagram, p.initial_build, Except.mapError, prepared_bind_ok,
    hNonempty, Bool.false_eq_true, hGetLast, Option.some.injEq, hLastNe, hCopiesNe,
    or_self, ↓reduceIte, hColumnRead, hTopRead, leftOf, p.top_left, hRootBound,
    not_true_eq_false, hRootColumnRead, hRootRead, hTake, Option.getD_some,
    p.reduced_build, hRestored, ne_eq, p.markers_built]
  rw [p.boundaries_of_column hRootColumn]

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.expandDiagram_eq_blocks
