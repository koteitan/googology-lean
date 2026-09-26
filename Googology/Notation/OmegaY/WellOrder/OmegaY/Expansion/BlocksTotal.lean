/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/BlocksTotal.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/BlocksTotal.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.BlockTotal
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ExpansionPrepared

set_option backward.do.legacy false

/-! Every finite number of actual blocks succeeds. The invariant supplies
the next block's complete boundary support, while each block recomputes its
own references using the original program. This is algorithmic totality,
not termination of an iterated expansion trajectory. -/

namespace OmegaY.Expansion

open Canonical

theorem Preparation.blocks_total {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) (copies : Nat) :
    ∃ result,
      (forIn (List.range copies) p.reduced (fun block ambient => do
        let next ← copyBlock ambient p.marked p.boundaries p.root.column
          (p.initial.size - 1 - p.root.column) (block + 1)
        pure (.yield next)) : Result Mountain) = .ok result ∧
      BlockReady p (copies + 1) result := by
  have hSizes : p.initial.size = p.reduced.size := by
    have hInitial := build_size p.initial_build
    have hReduced := build_size p.reduced_build
    simp only [List.length_append, List.length_singleton] at hInitial hReduced
    exact hInitial.trans hReduced.symm
  apply forIn_range_indexed copies p.reduced _ (fun block ambient => BlockReady p (block + 1) ambient)
  · exact p.initial_block_ready hLast
  · intro block _ ambient hReady
    obtain ⟨result, hRun, hNext⟩ := hReady.copyBlock hLast
    refine ⟨result, ?_, hNext⟩
    rw [hSizes, hRun]
    rfl

theorem Preparation.expandDiagram_total {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {copies : Nat} (hCopies : 0 < copies) :
    ∃ result, expandDiagram (front ++ [last]) copies = .ok result.pop ∧
      BlockReady p (copies + 1) result := by
  obtain ⟨result, hRun, hReady⟩ := p.blocks_total hLast copies
  refine ⟨result, ?_, hReady⟩
  rw [p.expandDiagram_eq_blocks hLast hCopies, hRun]
  rfl

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.blocks_total
#print axioms OmegaY.Expansion.Preparation.expandDiagram_total
