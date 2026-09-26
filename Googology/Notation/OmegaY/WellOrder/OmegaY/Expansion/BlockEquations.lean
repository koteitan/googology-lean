/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/BlockEquations.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/BlockEquations.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ColumnEquations
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.BlocksTotal
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.TruncateValues

set_option backward.do.legacy false

/-! The actual block loops preserve all numerical adjacent equations and
value-one tops, not merely those in the final boundary column. -/

namespace OmegaY.Expansion

open Canonical

theorem copyBlock_equations_of_success {mountain result : Mountain}
    {marked : Array (List Ref)} {boundaries : List Row} {rootColumn width block : Nat}
    (hSums : MountainSums mountain) (hTops : MountainTops mountain)
    (hRun : copyBlock mountain marked boundaries rootColumn width block = .ok result) :
    MountainSums result ∧ MountainTops result := by
  unfold copyBlock at hRun
  obtain ⟨references, _, hReferences⟩ := bind_success_witness hRun
  obtain ⟨output, hLoop, hResult⟩ := bind_success_witness hReferences
  have he : output = result := Except.ok.inj hResult
  subst output
  apply forIn_invariant_of_success _ _ _
    (fun ambient => MountainSums ambient ∧ MountainTops ambient) ⟨hSums, hTops⟩ _ hLoop
  intro offset _ ambient hState step hStep
  dsimp only at hStep
  split at hStep
  · cases hStep
  ·
    obtain ⟨column, hColumn, hYield⟩ := bind_success_witness hStep
    have hStepEq : ForInStep.yield (ambient.push column) = step := Except.ok.inj hYield
    rw [← hStepEq]
    have hFinished := copyColumn_finished_of_success hColumn
    exact ⟨hState.1.push hFinished, hState.2.push hFinished.topOne⟩

theorem MountainSums.pop {mountain : Mountain} (hSums : MountainSums mountain)
    (hValid : MountainValid mountain) : MountainSums mountain.pop := by
  intro c hc
  have hOld : c < mountain.size := by simp only [Array.size_pop] at hc; omega
  rw [Array.getElem_pop hc]
  apply (hSums c hOld).imp_of_mem_imp
  intro lower upper _ hUpper hSum hReal
  obtain ⟨ref, parent, hLeft, hParent, hPositive, hValue⟩ := hSum hReal
  obtain ⟨index, hRead⟩ := List.mem_iff_getElem?.mp hUpper
  have hArrayRead : mountain[c][index]? = some upper := by
    simpa only [Array.getElem?_toList] using hRead
  have hLeftward := ((hValid c hOld).stored_valid index upper ref hArrayRead hLeft).1
  have hBeforeCut : ref.column < mountain.size - 1 := by
    simp only [Array.size_pop] at hc
    omega
  have hCellEq : Canonical.cellAt mountain.pop ref = Canonical.cellAt mountain ref := by
    apply cellAt_eq_of_column_eq
    simp only [Array.getElem?_pop, hBeforeCut, ↓reduceIte]
  have hReadParent : lookup mountain.pop ref = .ok parent := by
    unfold lookup at *
    rw [hCellEq]
    exact hParent
  exact ⟨ref, parent, hLeft, hReadParent, hPositive, hValue⟩

theorem MountainTops.pop {mountain : Mountain} (hTops : MountainTops mountain) :
    MountainTops mountain.pop := by
  intro c hc
  have hOld : c < mountain.size := by simp only [Array.size_pop] at hc; omega
  rw [Array.getElem_pop hc]
  exact hTops c hOld

theorem Preparation.blocks_equations {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) (copies : Nat) :
    ∃ result,
      (forIn (List.range copies) p.reduced (fun block ambient => do
        let next ← copyBlock ambient p.marked p.boundaries p.root.column
          (p.initial.size - 1 - p.root.column) (block + 1)
        pure (.yield next)) : Result Mountain) = .ok result ∧
      BlockReady p (copies + 1) result ∧ MountainSums result ∧ MountainTops result := by
  obtain ⟨result, hRun, hReady⟩ := p.blocks_total hLast copies
  refine ⟨result, hRun, hReady, ?_⟩
  obtain ⟨built, hBuild, _, hTops⟩ := build_total (build_success_legal p.reduced_build)
  have he : built = p.reduced := Except.ok.inj (hBuild.symm.trans p.reduced_build)
  subst built
  apply forIn_invariant_of_success _ _ _ (fun ambient => MountainSums ambient ∧ MountainTops ambient)
    ⟨build_mountain_sums p.reduced_build, hTops⟩ _ hRun
  intro block _ ambient hState step hStep
  obtain ⟨next, hNext, hYield⟩ := bind_success_witness hStep
  have hStepEq : ForInStep.yield next = step := Except.ok.inj hYield
  rw [← hStepEq]
  exact copyBlock_equations_of_success hState.1 hState.2 hNext

theorem Preparation.expandDiagram_equations {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {copies : Nat} (hCopies : 0 < copies)
    {result : Mountain} (hRun : expandDiagram (front ++ [last]) copies = .ok result) :
    MountainSums result ∧ MountainTops result := by
  obtain ⟨output, hLoop, hReady, hSums, hTops⟩ := p.blocks_equations hLast copies
  have hActual := p.expandDiagram_of_blocks hLast hCopies hLoop
  have he : output.pop = result := Except.ok.inj (hActual.symm.trans hRun)
  subst result
  exact ⟨hSums.pop hReady.valid, MountainTops.pop hTops⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.copyBlock_equations_of_success
#print axioms OmegaY.Expansion.Preparation.blocks_equations
#print axioms OmegaY.Expansion.Preparation.expandDiagram_equations
