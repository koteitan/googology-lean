/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ColumnEquations.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/ColumnEquations.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.FinishAdjacent
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.FrozenSource
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.SuccessInvariant

set_option backward.do.legacy false

/-! Numerical equations preserved by actual successful copying. These
equations alone do not identify the specified parent as the first smaller
candidate; that separate geometric obligation remains explicit. -/

namespace OmegaY.Expansion

open Canonical

theorem copyColumn_finished_of_success {mountain : Mountain} {marked : Array (List Ref)}
    {references : List Ref} {sourceColumn shift rootColumn : Nat} {column : Column}
    (h : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column) :
    FinishedColumn mountain column := by
  unfold copyColumn at h
  obtain ⟨sources, _, hLoop⟩ := bind_success_witness h
  obtain ⟨cells, _, hFinish⟩ := bind_success_witness hLoop
  exact (finish_success_spec hFinish).2

theorem AdjacentSum.preserve {before after : Mountain} (hPreserve : PreservesColumns before after)
    {lower upper : Cell} (hSum : AdjacentSum before lower upper) : AdjacentSum after lower upper := by
  intro hReal
  obtain ⟨ref, parent, hLeft, hParent, hPositive, hValue⟩ := hSum hReal
  obtain ⟨nodes, hNodes, hRead⟩ := lookup_ok_iff.mp hParent
  exact ⟨ref, parent, hLeft, lookup_ok_iff.mpr ⟨nodes, hPreserve.column_read hNodes, hRead⟩,
    hPositive, hValue⟩

def MountainSums (mountain : Mountain) : Prop :=
  ∀ c (hc : c < mountain.size), mountain[c].toList.IsChain (AdjacentSum mountain)

theorem MountainSums.push {mountain : Mountain} (hSums : MountainSums mountain)
    {column : Column} (hFinished : FinishedColumn mountain column) :
    MountainSums (mountain.push column) := by
  intro c hc
  by_cases he : c = mountain.size
  · subst c
    simp only [Array.getElem_push_eq]
    exact hFinished.adjacent_sums.imp (fun _ _ h => h.preserve (PreservesColumns.push mountain column))
  · have hOld : c < mountain.size := by simp only [Array.size_push] at hc; omega
    rw [Array.getElem_push_lt hOld]
    exact (hSums c hOld).imp (fun _ _ h => h.preserve (PreservesColumns.push mountain column))

theorem build_mountain_sums {values : List Nat} {mountain : Mountain}
    (hBuild : Canonical.build values = .ok mountain) : MountainSums mountain := by
  have hValid := build_valid_of_success hBuild
  intro c hc
  rw [List.isChain_iff_getElem]
  intro index hIndex hReal
  have hi : index < mountain[c].size := by simpa only [Array.length_toList] using Nat.lt_of_succ_lt hIndex
  have hj : index + 1 < mountain[c].size := by simpa only [Array.length_toList] using hIndex
  have hIndexPositive : 0 < index := by
    by_contra h
    have he : index = 0 := by omega
    have hPhantom : mountain[c][index] = phantom := by
      have hp := (hValid c hc).phantom
      simpa only [he, Array.getElem?_eq_getElem (by omega : 0 < mountain[c].size), Option.some.injEq] using hp
    apply hReal
    simp only [Array.getElem_toList, hPhantom, phantom]
  obtain ⟨_, ref, parent, _, hFind, hRead, _, hValue, hLeft⟩ :=
    build_steps hBuild c hc index mountain[c][index] mountain[c][index + 1]
      (Array.getElem?_eq_getElem hi) (Array.getElem?_eq_getElem hj) hIndexPositive
  have hLowerRead : Canonical.cellAt mountain ⟨c, index⟩ = .ok mountain[c][index] :=
    cellAt_ok_iff.mpr ⟨mountain[c], Array.getElem?_eq_getElem hc, Array.getElem?_eq_getElem hi⟩
  obtain ⟨found, hFound, hPositive, hSmall⟩ := findParent_result hLowerRead hFind
  have he : found = parent := Except.ok.inj (hFound.symm.trans hRead)
  subst found
  exact ⟨ref, parent, hLeft, lookup_ok_iff.mpr (cellAt_ok_iff.mp hRead), hPositive, by
    simp only [Array.getElem_toList]
    omega⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.copyColumn_finished_of_success
#print axioms OmegaY.Expansion.MountainSums.push
#print axioms OmegaY.Expansion.build_mountain_sums
