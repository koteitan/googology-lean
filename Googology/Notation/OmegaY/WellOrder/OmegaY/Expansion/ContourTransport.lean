/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ContourTransport.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/ContourTransport.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.Contour
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.PowerSteps

set_option backward.do.legacy false

/-!
# Source-row recovery and transport of actual contour paths

Only the stored source column is required to satisfy ColumnPowerSteps. No
power-step property or canonical normality is assumed of a new copied column.
-/

namespace OmegaY.Expansion

open Canonical

/-- The actual source cells visited by the same stopping test as contour. -/
def contourSourceCells (markerIndices : List Nat) : Nat → Cell → List Cell → List Cell
  | _, _, [] => []
  | index, current, upper :: rest =>
      if current.value = 1 ∨ index + 1 ∈ markerIndices then []
      else upper :: contourSourceCells markerIndices (index + 1) upper rest

theorem contourSourceCells_eq_take (markerIndices : List Nat) (index : Nat)
    (current : Cell) (rest : List Cell) :
    contourSourceCells markerIndices index current rest =
      rest.take (contourExponents markerIndices index current rest).length := by
  induction rest generalizing index current with
  | nil => rfl
  | cons upper rest ih =>
    by_cases hStop : current.value = 1 ∨ index + 1 ∈ markerIndices
    · simp [contourSourceCells, contourExponents, hStop]
    · simp [contourSourceCells, contourExponents, hStop, ih]

private theorem source_suffix_cons {nodes : Column} {index : Nat} {upper : Cell}
    {rest : List Cell} (hRest : nodes.toList.drop (index + 1) = upper :: rest) :
    nodes[index + 1]? = some upper ∧ nodes.toList.drop ((index + 1) + 1) = rest := by
  constructor
  · simpa only [List.head?_drop, Array.getElem?_toList, List.head?_cons]
      using congrArg List.head? hRest
  · simpa only [List.tail_drop, List.tail_cons] using congrArg List.tail hRest

/-- Starting at the old row reproduces exactly the visited stored rows. -/
theorem contour_source_trace {nodes : Column} (hPower : ColumnPowerSteps nodes)
    (markerIndices : List Nat) {index : Nat} {current : Cell}
    (hCurrent : nodes[index]? = some current) {rest : List Cell}
    (hRest : nodes.toList.drop (index + 1) = rest) :
    bumpTrace current.row (contourExponents markerIndices index current rest) =
      (contourSourceCells markerIndices index current rest).map Cell.row := by
  induction rest generalizing index current with
  | nil => rfl
  | cons upper rest ih =>
    by_cases hStop : current.value = 1 ∨ index + 1 ∈ markerIndices
    · simp [contourExponents, contourSourceCells, hStop, bumpTrace]
    · obtain ⟨hUpper, hTail⟩ := source_suffix_cons hRest
      have hStep := hPower index current upper hCurrent hUpper
      simp only [contourExponents, contourSourceCells, hStop, ↓reduceIte, bumpTrace,
        List.map_cons, ← hStep]
      rw [ih hUpper hTail]

theorem bumpTrace_monotone {source target : Row} (hStart : source ≤ target)
    (exponents : List Nat) :
    List.Forall₂ (· ≤ ·) (bumpTrace source exponents) (bumpTrace target exponents) := by
  induction exponents generalizing source target with
  | nil => exact .nil
  | cons exponent rest ih =>
    exact .cons (Row.bump_monotone exponent hStart)
      (ih (Row.bump_monotone exponent hStart))

theorem bumpTrace_append (start : Row) (before after : List Nat) :
    bumpTrace start (before ++ after) =
      bumpTrace start before ++ bumpTrace (Row.run start before) after := by
  induction before generalizing start with
  | nil => rfl
  | cons exponent before ih => simp [bumpTrace, ih]

theorem bumpTrace_drop_append (start : Row) (before after : List Nat) :
    (bumpTrace start (before ++ after)).drop before.length =
      bumpTrace (Row.run start before) after := by
  rw [bumpTrace_append]
  exact List.drop_left' (bumpTrace_length start before)

/-- Every individual low-scale step, not only the final run, stays in the
root interval. The target need not be a canonical mountain row. -/
theorem bumpTrace_mem_interval {root start : Row} {scale : Nat}
    (hLower : root ≤ start) (hUpper : start < Row.bump root scale)
    (exponents : List Nat) (hSmall : ∀ d ∈ exponents, d < scale) :
    ∀ row ∈ bumpTrace start exponents, root ≤ row ∧ row < Row.bump root scale := by
  induction exponents generalizing start with
  | nil => simp [bumpTrace]
  | cons exponent rest ih =>
    obtain ⟨hNextLower, hNextUpper⟩ := Row.bump_mem_interval hLower hUpper
      (hSmall exponent (by simp))
    intro row hRow
    rcases List.mem_cons.mp hRow with rfl | hRow
    · exact ⟨hNextLower, hNextUpper⟩
    · exact ih hNextLower hNextUpper (fun d hd => hSmall d (by simp [hd])) row hRow

/-- At each corresponding step, either both rows remain below the cap or
the rows have already become equal. -/
theorem bumpTrace_same_or_below {root source target : Row} {scale : Nat}
    (hSourceLower : root ≤ source) (hSourceUpper : source < Row.bump root scale)
    (hTargetLower : root ≤ target) (hTargetUpper : target < Row.bump root scale)
    (exponents : List Nat) :
    List.Forall₂ (fun a b => a = b ∨ (a < Row.bump root scale ∧ b < Row.bump root scale))
      (bumpTrace source exponents) (bumpTrace target exponents) := by
  induction exponents generalizing source target with
  | nil => exact .nil
  | cons exponent rest ih =>
    by_cases hSmall : exponent < scale
    · obtain ⟨hSourceNextLower, hSourceNextUpper⟩ :=
        Row.bump_mem_interval hSourceLower hSourceUpper hSmall
      obtain ⟨hTargetNextLower, hTargetNextUpper⟩ :=
        Row.bump_mem_interval hTargetLower hTargetUpper hSmall
      exact .cons (Or.inr ⟨hSourceNextUpper, hTargetNextUpper⟩)
        (ih hSourceNextLower hSourceNextUpper hTargetNextLower hTargetNextUpper)
    · have hReset := Row.bump_reset hSourceLower hSourceUpper hTargetLower hTargetUpper
        (Nat.le_of_not_gt hSmall)
      simp only [bumpTrace, hReset]
      exact List.forall₂_same.mpr (fun _ _ => Or.inl rfl)

/-- All targets starting at the first high step are identical. The suffix
may contain arbitrary exponents; the starting offsets are permanently lost. -/
theorem bumpTrace_reset_after {root source target : Row} {scale exponent : Nat}
    (before after : List Nat)
    (hSourceLower : root ≤ source) (hSourceUpper : source < Row.bump root scale)
    (hTargetLower : root ≤ target) (hTargetUpper : target < Row.bump root scale)
    (hSmall : ∀ d ∈ before, d < scale) (hHigh : scale ≤ exponent) :
    (bumpTrace source (before ++ exponent :: after)).drop before.length =
      (bumpTrace target (before ++ exponent :: after)).drop before.length := by
  have hReset : Row.bump (Row.run source before) exponent =
      Row.bump (Row.run target before) exponent := by
    simpa only [Row.run_append, Row.run_cons, Row.run_nil] using
      Row.run_reset_after before [] hSourceLower hSourceUpper hTargetLower hTargetUpper hSmall hHigh
  rw [bumpTrace_drop_append, bumpTrace_drop_append]
  simp only [bumpTrace, hReset]

/-- Each generated row is at least its corresponding actual source row. -/
theorem contour_trace_ge_source {nodes : Column} (hPower : ColumnPowerSteps nodes)
    (markerIndices : List Nat) {index : Nat} {current : Cell}
    (hCurrent : nodes[index]? = some current) {rest : List Cell}
    (hRest : nodes.toList.drop (index + 1) = rest) {target : Row}
    (hStart : current.row ≤ target) :
    List.Forall₂ (· ≤ ·) ((contourSourceCells markerIndices index current rest).map Cell.row)
      (bumpTrace target (contourExponents markerIndices index current rest)) := by
  rw [← contour_source_trace hPower markerIndices hCurrent hRest]
  exact bumpTrace_monotone hStart _

/-- The suffix equality is to actual source rows, rather than an unrelated
second bump orbit. The split is in the exponents selected by contour itself. -/
theorem contour_trace_reset_after {nodes : Column} (hPower : ColumnPowerSteps nodes)
    (markerIndices : List Nat) {index : Nat} {current : Cell}
    (hCurrent : nodes[index]? = some current) {rest : List Cell}
    (hRest : nodes.toList.drop (index + 1) = rest)
    {root target : Row} {scale exponent : Nat} (before after : List Nat)
    (hSourceLower : root ≤ current.row) (hSourceUpper : current.row < Row.bump root scale)
    (hTargetLower : root ≤ target) (hTargetUpper : target < Row.bump root scale)
    (hWord : contourExponents markerIndices index current rest = before ++ exponent :: after)
    (hSmall : ∀ d ∈ before, d < scale) (hHigh : scale ≤ exponent) :
    (bumpTrace target (contourExponents markerIndices index current rest)).drop before.length =
      ((contourSourceCells markerIndices index current rest).map Cell.row).drop before.length := by
  rw [← contour_source_trace hPower markerIndices hCurrent hRest, hWord]
  exact (bumpTrace_reset_after before after hSourceLower hSourceUpper
    hTargetLower hTargetUpper hSmall hHigh).symm

/-- The transport inequality is a theorem about the successful executable
output, with its source cells paired in actual visit order. -/
theorem contour_total_transport {mountain : Mountain} (hValid : MountainValid mountain)
    {sourceColumn shift rootColumn : Nat} {nodes : Column}
    (hColumn : mountain[sourceColumn]? = some nodes) (hSourcePositive : 0 < sourceColumn)
    (hDestination : sourceColumn + shift ≤ mountain.size) (hTop : TopOne nodes)
    (hPower : ColumnPowerSteps nodes) (markerIndices : List Nat)
    {index : Nat} {current : Cell} (target : Row)
    (hCurrent : nodes[index]? = some current) {rest : List Cell}
    (hRest : nodes.toList.drop (index + 1) = rest) (hStart : current.row ≤ target) :
    ∃ result,
      contour mountain sourceColumn markerIndices shift rootColumn index target current rest = .ok result ∧
      List.Forall₂ (fun source copied => source.row ≤ copied.row)
        (contourSourceCells markerIndices index current rest) result ∧
      ContourParents mountain (sourceColumn + shift) result := by
  obtain ⟨result, hRun, hRows, hParents⟩ := contour_total hValid hColumn hSourcePositive
    hDestination hTop markerIndices target hCurrent hRest (rootColumn := rootColumn)
  have hTransport := contour_trace_ge_source hPower markerIndices hCurrent hRest hStart
  rw [← hRows, List.forall₂_map_left_iff, List.forall₂_map_right_iff] at hTransport
  exact ⟨result, hRun, hTransport, hParents⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.contour_source_trace
#print axioms OmegaY.Expansion.contour_trace_reset_after
#print axioms OmegaY.Expansion.contour_total_transport
