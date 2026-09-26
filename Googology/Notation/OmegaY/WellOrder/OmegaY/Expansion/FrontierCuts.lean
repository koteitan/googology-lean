/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/FrontierCuts.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/FrontierCuts.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.FrontierEvents
import Mathlib.Data.Finset.Sort

set_option backward.do.legacy false

/-!
# The actual finite event cuts of a mountain frame

Events are the sorted finite union of all actual rows at least one, with
one inserted even for an empty frame. Natural event indices are clamped at
the final event. Frontiers use finite column indices, so an empty mountain
never requires an inhabitant of its node type.

These facts only enumerate rows and actual adjacent frontier moves. Parent
closure, a raw B rule, and numerical suffix recovery are not assumed or
claimed here.
-/

namespace OmegaY.Geometry.Frame

noncomputable def eventRows (F : Frame) : Finset Row := by
  classical
  exact insert 1 ((Finset.univ.image F.height).filter fun row => 1 ≤ row)

noncomputable def eventCuts (F : Frame) : List Row := F.eventRows.sort (· ≤ ·)

theorem one_mem_eventRows (F : Frame) : (1 : Row) ∈ F.eventRows := by
  classical
  simp only [eventRows, Finset.mem_insert, true_or]

theorem eventRows_nonempty (F : Frame) : F.eventRows.Nonempty := ⟨1, F.one_mem_eventRows⟩

theorem one_le_of_mem_eventRows {F : Frame} {row : Row} (hRow : row ∈ F.eventRows) :
    (1 : Row) ≤ row := by
  classical
  rcases Finset.mem_insert.mp hRow with hOne | hActual
  · exact hOne ▸ le_rfl
  · exact (Finset.mem_filter.mp hActual).2

theorem height_mem_eventRows {F : Frame} (node : F.Node) (hRow : (1 : Row) ≤ F.height node) :
    F.height node ∈ F.eventRows := by
  classical
  apply Finset.mem_insert_of_mem
  exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨node, Finset.mem_univ _, rfl⟩, hRow⟩

theorem real_height_mem_eventRows {F : Frame} (hF : F.Ordered) {node : F.Node}
    (hReal : Real node) : F.height node ∈ F.eventRows :=
  height_mem_eventRows node (one_le_height hF hReal)

theorem mem_eventCuts {F : Frame} {row : Row} : row ∈ F.eventCuts ↔ row ∈ F.eventRows :=
  Finset.mem_sort (· ≤ ·)

theorem one_mem_eventCuts (F : Frame) : (1 : Row) ∈ F.eventCuts :=
  mem_eventCuts.mpr F.one_mem_eventRows

theorem eventCuts_nonempty (F : Frame) : F.eventCuts ≠ [] := by
  intro hEmpty
  have hOne := F.one_mem_eventCuts
  rw [hEmpty] at hOne
  cases hOne

theorem eventCuts_length_pos (F : Frame) : 0 < F.eventCuts.length :=
  List.length_pos_iff.mpr F.eventCuts_nonempty

theorem eventCuts_sorted (F : Frame) : F.eventCuts.SortedLT := Finset.sortedLT_sort F.eventRows

theorem eventCuts_nodup (F : Frame) : F.eventCuts.Nodup := F.eventCuts_sorted.nodup

theorem eventCuts_pairwise (F : Frame) : F.eventCuts.Pairwise (· ≤ ·) :=
  Finset.pairwise_sort F.eventRows (· ≤ ·)

theorem one_le_of_mem_eventCuts {F : Frame} {row : Row} (hRow : row ∈ F.eventCuts) :
    (1 : Row) ≤ row := one_le_of_mem_eventRows (mem_eventCuts.mp hRow)

theorem real_height_mem_eventCuts {F : Frame} (hF : F.Ordered) {node : F.Node}
    (hReal : Real node) : F.height node ∈ F.eventCuts :=
  mem_eventCuts.mpr (real_height_mem_eventRows hF hReal)

noncomputable def lastEvent (F : Frame) : Nat := F.eventCuts.length - 1

theorem lastEvent_lt (F : Frame) : F.lastEvent < F.eventCuts.length := by
  have hLength := F.eventCuts_length_pos
  dsimp only [lastEvent]
  omega

/-- Every out-of-range natural index denotes the actual final cut. -/
noncomputable def eventCut (F : Frame) (event : Nat) : Row :=
  F.eventCuts[min event F.lastEvent]'((Nat.min_le_right _ _).trans_lt F.lastEvent_lt)

theorem eventCut_of_lt (F : Frame) {event : Nat} (hEvent : event < F.eventCuts.length) :
    F.eventCut event = F.eventCuts[event] := by
  have hLe : event ≤ F.lastEvent := by dsimp only [lastEvent]; omega
  simp only [eventCut, Nat.min_eq_left hLe]

theorem eventCut_mem (F : Frame) (event : Nat) : F.eventCut event ∈ F.eventCuts :=
  List.mem_iff_getElem.mpr ⟨min event F.lastEvent,
    (Nat.min_le_right _ _).trans_lt F.lastEvent_lt, rfl⟩

theorem eventCut_one_le (F : Frame) (event : Nat) : (1 : Row) ≤ F.eventCut event :=
  one_le_of_mem_eventCuts (F.eventCut_mem event)

theorem eventCut_zero (F : Frame) : F.eventCut 0 = 1 := by
  apply le_antisymm _ (F.eventCut_one_le 0)
  obtain ⟨index, hIndex, hOne⟩ := List.getElem_of_mem F.one_mem_eventCuts
  rw [F.eventCut_of_lt F.eventCuts_length_pos, ← hOne]
  exact F.eventCuts_sorted.sortedLE.getElem_le_getElem_of_le (Nat.zero_le index)

theorem eventCuts_head (F : Frame) : F.eventCuts.head? = some 1 := by
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem F.eventCuts_length_pos,
    ← F.eventCut_of_lt F.eventCuts_length_pos, F.eventCut_zero]

theorem eventCut_monotone (F : Frame) : Monotone F.eventCut := by
  intro a b hLe
  exact F.eventCuts_sorted.sortedLE.getElem_le_getElem_of_le (min_le_min hLe le_rfl)

theorem eventCut_strict_step (F : Frame) {event : Nat} (hEvent : event < F.lastEvent) :
    F.eventCut event < F.eventCut (event + 1) := by
  have hNext : event + 1 < F.eventCuts.length := by have := F.lastEvent_lt; omega
  rw [F.eventCut_of_lt (by omega), F.eventCut_of_lt hNext]
  exact F.eventCuts_sorted.getElem_lt_getElem_of_lt (Nat.lt_succ_self event)

theorem eventCut_stable (F : Frame) {event : Nat} (hEvent : F.lastEvent ≤ event) :
    F.eventCut event = F.eventCut F.lastEvent := by
  simp only [eventCut, Nat.min_eq_right hEvent, Nat.min_self]

theorem eventCut_of_member {F : Frame} {row : Row} (hRow : row ∈ F.eventCuts) :
    ∃ event, event ≤ F.lastEvent ∧ F.eventCut event = row := by
  obtain ⟨event, hEvent, hEq⟩ := List.getElem_of_mem hRow
  refine ⟨event, ?_, (F.eventCut_of_lt hEvent).trans hEq⟩
  dsimp only [lastEvent]
  omega

theorem real_height_at_event {F : Frame} (hF : F.Ordered) {node : F.Node}
    (hReal : Real node) :
    ∃ event, event ≤ F.lastEvent ∧ F.eventCut event = F.height node :=
  eventCut_of_member (real_height_mem_eventCuts hF hReal)

theorem eventCut_last_read (F : Frame) : F.eventCuts.getLast? = some (F.eventCut F.lastEvent) := by
  rw [List.getLast?_eq_getElem?, F.eventCut_of_lt F.lastEvent_lt]
  exact List.getElem?_eq_getElem F.lastEvent_lt

theorem eventCut_covers_member {F : Frame} {row : Row} (hRow : row ∈ F.eventCuts) :
    row ≤ F.eventCut F.lastEvent := by
  obtain ⟨index, hIndex, hEq⟩ := List.getElem_of_mem hRow
  rw [F.eventCut_of_lt F.lastEvent_lt, ← hEq]
  apply F.eventCuts_sorted.sortedLE.getElem_le_getElem_of_le
  dsimp only [lastEvent]
  omega

/-- The inserted bottom cut also covers any actual row below one, so this
bound does not require a nonempty node type or an ordered-frame premise. -/
theorem height_le_last_eventCut (F : Frame) (node : F.Node) :
    F.height node ≤ F.eventCut F.lastEvent := by
  by_cases hOne : (1 : Row) ≤ F.height node
  · exact eventCut_covers_member (mem_eventCuts.mpr (height_mem_eventRows node hOne))
  · exact (le_of_lt (lt_of_not_ge hOne)).trans (F.eventCut_one_le F.lastEvent)

/-- Consecutiveness in the actual sorted union rules out every node row in
the open gap. It is not a separate geometric assumption. -/
theorem eventCut_no_between (F : Frame) {event : Nat} (hEvent : event < F.lastEvent)
    (node : F.Node) (hLow : F.eventCut event < F.height node)
    (hHigh : F.height node < F.eventCut (event + 1)) : False := by
  have hOne : (1 : Row) ≤ F.height node := (F.eventCut_one_le event).trans hLow.le
  have hMem : F.height node ∈ F.eventCuts := mem_eventCuts.mpr (height_mem_eventRows node hOne)
  obtain ⟨index, hIndex, hRow⟩ := List.getElem_of_mem hMem
  have hNext : event + 1 < F.eventCuts.length := by have := F.lastEvent_lt; omega
  rw [F.eventCut_of_lt (by omega), ← hRow] at hLow
  rw [F.eventCut_of_lt hNext, ← hRow] at hHigh
  have hIndexLow : event < index := F.eventCuts_sorted.getElem_lt_getElem_iff.mp hLow
  have hIndexHigh : index < event + 1 := F.eventCuts_sorted.getElem_lt_getElem_iff.mp hHigh
  omega

noncomputable def eventFrontier {F : Frame} (hF : F.Ordered) (event : Nat)
    (column : Fin F.width) : F.Node :=
  frontierAt hF (F.eventCut event) (F.eventCut_one_le event) column

theorem eventFrontier_spec {F : Frame} (hF : F.Ordered) (event : Nat) (column : Fin F.width) :
    let node := eventFrontier hF event column
    node.1 = column ∧ Real node ∧ F.height node ≤ F.eventCut event ∧
      (∀ i : Fin (F.length column), F.height ⟨column, i⟩ ≤ F.eventCut event → i ≤ node.2) ∧
      ∀ upper, F.upper node = some upper → F.eventCut event < F.height upper :=
  frontierAt_spec hF (F.eventCut_one_le event) column

theorem eventFrontier_zero {F : Frame} (hF : F.Ordered) (column : Fin F.width) :
    eventFrontier hF 0 column =
      ⟨column, ⟨1, by have := hF.length_ge_two column; omega⟩⟩ := by
  have hLength : 1 < F.length column := by have := hF.length_ge_two column; omega
  have hSpec := eventFrontier_spec hF 0 column
  have hLow : F.height (eventFrontier hF 0 column) ≤ 1 := by
    simpa only [F.eventCut_zero] using hSpec.2.2.1
  have hHigh : (1 : Row) ≤ F.height (eventFrontier hF 0 column) :=
    one_le_height hF hSpec.2.1
  have hRows : (F.cells column (eventFrontier hF 0 column).2).row =
      (F.cells column ⟨1, hLength⟩).row :=
    (le_antisymm hLow hHigh).trans (hF.bottom_row column hLength).symm
  have hIndices := (hF.rows_strict column).injective hRows
  exact congrArg (fun i : Fin (F.length column) => (⟨column, i⟩ : F.Node)) hIndices

/-- Every changing column takes one genuine immediate upper step, ending
at the same next global cut. A column is also allowed to stay unchanged. -/
theorem eventFrontier_advance {F : Frame} (hF : F.Ordered) {event : Nat}
    (hEvent : event < F.lastEvent) (column : Fin F.width)
    (hChanged : eventFrontier hF (event + 1) column ≠ eventFrontier hF event column) :
    F.upper (eventFrontier hF event column) = some (eventFrontier hF (event + 1) column) ∧
      F.height (eventFrontier hF (event + 1) column) = F.eventCut (event + 1) :=
  frontierAt_advance hF (F.eventCut_one_le event) (F.eventCut_one_le (event + 1))
    (F.eventCut_strict_step hEvent).le (F.eventCut_no_between hEvent) column hChanged

theorem eventFrontier_stable {F : Frame} (hF : F.Ordered) {event : Nat}
    (hEvent : F.lastEvent ≤ event) (column : Fin F.width) :
    eventFrontier hF event column = eventFrontier hF F.lastEvent column := by
  simp only [eventFrontier, F.eventCut_stable hEvent]

/-- The last event reaches each actual column top, with no extra top
existence or endpoint-read assumption. -/
theorem eventFrontier_last_upper_none {F : Frame} (hF : F.Ordered) (column : Fin F.width) :
    F.upper (eventFrontier hF F.lastEvent column) = none := by
  cases hUpper : F.upper (eventFrontier hF F.lastEvent column) with
  | none => rfl
  | some upper =>
    have hAbove := (eventFrontier_spec hF F.lastEvent column).2.2.2.2 upper hUpper
    exact False.elim (not_lt_of_ge (F.height_le_last_eventCut upper) hAbove)

theorem eventFrontier_upper_none_of_last_le {F : Frame} (hF : F.Ordered) {event : Nat}
    (hEvent : F.lastEvent ≤ event) (column : Fin F.width) :
    F.upper (eventFrontier hF event column) = none := by
  rw [eventFrontier_stable hF hEvent]
  exact eventFrontier_last_upper_none hF column

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry

theorem MountainTops.eventFrontier_last_value {mountain : Mountain}
    (hValid : MountainValid mountain) (hTops : MountainTops mountain)
    (column : Fin (Frame.ofMountain mountain).width) :
    (Frame.ofMountain mountain).value
      (Frame.eventFrontier hValid.toOrdered (Frame.ofMountain mountain).lastEvent column) = 1 :=
  MountainTops.value_one_of_upper_none hTops (Frame.eventFrontier_last_upper_none hValid.toOrdered column)

theorem MountainTops.eventFrontier_value_of_last_le {mountain : Mountain}
    (hValid : MountainValid mountain) (hTops : MountainTops mountain) {event : Nat}
    (hEvent : (Frame.ofMountain mountain).lastEvent ≤ event)
    (column : Fin (Frame.ofMountain mountain).width) :
    (Frame.ofMountain mountain).value (Frame.eventFrontier hValid.toOrdered event column) = 1 :=
  MountainTops.value_one_of_upper_none hTops
    (Frame.eventFrontier_upper_none_of_last_le hValid.toOrdered hEvent column)

end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.eventCuts_sorted
#print axioms OmegaY.Geometry.Frame.real_height_mem_eventCuts
#print axioms OmegaY.Geometry.Frame.eventCuts_head
#print axioms OmegaY.Geometry.Frame.eventCut_no_between
#print axioms OmegaY.Geometry.Frame.height_le_last_eventCut
#print axioms OmegaY.Geometry.Frame.eventFrontier_zero
#print axioms OmegaY.Geometry.Frame.eventFrontier_advance
#print axioms OmegaY.Geometry.Frame.eventFrontier_last_upper_none
#print axioms OmegaY.Expansion.MountainTops.eventFrontier_last_value
