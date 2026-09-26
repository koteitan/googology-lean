/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Canonical/Invariant.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Canonical/Invariant.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Prefix
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Fuel
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.Frame

set_option backward.do.legacy false

/-!
# Concrete invariants of partial canonical columns

The current last column may still have top value greater than one.  Neither
parent-search success nor an upper-neighbour existence property is a field.
Stored references are read in a concrete immutable mountain.
-/

namespace OmegaY.Canonical

structure ColumnValid (mountain : Mountain) (columnIndex : Nat) (column : Column) : Prop where
  size_ge_two : 2 ≤ column.size
  phantom : column[0]? = some Canonical.phantom
  bottom_row : ∀ (cell : Cell), column[1]? = some cell → cell.row = 1
  rows_strict : ∀ (i j : Nat) (a b : Cell), column[i]? = some a → column[j]? = some b →
    i < j → a.row < b.row
  real_positive : ∀ (i : Nat) (cell : Cell), column[i]? = some cell → 0 < i → 0 < cell.value
  stored_valid : ∀ (i : Nat) (cell : Cell) (ref : Ref), column[i]? = some cell → cell.left = some ref →
    ref.column < columnIndex ∧ ∃ (parent : Cell), cellAt mountain ref = .ok parent ∧
      parent.row ≤ cell.row
  stored_exists : ∀ (i : Nat) (cell : Cell), column[i]? = some cell → 0 < i → 0 < columnIndex →
    ∃ ref, cell.left = some ref
  first_values : ∀ (i : Nat) (cell : Cell), column[i]? = some cell → 0 < i → columnIndex = 0 →
    cell.value = 1

def MountainValid (mountain : Mountain) : Prop :=
  ∀ c (hc : c < mountain.size), ColumnValid mountain c mountain[c]

theorem mountainValid_empty : MountainValid #[] := by
  intro c hc
  simp at hc

theorem cellAt_ok_iff {mountain : Mountain} {ref : Ref} {cell : Cell} :
    cellAt mountain ref = .ok cell ↔
      ∃ column, mountain[ref.column]? = some column ∧ column[ref.index]? = some cell := by
  cases hColumn : mountain[ref.column]? with
  | none => simp [cellAt, hColumn]
  | some column =>
      cases hCell : column[ref.index]? with
      | none => simp [cellAt, hColumn, hCell]
      | some found => simp [cellAt, hColumn, hCell]

theorem cellAt_push_left {mountain : Mountain} {column : Column} {ref : Ref}
    (hc : ref.column < mountain.size) :
    cellAt (mountain.push column) ref = cellAt mountain ref := by
  apply cellAt_eq_of_column_eq
  simp [Array.getElem?_push, Nat.ne_of_lt hc]

theorem ColumnValid.transport {before after : Mountain} {c : Nat} {column : Column}
    (h : ColumnValid before c column)
    (hRefs : ∀ ref, ref.column < c → cellAt before ref = cellAt after ref) :
    ColumnValid after c column := by
  refine {
    size_ge_two := h.size_ge_two
    phantom := h.phantom
    bottom_row := h.bottom_row
    rows_strict := h.rows_strict
    real_positive := h.real_positive
    stored_exists := h.stored_exists
    first_values := h.first_values
    stored_valid := ?_ }
  intro i cell ref hCell hLeft
  obtain ⟨hc, parent, hParent, hRow⟩ := h.stored_valid i cell ref hCell hLeft
  exact ⟨hc, parent, (hRefs ref hc).symm.trans hParent, hRow⟩

theorem MountainValid.push {mountain : Mountain} {column : Column}
    (hMountain : MountainValid mountain)
    (hColumn : ColumnValid mountain mountain.size column) :
    MountainValid (mountain.push column) := by
  intro c hc
  by_cases he : c = mountain.size
  · subst c
    simp only [Array.getElem_push_eq]
    exact hColumn.transport (fun ref hr => (cellAt_push_left hr).symm)
  · have hOld : c < mountain.size := by
      simp only [Array.size_push] at hc
      omega
    rw [Array.getElem_push_lt hOld]
    exact (hMountain c hOld).transport
      (fun ref hr => (cellAt_push_left (Nat.lt_trans hr hOld)).symm)

def initialBottom (column value : Nat) : Cell :=
  ⟨1, value, if column = 0 then none else some ⟨column - 1, 0⟩⟩

theorem initialColumn_cases {c value i : Nat} {cell : Cell}
    (h : (initialColumn c value)[i]? = some cell) :
    (i = 0 ∧ cell = phantom) ∨ (i = 1 ∧ cell = initialBottom c value) := by
  have hi : i < 2 := by
    obtain ⟨hi, _⟩ := Array.getElem?_eq_some_iff.mp h
    exact hi
  by_cases he : i = 0
  · subst i
    exact Or.inl ⟨rfl, by simpa [initialColumn] using h.symm⟩
  · have he : i = 1 := by omega
    subst i
    exact Or.inr ⟨rfl, by simpa [initialColumn, initialBottom] using h.symm⟩

theorem initialColumn_valid {mountain : Mountain} {value : Nat}
    (hMountain : MountainValid mountain) (hPositive : 0 < value)
    (hFirst : mountain.size = 0 → value = 1) :
    ColumnValid mountain mountain.size (initialColumn mountain.size value) := by
  refine {
    size_ge_two := by simp [initialColumn]
    phantom := by simp [initialColumn]
    bottom_row := ?_
    rows_strict := ?_
    real_positive := ?_
    stored_valid := ?_
    stored_exists := ?_
    first_values := ?_ }
  · intro cell hCell
    rcases initialColumn_cases hCell with ⟨hi, _⟩ | ⟨_, rfl⟩
    · omega
    · rfl
  · intro i j a b ha hb hij
    rcases initialColumn_cases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    <;> rcases initialColumn_cases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · omega
    · exact Row.zero_lt_one
    · omega
    · omega
  · intro i cell hCell hi
    rcases initialColumn_cases hCell with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · omega
    · exact hPositive
  · intro i cell ref hCell hLeft
    rcases initialColumn_cases hCell with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · cases hLeft
    · by_cases hEmpty : mountain.size = 0
      · simp [initialBottom, hEmpty] at hLeft
      · have hRef : (⟨mountain.size - 1, 0⟩ : Ref) = ref := by
          simpa [initialBottom, hEmpty] using hLeft
        subst ref
        have hPrev : mountain.size - 1 < mountain.size := by omega
        refine ⟨hPrev, phantom, ?_, Row.zero_le 1⟩
        exact cellAt_ok_iff.mpr ⟨mountain[mountain.size - 1],
          Array.getElem?_eq_getElem hPrev, (hMountain _ hPrev).phantom⟩
  · intro i cell hCell hi hc
    rcases initialColumn_cases hCell with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · omega
    · refine ⟨⟨mountain.size - 1, 0⟩, ?_⟩
      simp [initialBottom, Nat.ne_of_gt hc]
  · intro i cell hCell hi hc
    rcases initialColumn_cases hCell with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · omega
    · exact hFirst hc

/-- Appending one genuine difference cell preserves every partial-column
condition.  The new left endpoint is a concrete cell in an earlier column. -/
theorem ColumnValid.push {mountain : Mountain} {c : Nat} {column : Column}
    {child next parent : Cell} {ref : Ref}
    (h : ColumnValid mountain c column) (hTop : column.back? = some child)
    (hAbove : child.row < next.row) (hPositive : 0 < next.value)
    (hLeft : next.left = some ref) (hRef : ref.column < c)
    (hParent : cellAt mountain ref = .ok parent) (hRow : parent.row ≤ next.row) :
    ColumnValid mountain c (column.push next) := by
  have hCases : ∀ i cell, (column.push next)[i]? = some cell →
      (i = column.size ∧ cell = next) ∨ (i < column.size ∧ column[i]? = some cell) := by
    intro i cell hCell
    by_cases hi : i = column.size
    · subst i
      exact Or.inl ⟨rfl, by simpa using hCell.symm⟩
    · have hOld : column[i]? = some cell := by
        simpa [Array.getElem?_push, hi] using hCell
      exact Or.inr ⟨(Array.getElem?_eq_some_iff.mp hOld).choose, hOld⟩
  have hBelow : ∀ (i : Nat) (cell : Cell), column[i]? = some cell → cell.row < next.row := by
    intro i cell hCell
    have hi := (Array.getElem?_eq_some_iff.mp hCell).choose
    have hLast : column[column.size - 1]? = some child := by
      simpa only [Array.back?_eq_getElem?] using hTop
    by_cases he : i = column.size - 1
    · subst i
      have hSame : cell = child := Option.some.inj (hCell.symm.trans hLast)
      simpa [hSame] using hAbove
    · exact lt_trans (h.rows_strict i (column.size - 1) cell child hCell hLast (by omega)) hAbove
  have hSize := h.size_ge_two
  refine {
    size_ge_two := by simp only [Array.size_push]; omega
    phantom := ?_
    bottom_row := ?_
    rows_strict := ?_
    real_positive := ?_
    stored_valid := ?_
    stored_exists := ?_
    first_values := ?_ }
  · rw [Array.getElem?_push, if_neg (show (0 : Nat) ≠ column.size by omega)]
    exact h.phantom
  · intro cell hCell
    rcases hCases 1 cell hCell with ⟨he, _⟩ | ⟨_, hOld⟩
    · have := h.size_ge_two; omega
    · exact h.bottom_row cell hOld
  · intro i j a b ha hb hij
    rcases hCases i a ha with ⟨rfl, rfl⟩ | ⟨hi, hOldA⟩
    · rcases hCases j b hb with ⟨he, _⟩ | ⟨hj, _⟩ <;> omega
    · rcases hCases j b hb with ⟨_, rfl⟩ | ⟨_, hOldB⟩
      · exact hBelow i a hOldA
      · exact h.rows_strict i j a b hOldA hOldB hij
  · intro i cell hCell hi
    rcases hCases i cell hCell with ⟨_, rfl⟩ | ⟨_, hOld⟩
    · exact hPositive
    · exact h.real_positive i cell hOld hi
  · intro i cell stored hCell hStored
    rcases hCases i cell hCell with ⟨_, rfl⟩ | ⟨_, hOld⟩
    · have he : ref = stored := Option.some.inj (hLeft.symm.trans hStored)
      subst stored
      exact ⟨hRef, parent, hParent, hRow⟩
    · exact h.stored_valid i cell stored hOld hStored
  · intro i cell hCell hi hc
    rcases hCases i cell hCell with ⟨_, rfl⟩ | ⟨_, hOld⟩
    · exact ⟨ref, hLeft⟩
    · exact h.stored_exists i cell hOld hi hc
  · intro _ _ _ _ hc
    omega

theorem cellAt_of_frame_node (mountain : Mountain)
    (u : (Geometry.Frame.ofMountain mountain).Node) :
    cellAt mountain (Geometry.Frame.ref u) = .ok ((Geometry.Frame.ofMountain mountain).cell u) := by
  rcases u with ⟨⟨c, hc⟩, ⟨i, hi⟩⟩
  change c < mountain.size at hc
  change i < mountain[c].size at hi
  exact cellAt_ok_iff.mpr ⟨mountain[c], Array.getElem?_eq_getElem hc,
    Array.getElem?_eq_getElem hi⟩

theorem frame_node_of_cellAt {mountain : Mountain} {ref : Ref} {cell : Cell}
    (h : cellAt mountain ref = .ok cell) :
    ∃ u : (Geometry.Frame.ofMountain mountain).Node,
      Geometry.Frame.ref u = ref ∧ (Geometry.Frame.ofMountain mountain).cell u = cell := by
  obtain ⟨column, hColumn, hCell⟩ := cellAt_ok_iff.mp h
  obtain ⟨hc, he⟩ := Array.getElem?_eq_some_iff.mp hColumn
  subst column
  obtain ⟨hi, hValue⟩ := Array.getElem?_eq_some_iff.mp hCell
  exact ⟨⟨⟨ref.column, hc⟩, ⟨ref.index, hi⟩⟩, rfl, hValue⟩

theorem MountainValid.toOrdered {mountain : Mountain} (h : MountainValid mountain) :
    (Geometry.Frame.ofMountain mountain).Ordered := by
  refine {
    length_ge_two := ?_
    phantom := ?_
    bottom_row := ?_
    rows_strict := ?_
    real_positive := ?_
    stored_valid := ?_ }
  · intro c
    exact (h c.val c.isLt).size_ge_two
  · intro c hc
    have hr := Array.getElem?_eq_getElem hc
    exact Option.some.inj (hr.symm.trans (h c.val c.isLt).phantom)
  · intro c hc
    exact (h c.val c.isLt).bottom_row _ (Array.getElem?_eq_getElem hc)
  · intro c i j hij
    exact (h c.val c.isLt).rows_strict i.val j.val _ _
      (Array.getElem?_eq_getElem i.isLt) (Array.getElem?_eq_getElem j.isLt) hij
  · intro u hu
    exact (h u.1.val u.1.isLt).real_positive u.2.val _
      (Array.getElem?_eq_getElem u.2.isLt) hu
  · intro u ref hLeft
    obtain ⟨hCol, parent, hParent, hRow⟩ :=
      (h u.1.val u.1.isLt).stored_valid u.2.val _ ref
        (Array.getElem?_eq_getElem u.2.isLt) hLeft
    obtain ⟨left, hRef, hCell⟩ := frame_node_of_cellAt hParent
    refine ⟨left, ?_, ?_, ?_⟩
    · rw [← hRef]
      exact Geometry.Frame.lookup_ref _ _
    · have he := congrArg Ref.column hRef
      change left.1.val = ref.column at he
      omega
    · change ((Geometry.Frame.ofMountain mountain).cell left).row ≤ _
      rw [hCell]
      exact hRow

theorem MountainValid.left_sources {mountain : Mountain} (h : MountainValid mountain)
    (u : (Geometry.Frame.ofMountain mountain).Node) (hu : Geometry.Frame.Real u)
    (hc : 0 < u.1.val) :
    ∃ ref, ((Geometry.Frame.ofMountain mountain).cell u).left = some ref :=
  (h u.1.val u.1.isLt).stored_exists u.2.val _ (Array.getElem?_eq_getElem u.2.isLt) hu hc

theorem MountainValid.first_values {mountain : Mountain} (h : MountainValid mountain)
    (u : (Geometry.Frame.ofMountain mountain).Node) (hu : Geometry.Frame.Real u)
    (hc : u.1.val = 0) : (Geometry.Frame.ofMountain mountain).value u = 1 :=
  (h u.1.val u.1.isLt).first_values u.2.val _ (Array.getElem?_eq_getElem u.2.isLt) hu hc

#print axioms initialColumn_valid
#print axioms MountainValid.push
#print axioms ColumnValid.push
#print axioms MountainValid.toOrdered

end OmegaY.Canonical
