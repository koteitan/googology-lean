/-
Por.BMS.Array: rectangular and valid arrays, the lemmas about deleting all-zero rows
(`trimZeroRows`) and about column heights, the expansion as a valid array, and the
strict well-order structure used in the final theorem types.

Written independently from the BM4 rule. The statements (names, binders, binder names,
structure field names) are fixed by how the imported 0-Y / 1-Y core
(Phyrion1343/1Y-Well-Ordering-Lean, `formalization/{ZeroY,OneY}`, Apache-2.0) calls them.
Lean core only; no Mathlib.
Taken from koteitan, 1y-wo-por, `Por/BMS/Array.lean` (https://github.com/koteitan/1y-wo-por,
revision db86f2d13c2e18a8e2c2fae5e083d00fc4d48a78, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`.
-/
import Googology.Notation.Y.WellOrder.Por.BMS.Search

namespace Por.BMS

/-! ## Structures -/

/-- An array whose columns all have the same length. -/
structure RectangularArray where
  raw : BMSArray
  rectangular_eq : rectangular raw = true

/-- A rectangular array with no all-zero rows at the bottom. -/
structure ValidArray extends RectangularArray where
  trimmed_eq : trimZeroRows raw = raw

namespace ValidArray

/-- Two valid arrays with the same entries are equal. -/
theorem ext {left right : ValidArray} (hRaw : left.raw = right.raw) :
    left = right := by
  obtain ⟨⟨leftRaw, leftRectangular⟩, leftTrimmed⟩ := left
  obtain ⟨⟨rightRaw, rightRectangular⟩, rightTrimmed⟩ := right
  change leftRaw = rightRaw at hRaw
  subst hRaw
  rfl

end ValidArray

/-! ## Support height of one column -/

theorem supportHeight_le_length (column : List Nat) :
    supportHeight column ≤ column.length := by
  induction column with
  | nil => simp [supportHeight]
  | cons value rest ih =>
      simp only [supportHeight, List.length_cons]
      split <;> omega

/-- One step of `supportHeight`. -/
theorem supportHeight_cons (first : Nat) (rest : List Nat) :
    supportHeight (first :: rest) =
      (if supportHeight rest = 0 ∧ first = 0 then 0 else supportHeight rest + 1) := rfl

/-- Entries at or below the support height are zero. -/
theorem eq_zero_of_supportHeight_le {column : List Nat} {row value : Nat}
    (hEntry : column[row]? = some value) (hRow : supportHeight column ≤ row) :
    value = 0 := by
  induction column generalizing row
  case nil => simp at hEntry
  case cons first rest ih =>
    rw [supportHeight_cons] at hRow
    cases row
    case zero =>
      rw [List.getElem?_cons_zero, Option.some.injEq] at hEntry
      split at hRow <;> omega
    case succ row =>
      rw [List.getElem?_cons_succ] at hEntry
      exact ih hEntry (by split at hRow <;> omega)

/-- A nonzero entry lies above the support height. -/
theorem lt_supportHeight_of_ne_zero {column : List Nat} {row value : Nat}
    (hEntry : column[row]? = some value) (hValue : value ≠ 0) :
    row < supportHeight column := by
  apply Nat.lt_of_not_le
  intro hRow
  exact hValue (eq_zero_of_supportHeight_le hEntry hRow)

/-- Cutting a column at or below its support height keeps the support height. -/
theorem supportHeight_take {column : List Nat} {count : Nat}
    (hCount : supportHeight column ≤ count) :
    supportHeight (column.take count) = supportHeight column := by
  induction column generalizing count
  case nil => simp
  case cons first rest ih =>
    rw [supportHeight_cons] at hCount
    cases count
    case zero =>
      split at hCount
      · next hBoth =>
          rw [List.take_zero, supportHeight_cons, if_pos hBoth]
          rfl
      · omega
    case succ count =>
      have hRest : supportHeight rest ≤ count := by split at hCount <;> omega
      rw [List.take_succ_cons, supportHeight_cons, supportHeight_cons, ih hRest]

/-! ## `trimHeight` -/

theorem trimHeight_nil : trimHeight [] = 0 := rfl

private theorem foldl_max_supportHeight (array : BMSArray) (initial : Nat) :
    array.foldl (fun result column => max result (supportHeight column)) initial =
      max initial (trimHeight array) := by
  unfold trimHeight
  induction array generalizing initial
  case nil => simp
  case cons first rest ih =>
    rw [List.foldl_cons, List.foldl_cons, ih (max initial (supportHeight first)),
      ih (max 0 (supportHeight first)), Nat.zero_max, Nat.max_assoc]

theorem trimHeight_cons (column : List Nat) (array : BMSArray) :
    trimHeight (column :: array) = max (supportHeight column) (trimHeight array) := by
  simp only [trimHeight, List.foldl_cons, Nat.zero_max]
  exact foldl_max_supportHeight array (supportHeight column)

theorem trimHeight_le_iff {array : BMSArray} {bound : Nat} :
    trimHeight array ≤ bound ↔ ∀ column ∈ array, supportHeight column ≤ bound := by
  induction array with
  | nil => simp [trimHeight_nil]
  | cons first rest ih =>
      simp only [trimHeight_cons, Nat.max_le, ih, List.mem_cons, forall_eq_or_imp]

theorem supportHeight_le_trimHeight {array : BMSArray} {column : List Nat}
    (hColumn : column ∈ array) : supportHeight column ≤ trimHeight array :=
  trimHeight_le_iff.mp (Nat.le_refl _) column hColumn

theorem trimHeight_map_of_supportHeight {array : BMSArray} {f : List Nat → List Nat}
    (hSame : ∀ column ∈ array, supportHeight (f column) = supportHeight column) :
    trimHeight (array.map f) = trimHeight array := by
  induction array with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.map_cons, trimHeight_cons]
      rw [hSame first (List.mem_cons_self ..),
        ih (fun column h => hSame column (List.mem_cons_of_mem _ h))]

/-! ## `rectangular` and `UniformHeight` -/

theorem rectangular_iff_exists_uniformHeight {array : BMSArray} :
    rectangular array = true ↔ ∃ height, UniformHeight height array := by
  match array with
  | [] => exact ⟨fun _ => ⟨0, fun column hColumn => by simp at hColumn⟩, fun _ => rfl⟩
  | first :: rest =>
      unfold rectangular
      rw [List.all_eq_true]
      constructor
      · intro hAll
        exact ⟨first.length, fun column hColumn =>
          (List.mem_cons.mp hColumn).elim (fun hFirst => by rw [hFirst])
            (fun hRest => beq_iff_eq.mp (hAll column hRest))⟩
      · rintro ⟨height, hUniform⟩ column hColumn
        apply beq_iff_eq.mpr
        rw [hUniform column (List.mem_cons_of_mem _ hColumn),
          hUniform first (List.mem_cons_self ..)]

theorem row_lt_uniformHeight_of_entry?_eq_some {array : BMSArray}
    {height column row value : Nat}
    (hUniform : UniformHeight height array)
    (hEntry : entry? array column row = some value) : row < height := by
  obtain ⟨found, hFound, hValue⟩ := entry?_eq_some_iff.mp hEntry
  rw [← hUniform found (List.mem_of_getElem? hFound)]
  exact (List.getElem?_eq_some_iff.mp hValue).1

theorem row_lt_trimHeight_of_entry?_eq_some_of_ne_zero {array : BMSArray}
    {column row value : Nat}
    (hEntry : entry? array column row = some value)
    (hValue : value ≠ 0) : row < trimHeight array := by
  obtain ⟨found, hFound, hFoundValue⟩ := entry?_eq_some_iff.mp hEntry
  exact Nat.lt_of_lt_of_le (lt_supportHeight_of_ne_zero hFoundValue hValue)
    (supportHeight_le_trimHeight (List.mem_of_getElem? hFound))

theorem exists_entry_of_uniformHeight {array : BMSArray} {height column row : Nat}
    (hUniform : UniformHeight height array)
    (hColumn : column < array.length) (hRow : row < height) :
    ∃ value, entry? array column row = some value := by
  have hLength : array[column].length = height :=
    hUniform _ (List.getElem_mem hColumn)
  refine ⟨array[column][row]'(by omega), ?_⟩
  simp [entry?, List.getElem?_eq_getElem hColumn]

/-! ## `trimZeroRows` -/

@[simp] theorem length_trimZeroRows (array : BMSArray) :
    (trimZeroRows array).length = array.length := by
  simp [trimZeroRows]

theorem trimHeight_trimZeroRows (array : BMSArray) :
    trimHeight (trimZeroRows array) = trimHeight array := by
  unfold trimZeroRows
  exact trimHeight_map_of_supportHeight fun column hColumn =>
    supportHeight_take (supportHeight_le_trimHeight hColumn)

theorem trimZeroRows_idempotent (array : BMSArray) :
    trimZeroRows (trimZeroRows array) = trimZeroRows array := by
  show (trimZeroRows array).map (·.take (trimHeight (trimZeroRows array))) = trimZeroRows array
  rw [trimHeight_trimZeroRows]
  simp only [trimZeroRows, List.map_map, Function.comp_def, List.take_take, Nat.min_self]

theorem entry?_trimZeroRows_of_lt (array : BMSArray) (column row : Nat)
    (hRow : row < trimHeight array) :
    entry? (trimZeroRows array) column row = entry? array column row := by
  simp only [entry?, trimZeroRows, List.getElem?_map]
  match array[column]? with
  | none => rfl
  | some found => simp [hRow]

theorem entry?_trimZeroRows_eq_none_of_le (array : BMSArray) (column row : Nat)
    (hRow : trimHeight array ≤ row) :
    entry? (trimZeroRows array) column row = none := by
  simp only [entry?, trimZeroRows, List.getElem?_map]
  match array[column]? with
  | none => rfl
  | some found => simp [List.getElem?_take, Nat.not_lt.mpr hRow]

theorem uniformHeight_trimZeroRows {array : BMSArray} {height : Nat}
    (hUniform : UniformHeight height array) :
    UniformHeight (trimHeight array) (trimZeroRows array) := by
  intro column hColumn
  unfold trimZeroRows at hColumn
  obtain ⟨original, hOriginal, rfl⟩ := List.mem_map.mp hColumn
  have hLength : original.length = height := hUniform original hOriginal
  have hBound : trimHeight array ≤ height := by
    apply trimHeight_le_iff.mpr
    intro other hOther
    rw [← hUniform other hOther]
    exact supportHeight_le_length other
  simp only [List.length_take]
  omega

theorem rectangular_trimZeroRows {array : BMSArray}
    (hRectangular : rectangular array = true) :
    rectangular (trimZeroRows array) = true := by
  obtain ⟨height, hUniform⟩ := rectangular_iff_exists_uniformHeight.mp hRectangular
  apply rectangular_iff_exists_uniformHeight.2
  exact ⟨trimHeight array, uniformHeight_trimZeroRows hUniform⟩

/-- On rows above `trimHeight`, deleting all-zero rows does not change the parent. -/
theorem parent_trimZeroRows_of_lt (array : BMSArray) {row : Nat}
    (hRow : row < trimHeight array) (target : Nat) :
    parent row (trimZeroRows array) target = parent row array target := by
  induction row generalizing target
  case zero =>
    have hEntry := fun column => entry?_trimZeroRows_of_lt array column 0 hRow
    simp only [parent, searchLeft, entryLt, length_trimZeroRows, hEntry]
  case succ row ih =>
    have hEntry := fun column => entry?_trimZeroRows_of_lt array column (row + 1) hRow
    have hLower : parent row (trimZeroRows array) = parent row array :=
      funext (ih (Nat.lt_of_succ_lt hRow))
    simp only [parent, searchLeft, entryLt, length_trimZeroRows, hEntry, hLower]

/-- On a row at or below `trimHeight`, the trimmed array has no parent. -/
theorem parent_trimZeroRows_eq_none_of_le (array : BMSArray) {row : Nat}
    (hRow : trimHeight array ≤ row) (target : Nat) :
    parent row (trimZeroRows array) target = none := by
  have hEntry : ∀ column, entry? (trimZeroRows array) column row = none :=
    fun column => entry?_trimZeroRows_eq_none_of_le array column row hRow
  rw [parent_eq_greatestBelow? row (trimZeroRows array) target]
  split
  · refine greatestBelow?_eq_none_iff.mpr fun candidate _ => ?_
    cases row <;> simp [parentEligible, entryLt, hEntry]
  · rfl

/-! ## Expansion keeps the column height -/

theorem mem_slice {array : BMSArray} {start count : Nat} {column : List Nat}
    (hColumn : column ∈ slice array start count) : column ∈ array :=
  List.mem_of_mem_drop (List.mem_of_mem_take hColumn)

theorem length_of_mem_copyBlock {array block : BMSArray}
    {m₀ parentColumn copyNumber : Nat} {lastColumn column : List Nat}
    (hColumn : column ∈ copyBlock array block m₀ parentColumn copyNumber lastColumn) :
    ∃ original ∈ block, column.length = original.length := by
  unfold copyBlock at hColumn
  obtain ⟨localColumn, hLocal, rfl⟩ := List.mem_mapIdx.mp hColumn
  exact ⟨block[localColumn], List.getElem_mem hLocal, List.length_mapIdx⟩

theorem uniformHeight_expandRaw {height index : Nat} {array : BMSArray}
    (hUniform : UniformHeight height array) :
    UniformHeight height (expandRaw array index) := by
  intro column hColumn
  unfold expandRaw at hColumn
  split at hColumn
  · exact hUniform column (List.mem_of_mem_take hColumn)
  · rcases List.mem_append.mp hColumn with hGood | hCopies
    · exact hUniform column (List.mem_of_mem_take hGood)
    · obtain ⟨_, _, hInCopy⟩ := List.mem_flatMap.mp hCopies
      obtain ⟨original, hOriginal, hSameLength⟩ := length_of_mem_copyBlock hInCopy
      exact hSameLength.trans (hUniform original (mem_slice hOriginal))

/-- The copy number 0 of the bad part is the bad part itself. -/
theorem copyBlock_zero (array block : BMSArray) (m₀ parentColumn : Nat)
    (lastColumn : List Nat) :
    copyBlock array block m₀ parentColumn 0 lastColumn = block := by
  apply List.ext_getElem (by simp [copyBlock])
  intro localColumn _ _
  apply List.ext_getElem (by simp [copyBlock])
  intro row _ _
  simp [copyBlock, copiedEntry]

/-- `A[0]` before deleting rows is `A` without its last column. -/
theorem expandRaw_zero (array : BMSArray) :
    expandRaw array 0 = array.take (array.length - 1) := by
  unfold expandRaw
  split
  · rfl
  · next m₀ root hPivot =>
      have hRoot := (parent_eq_some_facts (expansionPivot?_eq_some_iff.mp hPivot).2).2.1
      rw [List.range_one, List.flatMap_cons, List.flatMap_nil, List.append_nil, copyBlock_zero,
        slice, ← List.take_add, Nat.add_sub_cancel' (Nat.le_of_lt hRoot)]

namespace ValidArray

/-- The BM4 expansion `A[index]` as a valid array. -/
def expand (array : ValidArray) (index : Nat) : ValidArray where
  raw := BMS.expand array.raw index
  rectangular_eq := by
    obtain ⟨height, hUniform⟩ :=
      rectangular_iff_exists_uniformHeight.mp array.rectangular_eq
    exact rectangular_trimZeroRows
      (rectangular_iff_exists_uniformHeight.mpr ⟨height, uniformHeight_expandRaw hUniform⟩)
  trimmed_eq := trimZeroRows_idempotent _

theorem raw_expand (array : ValidArray) (index : Nat) :
    (array.expand index).raw = BMS.expand array.raw index := rfl

theorem raw_expand_zero (array : ValidArray) :
    (array.expand 0).raw =
      trimZeroRows (array.raw.take (array.raw.length - 1)) := by
  change trimZeroRows (expandRaw array.raw 0) = _
  rw [expandRaw_zero]

end ValidArray

end Por.BMS

namespace Por

/-- A strict well-order: well-founded, transitive and trichotomous. -/
structure StrictWellOrder (Carrier : Type) (relation : Carrier → Carrier → Prop) :
    Prop where
  wellFounded : WellFounded relation
  transitive : ∀ {first second third},
    relation first second → relation second third → relation first third
  trichotomy : ∀ first second,
    first = second ∨ relation first second ∨ relation second first

end Por
