/-
Adapted from Phyrion, 1Y-Well-Ordering-Lean, formalization/ZeroY/BMS/PaddedDescent.lean,
revision 6533b2975f3cafb3582dc8f8127e9ea7144d7e69 (Apache-2.0).
Changes: imports and namespaces of the BMS layer renamed to Por.BMS. Imports of modules not ported (ZeroY.BMS.AnyArray) removed; their ported imports added directly. Declarations about the generation and stability framework of the upstream BMS layer (length_pos_of_step through generatedMatrix_strictWellOrder, from the step relation onward) removed; they do not reach the entry theorems. In `expand_matrixLt`, the unfolding of `expandRaw` is replaced by the Por.BMS lemma `expandRaw_of_maximalParentRow_none`.
Taken from koteitan, 1y-wo-por, `ZeroY/BMS/PaddedDescent.lean` (https://github.com/koteitan/1y-wo-por,
revision db86f2d13c2e18a8e2c2fae5e083d00fc4d48a78, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`.
-/
import Googology.Notation.Y.WellOrder.ZeroY.PaddedOrder
import Googology.Notation.Y.WellOrder.ZeroY.Transport

/-!
# BM4 展开的补零字典序下降

所有坐标比较都采用无限尾零约定，允许展开后删除公共尾零行。
-/

namespace ZeroY

open Por.BMS

theorem matrixEntry_eq_entry_getD (array : Matrix) (column row : Nat) :
    matrixEntry array column row = (entry? array column row).getD 0 := by
  simp only [matrixEntry, columnEntry, entry?]
  cases array[column]? <;> simp

theorem matrixEntry_trimZeroRows (array : Matrix) (column row : Nat) :
    matrixEntry (trimZeroRows array) column row = matrixEntry array column row := by
  simp only [matrixEntry_eq_entry_getD]
  by_cases hRow : row < trimHeight array
  · rw [entry?_trimZeroRows_of_lt array column row hRow]
  · rw [entry?_trimZeroRows_eq_none_of_le array column row (by omega)]
    cases hEntry : entry? array column row with
    | none => rfl
    | some value =>
        have hZero : value = 0 := by
          apply Classical.byContradiction
          intro hNonzero
          exact hRow (row_lt_trimHeight_of_entry?_eq_some_of_ne_zero hEntry hNonzero)
        simp [hZero]

namespace MatrixLt

/-- 长度较短且全部已有列逐补零坐标相等时，是真前缀。 -/
theorem of_strict_prefix {a b : Matrix} (hLength : a.length < b.length)
    (hPrefix : ∀ column, column < a.length →
      ∀ row, matrixEntry a column row = matrixEntry b column row) : MatrixLt a b := by
  induction a generalizing b with
  | nil =>
      cases b with
      | nil => simp at hLength
      | cons column rest => exact .nil column rest
  | cons column rest ih =>
      cases b with
      | nil => simp at hLength
      | cons other tail =>
          apply MatrixLt.tail
          · intro row
            exact hPrefix 0 (by simp) row
          · apply ih (by simpa using hLength)
            intro index hIndex row
            exact hPrefix (index + 1) (by simpa using hIndex) row

/-- 首个不同列由首个不同条目决定。 -/
theorem of_first_difference {a b : Matrix} {column row : Nat}
    (hA : column < a.length) (hB : column < b.length)
    (hColumns : ∀ earlier, earlier < column → ∀ index,
      matrixEntry a earlier index = matrixEntry b earlier index)
    (hRows : ∀ earlier, earlier < row →
      matrixEntry a column earlier = matrixEntry b column earlier)
    (hLess : matrixEntry a column row < matrixEntry b column row) :
    MatrixLt a b := by
  induction column generalizing a b with
  | zero =>
      cases a with
      | nil => simp at hA
      | cons first rest =>
          cases b with
          | nil => simp at hB
          | cons other tail => exact .head ⟨row, hRows, hLess⟩
  | succ column ih =>
      cases a with
      | nil => simp at hA
      | cons first rest =>
          cases b with
          | nil => simp at hB
          | cons other tail =>
              apply MatrixLt.tail
              · intro index
                exact hColumns 0 (by omega) index
              · apply ih (by simpa using hA) (by simpa using hB)
                · intro earlier hEarlier index
                  exact hColumns (earlier + 1) (by omega) index
                · exact hRows
                · exact hLess

end MatrixLt

namespace BMS

private theorem first_copy_position {array : ValidArray}
    (context : ExpansionContext array) : context.copyPosition 1 0 = context.lastIndex := by
  simp only [ExpansionContext.copyPosition, ExpansionContext.copyStart,
    ExpansionContext.blockLength, Nat.one_mul, Nat.add_zero]
  have := context.parentColumn_lt_lastIndex
  omega

/-- 首个新增坏根在最大父行以下，逐坐标复制原末列。 -/
theorem first_copy_entry_below {array : ValidArray}
    (context : ExpansionContext array) {index row : Nat}
    (hIndex : 0 < index) (hRow : row < context.maximalRow) :
    entry? (expandRaw array.raw index) context.lastIndex row =
      entry? array.raw context.lastIndex row := by
  have hAncestor := isAncestor_of_lt_row hRow (direct_parent_isAncestor context.parent_eq)
  rcases ancestor_entries_lt hAncestor with
    ⟨firstValue, lastValue, hFirst, hLast, hLess⟩
  have hFirstBad : entry? context.badPart 0 row = some firstValue := by
    rw [context.entry?_badPart context.blockLength_pos]
    simpa using hFirst
  have hFirstAscending : ascending array.raw context.maximalRow
      context.parentColumn 0 row = true := by simp [ascending, hRow]
  rw [← first_copy_position context,
    context.entry?_expandRaw_copy (by omega) context.blockLength_pos]
  rw [ExpansionContext.entry?_copyBlock_first_of_ascending array.raw context.badPart
    context.maximalRow context.parentColumn 1 row firstValue lastValue
    (array.raw[context.lastIndex]?.getD []) hFirstBad hFirstAscending
    (ExpansionContext.getD_getElem?_of_entry?_eq_some array.raw hLast)]
  rw [first_copy_position context, hLast, Nat.one_mul,
    Nat.add_sub_of_le (Nat.le_of_lt hLess)]

/-- 首个新增坏根在最大父行的条目严格小于原末列。 -/
theorem first_copy_entry_at {array : ValidArray}
    (context : ExpansionContext array) {index : Nat} (hIndex : 0 < index) :
    matrixEntry (expandRaw array.raw index) context.lastIndex context.maximalRow <
      matrixEntry array.raw context.lastIndex context.maximalRow := by
  rcases parent_some_entry_lt context.parent_eq with
    ⟨firstValue, lastValue, hFirst, hLast, hLess⟩
  have hFirstBad : entry? context.badPart 0 context.maximalRow = some firstValue := by
    rw [context.entry?_badPart context.blockLength_pos]
    simpa using hFirst
  unfold entry? at hFirstBad
  cases hColumn : context.badPart[0]? with
  | none => simp [hColumn] at hFirstBad
  | some column =>
      have hValue : column[context.maximalRow]? = some firstValue := by
        simpa [hColumn] using hFirstBad
      have hCopied : entry? (expandRaw array.raw index) context.lastIndex
          context.maximalRow = some firstValue := by
        rw [← first_copy_position context,
          context.entry?_expandRaw_copy (by omega) context.blockLength_pos]
        exact ExpansionContext.entry?_copyBlock_of_not_ascending array.raw context.badPart
          context.maximalRow context.parentColumn 1 0 context.maximalRow firstValue
          (array.raw[context.lastIndex]?.getD []) column hColumn hValue
          (by simp [ascending])
      simpa only [matrixEntry_eq_entry_getD, hCopied, hLast, Option.getD_some]
        using hLess

theorem matrixLt_trimmed_take {array : Matrix} {count : Nat}
    (hCount : count < array.length) :
    MatrixLt (trimZeroRows (array.take count)) array := by
  apply MatrixLt.of_strict_prefix
  · simpa [length_trimZeroRows, List.length_take, Nat.min_eq_left (Nat.le_of_lt hCount)]
  · intro column hColumn row
    rw [length_trimZeroRows, List.length_take] at hColumn
    rw [matrixEntry_trimZeroRows]
    simp only [matrixEntry, List.getElem?_take_of_lt (Nat.lt_of_lt_of_le hColumn (Nat.min_le_left _ _))]

/-- 有坏根且复制次数为正时，首个差异发生于原末列的最大父行。 -/
theorem expand_matrixLt_of_context {array : ValidArray}
    (context : ExpansionContext array) {index : Nat} (hIndex : 0 < index) :
    MatrixLt (array.expand index).raw array.raw := by
  apply MatrixLt.of_first_difference (column := context.lastIndex)
    (row := context.maximalRow)
  · rw [← first_copy_position context]
    exact context.copyPosition_lt_length (by omega) context.blockLength_pos
  · rw [context.array_length]
    omega
  · intro earlier hEarlier row
    change matrixEntry (trimZeroRows (expandRaw array.raw index)) earlier row = _
    rw [matrixEntry_trimZeroRows, matrixEntry_eq_entry_getD, matrixEntry_eq_entry_getD,
      context.entry?_expandRaw_eq_of_lt_lastIndex index hEarlier]
  · intro row hRow
    change matrixEntry (trimZeroRows (expandRaw array.raw index)) context.lastIndex row = _
    rw [matrixEntry_trimZeroRows, matrixEntry_eq_entry_getD, matrixEntry_eq_entry_getD,
      first_copy_entry_below context hIndex hRow]
  · change matrixEntry (trimZeroRows (expandRaw array.raw index))
      context.lastIndex context.maximalRow < _
    rw [matrixEntry_trimZeroRows]
    exact first_copy_entry_at context hIndex

/-- 任意非空合法矩阵的一步展开在补零字典序下严格下降。 -/
theorem expand_matrixLt (array : ValidArray) (index : Nat)
    (hLength : 0 < array.raw.length) : MatrixLt (array.expand index).raw array.raw := by
  by_cases hIndex : index = 0
  · subst index
    rw [array.raw_expand_zero]
    exact matrixLt_trimmed_take (by omega)
  · cases hMaximal : maximalParentRow array.raw with
    | none =>
        have hRaw : (array.expand index).raw =
            trimZeroRows (array.raw.take (array.raw.length - 1)) := by
          rw [ValidArray.raw_expand]
          unfold Por.BMS.expand
          rw [expandRaw_of_maximalParentRow_none hMaximal]
        rw [hRaw]
        exact matrixLt_trimmed_take (by omega)
    | some maximalRow =>
        let context := Classical.choice
          (exists_expansionContext_of_maximalParentRow_eq_some hMaximal)
        exact expand_matrixLt_of_context context (by omega)

end BMS
end ZeroY
