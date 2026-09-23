/-
Por.BMS.Context: the data of one BM4 expansion step (`ExpansionContext`) and the lemmas
that locate the good part and the copies of the bad part inside `A[n]`.

Written independently from the BM4 rule. The statements (names, binders, binder names,
structure field names) are fixed by how the imported 0-Y / 1-Y core
(Phyrion1343/1Y-Well-Ordering-Lean, `formalization/{ZeroY,OneY}`, Apache-2.0) calls them.
Lean core only; no Mathlib.

Notation in the comments: `c` is the last column (`lastIndex`), `m₀` the largest row in
which `c` has a parent (`maximalRow`), `p` the bad root (`parentColumn`), `s = c - p` the
length of the bad part (`blockLength`). `A[n]` before deleting zero rows is
`A[0..p) ++ B⁽⁰⁾ ++ ... ++ B⁽ⁿ⁾`, where `B⁽q⁾` is the `q`-th copy of the bad part.
The Lemma 2.5 group (`Lemma25AtRow`, `Lemma25`, `lemma25_all`, ...) is in
`Por.BMS.CopyLemma`.
Taken from koteitan, 1y-wo-por, `Por/BMS/Context.lean` (https://github.com/koteitan/1y-wo-por,
revision db86f2d13c2e18a8e2c2fae5e083d00fc4d48a78, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`.
-/
import Googology.Notation.Y.WellOrder.Por.BMS.ParentAncestor

namespace Por.BMS

/-! ## The expansion context -/

/-- The data of one BM4 expansion step of a nonempty array whose last column has a parent:
`c = lastIndex`, `m₀ = maximalRow`, bad root `p = parentColumn`. -/
structure ExpansionContext (array : ValidArray) where
  lastIndex : Nat
  maximalRow : Nat
  parentColumn : Nat
  array_length : array.raw.length = lastIndex + 1
  maximal_row_eq : maximalParentRow array.raw = some maximalRow
  parent_eq : parent maximalRow array.raw lastIndex = some parentColumn

theorem exists_expansionContext_of_maximalParentRow_eq_some
    {array : ValidArray} {maximalRow : Nat}
    (hMaximal : maximalParentRow array.raw = some maximalRow) :
    Nonempty (ExpansionContext array) := by
  have hMaximal' := hMaximal
  unfold maximalParentRow at hMaximal'
  split at hMaximal'
  · cases hMaximal'
  · next lastIndex hLength =>
      obtain ⟨parentColumn, hParent⟩ :=
        Option.isSome_iff_exists.mp (greatestBelow?_some_satisfies hMaximal')
      exact ⟨⟨lastIndex, maximalRow, parentColumn, hLength, hMaximal, hParent⟩⟩

namespace ExpansionContext

/-! ## Derived definitions -/

/-- The length `s = c - p` of the bad part. -/
def blockLength {array : ValidArray} (context : ExpansionContext array) : Nat :=
  context.lastIndex - context.parentColumn

/-- The first column `p + q s` of copy `q`. -/
def copyStart {array : ValidArray} (context : ExpansionContext array)
    (copyNumber : Nat) : Nat :=
  context.parentColumn + copyNumber * context.blockLength

/-- The column `p + q s + j` of `A[n]` that is the `j`-th column of copy `q`. -/
def copyPosition {array : ValidArray} (context : ExpansionContext array)
    (copyNumber localColumn : Nat) : Nat :=
  context.copyStart copyNumber + localColumn

/-- Column `column` lies in copy `copyNumber`: `p + q s ≤ column < p + (q+1) s`. -/
def InCopy {array : ValidArray} (context : ExpansionContext array)
    (copyNumber column : Nat) : Prop :=
  context.copyStart copyNumber ≤ column ∧ column < context.copyStart (copyNumber + 1)

/-- The bad part: the columns `p, ..., c - 1`. -/
def badPart {array : ValidArray} (context : ExpansionContext array) : BMSArray :=
  slice array.raw context.parentColumn context.blockLength

/-- The entry in row `row` of column `localColumn` of copy `copyNumber`, where `value` is the
entry of the bad part there (see `copiedEntry` in `Por.BMS.Defs`). -/
def copiedValue (array block : BMSArray) (m₀ parentColumn copyNumber localColumn row value : Nat)
    (lastColumn : List Nat) : Nat :=
  copiedEntry array block m₀ parentColumn copyNumber localColumn row value lastColumn

/-! ## Arithmetic of the positions -/

theorem parentColumn_lt_lastIndex {array : ValidArray}
    (context : ExpansionContext array) :
    context.parentColumn < context.lastIndex :=
  parent_some_lt context.parent_eq

theorem blockLength_pos {array : ValidArray} (context : ExpansionContext array) :
    0 < context.blockLength := by
  have h := context.parentColumn_lt_lastIndex
  simp only [blockLength]
  omega

theorem copyPosition_zero {array : ValidArray} (context : ExpansionContext array)
    (localColumn : Nat) :
    context.copyPosition 0 localColumn = context.parentColumn + localColumn := by
  unfold copyPosition copyStart
  rw [Nat.zero_mul, Nat.add_zero]

theorem inCopy_iff_exists_copyPosition {array : ValidArray}
    (context : ExpansionContext array) {copyNumber column : Nat} :
    context.InCopy copyNumber column ↔
      ∃ localColumn, localColumn < context.blockLength ∧
        column = context.copyPosition copyNumber localColumn := by
  have hSucc : (copyNumber + 1) * context.blockLength =
      copyNumber * context.blockLength + context.blockLength := Nat.succ_mul _ _
  simp only [InCopy, copyPosition, copyStart]
  constructor
  · intro ⟨hLow, hHigh⟩
    refine ⟨column - (context.parentColumn + copyNumber * context.blockLength), ?_, ?_⟩
    · omega
    · omega
  · rintro ⟨localColumn, hLocal, rfl⟩
    omega

/-! ## The bad part -/

theorem length_badPart {array : ValidArray} (context : ExpansionContext array) :
    context.badPart.length = context.blockLength := by
  have hLength := context.array_length
  have hLt := context.parentColumn_lt_lastIndex
  simp only [badPart, slice, blockLength, List.length_take, List.length_drop]
  omega

theorem getElem?_badPart {array : ValidArray} (context : ExpansionContext array)
    {localColumn : Nat} (hLocal : localColumn < context.blockLength) :
    context.badPart[localColumn]? = array.raw[context.parentColumn + localColumn]? := by
  simp only [badPart, slice, List.getElem?_take_of_lt hLocal, List.getElem?_drop]

theorem entry?_badPart {array : ValidArray} (context : ExpansionContext array)
    {localColumn row : Nat} (hLocal : localColumn < context.blockLength) :
    entry? context.badPart localColumn row =
      entry? array.raw (context.parentColumn + localColumn) row := by
  simp only [entry?, context.getElem?_badPart hLocal]

theorem exists_badPart_entry {array : ValidArray} (context : ExpansionContext array)
    {height localColumn row : Nat}
    (hUniform : UniformHeight height array.raw)
    (hLocal : localColumn < context.blockLength)
    (hRow : row < height) :
    ∃ column value,
      context.badPart[localColumn]? = some column ∧
        column[row]? = some value := by
  have hLength := context.array_length
  have hBlock : context.blockLength = context.lastIndex - context.parentColumn := rfl
  have hLt := context.parentColumn_lt_lastIndex
  obtain ⟨value, hValue⟩ := exists_entry_of_uniformHeight (column :=
    context.parentColumn + localColumn) hUniform (by omega) hRow
  rw [← context.entry?_badPart hLocal] at hValue
  unfold entry? at hValue
  cases hColumn : context.badPart[localColumn]? with
  | none => simp [hColumn] at hValue
  | some column =>
      simp only [hColumn, Option.bind_some] at hValue
      exact ⟨column, value, rfl, hValue⟩

/-! ## Copies of the bad part -/

theorem getElem?_copyBlock (array block : BMSArray)
    (m₀ parentColumn copyNumber localColumn : Nat) (lastColumn : List Nat) :
    (copyBlock array block m₀ parentColumn copyNumber lastColumn)[localColumn]? =
      block[localColumn]?.map (List.mapIdx fun row value =>
        copiedEntry array block m₀ parentColumn copyNumber localColumn row value lastColumn) := by
  simp only [copyBlock, List.getElem?_mapIdx]

theorem length_copyBlock (array block : BMSArray)
    (m₀ parentColumn copyNumber : Nat) (lastColumn : List Nat) :
    (copyBlock array block m₀ parentColumn copyNumber lastColumn).length = block.length := by
  simp [copyBlock]

theorem entry?_copyBlock (array block : BMSArray)
    (m₀ parentColumn copyNumber localColumn row value : Nat) (lastColumn column : List Nat)
    (hColumn : block[localColumn]? = some column)
    (hValue : column[row]? = some value) :
    entry? (copyBlock array block m₀ parentColumn copyNumber lastColumn) localColumn row = some
      (copiedValue array block m₀ parentColumn copyNumber localColumn row value lastColumn) := by
  apply entry?_eq_some_iff.mpr
  refine ⟨_, by rw [getElem?_copyBlock, hColumn]; rfl, ?_⟩
  rw [List.getElem?_mapIdx, hValue]
  rfl

theorem entry?_copyBlock_first_of_ascending (array block : BMSArray)
    (m₀ parentColumn copyNumber row firstValue lastValue : Nat)
    (lastColumn : List Nat)
    (hFirstEntry : entry? block 0 row = some firstValue)
    (hAscending : ascending array m₀ parentColumn 0 row = true)
    (hLast : lastColumn[row]? = some lastValue) :
    entry? (copyBlock array block m₀ parentColumn copyNumber lastColumn) 0 row = some
      (firstValue + copyNumber * (lastValue - firstValue)) := by
  obtain ⟨first, hFirst, hFirstValue⟩ := entry?_eq_some_iff.mp hFirstEntry
  have hHead : block.head?.getD [] = first := by
    rw [List.head?_eq_getElem?, hFirst]
    rfl
  have hCopied := entry?_copyBlock array block m₀ parentColumn copyNumber 0 row firstValue
    lastColumn first hFirst hFirstValue
  rw [hCopied]
  simp [copiedValue, copiedEntry, rowGap, hAscending, hHead, hFirstValue, hLast]

theorem getD_getElem?_of_entry?_eq_some (array : BMSArray)
    {column row value : Nat} (hEntry : entry? array column row = some value) :
    (array[column]?.getD [])[row]? = some value := by
  obtain ⟨found, hFound, hValue⟩ := entry?_eq_some_iff.mp hEntry
  rw [hFound, Option.getD_some]
  exact hValue

theorem entry?_copyBlock_of_not_ascending (array block : BMSArray)
    (m₀ parentColumn copyNumber localColumn row value : Nat) (lastColumn column : List Nat)
    (hColumn : block[localColumn]? = some column)
    (hValue : column[row]? = some value)
    (hAscending : ascending array m₀ parentColumn localColumn row = false) :
    entry? (copyBlock array block m₀ parentColumn copyNumber lastColumn) localColumn row =
      some value := by
  have hCopied := entry?_copyBlock array block m₀ parentColumn copyNumber localColumn row value
    lastColumn column hColumn hValue
  rw [hCopied]
  simp [copiedValue, copiedEntry, hAscending]

/-! ## Ascending entries along ancestors -/

theorem ascending_of_ancestor_of_ascending
    (array : BMSArray) (m₀ parentColumn : Nat)
    {row candidateLocal targetLocal : Nat}
    (hAncestor : isAncestor array row
      (parentColumn + candidateLocal) (parentColumn + targetLocal) = true)
    (hTargetAscending : ascending array m₀ parentColumn targetLocal row = true) :
    ascending array m₀ parentColumn candidateLocal row = true := by
  have hLt := isAncestor_lt hAncestor
  simp only [ascending, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    beq_iff_eq] at hTargetAscending ⊢
  refine ⟨hTargetAscending.1, ?_⟩
  by_cases hCandidate : candidateLocal = 0
  · exact Or.inl hCandidate
  · right
    have hRoot : isAncestor array row parentColumn (parentColumn + targetLocal) = true := by
      rcases hTargetAscending.2 with hZero | hRoot
      · omega
      · exact hRoot
    have hDecrease : ∀ {larger smaller},
        parent row array larger = some smaller → smaller < larger :=
      fun hFound => parent_some_lt hFound
    rcases parentTransGen_comparable hDecrease
        (isAncestor_iff_strictAncestor.mp hRoot)
        (isAncestor_iff_strictAncestor.mp hAncestor) with hEq | hPath | hPath
    · omega
    · have := transGen_lt_of_decrease hDecrease hPath
      omega
    · exact isAncestor_iff_strictAncestor.mpr hPath

theorem ascending_eq_of_ancestor
    (array : BMSArray) (m₀ parentColumn : Nat)
    {row candidateLocal targetLocal : Nat}
    (hAncestor : isAncestor array row
      (parentColumn + candidateLocal) (parentColumn + targetLocal) = true) :
    ascending array m₀ parentColumn candidateLocal row =
      ascending array m₀ parentColumn targetLocal row := by
  refine bool_eq_of_true_iff ⟨fun hCandidate => ?_,
    ascending_of_ancestor_of_ascending array m₀ parentColumn hAncestor⟩
  · have hLt := isAncestor_lt hAncestor
    simp only [ascending, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
      beq_iff_eq] at hCandidate ⊢
    refine ⟨hCandidate.1, Or.inr ?_⟩
    rcases hCandidate.2 with hZero | hRoot
    · subst hZero
      simpa using hAncestor
    · exact isAncestor_trans hRoot hAncestor

/-! ## The shape of `expandRaw` -/

/-- `A[n]` before deleting rows: the good part followed by the copies `0, ..., n`. -/
theorem expandRaw_eq {array : ValidArray} (context : ExpansionContext array)
    (index : Nat) :
    expandRaw array.raw index =
      array.raw.take context.parentColumn ++
        (List.range (index + 1)).flatMap (fun copyNumber =>
          copyBlock array.raw context.badPart context.maximalRow context.parentColumn
            copyNumber (array.raw[context.lastIndex]?.getD [])) := by
  have hLast : array.raw.length - 1 = context.lastIndex := by
    rw [context.array_length, Nat.add_sub_cancel]
  have hPivot : expansionPivot? array.raw = some (context.maximalRow, context.parentColumn) := by
    rw [expansionPivot?_eq_some_iff, hLast]
    exact ⟨context.maximal_row_eq, context.parent_eq⟩
  unfold expandRaw
  rw [hPivot]
  dsimp only
  rw [hLast]
  rfl

/-- The concatenation of `count` blocks of length `size`. -/
private theorem length_flatMap_range {f : Nat → BMSArray} {size : Nat}
    (hSize : ∀ copyNumber, (f copyNumber).length = size) (count : Nat) :
    ((List.range count).flatMap f).length = count * size := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [List.range_succ, List.flatMap_append, List.length_append, ih]
      simp [hSize, Nat.succ_mul]

private theorem getElem?_flatMap_range {f : Nat → BMSArray} {size : Nat}
    (hSize : ∀ copyNumber, (f copyNumber).length = size) {count copyNumber localColumn : Nat}
    (hCopy : copyNumber < count) (hLocal : localColumn < size) :
    ((List.range count).flatMap f)[copyNumber * size + localColumn]? =
      (f copyNumber)[localColumn]? := by
  induction count with
  | zero => omega
  | succ count ih =>
      simp only [List.range_succ, List.flatMap_append]
      by_cases hLast : copyNumber < count
      · have hLe : (copyNumber + 1) * size ≤ count * size :=
          Nat.mul_le_mul_right _ hLast
        have hSucc : (copyNumber + 1) * size = copyNumber * size + size := Nat.succ_mul _ _
        have hIndex : copyNumber * size + localColumn <
            ((List.range count).flatMap f).length := by
          rw [length_flatMap_range hSize]
          omega
        rw [List.getElem?_append_left hIndex, ih hLast]
      · have hEq : copyNumber = count := by omega
        subst hEq
        have hIndex : ((List.range copyNumber).flatMap f).length ≤
            copyNumber * size + localColumn := by
          rw [length_flatMap_range hSize]
          omega
        rw [List.getElem?_append_right hIndex, length_flatMap_range hSize]
        simp

theorem length_copyBlock_badPart {array : ValidArray} (context : ExpansionContext array)
    (copyNumber : Nat) :
    (copyBlock array.raw context.badPart context.maximalRow context.parentColumn
      copyNumber (array.raw[context.lastIndex]?.getD [])).length = context.blockLength := by
  rw [length_copyBlock, length_badPart]

theorem length_expandRaw {array : ValidArray} (context : ExpansionContext array)
    (index : Nat) :
    (expandRaw array.raw index).length =
      context.parentColumn + (index + 1) * context.blockLength := by
  have hLength := context.array_length
  have hLt := context.parentColumn_lt_lastIndex
  rw [context.expandRaw_eq, List.length_append, List.length_take,
    length_flatMap_range (length_copyBlock_badPart context)]
  omega

/-- A column of the good part is unchanged. -/
theorem getElem?_expandRaw_of_lt_parentColumn {array : ValidArray}
    (context : ExpansionContext array) (index : Nat) {column : Nat}
    (hColumn : column < context.parentColumn) :
    (expandRaw array.raw index)[column]? = array.raw[column]? := by
  have hLength := context.array_length
  have hLt := context.parentColumn_lt_lastIndex
  have hTake : column < (array.raw.take context.parentColumn).length := by
    simp; omega
  rw [context.expandRaw_eq, List.getElem?_append_left hTake,
    List.getElem?_take_of_lt hColumn]

/-- The `j`-th column of copy `q ≤ n` of `A[n]`. -/
theorem getElem?_expandRaw_copy {array : ValidArray}
    (context : ExpansionContext array) {index copyNumber localColumn : Nat}
    (hCopy : copyNumber ≤ index) (hLocal : localColumn < context.blockLength) :
    (expandRaw array.raw index)[context.copyPosition copyNumber localColumn]? =
      (copyBlock array.raw context.badPart context.maximalRow
        context.parentColumn copyNumber
        (array.raw[context.lastIndex]?.getD []))[localColumn]? := by
  have hLength := context.array_length
  have hLt := context.parentColumn_lt_lastIndex
  have hTake : (array.raw.take context.parentColumn).length = context.parentColumn := by
    simp; omega
  have hIndex : (array.raw.take context.parentColumn).length ≤
      context.parentColumn + (copyNumber * context.blockLength + localColumn) := by
    rw [hTake]
    omega
  rw [context.expandRaw_eq, copyPosition, copyStart, Nat.add_assoc,
    List.getElem?_append_right hIndex, hTake, Nat.add_sub_cancel_left,
    getElem?_flatMap_range (length_copyBlock_badPart context) (Nat.lt_succ_of_le hCopy)
      hLocal]

theorem entry?_expandRaw_copy {array : ValidArray}
    (context : ExpansionContext array) {index copyNumber localColumn row : Nat}
    (hCopy : copyNumber ≤ index) (hLocal : localColumn < context.blockLength) :
    entry? (expandRaw array.raw index) (context.copyPosition copyNumber localColumn) row =
      entry? (copyBlock array.raw context.badPart context.maximalRow
        context.parentColumn copyNumber
        (array.raw[context.lastIndex]?.getD [])) localColumn row := by
  simp only [entry?, context.getElem?_expandRaw_copy hCopy hLocal]

/-- A column `x` of `A[n]` with `p ≤ x` is the `j`-th column of a copy `q ≤ n`. -/
theorem exists_copyPosition_of_lt_length_expandRaw {array : ValidArray}
    (context : ExpansionContext array) {index column : Nat}
    (hColumn : column < (expandRaw array.raw index).length)
    (hNotGood : context.parentColumn ≤ column) :
    ∃ copyNumber localColumn,
      copyNumber ≤ index ∧ localColumn < context.blockLength ∧
        column = context.copyPosition copyNumber localColumn := by
  rw [context.length_expandRaw] at hColumn
  have hPos := context.blockLength_pos
  have hOffset : column - context.parentColumn < (index + 1) * context.blockLength := by
    omega
  refine ⟨(column - context.parentColumn) / context.blockLength,
    (column - context.parentColumn) % context.blockLength, ?_, Nat.mod_lt _ hPos, ?_⟩
  · have := (Nat.div_lt_iff_lt_mul hPos).mpr hOffset
    omega
  · have hDiv := Nat.div_add_mod' (column - context.parentColumn) context.blockLength
    unfold copyPosition copyStart
    omega

theorem entry?_expandRaw_eq_of_lt_lastIndex {array : ValidArray}
    (context : ExpansionContext array) (index : Nat)
    {column row : Nat} (hColumn : column < context.lastIndex) :
    entry? (expandRaw array.raw index) column row = entry? array.raw column row := by
  unfold entry?
  rcases Nat.lt_or_ge column context.parentColumn with hGood | hGood
  · rw [context.getElem?_expandRaw_of_lt_parentColumn index hGood]
  · have hLocal : column - context.parentColumn < context.blockLength := by
      simp only [blockLength]
      omega
    have hPosition : column = context.copyPosition 0 (column - context.parentColumn) := by
      rw [copyPosition_zero]
      omega
    rw [hPosition, context.getElem?_expandRaw_copy (Nat.zero_le _) hLocal, copyBlock_zero,
      context.getElem?_badPart hLocal, copyPosition_zero]

theorem parent_expandRaw_eq_of_lt_lastIndex {array : ValidArray}
    (context : ExpansionContext array) (index row : Nat)
    {target : Nat} (hTarget : target < context.lastIndex) :
    parent row (expandRaw array.raw index) target = parent row array.raw target := by
  have hLength := context.array_length
  have hLt := context.parentColumn_lt_lastIndex
  have hPos := context.blockLength_pos
  have hExpandLength := context.length_expandRaw index
  have hMul : context.blockLength ≤ (index + 1) * context.blockLength := by
    rw [Nat.succ_mul]
    omega
  have hBlock : context.blockLength = context.lastIndex - context.parentColumn := rfl
  apply parent_eq_of_entry?_eq_below (by omega) (by omega)
  intro column hColumn row
  exact context.entry?_expandRaw_eq_of_lt_lastIndex index (by omega)

/-! ## The length of `A[n]` -/

theorem length_expand {array : ValidArray} (context : ExpansionContext array)
    (index : Nat) :
    (array.expand index).raw.length =
    context.parentColumn + (index + 1) * context.blockLength := by
  change (trimZeroRows (expandRaw array.raw index)).length = _
  rw [length_trimZeroRows, context.length_expandRaw]

theorem length_expand_mono {array : ValidArray}
    (context : ExpansionContext array) {smallerIndex largerIndex : Nat}
    (hIndices : smallerIndex ≤ largerIndex) :
    (array.expand smallerIndex).raw.length ≤
      (array.expand largerIndex).raw.length := by
  rw [length_expand context, length_expand context]
  have := Nat.mul_le_mul_right context.blockLength (Nat.add_le_add_right hIndices 1)
  omega

theorem copyPosition_lt_length {array : ValidArray} (context : ExpansionContext array)
    {index copyNumber localColumn : Nat}
    (hCopy : copyNumber ≤ index) (hLocal : localColumn < context.blockLength) :
    context.copyPosition copyNumber localColumn <
      (array.expand index).raw.length := by
  rw [length_expand context]
  have hLe := Nat.mul_le_mul_right context.blockLength (Nat.add_le_add_right hCopy 1)
  have hSucc : (copyNumber + 1) * context.blockLength =
      copyNumber * context.blockLength + context.blockLength := Nat.succ_mul _ _
  unfold copyPosition copyStart
  omega

theorem exists_copyPosition_of_not_good {array : ValidArray}
    (context : ExpansionContext array) {index column : Nat}
    (hColumn : column < (array.expand index).raw.length)
    (hNotGood : context.parentColumn ≤ column) :
    ∃ copyNumber localColumn,
      copyNumber ≤ index ∧ localColumn < context.blockLength ∧
        column = context.copyPosition copyNumber localColumn := by
  apply context.exists_copyPosition_of_lt_length_expandRaw _ hNotGood
  rw [length_expand context] at hColumn
  rw [context.length_expandRaw]
  exact hColumn

theorem entry?_expandRaw_indices_eq_of_lt_length {array : ValidArray}
    (context : ExpansionContext array)
    {smallerIndex largerIndex column row : Nat}
    (hIndices : smallerIndex ≤ largerIndex)
    (hColumn : column < (array.expand smallerIndex).raw.length) :
    entry? (expandRaw array.raw smallerIndex) column row =
      entry? (expandRaw array.raw largerIndex) column row := by
  unfold entry?
  rcases Nat.lt_or_ge column context.parentColumn with hGood | hGood
  · rw [context.getElem?_expandRaw_of_lt_parentColumn smallerIndex hGood,
      context.getElem?_expandRaw_of_lt_parentColumn largerIndex hGood]
  · obtain ⟨copyNumber, localColumn, hCopy, hLocal, rfl⟩ :=
      context.exists_copyPosition_of_not_good hColumn hGood
    rw [context.getElem?_expandRaw_copy hCopy hLocal,
      context.getElem?_expandRaw_copy (Nat.le_trans hCopy hIndices) hLocal]

end ExpansionContext

end Por.BMS
