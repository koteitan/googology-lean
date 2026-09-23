/-
Por.BMS.Defs: the computable definitions of the BMS layer (Bashicu Matrix System, BM4).

Written independently from the BM4 rule. The names and argument orders of the definitions
that the imported 0-Y / 1-Y core (Phyrion1343/1Y-Well-Ordering-Lean,
`formalization/{ZeroY,OneY}`, Apache-2.0) calls are kept; the bodies are our own
formulations, and the core reaches them through the lemmas of `Por.BMS.Search`,
`Por.BMS.ParentAncestor`, `Por.BMS.Array` and `Por.BMS.Context`.
Lean core only; no Mathlib.

Conventions. An array is a list of columns; `A(i,k)` is the entry of column `i` in row `k`
(row 0 is the top row of BM4). `c = |A| - 1` is the last column.
Taken from koteitan, 1y-wo-por, `Por/BMS/Defs.lean` (https://github.com/koteitan/1y-wo-por,
revision db86f2d13c2e18a8e2c2fae5e083d00fc4d48a78, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`.
-/

namespace Por.BMS

/-- A BMS array: a list of columns, each column a list of natural numbers. -/
abbrev BMSArray : Type := List (List Nat)

/-- The entry `A(column,row)`, or `none` if the column or the row is missing. -/
def entry? (array : BMSArray) (column row : Nat) : Option Nat :=
  array[column]?.bind (fun c => c[row]?)

/-- `true` iff all columns have the same length (the empty array is rectangular). -/
def rectangular : BMSArray → Bool
  | [] => true
  | first :: rest => rest.all (fun column => column.length == first.length)

/-- Every column of `array` has length `height`. -/
def UniformHeight (height : Nat) (array : BMSArray) : Prop :=
  ∀ column ∈ array, column.length = height

/-- The support height of a column: 1 + the largest index of a nonzero entry,
or 0 if every entry is 0. -/
def supportHeight : List Nat → Nat
  | [] => 0
  | value :: rest =>
      if supportHeight rest = 0 ∧ value = 0 then 0 else supportHeight rest + 1

/-- The largest support height of a column (0 for the empty array). Every row with index
`≥ trimHeight A` contains only zeros. -/
def trimHeight (array : BMSArray) : Nat :=
  array.foldl (fun result column => max result (supportHeight column)) 0

/-- Delete the all-zero rows at the bottom: cut every column to `trimHeight array`
entries. The number of columns is unchanged. -/
def trimZeroRows (array : BMSArray) : BMSArray :=
  array.map (fun column => column.take (trimHeight array))

/-- The columns `start, start+1, ..., start+count-1` (as far as they exist). -/
def slice (array : BMSArray) (start count : Nat) : BMSArray :=
  (array.drop start).take count

/-- The largest `m < bound` with `predicate m = true`, or `none`: scan
`bound - 1, bound - 2, ..., 0` and return the first hit. -/
def greatestBelow? (bound : Nat) (predicate : Nat → Bool) : Option Nat :=
  (List.range bound).reverse.find? predicate

/-- `ancestorChain f current fuel`: the list `[f current, f (f current), ...]`
(the start is not included), stopping at the first `none` or after `fuel` steps. -/
def ancestorChain (parentFunction : Nat → Option Nat) : Nat → Nat → List Nat
  | _, 0 => []
  | current, fuel + 1 =>
      (parentFunction current).elim [] fun next => next :: ancestorChain parentFunction next fuel

/-- `A(candidate,row) < A(target,row)`, where both entries must exist. -/
def entryLt (array : BMSArray) (row candidate target : Nat) : Bool :=
  (entry? array candidate row).any fun left =>
    (entry? array target row).any fun right => decide (left < right)

/-- The rightmost column `j < target` with `eligible j = true`; `none` if there is none
or if `target` is not a column of `array`. -/
def searchLeft (array : BMSArray) (target : Nat) (eligible : Nat → Bool) : Option Nat :=
  if target < array.length then greatestBelow? target eligible else none

/-- The BM4 parent of column `target` on row `row`.
Row 0: the nearest column `j < target` with `A(j,0) < A(target,0)`.
Row `k+1`: the nearest column `j < target` that is a strict row-`k` ancestor of `target`
and has `A(j,k+1) < A(target,k+1)`. `none` if there is no such column or `target ≥ |A|`. -/
def parent : Nat → BMSArray → Nat → Option Nat
  | 0, array, target => searchLeft array target (entryLt array 0 · target)
  | row + 1, array, target =>
      searchLeft array target fun candidate =>
        (ancestorChain (parent row array) target target).contains candidate &&
          entryLt array (row + 1) candidate target

/-- `ancestor` is a strict row-`row` ancestor of `target`
(it lies on the row-`row` parent chain of `target`). -/
def isAncestor (array : BMSArray) (row ancestor target : Nat) : Bool :=
  (ancestorChain (parent row array) target target).contains ancestor

/-- The test "`candidate` may be the row-`row` parent of `target`" used by `parent`. -/
def parentEligible (row : Nat) (array : BMSArray) (target candidate : Nat) : Bool :=
  match row with
  | 0 => entryLt array 0 candidate target
  | row + 1 => isAncestor array row candidate target && entryLt array (row + 1) candidate target

/-- BM4's `m₀`: the largest row in which the last column has a parent. -/
def maximalParentRow (array : BMSArray) : Option Nat :=
  match array.length with
  | 0 => none
  | lastIndex + 1 =>
      greatestBelow? ((array[lastIndex]?.map List.length).getD 0)
        (fun row => (parent row array lastIndex).isSome)

/-- The entry in row `row` of the bad-part column `parentColumn + localColumn` ascends:
`row < m₀` and (`localColumn = 0` or the bad root is a row-`row` ancestor of it). -/
def ascending (array : BMSArray) (m₀ parentColumn localColumn row : Nat) : Bool :=
  decide (row < m₀) &&
    (localColumn == 0 || isAncestor array row parentColumn (parentColumn + localColumn))

/-- The increase per copy in row `row`: `A(c,row) - A(p,row)`, read from the first column of
the bad part and from the last column; `0` if one of the two entries is missing. -/
def rowGap (firstColumn lastColumn : List Nat) (row : Nat) : Nat :=
  ((firstColumn[row]?).bind fun first => (lastColumn[row]?).map (· - first)).getD 0

/-- Row `row` of column `localColumn` of copy `copyNumber` of the bad part `block`, where
`value` is the entry of `block` there: ascending entries grow by `copyNumber` gaps. -/
def copiedEntry (array block : BMSArray) (m₀ parentColumn copyNumber localColumn row value : Nat)
    (lastColumn : List Nat) : Nat :=
  value + (if ascending array m₀ parentColumn localColumn row = true then
    copyNumber * rowGap (block.head?.getD []) lastColumn row else 0)

/-- The `copyNumber`-th copy of the bad part `block`: every ascending entry gets
`copyNumber * (A(c,row) - A(p,row))` added, where `A(p,·)` is the first column of `block`
and `A(c,·)` is `lastColumn`. -/
def copyBlock (array block : BMSArray) (m₀ parentColumn copyNumber : Nat)
    (lastColumn : List Nat) : BMSArray :=
  block.mapIdx fun localColumn column =>
    column.mapIdx (copiedEntry array block m₀ parentColumn copyNumber localColumn · · lastColumn)

/-- The pair `(m₀, p)` of one BM4 expansion step: `m₀` is the largest row in which the last
column has a parent, `p` is that parent (the bad root). -/
def expansionPivot? (array : BMSArray) : Option (Nat × Nat) :=
  (maximalParentRow array).bind fun m₀ =>
    (parent m₀ array (array.length - 1)).map fun root => (m₀, root)

/-- The BM4 expansion `A[index]` before deleting all-zero rows. Without `m₀` the last
column is dropped. With `m₀` and bad root `p`, the result is the good part `A[0..p)`
followed by the copies `0, 1, ..., index` of the bad part `A[p..c)`. -/
def expandRaw (array : BMSArray) (index : Nat) : BMSArray :=
  match expansionPivot? array with
  | none => array.take (array.length - 1)
  | some (m₀, root) =>
      array.take root ++ (List.range (index + 1)).flatMap fun copyNumber =>
        copyBlock array (slice array root (array.length - 1 - root)) m₀ root copyNumber
          (array[array.length - 1]?.getD [])

/-- The BM4 expansion `A[index]`. -/
def expand (array : BMSArray) (index : Nat) : BMSArray :=
  trimZeroRows (expandRaw array index)

end Por.BMS
