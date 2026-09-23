/-!
# The official 1-Y expansion, transcribed from `script.js`

This file is the Lean transcription of the Y sequence expansion as the
official implementation computes it: `calcMountain`, `calcDiagonal`,
`getBadRoot` and `expand` in
[`script.js`](https://github.com/Naruyoko/YNySequence/blob/2de13970b9ac818c935577b8284c41dec01f0039/script.js)
of [Naruyoko/YNySequence](https://github.com/Naruyoko/YNySequence) at revision
`2de1397`, which the
[wiki article](https://googology.fandom.com/ja/wiki/Y%E6%95%B0%E5%88%97) names
as the definition.  It copies the sparse-array representation, the index
arithmetic and the positions of the `break`s as they are, and gives the values
no meaning of their own.

The transcription is koteitan's, from `Equiv/Yukito.lean` of
[koteitan/1y-expand-equiv](https://github.com/koteitan/1y-expand-equiv/blob/c9a5368a09ceb62ec671a6c3447a4719d035dfc0/Equiv/Yukito.lean)
at revision `c9a5368`.  The code is unchanged; the comments are translated,
and the one import of that file, which this file does not use, is dropped.

A cell of the JS is `{value, position, parentIndex}`.  The `position` of a
cell in row `r` is its original column minus `r`, so

```
column c = position + r
```
-/

namespace Googology.Notation.Y

/-- A cell of the JS.  `par` is an array index in the same row (the JS
`parentIndex`; `-1` is `none`).  `forced` is the JS `forcedParent`: it is set
when the input had the form `"value v parent"`, and it skips the parent
search.  In a row built from plain numbers it is always `false`. -/
structure Cell where
  pos : Nat
  val : Nat
  par : Option Nat
  forced : Bool := false
  deriving Repr, DecidableEq

/-- A row is the JS `lastLayer`, a sparse array in increasing `position`. -/
abbrev Rowj := Array Cell

/-- JS: the first index reached by `while (lastLayer[j].position < target) j++`.
If the scan runs off the array it returns `row.size`, the place where the JS
`lastLayer[j]` is `undefined`. -/
def scanFrom (row : Rowj) (target : Nat) (j : Nat) : Nat :=
  if h : j < row.size then
    if row[j].pos < target then scanFrom row target (j+1) else j
  else j
termination_by row.size - j
decreasing_by simp_wf; omega

/-- The same scan started at `j = 0`: the JS `var j=0; while (…) j++`. -/
def firstAtLeast (row : Rowj) (target : Nat) : Nat := scanFrom row target 0

/-- The condition of the JS
`if (j<0 || j<lastLayer.length-1 && lastLayer[j].position+1!=lastLayer[j+1].position) break;`.
`j` is a natural number, so `j<0` is read as "ran off the array". -/
def breakHere (row : Rowj) (j : Nat) : Bool :=
  if h : j < row.size then
    if h2 : j + 1 < row.size then row[j].pos + 1 ≠ row[j+1].pos else false
  else true

/-- The body of the JS parent search for a row `r ≥ 1`.  `prev` is the row
below, and `p` walks its indices.  `fuel` equal to `prev.size` is enough. -/
def searchUpper (prev row : Rowj) (i : Nat) : Nat → Option Nat → Option Nat
  | 0, _ => none
  | _+1, none => none
  | fuel+1, some p =>
    if hp : p < prev.size then
      match prev[p].par with
      | none => none                            -- JS: `if (p<0) break;`
      | some p' =>
        if hp' : p' < prev.size then
          let target := prev[p'].pos - 1
          let j := firstAtLeast row target
          if breakHere row j then none
          else if hj : j < row.size then
            if hi : i < row.size then
              if row[j].val < row[i].val then some j
              else searchUpper prev row i fuel (some p')
            else none
          else none
        else none
    else none

/-- The JS parent search in row `0`: `p--; j=p-1;`, running left through
`j = c-1, c-2, …`. -/
def searchBase (row : Rowj) (i : Nat) : Nat → Option Nat
  | 0 => none
  | j+1 => if hj : j < row.size then
             if hi : i < row.size then
               if row[j].val < row[i].val then some j else searchBase row i j
             else none
           else none

/-- The next row of differences (the JS `currentLayer`).  Only the cells
with a parent appear in it, and their `position` goes down by one. -/
def nextRow (row : Rowj) : Rowj :=
  row.foldl (init := #[]) fun acc c =>
    match c.par with
    | none => acc
    | some p =>
      if hp : p < row.size then
        acc.push { pos := c.pos - 1, val := c.val - row[p].val, par := none }
      else acc

/-- Assign parents to a row.  `prev = none` is the JS
`calculatedMountain.length == 1`.  A cell with `forced` set is skipped by the
JS `continue`, so it is returned as it is. -/
def assignParents (prev : Option Rowj) (row : Rowj) : Rowj :=
  row.mapIdx fun i c =>
    if c.forced then c
    else
      match prev with
      | none     => { c with par := searchBase row i c.pos }
      | some pv  => { c with par := searchUpper pv row i (pv.size + 1)
                               (some (firstAtLeast pv (c.pos + 1))) }

/-- Row `0`, from the input sequence. -/
def row0 (s : List Nat) : Rowj :=
  (s.toArray.mapIdx fun i v => { pos := i, val := v, par := none })

/-- The loop of the JS `calcMountain`.  `fuel` bounds the number of rows (the
JS stops at `hasNextLayer`). -/
def mountainGo (cur : Rowj) : Nat → List Rowj
  | 0 => [cur]
  | f+1 =>
    if cur.all (fun c => c.par.isNone) then [cur]
    else cur :: mountainGo (assignParents (some cur) (nextRow cur)) f

/-- The JS `calcMountain`.  The JS accepts a string or an array, so this
starts from the row itself. -/
def calcMountainFrom (base : Rowj) : Nat → List Rowj
  | 0 => []
  | fuel+1 => mountainGo (assignParents none base) fuel

/-- The mountain of a plain sequence. -/
def calcMountain (s : List Nat) (fuel : Nat) : List Rowj :=
  calcMountainFrom (row0 s) fuel

/-! ## `calcDiagonal`

The second half of the JS.  For each column it walks the leg down from the
top and records the column it lands on in `diagonalTree`.

Exact-match scans such as `while (mountain[height-1][l].position != … + 1) l++`
are written with `firstAtLeast`.  The column searched for is always there (the
cell one row down in the same column is alive), so the behaviour is the same.
Where it is not, the JS reads past the array and fails; here that returns
`none`.
-/

/-- Row `h` of a mountain.  The JS only reads rows in range, so an empty row
outside the range makes no difference. -/
def rowAt (M : List Rowj) (h : Nat) : Rowj := M.getD h #[]

/-- The top row containing column `i`, with the index there.  The JS runs
`j` from the top down. -/
def topAt (M : List Rowj) (i : Nat) : Nat → Option (Nat × Nat)
  | 0 => none
  | j+1 =>
    let row := rowAt M j
    let k := firstAtLeast row (i - j)
    if hk : k < row.size then
      if (row[k]'hk).pos + j = i then some (j, k) else topAt M i j
    else topAt M i j

/-- The cell at position `t`, if there is one: the JS
`while (row[m].position < t) m++; if (row[m].position == t) …`. -/
def lookupPos (row : Rowj) (t : Nat) : Option Nat :=
  let m := firstAtLeast row t
  if hm : m < row.size then (if (row[m]'hm).pos = t then some m else none) else none

/-- One step of the JS leg walk (sparse version).  The state is
`(row, index in that row)`. -/
def legStepJS (M : List Rowj) (h idx : Nat) : Option (Nat × Nat) :=
  let row := rowAt M h
  if hi : idx < row.size then
    match h with
    | 0 =>
      match (row[idx]'hi).par with
      | none => none
      | some p => some (0, p)
    | h'+1 =>
      let below := rowAt M h'
      match lookupPos below ((row[idx]'hi).pos + 1) with
      | none => none
      | some l0 =>
        if hl0 : l0 < below.size then
          match (below[l0]'hl0).par with
          | none => none
          | some l =>
            if hl : l < below.size then
              -- The JS target is `position - 1`.  At `position = 0` that is `-1`,
              -- which matches no cell, so the walk always goes down a row.  Truncated
              -- subtraction would give `0`, so this case is split off.
              if (below[l]'hl).pos = 0 then some (h', l)
              else
                match lookupPos row ((below[l]'hl).pos - 1) with
                | some m => some (h' + 1, m)
                | none => some (h', l)
            else none
        else none
  else none

/-- The JS leg walk (sparse version).  Returns the column it lands on;
`none` is the JS `-1`. -/
def legWalkJS (M : List Rowj) : Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | fuel+1, h, idx =>
    match legStepJS M h idx with
    | none => none
    | some (h', idx') =>
      let row := rowAt M h'
      if hi : idx' < row.size then
        match (row[idx']'hi).par with
        | none => some ((row[idx']'hi).pos + h')
        | some _ => legWalkJS M fuel h' idx'
      else none

/-- One entry of the diagonal, for column `i`: the value and the result of
the walk. -/
def diagEntry (M : List Rowj) (i : Nat) : Option (Nat × Option Nat) :=
  match topAt M i M.length with
  | none => none
  | some (j, k) =>
    let row := rowAt M j
    if hk : k < row.size then
      some ((row[k]'hk).val, legWalkJS M (i + 1) j k)
    else none

/-- The values and walk results in order: the JS `diagonal` and
`diagonalTree`. -/
def diagList (M : List Rowj) : List (Nat × Option Nat) :=
  (List.range (rowAt M 0).size).filterMap (diagEntry M)

/-- The JS `pw`: run left to the first index with a smaller value. -/
def pwScan (d : List Nat) (target : Nat) : Nat → Option Nat
  | 0 => none
  | j+1 => if d.getD j 0 < target then some j else pwScan d target j

/-- The later JS loop: follow `diagonalTree` and stop at the first smaller
value. -/
def treeScan (d : List Nat) (tree : List (Option Nat)) (target : Nat) :
    Nat → Nat → Option Nat
  | 0, _ => none
  | fuel+1, p =>
    match tree.getD p none with
    | none => none
    | some q => if d.getD q 0 < target then some q else treeScan d tree target fuel q

/-- One element of the output.  `forced` is the JS `"v"` suffix. -/
structure DiagItem where
  val : Nat
  forced : Bool
  par : Option Nat
  deriving Repr, DecidableEq

/-- The output of the JS `calcDiagonal`, before it is turned into a string. -/
def calcDiagonal (M : List Rowj) : List DiagItem :=
  let e := diagList M
  let d := e.map Prod.fst
  let tree := e.map Prod.snd
  (List.range d.length).map fun i =>
    let target := d.getD i 0
    let p := treeScan d tree target (i + 1) i
    let w := pwScan d target i
    if p = w then { val := target, forced := false, par := none }
    else { val := target, forced := true, par := p }

/-- The JS `Math.max(Math.min(i-1,p),-1)`.  `p` is an ancestor of `i`, so in
fact it has no effect. -/
def clampPar (i : Nat) (p : Option Nat) : Option Nat :=
  match i, p with
  | 0, _ => none
  | _+1, none => none
  | i'+1, some q => some (min i' q)

/-- The JS `parseSequenceElement`.  An element with `"v"` sets `forced` and
fixes the parent. -/
def parseDiag (l : List DiagItem) : Rowj :=
  l.toArray.mapIdx fun i x =>
    { pos := i, val := x.val,
      par := if x.forced then clampPar i x.par else none, forced := x.forced }

/-! ## `getBadRoot`

The JS repeats the extraction until the last value of the diagonal is `1`,
then finds the top row containing the last column, and returns the column of
the parent of the last cell one row below. -/

/-- The column of the last cell of a row. -/
def lastCol (row : Rowj) (r : Nat) : Nat :=
  if h : 0 < row.size then (row[row.size - 1]'(by omega)).pos + r else 0

/-- The value of the last cell of a row. -/
def lastVal (row : Rowj) : Nat :=
  if h : 0 < row.size then (row[row.size - 1]'(by omega)).val else 0

/-- The top row containing column `n-1`: the JS
`for (i=mountain.length-1;i>=0;i--)`. -/
def topRowOfLast (M : List Rowj) (n : Nat) : Nat → Option Nat
  | 0 => none
  | i+1 => if lastCol (rowAt M i) i = n - 1 then some i else topRowOfLast M n i

/-- The JS `getBadRoot`.  `mfuel` is the fuel for building mountains and
`fuel` bounds the number of extractions. -/
def getBadRoot (M : List Rowj) (mfuel : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    let d := calcMountainFrom (parseDiag (calcDiagonal M)) mfuel
    if lastVal (rowAt d 0) = 1 then
      match topRowOfLast M (rowAt M 0).size M.length with
      | none => none
      | some i =>
        let prev := rowAt M (i - 1)
        if hp : 0 < prev.size then
          match (prev[prev.size - 1]'(by omega)).par with
          | none => none
          | some p =>
            if hq : p < prev.size then some ((prev[p]'hq).pos + (i - 1)) else none
        else none
    else getBadRoot d mfuel fuel

/-! ## The scans of the Mt. Fuji shell

The three scans the body of `expand` uses.

```js
// is column j in row r
var l=0; while (mountain[r][l] && mountain[r][l].position+r<j) l++;
mountain[r][l] && mountain[r][l].position+r==j

// seamHeight: one above the top row containing column j
var seamHeight=afterCutHeight-1;
while (true){ …break if column j is there…; seamHeight--; }
seamHeight++;

// isAscending: does the parent chain of column j in row badRootHeight reach column badRootSeam
```
-/

/-- Whether row `r` has column `j`. -/
def hasCol (M : List Rowj) (r j : Nat) : Bool :=
  match lookupPos (rowAt M r) (j - r) with
  | none => false
  | some m =>
    if h : m < (rowAt M r).size then ((rowAt M r)[m]'h).pos + r == j else false

/-- The JS `seamHeight`: one above the top row (below `hi`) containing
column `j`. -/
def seamHeightOf (M : List Rowj) (j : Nat) : Nat → Nat
  | 0 => 0
  | h + 1 => if hasCol M h j then h + 1 else seamHeightOf M j h

/-- The inner loop of the JS `isAscending`: follow the parent chain in row
`bh` and see whether it reaches column `seam`. -/
def ascendTo (M : List Rowj) (bh seam : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, p =>
    let row := rowAt M bh
    if hp : p < row.size then
      let col := (row[p]'hp).pos + bh
      if col < seam then false
      else if col = seam then true
      else
        match (row[p]'hp).par with
        | none => false
        | some q => ascendTo M bh seam fuel q
    else false

/-- The JS `isAscending`. -/
def isAscending (M : List Rowj) (bh seam j fuel : Nat) : Bool :=
  match lookupPos (rowAt M bh) (j - bh) with
  | none => false
  | some m =>
    if h : m < (rowAt M bh).size then
      if ((rowAt M bh)[m]'h).pos + bh = j then ascendTo M bh seam fuel m else false
    else false

/-! ## One cell of the Mt. Fuji shell

The three branches (Bb / Br / Be) differ only in how they choose `sy` (the
source row) and `sx` (the index of the source column); the cell they stack
has the same form.

```js
var sourceParentIndex=mountain[sy][sx].parentIndex;
var parentShifts=i-isReplacingCut;
var parentPosition=mountain[sy][sourceParentIndex]
  ? mountain[sy][sourceParentIndex].position
      + parentShifts*(afterCutLength-badRootSeam)*(parentColumn>=badRootSeam) - (k-sy)
  : -1;
var parentIndex=0;
while (result[k][parentIndex]&&result[k][parentIndex].position<parentPosition) parentIndex++;
if (!result[k][parentIndex]||result[k][parentIndex].position!=parentPosition) parentIndex=-1;
result[k].push({ value: …, position: j+(afterCutLength-badRootSeam)*i-k,
                 parentIndex: parentIndex, forcedParent: mountain[sy][sx].forcedParent });
```
-/

/-- The constants of an expansion. -/
structure FujiParams where
  /-- The column of the bad root. -/
  badRootSeam : Nat
  /-- The row of the bad root. -/
  badRootHeight : Nat
  /-- The row where the cut is made. -/
  cutHeight : Nat
  /-- The number of columns after the cut. -/
  afterCutLength : Nat
  /-- The branch the Yamakazi–Funka duality selects. -/
  yamakazi : Bool

/-- The length of one copy. -/
def FujiParams.len (P : FujiParams) : Nat := P.afterCutLength - P.badRootSeam

/-- The index of the source cell; with `useLast`, the last cell of the row. -/
def sourceIdx (M : List Rowj) (sy j : Nat) (useLast : Bool) : Nat :=
  if useLast then (rowAt M sy).size - 1 else firstAtLeast (rowAt M sy) (j - sy)

/-- The `position` of the parent.  `none` where the JS value is negative
(it matches no cell). -/
def parentPos (M : List Rowj) (P : FujiParams) (sy sx k shifts : Nat) : Option Nat :=
  let row := rowAt M sy
  if hx : sx < row.size then
    match (row[sx]'hx).par with
    | none => none
    | some sp =>
      if hp : sp < row.size then
        let ppos := (row[sp]'hp).pos
        let shift := if P.badRootSeam ≤ ppos + sy then shifts * P.len else 0
        if k - sy ≤ ppos + shift then some (ppos + shift - (k - sy)) else none
      else none
  else none

/-- One cell to stack.  Its `value` is fixed only when it has no parent;
otherwise it is filled in later.  The JS uses `NaN` for the latter; here the
value `0` marks "not yet fixed", which cannot clash, since real values are
positive. -/
def fujiCell (M : List Rowj) (P : FujiParams) (cur : Rowj) (sy sx k i j shifts : Nat)
    (topVal : Nat) : Cell :=
  let pp := parentPos M P sy sx k shifts
  let pi := match pp with
    | none => none
    | some q => lookupPos cur q
  let fp := if hx : sx < (rowAt M sy).size then ((rowAt M sy)[sx]'hx).forced else false
  { pos := j + P.len * i - k, val := if pi.isNone then topVal else 0,
    par := pi, forced := fp }

/-! ## The triple loop of the Mt. Fuji shell

```js
for (var i=1;i<=n;i++)            // repetitions
  for (var j=badRootSeam;j<afterCutLength;j++)   // seam columns
    …compute isAscending and seamHeight…
    for (var k=0;k<kmax;k++)      // rows
      …choose sy and sx by branch, stack the cell…
```
-/

/-- The value at an index. -/
def valAtIdx (row : Rowj) (i : Nat) : Nat := if h : i < row.size then (row[i]'h).val else 0

/-- The value in row `0` at column `c`. -/
def readValAt (row : Rowj) (c : Nat) : Nat :=
  match lookupPos row c with
  | none => 0
  | some m => if h : m < row.size then (row[m]'h).val else 0

/-- Stack a cell onto row `k` of `res`, creating the row if it is missing
(the JS `if (!result[k]) result.push([]);`). -/
def pushAt (res : List Rowj) (k : Nat) (c : Cell) : List Rowj :=
  if k < res.length then res.set k ((res.getD k #[]).push c) else res ++ [#[c]]

/-- The choice of branch: the JS Bb / Br replace / Br extend / Be.  Returns
(the source row, whether the source cell is the last of its row). -/
def fujiSource (P : FujiParams) (i k : Nat) (isRep : Bool) : Nat × Bool :=
  let d := P.cutHeight - P.badRootHeight
  let ir := if isRep then 1 else 0
  if k < P.badRootHeight then (k, isRep)
  else if k ≤ P.badRootHeight + d * (i - ir) then
    (P.badRootHeight, !P.yamakazi && isRep)
  else if isRep && k ≤ P.badRootHeight + d * i then
    (k - d * (i - 1), !P.yamakazi && isRep)
  else (k - d * i, !P.yamakazi && isRep)

/-- The choice of branch for a column that is not ascending.  The `else` side
of `isAscending` in `script.js` has only the Bb branch (`sy = k`); only the
ascending columns split four ways. -/
def fujiSourceAt (P : FujiParams) (i k : Nat) (isRep isAsc : Bool) : Nat × Bool :=
  if isAsc then fujiSource P i k isRep else (k, isRep)

/-- Stack rows `k = 0 … kmax−1`. -/
def fujiRows (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (i j : Nat)
    (isRep isAsc : Bool) :
    Nat → List Rowj → List Rowj
  | 0, res => res
  | kmax + 1, res =>
      let res := fujiRows M P nd i j isRep isAsc kmax res
      let sysx := fujiSourceAt P i kmax isRep isAsc
      let sx := sourceIdx M sysx.1 j sysx.2
      let ir := if isRep then 1 else 0
      let topVal := nd (j + P.len * i)
      pushAt res kmax (fujiCell M P (rowAt res kmax) sysx.1 sx kmax i j (i - ir) topVal)

/-- Run over the seam columns `j = badRootSeam … badRootSeam+t−1`. -/
def fujiSeams (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (i afterCutHeight ascFuel : Nat) :
    Nat → List Rowj → List Rowj
  | 0, res => res
  | t + 1, res =>
      let res := fujiSeams M P nd i afterCutHeight ascFuel t res
      let j := P.badRootSeam + t
      let isRep := decide (j = P.badRootSeam)
      let isAsc := isAscending M P.badRootHeight P.badRootSeam j ascFuel
      let seamH := seamHeightOf M j afterCutHeight
      let d := P.cutHeight - P.badRootHeight
      let kmax := if isAsc then seamH + d * i else seamH
      fujiRows M P nd i j isRep isAsc kmax res

/-- The repetitions `i = 1 … n`. -/
def fujiIters (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (afterCutHeight ascFuel : Nat) :
    Nat → List Rowj → List Rowj
  | 0, res => res
  | i + 1, res =>
      let res := fujiIters M P nd afterCutHeight ascFuel i res
      fujiSeams M P nd (i + 1) afterCutHeight ascFuel P.len res

/-! ## Cutting and filling in the values

```js
for (var i=0;i<=actualCutHeight;i++) result[i].pop();   // cut the child
if (!result[result.length-1].length) result.pop();

for (var i=result.length-1;i>=0;i--){                   // fill values from the top down
  if (!result[i].length){ result.pop(); continue; }
  for (var j=0;j<result[i].length;j++){
    if (!isNaN(result[i][j].value)) continue;
    …result[i][j].value = parent value + value in the same column one row up…
  }
}
```
-/

/-- The JS "cut the child": drop the last cell of rows `0 … cutH`, and drop
the top row if it becomes empty. -/
def cutChild (res : List Rowj) (cutH : Nat) : List Rowj :=
  let res := (List.range (cutH + 1)).foldl
    (fun r i => if i < r.length then r.set i ((r.getD i #[]).pop) else r) res
  if 0 < res.length ∧ (res.getD (res.length - 1) #[]).size = 0 then
    res.take (res.length - 1)
  else res

/-- Fill the values of one row.  `up` is the row above, already filled.  The
value `0` marks "not yet fixed". -/
def fillRow (row up : Rowj) : Rowj :=
  row.foldl (init := #[]) fun acc c =>
    acc.push (if c.val ≠ 0 then c
      else { c with val := (match c.par with
                            | none => 0
                            | some p => valAtIdx acc p) + readValAt up (c.pos - 1) })

/-- Fill the values from the top down. -/
def fillValues : List Rowj → List Rowj
  | [] => []
  | [r] => [r]
  | r :: rest =>
      let rest := fillValues rest
      fillRow r (rest.headD #[]) :: rest

/-- Drop empty rows at the top. -/
def dropEmptyTop : List Rowj → List Rowj
  | [] => []
  | a :: t =>
      if ((a :: t).getD (t.length) #[]).size = 0 then
        dropEmptyTop ((a :: t).take t.length)
      else a :: t
  termination_by l => l.length
  decreasing_by
    simp only [List.length_take, List.length_cons]
    omega

/-! ## The entry point `expand`

The JS computes `badRootSeamHeight` and `afterCutMountain` and never uses them
afterwards, so they are not transcribed.

Only `.value` of `newDiagonal` is ever read, so it is kept as a function
`Nat → Nat` of values.  The JS pushes references to the same cell with
`newDiagonal[0].push(newDiagonal[0][j])`, which duplicates `position`s, but
that does not affect the values. -/

/-- The top row containing column `j`: the JS scan for `badRootHeight`. -/
def topRowWithCol (M : List Rowj) (j : Nat) : Nat → Option Nat
  | 0 => none
  | i + 1 => if hasCol M i j then some i else topRowWithCol M j i

/-- The values of `newDiagonal` on the Yamakazi branch.  `base` is row `0` of
the diagonal with its last cell dropped; after it the interval `[seam, len)`
repeats periodically. -/
def yamaVal (base : Rowj) (seam len : Nat) (c : Nat) : Nat :=
  if c < len then valAtIdx base c
  else valAtIdx base (seam + (c - len) % (len - seam))

/-- The values of row `0`: the JS output, as `stringify` lists it. -/
def expandOut (M : List Rowj) : List Nat := (rowAt M 0).toList.map (·.val)

/-- The JS `expand`.  `nrep` is the number of repetitions `n`, `mfuel` the
fuel for building mountains, and `efuel` bounds the recursion through the
extraction. -/
def expandJS (nrep mfuel : Nat) : Nat → List Rowj → List Rowj
  | 0, _ => []
  | efuel + 1, M =>
    let row0 := rowAt M 0
    let n := row0.size
    let hasPar := if h : n - 1 < row0.size then ((row0[n - 1]'h).par).isSome else false
    if !hasPar then
      fillValues (dropEmptyTop (M.set 0 row0.pop))
    else
      let cutH := (topRowOfLast M n M.length).getD 0
      let seam := (getBadRoot M mfuel mfuel).getD 0
      let dg := calcMountainFrom (parseDiag (calcDiagonal M)) mfuel
      let yama := lastVal (rowAt dg 0) = 1
      let nd : Nat → Nat :=
        if yama then yamaVal (rowAt dg 0).pop seam (n - 1)
        else valAtIdx (rowAt (expandJS nrep mfuel efuel dg) 0)
      let cutH' := if yama then cutH - 1 else cutH
      let bh := if yama then cutH - 1 else (topRowWithCol M seam M.length).getD 0
      let res := cutChild M cutH
      let acl := (rowAt res 0).size
      let P : FujiParams := ⟨seam, bh, cutH', acl, yama⟩
      fillValues (dropEmptyTop (fujiIters M P nd res.length mfuel nrep res))

end Googology.Notation.Y
