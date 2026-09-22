import Googology

/-!
# The one-row reading, against known values

`Googology.Trans.BMS.read` sends a one-row Bashicu matrix to an extended
Buchholz term.  Agreement with the values the primitive sequence system is
known to take is a finite check, not a proof, so it lives here and not in the
library.
-/

namespace Googology.Trans.BMS

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term

/-! `(0)` is `1`, `(0,1)` is `ω`, `(0,1,2)` is `ω^ω`, and `(0,0)` is `2`. -/

#guard read 0 [0] == t1
#guard read 0 [0, 1] == tw
#guard read 0 [0, 1, 2] == psi nil tw
#guard read 0 [0, 0] == cons nil nil t1
#guard read 0 [0, 1, 1] == psi nil (cons nil nil t1)
#guard read 0 [0, 1, 0, 1] == cons nil t1 tw

/-! The readings are standard forms below `Ω`. -/

#guard ([[0], [0,0], [0,1], [0,1,1], [0,1,2], [0,1,0,1], [0,1,2,1],
         [0,1,2,2], [0,1,2,3]] : List (List Nat)).all fun s =>
  isOT (read 0 s) && decide (read 0 s < tW)

/-! And a non-standard one is not: `(0,1,0,1,2)` reads as `ω + ω^ω`, whose
principal terms increase. -/

#guard !(isOT (read 0 [0, 1, 0, 1, 2]))

/-! Writing a term back and reading it again gives the term, which is
`read_unread`. -/

#guard ([t1, tw, psi nil tw, cons nil nil t1, cons nil t1 tw] : List Term).all
  fun X => read 0 (unread 0 X) == X

/-! And reading a matrix and writing it back gives the matrix, which is
`unread_read`.  Each list below is a `Col 0`: it starts at `0`, stays at or
above it, and never rises by more than one. -/

#guard ([[], [0], [0, 1], [0, 1, 2], [0, 0], [0, 1, 1], [0, 1, 2, 1],
  [0, 1, 0, 1]] : List (List Nat)).all fun s => unread 0 (read 0 s) == s

/-! A list that rises by two is not a matrix, and is not written back as
itself. -/

#guard !(unread 0 (read 0 [0, 2]) == [0, 2])

/-! ### Expansion

The four steps of `(0)(1)(2)(3)[1][1][1][1]` in the reference implementation,
as `expandL` computes them. -/

#guard expandL 1 0 [0, 1, 2, 3] == [0, 1, 2, 2]
#guard expandL 1 0 [0, 1, 2, 2] == [0, 1, 2, 1, 2]
#guard expandL 1 0 [0, 1, 2, 1, 2] == [0, 1, 2, 1, 1]
#guard expandL 1 0 [0, 1, 2, 1, 1] == [0, 1, 2, 1, 0, 1, 2, 1]

/-! A matrix that ends at level `0` loses its last column. -/

#guard expandL 3 0 [0, 1, 0] == [0, 1]
#guard expandL 3 0 [0] == []

/-! And the count: `[n]` writes `n + 1` copies. -/

#guard expandL 0 0 [0, 1] == [0]
#guard expandL 2 0 [0, 1] == [0, 0, 0]

/-! The commutation of `read_expandL`, computed. -/

#guard ([[0], [0, 1], [0, 0], [0, 1, 2], [0, 1, 1], [0, 1, 0, 1],
  [0, 1, 2, 3], [0, 1, 2, 1, 1]] : List (List Nat)).all fun s =>
    (List.range 3).all fun n =>
      read 0 (expandL n 0 s) == fs (read 0 s) (idx (read 0 s) (n + 1))

/-! ### States of the primitive sequence system

The generators `(0)(1)⋯(n)` are states: their terms are standard forms. -/

#guard (List.range 6).all fun n => isOT (read 0 (List.range (n + 1)))

/-! And expansion keeps them so. -/

#guard (List.range 4).all fun n =>
  (List.range 3).all fun k => isOT (read 0 (expandL k 0 (List.range (n + 1))))

/-- Every term of size at most `n`, for the calibration below. -/
def bySizeProbe : Nat → Array (List Term)
  | 0 => #[[nil]]
  | n + 1 =>
      let prev := bySizeProbe n
      let here := (List.range (n + 1)).flatMap fun i =>
        (List.range (n + 1 - i)).flatMap fun j =>
          let k := n - i - j
          (prev[i]!).flatMap fun a =>
            (prev[j]!).flatMap fun b =>
              (prev[k]!).map fun t => cons a b t
      prev.push here

def upToProbe (n : Nat) : List Term := ((bySizeProbe n).toList).flatten

/-! ### What the reading reaches

Below `ψ_0(Ω)` is exactly where the subscripts are all `0`, so the reading
misses nothing there. Terms of size at most 6, both ways. -/

#guard ((upToProbe 6).filter (fun X => isOT X && decide (X < te0))).all
  fun X => read 0 (unread 0 X) == X

/-! Each of the 85 is standard, below `ψ_0(Ω)`, and read off a matrix; and no
standard form below `ψ_0(Ω)` carries a subscript other than `0`. -/

#guard ((upToProbe 6).filter (fun X => isOT X && decide (X < te0))).all
  fun X => isOT (read 0 (unread 0 X))

#guard ((upToProbe 6).filter (fun X => isOT X && decide (X < te0))).length == 85

/-! ### Standard forms, against the reference implementation

A one-row matrix is standard in
[yaBMS](https://github.com/koteitan/yaBMS) — the reference implementation of
BMS — exactly when its entries are a matrix and its term is a standard form.
That is what `Trans.BMS.prim` takes for its states, and
`Trans.BMS.std_entries_iff` proves it against `Pat.Std`. What the check adds
is that `Pat.Std` and the reference implementation agree.

Over all 1024 sequences of length 5 with entries below 4, `./bms -s` and the
predicate below agree on every one, and 19 come out standard. -/

def colB : Nat → Nat → List Nat → Bool
  | _, _, [] => true
  | b, prev, c :: r => decide (b ≤ c) && decide (c ≤ prev + 1) && colB b c r

def isColB : Nat → List Nat → Bool
  | _, [] => true
  | b, a :: r => (a == b) && colB b a r

/-- A matrix at level `0` whose term is a standard form. -/
def stdB (l : List Nat) : Bool := isColB 0 l && isOT (read 0 l)

/-- Every sequence of length `n` with entries below `4`. -/
def seqs : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (seqs n).flatMap fun l => (List.range 4).map fun k => l ++ [k]

#guard (seqs 5).length == 1024
#guard ((seqs 5).filter stdB).length == 19

/-! The nineteen, and each is read off by the round trip. -/

#guard ((seqs 5).filter stdB).all fun l => read 0 (unread 0 (read 0 l)) == read 0 l

/-! ### The row-0 parent chain

`(0)(1)(2)(1)` as the first row of an array: column 3 has entry 1, so its
parent is column 0; column 2 has entry 2, so its parent is column 1, whose
parent is column 0. Column 0 has none. -/

#guard parAt [0, 1, 2, 1] 3 == some 0
#guard parAt [0, 1, 2, 1] 2 == some 1
#guard parAt [0, 1, 2, 1] 1 == some 0
#guard parAt [0, 1, 2, 1] 0 == none

#guard ancAtB [0, 1, 2, 1] 0 3
#guard ancAtB [0, 1, 2, 1] 0 2
#guard ancAtB [0, 1, 2, 1] 1 2
#guard !(ancAtB [0, 1, 2, 1] 1 3)
#guard !(ancAtB [0, 1, 2, 1] 2 3)
#guard !(ancAtB [0, 1, 2, 1] 0 0)

/-! ### The parent chain, against the reference implementation

`./bms -d` prints a Parent Index Matrix, with `-1` where a column has no
parent. Its row `0` is what `parAt` computes. Five two-row matrices, row `0`
of each:

| matrix | row 0 | `./bms -d` row 0 |
|---|---|---|
| `(0,0)(1,1)(2,1)(1,1)(2,2)` | `0 1 2 1 2` | `-1 0 1 0 3` |
| `(0,0)(1,1)(2,2)(3,3)` | `0 1 2 3` | `-1 0 1 2` |
| `(0,0)(1,1)(1,1)(2,1)` | `0 1 1 2` | `-1 0 0 2` |
| `(0,0)(1,0)(2,0)(1,0)(2,0)` | `0 1 2 1 2` | `-1 0 1 0 3` |
| `(0,0)(1,1)(2,2)(3,1)(4,2)` | `0 1 2 3 4` | `-1 0 1 2 3` |
-/

/-- The row-`0` parents of a list, with `-1` for none, as `./bms -d` prints
them. -/
def parRow (l : List Nat) : List Int :=
  (List.range l.length).map fun i =>
    match parAt l i with
    | none => -1
    | some j => (j : Int)

#guard parRow [0, 1, 2, 1, 2] == [-1, 0, 1, 0, 3]
#guard parRow [0, 1, 2, 3] == [-1, 0, 1, 2]
#guard parRow [0, 1, 1, 2] == [-1, 0, 0, 2]
#guard parRow [0, 1, 2, 3, 4] == [-1, 0, 1, 2, 3]

/-! ### Two-row expansion, against the reference implementation

`expand2L` is `BM4.expand` written on the entries — `Trans.BMS.entries2_expand`
proves that. Running it beside `./bms` is what checks that
`Googology/Notation/BMS` and the reference implement the same `expand`.

The sweep: every two-row matrix of length at most `4` whose first column is
`(0,0)` and whose entries are below `3` — `819` of them, of which `./bms -s`
calls `46` standard — expanded at `0`, `1` and `2`. All `138` agree. The spot
checks below are drawn from it, including the cases where the row-`0`
increment fires and the cases where the matrix grows. -/

#guard expand2L 1 [(0,0),(1,1),(2,1),(3,2)] == [(0,0),(1,1),(2,1),(3,1)]
#guard expand2L 0 [(0,0),(1,1)] == [(0,0)]
#guard expand2L 1 [(0,0),(1,1)] == [(0,0),(1,0)]
#guard expand2L 2 [(0,0),(1,1)] == [(0,0),(1,0),(2,0)]
#guard expand2L 1 [(0,0),(1,1),(2,2)] == [(0,0),(1,1),(2,1)]
#guard expand2L 2 [(0,0),(1,1),(2,2)] == [(0,0),(1,1),(2,1),(3,1)]
#guard expand2L 1 [(0,0),(1,1),(2,1)] == [(0,0),(1,1),(2,0),(3,1)]
#guard expand2L 2 [(0,0),(1,1),(1,1)] == [(0,0),(1,1),(1,0),(2,1),(2,0),(3,1)]
#guard expand2L 1 [(0,0),(1,1),(2,2),(3,3)] == [(0,0),(1,1),(2,2),(3,2)]
#guard expand2L 2 [(0,0),(1,0),(2,0),(1,0)]
  == [(0,0),(1,0),(2,0),(0,0),(1,0),(2,0),(0,0),(1,0),(2,0)]
#guard expand2L 1 [(0,0),(1,1),(2,2),(3,1)] == [(0,0),(1,1),(2,2),(3,0),(4,1),(5,2)]
#guard expand2L 2 [(0,0),(1,1),(2,2),(3,2)]
  == [(0,0),(1,1),(2,2),(3,1),(4,2),(5,1),(6,2)]

#guard expand2L 2 [(0,0),(1,0),(1,0)] == [(0,0),(1,0),(0,0),(1,0),(0,0),(1,0)]
#guard expand2L 2 [(0,0),(1,1),(1,0)] == [(0,0),(1,1),(0,0),(1,1),(0,0),(1,1)]
#guard expand2L 2 [(0,0),(1,1),(2,1)] == [(0,0),(1,1),(2,0),(3,1),(4,0),(5,1)]
#guard expand2L 1 [(0,0),(1,0),(1,0),(1,0)] == [(0,0),(1,0),(1,0),(0,0),(1,0),(1,0)]
#guard expand2L 1 [(0,0),(1,0),(2,0),(1,0)] == [(0,0),(1,0),(2,0),(0,0),(1,0),(2,0)]

/-! A run of expansions at `0` from a pair-sequence generator, one column
shorter each step, and the empty matrix stays empty. -/

def runL : Nat → List (Nat × Nat) → List (Nat × Nat)
  | 0, l => l
  | n + 1, l => runL n (expand2L 0 l)

#guard (List.range 7).map (fun i => (runL i [(0,0),(1,1),(2,2),(3,3)]).length)
  == [4, 3, 2, 1, 0, 0, 0]
#guard expand2L 3 ([] : List (Nat × Nat)) == []

/-! ### The parent matrix at every row

`parAtR` computes the row-`k` parent for any `k`. Both rows of the Parent
Index Matrix that `./bms -d` prints, on two matrices:

| matrix | `./bms -d` |
|---|---|
| `(0,0)(1,1)(2,1)(1,1)(2,2)` | `(-1,-1)(0,0)(1,0)(0,0)(3,3)` |
| `(0,0)(1,1)(2,2)(3,1)(4,2)` | `(-1,-1)(0,0)(1,1)(2,0)(3,3)` |
-/

/-- The row-`k` parents of a matrix, with `-1` for none. -/
def parRowR (l : List (List Nat)) (k : Nat) : List Int :=
  (List.range l.length).map fun i =>
    match parAtR l k i with
    | none => -1
    | some j => (j : Int)

#guard parRowR [[0,0],[1,1],[2,1],[1,1],[2,2]] 0 == [-1, 0, 1, 0, 3]
#guard parRowR [[0,0],[1,1],[2,1],[1,1],[2,2]] 1 == [-1, 0, 0, 0, 3]
#guard parRowR [[0,0],[1,1],[2,2],[3,1],[4,2]] 0 == [-1, 0, 1, 2, 3]
#guard parRowR [[0,0],[1,1],[2,2],[3,1],[4,2]] 1 == [-1, 0, 1, 0, 3]

/-! ### Expansion at any number of rows

`expandRL` is `BM4.expand` on the entries for any `r` —
`Trans.BMS.entriesR_expand` proves that. Against `./bms` at three rows: every
matrix of length at most `3` whose first column is `(0,0,0)` and whose entries
are below `3` — `756` of them, of which `24` are standard — expanded at `0`,
`1` and `2`. All `72` agree. -/

#guard expandRL 3 1 [[0,0,0],[1,1,1]] == [[0,0,0],[1,1,0]]
#guard expandRL 3 2 [[0,0,0],[1,1,1]] == [[0,0,0],[1,1,0],[2,2,0]]
#guard expandRL 3 1 [[0,0,0],[1,1,1],[2,1,0]] == [[0,0,0],[1,1,1],[2,0,0],[3,1,1]]
#guard expandRL 3 2 [[0,0,0],[1,1,1],[2,1,0],[1,1,1]]
  == [[0,0,0],[1,1,1],[2,1,0],[1,1,0],[2,2,1],[3,2,0],[2,2,0],[3,3,1],[4,3,0]]
#guard expandRL 3 2 [[0,0,0],[1,1,1],[2,2,1]]
  == [[0,0,0],[1,1,1],[2,2,0],[3,3,1],[4,4,0],[5,5,1]]
#guard expandRL 3 1 [[0,0,0],[1,1,1],[2,2,2],[3,3,3]] == [[0,0,0],[1,1,1],[2,2,2],[3,3,2]]

/-! One row, through the same definition, agrees with `expandL`. -/

#guard expandRL 1 1 [[0],[1],[2],[3]] == (expandL 1 0 [0,1,2,3]).map (fun a => [a])
#guard expandRL 1 1 [[0],[1],[2],[1],[1]] == (expandL 1 0 [0,1,2,1,1]).map (fun a => [a])

/-! ### DBMS generators, on the entries

Column `i` holds `i - k` in row `k`, which is what `Trans.DBMS.entriesR_dstair`
says. Three rows give `(0,0,0)(1,0,0)(2,1,0)(3,2,1)`, which `./bms -s -v DBMS`
calls standard and `./bms -s` does not. -/

#guard (List.range 4).map (fun i => (List.range 3).map (fun k => i - k))
  == [[0,0,0],[1,0,0],[2,1,0],[3,2,1]]

/-! DBMS expands by the BM4 rule, so `expandRL` serves both, and `./bms` gives
the same answer under either version. -/

#guard expandRL 3 0 [[0,0,0],[1,0,0],[2,1,0],[3,2,1]] == [[0,0,0],[1,0,0],[2,1,0]]
#guard expandRL 3 1 [[0,0,0],[1,0,0],[2,1,0],[3,2,1]]
  == [[0,0,0],[1,0,0],[2,1,0],[3,2,0]]
#guard expandRL 3 2 [[0,0,0],[1,0,0],[2,1,0],[3,2,1]]
  == [[0,0,0],[1,0,0],[2,1,0],[3,2,0],[4,3,0]]

/-! ### Four rows

`expandRL` does not care how many rows there are. Five four-row matrices
against `./bms`, all agreeing. -/

#guard expandRL 4 2 [[0,0,0,0],[1,1,1,1]] == [[0,0,0,0],[1,1,1,0],[2,2,2,0]]
#guard expandRL 4 1 [[0,0,0,0],[1,1,1,1],[2,2,2,1]]
  == [[0,0,0,0],[1,1,1,1],[2,2,2,0],[3,3,3,1]]
#guard expandRL 4 2 [[0,0,0,0],[1,1,1,1],[2,2,1,0]]
  == [[0,0,0,0],[1,1,1,1],[2,2,0,0],[3,3,1,1],[4,4,0,0],[5,5,1,1]]
#guard expandRL 4 1 [[0,0,0,0],[1,1,1,1],[2,2,2,2],[3,3,3,1]]
  == [[0,0,0,0],[1,1,1,1],[2,2,2,2],[3,3,3,0],[4,4,4,1],[5,5,5,2]]
#guard expandRL 4 2 [[0,0,0,0],[1,1,1,0],[2,1,0,0]]
  == [[0,0,0,0],[1,1,1,0],[2,0,0,0],[3,1,1,0],[4,0,0,0],[5,1,1,0]]

/-! ### Matrices that are not standard forms

`Trans.BMS.bmsAllL_terminates` says expansion ends from any matrix, standard
or not. Three that are not standard — a first column other than all zeros,
entries out of order — run down to the empty matrix. -/

def runR (r : Nat) : Nat → Nat → List (List Nat) → List (List Nat)
  | 0, _, l => l
  | n + 1, k, l => runR r n k (expandRL r k l)

#guard (List.range 9).map (fun i => (runR 1 i 1 [[3],[1],[2]]).length)
  == [3, 3, 2, 1, 0, 0, 0, 0, 0]
#guard (List.range 9).map (fun i => (runR 2 i 1 [[2,1],[1,3],[3,0]]).length)
  == [3, 3, 2, 1, 0, 0, 0, 0, 0]
#guard (List.range 9).map (fun i => (runR 3 i 0 [[5,2,9],[1,1,1],[4,0,3]]).length)
  == [3, 2, 1, 0, 0, 0, 0, 0, 0]

/-! ### A row of zeros underneath

`Trans.BMS.expand2L_withZero` says the two-row rule on a one-row matrix with a
zero row added is the one-row rule. The matrices stay standard too, which the
theorem does not claim: `./bms -s` says so for the four below. -/

#guard ([[0,1,2], [0,1,1], [0,1,2,1,1], [0,1,0,1]] : List (List Nat)).all fun l =>
  expand2L 1 (withZero l) == withZero (expandL 1 0 l)

#guard ([[0,1,2], [0,1,1], [0,1,2,1,1], [0,1,0,1]] : List (List Nat)).all fun l =>
  (List.range 3).all fun n => expand2L n (withZero l) == withZero (expandL n 0 l)

/-! ### A row of zeros underneath, at any number of rows

`Trans.BMS.expandRL_zeroRow` says the same at every number of rows, and
`./bms` agrees: `(0,0)(1,1)(2,2)(1,1)[2]` and `(0,0,0)(1,1,0)(2,2,0)(1,1,0)[2]`
give the same matrix, one with the zero row and one without. -/

#guard expandRL 3 2 (zeroRow [[0,0],[1,1],[2,2],[1,1]])
  == zeroRow [[0,0],[1,1],[2,2],[1,0],[2,1],[3,2],[2,0],[3,1],[4,2]]
#guard ([[[0,0],[1,1],[2,2],[1,1]], [[0,0],[1,1],[2,1]], [[0,0],[1,1],[2,2],[3,1]]]
    : List (List (List Nat))).all fun l =>
  (List.range 3).all fun n => expandRL 3 n (zeroRow l) == zeroRow (expandRL 2 n l)
#guard ([[[0,0,0],[1,1,1],[2,1,0]], [[0,0,0],[1,1,1],[2,2,2],[3,3,3]]]
    : List (List (List Nat))).all fun l =>
  (List.range 3).all fun n => expandRL 4 n (zeroRow l) == zeroRow (expandRL 3 n l)

/-! `Trans.BMS.expandRL_gen`: the generator with one more row expands to the
generators with one fewer, with the zero row already underneath. Against
`./bms "(0,0,0)(1,1,1)[3]"` and `./bms "(0,0,0,0)(1,1,1,1)[2]"`. -/

#guard expandRL 3 3 [[0,0,0],[1,1,1]] == zeroRow [[0,0],[1,1],[2,2],[3,3]]
#guard expandRL 4 2 [[0,0,0,0],[1,1,1,1]] == zeroRow [[0,0,0],[1,1,1],[2,2,2]]

end Googology.Trans.BMS
