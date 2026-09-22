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

end Googology.Trans.BMS
