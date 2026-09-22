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

end Googology.Trans.BMS
