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

end Googology.Trans.BMS
