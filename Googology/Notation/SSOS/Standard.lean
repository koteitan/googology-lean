import Googology.Notation.SSOS.Def

/-!
Reachability definition of the 0/1 standard fragment, as proposed in the
handover. It does not use the Python greedy test or its unproved no-gaps
assumption. The generators and both closure operations are the actual ones.
-/

namespace Googology.Notation.SSOS

inductive Standard : List ℕ → Prop
  | tower (n : ℕ) : Standard ([0,0] ++ List.replicate n 1)
  | expand {S : List ℕ} (hS : Standard S) (hpos : 0 < Seq.entry S S.length)
      (k : ℕ) (hk : 1 ≤ k) : Standard (Seq.fs S k)
  | erase {S : List ℕ} (hS : Standard (S ++ [0])) : Standard S

end Googology.Notation.SSOS
