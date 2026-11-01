import Googology.Notation.SSOS.Flat

/-!
Experimental shape invariant, independent of `Standard` and `CutCorrect`.
At each depth, blocks are nonincreasing in lexicographic order, separated
by exactly two external zeros. Extra zeros are allowed only at the end.
No theorem identifying this predicate with standardness is claimed here.
-/

namespace Googology.Notation.SSOS

inductive StdShape : List U → Prop
  | nil : StdShape []
  | zero {t : List U} : StdShape t → StdShape (.z :: t)
  | single {u : List U} : StdShape u → StdShape [.b u]
  | next {u v P : List U} : StdShape u → StdShape (.b v :: P) →
      raiseBits (flat u) ≤ raiseBits (flat v) →
      StdShape (.b u :: .z :: .z :: .b v :: P)

theorem StdShape.canonical {t : List U} (h : StdShape t) : Canonical t := by
  induction h with
  | nil => exact .nil
  | zero _ ih => exact .zero ih
  | single _ ih => exact .block ih .nil trivial
  | next _ _ _ ihu ihP => exact .block ihu (.zero (.zero ihP)) trivial

theorem StdShape.tower (n : ℕ) : StdShape (Googology.Notation.SSOS.tower n) := by
  induction n with
  | zero => exact .nil
  | succ n ih => exact .single ih

theorem StdShape.erase {t : List U} (h : StdShape (.z :: t)) : StdShape t := by
  cases h with
  | zero h => exact h

end Googology.Notation.SSOS
