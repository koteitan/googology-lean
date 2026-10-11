import Googology.Goals
import Googology.Trans.BMS.ExBuchholz.PSS.Steps

/-!
# Pair sequences → extended Buchholz's ψ: reachability

`Goals.lean` refutes that `pairToExb` preserves one expansion step
(`pairToExb_not_preserves`).  This file proves the weaker statement that holds:
one step goes to one or more steps of `exbPair`, and more precisely `pairToExb`
preserves and reflects the transitive closure of the step relation.

`exbPair_transGen_iff` (`B` is reached from `A` in `exbPair` iff `B < A`) and
`pairToExb_transGen_iff` (`pairToExb b` is reached from `pairToExb a` iff `b` is
reached from `a`) are in `Goals.lean`, where the cofinality of `pairToExb`
(`pairToExb_cofinal`) uses them.  This file adds

* `pairToExb_preserves_transGen`: `pairL.Rel b a → TransGen exbPair.Rel
  (pairToExb b) (pairToExb a)`.

The term-level results are in `Trans/BMS/ExBuchholz/PSS/Steps.lean`.
-/

namespace Googology.Goals
open Googology.Trans.BMS Googology.Trans.PSS Googology.Notation.ExBuchholz Googology.Notation.ExBuchholz.Term
open Relation

/-- **One step of the pair sequences goes to finitely many (≥ 1) steps of `exbPair`.** -/
theorem pairToExb_preserves_transGen {a b : PairState} (h : pairL.Rel b a) :
    TransGen exbPair.Rel (pairToExb b) (pairToExb a) :=
  (pairToExb_transGen_iff a b).mpr (TransGen.single h)

end Googology.Goals
