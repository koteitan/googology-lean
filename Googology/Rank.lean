import Googology.Core
import Mathlib.SetTheory.Ordinal.Rank

/-!
# Every well-founded system has a canonical ordinal measure

`Rewrite.wf_of_measure` goes one way: a measure into a well-founded order
proves well-foundedness.  This file goes the other: a well-founded system
carries a measure into the ordinals, namely the rank of its one-step relation.

So `Eval R (· < · : Ordinal → Ordinal → Prop)` is never empty for a system that
terminates for any reason at all, and `Eval.ofSim` then transports that measure
backwards along any translation into it.

This is the one part of the library outside `Notation/` that needs mathlib, so
it is kept out of `Googology.Core`.
-/

namespace Googology

open Ordinal

/-- The rank of the one-step relation, as an evaluation into the ordinals. -/
noncomputable def Rewrite.rankEval {R : Rewrite} (h : R.WF) :
    Eval R (· < · : Ordinal.{0} → Ordinal.{0} → Prop) :=
  have : IsWellFounded R.State R.Rel := ⟨h⟩
  { val := IsWellFounded.rank R.Rel
    val_lt := fun _ _ hab => IsWellFounded.rank_lt_of_rel hab }

/-- A system terminates if and only if... one direction restated: the ordinal
measure a well-founded system carries proves its termination back. -/
theorem Rewrite.terminates_of_rankEval {R : Rewrite} (h : R.WF) : R.Terminates :=
  (Rewrite.rankEval h).terminates Ordinal.lt_wf

/-- A translation into a well-founded system pulls the rank back, so the source
gets an ordinal measure too. -/
noncomputable def Sim.rankEval {R Q : Rewrite} (f : Sim R Q) (h : Q.WF) :
    Eval R (· < · : Ordinal.{0} → Ordinal.{0} → Prop) :=
  Eval.ofSim f (Rewrite.rankEval h)

end Googology
