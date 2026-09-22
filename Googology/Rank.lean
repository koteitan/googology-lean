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

`wf_of_terminates` is the other half of the pair: a descending chain never
halts, so a system that terminates cannot have one.  With
`terminates_of_wf` that makes well-foundedness and termination the same
condition, and `rankEvalOfTerminates` turns either of them into an ordinal
measure.  It lives here rather than in `Core` because building the chain from
a non-accessible state needs choice, and `Core` uses none.

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


/-- **A terminating system is well founded.**  A descending chain never
halts, and termination says every chain does. -/
theorem Rewrite.wf_of_terminates {R : Rewrite} (h : R.Terminates) : R.WF := by
  constructor
  intro a
  by_contra hc
  obtain ⟨f, _, hf⟩ := not_acc_iff_exists_descending_chain.mp hc
  obtain ⟨n, hn⟩ := h f (fun n => (hf n).2)
  exact (hf n).1 hn

/-- **Well-foundedness and termination are the same condition.** -/
theorem Rewrite.wf_iff_terminates {R : Rewrite} : R.WF ↔ R.Terminates :=
  ⟨R.terminates_of_wf, Rewrite.wf_of_terminates⟩

/-- So a system that terminates for any reason at all carries the rank of its
own expansion as an ordinal measure. -/
noncomputable def Rewrite.rankEvalOfTerminates {R : Rewrite} (h : R.Terminates) :
    Eval R (· < · : Ordinal.{0} → Ordinal.{0} → Prop) :=
  Rewrite.rankEval (Rewrite.wf_of_terminates h)

end Googology
