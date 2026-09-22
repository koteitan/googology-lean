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

`StepHom.rank_map` goes the other way about: a translation that renumbers
brackets onto and halts exactly where the source halts gives its image the
steps the source has, so the rank is the same on both sides.  That is what
says an embedding does not change the ordinal a state names.

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

/-! ## A translation that is onto the steps keeps the rank -/

/-- **A `StepHom` whose bracket renumbering is onto and whose image halts
exactly where the source does carries the rank across unchanged.**  Its image
has precisely the steps the source has, so the two recursions agree. -/
theorem StepHom.rank_map {R Q : Rewrite} [hR : IsWellFounded R.State R.Rel]
    [IsWellFounded Q.State Q.Rel] (f : StepHom R Q)
    (hre : Function.Surjective f.reindex)
    (hh : ∀ s, R.halted s ↔ Q.halted (f.map s)) :
    ∀ a, IsWellFounded.rank Q.Rel (f.map a) = IsWellFounded.rank R.Rel a := by
  intro a
  induction a using WellFounded.induction hR.wf with
  | _ a ih =>
    refine le_antisymm ?_ ?_
    · rw [IsWellFounded.rank_eq]
      refine Ordinal.iSup_le ?_
      rintro ⟨b, hna, k, rfl⟩
      obtain ⟨n, rfl⟩ := hre k
      have hrel : R.Rel (R.step a n) a := ⟨fun hc => hna ((hh a).mp hc), n, rfl⟩
      have hval : IsWellFounded.rank Q.Rel (Q.step (f.map a) (f.reindex n))
          = IsWellFounded.rank R.Rel (R.step a n) := by
        rw [← f.map_step a n]
        exact ih _ hrel
      show Order.succ (IsWellFounded.rank Q.Rel (Q.step (f.map a) (f.reindex n))) ≤ _
      rw [hval]
      exact Order.succ_le_of_lt (IsWellFounded.rank_lt_of_rel hrel)
    · rw [IsWellFounded.rank_eq]
      refine Ordinal.iSup_le ?_
      rintro ⟨b, hna, k, rfl⟩
      show Order.succ (IsWellFounded.rank R.Rel (R.step a k)) ≤ _
      rw [← ih _ ⟨hna, k, rfl⟩]
      exact Order.succ_le_of_lt (IsWellFounded.rank_lt_of_rel
        ⟨fun hc => hna ((hh a).mpr hc), f.reindex k, f.map_step a k⟩)

end Googology
