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

`Eval.rank_le` says the rank is the least of these measures: any evaluation
into the ordinals bounds it.  So a translation gives an upper bound on how far
a system reaches, and the rank gives a lower one.

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

/-- **A state whose every step gives the same state has rank one more than
it.**  These are the successor states of the system: the bracket makes no
difference there. -/
theorem Rewrite.rank_succ_of_const_step {R : Rewrite} [IsWellFounded R.State R.Rel]
    {a b : R.State} (hna : ¬ R.halted a) (h : ∀ k, R.step a k = b) :
    IsWellFounded.rank R.Rel a = Order.succ (IsWellFounded.rank R.Rel b) := by
  rw [IsWellFounded.rank_eq]
  refine le_antisymm (Ordinal.iSup_le ?_) ?_
  · rintro ⟨m, _, k, rfl⟩
    show Order.succ (IsWellFounded.rank R.Rel (R.step a k)) ≤ _
    rw [h k]
  · exact Ordinal.le_iSup (fun b : {b // R.Rel b a} => Order.succ (IsWellFounded.rank R.Rel b.1))
      ⟨b, hna, 0, (h 0).symm⟩

/-- The rank recursion, with the brackets as the index. -/
theorem Rewrite.rank_eq_iSup_nat {R : Rewrite} [IsWellFounded R.State R.Rel] {a : R.State}
    (h : ¬ R.halted a) :
    IsWellFounded.rank R.Rel a
      = ⨆ N : Nat, Order.succ (IsWellFounded.rank R.Rel (R.step a N)) := by
  rw [IsWellFounded.rank_eq]
  refine le_antisymm (Ordinal.iSup_le ?_) (Ordinal.iSup_le (fun N => ?_))
  · rintro ⟨m, _, N, rfl⟩
    exact Ordinal.le_iSup
      (fun N : Nat => Order.succ (IsWellFounded.rank R.Rel (R.step a N))) N
  · exact Ordinal.le_iSup
      (fun b : {b // R.Rel b a} => Order.succ (IsWellFounded.rank R.Rel b.1))
      ⟨R.step a N, h, N, rfl⟩

/-- A state that can step has positive rank. -/
theorem Rewrite.rank_pos {R : Rewrite} [IsWellFounded R.State R.Rel] {a : R.State}
    (h : ¬ R.halted a) : 0 < IsWellFounded.rank R.Rel a := by
  rw [Rewrite.rank_eq_iSup_nat h]
  refine lt_of_lt_of_le ?_ (Ordinal.le_iSup
    (fun N : Nat => Order.succ (IsWellFounded.rank R.Rel (R.step a N))) 0)
  exact lt_of_le_of_lt (by simp) (Order.lt_succ _)

/-- A halting state has rank `0`. -/
theorem Rewrite.rank_halted {R : Rewrite} [IsWellFounded R.State R.Rel] {a : R.State}
    (h : R.halted a) : IsWellFounded.rank R.Rel a = 0 := by
  rw [IsWellFounded.rank_eq]
  exact le_antisymm (Ordinal.iSup_le (fun b => absurd h b.2.1)) (by simp)

/-- **The rank is the least ordinal measure.**  Any `Eval` into the ordinals
bounds it from above, so a translation gives an upper bound and the rank gives
a lower one. -/
theorem Eval.rank_le {R : Rewrite} [IsWellFounded R.State R.Rel]
    (e : Eval R (· < · : Ordinal.{0} → Ordinal.{0} → Prop)) :
    ∀ a, IsWellFounded.rank R.Rel a ≤ e.val a := by
  intro a
  induction a using WellFounded.induction (IsWellFounded.wf (r := R.Rel)) with
  | _ a IH =>
    rw [IsWellFounded.rank_eq]
    refine Ordinal.iSup_le ?_
    rintro ⟨b, hb⟩
    show Order.succ (IsWellFounded.rank R.Rel b) ≤ e.val a
    exact Order.succ_le_of_lt (lt_of_le_of_lt (IH b hb) (e.val_lt a b hb))

/-! ## Well-foundedness and rank on the standard forms -/

/-- **Termination from the standard forms gives well-foundedness on them.**  A
standard state that is not accessible starts a descending chain of standard
states, and a chain of steps from a standard state halts. -/
theorem Rewrite.Std.wf_of_terminates {R : Rewrite} (S : R.Std) (h : S.Terminates) :
    S.WF := by
  constructor
  intro a
  by_contra hc
  obtain ⟨f, -, hf⟩ := not_acc_iff_exists_descending_chain.mp hc
  obtain ⟨n, hn⟩ := h (fun n => (f n).1) (f 0).2 (fun n => (hf n).2)
  exact (hf n).1 hn

/-- **On the standard forms, well-foundedness and termination are the same
condition.** -/
theorem Rewrite.Std.wf_iff_terminates {R : Rewrite} (S : R.Std) : S.WF ↔ S.Terminates :=
  ⟨S.terminates_of_wf, S.wf_of_terminates⟩

/-- The rank of one step, on all states.  It is `(Rewrite.rankEval h).val`. -/
noncomputable def Rewrite.rank {R : Rewrite} (h : R.WF) : R.State → Ordinal.{0} :=
  (Rewrite.rankEval h).val

theorem Rewrite.rank_def {R : Rewrite} (h : R.WF) (a : R.State) :
    Rewrite.rank h a = @IsWellFounded.rank _ R.Rel ⟨h⟩ a := rfl

/-- The rank of one step restricted to the standard forms. -/
noncomputable def Rewrite.Std.rank {R : Rewrite} (S : R.Std) (h : S.WF) :
    (a : R.State) → S.Standard a → Ordinal.{0} :=
  fun a ha => @IsWellFounded.rank _ (fun b a : {s // S.Standard s} => R.Rel b.1 a.1) ⟨h⟩ ⟨a, ha⟩

/-- **On a standard state the two ranks agree**, because every step of a
standard state is standard. -/
theorem Rewrite.Std.rank_eq {R : Rewrite} (S : R.Std) (h : R.WF)
    (a : R.State) (ha : S.Standard a) :
    S.rank (S.wf_of_wf h) a ha = Rewrite.rank h a := by
  haveI : IsWellFounded R.State R.Rel := ⟨h⟩
  haveI hS : IsWellFounded {s // S.Standard s} (fun b a => R.Rel b.1 a.1) := ⟨S.wf_of_wf h⟩
  show IsWellFounded.rank (fun b a : {s // S.Standard s} => R.Rel b.1 a.1) ⟨a, ha⟩
    = IsWellFounded.rank R.Rel a
  induction a using WellFounded.induction h with
  | _ a ih =>
    refine le_antisymm ?_ ?_
    · rw [IsWellFounded.rank_eq]
      refine Ordinal.iSup_le ?_
      rintro ⟨⟨b, hb⟩, hrel⟩
      show Order.succ (IsWellFounded.rank (fun b a : {s // S.Standard s} => R.Rel b.1 a.1)
        ⟨b, hb⟩) ≤ _
      rw [ih b hrel hb]
      exact Order.succ_le_of_lt (IsWellFounded.rank_lt_of_rel hrel)
    · rw [IsWellFounded.rank_eq]
      refine Ordinal.iSup_le ?_
      rintro ⟨b, hrel⟩
      have hb : S.Standard b := by
        obtain ⟨_, k, rfl⟩ := hrel
        exact S.step_std a k ha
      show Order.succ (IsWellFounded.rank R.Rel b) ≤ _
      rw [← ih b hrel hb]
      exact Order.succ_le_of_lt
        (IsWellFounded.rank_lt_of_rel (r := fun b a : {s // S.Standard s} => R.Rel b.1 a.1)
          (a := ⟨b, hb⟩) (b := ⟨a, ha⟩) hrel)

end Googology
