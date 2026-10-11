import Googology.Rank

/-!
# Cofinality: the common form

A translation into the ordinals that lowers the value on every step
(`Eval.val_lt`) bounds the rank from above (`Eval.rank_le`).  The other half is
cofinality: below the value of a state, the expansions of the state reach up
to every ordinal.  Each notation proves that from its own cofinality of
fundamental sequences (`exists_le_fs` for the primitive sequences,
`exists_le_oper` for the pair sequences, …), in its own words.

`Eval.Cofinal` is the one statement they all reduce to, and
`Eval.Cofinal.rank_eq` is what it buys: a cofinal evaluation is the rank.  So
a notation that wants "the value is the rank" proves `Eval.Cofinal` for its
evaluation and nothing else.
-/

namespace Googology

open Ordinal

/-- **Cofinality of an evaluation into the ordinals.**  Every ordinal below the
value of a state is at most the value of one of its one-step successors. -/
structure Eval.Cofinal {R : Rewrite}
    (e : Eval R (· < · : Ordinal.{0} → Ordinal.{0} → Prop)) : Prop where
  /-- Below the value of `a`, some successor of `a` reaches at least as high. -/
  exists_ge : ∀ a, ∀ β < e.val a, ∃ b, R.Rel b a ∧ β ≤ e.val b

/-- **A cofinal evaluation is the rank.**  `Eval.rank_le` is one inequality;
cofinality gives the other, by induction along the steps. -/
theorem Eval.Cofinal.rank_eq {R : Rewrite} [IsWellFounded R.State R.Rel]
    {e : Eval R (· < · : Ordinal.{0} → Ordinal.{0} → Prop)} (hc : e.Cofinal) :
    ∀ a, IsWellFounded.rank R.Rel a = e.val a := by
  intro a
  induction a using WellFounded.induction (IsWellFounded.wf (r := R.Rel)) with
  | _ a IH =>
    refine le_antisymm (e.rank_le a) (le_of_forall_lt fun β hβ => ?_)
    obtain ⟨b, hb, hβb⟩ := hc.exists_ge a β hβ
    calc β ≤ e.val b := hβb
      _ = IsWellFounded.rank R.Rel b := (IH b hb).symm
      _ < IsWellFounded.rank R.Rel a := IsWellFounded.rank_lt_of_rel hb

/-- **The rank is cofinal.**  An evaluation that equals the rank is cofinal,
because the rank is the supremum of `rank b + 1` over the successors `b`. -/
theorem Eval.cofinal_of_rank_eq {R : Rewrite} [IsWellFounded R.State R.Rel]
    (e : Eval R (· < · : Ordinal.{0} → Ordinal.{0} → Prop))
    (he : ∀ a, IsWellFounded.rank R.Rel a = e.val a) : e.Cofinal where
  exists_ge a β hβ := by
    rw [← he a, IsWellFounded.rank_eq] at hβ
    obtain ⟨⟨b, hb⟩, hβb⟩ := Ordinal.lt_iSup_iff.mp hβ
    exact ⟨b, hb, by rw [← he b]; exact Order.lt_succ_iff.mp hβb⟩

/-- **Cofinality on the standard forms**: the successor that reaches high
enough is standard when its source is, because a step keeps a state
standard.  This is the form of the column "cofinal" of `OrdGoals`. -/
theorem Eval.Cofinal.std {R : Rewrite}
    {e : Eval R (· < · : Ordinal.{0} → Ordinal.{0} → Prop)} (hc : e.Cofinal) (S : R.Std) :
    ∀ a, S.Standard a → ∀ β < e.val a, ∃ b, S.Standard b ∧ R.Rel b a ∧ β ≤ e.val b := by
  intro a ha β hβ
  obtain ⟨b, hb, hβb⟩ := hc.exists_ge a β hβ
  refine ⟨b, ?_, hb, hβb⟩
  obtain ⟨-, k, rfl⟩ := hb
  exact S.step_std a k ha

/-- The same with the rank of `Googology/Rank.lean`. -/
theorem Eval.Cofinal.rank_eq' {R : Rewrite} (h : R.WF)
    {e : Eval R (· < · : Ordinal.{0} → Ordinal.{0} → Prop)} (hc : e.Cofinal) (a : R.State) :
    Rewrite.rank h a = e.val a := by
  haveI : IsWellFounded R.State R.Rel := ⟨h⟩
  rw [Rewrite.rank_def]
  exact hc.rank_eq a

/-! ## Cofinality of a translation between notations

A translation `F : R → Q` is cofinal when every step of an image is reached,
in zero or more steps of `Q`, from the image of a step.  With "one step goes
to one or more steps" it carries the rank across (`Rewrite.rank_map_of_cofinal`),
just as `Eval.Cofinal` with the descent gives the rank. -/

/-- Along zero or more steps the rank does not grow. -/
theorem rank_le_of_reflTransGen {α : Type} {r : α → α → Prop} [IsWellFounded α r]
    {a b : α} (h : Relation.ReflTransGen r a b) :
    IsWellFounded.rank r a ≤ IsWellFounded.rank r b := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => exact ih.trans (IsWellFounded.rank_lt_of_rel hbc).le

/-- Along one or more steps the rank goes down. -/
theorem rank_lt_of_transGen {α : Type} {r : α → α → Prop} [IsWellFounded α r]
    {a b : α} (h : Relation.TransGen r a b) :
    IsWellFounded.rank r a < IsWellFounded.rank r b := by
  induction h with
  | single h => exact IsWellFounded.rank_lt_of_rel h
  | tail _ hbc ih => exact ih.trans (IsWellFounded.rank_lt_of_rel hbc)

/-- **A cofinal translation that sends one step to one or more steps keeps the
rank.** -/
theorem Rewrite.rank_map_of_cofinal {R Q : Rewrite} [IsWellFounded R.State R.Rel]
    [IsWellFounded Q.State Q.Rel] (F : R.State → Q.State)
    (hp : ∀ a b, R.Rel b a → Relation.TransGen Q.Rel (F b) (F a))
    (hc : ∀ a c, Q.Rel c (F a) → ∃ b, R.Rel b a ∧ Relation.ReflTransGen Q.Rel c (F b)) :
    ∀ a, IsWellFounded.rank Q.Rel (F a) = IsWellFounded.rank R.Rel a := by
  intro a
  induction a using WellFounded.induction (IsWellFounded.wf (r := R.Rel)) with
  | _ a IH =>
    refine le_antisymm ?_ ?_
    · rw [IsWellFounded.rank_eq]
      refine Ordinal.iSup_le ?_
      rintro ⟨c, hc'⟩
      obtain ⟨b, hb, hcb⟩ := hc a c hc'
      refine Order.succ_le_of_lt ?_
      calc IsWellFounded.rank Q.Rel c ≤ IsWellFounded.rank Q.Rel (F b) := rank_le_of_reflTransGen hcb
        _ = IsWellFounded.rank R.Rel b := IH b hb
        _ < IsWellFounded.rank R.Rel a := IsWellFounded.rank_lt_of_rel hb
    · rw [IsWellFounded.rank_eq]
      refine Ordinal.iSup_le ?_
      rintro ⟨b, hb⟩
      refine Order.succ_le_of_lt ?_
      rw [← IH b hb]
      exact rank_lt_of_transGen (hp a b hb)

/-- **A translation that commutes with expansion is cofinal**, when its
renumbering of brackets is onto and it halts exactly where the source does:
every step of an image is the image of a step.  These are the hypotheses of
`StepHom.rank_map`. -/
theorem StepHom.cofinal {R Q : Rewrite} (f : StepHom R Q)
    (hre : Function.Surjective f.reindex) (hh : ∀ s, R.halted s ↔ Q.halted (f.map s)) :
    ∀ a c, Q.Rel c (f.map a) → ∃ b, R.Rel b a ∧ Relation.ReflTransGen Q.Rel c (f.map b) := by
  rintro a c ⟨hna, k', rfl⟩
  obtain ⟨k, rfl⟩ := hre k'
  refine ⟨R.step a k, ⟨fun h => hna ((hh a).mp h), k, rfl⟩, ?_⟩
  rw [f.map_step]

/-- **Mutually inverse translations are cofinal**: a step of an image goes
back to a step of the source, whose image it is. -/
theorem Equiv.cofinal {R Q : Rewrite} (e : Equiv R Q) :
    ∀ a c, Q.Rel c (e.toFun.map a) →
      ∃ b, R.Rel b a ∧ Relation.ReflTransGen Q.Rel c (e.toFun.map b) := by
  intro a c hc
  refine ⟨e.invFun.map c, ?_, ?_⟩
  · have h := e.invFun.map_rel _ _ hc
    rwa [e.left_inv] at h
  · rw [e.right_inv]

end Googology
