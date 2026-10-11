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

/-- The same with the rank of `Googology/Rank.lean`. -/
theorem Eval.Cofinal.rank_eq' {R : Rewrite} (h : R.WF)
    {e : Eval R (· < · : Ordinal.{0} → Ordinal.{0} → Prop)} (hc : e.Cofinal) (a : R.State) :
    Rewrite.rank h a = e.val a := by
  haveI : IsWellFounded R.State R.Rel := ⟨h⟩
  rw [Rewrite.rank_def]
  exact hc.rank_eq a

end Googology
