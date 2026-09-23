import Googology.Notation.ExBuchholz.Cofinal
import Googology.Notation.ExBuchholz.Onto
import Googology.Rank

/-!
# The rank of `exbOT` is the value of the term

`exbOT` carries two ordinal measures.  One is `exbOTEval`, the value of the
term.  The other is the rank of the one-step relation, which needs nothing but
the steps to define.  **They are the same**: `rank_exbOT_eq_val`.

One direction is `Eval.rank_le`: the rank is at most any measure.  The other
direction takes an ordinal `α` below `val X`.  `Onto.lean` gives a standard
`Y < X` with `val Y = α`, and `Cofinal.lean` puts `Y` at or below some step
`X[n]`.  So `α` does not exceed the value of a step, and that value is its
rank by induction, which is below the rank of `X`.
-/

namespace Googology.Notation.ExBuchholz.Term
open Googology

instance instIsWellFoundedExbOT : IsWellFounded exbOT.State exbOT.Rel := ⟨exbOT_wf⟩

/-- **The rank of the expansion system on the countable standard forms is the
value of the term.** -/
theorem rank_exbOT_eq_val : ∀ A : exbOT.State,
    IsWellFounded.rank exbOT.Rel A = val A.1 := by
  intro A
  induction A using WellFounded.induction exbOT_wf with
  | _ A IH =>
    refine le_antisymm (Eval.rank_le exbOTEval A) ?_
    refine le_of_forall_lt (fun α hα => ?_)
    have hne : A.1 ≠ nil := by
      intro h
      rw [h, val_nil] at hα
      exact absurd hα (by simp)
    obtain ⟨Y, ⟨hY, hYA, hvY⟩, _⟩ := existsUnique_OT_lt_of_lt_val A.2.1 A.2.2 hα
    obtain ⟨n, hn⟩ := exbOT_exists_le_step A hne hY hYA
    have hrel : exbOT.Rel (exbOT.step A n) A := ⟨hne, n, rfl⟩
    calc α = val Y := hvY.symm
      _ ≤ val (exbOT.step A n).1 := val_le_val_OT hY (exbOT.step A n).2.1 hn
      _ = IsWellFounded.rank exbOT.Rel (exbOT.step A n) := (IH _ hrel).symm
      _ < IsWellFounded.rank exbOT.Rel A := IsWellFounded.rank_lt_of_rel hrel

/-- **The value of a countable standard form equals the rank**, as the
ordinal-translation table states it: the evaluation `exbOTEval` and the rank
evaluation `Rewrite.rankEval` are one map. -/
theorem exbOTEval_eq_rankEval :
    exbOTEval.val = (Rewrite.rankEval exbOT_wf).val := by
  funext A
  exact (rank_exbOT_eq_val A).symm

end Googology.Notation.ExBuchholz.Term
