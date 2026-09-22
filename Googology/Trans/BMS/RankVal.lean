import Googology.Trans.BMS.Same
import Googology.Trans.BMS.Eps0

/-!
# The rank of the system is the ordinal of the term

A well-founded system carries a canonical ordinal measure of its own, the rank
of its one-step relation (`Googology/Rank.lean`), and it needs no notation
system to define.  The primitive sequence system also carries `primEval`, the
value of the extended Buchholz term the matrix reads as.  **They are the
same measure**: `rank_prim_eq_val`.

One direction is the descent, which `primEval` already states.  The other is
cofinality, and it is where `val` being onto below `ε₀` is used: an ordinal
`β` below the term's value is the value of some standard form `Y`, `Y` is then
below the term, and `Cofinal.exists_le_fs` puts `Y` under some `X[n]`.  So
nothing below the value escapes the supremum over the expansions.

That is what licenses reading `Rewrite.rankEval` as "the ordinal this matrix
names" at numbers of rows where no reading is available: at one row, where
both are defined, they agree.
-/

namespace Googology.Trans.BMS
open Ordinal
open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term

theorem val_le_val {x y : Term} (hx : OT x) (hy : OT y) (h : x ≤ y) : val x ≤ val y := by
  rcases le_iff_lt_or_eq.mp h with hlt | rfl
  · exact (val_lt_val hx hy hlt).le
  · exact le_refl _

instance instIsWellFoundedPrim : IsWellFounded prim.State prim.Rel := ⟨prim_wf⟩

/-- **The rank of the primitive sequence system is the value of the term.** -/
theorem rank_prim_eq_val : ∀ l : PrimState,
    IsWellFounded.rank prim.Rel l = val (read 0 l.1) := by
  intro l
  induction l using WellFounded.induction prim_wf with
  | _ l IH =>
    rw [IsWellFounded.rank_eq]
    refine le_antisymm ?_ ?_
    · refine Ordinal.iSup_le ?_
      rintro ⟨m, hna, N, rfl⟩
      show Order.succ (IsWellFounded.rank prim.Rel (prim.step l N)) ≤ _
      rw [IH _ ⟨hna, N, rfl⟩]
      exact Order.succ_le_of_lt (primEval.val_lt l (prim.step l N) ⟨hna, N, rfl⟩)
    · refine le_of_forall_lt (fun β hβ => ?_)
      have hX : OT (read 0 l.1) := l.2.2
      have hAX : AllNil (read 0 l.1) := allNil_read 0 l.1
      have hβ0 : β < Ord.eps0 := lt_trans hβ (val_read_lt_eps0 hX)
      obtain ⟨Y, hOTY, hAY, hvY⟩ := exists_OT_of_lt_eps0 hβ0
      have hYX : Y < read 0 l.1 := lt_of_val_lt hOTY hX (by rw [hvY]; exact hβ)
      obtain ⟨n, hn⟩ := exists_le_fs (read 0 l.1) Y hX hOTY hAX hAY hYX
      have hnil : ¬ prim.halted l := by
        intro h
        have : read 0 l.1 = nil := by
          show read 0 l.1 = nil
          rw [show l.1 = [] from h, read_nil]
        rw [this, val_nil] at hβ
        exact absurd hβ (by simp)
      have hrel : prim.Rel (prim.step l n) l := ⟨hnil, n, rfl⟩
      refine Ordinal.lt_iSup_iff.mpr ⟨⟨prim.step l n, hrel⟩, ?_⟩
      show β < Order.succ (IsWellFounded.rank prim.Rel (prim.step l n))
      refine lt_of_le_of_lt ?_ (Order.lt_succ _)
      rw [IH _ hrel]
      show β ≤ val (read 0 (expandL n 0 l.1))
      rw [read_expandL n l.1 0 l.2.1, ← hvY]
      exact val_le_val hOTY (Term.step_ok hX (read_lt_tW 0 l.1) (n + 1)).1 hn

/-- **The two measures on the primitive sequence system are one measure.** -/
theorem primRankEval_val (l : PrimState) : primRankEval.val l = primEval.val l :=
  rank_prim_eq_val l

/-! ### The same for the arrays -/

theorem entries_eq_nil_iff {A : BM4.Arr 1} : entries A = [] ↔ A.len = 0 := by
  constructor
  · intro h
    have hL := entries_length A
    rw [h] at hL
    exact hL.symm
  · intro h
    rw [entries, h, List.range_zero, List.map_nil]

instance instIsWellFoundedBms : IsWellFounded (Googology.Notation.BMS.bms 1).State
    (Googology.Notation.BMS.bms 1).Rel :=
  ⟨bmsHom.toSim.wf prim_wf⟩

/-- **The rank of one-row BMS is the ordinal the matrix names.**  The reading
is a `StepHom` that does not renumber the brackets, so `StepHom.rank_map`
carries `rank_prim_eq_val` across. -/
theorem rank_bms_eq_val (A : (Googology.Notation.BMS.bms 1).State) :
    IsWellFounded.rank (Googology.Notation.BMS.bms 1).Rel A = bmsOrdEval.val A := by
  have h := bmsHom.rank_map (fun k => ⟨k, rfl⟩)
    (fun s => by
      show s.1.len = 0 ↔ entries s.1 = []
      exact entries_eq_nil_iff.symm) A
  rw [← h]
  exact rank_prim_eq_val (bmsHom.map A)

end Googology.Trans.BMS
