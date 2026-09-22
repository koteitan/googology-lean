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

`rank_pairGen` is the first use of that licence.  Two rows have no reading,
but the generator `(0,0)(1,1)` expands into one-row matrices with a zero row
underneath, and `BMS/Embed.lean` carries their ordinals across unchanged, so
its rank comes out as `ε₀` — the pair sequence system starts where the
primitive sequence system ends.  That is also the value the correspondence
tables give `(0,0)(1,1)`.
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

/-! ### Two rows, at the generator

No reading of a two-row matrix is available, so the rank is the only ordinal
a two-row state carries.  At `(0,0)(1,1)` it can still be computed, because
that generator expands into one-row matrices with a zero row underneath, and
`BMS/Embed.lean` says those carry the one-row ordinals unchanged. -/

instance instIsWellFoundedPair : IsWellFounded pairL.State pairL.Rel := ⟨pairL_wf⟩

/-- Writing a zero row under a one-row matrix does not change its rank. -/
theorem rank_toPairS (l : PrimState) :
    IsWellFounded.rank pairL.Rel (toPairS l) = IsWellFounded.rank prim.Rel l :=
  primHomPair.rank_map (fun k => ⟨k, rfl⟩)
    (fun s => by
      show s.1 = [] ↔ withZero s.1 = []
      rw [withZero, List.map_eq_nil_iff]) l

/-- The one-row generator `(0)(1)⋯(n)`, as a state. -/
def primGen (n : Nat) : PrimState := ⟨List.range (n + 1), col_range n, OT_read_range n⟩

/-- The two-row generator `(0,0)(1,1)`, as a state. -/
def pairGen : PairState :=
  ⟨[(0, 0), (1, 1)], ⟨Pat.stair 2 1, Pat.Std.init 1, by rw [entries2_stair]; rfl⟩⟩

theorem step_pairGen (N : Nat) : pairL.step pairGen N = toPairS (primGen N) :=
  Subtype.ext (expand2L_gen N)

theorem rank_step_pairGen (N : Nat) :
    IsWellFounded.rank pairL.Rel (pairL.step pairGen N) = val (read 0 (List.range (N + 1))) := by
  rw [step_pairGen, rank_toPairS]
  exact rank_prim_eq_val (primGen N)

/-- **The pair sequence generator `(0,0)(1,1)` has rank `ε₀`.**  So the two-row
system starts where the one-row system ends, and the correspondence table's
`(0,0)(1,1) = ε₀` is a theorem here, not an assumption. -/
theorem rank_pairGen : IsWellFounded.rank pairL.Rel pairGen = Ord.eps0 := by
  have hnh : ¬ pairL.halted pairGen := by
    show ¬ ([(0, 0), (1, 1)] : List (Nat × Nat)) = []
    simp
  rw [IsWellFounded.rank_eq]
  refine le_antisymm ?_ ?_
  · refine Ordinal.iSup_le ?_
    rintro ⟨m, _, N, rfl⟩
    show Order.succ (IsWellFounded.rank pairL.Rel (pairL.step pairGen N)) ≤ Ord.eps0
    rw [rank_step_pairGen N]
    exact Order.succ_le_of_lt (val_read_lt_eps0 (OT_read_range N))
  · refine le_of_forall_lt (fun β hβ => ?_)
    obtain ⟨Y, hOTY, hAY, hvY⟩ := exists_OT_of_lt_eps0 hβ
    obtain ⟨m, hm⟩ := exists_lt_twr Y hAY
    cases m with
    | zero => exact absurd hm (by rw [twr]; exact not_lt_nil Y)
    | succ k =>
      have hrel : pairL.Rel (pairL.step pairGen k) pairGen := ⟨hnh, k, rfl⟩
      refine Ordinal.lt_iSup_iff.mpr ⟨⟨pairL.step pairGen k, hrel⟩, ?_⟩
      show β < Order.succ (IsWellFounded.rank pairL.Rel (pairL.step pairGen k))
      refine lt_of_le_of_lt ?_ (Order.lt_succ _)
      rw [rank_step_pairGen k, read_range_eq_twr k, ← hvY]
      exact (val_lt_val hOTY (by rw [← read_range_eq_twr k]; exact OT_read_range k) hm).le

end Googology.Trans.BMS
