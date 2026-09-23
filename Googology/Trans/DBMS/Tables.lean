import Googology.Trans.DBMS.OneRow
import Googology.Trans.BMS.Tables

/-!
# Cells of the translation tables: one-row DBMS

**Injective, on the matrices.**  A state of `dbms 1` is an array `Arr 1`, and
an array has a total column map: it holds values outside the matrix too.  Two
standard arrays can be the same matrix and differ only there.
`dstair 1 0` and `(dstair 1 1)[0]` are both the matrix `(0)`, and they differ
at column `1`.  So neither `dbmsOrdEval.val` nor `dbmsHom.map` is one to one on
the arrays: `dbmsOrdEval_not_injective`, `dbmsHom_not_injective`.

What is one to one is the matrix itself, its list of entries.  Two states have
the same ordinal exactly when they have the same entries
(`dbmsOrdEval_eq_iff`), and the same holds for `dbmsHom`
(`dbmsHom_map_eq_iff`).  This is the same form as `bmsOrdEval_inj` for BMS.

**Preserves the rank.**  `dbmsHom` keeps the bracket numbers and halts exactly
where the source halts, so `StepHom.rank_map` applies: `rank_dbmsHom`.

**Order-preserving.**  With the dictionary order on the entries,
`dbmsOrdEval_lt_iff` follows from `primEval_lt_iff`.
-/

namespace Googology.Trans.DBMS

open BM4
open Googology.Notation.DBMS
open Googology.Trans.BMS
open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term

/-! ### Injective, on the matrices -/

/-- **Two one-row DBMS states name the same ordinal exactly when they are the
same matrix.** -/
theorem dbmsOrdEval_eq_iff (A B : (dbms 1).State) :
    dbmsOrdEval.val A = dbmsOrdEval.val B ↔ entries A.1 = entries B.1 := by
  constructor
  · intro h
    have hA := dstd_entries A.1 A.2
    have hB := dstd_entries B.1 B.2
    exact read_inj hA.1 hB.1 (val_inj_of_OT hA.2 hB.2 h)
  · intro h
    rw [dbmsOrdEval_val, dbmsOrdEval_val, h]

/-- **One-row DBMS → primitive sequences is one to one on the matrices.** -/
theorem dbmsHom_map_eq_iff (A B : (dbms 1).State) :
    dbmsHom.map A = dbmsHom.map B ↔ entries A.1 = entries B.1 :=
  Subtype.ext_iff

/-- The generator `(0)`. -/
def stA : (dbms 1).State := ⟨dstair 1 0, DStd.init 0⟩

/-- `(0)(1)[0]`, which is also the matrix `(0)`. -/
noncomputable def stB : (dbms 1).State := ⟨expand (dstair 1 1) 0, DStd.step 0 (DStd.init 1)⟩

theorem parent_dstair_one : parent (dstair 1 1) 0 0 ((dstair 1 1).len - 1) := by
  refine parent_one.mpr ⟨by simp, by simp, fun j' h1 h2 => by simp at h2; omega, by simp⟩

theorem stB_len : stB.1.len = 1 := by
  show (expand (dstair 1 1) 0).len = 1
  rw [expand_one_len parent_dstair_one]
  simp

theorem stB_col (i k : Nat) : stB.1.col i k = 0 - k := by
  show (expand (dstair 1 1) 0).col i k = 0 - k
  rw [expand_one_col parent_dstair_one]
  simp [Nat.mod_one]

theorem entries_stA_stB : entries stA.1 = entries stB.1 := by
  rw [entries, entries, stB_len]
  show (List.range 1).map (fun i => (dstair 1 0).col i 0) = (List.range 1).map _
  simp [stB_col]

theorem stA_ne_stB : stA ≠ stB := by
  intro h
  have h1 := congrArg (fun s : (dbms 1).State => s.1.col 1 0) h
  simp only [stA, dstair_col] at h1
  rw [stB_col] at h1
  omega

/-- **`dbmsOrdEval` is not one to one on the arrays**: two standard arrays can
be one matrix. -/
theorem dbmsOrdEval_not_injective : ¬ Function.Injective dbmsOrdEval.val :=
  fun h => stA_ne_stB (h ((dbmsOrdEval_eq_iff stA stB).mpr entries_stA_stB))

/-- **Nor is `dbmsHom.map`**, for the same reason. -/
theorem dbmsHom_not_injective : ¬ Function.Injective dbmsHom.map :=
  fun h => stA_ne_stB (h ((dbmsHom_map_eq_iff stA stB).mpr entries_stA_stB))

/-! ### Preserves the rank -/

/-- **One-row DBMS → primitive sequences preserves the rank.** -/
theorem rank_dbmsHom (A : (dbms 1).State) :
    IsWellFounded.rank prim.Rel (dbmsHom.map A) = IsWellFounded.rank (dbms 1).Rel A :=
  dbmsHom.rank_map (fun k => ⟨k, rfl⟩)
    (fun s => by
      show s.1.len = 0 ↔ entries s.1 = []
      exact entries_eq_nil_iff.symm) A

/-! ### Order-preserving -/

/-- **One-row DBMS → ordinals is order-preserving**, for the dictionary order
on the entries. -/
theorem dbmsOrdEval_lt_iff (A B : (dbms 1).State) :
    entries A.1 < entries B.1 ↔ dbmsOrdEval.val A < dbmsOrdEval.val B :=
  primEval_lt_iff (dbmsHom.map A) (dbmsHom.map B)

end Googology.Trans.DBMS
