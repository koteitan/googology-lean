import Googology.Trans.BMS.Bms
import Googology.Notation.DBMS

/-!
# One-row DBMS

With one row a DBMS generator is a BM4 generator: `(dstair 1 n).col i 0` is
`i - 0`, which is `i`.  Expansion is the same rule in both systems, so
everything `Trans/BMS/Bms.lean` proves about `Notation.BMS.bms 1` holds of
`Notation.DBMS.dbms 1`, by the same induction with `DStd` in place of `Std`.

So one-row DBMS names the same ordinals as one-row BMS — both through
`read ∘ entries` — and terminates.  With two rows or more the generators
differ and none of this applies.
-/

namespace Googology.Trans.DBMS

open BM4
open Googology.Notation.DBMS
open Googology.Trans.BMS
open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term

/-- With one row the DBMS generator is `(0)(1)⋯(n)`, as in BM4. -/
theorem entries_dstair (n : Nat) : entries (dstair 1 n) = List.range (n + 1) := by
  rw [entries, dstair_len]
  exact List.map_id _

/-- **Every standard one-row DBMS matrix is a matrix whose term is a standard
form.** -/
theorem dstd_entries : ∀ A : Arr 1, DStd 1 A →
    Col 0 (entries A) ∧ OT (read 0 (entries A)) := by
  intro A h
  induction h with
  | init n => rw [entries_dstair]; exact ⟨col_range n, OT_read_range n⟩
  | step N _ ih =>
    rw [entries_expand' _ N ih.1]
    exact prim_step_ok ⟨_, ih⟩ N

/-- A standard one-row DBMS matrix, as a state of the primitive sequence
system. -/
def toEntries (A : (dbms 1).State) : PrimState := ⟨entries A.1, dstd_entries A.1 A.2⟩

/-- **Reading the entries is a translation** from one-row DBMS to the
primitive sequence system. -/
def dbmsHom : StepHom (dbms 1) prim where
  map := toEntries
  reindex := id
  map_step := fun A N => Subtype.ext (entries_expand' A.1 N (dstd_entries A.1 A.2).1)
  map_halted := fun A h => by
    have hL := entries_length A.1
    rw [show entries A.1 = [] from h] at hL
    exact hL.symm

/-- **A one-row DBMS matrix names a countable ordinal**, and expansion lowers
it. -/
noncomputable def dbmsOrdEval :
    Eval (dbms 1) (· < · : Ordinal.{0} → Ordinal.{0} → Prop) :=
  Eval.ofSim dbmsHom.toSim primEval

theorem dbmsOrdEval_val (A : (dbms 1).State) :
    dbmsOrdEval.val A = (read 0 (entries A.1)).val := rfl

/-- **One-row DBMS terminates.** -/
theorem dbms_one_terminates : (dbms 1).Terminates :=
  dbmsHom.toSim.terminates (primHom.toSim.wf exbOT_wf)

end Googology.Trans.DBMS
