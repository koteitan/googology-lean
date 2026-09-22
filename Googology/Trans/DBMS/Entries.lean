import Googology.Trans.BMS.Agree
import Googology.Trans.DBMS.OneRow

/-!
# DBMS on the entries

DBMS expands exactly as BM4 does, so `Trans.BMS.expandRL` is its rule too and
`Trans.BMS.entriesR_expand` is the proof.  What differs is where the
expansion starts, and `entriesR_dstair` says what the generators look like on
the entries: column `i` holds `i - k` in row `k`.

`dbmsL r` is DBMS with `r + 1` rows on the entries, with `dbmsLStd` naming the
generators.  Its step runs, which the array form does not.

Termination: `dbmsL_zero_terminates` covers one row, by the translation in
`Trans/DBMS/OneRow.lean`.  For two rows and up it is not proved anywhere here
— the label-system proof this library imports is about arrays reachable from
a stair, and these generators are not stairs.
-/

namespace Googology.Trans.DBMS

open BM4
open Googology.Notation.DBMS
open Googology.Trans.BMS

/-- The DBMS generators, on the entries. -/
theorem entriesR_dstair (r n : Nat) :
    entriesR (dstair r n)
      = (List.range (n + 1)).map (fun i => (List.range r).map (fun k => i - k)) := by
  rw [entriesR, show (dstair r n).len = n + 1 from rfl]
  rfl

/-- The state of DBMS with `r + 1` rows: the entries of a standard array. -/
def DBmsState (r : Nat) : Type :=
  {l : List (List Nat) // ∃ A : Arr (r + 1), DStd (r + 1) A ∧ entriesR A = l}

theorem dbmsL_step_ok {r : Nat} (l : DBmsState r) (N : Nat) :
    ∃ A : Arr (r + 1), DStd (r + 1) A ∧ entriesR A = expandRL (r + 1) N l.1 := by
  obtain ⟨A, hA, hl⟩ := l.2
  exact ⟨expand A N, DStd.step N hA, by rw [entriesR_expand (Nat.succ_pos r), hl]⟩

/-- **DBMS with `r + 1` rows, on the entries.**  The rule is BM4's, so it is
the same `expandRL`; only the generators differ. -/
def dbmsL (r : Nat) : Rewrite where
  State := DBmsState r
  step := fun l N => ⟨expandRL (r + 1) N l.1, dbmsL_step_ok l N⟩
  halted := fun l => l.1 = []

/-- The generators, column `i` holding `i - k` in row `k`. -/
def dbmsLStd (r : Nat) : (dbmsL r).Std where
  Standard := fun _ => True
  gen := fun n => ⟨(List.range (n + 1)).map
      (fun i => (List.range (r + 1)).map (fun k => i - k)),
    ⟨dstair (r + 1) n, DStd.init n, entriesR_dstair (r + 1) n⟩⟩
  gen_std := fun _ => trivial
  step_std := fun _ _ _ => trivial

/-- **One row of DBMS, on the entries, terminates.**  For `r + 1 ≥ 2` rows
termination is not proved anywhere in this repository. -/
theorem dbmsL_zero_terminates : (dbmsL 0).Terminates := by
  intro f hf
  obtain ⟨A, hA, h0⟩ := (f 0).2
  choose k hk using hf
  let g : Nat → Arr 1 := fun n => Nat.rec A (fun m B => expand B (k m)) n
  have hgStd : ∀ n, DStd 1 (g n) := by
    intro n
    induction n with
    | zero => exact hA
    | succ m ih => exact DStd.step (k m) ih
  have hgf : ∀ n, entriesR (g n) = (f n).1 := by
    intro n
    induction n with
    | zero => exact h0
    | succ m ih =>
      show entriesR (expand (g m) (k m)) = (f (m + 1)).1
      rw [entriesR_expand Nat.zero_lt_one, ih]
      exact (congrArg Subtype.val (hk m)).symm
  obtain ⟨n, hn⟩ := dbms_one_terminates (fun n => ⟨g n, hgStd n⟩) (fun n => ⟨k n, rfl⟩)
  refine ⟨n, ?_⟩
  show (f n).1 = []
  rw [← hgf n, entriesR]
  have hl : (g n).len = 0 := hn
  rw [hl, List.range_zero, List.map_nil]

/-- **From a DBMS generator with one row, any expansion sequence ends.** -/
theorem dbmsLStd_zero_terminates : (dbmsLStd 0).Terminates :=
  (dbmsLStd 0).of_terminates dbmsL_zero_terminates

/-- **One row of DBMS is well founded.** -/
theorem dbmsL_zero_wf : (dbmsL 0).WF := Rewrite.wf_of_terminates dbmsL_zero_terminates

end Googology.Trans.DBMS
