import Googology.Trans.BMS.Commute

/-!
# The primitive sequence system

The three files before this one give the reading of a one-row matrix, the rule
`BM4.expand` follows on one row, and the commutation between them.  This file
puts them together as a `Rewrite`.

A state is a one-row matrix — a list that starts at `0`, never goes below it
and never rises by more than one — whose term is a standard form.  A step is
`expandL`, and `primHom` is the `StepHom` into `exbOT`, the extended Buchholz
system: the reading commutes with expansion, and the brackets are renumbered
`N ↦ N + 1` because `A[N]` writes `N + 1` copies while `ψ_0(Z+1)[n]` writes `n`.

Two things follow with no further work.  `prim_terminates` — every expansion
sequence ends — because `exbOT` terminates.  And `primEval` — each matrix
names a countable ordinal, and expansion lowers it.

The term stays standard by itself: the commutation turns that question into
`OTFS_thm`, which is already proved.

What ties this to `Notation.BMS.bms 1` is still missing: `expandL` is the rule
written on the entries, and `BMS/OneRow.lean` shows `BM4.expand` follows the
same rule on `BM4.Arr 1`, but the bookkeeping between an array's indices and a
list's is not done.
-/

namespace Googology.Trans.BMS

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term

/-- Expansion keeps a matrix a matrix. -/
theorem col_expandL (N : Nat) : ∀ (l : List Nat) (b : Nat), Col b l →
    Col b (expandL N b l) := by
  intro l
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
    cases l with
    | nil => intro b _; rw [expandL_nil]; exact trivial
    | cons a rest =>
      intro b hc
      obtain ⟨ha, hch⟩ := hc
      subst ha
      have hcolhi : Col (a + 1) (rest.takeWhile (fun x => decide (a < x))) :=
        col_takeWhile rest a a (Nat.le_refl _) hch
      have hcollo : Col a (rest.dropWhile (fun x => decide (a < x))) :=
        col_dropWhile rest a a hch
      have hhilen : (rest.takeWhile (fun x => decide (a < x))).length < n := by
        subst hn; simp only [List.length_cons]
        exact Nat.lt_succ_of_le (List.takeWhile_sublist _).length_le
      have hlolen : (rest.dropWhile (fun x => decide (a < x))).length < n := by
        subst hn; simp only [List.length_cons]
        exact Nat.lt_succ_of_le (List.dropWhile_sublist _).length_le
      rw [expandL_cons]
      split
      · split
        · exact trivial
        · split
          · exact col_flatten _ _ a
              ⟨rfl, chain_of_col (col_dropLast _ _ hcolhi) (by omega) (by omega)⟩
          · exact ⟨rfl, chain_of_col (ih _ hhilen _ rfl _ hcolhi) (by omega) (by omega)⟩
      · refine ⟨rfl, chain_append _ a a
          (chain_of_col hcolhi (by omega) (by omega)) (Nat.le_refl a) _ ?_⟩
        exact ih _ hlolen _ rfl _ hcollo

theorem read_eq_nil : ∀ (l : List Nat) (b : Nat), read b l = nil → l = [] := by
  intro l b h
  cases l with
  | nil => rfl
  | cons a rest => exact absurd h (read_ne_nil b a rest)

/-- The state of the primitive sequence system: a one-row matrix whose term is
a standard form. -/
def PrimState : Type := {l : List Nat // Col 0 l ∧ OT (read 0 l)}

theorem prim_step_ok (l : PrimState) (N : Nat) :
    Col 0 (expandL N 0 l.1) ∧ OT (read 0 (expandL N 0 l.1)) := by
  refine ⟨col_expandL N l.1 0 l.2.1, ?_⟩
  rw [read_expandL N l.1 0 l.2.1]
  exact (Term.step_ok l.2.2 (read_lt_tW 0 l.1) (N + 1)).1

/-- **The primitive sequence system**, on the entries of a one-row matrix. -/
def prim : Rewrite where
  State := PrimState
  step := fun l N => ⟨expandL N 0 l.1, prim_step_ok l N⟩
  halted := fun l => l.1 = []

/-- Matrices with a standard term exist: `(0)` is one. -/
example : PrimState := ⟨[0], ⟨rfl, trivial⟩, by rw [read_singleton]; decide⟩

/-- The reading, as a map of states. -/
def toTerm (l : PrimState) : exbOT.State := ⟨read 0 l.1, l.2.2, read_lt_tW 0 l.1⟩

/-- **The reading is a translation**: it turns one expansion into one step of
the extended Buchholz system, with the brackets renumbered `N ↦ N + 1`. -/
def primHom : StepHom prim exbOT where
  map := toTerm
  reindex := fun N => N + 1
  map_step := fun l N => Subtype.ext (read_expandL N l.1 0 l.2.1)
  map_halted := fun l h => read_eq_nil l.1 0 h

/-- **The primitive sequence system terminates**, because the extended
Buchholz system does. -/
theorem prim_terminates : prim.Terminates :=
  (primHom.toSim).terminates exbOT_wf

/-- **A one-row matrix names an ordinal**, and it goes down at every
expansion. -/
noncomputable def primEval : Eval prim (· < · : Ordinal.{0} → Ordinal.{0} → Prop) :=
  Eval.ofSim primHom.toSim exbOTEval

end Googology.Trans.BMS
