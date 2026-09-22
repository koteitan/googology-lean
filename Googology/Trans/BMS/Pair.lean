import Googology.Trans.BMS.Entries2

/-!
# The pair sequence system

`BMS/Entries2.lean` writes two-row expansion on the entries and proves it is
`BM4.expand`.  This file packages it as a `Rewrite`, the way `BMS/Prim.lean`
packages one row.

A state is the entries of a standard two-row array.  The step is `expand2L`,
which is a function that runs — `BM4.expand` is `noncomputable`, so the array
form is not.  `pairL_terminates` is `Notation.BMS.bms_terminates 2` carried
across, and `pairStd` names the generators `(0,0)(1,1)⋯(n,n)`.

What is not here is an `Eval`.  One row has one because `read` says which
ordinal a matrix names; two rows would need a reading that uses `ψ` at every
finite subscript, and that is not written yet.
-/

namespace Googology.Trans.BMS

open BM4 Pat

/-- The state of the pair sequence system: the entries of a standard two-row
array. -/
def PairState : Type := {l : List (Nat × Nat) // ∃ A : Arr 2, Std 2 A ∧ entries2 A = l}

theorem pair_step_ok (l : PairState) (N : Nat) :
    ∃ A : Arr 2, Std 2 A ∧ entries2 A = expand2L N l.1 := by
  obtain ⟨A, hA, hl⟩ := l.2
  exact ⟨expand A N, Std.step N hA, by rw [entries2_expand, hl]⟩

/-- **The pair sequence system, on the entries.**  The step is a function that
runs, which `Notation.BMS.bms 2` is not. -/
def pairL : Rewrite where
  State := PairState
  step := fun l N => ⟨expand2L N l.1, pair_step_ok l N⟩
  halted := fun l => l.1 = []

@[simp] theorem pairL_step_val (l : PairState) (N : Nat) :
    ((pairL.step l N) : PairState).1 = expand2L N l.1 := rfl

@[simp] theorem pairL_halted_iff (l : PairState) : pairL.halted l ↔ l.1 = [] := Iff.rfl

/-- **The pair sequence system terminates.** -/
theorem pairL_terminates : pairL.Terminates := by
  intro f hf
  obtain ⟨A, hA, h0⟩ := (f 0).2
  exact expand2L_terminates A hA (fun n => (f n).1) h0.symm
    (fun n => by obtain ⟨k, hk⟩ := hf n; exact ⟨k, congrArg Subtype.val hk⟩)

theorem entries2_stair (n : Nat) :
    entries2 (stair 2 n) = (List.range (n + 1)).map (fun i => (i, i)) := by
  rw [entries2, show (stair 2 n).len = n + 1 from rfl]
  rfl

/-- The generators `(0,0)(1,1)⋯(n,n)`. -/
def pairStd : pairL.Std where
  Standard := fun _ => True
  gen := fun n => ⟨(List.range (n + 1)).map (fun i => (i, i)),
    ⟨stair 2 n, Std.init n, entries2_stair n⟩⟩
  gen_std := fun _ => trivial
  step_std := fun _ _ _ => trivial

/-- **From a generator, any expansion sequence ends.** -/
theorem pairStd_terminates : pairStd.Terminates :=
  pairStd.of_terminates pairL_terminates

/-- **The pair sequence system is well founded**, not merely terminating. -/
theorem pairL_wf : pairL.WF := Rewrite.wf_of_terminates pairL_terminates

end Googology.Trans.BMS
