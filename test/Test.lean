import Googology

/-!
# Scaffolding demonstration

**Nothing here is a real system.** The state types and the rules below are
invented for this file and carry no mathematical content: `dropHead` removes
the first element of a list, `dropLast` removes the last. They exist only to
show that the scaffolding type-checks.

Real systems live in `Googology/Notation/`, under their own names.

What is demonstrated:

* two state types, one proposition;
* two different rules on the *same* state type, which a type class could not
  hold;
* a measure discharging termination through the shared theorem;
* generators absorbing a choice of initial states;
* the translation-plus-evaluation spine.
-/

namespace Googology.Demo

/-- An invented state type: a list of lists of naturals. -/
abbrev Nested := List (List Nat)

/-- An invented state type: a list of naturals. -/
abbrev Flat := List Nat

/-- An invented rule: drop the first element. -/
def dropHead : Rewrite := ⟨Nested, fun s _ => s.tail, fun s => s = []⟩

/-- Another invented rule on the *same* state type: drop the last element.
Two `Rewrite` values on one type is what a type class could not express. -/
def dropLast : Rewrite := ⟨Nested, fun s _ => s.dropLast, fun s => s = []⟩

/-- An invented rule on the other state type. -/
def shrink : Rewrite := ⟨Flat, fun s _ => s.tail, fun s => s = []⟩

-- One proposition, three systems, two state types.
example : Prop := dropHead.Terminates
example : Prop := dropLast.Terminates
example : Prop := shrink.Terminates

/-- A system discharges termination by supplying a measure; the shared theorem
does the rest. -/
theorem shrink_terminates : shrink.Terminates := by
  refine shrink.terminates_of_measure (· < ·) Nat.lt_wfRel.wf List.length ?_
  rintro a b ⟨hne, k, rfl⟩
  cases a with
  | nil => exact absurd rfl hne
  | cons x xs => exact Nat.lt_succ_self _

/-- Generators absorb a choice of initial states. -/
def shrinkStd : shrink.Std where
  Standard := fun _ => True
  gen := fun n => List.replicate n 1
  gen_std := fun _ => trivial
  step_std := fun _ _ _ => trivial

example : shrinkStd.Terminates := shrinkStd.of_terminates shrink_terminates

/-- The spine: a translation plus an evaluation of the target gives
termination of the source, in one line. -/
example {Src Tgt : Rewrite} {O : Type} {ltO : O → O → Prop}
    (trans : Sim Src Tgt) (o : Eval Tgt ltO) (hO : WellFounded ltO) :
    Src.Terminates :=
  (Eval.ofSim trans o).terminates hO

end Googology.Demo
