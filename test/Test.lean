import Googology

/-!
# Demonstration

Three systems whose state types differ, one shared proposition, and the spine
that carries a translation all the way down to an order.

Nothing here is mathematics about the real systems: the expansion rules are
stubs.  The point is that the scaffolding type-checks.
-/

namespace Googology.Test

/-- Stand-in for a Bashicu matrix: a list of columns. -/
abbrev Matrix := List (List Nat)

/-- Stand-in for a Y sequence: a list of naturals. -/
abbrev Seq := List Nat

/-- A stub system on matrices. -/
def bms : Rewrite := ⟨Matrix, fun s _ => s.tail, fun s => s = []⟩

/-- Another rule on the *same* state type — impossible with a type class. -/
def bms33 : Rewrite := ⟨Matrix, fun s _ => s.tail, fun s => s = []⟩

/-- A stub system on sequences. -/
def yseq : Rewrite := ⟨Seq, fun s _ => s.tail, fun s => s = []⟩

-- One proposition, three systems, two state types.
example : Prop := bms.Terminates
example : Prop := bms33.Terminates
example : Prop := yseq.Terminates

/-- A system proves termination by supplying a measure; the general theorem
does the rest. -/
theorem yseq_terminates : yseq.Terminates := by
  refine yseq.terminates_of_measure (· < ·) Nat.lt_wfRel.wf List.length ?_
  rintro a b ⟨hne, k, rfl⟩
  cases a with
  | nil => exact absurd rfl hne
  | cons x xs => exact Nat.lt_succ_self _

/-- Generators absorb the differing initial states. -/
def yseqStd : yseq.Std where
  Standard := fun _ => True
  gen := fun n => List.replicate n 1
  gen_std := fun _ => trivial
  step_std := fun _ _ _ => trivial

example : yseqStd.Terminates := yseqStd.of_terminates yseq_terminates

/-- The spine: a translation plus an evaluation of the target gives
termination of the source, in one line. -/
example {Src Tgt : Rewrite} {O : Type} {ltO : O → O → Prop}
    (trans : Sim Src Tgt) (o : Eval Tgt ltO) (hO : WellFounded ltO) :
    Src.Terminates :=
  (Eval.ofSim trans o).terminates hO

end Googology.Test
