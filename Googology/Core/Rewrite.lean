/-!
# Expansion systems

A googological system (a sequence system, a matrix system) is packaged as a
single structure whose *first field is the state type itself*.  Because the
state type is a field, systems with different state types (matrices, lists of
naturals) all inhabit one type, so a single proposition `Terminates` speaks
about all of them.

This is deliberately a `structure` and not a `class`.  One state type carries
several expansion rules — BMS has BM4, 3.3, 2, 1.1 — and a class keyed on the
state type could only hold one of them.
-/

namespace Googology

/-- An expansion system. -/
structure Rewrite where
  /-- The type of states.  Differs from system to system. -/
  State : Type
  /-- One expansion step.  The second argument is the bracket number. -/
  step : State → Nat → State
  /-- The halting states. -/
  halted : State → Prop

namespace Rewrite

variable (R : Rewrite)

/-- One-step relation: `R.Rel b a` says `b` is obtained from `a` in one step. -/
def Rel (b a : R.State) : Prop := ¬ R.halted a ∧ ∃ k, b = R.step a k

/-- Well-foundedness of the one-step relation. -/
def WF : Prop := WellFounded R.Rel

/-- Termination: every expansion chain reaches a halting state in finitely
many steps. -/
def Terminates : Prop :=
  ∀ f : Nat → R.State, (∀ n, ∃ k, f (n + 1) = R.step (f n) k) → ∃ n, R.halted (f n)

/-- A well-founded system admits no infinite descending chain. -/
theorem no_infinite_chain (h : R.WF) (f : Nat → R.State)
    (hf : ∀ n, R.Rel (f (n + 1)) (f n)) : False := by
  have key : ∀ a, Acc R.Rel a → ∀ n, f n ≠ a := by
    intro a ha
    induction ha with
    | intro x _ ih => intro n hn; exact ih (f (n + 1)) (hn ▸ hf n) (n + 1) rfl
  exact key (f 0) (h.apply (f 0)) 0 rfl

/-- Well-foundedness implies termination. -/
theorem terminates_of_wf (h : R.WF) : R.Terminates := by
  intro f hf
  apply Classical.byContradiction
  intro hc
  have hall : ∀ n, ¬ R.halted (f n) := fun n hn => hc ⟨n, hn⟩
  exact R.no_infinite_chain h f (fun n => ⟨hall n, hf n⟩)

/-- A measure implies well-foundedness.  `W` may be any type carrying a
well-founded relation: `Nat`, an ordinal, or a term system of your own. -/
theorem wf_of_measure {W : Type v} (lt : W → W → Prop) (hw : WellFounded lt)
    (m : R.State → W) (hm : ∀ a b, R.Rel b a → lt (m b) (m a)) : R.WF :=
  Subrelation.wf (fun {b a} hba => hm a b hba) (InvImage.wf m hw)

/-- A measure implies termination. -/
theorem terminates_of_measure {W : Type v} (lt : W → W → Prop) (hw : WellFounded lt)
    (m : R.State → W) (hm : ∀ a b, R.Rel b a → lt (m b) (m a)) : R.Terminates :=
  R.terminates_of_wf (R.wf_of_measure lt hw m hm)

end Rewrite
end Googology
