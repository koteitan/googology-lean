import Googology.Core
import Googology.Notation.OmegaY.Official

/-!
# The ω-Y sequence as an expansion system

`Official.lean` holds the official expansion, `OmegaY.Official.expand`: the rule
of `expand` in Naruyoko's program
[StudyAndExpandSequence](https://github.com/Naruyoko/StudyAndExpandSequence)
(revision `b26ba7e`, v1.1, default settings), written in
[koteitan/wy-wo-por](https://github.com/koteitan/wy-wo-por) from a description
of the rule. This file packages it as a `Rewrite`.

`OmegaY.Official.expand s n` is an `Except`: every step of the rule that cannot
be carried out is an explicit error. The program has no such errors, and none
occurs on the 474 expansions of `test/OmegaYCheck.lean`, but that no error
occurs on a standard form is not proved. Here an error gives the empty
sequence, which halts. Since `()` is itself a standard form (`(1)[n] = ()`),
this adds no state to the standard forms that the rule does not reach.

The standard forms are the sequences reachable from the seeds `(1, h+2)`, as
in `notes/03-official-rule.md` §6 of wy-wo-por. The expansion at `0` drops the
last entry, so every prefix of a standard form is standard too.

Termination is proved in `WellFounded.lean`, from the proof ported into
`WellOrder/`.
-/

namespace Googology.Notation.OmegaY

/-- **The official expansion `s[n]`**. An error of the rule gives `()`. -/
def expand (s : List Nat) (n : Nat) : List Nat :=
  match _root_.OmegaY.Official.expand s n with
  | .ok t => t
  | .error _ => []

/-- Where the rule succeeds, `expand` is its result. -/
theorem expand_eq_of_ok {s t : List Nat} {n : Nat}
    (h : _root_.OmegaY.Official.expand s n = .ok t) : expand s n = t := by
  simp only [expand, h]

/-- Where the rule fails, `expand` gives `()`. -/
theorem expand_eq_nil_of_error {s : List Nat} {n : Nat} {e : _root_.OmegaY.Official.Error}
    (h : _root_.OmegaY.Official.expand s n = .error e) : expand s n = [] := by
  simp only [expand, h]

/-- The sequences reachable from a seed `(1, h+2)`. -/
inductive OmegaYStd : List Nat → Prop
  | init (h : Nat) : OmegaYStd [1, h + 2]
  | step {s : List Nat} (n : Nat) : OmegaYStd s → OmegaYStd (expand s n)

/-- **The ω-Y sequence**, as an expansion system on its standard forms. -/
def omegaYSys : Rewrite where
  State := {s : List Nat // OmegaYStd s}
  step := fun s n => ⟨expand s.1 n, OmegaYStd.step n s.2⟩
  halted := fun s => s.1 = []

/-- The seeds. -/
def omegaYStd : omegaYSys.Std where
  Standard := fun _ => True
  gen := fun h => ⟨[1, h + 2], OmegaYStd.init h⟩
  gen_std := fun _ => trivial
  step_std := fun _ _ _ => trivial

/-- **The ω-Y sequence on every list of naturals**, standard or not. -/
def omegaYAll : Rewrite where
  State := List Nat
  step := expand
  halted := fun s => s = []

-- Small cases; the expected values are the official program's.
#guard expand [1, 1] 3 = [1]
#guard expand [1] 3 = []
#guard expand [1, 2] 2 = [1, 1, 1]
#guard expand [1, 4] 2 = [1, 3, 10]

end Googology.Notation.OmegaY
