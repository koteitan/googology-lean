import Googology.Core
import Googology.Notation.Y.Yukito

/-!
# The Y sequence as an expansion system

`Yukito.lean` transcribes the official expansion, `expand` of `script.js`,
with explicit fuel.  This file fixes the fuel and packages the result as a
`Rewrite`.

The fuel is the one under which the transcription is known to compute the
expansion: in
[koteitan/1y-expand-equiv](https://github.com/koteitan/1y-expand-equiv), the
theorem `expand_eq` shows that `expandJS N (m + 1) efuel (calcMountain s (m + 1))`
equals an independently defined expansion as soon as `m` is at least the
largest entry and the length, and `efuel` at least the largest entry.  `bound`
is that largest entry, and `expand` takes `m = bound s + length s` and
`efuel = bound s`.

The standard forms are the sequences reachable from the seeds `(1, h+1)`.

Termination is proved in `WellFounded.lean`, from the ported proof in
`WellOrder/`.
-/

namespace Googology.Notation.Y

/-- The largest entry, and at least `1`. -/
def bound (s : List Nat) : Nat := max 1 (s.foldr max 0)

/-- **The official expansion `s[n]`**, with enough fuel. -/
def expand (s : List Nat) (n : Nat) : List Nat :=
  expandOut (expandJS n (bound s + s.length + 1) (bound s)
    (calcMountain s (bound s + s.length + 1)))

/-- The sequences reachable from a seed `(1, h+1)`. -/
inductive YStd : List Nat → Prop
  | init (h : Nat) : YStd [1, h + 1]
  | step {s : List Nat} (n : Nat) : YStd s → YStd (expand s n)

/-- **The Y sequence**, as an expansion system on its standard forms. -/
def ySys : Rewrite where
  State := {s : List Nat // YStd s}
  step := fun s n => ⟨expand s.1 n, YStd.step n s.2⟩
  halted := fun s => s.1 = []

/-- The seeds. -/
def yStd : ySys.Std where
  Standard := fun _ => True
  gen := fun h => ⟨[1, h + 1], YStd.init h⟩
  gen_std := fun _ => trivial
  step_std := fun _ _ _ => trivial

-- The seeds run down to the empty sequence.
#guard expand [1, 1] 3 = [1]
#guard expand [1] 3 = []
#guard expand [1, 2] 2 = [1, 1, 1]
#guard expand [1, 3] 3 = [1, 2, 4, 8]

end Googology.Notation.Y
