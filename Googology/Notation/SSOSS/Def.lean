import Mathlib.Data.List.Lex
import Mathlib.Logic.Function.Iterate
import Lean.Elab.Tactic.Omega

/-!
The literal rev 76153 definition. Positions are one-based; `cut` is the
number of entries retained. `fs S k` uses k copies, not k+1 copies.
All searches are finite and all definitions are executable.
-/

namespace Googology.Notation.SSOSS
namespace Seq

abbrev Sequence := List ℕ

/-- One-based entry; the value outside the sequence is irrelevant to valid searches. -/
def entry (S : Sequence) (i : ℕ) : ℕ := S[i - 1]?.getD 0

def suf (S : Sequence) (i : ℕ) : Sequence := S.drop (i - 1)

def sp (S : Sequence) (x : ℕ) : ℕ :=
  ((List.range x).filter fun i => 1 ≤ i ∧ suf S i < suf S x).foldl max 1

def p (S : Sequence) (i : ℕ) : ℕ := (sp S)^[i] S.length

def mbp (S : Sequence) (x : ℕ) : ℕ :=
  if h : S.length ≤ x then S.length
  else
    let m := mbp S (x + 1)
    if entry S x < entry S S.length ∧ suf S (m + 1) < suf S (x + 1)
      then x else m
termination_by S.length - x

def fbp (S : Sequence) (i : ℕ) : ℕ := mbp S (p S i)

def breakAt (S : Sequence) (i : ℕ) : Prop :=
  suf S (fbp S i + 1) ≤ suf S (fbp S (i - 1) + 1) ∨
  ∃ j ∈ List.range (fbp S i + 1), p S i < j ∧ entry S j ≤ entry S (p S i)

instance (S : Sequence) (i : ℕ) : Decidable (breakAt S i) := by
  unfold breakAt
  infer_instance

def br (S : Sequence) : ℕ :=
  ((List.range (S.length + 1)).find? fun i => 1 < i ∧ breakAt S i).getD S.length

def cut (S : Sequence) : ℕ := fbp S (br S)

/-- The right-to-left scan cannot leave the interval it scans. -/
theorem mbp_bounds (S : Sequence) (x : ℕ) :
    min x S.length ≤ mbp S x ∧ mbp S x ≤ S.length := by
  rw [mbp]
  split
  · omega
  · have ih := mbp_bounds S (x + 1)
    dsimp only
    split <;> omega
termination_by S.length - x

theorem cut_le_length (S : Sequence) : cut S ≤ S.length :=
  (mbp_bounds S (p S (br S))).2

def good (S : Sequence) : Sequence := S.take (cut S)

def bad (S : Sequence) : Sequence :=
  (S.dropLast.drop (cut S)) ++ [entry S S.length - 1]

/-- The sequence part of an expansion (also handles empty and successor cases). -/
def fs (S : Sequence) (k : ℕ) : Sequence :=
  if S.isEmpty then []
  else if entry S S.length = 0 then S.dropLast
  else good S ++ (List.replicate k (bad S)).flatten

/-- A terminal natural number, or a sequence with its new argument. -/
def step (S : Sequence) (n : ℕ) : ℕ ⊕ (Sequence × ℕ) :=
  if S.isEmpty then .inl n else .inr (fs S (n + 1), n + 1)

end Seq
end Googology.Notation.SSOSS
