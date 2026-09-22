import Googology.Trans.BMS.Zero
import Googology.Trans.BMS.Reach
import Googology.Trans.BMS.Pair

/-!
# One row inside two

`BMS/Zero.lean` says a row of zeros underneath changes the rule not at all.
That is about the rule; this file is about the systems, and the missing piece
was whether a standard one-row matrix stays standard with the zero row added.

It does, and the reason is `expand2L_gen`: the two-row generator `(0,0)(1,1)`
expands at `N` to `(0,0)(1,0)⋯(N,0)`, which is the one-row generator with the
zero row already underneath.  Everything after that is the same rule on both
sides, so `exists_std2_withZero` is an induction over reachability with no
content of its own.

`primHomPair` is what comes out: a `StepHom` from `prim` into `pairL`, with
the brackets unchanged.  **The primitive sequence system sits inside the pair
sequence system**, not merely resembles it.
-/

namespace Googology.Trans.BMS

open BM4 Pat
open Googology.Notation.ExBuchholz.Term

theorem parAt1_gen : parAt1 [(0, 0), (1, 1)] 1 = some 0 := by
  rw [parAt1_eq_some]
  refine ⟨by omega, ?_, by decide, fun j' a b _ => by omega⟩
  exact Relation.TransGen.single ⟨by omega, by decide, fun j' a b => by omega⟩

theorem badRootL_gen : badRootL [(0, 0), (1, 1)] = some (0, true) := by
  rw [badRootL, if_neg (by decide),
    show ([(0, 0), (1, 1)] : List (Nat × Nat)).length - 1 = 1 from rfl, parAt1_gen]

/-- The two-row generator `(0,0)(1,1)`, expanded, is the one-row generator
with a row of zeros underneath. -/
theorem expand2L_gen (N : Nat) :
    expand2L N [(0, 0), (1, 1)] = withZero (List.range (N + 1)) := by
  rw [expand2L, badRootL_gen]
  dsimp only
  rw [show ([(0, 0), (1, 1)] : List (Nat × Nat)).length - 1 - 0 = 1 from rfl,
    List.range_zero, List.map_nil, List.nil_append, Nat.mul_one]
  refine List.map_congr_left (fun t _ => ?_)
  show (if true && ((0 == 0 + t % 1) || _) then _ else _) = _
  rw [show t % 1 = 0 from Nat.mod_one t, if_pos (by decide)]
  show ((0 : Nat) + t / 1 * (1 - 0), (0 : Nat)) = (t, 0)
  rw [Nat.div_one, show (1 : Nat) - 0 = 1 from rfl, Nat.mul_one, Nat.zero_add]

/-- **A standard one-row array, with a row of zeros underneath, is the entries
of a standard two-row array.**  The two-row generator `(0,0)(1,1)` expands to
the one-row generators, and every step after that is the same rule. -/
theorem exists_std2_withZero : ∀ A1 : Arr 1, Std 1 A1 →
    ∃ A2 : Arr 2, Std 2 A2 ∧ entries2 A2 = withZero (entries A1) := by
  intro A1 h
  induction h with
  | init n =>
    refine ⟨expand (stair 2 1) n, Std.step n (Std.init 1), ?_⟩
    rw [entries2_expand,
      show entries2 (stair 2 1) = [(0, 0), (1, 1)] from by rw [entries2_stair]; rfl,
      expand2L_gen, entries_stair]
  | @step A N hA ih =>
    obtain ⟨A2, hA2, hE⟩ := ih
    refine ⟨expand A2 N, Std.step N hA2, ?_⟩
    rw [entries2_expand, hE, expand2L_withZero N _ (std_entries A hA).1,
      entries_expand' A N (std_entries A hA).1]

/-- **Every matrix whose term is a standard form is one with a row of zeros
underneath.** -/
theorem withZero_std {l : List Nat} (hc : Col 0 l) (hOT : OT (read 0 l)) :
    ∃ A2 : Arr 2, Std 2 A2 ∧ entries2 A2 = withZero l := by
  obtain ⟨A, hA, hl⟩ := exists_std_of_col hc hOT
  obtain ⟨A2, hA2, hE⟩ := exists_std2_withZero A hA
  exact ⟨A2, hA2, by rw [hE, hl]⟩

/-- A state of the primitive sequence system, as a state of the pair sequence
system. -/
def toPairS (l : PrimState) : PairState := ⟨withZero l.1, withZero_std l.2.1 l.2.2⟩

/-- **The primitive sequence system sits inside the pair sequence system**, by
writing a row of zeros underneath.  The brackets are not renumbered. -/
def primHomPair : StepHom prim pairL where
  map := toPairS
  reindex := id
  map_step := fun l N => Subtype.ext (expand2L_withZero N l.1 l.2.1).symm
  map_halted := fun l h => by
    have hh : withZero l.1 = [] := h
    simpa [withZero] using hh


end Googology.Trans.BMS
