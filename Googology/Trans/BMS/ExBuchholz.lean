import Googology.Notation.BMS
import Googology.Notation.ExBuchholz

/-!
# Bashicu matrices and extended Buchholz's ψ

What a translation between the two would buy is the **value**: which ordinal a
matrix names.  That is the ordinal analysis of BM4, and it is settled only for
few rows — one row is the primitive sequence system and lands below `ε₀`, two
rows land below the Bachmann–Howard ordinal, and three rows on are open.  So
the reachable target is one row.

This file has the map for that case.  `read` sends a one-row matrix, read as a
list of entries, to an extended Buchholz term: split the list at the entries
that are not above the current level, and send a block `a :: hi` to
`ψ_0(read (b+1) hi)`, which is `ω` to that power.  What is proved here is that the
reading is countable, that its subscripts are all `0`, and that a term of that
shape is below `ψ_0` of itself — which is what the standard-form condition
needs once the descending condition is in hand.

Two things are left before this becomes a `Sim`: that the reading of a
*standard* matrix is a standard form, and that it commutes with expansion.
The second is where the work is — `BM4.expand` is stated through
`Classical.choice`, so matching it against `fs` step for step is not a
rewriting exercise.
-/

namespace Googology.Trans.BMS

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term

/-- The primitive-sequence reading.  A one-row Bashicu matrix is a list of
entries; `read b s` reads `s` as an ordinal notation relative to the level
`b`, by splitting `s` at its entries that are not above `b`.  A block
`a :: hi`, with `hi` the entries above `b` that follow `a`, becomes
`ψ_0(read (b+1) hi)`, which is `ω` to that power. -/
def read (b : Nat) : List Nat → Term
  | [] => nil
  | _ :: rest =>
      cons nil (read (b + 1) (rest.takeWhile (fun a => decide (b < a))))
        (read b (rest.dropWhile (fun a => decide (b < a))))
  termination_by s => s.length
  decreasing_by
    all_goals simp only [List.length_cons]
    · exact Nat.lt_succ_of_le (List.takeWhile_sublist _).length_le
    · exact Nat.lt_succ_of_le (List.dropWhile_sublist _).length_le

@[simp] theorem read_nil (b : Nat) : read b [] = nil := by rw [read]

theorem read_cons (b : Nat) (a : Nat) (rest : List Nat) :
    read b (a :: rest)
      = cons nil (read (b + 1) (rest.takeWhile (fun x => decide (b < x))))
          (read b (rest.dropWhile (fun x => decide (b < x)))) := by
  rw [read]

/-- Everything the reading produces is countable: its subscripts are all
`0`. -/
theorem read_lt_tW (b : Nat) (s : List Nat) : read b s < tW := by
  cases s with
  | nil => rw [read_nil]; exact nil_lt_cons _ _ _
  | cons a rest =>
    rw [read_cons]
    exact cons_lt_cons_iff.mpr
      (Or.inl (psi_lt_psi_iff.mpr (Or.inl (nil_lt_cons _ _ _))))

/-- The reading of a nonempty list is a nonempty term. -/
theorem read_ne_nil (b : Nat) (a : Nat) (rest : List Nat) :
    read b (a :: rest) ≠ nil := by
  rw [read_cons]; exact fun h => Term.noConfusion h

/-- Every subscript in the term is `0`.  The reading of a one-row matrix has
this shape, because `ψ_0` is the only collapse it uses. -/
def AllNil : Term → Prop
  | nil => True
  | cons a b t => a = nil ∧ AllNil b ∧ AllNil t

theorem allNil_read : ∀ (b : Nat) (s : List Nat), AllNil (read b s) := by
  intro b s
  induction hn : s.length using Nat.strong_induction_on generalizing b s with
  | _ n ih =>
    cases s with
    | nil => rw [read_nil]; exact trivial
    | cons a rest =>
      rw [read_cons]
      refine ⟨rfl, ?_, ?_⟩
      · exact ih (rest.takeWhile (fun x => decide (b < x))).length
          (by subst hn; simp only [List.length_cons]
              exact Nat.lt_succ_of_le (List.takeWhile_sublist _).length_le) _ _ rfl
      · exact ih (rest.dropWhile (fun x => decide (b < x))).length
          (by subst hn; simp only [List.length_cons]
              exact Nat.lt_succ_of_le (List.dropWhile_sublist _).length_le) _ _ rfl

/-- A term whose subscripts are all `0` is below `ψ_0` of itself. -/
theorem lt_psi_self : ∀ X : Term, AllNil X → ∀ Y : Term, X < cons nil X Y := by
  intro X
  induction X with
  | nil => intro _ Y; exact nil_lt_cons _ _ _
  | cons a b t _ ihb _ =>
    intro h Y
    obtain ⟨ha, hb, _⟩ := h
    subst ha
    refine cons_lt_cons_iff.mpr (Or.inl (psi_lt_psi_iff.mpr (Or.inr ⟨rfl, ?_⟩)))
    exact ihb hb t

end Googology.Trans.BMS
