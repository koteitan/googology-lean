import Googology.Trans.BMS.Agree
import Googology.Trans.BMS.Reach

/-!
# The general system at one row

`bmsL 0` is the system with one row, built from `expandRL` and the entries of
standard arrays.  `prim` is the primitive sequence system, built from
`expandL` and the matrices whose term is a standard form.  They are the same
system: `bmsEquivPrim`.

Two things make it so.  `expandRL_one` says the rules agree, and
`std_entries_iff` says the states do — a matrix is the entries of a standard
one-row array exactly when its term is a standard form.  The only bookkeeping
left is that a one-row column is a singleton, so the two shapes convert back
and forth.

So everything `Trans/BMS/Equiv.lean` proves about `prim` — that it is the
standard forms below `ψ_0(Ω)`, written another way — applies to `bmsL 0` as
well, and the general machinery has the one-row theory as a special case
rather than beside it.
-/

namespace Googology.Trans.BMS

open BM4 Pat
open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term

theorem map_head_map_single (l : List Nat) :
    (l.map (fun a => [a])).map (fun c => c.head!) = l := by
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.map_cons, List.map_cons, ih]; rfl

/-- A state of the general system at one row is a column of singletons. -/
theorem bmsState_zero_eq (l : BmsState 0) :
    l.1 = (l.1.map (fun c => c.head!)).map (fun a => [a]) := by
  obtain ⟨A, _, hA⟩ := l.2
  rw [← hA, entriesR_one, map_head_map_single]

theorem col_of_bmsState (l : BmsState 0) : Col 0 (l.1.map (fun c => c.head!)) := by
  obtain ⟨A, hA, hl⟩ := l.2
  rw [← hl, entriesR_one, map_head_map_single]
  exact (std_entries A hA).1

theorem OT_of_bmsState (l : BmsState 0) : OT (read 0 (l.1.map (fun c => c.head!))) := by
  obtain ⟨A, hA, hl⟩ := l.2
  rw [← hl, entriesR_one, map_head_map_single]
  exact (std_entries A hA).2

/-- One row of the general system, as a state of the primitive sequence
system. -/
def toPrim (l : BmsState 0) : PrimState :=
  ⟨l.1.map (fun c => c.head!), col_of_bmsState l, OT_of_bmsState l⟩

/-- And back. -/
def toBms (l : PrimState) : BmsState 0 :=
  ⟨l.1.map (fun a => [a]), by
    obtain ⟨A, hA, hl⟩ := exists_std_of_col l.2.1 l.2.2
    exact ⟨A, hA, by rw [entriesR_one, hl]⟩⟩

def primOfBmsHom : StepHom (bmsL 0) prim where
  map := toPrim
  reindex := id
  map_step := fun l N => by
    refine Subtype.ext ?_
    show (expandRL 1 N l.1).map (fun c => c.head!)
      = expandL N 0 (l.1.map (fun c => c.head!))
    conv_lhs => rw [bmsState_zero_eq l]
    rw [expandRL_one N _ (col_of_bmsState l), map_head_map_single]
  map_halted := fun l h => by
    show l.1 = []
    rw [bmsState_zero_eq l, show l.1.map (fun c => c.head!) = [] from h, List.map_nil]

def bmsOfPrimHom : StepHom prim (bmsL 0) where
  map := toBms
  reindex := id
  map_step := fun l N => by
    refine Subtype.ext ?_
    show (expandL N 0 l.1).map (fun a => [a]) = expandRL 1 N (l.1.map (fun a => [a]))
    exact (expandRL_one N l.1 l.2.1).symm
  map_halted := fun l h => by
    show l.1 = []
    have : l.1.map (fun a => [a]) = [] := h
    simpa using this

/-- **The general system at one row is the primitive sequence system.** -/
def bmsEquivPrim : Equiv (bmsL 0) prim where
  toFun := primOfBmsHom.toSim
  invFun := bmsOfPrimHom.toSim
  left_inv := fun l => Subtype.ext (bmsState_zero_eq l).symm
  right_inv := fun l => Subtype.ext (map_head_map_single l.1)

end Googology.Trans.BMS
