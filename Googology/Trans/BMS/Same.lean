import Googology.Trans.BMS.Agree
import Googology.Trans.BMS.Reach
import Googology.Trans.BMS.Pair
import Googology.Trans.BMS.Embed

/-!
# The general system at one and two rows

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

`pairEquivBms` is the same at two rows, and easier: there the states are the
entries of standard two-row arrays on both sides, so nothing has to be said
about which matrices those are.

`bmsL_zero_sim_one` puts the picture together: composing this file's two
equivalences with `BMS/Embed.lean`'s `primHomPair` gives `bmsL 0` inside
`bmsL 1`, which is the first step of the hierarchy.  The step from `r` to
`r + 1` in general is `BMS/ZeroRow.lean`'s `bmsL_homSucc`, proved on the
entries rather than through one and two rows.

`prim_wf` and `bmsL_zero_wf` close the `Rewrite` API at one row: the relation
is well founded, not merely terminating, so `Rewrite.rankEval` applies and
`primRankEval` is the rank of expansion itself.  Two rows and up get the same
from `Rewrite.wf_of_terminates`, which is in `Googology/Rank.lean`: a
descending chain never halts, so a system that terminates cannot have one.
No map of states is needed, which is what blocked carrying well-foundedness
back from `Notation.BMS.bms r` directly.
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

/-! ### Two rows -/

theorem map_pair_map_two (l : List (Nat × Nat)) :
    (l.map (fun x => [x.1, x.2])).map (fun c => (c.head!, c.tail.head!)) = l := by
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.map_cons, List.map_cons, ih]; rfl

theorem bmsState_one_eq (l : BmsState 1) :
    l.1 = (l.1.map (fun c => (c.head!, c.tail.head!))).map (fun x => [x.1, x.2]) := by
  obtain ⟨A, _, hA⟩ := l.2
  rw [← hA, entriesR_two, map_pair_map_two]

/-- Two rows of the general system, as a state of the pair sequence system. -/
def toPair (l : BmsState 1) : PairState :=
  ⟨l.1.map (fun c => (c.head!, c.tail.head!)), by
    obtain ⟨A, hA, hl⟩ := l.2
    exact ⟨A, hA, by rw [← hl, entriesR_two, map_pair_map_two]⟩⟩

/-- And back. -/
def toBms2 (l : PairState) : BmsState 1 :=
  ⟨l.1.map (fun x => [x.1, x.2]), by
    obtain ⟨A, hA, hl⟩ := l.2
    exact ⟨A, hA, by rw [entriesR_two, hl]⟩⟩

def pairOfBmsHom : StepHom (bmsL 1) pairL where
  map := toPair
  reindex := id
  map_step := fun l N => by
    refine Subtype.ext ?_
    show (expandRL 2 N l.1).map (fun c => (c.head!, c.tail.head!))
      = expand2L N (l.1.map (fun c => (c.head!, c.tail.head!)))
    conv_lhs => rw [bmsState_one_eq l]
    rw [expandRL_two N _, map_pair_map_two]
  map_halted := fun l h => by
    show l.1 = []
    rw [bmsState_one_eq l, show l.1.map (fun c => (c.head!, c.tail.head!)) = [] from h, List.map_nil]

def bmsOfPairHom : StepHom pairL (bmsL 1) where
  map := toBms2
  reindex := id
  map_step := fun l N => by
    refine Subtype.ext ?_
    show (expand2L N l.1).map (fun x => [x.1, x.2])
      = expandRL 2 N (l.1.map (fun x => [x.1, x.2]))
    exact (expandRL_two N l.1).symm
  map_halted := fun l h => by
    show l.1 = []
    have hh : l.1.map (fun x => [x.1, x.2]) = [] := h
    simpa using hh

/-- **The general system at two rows is the pair sequence system.** -/
def pairEquivBms : Equiv (bmsL 1) pairL where
  toFun := pairOfBmsHom.toSim
  invFun := bmsOfPairHom.toSim
  left_inv := fun l => Subtype.ext (bmsState_one_eq l).symm
  right_inv := fun l => Subtype.ext (map_pair_map_two l.1)

/-- **The general system at one row names ordinals**, since it is the
primitive sequence system. -/
noncomputable def bmsZeroEval :
    Eval (bmsL 0) (· < · : Ordinal.{0} → Ordinal.{0} → Prop) :=
  Eval.ofSim primOfBmsHom.toSim primEval


/-! ### Well-foundedness -/

/-- **The primitive sequence system is well founded.** -/
theorem prim_wf : prim.WF := primHom.toSim.wf exbOT_wf

/-- **And so is the general system at one row**, being the same system. -/
theorem bmsL_zero_wf : (bmsL 0).WF := bmsEquivPrim.wf_iff.mpr prim_wf

/-- The primitive sequence system carries the rank of its own expansion as an
ordinal measure, as well as the value `primEval` gives. -/
noncomputable def primRankEval :
    Eval prim (· < · : Ordinal.{0} → Ordinal.{0} → Prop) := Rewrite.rankEval prim_wf

/-! ### One row inside two -/

/-- **One row sits inside two**, as the general systems.  Composed from
`bmsEquivPrim`, `primHomPair` and `bmsOfPairHom`. -/
def bmsL_zero_sim_one : Sim (bmsL 0) (bmsL 1) :=
  bmsEquivPrim.toFun.comp (primHomPair.toSim.comp bmsOfPairHom.toSim)

/-- And the value it takes: a one-row matrix, with a row of zeros underneath. -/
theorem bmsL_zero_sim_one_map (l : (bmsL 0).State) :
    (bmsL_zero_sim_one.map l).1 = (withZero (l.1.map (fun c => c.head!))).map
      (fun x => [x.1, x.2]) := rfl

end Googology.Trans.BMS
