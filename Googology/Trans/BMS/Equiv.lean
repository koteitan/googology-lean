import Googology.Trans.BMS.Bms
import Googology.Trans.BMS.Calibrate

/-!
# The primitive sequence system, as an equivalence

Everything before this file translates one way.  `prim` simulates into
`exbOT`, one-row matrices carry ordinals, and one row terminates.  But a
simulation only says the source is no harder than the target.

`exbE0` is `exbOT` cut down to the standard forms below `ψ_0(Ω)`, with the
bracket numbered the way BMS numbers it.  On that system the translation is
invertible: `read` and `unread` are mutually inverse, `read` carries expansion
to `[ ]` and `unread` carries `[ ]` back, so `primEquivE0` is an `Equiv`.

So the primitive sequence system and the standard forms below `ψ_0(Ω)` are not
two systems that resemble each other — they are one system written two ways.
Termination, well-foundedness and the ordinal each state names transfer in
both directions.

`Trans/BMS/Reach.lean` is what makes the statement sharp on the matrix side:
the states of `prim` are exactly the standard one-row Bashicu matrices, so
nothing has been quietly left out of either side.
-/

namespace Googology.Trans.BMS

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term

theorem te0_lt_tW : te0 < tW := psi_lt_psi_iff.mpr (Or.inl (nil_lt_cons _ _ _))

theorem step_e0_ok (X : Term) (hOT : OT X) (hlt : X < te0) (n : Nat) :
    OT (fs X (idx X (n + 1))) ∧ fs X (idx X (n + 1)) < te0 := by
  refine ⟨(Term.step_ok hOT (lt_trans hlt te0_lt_tW) (n + 1)).1, ?_⟩
  by_cases h : X = nil
  · subst h
    rw [show fs nil (idx nil (n + 1)) = nil from by rw [fs]]
    exact nil_lt_cons _ _ _
  · exact lt_trans (fs_lt (idx_lt_dom hOT (lt_trans hlt te0_lt_tW) h (n + 1))) hlt

/-- **The standard forms below `ψ_0(Ω)`, as an expansion system.**  This is
`exbOT` cut down to the countable forms with no subscript but `0`, with the
bracket numbered the way BMS numbers it: `A[N]` is `X[N+1]`. -/
def exbE0 : Rewrite where
  State := {X : Term // OT X ∧ X < te0}
  step := fun X n => ⟨fs X.1 (idx X.1 (n + 1)), step_e0_ok X.1 X.2.1 X.2.2 n⟩
  halted := fun X => X.1 = nil

/-- Reading a matrix. -/
def toRead (l : PrimState) : exbE0.State := ⟨read 0 l.1, l.2.2, read_lt_e0 0 l.1⟩

theorem allNil_of_state (X : exbE0.State) : AllNil X.1 :=
  allNil_of_OT_lt_e0 X.1 X.2.1 X.2.2

/-- Writing a term back. -/
def toUnread (X : exbE0.State) : PrimState :=
  ⟨unread 0 X.1, col_unread X.1 (allNil_of_state X) 0,
    by rw [read_unread X.1 (allNil_of_state X) 0]; exact X.2.1⟩

/-- Reading is a translation. -/
def primHomE0 : StepHom prim exbE0 where
  map := toRead
  reindex := id
  map_step := fun l n => Subtype.ext (read_expandL n l.1 0 l.2.1)
  map_halted := fun l h => read_eq_nil l.1 0 h

/-- Writing back is a translation. -/
def e0HomPrim : StepHom exbE0 prim where
  map := toUnread
  reindex := id
  map_step := fun X n => by
    refine Subtype.ext ?_
    have hcol : Col 0 (unread 0 X.1) := col_unread X.1 (allNil_of_state X) 0
    have hread : read 0 (unread 0 X.1) = X.1 := read_unread X.1 (allNil_of_state X) 0
    have hstep := read_expandL n (unread 0 X.1) 0 hcol
    rw [hread] at hstep
    show unread 0 (fs X.1 (idx X.1 (n + 1))) = expandL n 0 (unread 0 X.1)
    rw [← hstep, unread_read _ 0 (col_expandL n _ 0 hcol)]
  map_halted := fun X h => by
    have hread : read 0 (unread 0 X.1) = X.1 := read_unread X.1 (allNil_of_state X) 0
    rw [show unread 0 X.1 = [] from h, read_nil] at hread
    exact hread.symm

/-- **The primitive sequence system and the standard forms below `ψ_0(Ω)` are
the same system.**  Not merely simulated one by the other: the translations
are mutually inverse. -/
def primEquivE0 : Equiv prim exbE0 where
  toFun := primHomE0.toSim
  invFun := e0HomPrim.toSim
  left_inv := fun l => Subtype.ext (unread_read l.1 0 l.2.1)
  right_inv := fun X => Subtype.ext (read_unread X.1 (allNil_of_state X) 0)

/-- The generators of the primitive sequence system. -/
def primStd : prim.Std where
  Standard := fun _ => True
  gen := fun n => ⟨List.range (n + 1), col_range n, OT_read_range n⟩
  gen_std := fun _ => trivial
  step_std := fun _ _ _ => trivial

/-- **From a generator, any expansion sequence ends.** -/
theorem primStd_terminates : primStd.Terminates :=
  primStd.of_terminates prim_terminates

end Googology.Trans.BMS
