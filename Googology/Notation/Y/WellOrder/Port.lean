import Lean

/-!
# A tactic for the port to Lean 4.30.0

The modules under `WellOrder/` were written for Lean 4.33.1. Lean 4.30.0 keeps a
`save_info` annotation on the alternatives of a `match` written in a statement.
After the `match` is reduced, the annotation stays on the term, and `omega` then
treats a subtraction of natural numbers under it as an atom. `strip_mdata`
removes every annotation from the goal and the hypotheses. It changes nothing
up to definitional equality.
-/

namespace Googology.Notation.Y.WellOrder

open Lean Elab Tactic Meta

/-- `e` with every metadata annotation removed. -/
partial def stripMData (e : Expr) : Expr :=
  e.replace fun
    | .mdata _ b => some (stripMData b)
    | _ => none

/-- Remove the metadata annotations from the goal and the hypotheses. -/
elab "strip_mdata" : tactic => withMainContext do
  let mut g ← getMainGoal
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    let t' := stripMData t
    if t' != t then
      g ← g.replaceLocalDeclDefEq d.fvarId t'
  let t ← instantiateMVars (← g.getType)
  g ← g.replaceTargetDefEq (stripMData t)
  replaceMainGoal [g]

end Googology.Notation.Y.WellOrder
