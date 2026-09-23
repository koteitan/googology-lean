/-
From koteitan, 1y-wo-por, `Por/Model.lean` (https://github.com/koteitan/1y-wo-por,
revision db86f2d13c2e18a8e2c2fae5e083d00fc4d48a78, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`.
-/
import Googology.Notation.Y.WellOrder.Por.Reflection
import Googology.Notation.Y.WellOrder.Por.Chain

/-!
# The model discharges every semantic obligation

This file collects the hypotheses of `OneY.RootIndexed.actual_expansion_wellFounded`
for the model: labels are ordinals, `lt = (· < ·)`, `D = True`, and `R` is the
relation of `Por.Relation`. There is no constructible universe and no admissible
ordinal.

  * the order is well-founded and transitive (O1, O2);
  * `R` is strict (O3, `R_lt`) and allows a smaller root index (O4, `R_weaken`);
  * finite reflection holds (O6, `finiteReflection`);
  * every finite diagram has a representation (O7, `initial_all`).
-/

namespace Por

open OneY.RootIndexed (Diagram Representation FiniteReflection)

/-- All hypotheses of `OneY.RootIndexed.actual_expansion_wellFounded` hold in the model. -/
theorem model_obligations :
    WellFounded (α := Ord) (· < ·) ∧
    (∀ {a b c : Ord}, a < b → b < c → a < c) ∧
    (∀ {k : ℕ} {index a b : Ord}, R k index a b → a < b) ∧
    (∀ {k : ℕ} {small large p c : Ord}, small < large → R k large p c → R k small p c) ∧
    FiniteReflection (α := Ord) (· < ·) (fun _ => True) R ∧
    (∀ G : Diagram, ∃ f, Representation (α := Ord) (· < ·) (fun _ => True) R G f) :=
  ⟨Ordinal.lt_wf, fun h1 h2 => h1.trans h2, fun h => R_lt h, fun h hR => R_weaken h.le hR,
    finiteReflection, initial_all⟩

end Por

#print axioms Por.model_obligations
