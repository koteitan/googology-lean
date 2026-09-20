import Googology.Core.Rewrite

/-!
# Standard forms and generators

Initial states differ from system to system: BMS starts from
`(0,0,0)(1,1,1)(2,2,2)…`, DBMS from `(0)(1)(2,1)(3,2,1)…`, the Y sequence from
`1,k`.  That difference is absorbed by a bolt-on structure, attached only to
the systems that need it.
-/

namespace Googology

/-- Standard forms together with a family of generators. -/
structure Rewrite.Std (R : Rewrite) where
  /-- Being a standard form. -/
  Standard : R.State → Prop
  /-- The generators: the family of initial states of this system. -/
  gen : Nat → R.State
  /-- Generators are standard. -/
  gen_std : ∀ n, Standard (gen n)
  /-- Expansion preserves standardness. -/
  step_std : ∀ s k, Standard s → Standard (R.step s k)

namespace Rewrite.Std

variable {R : Rewrite} (S : R.Std)

/-- Termination restricted to chains starting from a standard form. -/
def Terminates : Prop :=
  ∀ f : Nat → R.State, S.Standard (f 0) →
    (∀ n, ∃ k, f (n + 1) = R.step (f n) k) → ∃ n, R.halted (f n)

/-- Termination on all states implies termination on standard forms. -/
theorem of_terminates (h : R.Terminates) : S.Terminates :=
  fun f _ hf => h f hf

end Rewrite.Std
end Googology
