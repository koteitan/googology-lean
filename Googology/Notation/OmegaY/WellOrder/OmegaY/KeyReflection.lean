/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/KeyReflection.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: imports `OmegaY.Reflection` instead of `OmegaY.Reflection.Stability`, which is not included.
Taken from koteitan, wy-wo-por, `OmegaY/KeyReflection.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Keys
import Googology.Notation.OmegaY.WellOrder.OmegaY.Reflection

set_option backward.do.legacy false

/-! The actual finite-vector vectorSyntax instantiates the recursively constructed
reflection relation. This is an explicit connection between the key proofs
and the semantic construction, not an assumed reflection model. -/

namespace OmegaY.KeyReflection

universe u
variable {Label : Type u} [LinearOrder Label]

def vectorSyntax (m : Nat) : Reflection.KeySyntax Label (Keys.Key m Label) where
  Template := Keys.Template m
  eval := Keys.eval
  monotone_eval := Keys.eval_mono

instance syntax_template_countable (m n : Nat) :
    Countable ((vectorSyntax (Label := Label) m).Template n) :=
  Keys.template_countable m n

variable [WellFoundedLT Label]

abbrev R (m : Nat) := Reflection.R (vectorSyntax (Label := Label) m)

theorem weaken {m : Nat} {small large : Keys.Key m Label} {a b : Label}
    (h : small ≤ large) (hr : R m large a b) : R m small a b :=
  Reflection.key_weaken (vectorSyntax m) h hr

/-- In particular, demands may share the control's first root and still be
strictly earlier because a later finite coordinate replaces infinity. -/
theorem shared_root_demand (a p b : Label)
    (h : R 2 (toLex (fun i : Fin 2 =>
      if i.val = 0 then (a : WithTop Label) else ⊤)) p b) :
    R 2 (toLex (fun _ : Fin 2 => (a : WithTop Label))) p b :=
  weaken (le_of_lt (Keys.shared_root_before_infinity a)) h

end OmegaY.KeyReflection

#print axioms OmegaY.KeyReflection.weaken
#print axioms OmegaY.KeyReflection.shared_root_demand
