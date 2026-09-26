/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Model.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Model.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.KeyReflection
import Googology.Notation.OmegaY.WellOrder.OmegaY.Reflection.OrdinalSupply

set_option backward.do.legacy false

/-! Concrete bounded-ordinal model for the finite multi-root keys. -/

namespace OmegaY.Model

abbrev Label := Reflection.OrdinalSupply.Label
abbrev Key (m : Nat) := Keys.Key m Label
noncomputable def keySyntax (m : Nat) := KeyReflection.vectorSyntax (Label := Label) m
instance keySyntax_countable (m : Nat) : ∀ n, Countable ((keySyntax m).Template n) :=
  fun n => Keys.template_countable m n
abbrev R (m : Nat) := Reflection.R (keySyntax m)
abbrev InternalAtom (m n : Nat) := Reflection.InternalAtom (keySyntax m) n
abbrev TopAtom (m n : Nat) := Reflection.TopAtom (keySyntax m) n

/-- An actual initial representation, including arbitrary finite virtual
reservoirs; neither reflection nor existence of representations is assumed. -/
theorem initial_finite_graph {m n : Nat} (G : List (InternalAtom m n))
    (N : List (TopAtom m n)) :
    ∃ beta : Label, beta < Reflection.OrdinalSupply.top ∧ ∃ f : Fin n → Label,
      StrictMono f ∧ Reflection.Bounded f beta ∧
      Reflection.InternalHolds (keySyntax m) (R m) G f ∧
      Reflection.TopHolds (keySyntax m) (R m) N f beta :=
  Reflection.OrdinalSupply.initial_finite_graph (keySyntax m) G N

theorem key_weaken {m : Nat} {small large : Key m} {a b : Label}
    (h : small ≤ large) (hr : R m large a b) : R m small a b :=
  Reflection.key_weaken (keySyntax m) h hr

/-- The first control and its strictly earlier virtual demands are supplied
from pure finite template comparisons, rather than assumed semantically. -/
theorem initial_controlled_graph {m n : Nat} (G : List (InternalAtom m n))
    (N : List (TopAtom m n)) (control : TopAtom m n)
    (hearlier : ∀ e ∈ N, Keys.templateKey e.key < Keys.templateKey control.key) :
    ∃ beta : Label, beta < Reflection.OrdinalSupply.top ∧ ∃ f : Fin n → Label,
      StrictMono f ∧ Reflection.Bounded f beta ∧
      Reflection.InternalHolds (keySyntax m) (R m) G f ∧
      Reflection.KeysBelow (keySyntax m) N f (Keys.eval control.key f) ∧
      Reflection.TopHolds (keySyntax m) (R m) N f beta ∧
      R m (Keys.eval control.key f) (f control.parent) beta := by
  obtain ⟨beta, hbeta, f, hf, hb, hG, hN⟩ :=
    initial_finite_graph G (N ++ [control])
  refine ⟨beta, hbeta, f, hf, hb, hG, ?_, ?_, ?_⟩
  · intro e he
    exact Keys.eval_lt_of_template_lt e.key control.key f hf (hearlier e he)
  · intro e he
    exact hN e (List.mem_append_left _ he)
  · exact hN control (by simp)

theorem finite_reflection {m n : Nat} (G : List (InternalAtom m n))
    (N : List (TopAtom m n)) (f : Fin n → Label) (cut : Fin n)
    {theta : Key m} {top : Label} (hmono : StrictMono f)
    (hbound : Reflection.Bounded f top)
    (hG : Reflection.InternalHolds (keySyntax m) (R m) G f)
    (hkeys : Reflection.KeysBelow (keySyntax m) N f theta)
    (hN : Reflection.TopHolds (keySyntax m) (R m) N f top)
    (hcontrol : R m theta (f cut) top) :
    ∃ g : Fin n → Label, StrictMono g ∧ Reflection.Bounded g (f cut) ∧
      (∀ i, i < cut → g i = f i) ∧ (∀ i, g i ≤ f i) ∧
      Reflection.InternalHolds (keySyntax m) (R m) G g ∧
      Reflection.TopHolds (keySyntax m) (R m) N g (f cut) :=
  Reflection.finite_reflection (keySyntax m) G N f cut hmono hbound hG hkeys hN hcontrol

end OmegaY.Model

#print axioms OmegaY.Model.initial_finite_graph
#print axioms OmegaY.Model.finite_reflection
#print axioms OmegaY.Model.initial_controlled_graph
