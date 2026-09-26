/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Reflection.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: the definitions of the interface moved, unchanged, to
OmegaY/Reflection/Interface.lean.  The relation `R` is no longer defined by
positive finite-graph compression; it is the Σ₁-elementarity relation
`Por.R` of this repository.  `key_weaken` and `finite_reflection` keep their
statements and are proved from `Por.key_weaken` and `Por.finite_reflection`.
`Reflects`, `StageLT`, `stage_wellFounded`, `recursionStep`, `equation`,
`lower_lt`, `reflects`, `pointwise_le_of_compression` and `trans` are removed.
Taken from koteitan, wy-wo-por, `OmegaY/Reflection.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.Por.Relation

set_option backward.do.legacy false

/-!
# The reflection relation read by the omega-Y core

`R S θ a b` is the relation of the patterns-of-resemblance model: the
height-`a` structure is a Σ₁-elementary substructure of the height-`b`
structure, with top bits defined below the key `θ`. No reflection or existence
axiom is assumed.
-/

namespace OmegaY.Reflection

universe u v w

variable {Label : Type u} {Key : Type v}
variable [LinearOrder Label] [LinearOrder Key] [WellFoundedLT Label] [WellFoundedLT Key]
variable (S : KeySyntax.{u,v,w} Label Key)

/-- The relation, from `Por.Relation`. -/
noncomputable def R (theta : Key) (a b : Label) : Prop := Por.R S theta a b

/-- Lowering the control key only restricts which top bits are defined. -/
theorem key_weaken {theta Theta : Key} {a b : Label}
    (hle : theta ≤ Theta) (h : R S Theta a b) : R S theta a b :=
  Por.key_weaken S hle h

/-- The retained prefix is fixed at a selected cut, while the cut label itself
is allowed to move. No root used in a key is required to be retained. -/
theorem finite_reflection {n : Nat} (G : List (InternalAtom S n))
    (N : List (TopAtom S n)) (f : Fin n → Label) (cut : Fin n)
    {theta : Key} {top : Label} (hmono : StrictMono f) (hbound : Bounded f top)
    (hG : InternalHolds S (R S) G f) (hkeys : KeysBelow S N f theta)
    (hN : TopHolds S (R S) N f top) (hcontrol : R S theta (f cut) top) :
    ∃ g : Fin n → Label, StrictMono g ∧ Bounded g (f cut) ∧
      (∀ i, i < cut → g i = f i) ∧ (∀ i, g i ≤ f i) ∧
      InternalHolds S (R S) G g ∧ TopHolds S (R S) N g (f cut) :=
  Por.finite_reflection S G N f cut hmono hbound hG hkeys hN hcontrol

#print axioms key_weaken
#print axioms finite_reflection

end OmegaY.Reflection
