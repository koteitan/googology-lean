/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean,
OmegaY/Reflection/OrdinalSupply.lean, revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: `Label` and `top` are those of `Por.Supply` (same definitions);
the `OrderBot` instance and `bot_lt_top` are kept.  The Skolem-function
supply (`arity` … `points_strictMono`) is removed, and
`initial_finite_graph` keeps its statement and is proved from
`Por.Supply.initial_finite_graph` (closed points of the Σ₁ model).
Taken from koteitan, wy-wo-por, `OmegaY/Reflection/OrdinalSupply.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Reflection
import Googology.Notation.OmegaY.WellOrder.Por.Supply

set_option backward.do.legacy false

/-!
# Labels below ω₁ and the initial representations

All labels belong to the set-bounded well-order `[0, ω₁]`. Every finite
positive graph and finite reservoir has an actual initial representation by
closed points of the patterns-of-resemblance model (`Por.Supply`).
-/

namespace OmegaY.Reflection.OrdinalSupply

open Ordinal Cardinal
open scoped Cardinal Ordinal

universe v w

abbrev Label : Type 1 := Por.Supply.Label

instance : OrderBot Label where
  bot := ⟨0, zero_le⟩
  bot_le a := by
    change (0 : Ordinal) ≤ a.1
    exact zero_le

noncomputable def top : Label := Por.Supply.top

theorem bot_lt_top : (⊥ : Label) < top := by
  change (0 : Ordinal) < ω₁
  exact lt_trans omega0_pos omega0_lt_omega_one

variable {Key : Type v} [LinearOrder Key] [WellFoundedLT Key]
variable (S : KeySyntax.{1,v,w} Label Key)
variable [∀ n, Countable (S.Template n)]

/-- Every finite positive graph and finite reservoir has an actual initial
representation, with its own top strictly below omega-one. -/
theorem initial_finite_graph {n : Nat} (G : List (InternalAtom S n))
    (N : List (TopAtom S n)) :
    ∃ beta : Label, beta < top ∧ ∃ f : Fin n → Label,
      StrictMono f ∧ Bounded f beta ∧
      InternalHolds S (R S) G f ∧ TopHolds S (R S) N f beta :=
  Por.Supply.initial_finite_graph S G N

#print axioms initial_finite_graph

end OmegaY.Reflection.OrdinalSupply
