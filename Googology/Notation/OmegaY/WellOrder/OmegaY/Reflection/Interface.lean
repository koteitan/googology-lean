/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Reflection.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: only the definitions of the interface are kept, unchanged (from the
beginning of the file to `KeysBelow`); the module comment is rewritten.  The relation `R`, its recursion and its theorems are replaced by the
model of `Por.Relation` (see OmegaY/Reflection.lean).
Taken from koteitan, wy-wo-por, `OmegaY/Reflection/Interface.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Mathlib.Order.WellFounded
import Mathlib.Order.Fin.Basic

set_option backward.do.legacy false

/-!
# The interface of the reflection layer

The finite key syntax, internal atoms and top atoms, and what it means for a
labelling to satisfy them. These are the names the omega-Y core reads; the
relation itself is defined in `Por.Relation`.
-/

namespace OmegaY.Reflection

universe u v w

variable {Label : Type u} {Key : Type v}

/-- A finite syntax with a pointwise-monotone interpretation in the key order. -/
structure KeySyntax (Label : Type u) (Key : Type v)
    [Preorder Label] [Preorder Key] where
  Template : Nat → Type w
  eval : {n : Nat} → Template n → (Fin n → Label) → Key
  monotone_eval : ∀ {n : Nat} (t : Template n) {f g : Fin n → Label},
    (∀ i, g i ≤ f i) → eval t g ≤ eval t f

variable [LinearOrder Label] [LinearOrder Key]

structure InternalAtom (S : KeySyntax.{u,v,w} Label Key) (n : Nat) where
  key : S.Template n
  parent : Fin n
  child : Fin n
  parent_lt_child : parent < child

structure TopAtom (S : KeySyntax.{u,v,w} Label Key) (n : Nat) where
  key : S.Template n
  parent : Fin n

variable (S : KeySyntax.{u,v,w} Label Key)

abbrev Relation := Key → Label → Label → Prop

def Bounded {n : Nat} (f : Fin n → Label) (b : Label) : Prop := ∀ i, f i < b

def FixesBelow {n : Nat} (a : Label) (f g : Fin n → Label) : Prop :=
  ∀ i, f i < a → g i = f i

def InternalHolds (R : Relation (Label := Label) (Key := Key))
    {n : Nat} (G : List (InternalAtom S n)) (f : Fin n → Label) : Prop :=
  ∀ e ∈ G, R (S.eval e.key f) (f e.parent) (f e.child)

def TopHolds (R : Relation (Label := Label) (Key := Key))
    {n : Nat} (N : List (TopAtom S n)) (f : Fin n → Label) (b : Label) : Prop :=
  ∀ e ∈ N, R (S.eval e.key f) (f e.parent) b

def KeysBelow {n : Nat} (N : List (TopAtom S n))
    (f : Fin n → Label) (theta : Key) : Prop :=
  ∀ e ∈ N, S.eval e.key f < theta

end OmegaY.Reflection
