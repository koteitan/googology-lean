/-
The patterns-of-resemblance model of the omega-Y core, part 1 (this repository).
Taken from koteitan, wy-wo-por, `Por/Formula.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
The namespace `Por` is renamed to `OmegaY.Por`, since the 1-Y model of this repository uses `Por`.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Reflection.Interface

set_option backward.do.legacy false

/-!
# Σ₁ formulas over the key structures

A literal is an order bit, an internal relation bit `Rel_t(v_i, v_j)` or a top bit
`Top_t(v_i)`; the key of a relation or top bit is `eval t v`. A formula is a
conjunction of literals with some positions fixed as parameters. The top bit of
key `κ` is defined only where `allow κ` holds, and a top literal is true only
where its bit is defined. `ElemL` is Σ₁-elementarity with the top bits defined
below a key `θ`.

It proves that truth only depends on the bits the formula reads
(`Lit.holds_congr`, `sat_congr`), and that lowering the tuple pointwise keeps
the guards (`Lit.holds_of_le`).
-/

namespace OmegaY.Por

open OmegaY.Reflection

universe u v w

variable {Label : Type u} {Key : Type v} [LinearOrder Label] [LinearOrder Key]
variable (S : KeySyntax.{u,v,w} Label Key)

/-- A literal over `n` variables: an order bit, an internal relation bit
`Rel_t(v_i, v_j)` (key `eval t v`), or a top bit `Top_t(v_i)` (key `eval t v`).
`pos = false` is the negated literal. -/
inductive Lit (n : Nat) where
  | lt (i j : Fin n) (pos : Bool)
  | rel (t : S.Template n) (i j : Fin n) (pos : Bool)
  | top (t : S.Template n) (i : Fin n) (pos : Bool)

/-- A Σ₁ formula `∃ (unfixed variables), ⋀ lits`. The fixed positions are the
parameters. -/
structure Form where
  n : Nat
  fixed : Fin n → Bool
  lits : List (Lit S n)

variable {S}

/-- Truth of a literal. `rel κ x y` is the internal relation, `top κ x` the top
predicate of the structure, and `allow κ` says that the top bit of key `κ` is
defined in this structure. A top literal holds only where its bit is defined. -/
def Lit.Holds {n : Nat} (rel : Key → Label → Label → Prop) (top : Key → Label → Prop)
    (allow : Key → Prop) (v : Fin n → Label) : Lit S n → Prop
  | .lt i j pos => (v i < v j ↔ pos = true)
  | .rel t i j pos => (rel (S.eval t v) (v i) (v j) ↔ pos = true)
  | .top t i pos => allow (S.eval t v) ∧ (top (S.eval t v) (v i) ↔ pos = true)

/-- `φ` holds in the structure of height `c` with parameters `p` (only the fixed
positions of `p` are read). -/
def Sat (rel : Key → Label → Label → Prop) (top : Key → Label → Prop)
    (allow : Key → Prop) (c : Label) (φ : Form S) (p : Fin φ.n → Label) : Prop :=
  ∃ v : Fin φ.n → Label, (∀ i, φ.fixed i = true → v i = p i) ∧ (∀ i, v i < c) ∧
    ∀ l ∈ φ.lits, l.Holds rel top allow v

/-- Σ₁-elementarity of the height-`a` structure in the height-`b` structure, with
the top bits defined for keys below `θ`. -/
def ElemL (rel : Key → Label → Label → Prop) (topA topB : Key → Label → Prop)
    (θ : Key) (a b : Label) : Prop :=
  ∀ (φ : Form S) (p : Fin φ.n → Label), (∀ i, φ.fixed i = true → p i < a) →
    (Sat rel topA (· < θ) a φ p ↔ Sat rel topB (· < θ) b φ p)


/-! ### Helper lemmas (congruence of truth) -/

theorem Lit.holds_congr {n : Nat} {rel rel' : Key → Label → Label → Prop}
    {top top' : Key → Label → Prop} {allow : Key → Prop} {v : Fin n → Label} {c : Label}
    (hv : ∀ i, v i < c) (hrel : ∀ κ x y, y < c → (rel κ x y ↔ rel' κ x y))
    (htop : ∀ κ x, allow κ → (top κ x ↔ top' κ x)) (l : Lit S n) :
    l.Holds rel top allow v ↔ l.Holds rel' top' allow v := by
  cases l with
  | lt i j pos => exact Iff.rfl
  | rel t i j pos => exact iff_congr (hrel _ _ _ (hv j)) Iff.rfl
  | top t i pos => exact and_congr_right fun h => iff_congr (htop _ _ h) Iff.rfl

theorem sat_congr {rel rel' : Key → Label → Label → Prop}
    {top top' : Key → Label → Prop} {allow : Key → Prop} {c : Label} {φ : Form S}
    {p : Fin φ.n → Label} (hrel : ∀ κ x y, y < c → (rel κ x y ↔ rel' κ x y))
    (htop : ∀ κ x, allow κ → (top κ x ↔ top' κ x)) :
    Sat rel top allow c φ p ↔ Sat rel' top' allow c φ p :=
  exists_congr fun _ => and_congr_right fun _ => and_congr_right fun hv =>
    forall₂_congr fun l _ => Lit.holds_congr hv hrel htop l

theorem Lit.holds_allow_mono {n : Nat} {rel : Key → Label → Label → Prop}
    {top : Key → Label → Prop} {allow allow' : Key → Prop} {v : Fin n → Label}
    (hA : ∀ κ, allow κ → allow' κ) {l : Lit S n} (h : l.Holds rel top allow v) :
    l.Holds rel top allow' v := by
  cases l with
  | lt i j pos => exact h
  | rel t i j pos => exact h
  | top t i pos => exact ⟨hA _ h.1, h.2⟩

theorem Lit.holds_of_le {n : Nat} {rel rel' : Key → Label → Label → Prop}
    {top top' : Key → Label → Prop} {θ Θ : Key} {v w : Fin n → Label}
    (hwv : ∀ i, w i ≤ v i) {l : Lit S n} (h1 : l.Holds rel top (· < θ) v)
    (h2 : l.Holds rel' top' (· < Θ) w) : l.Holds rel' top' (· < θ) w := by
  cases l with
  | lt i j pos => exact h2
  | rel t i j pos => exact h2
  | top t i pos => exact ⟨lt_of_le_of_lt (S.monotone_eval t hwv) h1.1, h2.2⟩


end OmegaY.Por
