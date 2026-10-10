import Mathlib

/-!
# `R₂^C`: Carlson's patterns of resemblance of order 2, defined by coverings

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.

The arithmetic part is `R₀ = (On; ≤, 0, +)`, `+` a binary function symbol, `0` a constant
([C09] §3, "two important examples of EM structures ... (ORD, ≤, 0, +)").  The language `L₂`
adds `≤₁`, `≤₂` ([C09] §5).  This file defines, literally after [C09]:

* `DecompR0`, `DecompIn`, `Closed` — decomposable / closed ([C09] Def 2.1, Def 2.3);
* `ArithIso`, `Cov` — (onto) embedding of arithmetic parts, covering ([C09] Def 5.2);
* `Inf1`, `Inf2`, `CofCov` — the relations `≤₁^∞`, `≤₂^∞` of [C09] Def 5.3 for a given
  interpretation `R` of `≤₁, ≤₂`;
* `col`, `le1`, `le2`, `R2C` — [C09] Def 5.4: `α ≤ₙ β iff α ≤ₙ^∞ β in R₂`, a recursion on `β`
  (the right-hand side only reads `≤₁, ≤₂` on pairs below `β`, and, in clause 1(d) of
  `≤₂^∞`, the pairs `(y, β)` of `≤₁`, which are computed first);
* `Iso`, `PwLe`, `Isominimal`, `Core` — [C09] Def 2.6 for any interpretation `R`.

Two readings, both equivalent to the text:
* [C09] Def 5.3 (c)+(d) for `≤₂`: "there is a covering of `X ∪ Y` onto `X ∪ Ỹ`" and "the
  `i`-th element `y` of `Y` with `y ≤₁ b` has `ỹ ≤₁ a` for the `i`-th element `ỹ` of `Ỹ`".
  A covering is strictly increasing and `X < Y`, `X < Ỹ`, so it maps the `i`-th element of
  `Y` to the `i`-th element of `Ỹ`; we state (c)+(d) as one covering `h` with
  `y ≤₁ b → h y ≤₁ a`.
* [C09] Def 5.3 clause 2 ("any finite structure `P`"): a finite `L₂`-structure whose arithmetic
  part is arithmetic is isomorphic to a closed substructure of `R₀` ([C09] remark after
  Lemma 4.6), and the clause is invariant under isomorphism of `P`; so `P` ranges over the
  pairs (a finite closed `Z ⊆ On`, an interpretation `P` of `≤₁, ≤₂`).
  "Cofinally many finite `Y` below `c`": for every `c' < c` there is one with `c' < Y`
  (as in [C09] Lemma 5.5 (1), "cofinally many `Ỹ` below `α` ... Moreover, `α' < Ỹ`").
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-! ## Closed sets of `R₀ = (On; ≤, 0, +)` -/

/-- `x` is decomposable in `R₀` ([C09] Def 2.1): `x` is the constant `0`, or `x = y + z`
with `y, z < x`. -/
def DecompR0 (x : Ordinal.{0}) : Prop := x = 0 ∨ ∃ y z, y < x ∧ z < x ∧ y + z = x

/-- `x` is decomposable in the substructure of `R₀` with universe `A` ([C09] Def 2.1; the
constant `0` is interpreted in `A` iff `0 ∈ A`, and `+` is the restriction of `+`). -/
def DecompIn (A : Set Ordinal.{0}) (x : Ordinal.{0}) : Prop :=
  x = 0 ∨ ∃ y ∈ A, ∃ z ∈ A, y < x ∧ z < x ∧ y + z = x

/-- **Closed** ([C09] Def 2.3): every indecomposable of `A` is an indecomposable of `R₀`,
i.e. every `x ∈ A` that is decomposable in `R₀` is decomposable in `A`. -/
def Closed (A : Set Ordinal.{0}) : Prop := ∀ x ∈ A, DecompR0 x → DecompIn A x

/-! ## Interpretations of `≤₁, ≤₂`, coverings -/

/-- An interpretation of the two relation symbols `≤₁, ≤₂` of `L₂` on `On` (the arithmetic
part `≤, 0, +` is always that of `R₀`). -/
structure Str where
  le1 : Ordinal.{0} → Ordinal.{0} → Prop
  le2 : Ordinal.{0} → Ordinal.{0} → Prop

/-- `h` is an isomorphism of the arithmetic parts of the substructures with universes `A`
and `B` (a bijection that keeps and reflects `≤` and the graph of `+`; it sends `0` to `0`,
the only `x` with `x + x = x`). -/
def ArithIso (A B : Set Ordinal.{0}) (h : Ordinal.{0} → Ordinal.{0}) : Prop :=
  Set.BijOn h A B ∧ StrictMonoOn h A ∧
    ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, (x + y = z ↔ h x + h y = h z)

/-- **A covering of `(A; R)` onto `(B; R')`** ([C09] Def 5.2): a closed embedding of the
arithmetic parts (onto `B`, so its range is closed in `B`) with
`x ≤ᵢ y → h(x) ≤ᵢ h(y)` (`i = 1, 2`). -/
def Cov (R R' : Str) (A B : Set Ordinal.{0}) (h : Ordinal.{0} → Ordinal.{0}) : Prop :=
  ArithIso A B h ∧ (∀ x ∈ A, ∀ y ∈ A, R.le1 x y → R'.le1 (h x) (h y)) ∧
    (∀ x ∈ A, ∀ y ∈ A, R.le2 x y → R'.le2 (h x) (h y))

/-! ## [C09] Definition 5.3 -/

/-- **`a ≤₁^∞ b` in `R`** ([C09] Def 5.3): `a ≤ b`, and for any finite `X ⊆ (−∞, a)` and
finite `Y ⊆ [a, b)` with `X ∪ Y` closed there is a finite `Ỹ ⊆ (−∞, a)` with (a) `X < Ỹ`,
(b) `X ∪ Ỹ` closed, (c) `X ∪ Ỹ` is a covering of `X ∪ Y`. -/
def Inf1 (R : Str) (a b : Ordinal.{0}) : Prop :=
  a ≤ b ∧ ∀ X Y : Finset Ordinal.{0}, (∀ x ∈ X, x < a) → (∀ y ∈ Y, a ≤ y ∧ y < b) →
    Closed ↑(X ∪ Y) → ∃ Yt : Finset Ordinal.{0}, (∀ y ∈ Yt, y < a) ∧
      (∀ x ∈ X, ∀ y ∈ Yt, x < y) ∧ Closed ↑(X ∪ Yt) ∧ ∃ h, Cov R R ↑(X ∪ Y) ↑(X ∪ Yt) h

/-- "There are cofinally many finite `Y` below `c` such that `X ∪ Y` is closed and
`X ∪ Y` is a covering of `P`" ([C09] Def 5.3, clause 2 of `≤₂^∞`), for the pattern
`P = (Z; P)`. -/
def CofCov (R : Str) (X : Finset Ordinal.{0}) (Z : Finset Ordinal.{0}) (P : Str)
    (c : Ordinal.{0}) : Prop :=
  ∀ c' < c, ∃ Y : Finset Ordinal.{0}, (∀ y ∈ Y, c' < y ∧ y < c) ∧ Closed ↑(X ∪ Y) ∧
    ∃ h, Cov P R ↑Z ↑(X ∪ Y) h

/-- **`a ≤₂^∞ b` in `R`** ([C09] Def 5.3); `top1 y` stands for `y ≤₁ b`.
1. for finite `X ⊆ (−∞, a)`, `Y ⊆ [a, b)` with `X ∪ Y` closed there is a finite
   `Ỹ ⊆ (−∞, a)` with `X < Ỹ`, `X ∪ Ỹ` closed and a covering `h` of `X ∪ Y` onto `X ∪ Ỹ`
   with `h(y) ≤₁ a` whenever `y ∈ Y` and `y ≤₁ b` ((c) and (d));
2. for any finite `X` below `a` and any finite pattern `P`, if there are cofinally many
   finite `Y` below `a` with `X ∪ Y` closed and a covering of `P`, then there are cofinally
   many such `Y` below `b`. -/
def Inf2 (R : Str) (top1 : Ordinal.{0} → Prop) (a b : Ordinal.{0}) : Prop :=
  a ≤ b ∧
  (∀ X Y : Finset Ordinal.{0}, (∀ x ∈ X, x < a) → (∀ y ∈ Y, a ≤ y ∧ y < b) →
    Closed ↑(X ∪ Y) → ∃ Yt : Finset Ordinal.{0}, (∀ y ∈ Yt, y < a) ∧
      (∀ x ∈ X, ∀ y ∈ Yt, x < y) ∧ Closed ↑(X ∪ Yt) ∧
      ∃ h, Cov R R ↑(X ∪ Y) ↑(X ∪ Yt) h ∧ ∀ y ∈ Y, top1 y → R.le1 (h y) a) ∧
  (∀ X : Finset Ordinal.{0}, (∀ x ∈ X, x < a) → ∀ (Z : Finset Ordinal.{0}) (P : Str),
    Closed ↑Z → CofCov R X Z P a → CofCov R X Z P b)

/-! ## [C09] Definition 5.4: `R₂` -/

/-- The interpretation of `≤₁, ≤₂` on the pairs with right end below `b`, read off the
columns `IH y` (`y < b`). -/
def below (b : Ordinal.{0}) (IH : ∀ y : Ordinal.{0}, y < b → Ordinal.{0} → Prop × Prop) : Str :=
  ⟨fun x y => ∃ h : y < b, (IH y h x).1, fun x y => ∃ h : y < b, (IH y h x).2⟩

/-- The column of `b`: `col b a = (a ≤₁ b, a ≤₂ b)`, by recursion on `b` ([C09] Def 5.4). -/
noncomputable def col : Ordinal.{0} → Ordinal.{0} → Prop × Prop :=
  (wellFounded_lt (α := Ordinal.{0})).fix fun b IH a =>
    (Inf1 (below b IH) a b, Inf2 (below b IH) (fun y => Inf1 (below b IH) y b) a b)

/-- **`α ≤₁ β` in `R₂^C`** ([C09] Def 5.4). -/
def le1 (a b : Ordinal.{0}) : Prop := (col b a).1

/-- **`α ≤₂ β` in `R₂^C`** ([C09] Def 5.4). -/
def le2 (a b : Ordinal.{0}) : Prop := (col b a).2

/-- `R₂^C = (On; ≤, 0, +, ≤₁, ≤₂)` ([C09] Def 5.4). -/
def R2C : Str := ⟨le1, le2⟩

/-! ## Isominimal sets and the core ([C09] Def 2.6) -/

/-- An isomorphism of the substructures of `(On; ≤, 0, +, R)` with universes `A`, `B`. -/
def Iso (R : Str) (A B : Set Ordinal.{0}) (g : Ordinal.{0} → Ordinal.{0}) : Prop :=
  ArithIso A B g ∧ (∀ x ∈ A, ∀ y ∈ A, R.le1 x y ↔ R.le1 (g x) (g y)) ∧
    (∀ x ∈ A, ∀ y ∈ A, R.le2 x y ↔ R.le2 (g x) (g y))

/-- `X ≤pw Y` ([C09] §1): same cardinality, and the `i`-th element of `X` is at most the
`i`-th element of `Y` (both listed increasingly). -/
def PwLe (X Y : Finset Ordinal.{0}) : Prop :=
  ∃ hc : X.card = Y.card, ∀ i : Fin X.card,
    X.orderEmbOfFin rfl i ≤ Y.orderEmbOfFin rfl (Fin.cast hc i)

/-- **Isominimal** ([C09] Def 2.6): `B` is finite and closed, and `B` is the only closed
`C` with `C ≅ B` and `C ≤pw B`. -/
def Isominimal (R : Str) (B : Finset Ordinal.{0}) : Prop :=
  Closed ↑B ∧ ∀ C : Finset Ordinal.{0}, Closed ↑C → (∃ g, Iso R ↑B ↑C g) → PwLe C B → C = B

/-- **The core** ([C09] Def 2.6): the elements of the isominimal sets. -/
def Core (R : Str) : Set Ordinal.{0} := {x | ∃ B : Finset Ordinal.{0}, Isominimal R B ∧ x ∈ B}

end Googology.Trans.PoR.InaccPsi.R2
