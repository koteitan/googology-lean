import Googology.Trans.PoR.InaccPsi.R2.Defs

/-!
# Two cited theorems of Carlson 2009, as axioms about the Lean `R₂^C`

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.

`R₂^C` (`R2C`) is defined in `R2.Defs` literally from [C09] Def 5.3–5.4, so the two theorems below
are statements about a defined object.  They are stated for the special case that is used
(a covered pattern that is a finite closed substructure of `R₂`), with the clauses copied from the
paper.  If the Lean `R₂^C` differed from Carlson's `R₂`, these axioms could be false; the audit of
`R2.Defs` found the definitions literal.

* `C09_thm14_10`: [C09] Theorem 14.10, parts 1–3.
* `C09_thm14_14`: [C09] Theorem 14.14.

Conventions: a finite closed substructure of `R₂` is a pattern ([C09] Lemma 5.7 (2)) and is covered
(the identity is a covering, [C09] Def 5.2, Def 14.1); "`Q` is a covering of `P`" means that some
covering of `P` is onto `Q` ([C09] Def 5.2); `≤pw` is `PwLe` ([C09] §1); the core of `R₂` is
`Core R2C` ([C09] Def 2.6); "`κ ≤₁ ∞`" means `κ ≤₁ α` for all `α ≥ κ` ([C09] §1, end).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- `κ ≤₁ ∞` in `R₂^C`: `κ ≤₁ α` for every `α ≥ κ` ([C09] §1: "we have written `κ ≤₁ ∞` to indicate
`κ ≤₁ α` for all `α ≥ κ`"). -/
def LeInfC (κ : Ordinal.{0}) : Prop := ∀ a, κ ≤ a → le1 κ a

/-- **[C09] Theorem 14.10**, parts 1–3: "If `P` is a covered pattern then there is a substructure
`P*` of `R₂` such that 1. `P*` is isomorphic to `P`. 2. `|P*| ≤pw |Q|` whenever `Q` is a closed
substructure of `R₂` which is a covering of `P*`. 3. `P*` is an isominimal substructure of `R₂`."
Stated for `P` the finite closed substructure of `R₂` with universe `A` (a pattern by [C09]
Lemma 5.7 (2), covered by the identity).  The case `0 ∉ A` (allowed by `Closed`) follows from the case
`0 ∈ A`: apply the theorem to `A ∪ {0}` and remove `0` from the copy; in `R₂` the relation `0 ≤ᵢ b`
holds only for `b = 0` (the clause of [C09] Def 5.3 with `Y = {0}` fails), and isomorphisms and
coverings send `0` to `0`, the only `x` with `x + x = x`. -/
axiom C09_thm14_10 {A : Finset Ordinal.{0}} (hA : Closed ↑A) :
    ∃ Ps : Finset Ordinal.{0}, (∃ g, Iso R2C ↑A ↑Ps g) ∧
      (∀ Q : Finset Ordinal.{0}, Closed ↑Q → (∃ h, Cov R2C R2C ↑Ps ↑Q h) → PwLe Ps Q) ∧
      Isominimal R2C Ps

/-- **[C09] Theorem 14.14**: "If there exists a `κ` such that `κ ≤₁ ∞` then the least such `κ` is the
core of `R₂`.  Otherwise, the core of `R₂` is ORD." -/
axiom C09_thm14_14 :
    (∀ κ, IsLeast {k | LeInfC k} κ → Core R2C = Set.Iio κ) ∧
      ((¬ ∃ κ, LeInfC κ) → Core R2C = Set.univ)

end Googology.Trans.PoR.InaccPsi.R2
