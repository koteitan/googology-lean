import Googology.Trans.PoR.InaccPsi.R2.CitedC09
import Googology.Trans.PoR.InaccPsi.R2.Cited

/-!
# Two more cited facts of Carlson 2009 about the Lean `R₂^C`: the core is countable, and a pair with a
pair nested inside exists

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.

As in `R2.CitedC09`, `R₂^C` (`R2C`) is defined in `R2.Defs` literally from [C09] Def 5.3–5.4, so the
axioms below are statements about a defined object; they would be false only if the Lean `R₂^C`
differed from Carlson's `R₂`.

* `C09_cor15_15`: [C09] Corollary 15.15 ("Assume ZF.  If the collection of arithmetic structures in
  `H(ω)` is computable then the substructure of `R₂` whose universe is the core is isomorphic to a
  computable structure and, hence, the core is a computable ordinal"), used only through "the core is
  a countable ordinal": `Core R2C = [0, κ)` for some `κ < ω₁`.  Here `R₀ = (On; ≤, 0, +)`.  The
  hypothesis of the corollary is about `R₀`: an arithmetic structure ([C09] Def 4.1) is decided by the
  atomic formulas `t(κ₁, …, κₙ) ≤ s(κ₁, …, κₙ)`, `= `, on increasing indecomposables `κ₁ < ⋯ < κₙ` of
  `R₀`, and for `+` such a term is a sum of the `κᵢ` that reduces, by `κᵢ + κⱼ = κⱼ` for `i < j`, to a
  sum `κ_{i₁} + ⋯ + κ_{iₘ}` with `i₁ ≥ ⋯ ≥ iₘ`; two such sums compare lexicographically.  So the
  encoding of `R₀` is computable, and so is the collection of arithmetic structures in `H(ω)`.  This
  remark is the only step that is not a quotation; the conclusion is used as stated in the paper.
  [C09] §15 assumes that the language `L₂` is finite; here `L₂ = {0, +, ≤, ≤₁, ≤₂}`.  The
  introduction of [C09] states this computability of the core for `R₀ = (On; 0, +, ≤)` as an aim of
  the paper.
* `C09_nest`: [C09] Lemma 15.11 ("Assuming ZF, every pattern is covered") with [C09] Theorem 14.10,
  part 1 ("If `P` is a covered pattern then there is a substructure `P*` of `R₂` such that `P*` is
  isomorphic to `P`"), for one pattern `N`: the universe `{0, a, b, c, d}` with the arithmetic of
  `{0, ω, ω², ω³, ω⁴}` (`0 < a < b < c < d`, `a, b, c, d` indecomposable), `≤₁` the reflexive closure of
  `{(a, b), (a, c), (a, d), (b, c)}`, `≤₂` the reflexive closure of `{(a, d), (b, c)}`.  `N` is a
  pattern ([C09] Def 5.6, a finite model of reflection of order two): 1. its arithmetic part is a
  closed substructure of `R₀`, hence arithmetic; 2. the left ends `a, b` of `≺₁` are indecomposable;
  3. the right ends `d, c` of `≺₂` are indecomposable; 4. `≤₁` is a partial order (transitive:
  `a ≤₁ b ≤₁ c` and `a ≤₁ c`); 5. `≤₂` is a partial order (no two non-trivial pairs compose);
  6. `≤₁` respects `≤` ([C01]: `≤₁ ⊆ ≤`, and `a ≤₁ x` whenever `a ≤₁ y`, `a ≤ x ≤ y`: for `a` every
  `x ∈ [a, d]` is `≤₁`-above `a`; for `b`, `x ∈ [b, c]`); 7. `≤₂` respects `≤₁` (`≤₂ ⊆ ≤₁`, and
  `a ≤₂ x` whenever `a ≤₂ y`, `a ≤₁ x ≤₁ y`: `x ≤₁ d` holds only for `x ∈ {a, d}`, `x ≤₁ c` only for
  `x ∈ {a, b, c}`, and `b ≤₁ x` only for `x ∈ {b, c}`).  The copy `P*` gives four ordinals
  `x < x' < y' < y` with `x ≤₂ y` and `x' ≤₂ y'` in `R₂`.

[C01] T. J. Carlson, "Elementary patterns of resemblance", APAL 108 (2001) 19–77 (the definition of
"respects").
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- **[C09] Corollary 15.15** (used as "the core of `R₂` is a countable ordinal"; the hypothesis on
`R₀ = (On; ≤, 0, +)` is discussed in the module docstring). -/
axiom C09_cor15_15 : ∃ κ, κ < Om1 ∧ Core R2C = Set.Iio κ

/-- **[C09] Lemma 15.11 with Theorem 14.10 (1)** for the pattern `N` of the module docstring (a pair
with a pair nested inside): `R₂` has `x < x' < y' < y` with `x ≤₂ y` and `x' ≤₂ y'`. -/
axiom C09_nest : ∃ x x' y' y : Ordinal.{0}, x < x' ∧ x' < y' ∧ y' < y ∧ le2 x y ∧ le2 x' y'

end Googology.Trans.PoR.InaccPsi.R2
