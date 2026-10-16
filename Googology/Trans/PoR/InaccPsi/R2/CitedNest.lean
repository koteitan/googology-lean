import Googology.Trans.PoR.InaccPsi.R2.NestK

/-!
# A cited fact of Carlson 2009 about the Lean `R₂^C`: nests of every depth exist

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
[C01] T. J. Carlson, "Elementary patterns of resemblance", APAL 108 (2001) 19–77 (the definition of
"respects", p. 241: "`≼₁` respects `≼` if `≼₁` is a subset of `≼` and `a ≼₁ x` whenever `a ≼₁ b` and
`a ≼ x ≼ b`").

As in `R2.CitedC09` and `R2.CitedCore`, `R₂^C` (`R2C`) is defined in `R2.Defs` literally from [C09]
Def 5.3–5.4, so the axiom below is a statement about a defined object.  `NestSeq` is defined in
`R2.NestK` (imported here): `NestSeq k a b` says `a 0 < ⋯ < a (k-1) < b (k-1) < ⋯ < b 0` and
`a i ≤₂ b i` for `i < k`.

* `C09_nestk`: [C09] Lemma 15.11 ("Assuming ZF, every pattern is covered") with [C09] Theorem 14.10,
  part 1 ("If `P` is a covered pattern then there is a substructure `P*` of `R₂` such that `P*` is
  isomorphic to `P`"), for the pattern `N_k` (`k ≥ 1`; for `k = 0` the statement is trivial).  This is
  the axiom `C09_nest` of `R2.CitedCore` (the case `k = 2`) for every `k`.

  **The pattern `N_k`** (the check below is ours, not a quotation).  Universe
  `{0, c₁, …, c_{2k}}` with the arithmetic of `{0, ω¹, …, ω^{2k}}` (`cⱼ = ω^j`); write `aᵢ = c_{i+1}`,
  `bᵢ = c_{2k-i}` (`i < k`), so `a₀ < ⋯ < a_{k-1} < b_{k-1} < ⋯ < b₀`.  `≤₁` is the reflexive closure of
  `{(aᵢ, z) : aᵢ < z ≤ bᵢ}`, and `≤₂` is the reflexive closure of `{(aᵢ, bᵢ) : i < k}`.  The items of
  [C09] Def 5.6 (a model of reflection of order two, finite):
  1. the `L₀`-part is the substructure of `R₀ = (On; ≤, 0, +)` on a set of indecomposables and `0`;
     such a set is closed ([C09] Def 2.3), so the part is arithmetic ([C09] Lemma 4.2 and Lemma 4.3:
     "any closed substructure of an arithmetic structure is arithmetic");
  2. every left end of `≺₁` (an `aᵢ`) is indecomposable (all `cⱼ` are powers of `ω`);
  3. every right end of `≺₂` (a `bᵢ`) is indecomposable;
  4. `≤₁` is a partial order: reflexive by definition; antisymmetric since `≤₁ ⊆ ≤`; transitive: if
     `aᵢ ≤₁ y ≤₁ z` with `y ≠ aᵢ`, `y ≠ z`, then `y = aⱼ` with `aᵢ < aⱼ ≤ bᵢ`, so `j > i`, `bⱼ < bᵢ`, and
     `z ∈ (aⱼ, bⱼ] ⊆ (aᵢ, bᵢ]`, so `aᵢ ≤₁ z` (a `bⱼ` is `≤₁` only itself);
  5. `≤₂` is a partial order: no two non-trivial pairs `(aᵢ, bᵢ)`, `(aⱼ, bⱼ)` compose (`bᵢ` is no `aⱼ`);
  6. `≤₁` respects `≤`: `≤₁ ⊆ ≤`, and if `aᵢ ≤₁ y` and `aᵢ ≤ x ≤ y` then `x ∈ [aᵢ, bᵢ]`, so `aᵢ ≤₁ x`;
  7. `≤₂` respects `≤₁`: `≤₂ ⊆ ≤₁` (`aᵢ ≤₁ bᵢ`), and if `aᵢ ≤₂ bᵢ` and `aᵢ ≤₁ x ≤₁ bᵢ` then
     `x ∈ {aᵢ, bᵢ}`: `x ≤₁ bᵢ` holds only for `x = bᵢ` and `x = aⱼ` with `bᵢ ≤ bⱼ`, i.e. `j ≤ i`, and
     `aᵢ ≤₁ aⱼ` needs `aⱼ ≥ aᵢ`, i.e. `j ≥ i`.  (The non-trivial pairs of `≤₂` have `aᵢ ≤₂ bᵢ`; the
     trivial ones are reflexive.)
  So `N_k` is a pattern; by Lemma 15.11 it is covered, and Theorem 14.10 (1) gives `P* ≅ N_k` inside
  `R₂`: ordinals `a*₀ < ⋯ < a*_{k-1} < b*_{k-1} < ⋯ < b*₀` (the isomorphism keeps `≤`) with
  `a*ᵢ ≤₂ b*ᵢ` (it keeps `≤₂`).  Only this order and these `≤₂`-relations are used, so the statement
  is weaker than the cited one.  "Assuming ZF": the Lean metatheory is stronger.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

/-- **[C09] Lemma 15.11 with Theorem 14.10 (1)** for the pattern `N_k` of the module docstring: `R₂` has
a `k`-nest for every `k`. -/
axiom C09_nestk : ∀ k : ℕ, ∃ a b : ℕ → Ordinal.{0}, NestSeq k a b

end Googology.Trans.PoR.InaccPsi.R2
