import Googology.Trans.PoR.InaccPsi.R2.CitedR1

set_option autoImplicit false

/-!
# Cited: [W07b] Claim 5.6 in its full form (`X ≤pw h[X]`)

[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.

`R2.claim56` states [W07b] Claim 5.6 for the coverings that fix `X`.  The claim itself asks only `X ≤pw h[X]`; this is
the form used for Lemma IMG at every point (`Xi.xi_img_eps`), where the covering `π⁻¹ ∘ f` moves the points of `X`
up, not to themselves.

Literal text: Claim 5.6 as quoted in `R2.CitedR1` (`claim56`), word for word ("there is no covering `h` of `X ∪ Z` with
`X ≤pw h[X] < h[Z] < α`"); Def 5.1 (coverings) and the definition of `≤pw` ("`X ≤pw Y` for finite sets `X` and `Y`
(of ordinals) means that `X` and `Y` are of the same cardinality and satisfy `≤` pointwise with respect to increasing
enumerations of their elements") and of `X < Y` ("for `max(X) < min(Y)`") from [W07b] §5, as paraphrased in
`R2.CitedR1` (`R1Cov`).

Our steps.  A covering `h` of `X ∪ Z` is strictly increasing (`R1Cov`), so `h[X]` has the cardinality of `X` and its
increasing enumeration is `h` applied to that of `X`: `X ≤pw h[X]` is `x ≤ h(x)` for every `x ∈ X`; `h[X] < h[Z]` is
`h(x) < h(z)` for `x ∈ X`, `z ∈ Z`; `h[Z] < α` is `h(z) < α` for `z ∈ Z`.  `R1Cov` keeps the graph of `+` in both
directions, a narrower notion of covering, so the negated statement below follows from the claim.  The hypotheses on
`τ`, `α` are those of `claim56` (Def 3.2, Lemma 3.4 (b), Cor 5.10).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- **[W07b] Claim 5.6** (proof of Theorem 5.3), full form: for `τ ∈ {1} ∪ E` and an additive principal
`τ`-`≤₁`-minimal `α ∈ Tᵗ ∩ (τ, Ω₁)` there are finite `X ⊆ α` and `Z ⊆ [α, lh(α)]` with `α, lh(α) ∈ Z` and no covering
`h` of `X ∪ Z` with `X ≤pw h[X] < h[Z] < α`. -/
axiom claim56pw {τ α : Ordinal.{0}} (hτ : τ = 1 ∨ InE τ) (hτ1 : τ < Om1) (hαT : α ∈ Tset τ)
    (hτα : τ < α) (hα1 : α < Om1) (hαP : Indec α) (hmin : ∀ d, le1R d α → d < α → d ≤ τ) :
    ∃ l, IsLh1 α l ∧ ∃ X Z : Finset Ordinal.{0}, (∀ x ∈ X, x < α) ∧ (∀ z ∈ Z, α ≤ z ∧ z ≤ l) ∧
      α ∈ Z ∧ l ∈ Z ∧
      ¬ ∃ h, R1Cov ↑(X ∪ Z) h ∧ (∀ x ∈ X, x ≤ h x) ∧ (∀ x ∈ X, ∀ z ∈ Z, h x < h z) ∧
        ∀ z ∈ Z, h z < α

end Googology.Trans.PoR.InaccPsi.R2
