import Googology.Trans.PoR.InaccPsi.R2.BrTerm
import Googology.Trans.PoR.InaccPsi.R2.Cited

/-!
# Cited facts of [W25] on the simultaneously defined `ϑ̄`-functions, as axioms

[W25] G. Wilken, "Fundamental sequences based on localization", arXiv 2410.15953v4 (2025).  §2.2 and
§2.4 of [W25] restate, with their numbers there, results of A. Weiermann and G. Wilken, "Ordinal
arithmetic with simultaneously defined theta-functions", MLQ 57 (2011); that paper is not used here, the
statements are cited from [W25].

The objects are DEFINED in Lean (`R2.BrThb`: `thb τ`, `Dom τ`, `Tbar τ` literally after [W25] Def 2.7,
Def 2.9; `R2.BrTerm`: normal terms `NF τ`, `Ki`, `Kst`, `star` after [W25] Def 2.11), except `Tset`, the
constant of `R2.Cited` for Wilken's stepwise `Tᵗ`.  The axioms below are statements about these
objects; they would be false only if the Lean definitions differed from the paper's.

The setting ([W25] §2.1): "For `τ ∈ E₁`, i.e. `τ` is either equal to 1 or any epsilon number, we defined the
relativized notation system `Tᵗ` ... `Tᵗ` is built up over a sequence `τ = Ω₀ = ϑ₀(0), Ω₁ = ϑ₁(0),
Ω₂ = ϑ₂(0), …`, where `Ω₁, Ω₂, …` is a strictly increasing sequence of regular ordinals such that `Ω₁ > τ`.
The canonical choice is to assume that `τ` is countable (recursive) and that `Ωᵢ = ℵᵢ` for `0 < i < ω`."
[W25] §2.2: "We keep conventions regarding `Ω₀ = τ` and the sequence `(Ωᵢ)_{0<i<ω}` of regular ordinals
strictly above `τ`, and set `Ω_ω := sup_{n<ω} Ωₙ`."  `Base τ` (`τ = 1` or `ω^τ = τ`, and `τ < ω₁`) is
this setting with the canonical choice (`OmT τ i = ω_i` for `i > 0`, `Tset` of `R2.Cited` is taken with
`Ω₁ = ω₁` too).

Our own steps that discharge the hypotheses "`α ∈ T̄^τ`" and that identify the sets of Def 2.11:
* every value of a normal term is in `T̄^τ` (`NF.mem_Tbar`), and every element of `T̄^τ` is the value of a
  normal term (`exists_NF`);
* a normal term is the unique normal term of its value (`NF.unique`, from the injectivity of `ϑ̄ᵢ` on
  `dom(ϑ̄ᵢ)` and the ranges `[Ωᵢ, Ω_{i+1})`, both proved in `R2.BrThb`); the term of `α = ϑ̄ⱼ(ξ)` has the
  argument term of `ξ` (and `ξ ∈ dom(ϑ̄ⱼ)`), the term of a sum lists the additive components in the order of
  the additive normal form, a trailing sum of components below `τ` being one parameter;
* so `Ki i t`, and the second components of `Kst i t`, computed on the normal term `t` of `α`, are
  `Kᵢ(α)` and `K*ᵢ(α)` of [W25] Def 2.11 (clause 2 splits `α =NF ξ + η` into the last component `η` and the
  rest `ξ`, so `Kᵢ(α)` is the union over all components; a component below `τ` contributes `∅` by
  clause 1), and `star τ i t` is `α^{*i} = max(Kᵢ(α) ∪ {0})` ([W25] after Def 2.11: "We also set
  `α^{*i} := max(Kᵢ(α) ∪ {0})` ... we simply write `α^{⋆i}` instead of `α^{*i}`").

The axioms (4):
* `W25_lem212`: [W25] Lemma 2.12 (4.2 of [10]), its last sentence: "In particular, for every
  `γ ∈ T̄^τ ∩ dom(ϑ̄ₖ)` we have `γ^{*k} < ϑ̄ₖ(γ)`."
* `W25_lem213`: [W25] Lemma 2.13 (4.3 of [10]): "`α ∈ dom(ϑ̄_m) ⇔ K*_{m+1}(α) < α` for `α ∈ T̄^τ`."
* `W25_prop215`: [W25] Proposition 2.15 (4.4 of [10]): "For `α, β ∈ T̄^τ ∩ dom(ϑ̄ᵢ)` we have
  `ϑ̄ᵢ(α) < ϑ̄ᵢ(β) ⇔ (α < β & α^{⋆i} < ϑ̄ᵢ(β)) ∨ ϑ̄ᵢ(α) ≤ β^{⋆i}`."
* `W25_same`: `Tᵗ ∩ Ω₁ = T̄^τ ∩ Ω₁`, from [W25] Definition 2.29 (3.9 of [10]): "Let `fᵗ : Tᵗ → T̄^τ` denote the
  order-isomorphism of `Tᵗ` onto `T̄^τ`, that is `fᵗ(α) := α` if `α < τ`, `fᵗ(ξ) + fᵗ(η)` if
  `α =NF ξ + η > τ`, `ϑ̄ₘ(itₘ(ξ))` if `α = ϑₘ(ξ)`", and [W25] Theorem 2.28 (cf. 3.7 of [10]): "For `m < ω`
  the domain transformation functions `itₘ` and `rtₘ` are strictly increasing and are inverses of one
  another. ... We have `ϑₘ = ϑ̄ₘ ∘ itₘ` and `ϑ̄ₘ = ϑₘ ∘ rtₘ`."  Our steps: by induction on the term of
  `α ∈ Tᵗ`, `fᵗ(α) = α` (for `α < τ` by the first clause; for `α =NF ξ + η` by the second and the induction
  hypothesis; for `α = ϑₘ(ξ)`, `fᵗ(α) = ϑ̄ₘ(itₘ(ξ)) = ϑₘ(ξ) = α` by Theorem 2.28, an equality of ordinals).
  So `fᵗ` is the identity, and as it is onto `T̄^τ`, `Tᵗ = T̄^τ` as sets of ordinals; here only the
  countable part is stated.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Googology.Notation.InaccPsi Tm

/-- **[W25] Lemma 2.12**, last sentence: `γ^{*k} < ϑ̄ₖ(γ)` for `γ ∈ T̄^τ ∩ dom(ϑ̄ₖ)`. -/
axiom W25_lem212 {τ : Ordinal.{0}} (hτ : Base τ) {t : Tm} (ht : NF τ t) (k : ℕ)
    (hd : Dom τ k (ev τ t)) : Tm.star τ k t < thb τ (ev τ t) k

/-- **[W25] Lemma 2.13**: `α ∈ dom(ϑ̄ₘ) ⇔ K*_{m+1}(α) < α` for `α ∈ T̄^τ`. -/
axiom W25_lem213 {τ : Ordinal.{0}} (hτ : Base τ) {t : Tm} (ht : NF τ t) (m : ℕ) :
    Dom τ m (ev τ t) ↔ ∀ p ∈ Kst (m + 1) t, ev τ p.2 < ev τ t

/-- **[W25] Proposition 2.15**: for `α, β ∈ T̄^τ ∩ dom(ϑ̄ᵢ)`,
`ϑ̄ᵢ(α) < ϑ̄ᵢ(β) ⇔ (α < β ∧ α^{⋆i} < ϑ̄ᵢ(β)) ∨ ϑ̄ᵢ(α) ≤ β^{⋆i}`. -/
axiom W25_prop215 {τ : Ordinal.{0}} (hτ : Base τ) {s t : Tm} (hs : NF τ s) (ht : NF τ t) (i : ℕ)
    (hds : Dom τ i (ev τ s)) (hdt : Dom τ i (ev τ t)) :
    thb τ (ev τ s) i < thb τ (ev τ t) i ↔
      (ev τ s < ev τ t ∧ Tm.star τ i s < thb τ (ev τ t) i) ∨ thb τ (ev τ s) i ≤ Tm.star τ i t

/-- **[W25] Def 2.29 with Theorem 2.28**: Wilken's stepwise `Tᵗ` and the simultaneous `T̄^τ` have the same
countable elements. -/
axiom W25_same {τ : Ordinal.{0}} (hτ : Base τ) {a : Ordinal.{0}} (ha : a < Om (1 : Ordinal.{0})) :
    a ∈ Tset τ ↔ a ∈ Tbar τ

end Googology.Trans.PoR.InaccPsi.R2.Br
