import Googology.Trans.PoR.InaccPsi.R2.CitedLu

set_option autoImplicit false

/-!
# Wilken 2007, `Σ₁`-elementarity and Skolem hull operators, Lemma 4.2: `lhᵗ(α) < α⁺`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.

Same conventions as `R2.Cited`, `R2.CitedL`, `R2.CitedW` (`Ω₁ = ω₁` is the uncountable regular cardinal of [W07a] §3
chosen in `R2.Cited`, `Ω₂ = OmTwo = ω₂`, `Tset τ = Tᵗ`, `vt τ = ϑᵗ = ϑ₀` over the base `τ`, `lhT τ = lhᵗ` the
constant of `R2.CitedL` for [W07b] Def 4.1).

One axiom, `yzLhT_lt_plus`.

Literal texts (checked word for word against the printed papers):
* (4.2b) [W07b] Lemma 4.2, p. 166: "Lemma 4.2. Let `α = ϑ^τ(∆ + η) > τ`. Then `lh^τ(α) < α^+`."
* (§4b) [W07b] §4, p. 165: "Let `τ ∈ {1} ∪ E` and `T^τ` be the relativized notation system introduced in Section 3
  of [5]." ([5] = [W07a].)  [W07b] Def 4.1, p. 166: "For `α ∈ T^τ ∩ Ω₁` we define an ordinal `lh^τ(α) ∈ T^τ ∩ Ω₁` by recursion
  on `h^τ(α)` as follows."
* (C4.1) [W07a] Convention 4.1, p. 142: "Given a term `α = ϑ^τ(ξ) ∈ T^τ` we introduce the notational convention that
  `α = ϑ^τ(∆ + η)` automatically means that `ξ = ∆ + η` is a decomposition such that `Ω₁ | ∆` and `η < Ω₁`. […] In a
  situation where some `α = ϑ^τ(∆ + η)` is fixed, we will write `α^+` to denote the ordinal `ϑ^τ(∆ + η + 1)`."
* (D3.22) [W07a] Def 3.22, third clause: "`ξ ∈ T_m ∩ Ω_{k+2} ⇒ ϑ_k(ξ) ∈ T_m` for `k ≥ m`" (here `m = k = 0`, over the
  base `τ`, Convention 3.25: `ϑ₀ = ϑ^τ`).
* (L3.30) [W07a] Lemma 3.30: "For `m < ω` the function `ϑ_m ↾ T^τ ∩ Ω_{m+2}` is 1-1 and has values in
  `P ∩ [Ω_m, Ω_{m+1})`."

Our steps (they discharge the hypotheses of (4.2b) from those of the axiom; nothing else is used):
* (◇τ) `InE τ` gives `τ ∈ E ⊆ {1} ∪ E` (§4b); `τ < Ω₁` is the standing convention of `R2.Cited` that every base is
  countable, so `Ω₁` is "an uncountable regular cardinal greater than `τ`" as [W07a] §3 asks.
* (◇α) `ξ ∈ Tᵗ` and `ξ < Ω₂` give, by (D3.22) with `m = k = 0`, the term `α := ϑᵗ(ξ) ∈ Tᵗ`, whose value is
  `vt τ ξ < Ω₁` (L3.30: values in `[Ω₀, Ω₁)`), so `α ∈ Tᵗ ∩ Ω₁` and `lhᵗ(α) = lhT τ α` is defined (§4b).  By (L3.30)
  `ϑ₀` is 1-1 on `Tᵗ ∩ Ω₂`, so `ξ` is THE argument of the term of `α` (no other argument in `Tᵗ ∩ Ω₂` has the value
  `α`).
* (◇Δ) Write `ξ = Δ + η` with `Δ := Ω₁·(ξ / Ω₁)` and `η := ξ mod Ω₁`: then `Ω₁ | Δ` and `η < Ω₁`, the decomposition of
  (C4.1) (it is unique: `Δ` is the largest multiple of `Ω₁` that is `≤ ξ`).  So `α = ϑᵗ(Δ + η)` in the sense of
  (C4.1), and `α⁺ = ϑᵗ(Δ + η + 1) = ϑᵗ(ξ + 1) = vt τ (ξ + 1)` (`Δ + η + 1 = ξ + 1` by associativity).
* (◇>) `α > τ` is the hypothesis `τ < vt τ ξ`.
Then (4.2b) reads `lhT τ (vt τ ξ) < vt τ (ξ + 1)`, the statement of the axiom.  (`α⁺` is an ordinal; (4.2b) does not
ask `ξ + 1 ∈ Tᵗ`, and the axiom does not use `ξ + 1 ∈ Tᵗ`.)

The axiom mentions only `InE`, `Om1`, `Tset`, `OmTwo`, `vt`, `lhT`, all imported (`R2.CitedLu` imports `R2.CitedL`
and `R2.CitedW`, and defines `OmTwo`); `set_option autoImplicit false` is on.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- **[W07b] Lemma 4.2** ("Let `α = ϑ^τ(∆ + η) > τ`. Then `lh^τ(α) < α^+`."), with [W07a] Convention 4.1
(`α⁺ = ϑᵗ(Δ + η + 1)`), Def 3.22 and Lemma 3.30 (see the module docstring, steps ◇τ, ◇α, ◇Δ, ◇>): for a countable
`ε`-number base `τ`, `ξ ∈ Tᵗ ∩ Ω₂` with `τ < ϑᵗ(ξ)`: `lhᵗ(ϑᵗ(ξ)) < ϑᵗ(ξ + 1)`. -/
axiom yzLhT_lt_plus {τ ξ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hξT : ξ ∈ Tset τ) (hξ2 : ξ < OmTwo)
    (hτα : τ < vt τ ξ) : lhT τ (vt τ ξ) < vt τ (ξ + 1)

end Googology.Trans.PoR.InaccPsi.R2
