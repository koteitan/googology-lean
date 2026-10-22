import Googology.Trans.PoR.InaccPsi.R2.CitedLq

set_option autoImplicit false

/-!
# A cited fact of Wilken 2007: the countable components of `Ω₁·(Ω₁·γ + β) + η ∈ Tᵗ` lie in `Tᵗ`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

Same conventions as `R2.CitedLq` (`Ω₁ = Om1`, `Tset τ = Tᵗ`, `ϑᵗ = vt τ`, every base `τ` a countable `ε`-number).
`R2.CitedLq` states the direction "components in `Tᵗ` ⇒ `Ω₁·(Ω₁·γ + β) + η ∈ Tᵗ`" (`lqArg_mem`), and `R2.CitedVz`
the last component (`vzRem_T`: `η ∈ Tᵗ` for `ξ = Δ + η ∈ Tᵗ`, `Ω₁ ∣ Δ`, `η < Ω₁`); the converse for `γ` and `β` is
stated here, once, because the comparison of a level `Ω₁·(Ω₁·(1 + γ') + β')` with a level of a larger `γ` needs it
(the data `β'` of a lower level is not bounded by the data of the larger level).

What is **not** restated (checked first): `lqArg_mem`, `lqVt_lt`, `lqLt_of_vt_lt`, `lqLevel_lt_vt`, `lqLhT`, `lqPi`
(`R2.CitedLq`), `lgArg_mem`, `lgQuot_mem` (`R2.CitedLg`: `ξ / Ω₁ ∈ Tᵗ` for `ξ ∈ Tᵗ`, `ξ < Ω₁·Ω₁`), `vzRem_T`
(`R2.CitedVz`), `vt_rep`, `vt_E_iff`, `vt_memTwo` (`R2.CitedEv`).

Literal texts ([W07a]):
* (T) Def 3.22: "`T_m` is defined inductively as follows: • `Ω_m ⊆ T_m` • `ξ, η ∈ T_m ⇒ ξ + η ∈ T_m` • `ξ ∈ T_m ∩
  Ω_{k+2} ⇒ ϑ_k(ξ) ∈ T_m` for `k ≥ m`."
* (Θ) Theorem 3.23: "For `m < ω` we have … `T_m ∩ Ω_{m+1} = θ_m = sup_{n≥m} ϑ_m(⋯(ϑ_n(0))⋯)`."
* (U) Remark after Corollary 3.24: "each `T_m` again gives rise to a notation system with parameters from `Ω_m` that
  provides a unique term for every ordinal which is element of some `Tⁿ_m` where `n > m` (again refining the clause
  for ordinal addition as we did for the systems `Tⁿ_m`)."
* (S) Def 3.28: "We define sets of subterms `Subᵗ_m(α)` for `m < ω` and notations `α` in `Tᵗ` by recursion on the
  build up of `Tᵗ`: • `Subᵗ_m(α) := {α}` for parameters `α < τ` • `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ) ∪ Subᵗ_m(η)` for
  `ξ, η ∈ Tᵗ` s.t. `α =NF ξ + η > τ` • `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ)` if `k ≥ m`, `{α}` if `k < m`, for `α = ϑ_k(ξ)`
  where `ξ ∈ Tᵗ ∩ Ω_{k+2}`."
* (W) Lemma 4.2: "For any `m < ω` and any `α < Ω_{m+1}` we have `ϑ_m(1 + α) = ω̄_{Ω_m+α}`"; (Z) after Def 3.1:
  "`ϑⁿ_m(0) = Ω_m` for `m < n`".
* (E) Lemma 4.3: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ`.  Then `τ < α ∈ E ⇔ Δ > 0`."
* (L) Lemma 3.30: "For `m < ω` the function `ϑ_m ↾ Tᵗ ∩ Ω_{m+2}` is 1-1 and has values in `P ∩ [Ω_m, Ω_{m+1})`.  Let
  `α, γ ∈ Tᵗ ∩ Ω_{m+2}`.  Then `α^{*m} < ϑ_m(α)` and `ϑ_m(α) < ϑ_m(γ) ⇔ α < γ ∧ α^{*m} < ϑ_m(γ) ∨ ϑ_m(α) ≤ γ^{*m}`."
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- **[W07a] Def 3.22, Theorem 3.23, the Remark after Corollary 3.24, Def 3.28, Lemma 3.30 (`m = 1`), Lemma 4.2, the
remark after Def 3.1, Lemma 4.3** (texts T, Θ, U, S, L, W, Z, E): for `γ, β, η < Ω₁` with `Ω₁·(Ω₁·γ + β) + η ∈ Tᵗ`: `γ ∈ Tᵗ` and `β ∈ Tᵗ`.

Our steps.  Write `γ =ANF ω^{c₁} + ⋯ + ω^{cᵢ}` and `β =ANF ω^{b₁} + ⋯ + ω^{bⱼ}` (`cₗ ≤ γ`, `bₗ ≤ β`, all `< Ω₁`).
* (◇c, ◆β of `R2.CitedLq`, `R2.CitedLv`, by W with `m = 1` and Z) `ϑ₁(Ω₁ + c) = Ω₁·Ω₁·ω^c` and `ϑ₁(b) = Ω₁·ω^b` for
  `b, c < Ω₁`, so `ξ := Ω₁·(Ω₁·γ + β) + η = ϑ₁(Ω₁ + c₁) + ⋯ + ϑ₁(Ω₁ + cᵢ) + ϑ₁(b₁) + ⋯ + ϑ₁(bⱼ) + η`, a non-increasing
  sum of additive principal numbers (`Ω₁ + cₗ > bₗ'`) followed by `η < Ω₁`, i.e. `ξ =NF` this sum.
* By U the term of `ξ ∈ Tᵗ` is unique; it is this sum (a sum of `ϑ₁`-terms and `η`; its summands are additive principal
  and non-increasing, and an additive principal member of `Tᵗ` that is `≥ Ω₁` and below `Ω₂ = ϑ₂(0)` is a `ϑ₁`-term
  by the clauses T: neither a parameter `< τ`, nor a value of `ϑ₀ < Ω₁`, nor a proper sum).  By S (the second clause,
  read along the build up of the term) every summand `ϑ₁(Ω₁ + cₗ)`, `ϑ₁(bₗ)` is a member of `Tᵗ`, and by S (the third
  clause, `k = 1 ≥ 0`) its argument `ζ` is a member of `Tᵗ ∩ Ω₃`.  This argument is `Ω₁ + cₗ` resp. `bₗ`: by L
  (`m = 1`), `ζ ≥ Ω₂` would give `ϑ₁(ζ) ≥ ϑ₁(Ω₂)` (`(Ω₂)^{*1} = 0`) and `ϑ₁(Ω₂) > ϑ₁(Ω₁·2) = Ω₁³` (`Ω₁·2 < Ω₂`,
  `(Ω₁·2)^{*1} = Ω₁ < ϑ₁(Ω₂)`), above the summand; so `ζ < Ω₂`, and `ϑ₁` is 1-1 there (L), which with W and Z gives
  `ζ = Ω₁ + cₗ` resp. `bₗ`.  By S again (the second clause for
  `Ω₁ + cₗ =NF Ω₁ + cₗ₁ + ⋯` with `cₗ =ANF cₗ₁ + ⋯`, `Ω₁ = ϑ₁(0)` by Z) the additive components of `cₗ` are members
  of `Tᵗ`, and `cₗ ∈ Tᵗ` (T, second clause).
* `Tᵗ ∩ Ω₁ = θ₀` is an ordinal (Θ), a supremum of values `ϑ₀(ϑ₁(⋯))` with `ϑ₁(⋯) ≥ Ω₁`, which are `ε`-numbers by E;
  so `θ₀` is closed under `ζ ↦ ω^ζ` and `+`.  Hence `ω^{cₗ}, ω^{bₗ} ∈ θ₀` and `γ, β ∈ θ₀ = Tᵗ ∩ Ω₁`.
For `γ = 0` the `ϑ₁(Ω₁ + cₗ)` part is empty, for `β = 0` the `ϑ₁(bₗ)` part; then the claim for that component is
`0 ∈ Tᵗ`, which holds since `0 < τ` is a parameter (S, first clause). -/
axiom riArg_T {τ γ β η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hγΩ : γ < Om1) (hβΩ : β < Om1)
    (hηΩ : η < Om1) (h : Om1 * (Om1 * γ + β) + η ∈ Tset τ) : γ ∈ Tset τ ∧ β ∈ Tset τ

end Googology.Trans.PoR.InaccPsi.R2
