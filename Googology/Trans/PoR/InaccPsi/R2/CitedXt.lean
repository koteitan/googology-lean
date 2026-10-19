import Googology.Trans.PoR.InaccPsi.R2.CitedVz
import Googology.Trans.PoR.InaccPsi.R2.CitedLu
import Googology.Trans.PoR.InaccPsi.R2.EpsQ

/-!
# A cited fact of Wilken 2007, as an axiom: the base change of `Ω₁·ω = ϑ₁(1)`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

Same conventions as `R2.Cited` and `R2.CitedVz` (`Ω₁ = ω₁`, `Tset τ = Tᵗ`, `Par τ = Parᵗ`, `TB τ σ = Tᵗ[σ]`,
`pi σ τ = π_{σ,τ}`, all bases countable `ε`-numbers, `Bases σ τ`: `σ, τ ∈ E`, `σ < τ < Ω₁`).

Literal texts used ([W07a]):
* (D) Def 5.1: "Let `τ ∈ E` and `Tᵗ` be the notation system over `τ`.  Further, let `σ ∈ {1} ∪ (E ∩ τ)`.  We define
  `Tᵗ[σ] := {α ∈ Tᵗ | Parᵗ(α) ⊆ σ}` and `π_{σ,τ} : Tᵗ[σ] → Tᵟ` by the following clauses:
  • `π_{σ,τ}(ξ) := ξ` if `ξ < σ`
  • `π_{σ,τ}(ξ) := π_{σ,τ}(ξ₁) + π_{σ,τ}(ξ₂)` if `ξ =NF ξ₁ + ξ₂ > τ`
  • `π_{σ,τ}(ξ) := ϑ_k(π_{σ,τ}(η))` if `ξ = ϑ_k(η)` for some `k > 0` and `η ∈ Tᵗ[σ] ∩ Ω_{k+2}`
  • `π_{σ,τ}(ξ) := ϑ^σ(π_{σ,τ}(η))` if `ξ = ϑᵗ(η)` for some `η ∈ Tᵗ[σ] ∩ Ω₂`."
* (S) Def 3.28: "We define sets of subterms `Subᵗ_m(α)` for `m < ω` and notations `α` in `Tᵗ` by recursion on the
  build up of `Tᵗ`: • `Subᵗ_m(α) := {α}` for parameters `α < τ` • `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ) ∪ Subᵗ_m(η)` for
  `ξ, η ∈ Tᵗ` s.t. `α =NF ξ + η > τ` • `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ)` if `k ≥ m`, `{α}` if `k < m`, for
  `α = ϑ_k(ξ)` where `ξ ∈ Tᵗ ∩ Ω_{k+2}`. … The set of parameters `< τ` used in the unique term denoting some
  `α ∈ Tᵗ` is denoted by `Parᵗ(α) := Subᵗ₀(α) ∩ τ`."
* (T) Def 3.22: "`T_m` is defined inductively as follows: • `Ω_m ⊆ T_m` • `ξ, η ∈ T_m ⇒ ξ + η ∈ T_m`
  • `ξ ∈ T_m ∩ Ω_{k+2} ⇒ ϑ_k(ξ) ∈ T_m` for `k ≥ m`."
* (W) Lemma 4.2: "For any `m < ω` and any `α < Ω_{m+1}` we have `ϑ_m(1 + α) = ω̄_{Ω_m + α}`."
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- **[W07a] Def 5.1 (first and third clauses), Def 3.28, Def 3.22, Lemma 4.2 (`m = 1`)** (texts D, S, T, W):
for bases `σ < τ`, `Ω₁·ω ∈ Tᵗ[σ]` and `π_{σ,τ}(Ω₁·ω) = Ω₁·ω`.

Our steps.  (1) The term.  `1 < τ = Ω₀ ⊆ T₀` (T, first clause; `τ ∈ E`), so `1` is a parameter, `1 ∈ T₀ ∩ Ω₃`, and
`ϑ₁(1) ∈ T₀` (T, third clause, `k = 1 ≥ m = 0`).  By W (`m = 1`, `α = 0`), `ϑ₁(1) = ω̄_{Ω₁}`, and `ω̄_{Ω₁} = Ω₁·ω`
(the computation in the docstring of the axiom `vzOm1w_T` of `R2.CitedVz`: `ω̄` enumerates the additive principal
numbers that are not `ε`-numbers, `(P ∖ E) ∩ Ω₁` has order type `Ω₁`, and the least element of `P ∖ E` that is
`≥ Ω₁ = ω^{Ω₁}` is `ω^{Ω₁+1} = Ω₁·ω`).  So `Ω₁·ω` is denoted by the term `ϑ₁(1)` of `Tᵗ`.
(2) The parameters.  By S (third clause, `k = 1 ≥ m = 0`), `Subᵗ₀(ϑ₁(1)) = {ϑ₁(1)} ∪ Subᵗ₀(1)`, and `Subᵗ₀(1) = {1}`
(S, first clause: `1 < τ` is a parameter).  So `Parᵗ(Ω₁·ω) = {Ω₁·ω, 1} ∩ τ = {1}` (`Ω₁·ω ≥ Ω₁ > τ`).  As `σ ∈ E`,
`1 < σ`, so `Parᵗ(Ω₁·ω) ⊆ σ` and `Ω₁·ω ∈ Tᵗ[σ]` (D, the definition of `Tᵗ[σ]`).  Likewise `Parᵗ(1) = {1} ⊆ σ`, so
`1 ∈ Tᵗ[σ] ∩ Ω₃`.
(3) The base change.  D, third clause (`ξ = ϑ₁(η)`, `k = 1 > 0`, `η = 1 ∈ Tᵗ[σ] ∩ Ω₃`):
`π_{σ,τ}(ϑ₁(1)) = ϑ₁(π_{σ,τ}(1))`; D, first clause (`1 < σ`): `π_{σ,τ}(1) = 1`.  So `π_{σ,τ}(Ω₁·ω)` is `ϑ₁(1)` of
the system `Tᵟ` over `σ`, and there too `ϑ₁(1) = ω̄_{Ω₁} = Ω₁·ω` (W for the system over `σ`, the computation of
(1)). Proved from `CitedLu`. -/
theorem xtOm1w_TB {σ τ : Ordinal.{0}} (h : Bases σ τ) : Om1 * ω ∈ TB τ σ ∧ pi σ τ (Om1 * ω) = Om1 * ω := by
  have := luOm1_opow_TB h ((one_lt_omega0).trans (omega0_lt_inE h.1)); rwa [opow_one] at this



end Googology.Trans.PoR.InaccPsi.R2
