import Googology.Trans.PoR.InaccPsi.R2.CitedRk

set_option autoImplicit false

/-!
# A cited fact of Wilken 2007, as an axiom, ONCE: the base change `π` at the `ϑ₁`-terms `Ω₁·ω^b`, `b < ε_{Ω₁+1}`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

Same conventions as `R2.CitedRj`, `R2.CitedRk` (`Ω₁ = Om1`, `Ω₂ = OmTwo`, `Tset τ = Tᵗ`, `Tᵗ[σ] = TB τ σ`,
`π_{σ,τ} = pi σ τ`, `Bases σ τ`: `σ < τ < Ω₁` are `ε`-numbers, `ε_{Ω₁+1} = Gg.ggE`).

What is **not** restated (checked first): `R2.Cited` (`luOm1_opow_TB`: `Ω₁·ω^b ∈ Tᵗ[σ]`, `π(Ω₁·ω^b) = Ω₁·ω^b` for
`b < σ`; `pi_add`, `pi_bijOn`, `pi_vt_two` for the clauses of Def 5.1 at `+` and `ϑᵗ`), `R2.CitedLv` (`lvPi_mul`:
`π(Ω₁·β) = Ω₁·π(β)` for countable `β ≥ τ`), `R2.CitedLq` (`lqPi`: `π(Ω₁·(Ω₁·γ + β))` for countable `γ, β`), `R2.CitedLg`
(`lgPi_OmOm`), `R2.CitedRj`, `R2.CitedRk` (membership and data of `Ω₁·M + η`, no `π`), `R2.CitedLu`, `R2.CitedLt`,
`R2.CitedLz`, `R2.CitedVz`, `R2.CitedEv`, `R2.CitedEps`, `R2.CitedW`, `R2.CitedL`, `R2.CitedR1`, `R2.CitedXt`,
`R2.CitedBr`, `R2.CitedC09`, `R2.CitedCore`: **apart from `lgPi_OmOm` (`ϑ₁(Ω₁)`) and `lqPi` (`ϑ₁(Ω₁ + c)`), whose
values agree with the axiom below, no axiom gives `π` at a `ϑ₁`-term with an uncountable argument**.
The axiom below is the third clause of Def 5.1 (`k = 1`) at the arguments `b < ε_{Ω₁+1}`, read through Lemma 4.2
(`m = 1`), with the membership in both directions (Def 3.28, Lemma 3.30 at `m = 1`).  It contains `luOm1_opow_TB`
(`b < σ`) as a special case; it is used at uncountable `b` only.

Literal texts (all of [W07a]; checked against the paper):
* (P) Def 5.1: "Let `τ ∈ E` and `Tᵗ` be the notation system over `τ`.  Further, let `σ ∈ {1} ∪ (E ∩ τ)`.  We define
  `Tᵗ[σ] := {α ∈ Tᵗ | Parᵗ(α) ⊆ σ}` and `π_{σ,τ} : Tᵗ[σ] → T^σ` by the following clauses: • `π_{σ,τ}(ξ) := ξ` if
  `ξ < σ` • `π_{σ,τ}(ξ) := π_{σ,τ}(ξ₁) + π_{σ,τ}(ξ₂)` if `ξ =NF ξ₁ + ξ₂ > τ` • `π_{σ,τ}(ξ) := ϑ_k(π_{σ,τ}(η))` if
  `ξ = ϑ_k(η)` for some `k > 0` and `η ∈ Tᵗ[σ] ∩ Ω_{k+2}` • `π_{σ,τ}(ξ) := ϑ^σ(π_{σ,τ}(η))` if `ξ = ϑᵗ(η)` for some
  `η ∈ Tᵗ[σ] ∩ Ω₂`."
* (5.3) Lemma 5.3: "(b) `π_{σ,τ}` preserves `<`."
* (T) Def 3.22: "`Ω_m ⊆ T_m` • `ξ, η ∈ T_m ⇒ ξ + η ∈ T_m` • `ξ ∈ T_m ∩ Ω_{k+2} ⇒ ϑ_k(ξ) ∈ T_m` for `k ≥ m`."
* (U) Remark after Corollary 3.24: "each `T_m` again gives rise to a notation system with parameters from `Ω_m` that
  provides a unique term for every ordinal which is element of some `Tⁿ_m` where `n > m`".
* (Z) After Def 3.1: "Note that we have `ϑⁿ_m(0) = Ω_m` for `m < n`".
* (W) Def 3.4: "Let `α ↦ ω̄_α` be the enumeration function of the additive principle numbers which are not epsilon
  numbers."  Lemma 4.2: "For any `m < ω` and any `α < Ω_{m+1}` we have `ϑ_m(1 + α) = ω̄_{Ω_m+α}`".
* (S) Def 3.28: "`Subᵗ_m(α) := {α}` for parameters `α < τ`; `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ) ∪ Subᵗ_m(η)` for
  `ξ, η ∈ Tᵗ` s.t. `α =NF ξ + η > τ`; `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ)` if `k ≥ m`, `{α}` if `k < m`, for `α = ϑ_k(ξ)`
  where `ξ ∈ Tᵗ ∩ Ω_{k+2}`.  …  `P_m(α) := Subᵗ_m(α) ∩ P ∩ [Ω_m, Ω_{m+1})` and `α^{*m} := max(P_m(α) ∪ {0})`.  The
  set of parameters `< τ` used in the unique term denoting some `α ∈ Tᵗ` is denoted by `Parᵗ(α) := Subᵗ₀(α) ∩ τ`."
* (L) Lemma 3.30: "For `m < ω` the function `ϑ_m ↾ Tᵗ ∩ Ω_{m+2}` is 1-1 and has values in `P ∩ [Ω_m, Ω_{m+1})`.  Let
  `α, γ ∈ Tᵗ ∩ Ω_{m+2}`.  Then `α^{*m} < ϑ_m(α)` and `ϑ_m(α) < ϑ_m(γ) ⇔ α < γ ∧ α^{*m} < ϑ_m(γ) ∨ ϑ_m(α) ≤ γ^{*m}`."
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- **[W07a] Def 5.1 (first and third clauses), Lemma 5.3 (b), Def 3.22, the Remark after Corollary 3.24, the remark
after Def 3.1, Def 3.4 with Lemma 4.2 (`m = 1`), Def 3.28, Lemma 3.30 (`m = 1`)** (texts P, 5.3, T, U, Z, W, S, L): for
bases `σ < τ` and `b < ε_{Ω₁+1}`: `Ω₁·ω^b ∈ Tᵗ[σ]` iff `b ∈ Tᵗ[σ]`, and then `π_{σ,τ}(Ω₁·ω^b) = Ω₁·ω^{π_{σ,τ}(b)}`.

Our steps.
* (★1) `ϑ₁(0) = Ω₁` (Z) and `ϑ₁(m) = ω^{Ω₁+m}` for `1 ≤ m < ε_{Ω₁+1}` (W: `ϑ₁(1 + a) = ω̄_{Ω₁+a}`; the additive
  principal numbers below `Ω₁ = ω^{Ω₁}` that are not `ε`-numbers have order type `Ω₁`, and there is no `ε`-number in
  `(Ω₁, ε_{Ω₁+1})`, so `ω̄_{Ω₁+a} = ω^{Ω₁+1+a}`); hence `Ω₁·ω^m = ω^{Ω₁+m} = ϑ₁(m)` for every `m < ε_{Ω₁+1}`, and
  `m ↦ ϑ₁(m)` is strictly increasing on `[0, Ω₂)` (W: `ω̄` is an enumeration).  These hold over every base (the
  `ϑ₁`-function does not depend on `τ`: `Ω₀ = τ` enters `C_m` only for `m = 0`).
* (★2) `ε_{Ω₁+1} ≤ ϑ₁(Ω₂)`: `a₀ = 0`, `a_{k+1} = ϑ₁(a_k)` (`a₁ = Ω₁`, `a_{k+1} = ω^{Ω₁+a_k}`, `sup_k a_k = ε_{Ω₁+1}` by
  ★1) lie in `Tᵗ ∩ Ω₂` (T); `Ω₂ = ϑ₂(0) ∈ Tᵗ` (Z, T), `(Ω₂)^{*1} = 0` (S); by induction on `k`, `P₁(a_k) ⊆ {a₁, …, a_k}`
  (S), so `(a_k)^{*1} = a_k < ϑ₁(Ω₂)` and L (`m = 1`, `α = a_k`, `γ = Ω₂`) gives `a_{k+1} < ϑ₁(Ω₂)`.
* (★3) **The term of `Ω₁·ω^b`.**  Let `s := Ω₁·ω^b ∈ Tᵗ` (`b < ε_{Ω₁+1}`).  By U its term is unique; `s` is additive
  principal (so not an `=NF`-sum) in `[Ω₁, Ω₂)`, so it is not a parameter (`< τ`), not a `ϑ₀`-term (values `< Ω₁`, L
  at `m = 0`), not a `ϑ_k`-term for `k ≥ 2` (values `≥ Ω₂`, L): it is `ϑ₁(ζ)` with `ζ ∈ Tᵗ ∩ Ω₃` (T).  If `ζ ≥ Ω₂`:
  `ζ = Ω₂`, or L (`α = Ω₂ < γ = ζ`, `(Ω₂)^{*1} = 0 < ϑ₁(ζ)`) gives `ϑ₁(Ω₂) < ϑ₁(ζ)`; either way `ε_{Ω₁+1} ≤ ϑ₁(Ω₂) ≤
  s < ε_{Ω₁+1}` (★2), impossible.  So `ζ < Ω₂` and `ϑ₁(ζ) = ϑ₁(b)` gives `ζ = b` (★1, injective on `[0, Ω₂)`).  So
  `s ∈ Tᵗ` iff `b ∈ Tᵗ` (⇐: T, third clause, `k = 1 ≥ 0`, `b ∈ Tᵗ ∩ Ω₃`), and then the term of `s` is `ϑ₁(b)`.
* (★4) **Parameters.**  By S (third clause, `k = 1 ≥ 0`), `Subᵗ₀(ϑ₁(b)) = {ϑ₁(b)} ∪ Subᵗ₀(b)`, and `ϑ₁(b) ≥ Ω₁ > τ`,
  so `Parᵗ(s) = Subᵗ₀(b) ∩ τ = Parᵗ(b)`.  Hence `s ∈ Tᵗ[σ]` iff `b ∈ Tᵗ[σ]` (P: `Tᵗ[σ] = {α ∈ Tᵗ | Parᵗ(α) ⊆ σ}`).
* (★5) **The value of `π`.**  For `b ∈ Tᵗ[σ]` (`b < Ω₃`): P, third clause (`k = 1 > 0`, `η = b ∈ Tᵗ[σ] ∩ Ω₃`),
  `π_{σ,τ}(s) = ϑ₁(π_{σ,τ}(b))`.  The `a_k` of ★2 lie in `Tᵗ[σ]` (`Parᵗ(a_k) ⊆ {0}`, S, `0 < σ`) and `π_{σ,τ}(a_k) =
  a_k` (P, first clause at `a₀ = 0`, third clause at `a_{k+1}`, by induction).  As `b < ε_{Ω₁+1} = sup_k a_k`, `b < a_k`
  for some `k`, so `π_{σ,τ}(b) < π_{σ,τ}(a_k) = a_k < ε_{Ω₁+1}` (5.3).  So by ★1 (over the base `σ`) `ϑ₁(π_{σ,τ}(b)) =
  Ω₁·ω^{π_{σ,τ}(b)}`, i.e. `π_{σ,τ}(Ω₁·ω^b) = Ω₁·ω^{π_{σ,τ}(b)}`. -/
axiom siOm1_opow_TB {σ τ b : Ordinal.{0}} (h : Bases σ τ) (hbE : b < Gg.ggE) :
    (Om1 * ω ^ b ∈ TB τ σ ↔ b ∈ TB τ σ) ∧ (b ∈ TB τ σ → pi σ τ (Om1 * ω ^ b) = Om1 * ω ^ pi σ τ b)

end Googology.Trans.PoR.InaccPsi.R2
