import Googology.Trans.PoR.InaccPsi.R2.OffPhi

/-!
# More cited facts of Wilken 2007, as axioms (for offset terms with `ω`-powers)

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.

Same conventions as `R2.Cited` (`Ω₁ = ω₁`, `Tset τ = Tᵗ`, `Par τ = Parᵗ`, `pi σ τ = π_{σ,τ}`, all bases
countable).  `Ω₁ = ω₁` is the choice, made in `R2.Cited`, of "an uncountable regular cardinal number
greater than `τ`" of [W07a] §3; `vt_wbar` states [W07a] Lemma 4.2 for every `α < Ω₁`, as the paper does
(`ϑ₀` is a function on all of `Ω₂`), although below it is used only at terms.  [W07b] Theorem 2.2 is
proved in another paper, which is not used; here, as in `R2.Cited` (`le1R_two_iff`, the case `ξ = α`),
it is cited from its statement in [W07b] §2.

* `le1R_thm22`: [W07b] Theorem 2.2 ("For `α ∈ On` and `ξ ∈ (0, α]` we have
  `α ≤₁ α + ξ ⇔ α = ω^{α'}` for some `α'` with `logend(α') ≥ ξ`").  `logend(α')` is "the exponent of the
  last summand of the Cantor normal form representation of `α'`"; for `α' ≠ 0` this is `lg α'`
  (`lg α' = sup{k | ω^k ∣ α'}`).  For `α' = 0` the Cantor normal form has no summand, so no `ξ > 0`
  satisfies the condition; the statement below asks `α' ≠ 0`, which is the same.
* `vt` (constant): `ϑᵗ = ϑ₀` over `τ` ([W07a] Def 3.22, Convention 3.25).
* `NonEAP`, `wbar`: "`α ↦ ω̄_α` the enumeration function of the additive principal numbers which are
  not epsilon numbers" ([W07a] Def 3.4); defined here (no axiom).
* `vt_wbar`: [W07a] Lemma 4.2 with `m = 0` ("For any `m < ω` and any `α < Ω_{m+1}` we have
  `ϑ_m(1 + α) = ω̄_{Ω_m + α}`"; "for `m = 0` by convention we have `Ω₀ = τ` and `ϑ₀ = ϑᵗ`").
* `vt_mem`: [W07a] Def 3.22, third clause with `k = m = 0` ("`ξ ∈ T_m ∩ Ω_{k+2} ⇒ ϑ_k(ξ) ∈ T_m`"), and
  [W07a] Def 3.28 (`Subᵗ₀(ϑ₀(ξ)) = {ϑ₀(ξ)} ∪ Subᵗ₀(ξ)`, `Parᵗ = Subᵗ₀ ∩ τ`) with Lemma 3.30 (the values
  of `ϑ₀` lie in `[Ω₀, Ω₁) = [τ, Ω₁)`, so `ϑᵗ(ξ) ∉ τ`): `Parᵗ(ϑᵗ(ξ)) = Parᵗ(ξ)`.
* `pi_vt`: [W07a] Def 5.1, fourth clause ("`π_{σ,τ}(ξ) := ϑ^σ(π_{σ,τ}(η))` if `ξ = ϑᵗ(η)` for some
  `η ∈ Tᵗ[σ] ∩ Ω₂`").

Here `ξ < Ω₁` is used for `ξ ∈ Ω₂` (`Ω₁ < Ω₂`); every argument used below is countable.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- **[W07b] Theorem 2.2**, as stated in [W07b] §2: for `ξ ∈ (0, α]`,
`α ≤₁ α + ξ` iff `α = ω^{α'}` for some `α'` with `logend(α') ≥ ξ` (here `α' ≠ 0`, `logend = lg`,
see the module docstring).  Only the statement is cited; the proof of Theorem 2.2 is in a paper that
is not used here. -/
axiom le1R_thm22 {a ξ : Ordinal.{0}} (h0 : 0 < ξ) (hξ : ξ ≤ a) :
    le1R a (a + ξ) ↔ ∃ a', a' ≠ 0 ∧ a = ω ^ a' ∧ ξ ≤ lg a'

/-- `ϑᵗ` (`ϑ₀` of [W07a] Def 3.22 over the base `τ`, Convention 3.25).  A constant without
definition. -/
axiom vt : Ordinal.{0} → Ordinal.{0} → Ordinal.{0}

/-- The additive principal numbers which are not epsilon numbers ([W07a] Def 3.4). -/
def NonEAP : Set Ordinal.{0} := {a | Indec a ∧ ¬ InE a}

/-- `ω̄_α`: the enumeration function of `NonEAP` ([W07a] Def 3.4). -/
noncomputable def wbar : Ordinal.{0} → Ordinal.{0} := enumOrd NonEAP

/-- **[W07a] Lemma 4.2** (`m = 0`): `ϑᵗ(1 + α) = ω̄_{τ+α}` for `α < Ω₁`. -/
axiom vt_wbar {τ α : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hα : α < Om1) :
    vt τ (1 + α) = wbar (τ + α)

/-- **[W07a] Def 3.22** (third clause, `k = m = 0`) and **Def 3.28** with **Lemma 3.30**: for
`ξ ∈ Tᵗ ∩ Ω₁`, `ϑᵗ(ξ) ∈ Tᵗ` and `Parᵗ(ϑᵗ(ξ)) = Parᵗ(ξ)`. -/
axiom vt_mem {τ ξ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hξ : ξ ∈ Tset τ) (hξ1 : ξ < Om1) :
    vt τ ξ ∈ Tset τ ∧ Par τ (vt τ ξ) = Par τ ξ

/-- **[W07a] Def 5.1**, fourth clause: `π_{σ,τ}(ϑᵗ(η)) = ϑ^σ(π_{σ,τ}(η))` for `η ∈ Tᵗ[σ] ∩ Ω₁`. -/
axiom pi_vt {σ τ ξ : Ordinal.{0}} (h : Bases σ τ) (hξ : ξ ∈ TB τ σ) (hξ1 : ξ < Om1) :
    pi σ τ (vt τ ξ) = vt σ (pi σ τ ξ)

end Googology.Trans.PoR.InaccPsi.R2
