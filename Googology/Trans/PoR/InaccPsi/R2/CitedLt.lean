import Googology.Trans.PoR.InaccPsi.R2.CitedLz
import Googology.Trans.PoR.InaccPsi.R2.CitedLu
import Googology.Trans.PoR.InaccPsi.R2.EpsQ
import Googology.Trans.PoR.InaccPsi.R2.EvV

/-!
# Cited facts of Wilken 2007, as axioms: the `R₁⁺`-reach of `ϑᵗ(Ω₁·ω + η)`, and `ϑᵗ` at `Ω₁·(ω+1)`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.

Same conventions as `R2.Cited`, `R2.CitedEv`, `R2.CitedVz`, `R2.CitedLz` (`Ω₁ = ω₁`, `Ω₂ = ω₂ = OmTwo`,
`Tset τ = Tᵗ = T₀` over the base `τ`, `vt τ = ϑᵗ = ϑ₀`, `lhT τ = lhᵗ`, `lg = logend`, every base `τ` a countable
`ε`-number).  The axioms speak of `vt τ` only at elements of `Tᵗ ∩ Ω₂` (`Ω₁·ω + η` with `η ∈ Tᵗ ∩ Ω₁`, and
`Ω₁·(ω+1)`).

Literal texts used below:
* (H) [W07b] Def 4.1: "For `α ∈ Tᵗ ∩ Ω₁` we define an ordinal `lhᵗ(α) ∈ Tᵗ ∩ Ω₁` by recursion on `hᵗ(α)` as
  follows. • `lhᵗ(α) := 0` if `α ≤ τ` • `lhᵗ(α) := α` if `α =NF α₁ + α₂ ≥ τ` • If `α = ϑᵗ(Δ + η) > τ` we set
  `δ := (λᵗ_α)^*`. • `lhᵗ(α) := α + λᵗ_α` if `δ ≤ α`, i.e. `Δ < ϑ₁(1)` • If `δ > α` let `(α = δ₀, …, δ_m = δ)` be
  the `α`-localization of `δ` in `Tᵗ`.  `lhᵗ(α) := lhᵗ(δᵢ) + λᵗ_α` if `i := cr(α, δ) < m`, `lhᵗ(δ) + ρ` where
  `ρ := −δ + λᵗ_α` otherwise."; after it: "Note that `(λᵗ_α)^*` is the maximum additive principal number less than
  or equal to `λᵗ_α`."
* (T) [W07a] Def 3.22: "`T_m` is defined inductively as follows: • `Ω_m ⊆ T_m` • `ξ, η ∈ T_m ⇒ ξ + η ∈ T_m`
  • `ξ ∈ T_m ∩ Ω_{k+2} ⇒ ϑ_k(ξ) ∈ T_m` for `k ≥ m`."
* (Θ) [W07a] Theorem 3.23: "For `m < ω` we have `T_m = ⋃_{n>m} Tⁿ_m` and `T_m ∩ Ω_{m+1} = θ_m =
  sup_{n≥m} ϑ_m(⋯(ϑ_n(0))⋯)`" (so `Tᵗ ∩ Ω₁` is an initial segment of the ordinals).
* (L) [W07a] Lemma 3.30: "For `m < ω` the function `ϑ_m ↾ Tᵗ ∩ Ω_{m+2}` is 1-1 and has values in
  `P ∩ [Ω_m, Ω_{m+1})`.  Let `α, γ ∈ Tᵗ ∩ Ω_{m+2}`.  Then `α^{*m} < ϑ_m(α)` and
  `ϑ_m(α) < ϑ_m(γ) ⇔ α < γ ∧ α^{*m} < ϑ_m(γ) ∨ ϑ_m(α) ≤ γ^{*m}`."
* (U) [W07a] remark after Cor 3.24: "each `T_m` again gives rise to a notation system with parameters from `Ω_m`
  that provides a unique term for every ordinal which is element of some `Tⁿ_m` where `n > m` (again refining the
  clause for ordinal addition as we did for the systems `Tⁿ_m`)".  §2: "We write `ξ =ANF ξ₁ + ⋯ + ξₙ` if
  `ξ₁, …, ξₙ ∈ P`, `ξ₁ ≥ ⋯ ≥ ξₙ` (`ξ` given in additive normal form).  For convenience we also write
  `ξ =NF η + ρ` provided `η =ANF η₁ + ⋯ + ηₙ` for some `η₁, …, ηₙ`, and `ηₙ ≥ ρ ∈ P`."
* (Z) [W07a] remark after Def 3.1: "Note that we have `ϑⁿ_m(0) = Ω_m` for `m < n`" (so `ϑ₁(0) = Ω₁`); proof of
  Lemma 3.27: "We have `ϑ₀(0) = τ`".
* (S) [W07a] Def 3.28: "`Subᵗ_m(α) := {α}` for parameters `α < τ`; `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ) ∪ Subᵗ_m(η)` for
  `ξ, η ∈ Tᵗ` s.t. `α =NF ξ + η > τ`; `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ)` if `k ≥ m` (`{α}` if `k < m`) for
  `α = ϑ_k(ξ)` where `ξ ∈ Tᵗ ∩ Ω_{k+2}`.  We define the additive principal parts of level `m` of `α ∈ Tᵗ` by
  `P_m(α) := Subᵗ_m(α) ∩ P ∩ [Ω_m, Ω_{m+1})` and `α^{*m} := max(P_m(α) ∪ {0})`."
* (C) [W07a] Convention 4.1: "Given a term `α = ϑᵗ(ξ) ∈ Tᵗ` we introduce the notational convention that
  `α = ϑᵗ(Δ + η)` automatically means that `ξ = Δ + η` is a decomposition such that `Ω₁ | Δ` and `η < Ω₁`. …
  In a situation where some `α = ϑᵗ(Δ + η)` is fixed, we will write `α⁺` to denote the ordinal `ϑᵗ(Δ + η + 1)`."
* (E) [W07a] Lemma 4.3: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ`.  Then `τ < α ∈ E ⇔ Δ > 0`."
* (W) [W07a] Def 3.4: "Let `α ↦ ω̄_α` be the enumeration function of the additive principle numbers which are not
  epsilon numbers."  Lemma 4.2: "For any `m < ω` and any `α < Ω_{m+1}` we have `ϑ_m(1 + α) = ω̄_{Ω_m+α}`" (proof:
  "for `m = 0` by convention we have `Ω₀ = τ` and `ϑ₀ = ϑᵗ`").
* (G) [W07a] Def 4.11: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ` such that `α > τ` be given.  We define `ζᵗ_α := logend(η)` if
  `η < sup_{σ<η} ϑᵗ(Δ + σ)`, `0` otherwise."
* (D) [W07a] Def 6.1: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ`.  The restriction of `Tᵗ` to `α`, written as `Tᵗ_α`, is defined by
  `Tᵗ_α := {β ∈ Tᵗ | β^{*τ} < α}`."
* (I) [W07a] Def 7.1: "Let `α = ϑᵗ(Δ + η)` where `Δ > 0`.  We define `ι_{τ,α} : Tᵗ_α → T^α` by recursion on the
  definition of `Tᵗ` as follows: • `ι_{τ,α}(ξ) := ξ` if `ξ < α` • `ι_{τ,α}(ξ) := ι_{τ,α}(ξ₁) + ι_{τ,α}(ξ₂)` if
  `ξ =NF ξ₁ + ξ₂ > Ω₁` • `ι_{τ,α}(ξ) := ϑ_k(ι_{τ,α}(η))` if `ξ = ϑ_{k+1}(η)` where `k < ω`.  Note that
  `ι_{τ,α}(ϑ₁(η)) = ϑ^α(ι_{τ,α}(η))`."
* (Λ) [W07a] Def 7.5: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ` such that `α > τ`.  We define `λᵗ_α := ι_{τ,α}(Δ) + ζᵗ_α` if
  `α ∈ E`, `ζᵗ_α` otherwise."
* (LOC) [W07a] Def 4.6: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ`, `α ≥ τ`.  We define a finite sequence of ordinals as follows.
  Set `α₀ := τ`.  Suppose that `αₙ` is already defined and `αₙ < α`.  Let `αₙ₊₁` be the element `ϑᵗ(ξ)` of
  `Pᵗ(α) − (αₙ + 1)` with maximal `ξ`.  This yields a finite sequence `τ = α₀ < ⋯ < αₙ = α` for some `n < ω` which
  we call the `τ`-localization of `α`."  Convention 6.6: "we call the sequence `(α, β₁^{t^α_τ}, …, β_m^{t^α_τ} =
  β^{t^α_τ})` the `α`-localization of `β^{t^α_τ} = β` in `Tᵗ`" (`(α = β₀, …, β_m = β)` the `α`-localization of `β`
  in `T^α`).
* (TR) [W07a] Lemma 6.3: "We have • `α⁺ = ϑ^α(Δ)`, • the restriction of `t^τ_α` to `Tᵗ_{α⁺}` is the identity, and
  • the restriction of `t^α_τ` to `T^α_{α⁺}` is the identity."
* (CR) [W07a] Def 7.15: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ`, `α ≥ τ`, and `(τ = α₀, …, αₙ = α)` be the `τ`-localization of
  `α`.  Define `cr(τ, α) := min{i ∈ {1, …, n − 1} | λᵗ_{αᵢ} ≥ α}` if that exists, `n` otherwise."
* (W07a Lemma 4.3, proof) "First, suppose that `ζᵗ_α = 0`.  Then `λᵗ_α` is a proper multiple of `α`, namely
  `λᵗ_α = α · ξ` for `ξ > 0` such that `Δ = Ω · ξ`.  This follows by a straightforward induction along the definition
  of `ι_{τ,α}`."  (Used only as a check of the value `ι_{τ,α}(Ω₁·ω) = α·ω` below.)

Facts used below (our steps; (★1), (★w) are those of `R2.CitedEv`, `R2.CitedLz`):
* (★1) For `η ∈ Tᵗ ∩ Ω₁`: `η^* ≤ η`.
* (★1) also: every additive component of `η ∈ Tᵗ ∩ Ω₁` is `< τ` or `≤ η^*` (the proof in `R2.CitedEv`).
* (★w) For `η ∈ Tᵗ ∩ Ω₁`: `Ω₁·ω + η ∈ Tᵗ ∩ Ω₂` and `(Ω₁·ω + η)^* = η^*`; the term of `Ω₁·ω` is `ϑ₁(1) = ω̄_{Ω₁}`
  (W with `m = 1`, `α = 0`), and `(Ω₁·ω)^* = 0`.
* (★w1) `γ₁ := Ω₁·(ω+1) = Ω₁·ω + Ω₁ ∈ Tᵗ ∩ Ω₂` and `γ₁^* = 0`.  The term: `ϑ₁(1) = Ω₁·ω` (★w) and `ϑ₁(0) = Ω₁` (Z)
  lie in `T₀` (T, third clause, `k = 1 ≥ 0`, `0, 1 < τ`), so `γ₁ = ϑ₁(1) + ϑ₁(0) ∈ T₀` (T, second clause), and
  `γ₁ < Ω₁·ω·2 < Ω₂`.  `γ₁ =NF ϑ₁(1) + ϑ₁(0)` (§2: `ϑ₁(1) = Ω₁·ω ∈ P`, `Ω₁·ω ≥ Ω₁ ∈ P`), so (S)
  `Subᵗ₀(γ₁) = {γ₁} ∪ {ϑ₁(1), 1} ∪ {ϑ₁(0), 0}`; none of these lies in `P ∩ [τ, Ω₁)` (`γ₁, Ω₁·ω, Ω₁ ≥ Ω₁`; `0, 1 < τ`),
  so `P₀(γ₁) = ∅` and `γ₁^* = 0`.  In Lean `Ω₁·(ω+1)` is `Om1 * (ω + 1)`.

The axioms (5 facts, no constant):
1. `ltLhT_w_lim` (H, …): for `η ∈ Tᵗ ∩ Ω₁`, `η ≠ 0`, `η < ϑᵗ(Ω₁·ω + η)` and `η < ϑᵗ(Ω₁·ω + σ)` for some `σ < η`,
   `lhᵗ(ϑᵗ(Ω₁·ω + η)) = ϑᵗ(Ω₁·ω + η)·ω + logend(η)`.  For `η = 0` this is the axiom `vzLhT_w` of `R2.CitedVz`.
2. `ltLt_vt_self_w` (L, E, ★w, ★1): `η < ϑᵗ(Ω₁·ω + η)` for every `η ∈ Tᵗ ∩ Ω₁` (the level-`ω` form of the axiom
   `vzLt_vt_self` of `R2.CitedVz`).
3. `ltVt_lt_w1` (L, ★w, ★w1, ★1): `ϑᵗ(Ω₁·ω + η') < ϑᵗ(Ω₁·(ω+1))` when `η' < ϑᵗ(Ω₁·(ω+1))`.
4. `ltLt_of_vt_lt_w1` (L, ★w1): `ϑᵗ(ξ) < ϑᵗ(Ω₁·(ω+1))` gives `ξ < Ω₁·(ω+1)`.
5. `ltLhT_w1` (H, …, ★w1): `lhᵗ(ϑᵗ(Ω₁·(ω+1))) = ϑᵗ(Ω₁·(ω+1))·ω + ϑᵗ(Ω₁·(ω+1))`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

private theorem luOld_omega_lt_E {τ : Ordinal.{0}} (hτ : InE τ) : (ω : Ordinal.{0}) < τ := omega0_lt_inE hτ

private theorem luOld_one_lt_E {τ : Ordinal.{0}} (hτ : InE τ) : (1 : Ordinal.{0}) < τ :=
  one_lt_omega0.trans (luOld_omega_lt_E hτ)

private theorem luOld_omega_one_lt_E {τ : Ordinal.{0}} (hτ : InE τ) : (ω : Ordinal.{0}) + 1 < τ :=
  (inE_indec hτ).add_lt (luOld_omega_lt_E hτ) (luOld_one_lt_E hτ)

private theorem luOld_zero_T {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) :
    (0 : Ordinal.{0}) ∈ Tset τ := mem_T_of_le hτ hτ1 zero_le

private theorem luOld_lev_lt {τ β' η' β η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1)
    (hβ'β : β' < β) (hβ : β < τ) (hη' : η' ∈ Tset τ) (hη'1 : η' < Om1)
    (hη : η ∈ Tset τ) (hη1 : η < Om1) (h : η' < vt τ (Om1 * β + η)) :
    vt τ (Om1 * β' + η') < vt τ (Om1 * β + η) := by
  refine luVt_lt hτ hτ1 (hβ'β.trans hβ) hη' hη'1 hβ hη hη1 ?_ h
  calc Om1 * β' + η' < Om1 * β' + Om1 := (add_lt_add_iff_left _).2 hη'1
    _ = Om1 * (β' + 1) := by rw [mul_add_one]
    _ ≤ Om1 * β := mul_le_mul_right (Order.add_one_le_of_lt hβ'β) Om1
    _ ≤ Om1 * β + η := le_self_add

/-- **[W07b] Def 4.1, the case `δ > α` with `cr(α, δ) = m`, with [W07a] Def 7.5, Def 7.1, Def 6.1, Def 4.11,
Def 4.6, Def 7.15, Convention 6.6, Convention 4.1, Lemma 6.3, Lemma 4.2, Lemma 4.3, Def 3.4, Def 3.28, Def 3.22,
Theorem 3.23** (texts H, Λ, I, D, G, LOC, CR, TR, C, W, E, S, T, Θ): for `η ∈ Tᵗ ∩ Ω₁`, `η ≠ 0`, with
`η < ϑᵗ(Ω₁·ω + η)` and `η < ϑᵗ(Ω₁·ω + σ)` for some `σ < η`, and `α := ϑᵗ(Ω₁·ω + η)`:
`lhᵗ(α) = α·ω + logend(η)`.

Our steps.  `Δ := Ω₁·ω = ϑ₁(1)` (★w; the axiom `vzOm1w_T` of `R2.CitedVz`), `α = ϑᵗ(Δ + η)` (C: `Ω₁ | Δ`,
`η < Ω₁`); `Δ + η ∈ Tᵗ ∩ Ω₂` (★w), so `α ∈ Tᵗ` (T, third clause), and `τ < α ∈ E` (E, `Δ > 0`).
* `ζᵗ_α` (G): for the given `σ < η`, `σ ∈ Tᵗ` (Θ: `Tᵗ ∩ Ω₁` is an initial segment and `η ∈ Tᵗ ∩ Ω₁`), so
  `ϑᵗ(Δ + σ)` is a term (★w, T), and `η < ϑᵗ(Δ + σ) ≤ sup_{σ'<η} ϑᵗ(Δ + σ')`.  Hence `ζᵗ_α = logend(η)`.
* `ι_{τ,α}(Δ)` (I): `Δ ∈ Tᵗ_α` (D: `Δ^* = 0 < α`, ★w).  By the note after Def 7.1,
  `ι_{τ,α}(ϑ₁(1)) = ϑ^α(ι_{τ,α}(1))`, and `ι_{τ,α}(1) = 1` (first clause, `1 < α`).  Lemma 4.2 at the base `α`
  (`m = 0`, `Ω₀ = α`): `ϑ^α(1) = ω̄_α`.  By Def 3.4, `(P ∖ E) ∩ α` has order type `α` (`c ↦ ω^{c+1}` maps `α`
  strictly increasingly into it, `α ∈ E`), so `ω̄_α` is the least element of `P ∖ E` that is `≥ α`, which is
  `ω^{α+1} = α·ω`.  So `ι_{τ,α}(Δ) = α·ω` (in accordance with the proof of [W07a] Lemma 4.3 quoted above:
  `Δ = Ω·ω`, `λ = α·ω` when `ζ = 0`).
* `λᵗ_α` (Λ): `α ∈ E`, so `λᵗ_α = α·ω + logend(η)`.
* `δ = (λᵗ_α)^*` (H, the note): `logend(η) ≤ η < α` (hypothesis `η < ϑᵗ(Ω₁·ω + η)`), so
  `α·ω ≤ λᵗ_α < α·ω + α ≤ α·ω·2`.  `α·ω = ω^{α+1}` is additive principal, and the next additive principal number
  is `ω^{α+2} = α·ω·ω > α·ω·2`; so `δ = α·ω`, and `δ > α`: the second branch of (H) applies.
* The `α`-localization of `δ` in `Tᵗ` (LOC, Convention 6.6): in `T^α`, `δ = ω̄_α = ϑ^α(1)` and
  `Sub^α₀(ϑ^α(1)) = {ϑ^α(1), 1}` (S; `1 < α` is a parameter), so the only `ϑ`-subterm of `δ` is `δ` itself and the
  localization is `(α = δ₀, δ₁ = δ)`, `m = 1`.  `δ ∈ T^α_{α⁺}` (D: `δ^{*α} = δ < α⁺ = ϑ^α(Δ)`, TR; `α⁺ = ϑᵗ(Δ + η + 1)`
  (C) is an `ε`-number above `α` (E and [W07a] Lemma 3.30), so above `α·ω`), hence `δ^{t^α_τ} = δ` (TR).
* `cr(α, δ)` (CR with `n = m = 1`): `{1, …, n − 1}` is empty, so `cr(α, δ) = m`, and (H) gives
  `lhᵗ(α) = lhᵗ(δ) + ρ` with `ρ := −δ + λᵗ_α = −(α·ω) + α·ω + logend(η) = logend(η)`.
* `lhᵗ(δ)` (H) for `δ = α·ω ∈ Tᵗ` (`δ < α⁺`, Θ): `δ` is additive principal and not in `E`, so `δ = ϑᵗ(ξ_δ)` with
  `ξ_δ < Ω₁` (E, C: `Δ_δ = 0`); Lemma 4.2 (`m = 0`): `ϑᵗ(1 + ξ') = ω̄_{τ+ξ'}` and `ω̄_α = δ` give `τ + ξ' = α`,
  `ξ' = α` (`α` additive principal `> τ`), `ξ_δ = 1 + α = α`.  `λᵗ_δ = ζᵗ_δ` (Λ, `δ ∉ E`), and `ζᵗ_δ = 0` (G):
  every `σ' < α` has `ϑᵗ(σ') < α` (`ϑᵗ(1 + σ'') = ω̄_{τ+σ''}` with `τ + σ'' < α`, and `ω̄` maps `α` into `α`), so
  `sup_{σ'<α} ϑᵗ(σ') ≤ α` and `α < sup` fails.  So `(λᵗ_δ)^* = 0 ≤ δ` and `lhᵗ(δ) = δ + λᵗ_δ = δ` (first branch).
So `lhᵗ(α) = δ + ρ = α·ω + logend(η)`.  (For `η = 0`, `ζᵗ_α = 0` and the same steps give the axiom `vzLhT_w`.)
Proved from `CitedLu` (`luLhT_inf` at `β = ω`, and the `R₁⁺`-reach of `α·ω = ω^{α+1}` from [W07b] Theorem 2.2
and Theorem 5.3). -/
theorem ltLhT_w_lim {τ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hη : η ∈ Tset τ) (hη1 : η < Om1)
    (hη0 : η ≠ 0) (hself : η < vt τ (Om1 * ω + η)) (hlim : ∃ σ, σ < η ∧ η < vt τ (Om1 * ω + σ)) :
    lhT τ (vt τ (Om1 * ω + η)) = vt τ (Om1 * ω + η) * ω + lg η := by
  have _ := hη0
  have _ := hself
  have h := luLhT_inf hτ hτ1 le_rfl (luOld_omega_lt_E hτ) hη hη1
  rw [lkcLog_omega, opow_one, lkcZeta_lim hlim, Ordinal.add_sub_cancel,
    lkcLhT_mul_omega hτ hτ1 one_lt_omega0.le (luOld_omega_lt_E hτ) hη hη1] at h
  exact h

/-- **[W07a] Lemma 3.30 (`α^* < ϑ₀(α)`), Lemma 4.3, Def 3.28** (texts L, E, S, ★w, ★1): for `η ∈ Tᵗ ∩ Ω₁`,
`η < ϑᵗ(Ω₁·ω + η)`.

Our steps.  `γ := Ω₁·ω + η ∈ Tᵗ ∩ Ω₂` (★w).  Lemma 3.30 (`m = 0`): `γ^* < ϑ₀(γ)`, and `γ^* = η^*` (★w).  By Lemma 4.3
(`Δ = Ω₁·ω > 0`), `τ < ϑ₀(γ) ∈ E ⊆ P`.  By (★1) every additive component of `η` is `< τ` or `≤ η^*`, so it is
`< ϑ₀(γ)`; as `ϑ₀(γ)` is additive principal, `η < ϑ₀(γ)` (for `η = 0` as `ϑ₀(γ) > τ > 0`).  (For `Ω₁·n + η`,
`1 ≤ n < ω`, this is the axiom `vzLt_vt_self` of `R2.CitedVz`, with the same steps.) Proved from `CitedLu`. -/
theorem ltLt_vt_self_w {τ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hη : η ∈ Tset τ)
    (hη1 : η < Om1) : η < vt τ (Om1 * ω + η) :=
  luLt_vt_self hτ hτ1 one_lt_omega0.le (luOld_omega_lt_E hτ) hη hη1



/-- **[W07a] Lemma 3.30, the direction `⇐`, at `γ = Ω₁·(ω+1)`, with Def 3.28** (texts L, S, ★w, ★w1, ★1): for
`η' ∈ Tᵗ ∩ Ω₁` with `η' < ϑᵗ(Ω₁·(ω+1))`, `ϑᵗ(Ω₁·ω + η') < ϑᵗ(Ω₁·(ω+1))`.

Our steps.  `α := Ω₁·ω + η' ∈ Tᵗ ∩ Ω₂` (★w) and `γ := Ω₁·(ω+1) ∈ Tᵗ ∩ Ω₂` (★w1); `α < Ω₁·ω + Ω₁ = γ` (`η' < Ω₁`).
By (★w) and (★1), `α^* = η'^* ≤ η' < ϑ₀(γ)`.  So the first disjunct of the right side of Lemma 3.30 (`m = 0`) holds:
`ϑ₀(α) < ϑ₀(γ)`. Proved from `CitedLu`. -/
theorem ltVt_lt_w1 {τ η' : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hη' : η' ∈ Tset τ)
    (hη'1 : η' < Om1) (h : η' < vt τ (Om1 * (ω + 1))) : vt τ (Om1 * ω + η') < vt τ (Om1 * (ω + 1)) := by
  rw [← add_zero (Om1 * (ω + 1))] at h ⊢
  exact luOld_lev_lt hτ hτ1 (lt_add_one ω) (luOld_omega_one_lt_E hτ) hη' hη'1 (luOld_zero_T hτ hτ1)
    (Ordinal.omega_pos 1) h



/-- **[W07a] Lemma 3.30, the direction `⇒`, at `γ = Ω₁·(ω+1)`, with Def 3.28** (texts L, S, ★w1): for
`ξ ∈ Tᵗ ∩ Ω₂`, `ϑᵗ(ξ) < ϑᵗ(Ω₁·(ω+1))` implies `ξ < Ω₁·(ω+1)`.

Our steps.  `γ := Ω₁·(ω+1) ∈ Tᵗ ∩ Ω₂` and `γ^* = 0` (★w1).  Lemma 3.30 (`m = 0`, `α = ξ`): `ϑ₀(ξ) < ϑ₀(γ)` gives
`ξ < γ ∧ ξ^* < ϑ₀(γ)` or `ϑ₀(ξ) ≤ γ^* = 0`; the second is impossible (`ϑ₀(ξ) ∈ P`, so `> 0`).  So `ξ < γ`. Proved from `CitedLu`. -/
theorem ltLt_of_vt_lt_w1 {τ ξ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hξ : ξ ∈ Tset τ)
    (hξ2 : ξ < OmTwo) (h : vt τ ξ < vt τ (Om1 * (ω + 1))) : ξ < Om1 * (ω + 1) := by
  have h0 : (0 : Ordinal.{0}) < vt τ ξ := hτ.pos.trans_le (vt_memTwo hτ hτ1 hξ hξ2).2.1
  rw [← add_zero (Om1 * (ω + 1))] at h ⊢
  exact luLt_of_vt_lt hτ hτ1 hξ hξ2 (luOld_omega_one_lt_E hτ) (luOld_zero_T hτ hτ1) (Ordinal.omega_pos 1) h0 h



/-- **[W07b] Def 4.1, the case `δ > α` with `cr(α, δ) = m`, with [W07a] Def 7.5, Def 7.1, Def 6.1, Def 4.11,
Def 4.6, Def 7.15, Convention 6.6, Convention 4.1, Lemma 6.3, Lemma 4.2, Lemma 4.3, Def 3.4, Def 3.28, Def 3.22, the
remark after Def 3.1 and the proof of Lemma 3.27** (texts H, Λ, I, D, G, LOC, CR, TR, C, W, E, S, T, Z, U, ★w1): for
`α := ϑᵗ(Ω₁·(ω+1))`, `lhᵗ(α) = α·ω + α`.

Our steps.  `Δ := Ω₁·(ω+1) = ϑ₁(1) + ϑ₁(0)` (★w1), `α = ϑᵗ(Δ + 0)` (C: `Ω₁ | Δ`, `η = 0`); `α ∈ Tᵗ` (T, third
clause, `Δ ∈ Tᵗ ∩ Ω₂`) and `τ < α ∈ E` (E, `Δ > 0`).
* `ζᵗ_α = 0` (G: `η = 0`, and `0 < sup_{σ<0} …` fails).
* `ι_{τ,α}(Δ)` (I): `Δ ∈ Tᵗ_α` (D: `Δ^* = 0 < α`, ★w1).  `Δ =NF ϑ₁(1) + ϑ₁(0) > Ω₁` (★w1), so by the second clause
  `ι_{τ,α}(Δ) = ι_{τ,α}(ϑ₁(1)) + ι_{τ,α}(ϑ₁(0))`.  By the note after Def 7.1, `ι_{τ,α}(ϑ₁(1)) = ϑ^α(ι_{τ,α}(1)) =
  ϑ^α(1)` and `ι_{τ,α}(ϑ₁(0)) = ϑ^α(ι_{τ,α}(0)) = ϑ^α(0)` (first clause: `0, 1 < α`).  `ϑ^α(0) = α` (proof of Lemma
  3.27 at the base `α`: "`ϑ₀(0) = τ`"); `ϑ^α(1) = ω̄_α = α·ω` (Lemma 4.2 at the base `α`, `m = 0`, `Ω₀ = α`, and
  Def 3.4: `(P ∖ E) ∩ α` has order type `α`, so `ω̄_α` is the least element of `P ∖ E` that is `≥ α`, i.e.
  `ω^{α+1} = α·ω`).  So `ι_{τ,α}(Δ) = α·ω + α`.
* `λᵗ_α` (Λ): `α ∈ E`, so `λᵗ_α = α·ω + α + 0 = α·ω + α`.
* `δ = (λᵗ_α)^*` (H, the note): `α·ω ≤ λᵗ_α = α·ω + α < α·ω·2`; `α·ω = ω^{α+1}` is additive principal and the next
  one is `ω^{α+2} > α·ω·2`, so `δ = α·ω > α`: the second branch of (H) applies.
* The `α`-localization of `δ` in `Tᵗ` (LOC, Convention 6.6): in `T^α`, `δ = ϑ^α(1)` with `Sub^α₀(ϑ^α(1)) =
  {ϑ^α(1), 1}` (S; `1 < α` a parameter), so it is `(α = δ₀, δ₁ = δ)`, `m = 1`; `δ ∈ T^α_{α⁺}` (D: `δ^{*α} = δ <
  α⁺ = ϑ^α(Δ)`, TR; `α⁺ = ϑᵗ(Δ + 1)` (C) is an `ε`-number above `α` (E, Lemma 3.30), so above `α·ω`), hence
  `δ^{t^α_τ} = δ` (TR).
* `cr(α, δ) = m` (CR with `n = m = 1`, `{1, …, n − 1} = ∅`), so (H) gives `lhᵗ(α) = lhᵗ(δ) + ρ` with
  `ρ := −δ + λᵗ_α = −(α·ω) + α·ω + α = α`.
* `lhᵗ(δ) = δ` for `δ = α·ω`, exactly as in the docstring of `ltLhT_w_lim` (`δ ∈ P ∖ E`, `δ = ϑᵗ(α)`, `λᵗ_δ = ζᵗ_δ = 0`,
  first branch of H).
So `lhᵗ(α) = δ + ρ = α·ω + α`.  Proved from `CitedLu` (`luLhT_inf` at `β = ω + 1`, `η = 0`, and the `R₁⁺`-reach
of `α·ω` from [W07b] Theorem 2.2 and Theorem 5.3). -/
theorem ltLhT_w1 {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) :
    lhT τ (vt τ (Om1 * (ω + 1))) = vt τ (Om1 * (ω + 1)) * ω + vt τ (Om1 * (ω + 1)) := by
  have hω1 : (ω : Ordinal.{0}) ≤ ω + 1 := le_self_add
  have h := luLhT_inf hτ hτ1 hω1 (lkcOmega_one_lt_E hτ) (luOld_zero_T hτ hτ1) (Ordinal.omega_pos 1)
  have hm := lkcLhT_mul_omega hτ hτ1 (one_lt_omega0.le.trans hω1) (lkcOmega_one_lt_E hτ) (luOld_zero_T hτ hτ1)
    (Ordinal.omega_pos 1)
  simp only [add_zero] at hm
  rw [lkcLog_omega_one, opow_one, lkcZeta_zero, add_zero, hm] at h
  simp only [add_zero] at h
  set α := vt τ (Om1 * (ω + 1)) with hα
  rw [show α * (ω + 1) = α * ω + α from mul_add_one α ω, Ordinal.add_sub_cancel] at h
  exact h

end Googology.Trans.PoR.InaccPsi.R2
