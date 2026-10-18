import Googology.Trans.PoR.InaccPsi.R2.CitedXt

/-!
# Cited facts of Wilken 2007, as axioms: [W07a] Lemma 3.30 at the arguments `Ω₁·ω + η`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

Same conventions as `R2.Cited`, `R2.CitedEv`, `R2.CitedVz`, `R2.CitedXt` (`Ω₁ = ω₁`, `Ω₂ = ω₂ = OmTwo`, `Tset τ = Tᵗ =
T₀` over the base `τ`, `vt τ = ϑᵗ = ϑ₀`, every base `τ` a countable `ε`-number).  In Lean `vt τ` is a function on all
ordinals; the axioms below speak of it only at elements of `Tᵗ` below `Ω₂` (`Ω₁·m + η'`, `Ω₁·ω + η` with
`η', η < Ω₁`).

Literal texts used below (all of [W07a]):
* (T) Def 3.22: "`T_m` is defined inductively as follows: • `Ω_m ⊆ T_m` • `ξ, η ∈ T_m ⇒ ξ + η ∈ T_m`
  • `ξ ∈ T_m ∩ Ω_{k+2} ⇒ ϑ_k(ξ) ∈ T_m` for `k ≥ m`."  Convention 3.25: "we will indicate this explicitly in
  writing `ϑᵗ` and `Tᵗ` instead of `ϑ₀` and `T₀`."
* (U) Remark after Cor 3.24: "each `T_m` again gives rise to a notation system with parameters from `Ω_m` that
  provides a unique term for every ordinal which is element of some `Tⁿ_m` where `n > m` (again refining the
  clause for ordinal addition as we did for the systems `Tⁿ_m`)".  §2: "We write `ξ =ANF ξ₁ + ⋯ + ξₙ` if
  `ξ₁, …, ξₙ ∈ P`, `ξ₁ ≥ ⋯ ≥ ξₙ` (`ξ` given in additive normal form).  For convenience we also write
  `ξ =NF η + ρ` provided `η =ANF η₁ + ⋯ + ηₙ` for some `η₁, …, ηₙ`, and `ηₙ ≥ ρ ∈ P`."
* (S) Def 3.28: "`Subᵗ_m(α) := {α}` for parameters `α < τ`; `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ) ∪ Subᵗ_m(η)` for
  `ξ, η ∈ Tᵗ` s.t. `α =NF ξ + η > τ`; `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ)` if `k ≥ m` (`{α}` if `k < m`) for
  `α = ϑ_k(ξ)` where `ξ ∈ Tᵗ ∩ Ω_{k+2}`.  We define the additive principal parts of level `m` of `α ∈ Tᵗ` by
  `P_m(α) := Subᵗ_m(α) ∩ P ∩ [Ω_m, Ω_{m+1})` and `α^{*m} := max(P_m(α) ∪ {0})`."  Convention 3.29: "instead of
  `*₀` we will also write `*`".
* (L) Lemma 3.30: "For `m < ω` the function `ϑ_m ↾ Tᵗ ∩ Ω_{m+2}` is 1-1 and has values in `P ∩ [Ω_m, Ω_{m+1})`.
  Let `α, γ ∈ Tᵗ ∩ Ω_{m+2}`.  Then `α^{*m} < ϑ_m(α)` and
  `ϑ_m(α) < ϑ_m(γ) ⇔ α < γ ∧ α^{*m} < ϑ_m(γ) ∨ ϑ_m(α) ≤ γ^{*m}`."
* (W) Def 3.4: "Let `α ↦ ω̄_α` be the enumeration function of the additive principle numbers which are not epsilon
  numbers."  Lemma 4.2: "For any `m < ω` and any `α < Ω_{m+1}` we have `ϑ_m(1 + α) = ω̄_{Ω_m+α}`."

Facts on `α^* = α^{*0}` used below (our steps, from (S), (U), (L), (W)); (★1) and (★3) are those of `R2.CitedEv` and
`R2.CitedVz`:
* (★1) For `η ∈ Tᵗ ∩ Ω₁`: `η^* ≤ η` (by induction on the unique term of `η`: a parameter has `η^* = 0`, a term
  `ϑ₀(ξ)` has `η^* = η`, an `=NF`-sum has `η^*` the maximum of the two parts).
* (★3) For `η' ∈ Tᵗ ∩ Ω₁` and `m < ω`: `Ω₁·m + η' ∈ Tᵗ` and `(Ω₁·m + η')^* = η'^*`.
* (★w) For `η ∈ Tᵗ ∩ Ω₁`: `Ω₁·ω + η ∈ Tᵗ ∩ Ω₂` and `(Ω₁·ω + η)^* = η^*`.  The term: `1 < τ = Ω₀ ⊆ T₀` (T, first
  clause), so `1 ∈ T₀ ∩ Ω₃` and `ϑ₁(1) ∈ T₀` (T, third clause, `k = 1 ≥ m = 0`); by (W) with `m = 1`, `α = 0`,
  `ϑ₁(1) = ω̄_{Ω₁}`, and `ω̄_{Ω₁} = Ω₁·ω` (the computation in the docstring of the axiom `vzOm1w_T` of `R2.CitedVz`:
  `(P ∖ E) ∩ Ω₁` has order type `Ω₁`, and the least element of `P ∖ E` that is `≥ Ω₁ = ω^{Ω₁}` is
  `ω^{Ω₁+1} = Ω₁·ω`).  `Ω₁·ω + η ∈ T₀` by the second clause of (T); `Ω₁·ω + η < Ω₁·ω·2 < Ω₂`.  Let
  `η =ANF η₁ + ⋯ + ηₖ`.  The term of `Ω₁·ω + η` (U) is the `=NF`-sum `(⋯((ϑ₁(1) + η₁) + η₂)⋯) + ηₖ` (§2: `ϑ₁(1) = Ω₁·ω`
  is additive principal, `Ω₁·ω ≥ η₁ ≥ ⋯ ≥ ηₖ`, all in `P`); for `η = 0` it is `ϑ₁(1)`.  By (S) its `Subᵗ₀` is the set
  of its partial sums with at least two summands, `Subᵗ₀(ϑ₁(1)) = {ϑ₁(1)} ∪ Subᵗ₀(1) = {Ω₁·ω, 1}` (`k = 1 ≥ m = 0`;
  `1 < τ` a parameter), and `⋃ⱼ Subᵗ₀(ηⱼ)`.  The partial sums with at least two summands are not in `P`
  (`Ω₁·ω + η₁ + ⋯ + ηⱼ` with `j ≥ 1` is the sum of two smaller nonzero ordinals), `Ω₁·ω ≥ Ω₁` lies outside
  `[τ, Ω₁)`, and `1 < τ`; so `P₀(Ω₁·ω + η) = ⋃ⱼ P₀(ηⱼ) = P₀(η)` (for `η < τ` both are empty, the `ηⱼ` being
  parameters; for `η ≥ τ` the term of `η` is the `=NF`-sum of its components), and `(Ω₁·ω + η)^* = η^*`.

The axioms (3 facts, no constant):
1. `lzVt_lt_w` (L, ★3, ★w, ★1): `ϑᵗ(Ω₁·m + η') < ϑᵗ(Ω₁·ω + η)` when `η' < ϑᵗ(Ω₁·ω + η)`.
2. `lzVt_lt_ww` (L, ★w, ★1): `ϑᵗ(Ω₁·ω + η') < ϑᵗ(Ω₁·ω + η)` when `η' < η` and `η' < ϑᵗ(Ω₁·ω + η)`.
3. `lzLt_of_vt_lt_ww` (L, ★w, ★1): `ϑᵗ(ξ) < ϑᵗ(Ω₁·ω + η)` and `η < ϑᵗ(ξ)` give `ξ < Ω₁·ω + η`.
For `η = 0` the first and the third are the axioms `vzVt_lt_w` and `vzLt_of_vt_lt_w` of `R2.CitedVz`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- **[W07a] Lemma 3.30, the direction `⇐`, at `γ = Ω₁·ω + η`, with Def 3.28** (texts L, S, ★3, ★w, ★1): for
`η', η ∈ Tᵗ ∩ Ω₁` and `m < ω` with `η' < ϑᵗ(Ω₁·ω + η)`, `ϑᵗ(Ω₁·m + η') < ϑᵗ(Ω₁·ω + η)`.

Our steps.  `α := Ω₁·m + η' ∈ Tᵗ ∩ Ω₂` (★3) and `γ := Ω₁·ω + η ∈ Tᵗ ∩ Ω₂` (★w); `α < Ω₁·(m + 1) ≤ Ω₁·ω ≤ γ`.  By
(★3) and (★1), `α^* = η'^* ≤ η' < ϑ₀(γ)`.  So the first disjunct of the right side of Lemma 3.30 (`m = 0`) holds:
`α < γ ∧ α^* < ϑ₀(γ)`, and `ϑ₀(α) < ϑ₀(γ)`. -/
axiom lzVt_lt_w {τ η' η : Ordinal.{0}} {m : ℕ} (hτ : InE τ) (hτ1 : τ < Om1) (hη' : η' ∈ Tset τ)
    (hη'1 : η' < Om1) (hη : η ∈ Tset τ) (hη1 : η < Om1) (h : η' < vt τ (Om1 * ω + η)) :
    vt τ (Om1 * (m : Ordinal.{0}) + η') < vt τ (Om1 * ω + η)

/-- **[W07a] Lemma 3.30, the direction `⇐`, between `Ω₁·ω + η'` and `Ω₁·ω + η`, with Def 3.28** (texts L, S, ★w,
★1): for `η', η ∈ Tᵗ ∩ Ω₁` with `η' < η` and `η' < ϑᵗ(Ω₁·ω + η)`, `ϑᵗ(Ω₁·ω + η') < ϑᵗ(Ω₁·ω + η)`.

Our steps.  `α := Ω₁·ω + η'` and `γ := Ω₁·ω + η` lie in `Tᵗ ∩ Ω₂` (★w; `η' < η < Ω₁`), and `α < γ`.  By (★w) and
(★1), `α^* = η'^* ≤ η' < ϑ₀(γ)`.  So the first disjunct of the right side of Lemma 3.30 (`m = 0`) holds:
`ϑ₀(α) < ϑ₀(γ)`. -/
axiom lzVt_lt_ww {τ η' η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hη' : η' ∈ Tset τ)
    (hη : η ∈ Tset τ) (hη1 : η < Om1) (hlt : η' < η) (h : η' < vt τ (Om1 * ω + η)) :
    vt τ (Om1 * ω + η') < vt τ (Om1 * ω + η)

/-- **[W07a] Lemma 3.30, the direction `⇒`, at `γ = Ω₁·ω + η`, with Def 3.28** (texts L, S, ★w, ★1): for
`ξ ∈ Tᵗ ∩ Ω₂` and `η ∈ Tᵗ ∩ Ω₁` with `η < ϑᵗ(ξ)`, `ϑᵗ(ξ) < ϑᵗ(Ω₁·ω + η)` implies `ξ < Ω₁·ω + η`.

Our steps.  `γ := Ω₁·ω + η ∈ Tᵗ ∩ Ω₂` (★w).  By (★w) and (★1), `γ^* = η^* ≤ η < ϑᵗ(ξ)`.  Lemma 3.30 with `m = 0`,
`α = ξ`: `ϑ₀(ξ) < ϑ₀(γ)` gives `ξ < γ ∧ ξ^* < ϑ₀(γ)` or `ϑ₀(ξ) ≤ γ^*`; the second is impossible.  So `ξ < γ`. -/
axiom lzLt_of_vt_lt_ww {τ ξ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hξ : ξ ∈ Tset τ)
    (hξ2 : ξ < OmTwo) (hη : η ∈ Tset τ) (hη1 : η < Om1) (hηξ : η < vt τ ξ)
    (h : vt τ ξ < vt τ (Om1 * ω + η)) : ξ < Om1 * ω + η

end Googology.Trans.PoR.InaccPsi.R2
