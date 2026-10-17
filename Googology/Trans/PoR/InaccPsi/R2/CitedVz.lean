import Googology.Trans.PoR.InaccPsi.R2.CitedEv

/-!
# Cited facts of Wilken 2007, as axioms: the arguments `Ω₁·n + η` of `ϑᵗ`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.

Same conventions as `R2.Cited`, `R2.CitedW`, `R2.CitedEps`, `R2.CitedL`, `R2.CitedEv` (`Ω₁ = ω₁`, `Ω₂ = ω₂ = OmTwo`,
`Tset τ = Tᵗ = T₀` over the base `τ`, `vt τ = ϑᵗ = ϑ₀`, `lhT τ = lhᵗ`, every base `τ` a countable `ε`-number, so
`τ ∈ {1} ∪ E`).  `n` ranges over the natural numbers; `Ω₁·n` is `Om1 * n`.  In Lean `vt τ` is a function on all
ordinals; the axioms below speak of it only at elements of `Tᵗ` below `Ω₂` (`Ω₁·n + η < Ω₂` for `η < Ω₁`).

Literal texts used below (all of [W07a] unless said otherwise):
* (T) Def 3.22: "`T_m` is defined inductively as follows: • `Ω_m ⊆ T_m` • `ξ, η ∈ T_m ⇒ ξ + η ∈ T_m`
  • `ξ ∈ T_m ∩ Ω_{k+2} ⇒ ϑ_k(ξ) ∈ T_m` for `k ≥ m`."  Convention 3.25: "we will indicate this explicitly in
  writing `ϑᵗ` and `Tᵗ` instead of `ϑ₀` and `T₀`."
* (U) Remark after Cor 3.24: "each `T_m` again gives rise to a notation system with parameters from `Ω_m` that
  provides a unique term for every ordinal which is element of some `Tⁿ_m` where `n > m` (again refining the
  clause for ordinal addition as we did for the systems `Tⁿ_m`)".  §2: "We write `ξ =ANF ξ₁ + ⋯ + ξₙ` if
  `ξ₁, …, ξₙ ∈ P`, `ξ₁ ≥ ⋯ ≥ ξₙ` (`ξ` given in additive normal form).  For convenience we also write
  `ξ =NF η + ρ` provided `η =ANF η₁ + ⋯ + ηₙ` for some `η₁, …, ηₙ`, and `ηₙ ≥ ρ ∈ P`."
* (Z) Remark after Def 3.1: "Note that we have `ϑⁿ_m(0) = Ω_m` for `m < n`"; with Def 3.22 (`ϑ_m(α) := ϑⁿ_m(α)`
  for `n` large): `ϑ₁(0) = Ω₁`.  Proof of Lemma 3.27: "We have `ϑ₀(0) = τ`".
* (S) Def 3.28: "`Subᵗ_m(α) := {α}` for parameters `α < τ`; `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ) ∪ Subᵗ_m(η)` for
  `ξ, η ∈ Tᵗ` s.t. `α =NF ξ + η > τ`; `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ)` if `k ≥ m` (`{α}` if `k < m`) for
  `α = ϑ_k(ξ)` where `ξ ∈ Tᵗ ∩ Ω_{k+2}`.  We define the additive principal parts of level `m` of `α ∈ Tᵗ` by
  `P_m(α) := Subᵗ_m(α) ∩ P ∩ [Ω_m, Ω_{m+1})` and `α^{*m} := max(P_m(α) ∪ {0})`."  Convention 3.29: "instead of
  `*₀` we will also write `*`".
* (Θ) Theorem 3.23: "For `m < ω` we have `T_m = ⋃_{n>m} Tⁿ_m` and `T_m ∩ Ω_{m+1} = θ_m = sup_{n≥m} ϑ_m(⋯(ϑ_n(0))⋯)`"
  (so `Tᵗ ∩ Ω₁` is an initial segment of the ordinals).
* (L) Lemma 3.30: "For `m < ω` the function `ϑ_m ↾ Tᵗ ∩ Ω_{m+2}` is 1-1 and has values in `P ∩ [Ω_m, Ω_{m+1})`.
  Let `α, γ ∈ Tᵗ ∩ Ω_{m+2}`.  Then `α^{*m} < ϑ_m(α)` and
  `ϑ_m(α) < ϑ_m(γ) ⇔ α < γ ∧ α^{*m} < ϑ_m(γ) ∨ ϑ_m(α) ≤ γ^{*m}`."
* (C) Convention 4.1: "Given a term `α = ϑᵗ(ξ) ∈ Tᵗ` we introduce the notational convention that
  `α = ϑᵗ(Δ + η)` automatically means that `ξ = Δ + η` is a decomposition such that `Ω₁ | Δ` and `η < Ω₁`. …
  So, `Δ = 0` iff `ξ < Ω₁` and `Δ` is a proper, i.e. nonzero, multiple of `Ω₁` otherwise.  Clearly, for the
  argument of a `ϑᵗ`-term in `Tᵗ`, to be a nonzero multiple of `Ω₁` means to be a sum of `ϑ₁`-terms.  The rest
  term `η` of the decomposition is then a sum of `ϑᵗ`-terms and parameters below `τ`."
* (E) Lemma 4.3: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ`.  Then `τ < α ∈ E ⇔ Δ > 0`."
* (F) Lemma 4.4: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ`.  Then `η = sup_{σ<η} ϑᵗ(Δ + σ)` ⇔ `η` has a form `ϑᵗ(Γ + ρ)` where
  `Γ > Δ` and `η > Δ^*`."
* (G) Def 4.11: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ` such that `α > τ` be given.  We define `ζᵗ_α := logend(η)` if
  `η < sup_{σ<η} ϑᵗ(Δ + σ)`, `0` otherwise."
* (D) Def 6.1: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ`.  The restriction of `Tᵗ` to `α`, written as `Tᵗ_α`, is defined by
  `Tᵗ_α := {β ∈ Tᵗ | β^{*τ} < α}`."
* (I) Def 7.1: "Let `α = ϑᵗ(Δ + η)` where `Δ > 0`.  We define `ι_{τ,α} : Tᵗ_α → T^α` by recursion on the
  definition of `Tᵗ` as follows: • `ι_{τ,α}(ξ) := ξ` if `ξ < α` • `ι_{τ,α}(ξ) := ι_{τ,α}(ξ₁) + ι_{τ,α}(ξ₂)` if
  `ξ =NF ξ₁ + ξ₂ > Ω₁` • `ι_{τ,α}(ξ) := ϑ_k(ι_{τ,α}(η))` if `ξ = ϑ_{k+1}(η)` where `k < ω`.  Note that
  `ι_{τ,α}(ϑ₁(η)) = ϑ^α(ι_{τ,α}(η))`."
* (Λ) Def 7.5: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ` such that `α > τ`.  We define `λᵗ_α := ι_{τ,α}(Δ) + ζᵗ_α` if `α ∈ E`,
  `ζᵗ_α` otherwise."
* (W) Def 3.4: "Let `α ↦ ω̄_α` be the enumeration function of the additive principle numbers which are not epsilon
  numbers."  Lemma 4.2: "For any `m < ω` and any `α < Ω_{m+1}` we have `ϑ_m(1 + α) = ω̄_{Ω_m+α}`" (proof: "for `m = 0`
  by convention we have `Ω₀ = τ` and `ϑ₀ = ϑᵗ`").
* (LOC) Def 4.6: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ`, `α ≥ τ`.  We define a finite sequence of ordinals as follows.  Set
  `α₀ := τ`.  Suppose that `αₙ` is already defined and `αₙ < α`.  Let `αₙ₊₁` be the element `ϑᵗ(ξ)` of `Pᵗ(α) − (αₙ + 1)`
  with maximal `ξ`.  This yields a finite sequence `τ = α₀ < ⋯ < αₙ = α` for some `n < ω` which we call the
  `τ`-localization of `α`."  Convention 6.6: "we call the sequence `(α, β₁^{t^α_τ}, …, β_m^{t^α_τ} = β^{t^α_τ})` the
  `α`-localization of `β^{t^α_τ} = β` in `Tᵗ`" (`(α = β₀, …, β_m = β)` the `α`-localization of `β` in `T^α`).
* (TR) Lemma 6.3: "We have • `α⁺ = ϑ^α(Δ)`, • the restriction of `t^τ_α` to `Tᵗ_{α⁺}` is the identity, and • the
  restriction of `t^α_τ` to `T^α_{α⁺}` is the identity."
* (CR) Def 7.15: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ`, `α ≥ τ`, and `(τ = α₀, …, αₙ = α)` be the `τ`-localization of `α`.  Define
  `cr(τ, α) := min{i ∈ {1, …, n − 1} | λᵗ_{αᵢ} ≥ α}` if that exists, `n` otherwise."
* (H) [W07b] Def 4.1: "For `α ∈ Tᵗ ∩ Ω₁` we define an ordinal `lhᵗ(α) ∈ Tᵗ ∩ Ω₁` by recursion on `hᵗ(α)` as
  follows. • `lhᵗ(α) := 0` if `α ≤ τ` • `lhᵗ(α) := α` if `α =NF α₁ + α₂ ≥ τ` • If `α = ϑᵗ(Δ + η) > τ` we set
  `δ := (λᵗ_α)^*`. • `lhᵗ(α) := α + λᵗ_α` if `δ ≤ α`, i.e. `Δ < ϑ₁(1)` • If `δ > α` let `(α = δ₀, …, δ_m = δ)` be
  the `α`-localization of `δ` in `Tᵗ`.  `lhᵗ(α) := lhᵗ(δᵢ) + λᵗ_α` if `i := cr(α, δ) < m`, `lhᵗ(δ) + ρ` where
  `ρ := −δ + λᵗ_α` otherwise."; after it: "Note that
  `(λᵗ_α)^*` is the maximum additive principal number less than or equal to `λᵗ_α`."

Facts on `α^* = α^{*0}` used below (our steps, from (S), (U), (L), (Z)); (★1) is (★1) of `R2.CitedEv`:
* (★1) For `η ∈ Tᵗ ∩ Ω₁`: `η^* ≤ η`, and every additive component of `η` is `< τ` or `≤ η^*` (the proof in
  `R2.CitedEv`: by induction on the unique term of `η`, a parameter (`η^* = 0`, components `< τ`), `ϑ₀(ξ)`
  (`η^* = η`, the only component), or an `=NF`-sum (`η^*` the maximum of the two parts, components those of
  the parts)).
* (★3) For `η ∈ Tᵗ ∩ Ω₁` and `n < ω`: `Ω₁·n + η ∈ Tᵗ` and `(Ω₁·n + η)^* = η^*`.  Membership: `0 ∈ Ω₀ = τ ⊆ T₀`
  (T, first clause), `ϑ₁(0) ∈ T₀` (third clause, `k = 1 ≥ m = 0`, `0 ∈ T₀ ∩ Ω₃`), `ϑ₁(0) = Ω₁` (Z); then
  `Ω₁·n = Ω₁ + ⋯ + Ω₁` and `Ω₁·n + η` lie in `T₀` (second clause).  Subterms: let `η =ANF η₁ + ⋯ + ηₖ`.  The term
  of `Ω₁·n + η` (U) is the `=NF`-sum `(⋯((⋯(Ω₁ + Ω₁)⋯ + Ω₁) + η₁)⋯) + ηₖ` (§2: `Ω₁ ≥ ⋯ ≥ Ω₁ ≥ η₁ ≥ ⋯ ≥ ηₖ`,
  all in `P`); by (S) its `Subᵗ₀` is the set of its partial sums with at least two summands, `{Ω₁, 0}`
  (`Subᵗ₀(ϑ₁(0)) = {ϑ₁(0)} ∪ Subᵗ₀(0)`, `k = 1 ≥ m = 0`; `0 < τ` a parameter) and `⋃ⱼ Subᵗ₀(ηⱼ)`.  The partial
  sums with a summand `Ω₁` and `Ω₁` itself are `≥ Ω₁`, outside `[τ, Ω₁)`, `0 ∉ P`, and the partial sums of
  `η₁ + ⋯ + ηₖ` with at least two summands are not in `P`; so `P₀(Ω₁·n + η) = ⋃ⱼ P₀(ηⱼ) = P₀(η)` (for `η < τ` both
  are empty, the `ηⱼ` being parameters; for `η ≥ τ` the term of `η` is the `=NF`-sum of its components), and
  `(Ω₁·n + η)^* = η^*`.  For `n = 0` this is trivial.
* (★4) `(Ω₁·n)^* = 0` (★3 with `η = 0`: `P₀(0) = ∅`, `0` being a parameter).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- **[W07a] Def 3.22, second clause** (text T): "`ξ, η ∈ T_m ⇒ ξ + η ∈ T_m`", for `m = 0` (Convention 3.25:
`T₀ = Tᵗ`).  Literal; the hypotheses on `τ` are the standing setting (`τ ∈ E` countable). -/
axiom vzT_add {τ x y : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hx : x ∈ Tset τ) (hy : y ∈ Tset τ) :
    x + y ∈ Tset τ

/-- **[W07a] Convention 4.1 with Def 3.22, the remark after Cor 3.24 and Def 3.28** (texts C, T, U, S): if
`ξ ∈ Tᵗ ∩ Ω₂` and `ξ = Δ + η` with `Ω₁ | Δ` and `η < Ω₁`, then `η ∈ Tᵗ`.

Our steps.  `ϑᵗ(ξ) ∈ Tᵗ` (T, third clause, `k = m = 0`, `ξ ∈ T₀ ∩ Ω₂`), so (C) applies to the term
`α = ϑᵗ(ξ)`: the decomposition `ξ = Δ + η` with `Ω₁ | Δ`, `η < Ω₁` is the one of (C) (it is unique: `Δ = Ω₁·q`,
`η` the remainder, by division by `Ω₁`), and "the rest term `η` of the decomposition is then a sum of
`ϑᵗ`-terms and parameters below `τ`".  These summands are subterms of the unique term of `ξ` (U: the term of
`ξ` is the `=NF`-sum of its additive components, and the components below `Ω₁` are the components of `η`), and
a subterm of a term of `Tᵗ` is a term of `Tᵗ` (Def 3.22 is an inductive definition; (S) lists the
subterms).  So each summand lies in `Tᵗ`, and `η ∈ Tᵗ` by the second clause of (T) (for `η = 0`: `0 ∈ Ω₀ = τ ⊆ T₀`,
first clause). -/
axiom vzRem_T {τ ξ Δ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hξ : ξ ∈ Tset τ) (hξ2 : ξ < OmTwo)
    (hdec : ξ = Δ + η) (hΔ : Om1 ∣ Δ) (hη : η < Om1) : η ∈ Tset τ

/-- **[W07a] Lemma 3.30, the direction `⇒`, with Def 3.28** (texts L, S, ★): for `ξ ∈ Tᵗ ∩ Ω₂`, `η ∈ Tᵗ ∩ Ω₁`
with `η < ϑᵗ(ξ)` and `n < ω`, `ϑᵗ(ξ) < ϑᵗ(Ω₁·n + η)` implies `ξ < Ω₁·n + η`.

Our steps.  `γ := Ω₁·n + η ∈ Tᵗ ∩ Ω₂` (★3; `Ω₁·n + η < Ω₁·ω ≤ Ω₂`).  By (★3) and (★1), `γ^* = η^* ≤ η < ϑᵗ(ξ)`.
Lemma 3.30 with `m = 0`, `α = ξ`: `ϑ₀(ξ) < ϑ₀(γ)` gives `ξ < γ ∧ ξ^* < ϑ₀(γ)` or `ϑ₀(ξ) ≤ γ^*`; the second is
impossible.  So `ξ < γ`.  (For `n = 1` this is the axiom `vt_lt_Om1_add` of `R2.CitedEv`.) -/
axiom vzLt_of_vt_lt {τ ξ η : Ordinal.{0}} {n : ℕ} (hτ : InE τ) (hτ1 : τ < Om1) (hξ : ξ ∈ Tset τ)
    (hξ2 : ξ < OmTwo) (hη : η ∈ Tset τ) (hη1 : η < Om1) (hηξ : η < vt τ ξ)
    (h : vt τ ξ < vt τ (Om1 * (n : Ordinal.{0}) + η)) : ξ < Om1 * (n : Ordinal.{0}) + η

/-- **[W07a] Lemma 3.30, the direction `⇐`, with Def 3.28** (texts L, S, ★): for `η', η ∈ Tᵗ ∩ Ω₁` and `m, n < ω`
with `Ω₁·m + η' < Ω₁·n + η` and `η' < ϑᵗ(Ω₁·n + η)`, `ϑᵗ(Ω₁·m + η') < ϑᵗ(Ω₁·n + η)`.

Our steps.  `α := Ω₁·m + η'` and `γ := Ω₁·n + η` lie in `Tᵗ ∩ Ω₂` (★3), and `α < γ`.  By (★3) and (★1),
`α^* = η'^* ≤ η' < ϑ₀(γ)`.  So the first disjunct of the right side of Lemma 3.30 (`m = 0`) holds:
`ϑ₀(α) < ϑ₀(γ)`.  (For `m = n = 1` this is the axiom `vt_Om1_add_lt` of `R2.CitedEv`.) -/
axiom vzVt_lt {τ η' η : Ordinal.{0}} {m n : ℕ} (hτ : InE τ) (hτ1 : τ < Om1) (hη' : η' ∈ Tset τ)
    (hη'1 : η' < Om1) (hη : η ∈ Tset τ) (hη1 : η < Om1)
    (hlt : Om1 * (m : Ordinal.{0}) + η' < Om1 * (n : Ordinal.{0}) + η)
    (h : η' < vt τ (Om1 * (n : Ordinal.{0}) + η)) :
    vt τ (Om1 * (m : Ordinal.{0}) + η') < vt τ (Om1 * (n : Ordinal.{0}) + η)

/-- **[W07b] Def 4.1 with [W07a] Def 7.5, Def 7.1, Def 6.1, Def 4.11, Lemma 4.3, the remark after Def 3.1 and
the proof of Lemma 3.27** (texts H, Λ, I, D, G, E, Z, ★): for `1 ≤ n < ω` and `η ∈ Tᵗ ∩ Ω₁` with
`ϑᵗ(Ω₁·n + σ) ≤ η` for every `σ < η` (for instance `η = 0`), and `α := ϑᵗ(Ω₁·n + η)`: `lhᵗ(α) = α·(n + 1)`.

Our steps.  `α = ϑᵗ(Δ + η)` with `Δ = Ω₁·n` (`Ω₁ | Δ`, `η < Ω₁`: Convention 4.1); `α ∈ Tᵗ` (★3 and T, third
clause), and `τ < α ∈ E` (E, `Δ > 0`).
* `ζᵗ_α` (G): `sup_{σ<η} ϑᵗ(Δ + σ) ≤ η` by the hypothesis (`= 0` for `η = 0`), so `η < sup` fails: `ζᵗ_α = 0`.
* `ι_{τ,α}(Δ)` (I): `Δ ∈ Tᵗ_α` (D: `Δ^* = 0 < α`, ★4).  `Ω₁ = ϑ₁(0)` (Z), and by the note after Def 7.1,
  `ι_{τ,α}(ϑ₁(0)) = ϑ^α(ι_{τ,α}(0))`, `ι_{τ,α}(0) = 0` (first clause, `0 < α`), `ϑ^α(0) = α` (proof of Lemma 3.27
  at the base `α`): `ι_{τ,α}(Ω₁) = α`.  For `n ≥ 2`, `Ω₁·n =NF Ω₁·(n − 1) + Ω₁ > Ω₁` (§2: `Ω₁·(n − 1) =ANF
  Ω₁ + ⋯ + Ω₁`, `Ω₁ ≥ Ω₁ ∈ P`), so by the second clause `ι_{τ,α}(Ω₁·n) = ι_{τ,α}(Ω₁·(n − 1)) + α`, and by
  induction `ι_{τ,α}(Δ) = α·n`.
* `λᵗ_α` (Λ): `α ∈ E`, so `λᵗ_α = ι_{τ,α}(Δ) + ζᵗ_α = α·n`.
* `lhᵗ(α)` (H): `α = ϑᵗ(Δ + η) > τ`; the maximum additive principal number `≤ α·n` is `α` (`α ∈ P`, and the next
  additive principal number after `α` is `α·ω > α·n`), so `δ = (λᵗ_α)^* = α ≤ α` (also `Δ = Ω₁·n < Ω₁·ω = ϑ₁(1)`,
  [W07a] Lemma 4.2 with `m = 1`), and `lhᵗ(α) = α + λᵗ_α = α + α·n = α·(n + 1)`. -/
axiom vzLhT_fix {τ η : Ordinal.{0}} {n : ℕ} (hτ : InE τ) (hτ1 : τ < Om1) (hn : 1 ≤ n) (hη : η ∈ Tset τ)
    (hη1 : η < Om1) (hfix : ∀ σ, σ < η → vt τ (Om1 * (n : Ordinal.{0}) + σ) ≤ η) :
    lhT τ (vt τ (Om1 * (n : Ordinal.{0}) + η)) =
      vt τ (Om1 * (n : Ordinal.{0}) + η) * ((n + 1 : ℕ) : Ordinal.{0})

/-- **[W07a] Lemma 3.30, Lemma 4.3, Def 3.28** (texts L, E, S, ★): for `1 ≤ n < ω` and `η ∈ Tᵗ ∩ Ω₁`,
`η < ϑᵗ(Ω₁·n + η)`.

Our steps.  `γ := Ω₁·n + η ∈ Tᵗ ∩ Ω₂` (★3).  Lemma 3.30: `γ^* < ϑ₀(γ)`, and `γ^* = η^*` (★3).  By Lemma 4.3
(`Δ = Ω₁·n > 0`), `τ < ϑ₀(γ) ∈ E ⊆ P`.  By (★1) every additive component of `η` is `< τ` or `≤ η^*`, so it is
`< ϑ₀(γ)`; as `ϑ₀(γ)` is additive principal, `η < ϑ₀(γ)` (for `η = 0` as `ϑ₀(γ) > τ > 0`).  (For `n = 1` this is
the axiom `lt_vt_Om1_add` of `R2.CitedEv`.) -/
axiom vzLt_vt_self {τ η : Ordinal.{0}} {n : ℕ} (hτ : InE τ) (hτ1 : τ < Om1) (hn : 1 ≤ n) (hη : η ∈ Tset τ)
    (hη1 : η < Om1) : η < vt τ (Om1 * (n : Ordinal.{0}) + η)

/-- **[W07b] Def 4.1 with [W07a] Def 7.5, Def 7.1, Def 6.1, Def 4.11, Lemma 4.3, the remark after Def 3.1 and
the proof of Lemma 3.27** (texts H, Λ, I, D, G, E, Z, ★): for `1 ≤ n < ω` and `η ∈ Tᵗ ∩ Ω₁`, `η ≠ 0`, with
`η < ϑᵗ(Ω₁·n + σ)` for some `σ < η`, and `α := ϑᵗ(Ω₁·n + η)`: `lhᵗ(α) = α·(n + 1) + logend(η)` (`logend = lg`,
see `R2.CitedW`; `η ≠ 0`).

Our steps.  `α = ϑᵗ(Δ + η)` with `Δ = Ω₁·n` (Convention 4.1); `α ∈ Tᵗ` (★3, T) and `τ < α ∈ E` (E, `Δ > 0`).
* `ζᵗ_α` (G): `η < ϑᵗ(Δ + σ) ≤ sup_{σ'<η} ϑᵗ(Δ + σ')` for the given `σ < η` (`ϑᵗ(Δ + σ)` is a term: `σ < η`
  and `Tᵗ ∩ Ω₁` is an initial segment, Θ); hence `ζᵗ_α = logend(η)`.
* `ι_{τ,α}(Δ) = α·n` (I, D, Z, ★4), as in the docstring of `vzLhT_fix`.
* `λᵗ_α` (Λ): `α ∈ E`, so `λᵗ_α = α·n + logend(η)`.
* `lhᵗ(α)` (H): `logend(η) ≤ η < α` (axiom `vzLt_vt_self`), so `α·n + logend(η) < α·(n + 1) ≤ α·ω`, and the maximum
  additive principal number `≤ λᵗ_α` is `α`: `δ = α ≤ α`, `lhᵗ(α) = α + λᵗ_α = α·(n + 1) + logend(η)`.  (For `n = 1`
  this is the axiom `lhT_Om1_add` of `R2.CitedEv`.) -/
axiom vzLhT_lim {τ η : Ordinal.{0}} {n : ℕ} (hτ : InE τ) (hτ1 : τ < Om1) (hn : 1 ≤ n) (hη : η ∈ Tset τ)
    (hη1 : η < Om1) (hη0 : η ≠ 0) (hlim : ∃ σ, σ < η ∧ η < vt τ (Om1 * (n : Ordinal.{0}) + σ)) :
    lhT τ (vt τ (Om1 * (n : Ordinal.{0}) + η)) =
      vt τ (Om1 * (n : Ordinal.{0}) + η) * ((n + 1 : ℕ) : Ordinal.{0}) + lg η

/-- **[W07a] Lemma 4.4, the direction `⇒`, with Lemma 3.30 (1-1), Convention 4.1 and Theorem 3.23** (texts F, L,
C, Θ, U): for `1 ≤ k < ω` and `η ∈ Tᵗ ∩ Ω₁`, `η > 0`, with `ϑᵗ(Ω₁·k + σ) < η` for every `σ < η`: every
`ξ ∈ Tᵗ ∩ Ω₂` with `ϑᵗ(ξ) = η` has `ξ ≥ Ω₁·(k + 1)`.

Our steps.  `α := ϑᵗ(Ω₁·k + η) ∈ Tᵗ` (★3, T), with `Δ = Ω₁·k`.  `η = sup_{σ<η} ϑᵗ(Δ + σ)`: `≤` by the hypothesis;
`≥` as every `σ < η` lies in `Tᵗ` (Θ) and has `σ < ϑᵗ(Δ + σ)` (axiom `vzLt_vt_self`), so the supremum is
`≥ sup_{σ<η} (σ + 1) = η`.  Lemma 4.4 (`⇒`): the term of `η` has the form `ϑᵗ(Γ + ρ)` with `Γ > Δ`, `Ω₁ | Γ`,
`ρ < Ω₁` (C), and `Γ + ρ ∈ Tᵗ ∩ Ω₂` is its argument (U, T).  For `ξ` as given, `ϑᵗ(ξ) = η = ϑᵗ(Γ + ρ)` and
Lemma 3.30 (`ϑ₀ ↾ Tᵗ ∩ Ω₂` is 1-1) give `ξ = Γ + ρ`.  `Γ` is a multiple of `Ω₁` above `Ω₁·k`, so `Γ ≥ Ω₁·(k + 1)` and
`ξ ≥ Ω₁·(k + 1)`. -/
axiom vzFix_level {τ η ξ : Ordinal.{0}} {k : ℕ} (hτ : InE τ) (hτ1 : τ < Om1) (hk : 1 ≤ k) (hη : η ∈ Tset τ)
    (hη1 : η < Om1) (hη0 : 0 < η) (hfix : ∀ σ, σ < η → vt τ (Om1 * (k : Ordinal.{0}) + σ) < η)
    (hξ : ξ ∈ Tset τ) (hξ2 : ξ < OmTwo) (hv : vt τ ξ = η) : Om1 * ((k + 1 : ℕ) : Ordinal.{0}) ≤ ξ

/-- **[W07a] Def 3.22, Lemma 4.2 (`m = 1`), Def 3.4** (texts T, W): `Ω₁·ω ∈ Tᵗ`.

Our steps.  `1 < τ = Ω₀ ⊆ T₀` (T, first clause), so `1 ∈ T₀ ∩ Ω₃` and `ϑ₁(1) ∈ T₀` (T, third clause, `k = 1 ≥ m = 0`).
Lemma 4.2 with `m = 1`, `α = 0`: `ϑ₁(1) = ω̄_{Ω₁}`.  By Def 3.4, `ω̄` enumerates `P ∖ E`.  The set `(P ∖ E) ∩ Ω₁` has
order type `Ω₁`: it is a subset of `Ω₁`, and `c ↦ ω^{c+1}` maps `Ω₁` strictly increasingly into it (`ω^{c+1}` is not
an `ε`-number, its exponent being a successor).  So `ω̄_c < Ω₁` for `c < Ω₁`, and `ω̄_{Ω₁}` is the least element of
`P ∖ E` that is `≥ Ω₁`.  `Ω₁ = ω₁ = ω^{Ω₁}` is an `ε`-number, and the least additive principal number above it is
`ω^{Ω₁+1} = Ω₁·ω ∉ E`.  So `Ω₁·ω = ϑ₁(1) ∈ T₀ = Tᵗ`. -/
axiom vzOm1w_T {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) : Om1 * ω ∈ Tset τ

/-- **[W07a] Lemma 3.30, the direction `⇒`, at `γ = Ω₁·ω`, with Def 3.28** (texts L, S, W): for `ξ ∈ Tᵗ ∩ Ω₂`,
`ϑᵗ(ξ) < ϑᵗ(Ω₁·ω)` implies `ξ < Ω₁·ω`.

Our steps.  `γ := Ω₁·ω = ϑ₁(1) ∈ Tᵗ ∩ Ω₂` (axiom `vzOm1w_T`).  By (S), `Subᵗ₀(ϑ₁(1)) = {ϑ₁(1)} ∪ Subᵗ₀(1) = {Ω₁·ω, 1}`
(`k = 1 ≥ m = 0`; `1 < τ` a parameter), so `P₀(γ) = ∅` (`Ω₁·ω ≥ Ω₁`, `1 < τ`) and `γ^* = 0`.  Lemma 3.30 (`m = 0`):
`ϑ₀(ξ) < ϑ₀(γ)` gives `ξ < γ ∧ ξ^* < ϑ₀(γ)` or `ϑ₀(ξ) ≤ γ^* = 0`; the second is impossible (`ϑ₀(ξ) ∈ P`, so `> 0`).
So `ξ < γ`. -/
axiom vzLt_of_vt_lt_w {τ ξ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hξ : ξ ∈ Tset τ) (hξ2 : ξ < OmTwo)
    (h : vt τ ξ < vt τ (Om1 * ω)) : ξ < Om1 * ω

/-- **[W07a] Lemma 3.30, the direction `⇐`, at `γ = Ω₁·ω`, with Def 3.28** (texts L, S, ★, W): for `η' ∈ Tᵗ ∩ Ω₁`
and `m < ω` with `η' < ϑᵗ(Ω₁·ω)`, `ϑᵗ(Ω₁·m + η') < ϑᵗ(Ω₁·ω)`.

Our steps.  `α := Ω₁·m + η' ∈ Tᵗ ∩ Ω₂` (★3) and `γ := Ω₁·ω ∈ Tᵗ ∩ Ω₂` (axiom `vzOm1w_T`); `α < Ω₁·(m + 1) ≤ γ`.  By
(★3) and (★1), `α^* = η'^* ≤ η' < ϑ₀(γ)`.  So the first disjunct of the right side of Lemma 3.30 (`m = 0`) holds:
`ϑ₀(α) < ϑ₀(γ)`. -/
axiom vzVt_lt_w {τ η' : Ordinal.{0}} {m : ℕ} (hτ : InE τ) (hτ1 : τ < Om1) (hη' : η' ∈ Tset τ)
    (hη'1 : η' < Om1) (h : η' < vt τ (Om1 * ω)) :
    vt τ (Om1 * (m : Ordinal.{0}) + η') < vt τ (Om1 * ω)

/-- **[W07b] Def 4.1, the case `δ > α`, with [W07a] Def 7.5, Def 7.1, Def 6.1, Def 4.11, Def 4.6, Def 7.15,
Convention 6.6, Lemma 6.3, Lemma 4.2, Lemma 4.3, Def 3.4, Def 3.28** (texts H, Λ, I, D, G, LOC, CR, TR, W, E, S):
for `α := ϑᵗ(Ω₁·ω)`, `lhᵗ(α) = α·ω`.

Our steps.  `Δ := Ω₁·ω = ϑ₁(1)` (axiom `vzOm1w_T`), `α = ϑᵗ(Δ + 0)` (Convention 4.1: `Ω₁ | Δ`, `η = 0`); `α ∈ Tᵗ`,
`τ < α ∈ E` (E, `Δ > 0`).
* `ζᵗ_α = 0` (G: `η = 0`, and `0 < sup_{σ<0} …` fails).
* `ι_{τ,α}(Δ)` (I): `Δ ∈ Tᵗ_α` (D: `Δ^* = 0 < α`, see `vzLt_of_vt_lt_w`); by the note after Def 7.1,
  `ι_{τ,α}(ϑ₁(1)) = ϑ^α(ι_{τ,α}(1))`, and `ι_{τ,α}(1) = 1` (first clause, `1 < α`).  Lemma 4.2 at the base `α`
  (`m = 0`, `Ω₀ = α`): `ϑ^α(1) = ω̄_α`.  As in `vzOm1w_T` (Def 3.4), `(P ∖ E) ∩ α` has order type `α` (`c ↦ ω^{c+1}`
  maps `α` into it, `α ∈ E`), so `ω̄_α` is the least element of `P ∖ E` that is `≥ α`, which is `ω^{α+1} = α·ω`.
  So `ι_{τ,α}(Δ) = α·ω`.
* `λᵗ_α` (Λ): `α ∈ E`, so `λᵗ_α = α·ω + 0 = α·ω`.
* `lhᵗ(α)` (H): `δ := (λᵗ_α)^* = α·ω` (it is additive principal), and `δ > α`.  The `α`-localization of `δ` in `Tᵗ`
  (Convention 6.6: the `α`-localization of `δ` in `T^α`, Def 4.6 at the base `α`, translated by `t^α_τ`): in `T^α`,
  `δ = ω̄_α = ϑ^α(1)`, `Sub^α₀(ϑ^α(1)) = {ϑ^α(1), 1}` (S; `1 < α` a parameter), so `P^α(δ) = {δ}` and the localization
  is `(α = δ₀, δ₁ = δ)`, `m = 1`; `δ ∈ T^α_{α⁺}` (`δ^{*α} = δ < α⁺ = ϑ^α(Δ)`, Lemma 6.3; `α⁺ = ϑᵗ(Δ + 1)` is an
  `ε`-number above `α` (E, Lemma 3.30), so above `α·ω`), so `δ^{t^α_τ} = δ`
  (Lemma 6.3).  Def 7.15 with `n = m = 1`: `{1, …, n − 1}` is empty, so `cr(α, δ) = m` and the second branch of (H)
  applies: `lhᵗ(α) = lhᵗ(δ) + ρ` with `ρ := −δ + λᵗ_α = −(α·ω) + α·ω = 0`.
* `lhᵗ(δ)` (H) for `δ = α·ω ∈ Tᵗ` (`δ < α⁺`): `δ` is additive principal and not in `E`, so `δ = ϑᵗ(ξ_δ)` with
  `ξ_δ < Ω₁` (E); Lemma 4.2 (`m = 0`): `ϑᵗ(1 + ξ') = ω̄_{τ+ξ'}` and `ω̄_α = δ` give `τ + ξ' = α`, `ξ' = α` (`α`
  additive principal `> τ`), `ξ_δ = 1 + α = α`.  `λᵗ_δ = ζᵗ_δ` (Λ, `δ ∉ E`), and `ζᵗ_δ = 0` (G): every `σ < α` has
  `ϑᵗ(σ) < α` (`ϑᵗ(1 + σ') = ω̄_{τ+σ'}` with `τ + σ' < α`, and `ω̄` maps `α` into `α`, see above), so
  `sup_{σ<α} ϑᵗ(σ) ≤ α` and `α < sup` fails.  `(λᵗ_δ)^* = 0 ≤ δ`, so `lhᵗ(δ) = δ + 0 = δ`.
So `lhᵗ(α) = δ + 0 = α·ω`. -/
axiom vzLhT_w {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) :
    lhT τ (vt τ (Om1 * ω)) = vt τ (Om1 * ω) * ω

end Googology.Trans.PoR.InaccPsi.R2
