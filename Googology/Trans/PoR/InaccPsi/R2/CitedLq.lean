import Googology.Trans.PoR.InaccPsi.R2.CitedLg

set_option autoImplicit false

/-!
# Cited facts of Wilken 2007, as axioms, ONCE for the arguments `Δ + η` with `Δ = Ω₁·(Ω₁·γ + β)`, `γ ≥ 1`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.

Same conventions as `R2.CitedLu`, `R2.CitedLv`, `R2.CitedLg` (`Ω₁ = Om1`, `Ω₂ = OmTwo`, `Tset τ = Tᵗ`, `vt τ = ϑᵗ = ϑ₀`,
`lhT τ = lhᵗ`, `lg = logend`, `TB τ σ = Tᵗ[σ]`, `pi σ τ = π_{σ,τ}`, every base `τ` a countable `ε`-number).  Here the
arguments are `ξ = Ω₁·(Ω₁·γ + β) + η` with `γ, β, η ∈ Tᵗ ∩ Ω₁` and `γ ≥ 1`, i.e. every `ξ ∈ Tᵗ` with
`Ω₁·Ω₁ ≤ ξ < Ω₁·Ω₁·Ω₁ = ϑ₁(Ω₁·2)`; the multiple of `Ω₁` (Convention 4.1) is `Δ = Ω₁·(Ω₁·γ + β)`.  The values may be
strongly critical (`ϑᵗ(Ω₁·Ω₁) = Γ_{τ+1}`); nothing below assumes that a value is `φ_b(c)` with `b` below it.

What is **not** restated (checked first): `R2.CitedLu` (levels `β < τ`: `Ω₁·β + η`), `R2.CitedLv` (levels
`τ ≤ β < Ω₁`: `lvArg_mem`, `lvVt_lt_gen`, `lvLt_of_vt_lt`, `lvLevel_lt_vt`, `lvLhT_gen`, `lvPi_mul`), `R2.CitedLg`
(`lgArg_mem`, `lgVt_lt_low`, `lgLt_of_vt_lt`, `lgQuot_mem`, `lgLhT_sq`, `lgPi_OmOm`), `vt_memTwo`, `vt_rep`,
`vt_E_iff` (`R2.CitedEv`), `lh_eq_lhT` (`R2.CitedL`).  The axioms `lgArg_mem`, `lgVt_lt_low`, `lgLt_of_vt_lt` of
`R2.CitedLg` are the cases `γ = 1`, `β = 0` of `lqArg_mem`, `lqVt_lt`, `lqLt_of_vt_lt` below, and the lower bound
`lgLhT_sq` follows from `lqLhT` on this range; they are kept (nothing is changed or removed).  No quotient is formed
here (the trap `ξ/Ω₁ = Ω₁` of the removed `lvQuot_mem` does not arise).

Literal texts used below (all of [W07a] unless said otherwise; the full quotations of T, Θ, U, Z, S, L, C, W, E, G,
LOC, D, TR, I, Λ, CR, P, H are in the module docstring of `R2.CitedLu`):
* (T) Def 3.22: "`Ω_m ⊆ T_m` • `ξ, η ∈ T_m ⇒ ξ + η ∈ T_m` • `ξ ∈ T_m ∩ Ω_{k+2} ⇒ ϑ_k(ξ) ∈ T_m` for `k ≥ m`."
* (Θ) Theorem 3.23: "`T_m ∩ Ω_{m+1} = θ_m = sup_{n≥m} ϑ_m(⋯(ϑ_n(0))⋯)`."
* (Z) After Def 3.1: "Note that we have `ϑⁿ_m(0) = Ω_m` for `m < n`"; proof of Lemma 3.27: "We have `ϑ₀(0) = τ`".
* (W) Def 3.4: "Let `α ↦ ω̄_α` be the enumeration function of the additive principle numbers which are not epsilon
  numbers."  Lemma 4.2: "For any `m < ω` and any `α < Ω_{m+1}` we have `ϑ_m(1 + α) = ω̄_{Ω_m+α}`" (proof: "for
  `m = 0` by convention we have `Ω₀ = τ`").
* (S) Def 3.28: "`Subᵗ_m(α) := {α}` for parameters `α < τ`; `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ) ∪ Subᵗ_m(η)` for
  `ξ, η ∈ Tᵗ` s.t. `α =NF ξ + η > τ`; `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ)` if `k ≥ m`, `{α}` if `k < m`, for `α = ϑ_k(ξ)`
  where `ξ ∈ Tᵗ ∩ Ω_{k+2}`.  …  `P_m(α) := Subᵗ_m(α) ∩ P ∩ [Ω_m, Ω_{m+1})` and `α^{*m} := max(P_m(α) ∪ {0})`."
* (L) Lemma 3.30: "For `m < ω` the function `ϑ_m ↾ Tᵗ ∩ Ω_{m+2}` is 1-1 and has values in `P ∩ [Ω_m, Ω_{m+1})`.  Let
  `α, γ ∈ Tᵗ ∩ Ω_{m+2}`.  Then `α^{*m} < ϑ_m(α)` and `ϑ_m(α) < ϑ_m(γ) ⇔ α < γ ∧ α^{*m} < ϑ_m(γ) ∨ ϑ_m(α) ≤ γ^{*m}`."
* (C) Convention 4.1: "`α = ϑᵗ(Δ + η)` automatically means that `ξ = Δ + η` is a decomposition such that `Ω₁ | Δ` and
  `η < Ω₁`.  …  we will write `α⁺` to denote the ordinal `ϑᵗ(Δ + η + 1)`."
* (E) Lemma 4.3: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ`.  Then `τ < α ∈ E ⇔ Δ > 0`."
* (G) Def 4.11: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ` such that `α > τ` be given.  We define `ζᵗ_α := logend(η)` if
  `η < sup_{σ<η} ϑᵗ(Δ + σ)`, `0` otherwise."
* (D) Def 6.1: "`Tᵗ_α := {β ∈ Tᵗ | β^{*τ} < α}`."
* (LOC) Def 4.6: "Set `α₀ := τ`.  Suppose that `αₙ` is already defined and `αₙ < α`.  Let `αₙ₊₁` be the element
  `ϑᵗ(ξ)` of `Pᵗ(α) − (αₙ + 1)` with maximal `ξ`."  Convention 6.6: "we call the sequence `(α, β₁^{t^α_τ}, …,
  β_m^{t^α_τ} = β^{t^α_τ})` the `α`-localization of `β^{t^α_τ} = β` in `Tᵗ`".
* (TR) Lemma 6.3: "`α⁺ = ϑ^α(Δ)`, • the restriction of `t^τ_α` to `Tᵗ_{α⁺}` is the identity, and • the restriction of
  `t^α_τ` to `T^α_{α⁺}` is the identity."
* (CR) Def 7.15: "Define `cr(τ, α) := min{i ∈ {1, …, n − 1} | λᵗ_{αᵢ} ≥ α}` if that exists, `n` otherwise."
* (I) Def 7.1: "Let `α = ϑᵗ(Δ + η)` where `Δ > 0`.  We define `ι_{τ,α} : Tᵗ_α → T^α` … • `ι_{τ,α}(ξ) := ξ` if `ξ < α`
  • `ι_{τ,α}(ξ) := ι_{τ,α}(ξ₁) + ι_{τ,α}(ξ₂)` if `ξ =NF ξ₁ + ξ₂ > Ω₁` • `ι_{τ,α}(ξ) := ϑ_k(ι_{τ,α}(η))` if `ξ =
  ϑ_{k+1}(η)` where `k < ω`.  Note that `ι_{τ,α}(ϑ₁(η)) = ϑ^α(ι_{τ,α}(η))`."
* (Λ) Def 7.5: "`λᵗ_α := ι_{τ,α}(Δ) + ζᵗ_α` if `α ∈ E`, `ζᵗ_α` otherwise."
* (P) Def 5.1: "`Tᵗ[σ] := {α ∈ Tᵗ | Parᵗ(α) ⊆ σ}` … • `π_{σ,τ}(ξ) := ξ` if `ξ < σ` • `π_{σ,τ}(ξ) := π_{σ,τ}(ξ₁) +
  π_{σ,τ}(ξ₂)` if `ξ =NF ξ₁ + ξ₂ > τ` • `π_{σ,τ}(ξ) := ϑ_k(π_{σ,τ}(η))` if `ξ = ϑ_k(η)` for some `k > 0` and `η ∈
  Tᵗ[σ] ∩ Ω_{k+2}` • …"; Lemma 5.3: "(b) `π_{σ,τ}` preserves `<`. (c) `π_{σ,τ}` preserves ordinal addition."
* (H) [W07b] Def 4.1: "• `lhᵗ(α) := 0` if `α ≤ τ` • `lhᵗ(α) := α` if `α =NF α₁ + α₂ ≥ τ` • If `α = ϑᵗ(Δ + η) > τ` we
  set `δ := (λᵗ_α)^*`. • `lhᵗ(α) := α + λᵗ_α` if `δ ≤ α`, i.e. `Δ < ϑ₁(1)` • If `δ > α` let `(α = δ₀, …, δ_m = δ)` be
  the `α`-localization of `δ` in `Tᵗ`.  `lhᵗ(α) := lhᵗ(δᵢ) + λᵗ_α` if `i := cr(α, δ) < m`, `lhᵗ(δ) + ρ` where `ρ :=
  −δ + λᵗ_α` otherwise."  "Note that `(λᵗ_α)^*` is the maximum additive principal number less than or equal to
  `λᵗ_α`."

Our steps (`τ` a countable `ε`-number; `γ, β, η ∈ Tᵗ ∩ Ω₁`, `γ ≥ 1`; used in every docstring below):
* (◇c) For `c < Ω₁`: `ϑ₁(Ω₁ + c) = Ω₁·Ω₁·ω^c`.  By W with `m = 1`, `α = Ω₁ + c` (`1 + (Ω₁ + c) = Ω₁ + c`):
  `ϑ₁(Ω₁ + c) = ω̄_{Ω₁+Ω₁+c}`; the members of `P ∖ E` from `Ω₁` on are `ω^{Ω₁+1+a}` for `a < ε_{Ω₁+1}` (`(P ∖ E) ∩ Ω₁`
  has order type `Ω₁`, and there is no `ε`-number in `(Ω₁, ε_{Ω₁+1})`), so `ϑ₁(Ω₁ + c) = ω^{Ω₁+1+Ω₁+c} = ω^{Ω₁·2+c} =
  Ω₁·Ω₁·ω^c`.  For `c = 0` this is step ◇Ω of `R2.CitedLg`.  If `c ∈ T₀` then `Ω₁ + c ∈ T₀ ∩ Ω₃` (`Ω₁ = ϑ₁(0)` by Z;
  T, second clause) and `ϑ₁(Ω₁ + c) ∈ T₀` (T, third clause, `k = 1 ≥ 0`).
* (◇Δ) Write `γ =ANF ω^{c₁} + ⋯ + ω^{cᵢ}` and `β =ANF ω^{b₁} + ⋯ + ω^{bⱼ}` (§2).  The exponents `cₗ ≤ γ`, `bₗ ≤ β`
  lie in `T₀ ∩ Ω₁` (Θ: an initial segment).  By ◇c and by step ◆β of `R2.CitedLv` (★β of `R2.CitedLu` for the
  exponents `< τ`, `ϑ₁(b) = Ω₁·ω^b`): **`Δ = Ω₁·(Ω₁·γ + β) =NF ϑ₁(Ω₁ + c₁) + ⋯ + ϑ₁(Ω₁ + cᵢ) + ϑ₁(b₁) + ⋯ +
  ϑ₁(bⱼ)`**, a non-increasing sum of additive principal terms of `T₀` (`Ω₁ + cₗ > bₗ'`), so `Δ ∈ T₀`, and
  `ξ = Δ + η ∈ T₀ ∩ Ω₂` (T, second clause; `ξ < Ω₁·Ω₁·(γ + 1) < Ω₂`).
* (◇*) By S (second and third clauses, `k = 1 ≥ 0`) the level-zero subterms of `ξ` are its partial sums with at least
  two summands (not in `P`), the `ϑ₁`-terms (`≥ Ω₁`), the terms `Ω₁ + cₗ`, `Ω₁`, `0`, and the members of `Subᵗ₀(cₗ)`,
  `Subᵗ₀(bₗ)`, `Subᵗ₀(η)`.  Every member of `Subᵗ₀(cₗ)`, `Subᵗ₀(bₗ)` in `[τ, Ω₁)` is a subterm of the term of `cₗ`
  resp. `bₗ`, hence `≤ cₗ ≤ γ` resp. `≤ bₗ ≤ β` (L: `α^* < ϑ₀(α)` along the term), and every member of `P₀(η)` is
  `≤ η` (★1 of `R2.CitedLu`).  So **`ξ^* ≤ max(γ, β, η)`** (also for `γ = 0`: step ◆* of `R2.CitedLv`).
* (◇<) For an `ε`-number `a > τ` with `ξ^* < a`: each additive component of `cₗ`, `bₗ`, `η` is `< τ` or a member of
  `Subᵗ₀(ξ) ∩ P ∩ [τ, Ω₁)`, hence `≤ ξ^* < a`, so `cₗ, bₗ, η < a` (`a` additive principal) and `ω^{cₗ}, ω^{bₗ} < a`
  (`a ∈ E`): **`γ, β, η < a`** (step ◆< of `R2.CitedLv`).
* (◇ι) For `α := ϑᵗ(ξ)`: `Δ` is the `Δ` of C, `Δ > 0`, so `τ < α ∈ E` (E); `ξ^* < α` (L), so `γ, β, η < α` (◇<) and
  `Δ ∈ Tᵗ_α` (D: `Δ^* ≤ ξ^* < α`).  By I: `ι(Ω₁) = ϑ^α(ι(0)) = ϑ^α(0) = α` (note of I, first clause, Z at the base
  `α`); `ι(Ω₁ + c) = ι(Ω₁) + ι(c) = α + c` for `0 < c < α` (second clause, `Ω₁ + c > Ω₁`; first clause); so
  `ι(ϑ₁(Ω₁ + c)) = ϑ^α(α + c) = ϑ^α(1 + (α + c)) = ω̄_{α+α+c} = ω^{α+1+α+c} = α·α·ω^c` (W at the base `α`, `m = 0`,
  `Ω₀ = α`; `(P ∖ E) ∩ α` has order type `α`, and the members of `P ∖ E` from `α` on are `ω^{α+1+a}` below `ε_{α+1}`);
  with ◆ι of `R2.CitedLv` (`ι(ϑ₁(b)) = α·ω^b`, `b < α`) and the second clause: **`ι_{τ,α}(Δ) = α·α·γ + α·β =
  α·(α·γ + β)`**.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

open Classical in
/-- **`ζᵗ_α` of [W07a] Def 4.11** for `α = ϑᵗ(Δ + η)` with a general multiple `Δ` of `Ω₁` (text G, read as in step ★ζ
of `R2.CitedLu`: a supremum of terms exceeds `η` iff one of them does): `logend(η)` if `η < ϑᵗ(Δ + σ)` for some
`σ < η`, else `0`.  `luZeta τ β η` is `lqZeta τ (Ω₁·β) η`. -/
noncomputable def lqZeta (τ Δ η : Ordinal.{0}) : Ordinal.{0} :=
  if ∃ σ, σ < η ∧ η < vt τ (Δ + σ) then lg η else 0

/-- **[W07a] Def 3.22, Lemma 4.2 (`m = 1`), the remark after Def 3.1, Theorem 3.23** (texts T, W, Z, Θ): for
`γ, β, η ∈ Tᵗ ∩ Ω₁` with `γ ≥ 1`, `Ω₁·(Ω₁·γ + β) + η ∈ Tᵗ`.

Our steps.  Step ◇Δ of the module docstring: `Ω₁·(Ω₁·γ + β)` is the `=NF`-sum of the terms `ϑ₁(Ω₁ + cₗ)` (◇c: `Ω₁ + cₗ
∈ T₀ ∩ Ω₃`, T third clause with `k = 1 ≥ 0`) and `ϑ₁(bₗ)` (◆β of `R2.CitedLv`, ★β of `R2.CitedLu`), each in `T₀`; so
`Ω₁·(Ω₁·γ + β) ∈ T₀` and `Ω₁·(Ω₁·γ + β) + η ∈ T₀` (T, second clause).  For `γ = 1`, `β = 0` this is `lgArg_mem` of
`R2.CitedLg`. -/
axiom lqArg_mem {τ γ β η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hγ1 : 1 ≤ γ) (hγ : γ ∈ Tset τ)
    (hγΩ : γ < Om1) (hβ : β ∈ Tset τ) (hβΩ : β < Om1) (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    Om1 * (Om1 * γ + β) + η ∈ Tset τ

/-- **[W07a] Lemma 3.30, the direction `⇐`, with Def 3.28** (texts L, S): for `γ', β', η', γ, β, η ∈ Tᵗ ∩ Ω₁` with
`γ ≥ 1` (`γ' = 0` allowed), `ξ' := Ω₁·(Ω₁·γ' + β') + η' < ξ := Ω₁·(Ω₁·γ + β) + η` and `γ', β', η' < ϑᵗ(ξ)`:
`ϑᵗ(ξ') < ϑᵗ(ξ)`.

Our steps.  `ξ' ∈ Tᵗ ∩ Ω₂` (◇Δ; for `γ' = 0` step ◆β of `R2.CitedLv`, ★β of `R2.CitedLu`) and `ξ ∈ Tᵗ ∩ Ω₂` (◇Δ).
By ◇* (◆* of `R2.CitedLv` for `γ' = 0`), `ξ'^* ≤ max(γ', β', η') < ϑ₀(ξ)`.  So `ξ' < ξ ∧ ξ'^* < ϑ₀(ξ)`, the first
disjunct of the right side of Lemma 3.30 (`m = 0`), and `ϑ₀(ξ') < ϑ₀(ξ)`.  (`lgVt_lt_low` of `R2.CitedLg` is the case
`γ = 1`, `β = 0`, `γ' = 0`.) -/
axiom lqVt_lt {τ γ' β' η' γ β η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1)
    (hγ' : γ' ∈ Tset τ) (hγ'Ω : γ' < Om1) (hβ' : β' ∈ Tset τ) (hβ'Ω : β' < Om1)
    (hη' : η' ∈ Tset τ) (hη'Ω : η' < Om1) (hγ1 : 1 ≤ γ) (hγ : γ ∈ Tset τ) (hγΩ : γ < Om1)
    (hβ : β ∈ Tset τ) (hβΩ : β < Om1) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (harg : Om1 * (Om1 * γ' + β') + η' < Om1 * (Om1 * γ + β) + η)
    (hγ'θ : γ' < vt τ (Om1 * (Om1 * γ + β) + η)) (hβ'θ : β' < vt τ (Om1 * (Om1 * γ + β) + η))
    (hη'θ : η' < vt τ (Om1 * (Om1 * γ + β) + η)) :
    vt τ (Om1 * (Om1 * γ' + β') + η') < vt τ (Om1 * (Om1 * γ + β) + η)

/-- **[W07a] Lemma 3.30, the direction `⇒`, with Def 3.28** (texts L, S): for `ξ ∈ Tᵗ ∩ Ω₂` and `γ, β, η ∈ Tᵗ ∩ Ω₁`
with `γ ≥ 1` and `γ, β, η < ϑᵗ(ξ)`: `ϑᵗ(ξ) < ϑᵗ(Ω₁·(Ω₁·γ + β) + η)` implies `ξ < Ω₁·(Ω₁·γ + β) + η`.

Our steps.  `ζ := Ω₁·(Ω₁·γ + β) + η ∈ Tᵗ ∩ Ω₂` (◇Δ) and `ζ^* ≤ max(γ, β, η) < ϑᵗ(ξ)` (◇*).  Lemma 3.30 (`m = 0`,
`α = ξ`): `ϑ₀(ξ) < ϑ₀(ζ)` gives `ξ < ζ ∧ ξ^* < ϑ₀(ζ)` or `ϑ₀(ξ) ≤ ζ^*`; the second is impossible.  So `ξ < ζ`.
(`lgLt_of_vt_lt` of `R2.CitedLg` is the case `γ = 1`, `β = 0`.) -/
axiom lqLt_of_vt_lt {τ ξ γ β η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hξ : ξ ∈ Tset τ)
    (hξ2 : ξ < OmTwo) (hγ1 : 1 ≤ γ) (hγ : γ ∈ Tset τ) (hγΩ : γ < Om1) (hβ : β ∈ Tset τ) (hβΩ : β < Om1)
    (hη : η ∈ Tset τ) (hηΩ : η < Om1) (hγξ : γ < vt τ ξ) (hβξ : β < vt τ ξ) (hηξ : η < vt τ ξ)
    (h : vt τ ξ < vt τ (Om1 * (Om1 * γ + β) + η)) : ξ < Om1 * (Om1 * γ + β) + η

/-- **[W07a] Lemma 3.30 (`α^* < ϑ₀(α)`), Lemma 4.3, Def 3.28** (texts L, E, S): for `γ, β, η ∈ Tᵗ ∩ Ω₁` with `γ ≥ 1`:
`γ, β, η < ϑᵗ(Ω₁·(Ω₁·γ + β) + η)`.

Our steps.  `ξ := Ω₁·(Ω₁·γ + β) + η ∈ Tᵗ ∩ Ω₂` (◇Δ).  Lemma 3.30 (`m = 0`): `ξ^* < ϑ₀(ξ) =: a`.  By Lemma 4.3 (`Δ =
Ω₁·(Ω₁·γ + β) > 0`), `τ < a ∈ E`.  By ◇< (with `ξ^* < a`), `γ, β, η < a`. -/
axiom lqLevel_lt_vt {τ γ β η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hγ1 : 1 ≤ γ) (hγ : γ ∈ Tset τ)
    (hγΩ : γ < Om1) (hβ : β ∈ Tset τ) (hβΩ : β < Om1) (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    γ < vt τ (Om1 * (Om1 * γ + β) + η) ∧ β < vt τ (Om1 * (Om1 * γ + β) + η) ∧
      η < vt τ (Om1 * (Om1 * γ + β) + η)

/-- **[W07b] Def 4.1, the case `δ > α` with `cr(α, δ) = m`, with [W07a] Def 7.5, Def 7.1, Def 6.1, Def 4.11, Def 4.6,
Def 7.15, Convention 6.6, Convention 4.1, Lemma 6.3, Lemma 4.2, Lemma 4.3, Lemma 3.30, Def 3.28, Def 3.22** (texts H,
Λ, I, D, G, LOC, CR, TR, C, W, E, L, S, T): for `γ, β, η ∈ Tᵗ ∩ Ω₁`, `γ ≥ 1`, `α := ϑᵗ(Ω₁·(Ω₁·γ + β) + η)`,
`g := log_ω γ` and `δ := α·α·ω^g`: **`lhᵗ(α) = lhᵗ(δ) + (−δ + (α·(α·γ + β) + ζᵗ_α))`**, with `ζᵗ_α =
lqZeta τ (Ω₁·(Ω₁·γ + β)) η`.

Our steps.  `α = ϑᵗ(Δ + η)` with `Δ = Ω₁·(Ω₁·γ + β)` (C), `α ∈ Tᵗ` (◇Δ, T), `τ < α ∈ E`, `γ, β, η < α`, `Δ ∈ Tᵗ_α`
and `ι_{τ,α}(Δ) = α·(α·γ + β)` (◇ι); `ζᵗ_α = lqZeta τ Δ η` (G, read as in ★ζ of `R2.CitedLu`), `ζᵗ_α ≤ η < α`; so
`λᵗ_α = α·(α·γ + β) + ζᵗ_α` (Λ, `α ∈ E`).
* `δ = (λᵗ_α)^*` (H, the note): `γ = ω^g·k + γ''` with `1 ≤ k < ω`, `γ'' < ω^g`; `λᵗ_α = ω^{α·2+g}·k + (α·α·γ'' + α·β
  + ζᵗ_α)` with the rest `< ω^{α·2+g}` (`β, ζᵗ_α < α`), so `ω^{α·2+g} ≤ λᵗ_α < ω^{α·2+g}·(k + 1) < ω^{α·2+g+1}`: the
  maximum additive principal number `≤ λᵗ_α` is `ω^{α·2+g} = α·α·ω^g = δ`.  `δ ≥ α·α > α`: the branch `δ > α` of H
  (consistent with its "`δ ≤ α` i.e. `Δ < ϑ₁(1)`", as `Δ ≥ Ω₁·Ω₁`).
* The `α`-localization of `δ` in `Tᵗ` (LOC, Convention 6.6): in `T^α`, `δ = ϑ^α(α + g)` (W at the base `α`: `ϑ^α(1 +
  (α + g)) = ω̄_{α+α+g} = ω^{α·2+g}`; `g < α` as `g ≤ γ < α`), and `Sub^α₀(δ) = {δ} ∪ Sub^α₀(α + g) ⊆ {δ, α + g, α, 0,
  g}` (S; `α = ϑ^α(0)` by Z at the base `α`, `g < α` a parameter of `T^α`), whose members in `P ∩ [α, Ω₁)` are `α` and
  `δ` (`α + g` is not additive principal for `0 < g < α`).  So the localization is `(α = δ₀, δ₁ = δ)`, `m = 1`.
  `δ ∈ T^α_{α⁺}` (D: `δ^{*α} = δ < ε_{α+1} ≤ ϑ^α(Δ) = α⁺`, TR and E at the base `α`), hence `δ^{t^α_τ} = δ` (TR).
* `cr(α, δ)` (CR with `n = m = 1`, and the remark after it): `{1, …, n − 1} = ∅`, so `cr(α, δ) = m`, and H gives
  `lhᵗ(α) = lhᵗ(δ) + ρ` with `ρ := −δ + λᵗ_α = −δ + (α·(α·γ + β) + ζᵗ_α)`.
This is the computation of `lvLhT_gen` of `R2.CitedLv` with `ι_{τ,α}(Δ) = α·(α·γ + β)` in place of `α·β`; it extends
the lower bound `lgLhT_sq` of `R2.CitedLg` (`lhᵗ(α) ≥ δ ≥ α·α`).  The value `lhᵗ(δ)` is not part of this axiom
(`δ ∈ P ∖ E`: [W07b] Theorem 2.2 and Theorem 5.3 through `le1R_thm22`, `lh_eq_lhT`). -/
axiom lqLhT {τ γ β η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hγ1 : 1 ≤ γ) (hγ : γ ∈ Tset τ)
    (hγΩ : γ < Om1) (hβ : β ∈ Tset τ) (hβΩ : β < Om1) (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    lhT τ (vt τ (Om1 * (Om1 * γ + β) + η)) =
      lhT τ (vt τ (Om1 * (Om1 * γ + β) + η) * vt τ (Om1 * (Om1 * γ + β) + η) * ω ^ log ω γ) +
        ((vt τ (Om1 * (Om1 * γ + β) + η) * (vt τ (Om1 * (Om1 * γ + β) + η) * γ + β) +
            lqZeta τ (Om1 * (Om1 * γ + β)) η) -
          vt τ (Om1 * (Om1 * γ + β) + η) * vt τ (Om1 * (Om1 * γ + β) + η) * ω ^ log ω γ)

/-- **[W07a] Def 5.1 (second and third clauses), Lemma 5.3 (b), (c), Def 3.28, Lemma 4.2, the remark after Def 3.1**
(texts P, S, W, Z): for bases `σ < τ` and `γ, β ∈ Tᵗ[σ] ∩ Ω₁` with `γ ≥ 1`: `Ω₁·(Ω₁·γ + β) ∈ Tᵗ[σ]` and
`π_{σ,τ}(Ω₁·(Ω₁·γ + β)) = Ω₁·(Ω₁·π_{σ,τ}(γ) + π_{σ,τ}(β))`.

Our steps.  `Ω₁·(Ω₁·γ + β) = ϑ₁(Ω₁ + c₁) + ⋯ + ϑ₁(Ω₁ + cᵢ) + ϑ₁(b₁) + ⋯ + ϑ₁(bⱼ)` (◇Δ).  As in the docstring of
`lvPi_mul` of `R2.CitedLv`: for `y ∈ Tᵗ ∩ Ω₁`, `ω^y ∈ Tᵗ[σ] ⇔ y ∈ Tᵗ[σ]`, and then `π_{σ,τ}(ω^y) = ω^{π_{σ,τ}(y)}`;
since `Parᵗ(γ) = ⋃ₗ Parᵗ(ω^{cₗ})` (S) each `cₗ ∈ Tᵗ[σ]`, likewise each `bₗ`.  By S, `Parᵗ(Ω₁ + c) = {0} ∪ Parᵗ(c)`
and `Parᵗ(ϑ₁(Ω₁ + c)) = Parᵗ(Ω₁ + c)`, so `Parᵗ(Ω₁·(Ω₁·γ + β)) = {0} ∪ ⋃ₗ Parᵗ(cₗ) ∪ ⋃ₗ Parᵗ(bₗ) ⊆ σ` and
`Ω₁·(Ω₁·γ + β) ∈ Tᵗ[σ]`.  P, second clause (the sum is `> τ`): `π` of the sum is the sum of the `π`-images; third
clause (`k = 1 > 0`): `π(ϑ₁(Ω₁ + c)) = ϑ₁(π(Ω₁ + c)) = ϑ₁(π(Ω₁) + π(c)) = ϑ₁(Ω₁ + π(c))` (second clause, `Ω₁ + c >
τ`; `π(Ω₁) = Ω₁`, the theorem `pi_Om1` of `R2.Cited`), and `π(ϑ₁(b)) = ϑ₁(π(b))`.  With ◇c and `ϑ₁(b) = Ω₁·ω^b`
(W, Z, over `σ`): `π(Ω₁·(Ω₁·γ + β)) = Σₗ Ω₁·Ω₁·ω^{π(cₗ)} + Σₗ Ω₁·ω^{π(bₗ)}`; by Lemma 5.3 (b), (c), `π(γ) =ANF
Σₗ ω^{π(cₗ)}` and `π(β) =ANF Σₗ ω^{π(bₗ)}`, so `π(Ω₁·(Ω₁·γ + β)) = Ω₁·(Ω₁·π(γ) + π(β))`.  (`lgPi_OmOm` of
`R2.CitedLg` is the case `γ = 1`, `β = 0`.) -/
axiom lqPi {σ τ γ β : Ordinal.{0}} (h : Bases σ τ) (hγ1 : 1 ≤ γ) (hγ : γ ∈ TB τ σ) (hγΩ : γ < Om1)
    (hβ : β ∈ TB τ σ) (hβΩ : β < Om1) :
    Om1 * (Om1 * γ + β) ∈ TB τ σ ∧ pi σ τ (Om1 * (Om1 * γ + β)) = Om1 * (Om1 * pi σ τ γ + pi σ τ β)

end Googology.Trans.PoR.InaccPsi.R2
