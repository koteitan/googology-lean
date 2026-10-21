import Googology.Trans.PoR.InaccPsi.R2.CitedLv

set_option autoImplicit false

/-!
# Cited facts of Wilken 2007, as axioms, at the arguments `Δ + η` with `Δ ≥ Ω₁·Ω₁ = ϑ₁(Ω₁)`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.

Same conventions as `R2.CitedLu` and `R2.CitedLv` (`Ω₁ = Om1`, `Ω₂ = OmTwo`, `Tset τ = Tᵗ`, `vt τ = ϑᵗ = ϑ₀`, `lhT τ =
lhᵗ`, every base `τ` a countable `ε`-number).  `R2.CitedLu` and `R2.CitedLv` state the facts only for arguments
`Ω₁·β + η` with `β < Ω₁`, i.e. below `Ω₁·Ω₁`; here the first argument `Ω₁·Ω₁` and the arguments above it.

What `R2.CitedLu` / `R2.CitedLv` already give and is **not** restated: `vt_memTwo` (values in `Tᵗ ∩ P ∩ [τ, Ω₁)`),
`vt_rep`, `vt_E_iff` (`R2.CitedEv`), `lh_eq_lhT` (`R2.CitedL`), the facts at `Ω₁·β + η` for `β < Ω₁` (`lvArg_mem`,
`lvVt_lt_gen`, `lvLt_of_vt_lt`, `lvLevel_lt_vt`, `lvLhT_gen` and the `Lu` axioms).  The comparisons below are the
two directions of Lemma 3.30 with `γ = Ω₁·Ω₁ + η`; the reach is a lower bound from Def 4.1 for every `Δ ≥ Ω₁·Ω₁`.

Literal texts used below (all of [W07a] unless said otherwise; the full quotations of T, Θ, U, Z, S, L, C, W, E, G, D
are in the module docstring of `R2.CitedLu`, and of I, Λ, H in that of `R2.CitedLv`):
* (T) Def 3.22: "`T_m` is defined inductively as follows: • `Ω_m ⊆ T_m` • `ξ, η ∈ T_m ⇒ ξ + η ∈ T_m` • `ξ ∈ T_m ∩
  Ω_{k+2} ⇒ ϑ_k(ξ) ∈ T_m` for `k ≥ m`."
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
* (U) Remark after Cor 3.24: each `T_m` "provides a unique term for every ordinal which is element of some `Tⁿ_m`".
* (C) Convention 4.1: "`α = ϑᵗ(Δ + η)` automatically means that `ξ = Δ + η` is a decomposition such that `Ω₁ | Δ` and
  `η < Ω₁`."
* (E) Lemma 4.3: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ`.  Then `τ < α ∈ E ⇔ Δ > 0`."
* (D) Def 6.1: "`Tᵗ_α := {β ∈ Tᵗ | β^{*τ} < α}`."
* (I) Def 7.1: "Let `α = ϑᵗ(Δ + η)` where `Δ > 0`.  We define `ι_{τ,α} : Tᵗ_α → T^α` … • `ι_{τ,α}(ξ) := ξ` if `ξ < α`
  • `ι_{τ,α}(ξ) := ι_{τ,α}(ξ₁) + ι_{τ,α}(ξ₂)` if `ξ =NF ξ₁ + ξ₂ > Ω₁` • `ι_{τ,α}(ξ) := ϑ_k(ι_{τ,α}(η))` if `ξ =
  ϑ_{k+1}(η)` where `k < ω`.  Note that `ι_{τ,α}(ϑ₁(η)) = ϑ^α(ι_{τ,α}(η))`."  Lemma 7.2: "(b) `ι_{τ,α}` preserves `<`."
* (Λ) Def 7.5: "`λᵗ_α := ι_{τ,α}(Δ) + ζᵗ_α` if `α ∈ E`, `ζᵗ_α` otherwise."
* (H) [W07b] Def 4.1: "• `lhᵗ(α) := 0` if `α ≤ τ` • `lhᵗ(α) := α` if `α =NF α₁ + α₂ ≥ τ` • If `α = ϑᵗ(Δ + η) > τ` we
  set `δ := (λᵗ_α)^*`. • `lhᵗ(α) := α + λᵗ_α` if `δ ≤ α`, i.e. `Δ < ϑ₁(1)` • If `δ > α` let `(α = δ₀, …, δ_m = δ)` be
  the `α`-localization of `δ` in `Tᵗ`.  `lhᵗ(α) := lhᵗ(δᵢ) + λᵗ_α` if `i := cr(α, δ) < m`, `lhᵗ(δ) + ρ` where `ρ :=
  −δ + λᵗ_α` otherwise."  "Note that `(λᵗ_α)^*` is the maximum additive principal number less than or equal to
  `λᵗ_α`."

Our steps (used in the docstrings below; `τ` a countable `ε`-number):
* (◇Ω) `Ω₁ = ϑ₁(0)` (Z) and `Ω₁ ∈ T₀ ∩ Ω₃`, so `ϑ₁(Ω₁) ∈ T₀` (T, third clause, `k = 1 ≥ 0`).  By W with `m = 1`,
  `α = Ω₁`: `ϑ₁(Ω₁) = ϑ₁(1 + Ω₁) = ω̄_{Ω₁+Ω₁}`.  The members of `P ∖ E` from `Ω₁` on are `ω^{Ω₁+1+c}`
  (`Ω₁ = ω^{Ω₁}` is an
  `ε`-number and there is none in `(Ω₁, ε_{Ω₁+1})`), and `(P ∖ E) ∩ Ω₁` has order type `Ω₁`; so `ω̄_{Ω₁+c} = ω^{Ω₁+1+c}`
  and **`ϑ₁(Ω₁) = ω^{Ω₁+1+Ω₁} = ω^{Ω₁·2} = Ω₁·Ω₁`**.  It lies in `[Ω₁, Ω₂)` (L, `m = 1`).
* (◇*) `Sub₀(ϑ₁(Ω₁)) = {ϑ₁(Ω₁)} ∪ Sub₀(ϑ₁(0)) = {ϑ₁(Ω₁), Ω₁, 0}` (S, `k = 1 ≥ m = 0`; `0` a parameter), none of which
  is in `P ∩ [τ, Ω₁)`; so **`(Ω₁·Ω₁)^* = 0`**, and for `η ∈ Tᵗ ∩ Ω₁`, `Ω₁·Ω₁ + η =NF ϑ₁(Ω₁) + η` has `(Ω₁·Ω₁ + η)^* =
  η^* ≤ η` (S, second clause; step ★1 of `R2.CitedLu`: every member of `P₀(η)` is `≤ η`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- **[W07a] Def 3.22, Lemma 4.2 (`m = 1`), the remark after Def 3.1** (texts T, W, Z): for `η ∈ Tᵗ ∩ Ω₁`,
`Ω₁·Ω₁ + η ∈ Tᵗ`.

Our steps.  Step ◇Ω: `Ω₁·Ω₁ = ϑ₁(Ω₁) ∈ T₀` (`Ω₁ = ϑ₁(0) ∈ T₀ ∩ Ω₃`, T third clause with `k = 1 ≥ 0`); then
`Ω₁·Ω₁ + η ∈ T₀` by the second clause of T. -/
axiom lgArg_mem {τ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hη : η ∈ Tset τ) (hη1 : η < Om1) :
    Om1 * Om1 + η ∈ Tset τ

/-- **[W07a] Lemma 3.30, the direction `⇐`, with Def 3.28** (texts L, S): for `β' ∈ Tᵗ ∩ Ω₁`, `η', η ∈ Tᵗ ∩ Ω₁` with
`β' < ϑᵗ(Ω₁·Ω₁ + η)` and `η' < ϑᵗ(Ω₁·Ω₁ + η)`: `ϑᵗ(Ω₁·β' + η') < ϑᵗ(Ω₁·Ω₁ + η)`.

Our steps.  `α := Ω₁·β' + η' ∈ Tᵗ ∩ Ω₂` (step ◆β of `R2.CitedLv` for `β' ≥ τ`, step ★β of `R2.CitedLu` for
`β' < τ`; for `β' = 0`, `α = η'`), and `γ := Ω₁·Ω₁ + η ∈ Tᵗ ∩ Ω₂` (◇Ω, `lgArg_mem`).  `α < Ω₁·(β' + 1) ≤ Ω₁·Ω₁ ≤ γ`.
By ◆* of `R2.CitedLv` (★β, ★1 of `R2.CitedLu` for `β' < τ`), `α^* ≤ max(β', η') < ϑ₀(γ)`.  So the first disjunct of
the right side of Lemma 3.30 (`m = 0`) holds, and `ϑ₀(α) < ϑ₀(γ)`. -/
axiom lgVt_lt_low {τ β' η' η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1)
    (hβ' : β' ∈ Tset τ) (hβ'1 : β' < Om1) (hη' : η' ∈ Tset τ) (hη'1 : η' < Om1)
    (hη : η ∈ Tset τ) (hη1 : η < Om1)
    (hβ'θ : β' < vt τ (Om1 * Om1 + η)) (hη'θ : η' < vt τ (Om1 * Om1 + η)) :
    vt τ (Om1 * β' + η') < vt τ (Om1 * Om1 + η)

/-- **[W07a] Lemma 3.30, the direction `⇒`, with Def 3.28** (texts L, S): for `ξ ∈ Tᵗ ∩ Ω₂` and `η ∈ Tᵗ ∩ Ω₁` with
`η < ϑᵗ(ξ)`: `ϑᵗ(ξ) < ϑᵗ(Ω₁·Ω₁ + η)` implies `ξ < Ω₁·Ω₁ + η`.

Our steps.  `γ := Ω₁·Ω₁ + η ∈ Tᵗ ∩ Ω₂` (◇Ω), and `γ^* ≤ η < ϑᵗ(ξ)` (◇*).  Lemma 3.30 (`m = 0`, `α = ξ`): `ϑ₀(ξ) <
ϑ₀(γ)` gives `ξ < γ ∧ ξ^* < ϑ₀(γ)` or `ϑ₀(ξ) ≤ γ^*`; the second is impossible.  So `ξ < γ`.  (The trap of the
removed axiom `lvQuot_mem` does not arise: no quotient is formed here.) -/
axiom lgLt_of_vt_lt {τ ξ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1)
    (hξ : ξ ∈ Tset τ) (hξ2 : ξ < OmTwo) (hη : η ∈ Tset τ) (hη1 : η < Om1) (hηξ : η < vt τ ξ)
    (h : vt τ ξ < vt τ (Om1 * Om1 + η)) : ξ < Om1 * Om1 + η

/-- **[W07a] Def 3.22, Remark after Cor 3.24, Def 3.28, Lemma 3.30 (`m = 1`), Lemma 4.2, Theorem 3.23** (texts T, U,
S, L, W, Z, Θ): for `ξ ∈ Tᵗ` with `ξ < Ω₁·Ω₁`, the quotient `ξ / Ω₁` lies in `Tᵗ`.

Our steps.  By U, `ξ` has a unique term; its `=NF` summands `≥ Ω₁` are values of `ϑ_k`, `k ≥ 1` (L: `ϑ₀`-values and
parameters are `< Ω₁`), and since `ξ < Ω₂`, `k = 1` (L, `m ≥ 2` gives values `≥ Ω₂`): `ξ =NF ϑ₁(b₁) + ⋯ + ϑ₁(bⱼ) + r`
with `r < Ω₁` and `bᵢ ∈ T₀ ∩ Ω₃` (T, third clause and U).  Each `ϑ₁(bᵢ) ≤ ξ < ϑ₁(Ω₁)` (◇Ω), so by L (`m = 1`) `bᵢ <
Ω₁ ∧ …` or `ϑ₁(bᵢ) ≤ Ω₁^{*1} = Ω₁` (S: `P₁(Ω₁) = {Ω₁}`), i.e. `bᵢ = 0`; in both cases `bᵢ < Ω₁`.  By W and Z,
`ϑ₁(bᵢ) = Ω₁·ω^{bᵢ}` (step ★p of `R2.CitedLu`), so `ξ / Ω₁ = ω^{b₁} + ⋯ + ω^{bⱼ}`.  The `bᵢ` lie in `T₀ ∩ Ω₁ = θ₀`
(Θ); `θ₀ = sup_n ϑ₀(⋯(ϑ_n(0))⋯)` is a supremum of `ε`-numbers (E: each `ϑ₀(Δ)` with `Δ = ϑ₁(⋯) > 0`), hence an
`ε`-number, so `ω^{bᵢ} < θ₀` and the finite sum `ξ / Ω₁ < θ₀`, i.e. `ξ / Ω₁ ∈ Tᵗ` (Θ: `T₀ ∩ Ω₁ = θ₀` is an initial
segment).  The hypothesis `ξ < Ω₁·Ω₁` is needed: at `ξ = Ω₁·Ω₁ = ϑ₁(Ω₁)` the quotient is `Ω₁ ∉ Tᵗ ∩ Ω₁`. -/
axiom lgQuot_mem {τ ξ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hξ : ξ ∈ Tset τ) (hξ2 : ξ < Om1 * Om1) :
    ξ / Om1 ∈ Tset τ

/-- **[W07b] Def 4.1, with [W07a] Def 7.5, Def 7.1, Lemma 7.2 (b), Def 6.1, Def 4.11, Lemma 4.2, Lemma 4.3, Lemma 3.30,
Def 3.28, Convention 4.1** (texts H, Λ, I, D, G, W, Z, E, L, S, C): for `ξ ∈ Tᵗ ∩ Ω₂` with `ξ ≥ Ω₁·Ω₁` and `α :=
ϑᵗ(ξ)`: **`α·α ≤ lhᵗ(α)`**.

Our steps.  Write `ξ = Δ + η` (C); `Ω₁ | Ω₁·Ω₁` and `η < Ω₁` give `Δ ≥ Ω₁·Ω₁ > 0`.  By E, `τ < α ∈ E`.
`ι := ι_{τ,α}` is
defined on `Tᵗ_α` (I), which contains `Δ` (D: `Δ^* ≤ ξ^* < α` by S and L) and `Ω₁·Ω₁` (D: `(Ω₁·Ω₁)^* = 0`, ◇*).
* `ι(Ω₁·Ω₁) = α·α`: `Ω₁·Ω₁ = ϑ₁(Ω₁)` (◇Ω) and `Ω₁ = ϑ₁(0)` (Z), so by the third clause of I (`k = 0`) and the note,
  `ι(Ω₁) = ϑ^α(ι(0)) = ϑ^α(0) = α` (first clause, `0 < α`; Z at the base `α`, "`ϑ₀(0) = τ`" with `τ := α`) and
  `ι(Ω₁·Ω₁) = ϑ^α(ι(Ω₁)) = ϑ^α(α) = ϑ^α(1 + α) = ω̄_{α+α}` (W at the base `α`, `m = 0`, `Ω₀ = α`).  The members of
  `P ∖ E` from `α` on are `ω^{α+1+c}` below `ε_{α+1}` and `(P ∖ E) ∩ α` has order type `α` (`α ∈ E`), so `ω̄_{α+α} =
  ω^{α+1+α} = ω^{α·2} = α·α`.
* `λᵗ_α = ι(Δ) + ζᵗ_α ≥ ι(Δ) ≥ ι(Ω₁·Ω₁) = α·α` (Λ, `α ∈ E`; Lemma 7.2 (b) for `Ω₁·Ω₁ ≤ Δ`).
* `δ := (λᵗ_α)^*` (H) is the maximum additive principal number `≤ λᵗ_α` (H, the note); `α·α = ω^{α·2}` is additive
  principal and `≤ λᵗ_α`, so `δ ≥ α·α > α`: the branch `δ > α` of H.  In its first case `lhᵗ(α) = lhᵗ(δᵢ) + λᵗ_α ≥
  λᵗ_α`; in its second `lhᵗ(α) = lhᵗ(δ) + (−δ + λᵗ_α) ≥ δ + (−δ + λᵗ_α) = λᵗ_α`, using `lhᵗ(β) ≥ β` for every `β ∈
  Tᵗ ∩ (τ, Ω₁)` (induction on `hᵗ` along H: the second clause gives `β`, the third `β + λᵗ_β ≥ β`, the fourth
  `lhᵗ(δ'ᵢ) + λᵗ_β ≥ λᵗ_β ≥ δ' > β` and `lhᵗ(δ') + ρ ≥ δ' > β` by the induction hypothesis for `δ'`).
So `lhᵗ(α) ≥ λᵗ_α ≥ α·α`. -/
axiom lgLhT_sq {τ ξ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hξ : ξ ∈ Tset τ) (hξ2 : ξ < OmTwo)
    (hΩ : Om1 * Om1 ≤ ξ) : vt τ ξ * vt τ ξ ≤ lhT τ (vt τ ξ)

/-- **[W07a] Def 5.1 (third and first clauses), Lemma 5.3, Def 3.28, the remark after Def 3.1, Lemma 4.2** (texts P, S,
Z, W; P: "`π_{σ,τ}(ξ) := ξ` if `ξ < σ` • … • `π_{σ,τ}(ξ) := ϑ_k(π_{σ,τ}(η))` if `ξ = ϑ_k(η)` for some `k > 0` and `η ∈
Tᵗ[σ] ∩ Ω_{k+2}`", Def 5.1: "`Tᵗ[σ] := {α ∈ Tᵗ | Parᵗ(α) ⊆ σ}`"): for bases `σ < τ`, `Ω₁·Ω₁ ∈ Tᵗ[σ]` and
`π_{σ,τ}(Ω₁·Ω₁) = Ω₁·Ω₁`.

Our steps.  `Ω₁·Ω₁ = ϑ₁(Ω₁)` and `Ω₁ = ϑ₁(0)` (◇Ω, over `τ` and over `σ` alike: Lemma 4.2 with `m = 1` and Z do not
depend on the base).  By S, `Subᵗ₀(ϑ₁(Ω₁)) = {ϑ₁(Ω₁), Ω₁, 0}`, so `Parᵗ(Ω₁·Ω₁) = {0} ⊆ σ` and `Ω₁·Ω₁ ∈ Tᵗ[σ]`
(also `Ω₁ ∈ Tᵗ[σ]`, `0 ∈ Tᵗ[σ]`).  P, first clause: `π(0) = 0`; third clause (`k = 1 > 0`, `η = 0`): `π(Ω₁) =
ϑ₁(π(0)) = ϑ₁(0) = Ω₁` (this is the axiom `pi_Om1` of `R2.Cited`); third clause (`k = 1`, `η = Ω₁ ∈ Tᵗ[σ] ∩ Ω₃`):
`π(ϑ₁(Ω₁)) = ϑ₁(π(Ω₁)) = ϑ₁(Ω₁) = Ω₁·Ω₁`. -/
axiom lgPi_OmOm {σ τ : Ordinal.{0}} (h : Bases σ τ) :
    Om1 * Om1 ∈ TB τ σ ∧ pi σ τ (Om1 * Om1) = Om1 * Om1

end Googology.Trans.PoR.InaccPsi.R2
