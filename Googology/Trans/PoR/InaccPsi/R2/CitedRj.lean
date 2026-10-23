import Googology.Trans.PoR.InaccPsi.R2.CitedLq
import Googology.Trans.PoR.InaccPsi.R2.RjCode

set_option autoImplicit false

/-!
# Cited facts of Wilken 2007, as axioms, ONCE for every level `Δ = Ω₁·M` with `Ω₁ ≤ M < ε_{Ω₁+1}`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.

Same conventions as `R2.CitedLu`, `R2.CitedLv`, `R2.CitedLg`, `R2.CitedLq` (`Ω₁ = Om1`, `Ω₂ = OmTwo`, `Tset τ = Tᵗ`,
`vt τ = ϑᵗ = ϑ₀`, `lhT τ = lhᵗ`, `lg = logend`, every base `τ` a countable `ε`-number).  New here: the levels are
**generic**.  `ε_{Ω₁+1} = Gg.ggE` is the least `ε`-number above `Ω₁`; a **code** is an `M < ε_{Ω₁+1}`; its countable
leaves (the countable remainders and countable exponents of its hereditary Cantor normal form over `{0, Ω₁}`) have
the maximum `rjDat M` (`R2.Rj.rjDat`, an own definition; `rjDat M = M` for `M < Ω₁`).  The arguments are
`ξ = Ω₁·M + η` with `η ∈ Tᵗ ∩ Ω₁`: for `Ω₁ ≤ M` the multiple of `Ω₁` (Convention 4.1) is `Δ = Ω₁·M ≥ Ω₁·Ω₁`, which
covers `R2.CitedLq` (`M = Ω₁·γ + β`, `1 ≤ γ < Ω₁`) and every `M` up to `ε_{Ω₁+1}` (all `Δ < ε_{Ω₁+1}`, e.g.
`Δ ≥ Ω₁³`).  The reading `Θ_α = Gg.ggTh α` is the order type of the codes over `α` below a given ordinal.

What is **not** restated (checked first): `R2.CitedLq` (`lqArg_mem`, `lqVt_lt`, `lqLt_of_vt_lt`, `lqLevel_lt_vt`,
`lqLhT`, `lqPi`: the levels `M = Ω₁·γ + β`), `R2.CitedLg`, `R2.CitedLv`, `R2.CitedLu` (levels `M < Ω₁` and
`M = Ω₁`), `riArg_T` (formerly `R2.CitedRi`, now the theorem `R2.Rk.rkArg_T`), `vt_memTwo`, `vt_rep`, `vt_E_iff` (`R2.CitedEv`), `lh_eq_lhT` (`R2.CitedL`).
The axioms below contain those of `R2.CitedLq` as the special case `M = Ω₁·γ + β` (proved in `R2.RjFacts`:
`rjLq_arg`, `rjLq_lh`).  The former axiom `rjArgT_gamma` (the `γ` half of `riArg_T`) is the theorem
`R2.Rk.rkArgT_gamma`, from the generic cited fact `R2.rkArg_dat` of `R2.CitedRk`.

Literal texts (all of [W07a] unless said otherwise):
* (T) Def 3.22: "`Ω_m ⊆ T_m` • `ξ, η ∈ T_m ⇒ ξ + η ∈ T_m` • `ξ ∈ T_m ∩ Ω_{k+2} ⇒ ϑ_k(ξ) ∈ T_m` for `k ≥ m`."
* (Θ) Theorem 3.23: "`T_m ∩ Ω_{m+1} = θ_m = sup_{n≥m} ϑ_m(⋯(ϑ_n(0))⋯)`."
* (U) Remark after Corollary 3.24: "each `T_m` again gives rise to a notation system with parameters from `Ω_m` that
  provides a unique term for every ordinal which is element of some `Tⁿ_m` where `n > m`".
* (Z) After Def 3.1: "Note that we have `ϑⁿ_m(0) = Ω_m` for `m < n`".
* (W) Def 3.4: "Let `α ↦ ω̄_α` be the enumeration function of the additive principle numbers which are not epsilon
  numbers."  Lemma 4.2: "For any `m < ω` and any `α < Ω_{m+1}` we have `ϑ_m(1 + α) = ω̄_{Ω_m+α}`" (proof: "for
  `m = 0` by convention we have `Ω₀ = τ`").
* (S) Def 3.28: "`Subᵗ_m(α) := {α}` for parameters `α < τ`; `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ) ∪ Subᵗ_m(η)` for
  `ξ, η ∈ Tᵗ` s.t. `α =NF ξ + η > τ`; `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ)` if `k ≥ m`, `{α}` if `k < m`, for `α = ϑ_k(ξ)`
  where `ξ ∈ Tᵗ ∩ Ω_{k+2}`.  …  `P_m(α) := Subᵗ_m(α) ∩ P ∩ [Ω_m, Ω_{m+1})` and `α^{*m} := max(P_m(α) ∪ {0})`."
* (L) Lemma 3.30: "For `m < ω` the function `ϑ_m ↾ Tᵗ ∩ Ω_{m+2}` is 1-1 and has values in `P ∩ [Ω_m, Ω_{m+1})`.  Let
  `α, γ ∈ Tᵗ ∩ Ω_{m+2}`.  Then `α^{*m} < ϑ_m(α)` and `ϑ_m(α) < ϑ_m(γ) ⇔ α < γ ∧ α^{*m} < ϑ_m(γ) ∨ ϑ_m(α) ≤ γ^{*m}`."
* (C) Convention 4.1: "`α = ϑᵗ(Δ + η)` automatically means that `ξ = Δ + η` is a decomposition such that `Ω₁ | Δ` and
  `η < Ω₁`. …  we will write `α⁺` to denote the ordinal `ϑᵗ(Δ + η + 1)`."  After it: "Clearly, for the argument of a
  `ϑᵗ`-term in `Tᵗ`, to be a nonzero multiple of `Ω₁` means to be a sum of `ϑ₁`-terms."
* (E) Lemma 4.3: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ`.  Then `τ < α ∈ E ⇔ Δ > 0`."
* (G) Def 4.11: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ` such that `α > τ` be given.  We define `ζᵗ_α := logend(η)` if
  `η < sup_{σ<η} ϑᵗ(Δ + σ)`, `0` otherwise."
* (LOC) Def 4.6: "Set `α₀ := τ`.  Suppose that `αₙ` is already defined and `αₙ < α`.  Let `αₙ₊₁` be the element
  `ϑᵗ(ξ)` of `Pᵗ(α) − (αₙ + 1)` with maximal `ξ`."  Convention 6.6: "we call the sequence `(α, β₁^{t^α_τ}, …,
  β_m^{t^α_τ} = β^{t^α_τ})` the `α`-localization of `β^{t^α_τ} = β` in `Tᵗ`".
* (D) Def 6.1: "`Tᵗ_α := {β ∈ Tᵗ | β^{*τ} < α}`."  After it: "Note further that `Tᵗ_α ∩ Ω₁ = α`."
* (TR) Lemma 6.3: "`α⁺ = ϑ^α(Δ)`, • the restriction of `t^τ_α` to `Tᵗ_{α⁺}` is the identity, and • the restriction of
  `t^α_τ` to `T^α_{α⁺}` is the identity."
* (I) Def 7.1: "Let `α = ϑᵗ(Δ + η)` where `Δ > 0`.  We define `ι_{τ,α} : Tᵗ_α → T^α` … • `ι_{τ,α}(ξ) := ξ` if `ξ < α`
  • `ι_{τ,α}(ξ) := ι_{τ,α}(ξ₁) + ι_{τ,α}(ξ₂)` if `ξ =NF ξ₁ + ξ₂ > Ω₁` • `ι_{τ,α}(ξ) := ϑ_k(ι_{τ,α}(η))` if `ξ =
  ϑ_{k+1}(η)` where `k < ω`.  Note that `ι_{τ,α}(ϑ₁(η)) = ϑ^α(ι_{τ,α}(η))`."  Lemma 7.2: "(b) `ι_{τ,α}` preserves `<`.
  (c) `ι_{τ,α}` preserves ordinal addition.  (d) `ι_{τ,α}` maps `Tᵗ_α` onto `T^α`."
* (Λ) Def 7.5: "`λᵗ_α := ι_{τ,α}(Δ) + ζᵗ_α` if `α ∈ E`, `ζᵗ_α` otherwise."
* (CR) Def 7.15: "Define `cr(τ, α) := min{i ∈ {1, …, n − 1} | λᵗ_{αᵢ} ≥ α}` if that exists, `n` otherwise."
* (H) [W07b] Def 4.1: "• `lhᵗ(α) := 0` if `α ≤ τ` • `lhᵗ(α) := α` if `α =NF α₁ + α₂ ≥ τ` • If `α = ϑᵗ(Δ + η) > τ` we
  set `δ := (λᵗ_α)^*`. • `lhᵗ(α) := α + λᵗ_α` if `δ ≤ α`, i.e. `Δ < ϑ₁(1)` • If `δ > α` let `(α = δ₀, …, δ_m = δ)` be
  the `α`-localization of `δ` in `Tᵗ`.  `lhᵗ(α) := lhᵗ(δᵢ) + λᵗ_α` if `i := cr(α, δ) < m`, `lhᵗ(δ) + ρ` where `ρ :=
  −δ + λᵗ_α` otherwise."  "Note that `(λᵗ_α)^*` is the maximum additive principal number less than or equal to
  `λᵗ_α`."

Our steps (`τ` a countable `ε`-number, `η ∈ Tᵗ ∩ Ω₁`, `M` a code; used in every docstring below):
* (□1) `ϑ₁(m) = ω^{Ω₁+m}` for `m < ε_{Ω₁+1}`: by W (`m = 1`) `ϑ₁(1 + a) = ω̄_{Ω₁+a}`, and the members of `P ∖ E` from
  `Ω₁` on below `ε_{Ω₁+1}` are the `ω^{Ω₁+1+a}` (`(P ∖ E) ∩ Ω₁` has order type `Ω₁`, no `ε`-number lies in `(Ω₁,
  ε_{Ω₁+1})`); so `ϑ₁(m) = ω^{Ω₁+m}` for `m = 1 + a ≥ 1`, and `ϑ₁(0) = Ω₁ = ω^{Ω₁}` by Z.
* (□2) **The term of a code.**  For `Ω₁ < z < ε_{Ω₁+1}`, `z =NF ω^{e}·k + r` (`e = log_ω z ≥ Ω₁`, `k < ω`,
  `r < ω^e`) with `ω^e = ϑ₁(−Ω₁ + e)` (□1), `e < z`; a countable `z` is a sum of `ϑ₀`-terms and parameters.
  Recursively, `z` is built by the clauses of T (`k = 1 ≥ 0` for `ϑ₁`, arguments `< ε_{Ω₁+1} < Ω₂ < Ω₃`) from `Ω₁ =
  ϑ₁(0)` and its countable leaves; the leaves of `−Ω₁ + e` are those of `e`.  By (C) and (□1), `Δ = Ω₁·M =
  Σ ϑ₁(m_l)·k_l` for `M =CNF Σ ω^{m_l}·k_l`, the `m_l` codes with the leaves of `M`.  The leaves are `≤ rjDat M`, and
  `Tᵗ ∩ Ω₁` is an initial segment (Θ), so `rjDat M ∈ Tᵗ` puts every leaf, hence `Δ` and `ξ = Δ + η`, in `Tᵗ`
  (T, second clause), with `ξ < ε_{Ω₁+1} < Ω₂`.
* (□*) **`ξ^* ≤ max(rjDat M, η)`**: by S (third clause with `k = 1 ≥ 0`, second clause for the sums) the members of
  `P₀(ξ)` in `[τ, Ω₁)` are members of `P₀(c)` for `c = η`, for a countable leaf `c` of `M` inside a code `m_l`, or
  for an exponent `c = b_l` of the top countable remainder `r =ANF Σ ω^{b_l}` of `M` (there `Ω₁·r = Σ ϑ₁(b_l)`, so
  the subterms are the `b_l`, not the `ω^{b_l}`; e.g. `M = Ω₁ + τ·ω`).  Every member of `P₀(c)` is `≤ c` (step ★1 of
  `R2.CitedLu`: L, `α^* < ϑ₀(α)`, along the term of `c`), and `c ≤ max(rjDat M, η)` (`b_l ≤ r`).  For `M < Ω₁` this
  is step ◆* of `R2.CitedLv` (`rjDat M = M`).
* (□<) For an `ε`-number `a > τ` with `ξ^* < a`: each additive component of `η`, of a leaf of `M` inside a code
  `m_l`, and of an exponent `b_l` of the top remainder `r` is `< τ` or a member of `P₀(ξ)`, hence `< a`; since
  `a ∈ E` is closed under `ω^·`, also `r = Σ ω^{b_l} < a`; so every leaf and `η` are `< a`: **`rjDat M, η < a`**.
* (□ι) For `α := ϑᵗ(ξ)`, `Ω₁ ≤ M`: `Δ = Ω₁·M > 0`, so `τ < α ∈ E` (E); `ξ^* < α` (L), so `rjDat M, η < α` (□<) and
  `Δ ∈ Tᵗ_α` (D, `Δ^* ≤ ξ^* < α`).  Let `α` be strongly critical.  The codes over `α` (`Gg.GgCl α`: generated from
  `[0, α)` and `Ω₁` by `+` and `φ`) below `ε_{Ω₁+1}` are exactly the members of `Tᵗ_α` below `ε_{Ω₁+1}` (by □2 and the
  note after D, `Tᵗ_α ∩ Ω₁ = α`; the countable codes over a strongly critical `α` are `< α`).  On them `ι = ι_{τ,α}`
  is strictly increasing (Lemma 7.2 (b)), additive (7.2 (c)), the identity below `α` (I, first clause), `ι(Ω₁) =
  ι(ϑ₁(0)) = ϑ^α(0) = α` (note of I, Z at the base `α`), and `ι(ϑ₁(m)) = ϑ^α(ι(m)) = ω^{α + ι(m)}` (W at the base
  `α`, `Ω₀ = α`, as in □1); so `ι(ω^z) = ω^{ι(z)}` for codes `z ≥ Ω₁`, and `ι` maps these codes onto the closure of
  `α + 1` under `+` and `ω^·` below `ε_{α+1}`, which is `ε_{α+1}`.  A strictly increasing map of a set of ordinals onto
  an ordinal is the order type function of that set: **`ι_{τ,α}(Δ) = Θ_α(Ω₁·M)`** (`Gg.ggTh α (Om1 * M)`), and
  `ι_{τ,α}(Δ) < ε_{α+1}`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Googology.Trans.PoR.InaccPsi.R2.Rj

/-- **[W07a] Def 3.22, Lemma 4.2 (`m = 1`), the remark after Def 3.1, Theorem 3.23, Convention 4.1** (texts T, W, Z,
Θ, C): for a code `Ω₁ ≤ M < ε_{Ω₁+1}` with `rjDat M ∈ Tᵗ` and `η ∈ Tᵗ ∩ Ω₁`: `Ω₁·M + η ∈ Tᵗ`.

Our steps.  Step □2 of the module docstring: `Ω₁·M` is the `=NF`-sum of the `ϑ₁`-terms `ϑ₁(m_l)` built by T from
`Ω₁ = ϑ₁(0)` and the leaves of `M`, which are `≤ rjDat M ∈ Tᵗ ∩ Ω₁` and so in `Tᵗ` (Θ: an initial segment); then
`Ω₁·M + η ∈ Tᵗ` (T, second clause).  For `M = Ω₁·γ + β` this is `lqArg_mem` of `R2.CitedLq`. -/
axiom rjArg_mem {τ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Om1 ≤ M) (hME : M < Gg.ggE)
    (hMT : rjDat M ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    Om1 * M + η ∈ Tset τ

/-- **[W07a] Lemma 3.30, the direction `⇐`, with Def 3.28** (texts L, S): for codes `M' < ε_{Ω₁+1}` (`M' < Ω₁`
allowed) and `Ω₁ ≤ M < ε_{Ω₁+1}` with data in `Tᵗ`, `η', η ∈ Tᵗ ∩ Ω₁`, `ξ' := Ω₁·M' + η' < ξ := Ω₁·M + η` and
`rjDat M', η' < ϑᵗ(ξ)`: `ϑᵗ(ξ') < ϑᵗ(ξ)`.

Our steps.  `ξ', ξ ∈ Tᵗ ∩ Ω₂` (□2; for `M' < Ω₁` the step ◆β of `R2.CitedLv`).  By □*, `ξ'^* ≤ max(rjDat M', η') <
ϑ₀(ξ)`.  So `ξ' < ξ ∧ ξ'^* < ϑ₀(ξ)`, the first disjunct of the right side of L (`m = 0`), and `ϑ₀(ξ') < ϑ₀(ξ)`.
(`lqVt_lt` of `R2.CitedLq` is the case `M = Ω₁·γ + β`, `M' = Ω₁·γ' + β'`.) -/
axiom rjVt_lt {τ M' η' M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM'E : M' < Gg.ggE)
    (hM'T : rjDat M' ∈ Tset τ) (hη' : η' ∈ Tset τ) (hη'Ω : η' < Om1) (hM1 : Om1 ≤ M) (hME : M < Gg.ggE)
    (hMT : rjDat M ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1) (harg : Om1 * M' + η' < Om1 * M + η)
    (hd' : rjDat M' < vt τ (Om1 * M + η)) (hη'v : η' < vt τ (Om1 * M + η)) :
    vt τ (Om1 * M' + η') < vt τ (Om1 * M + η)

/-- **[W07a] Lemma 3.30, the direction `⇒`, with Def 3.28** (texts L, S): for `ξ ∈ Tᵗ ∩ Ω₂`, a code
`Ω₁ ≤ M < ε_{Ω₁+1}` with `rjDat M ∈ Tᵗ` and `η ∈ Tᵗ ∩ Ω₁` with `rjDat M, η < ϑᵗ(ξ)`: `ϑᵗ(ξ) < ϑᵗ(Ω₁·M + η)` implies
`ξ < Ω₁·M + η`.

Our steps.  `ζ := Ω₁·M + η ∈ Tᵗ ∩ Ω₂` (□2) and `ζ^* ≤ max(rjDat M, η) < ϑᵗ(ξ)` (□*).  L (`m = 0`, `α = ξ`): `ϑ₀(ξ)
< ϑ₀(ζ)` gives `ξ < ζ ∧ ξ^* < ϑ₀(ζ)` or `ϑ₀(ξ) ≤ ζ^*`; the second is impossible.  So `ξ < ζ`. -/
axiom rjLt_of_vt_lt {τ ξ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hξ : ξ ∈ Tset τ) (hξ2 : ξ < OmTwo)
    (hM1 : Om1 ≤ M) (hME : M < Gg.ggE) (hMT : rjDat M ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (hdξ : rjDat M < vt τ ξ) (hηξ : η < vt τ ξ) (h : vt τ ξ < vt τ (Om1 * M + η)) : ξ < Om1 * M + η

/-- **[W07a] Lemma 3.30 (`α^* < ϑ₀(α)`), Lemma 4.3, Def 3.28** (texts L, E, S): for a code `Ω₁ ≤ M < ε_{Ω₁+1}` with
`rjDat M ∈ Tᵗ` and `η ∈ Tᵗ ∩ Ω₁`: `rjDat M, η < ϑᵗ(Ω₁·M + η)`.

Our steps.  `ξ := Ω₁·M + η ∈ Tᵗ ∩ Ω₂` (□2).  L (`m = 0`): `ξ^* < ϑ₀(ξ) =: a`.  E (`Δ = Ω₁·M > 0`): `τ < a ∈ E`.
By □<, `rjDat M, η < a`. -/
axiom rjLevel_lt_vt {τ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Om1 ≤ M) (hME : M < Gg.ggE)
    (hMT : rjDat M ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    rjDat M < vt τ (Om1 * M + η) ∧ η < vt τ (Om1 * M + η)

/-- **[W07b] Def 4.1, the case `δ > α` with `cr(α, δ) = m`, with [W07a] Def 7.5, Def 7.1, Lemma 7.2 (b)–(d),
Def 6.1, Def 4.11, Def 4.6, Def 7.15, Convention 6.6, Convention 4.1, Lemma 6.3, Lemma 4.2, Lemma 4.3, Lemma 3.30,
Def 3.28, Def 3.22** (texts H, Λ, I, D, G, LOC, CR, TR, C, W, E, L, S, T): for a code `Ω₁ ≤ M < ε_{Ω₁+1}` with
`rjDat M ∈ Tᵗ`, `η ∈ Tᵗ ∩ Ω₁`, `α := ϑᵗ(Ω₁·M + η)` strongly critical, `λ₀ := Θ_α(Ω₁·M)` and `δ := ω^{log_ω λ₀}`:
**`lhᵗ(α) = lhᵗ(δ) + (−δ + (λ₀ + ζᵗ_α))`**, with `ζᵗ_α = lqZeta τ (Ω₁·M) η`.

Our steps.  `α = ϑᵗ(Δ + η)` with `Δ = Ω₁·M` (C), `α ∈ Tᵗ` (□2, T), `τ < α ∈ E`, `rjDat M, η < α`, `Δ ∈ Tᵗ_α` and
`ι_{τ,α}(Δ) = λ₀ < ε_{α+1}` (□ι); `ζᵗ_α = lqZeta τ Δ η` (G, read as in step ★ζ of `R2.CitedLu`), `ζᵗ_α ≤ η < α`; so
`λᵗ_α = λ₀ + ζᵗ_α` (Λ, `α ∈ E`).
* `δ = (λᵗ_α)^*` (H, the note): every component of `Δ` is `ϑ₁(m) = ω^{Ω₁+m}` (□1), with image `ω^{α+ι(m)}` (□ι), so
  `ω^α = α` divides `λ₀ ≠ 0`, and `ζᵗ_α < α`; the leading component of `λᵗ_α` is that of `λ₀`, and the maximum
  additive principal number `≤ λᵗ_α` is `δ = ω^{log_ω λ₀}`.  `M ≥ Ω₁` gives `λ₀ ≥ Θ_α(Ω₁·Ω₁) = α·α`, so `δ ≥ α·α > α`:
  the branch `δ > α` of H (consistent with "`δ ≤ α` i.e. `Δ < ϑ₁(1)`", as `Δ ≥ Ω₁·Ω₁ > ϑ₁(1) = Ω₁·ω`).  Also `δ ≤
  λᵗ_α < ε_{α+1}`, so `δ ∈ P ∖ E` (no `ε`-number in `(α, ε_{α+1})`).
* The `α`-localization of `δ` in `Tᵗ` (LOC, Convention 6.6): `α⁺ = ϑ^α(Δ) ≥ ϑ^α(Ω₁) = ε_{α+1} > δ` (TR; E and L at the
  base `α`), so `δ ∈ (α, α⁺)`.  In `T^α`, a term with value `< ε_{α+1} = ϑ^α(Ω₁)` has only `ϑ^α`-subterms `ϑ^α(ξ')`
  with `ξ' < Ω₁` (L at the base `α`: `ξ' ≥ Ω₁` gives `ϑ^α(ξ') ≥ ϑ^α(Ω₁)`), and then `ξ' < ϑ^α(ξ')` (W: `ϑ^α(1 + a) =
  ω̄_{α+a} > a`, `ϑ^α(0) = α`); by induction along the term every subterm is `≤` the term's value.  So every
  `ϑ^α(ξ') ∈ P^α(δ) − (α + 1)` other than `δ = ϑ^α(ξ_δ)` is a subterm of `ξ_δ`, `ξ' < ϑ^α(ξ') ≤ ξ_δ`: `δ` has the
  maximal argument, and the localization is `(α = δ₀, δ₁ = δ)`, `m = 1`; `δ^{t^α_τ} = δ` (TR, `δ ∈ T^α_{α⁺}` by D).
* `cr(α, δ)` (CR with `n = m = 1`): `{1, …, n − 1} = ∅`, so `cr(α, δ) = m`, and H gives `lhᵗ(α) = lhᵗ(δ) + ρ`,
  `ρ := −δ + λᵗ_α = −δ + (λ₀ + ζᵗ_α)`.
This is the computation of `lqLhT` of `R2.CitedLq` with `ι_{τ,α}(Δ) = Θ_α(Ω₁·M)` in place of `α·(α·γ + β)` (the two
agree at `M = Ω₁·γ + β`: `R2.RjFacts.rjLq_lh`).  The value `lhᵗ(δ)` is not part of this axiom (`δ ∈ P ∖ E`:
[W07b] Theorem 2.2 and Theorem 5.3 through `le1R_thm22`, `lh_eq_lhT`).  The hypothesis that `α` is strongly critical
is a theorem (`R2.RjFacts.rjK_SC`, from `rjVt_lt`); it is kept so that □ι applies verbatim. -/
axiom rjLhT {τ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Om1 ≤ M) (hME : M < Gg.ggE)
    (hMT : rjDat M ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (hSC : Googology.Notation.InaccPsi.SC (vt τ (Om1 * M + η))) :
    lhT τ (vt τ (Om1 * M + η)) =
      lhT τ (ω ^ log ω (Gg.ggTh (vt τ (Om1 * M + η)) (Om1 * M))) +
        ((Gg.ggTh (vt τ (Om1 * M + η)) (Om1 * M) + lqZeta τ (Om1 * M) η) -
          ω ^ log ω (Gg.ggTh (vt τ (Om1 * M + η)) (Om1 * M)))

end Googology.Trans.PoR.InaccPsi.R2
