import Googology.Trans.PoR.InaccPsi.R2.CitedRj
import Googology.Trans.PoR.InaccPsi.R2.UcDat

set_option autoImplicit false

/-!
# Wilken 2007 §6: both subcases `Γ > 0` of Definition 6.2 at every level `Γ = Ω₁·M < B₂` (data `ucDat Γ`)

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

Two axioms, a twin pair: `uvVt_trL` (the printed subcase "`Γ > 0` and `Γ^* < α`", data `ucDat Γ < α`, the translation
inserts `α`) and `uvVt_trH` (the printed subcase "`Γ^* ≥ α`", data `α ≤ ucDat Γ`, the translation keeps the argument),
both of [W07a] Def 6.2 read with Lemma 6.3, at every level `Γ = Ω₁·M` with `1 ≤ M` and `Γ < B₂ = Uc.ucB` (the bound
`ψ_{Ω₂}(ε_{Ω₂+1})` of `R2.CitedUc`).  The data is `Uc.ucDat` (the largest countable leaf of the canonical term of a code
below `B₂`, the data of `R2.CitedUc`), which equals `Rj.rjDat` below `ε_{Ω₁+1}` (the Lean theorem `R2.Uv.uvDat_eq_rj`).
So below `ε_{Ω₁+1}` the two axioms are literally `R2.urVt_tr2` and `R2.ukVt_tr3`, which become the theorems
`R2.Uv.uvVt_tr2` and `R2.Uv.uvVt_tr3`; the new levels are `ε_{Ω₁+1} ≤ Γ < B₂`.  Net count of axioms at the merge:
`+2 −2`.  The two hypotheses `ucDat Γ < α` and `α ≤ ucDat Γ` split every level (`R2.Uv.uvVt_trS`).

Literal texts (all of [W07a], re-checked against the paper, pp. 132, 139–143, 148–149; `Tᵗ_α`, `t^τ_α`, `t^α_τ` as
printed there):
* (6.1) Def 6.1: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ`.  The restriction of `Tᵗ` to `α`, written as `Tᵗ_α`, is defined by
  `Tᵗ_α := {β ∈ Tᵗ | β^{*τ} < α}`."
* (6.2) Def 6.2: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ` where `Δ > 0`.  We define (partially correct) translations `t^τ_α` from
  `Tᵗ` to `T^α` and `t^α_τ` from `T^α` to `Tᵗ`.  `t^τ_α : Tᵗ → T^α` is defined as follows: • `ξ^{t^τ_α} := ξ` if
  `ξ < α` thus becoming a constant • `ξ^{t^τ_α} := ξ₁^{t^τ_α} + ξ₂^{t^τ_α}` if `ξ₁, ξ₂ ∈ Tᵗ` s.t. `ξ =NF ξ₁ + ξ₂ > α`
  • `ϑ_k(ξ)^{t^τ_α} := ϑ_k(ξ^{t^τ_α})` if `ξ ∈ Tᵗ ∩ Ω_{k+2}` and `k > 0` • If `ξ ∈ Tᵗ ∩ Ω₂` such that `ϑᵗ(ξ) ≥ α` in
  order to define `ϑᵗ(ξ)^{t^τ_α}` we distinguish between four cases: • `α^{t^τ_α} = ϑᵗ(Δ + η)^{t^τ_α} := ϑ^α(0)`
  • If `ϑᵗ(ξ) ∈ (α, α⁺)` we distinguish between three subcases.  `ξ` has a form `ξ = Γ + ρ` where `Γ < Δ` (cf. 4.5)
  and `α ≤ (Γ + ρ)^{*τ} < α⁺`.  • `ϑᵗ(ξ)^{t^τ_α} := ϑ^α(1 + (−α + ρ)^{t^τ_α})` if `Γ = 0` • `ϑᵗ(ξ)^{t^τ_α} :=
  ϑ^α(Γ^{t^τ_α} + (−α + ρ)^{t^τ_α})` if `Γ > 0` and `Γ^* < α` • `ϑᵗ(ξ)^{t^τ_α} := ϑ^α(Γ^{t^τ_α} + ρ^{t^τ_α})` if
  `Γ^* ≥ α` • `(α⁺)^{t^τ_α} = ϑᵗ(Δ + η + 1)^{t^τ_α} := ϑ^α(Δ)` • `ϑᵗ(ξ)^{t^τ_α} := 0` if `ϑᵗ(ξ) > α⁺`.
  `t^α_τ : T^α → Tᵗ` is defined as follows: • `ξ^{t^α_τ} := ξ` if `ξ < α` taking the unique notation for `ξ` in
  `Tᵗ` • `ξ^{t^α_τ} := ξ₁^{t^α_τ} + ξ₂^{t^α_τ}` if `ξ₁, ξ₂ ∈ T^α` s.t. `ξ =NF ξ₁ + ξ₂ > α` • `ϑ_k(ξ)^{t^α_τ} :=
  ϑ_k(ξ^{t^α_τ})` if `ξ ∈ T^α ∩ Ω_{k+2}` and `k > 0` • For `ξ ∈ T^α ∩ Ω₂` […] we distinguish between four cases:
  • `ϑ^α(0)^{t^α_τ} := ϑᵗ(Δ + η)` • If `ϑ^α(ξ) ∈ (α, ϑ^α(Δ))` (regarding `Δ` to be represented in `T^α`) we
  distinguish between three subcases: `ξ` has a form `ξ = Γ + ρ` where `Γ < Δ` and `(Γ + ρ)^{*α} < ϑ^α(Δ)`.
  • `ϑ^α(ξ)^{t^α_τ} := ϑᵗ(α + (−1 + ρ)^{t^α_τ})` if `Γ = 0` • `ϑ^α(ξ)^{t^α_τ} := ϑᵗ(Γ^{t^α_τ} + α + ρ^{t^α_τ})` if
  `Γ > 0` and `Γ^* < α` • `ϑ^α(ξ)^{t^α_τ} := ϑᵗ(Γ^{t^α_τ} + ρ^{t^α_τ})` if `Γ^* ≥ α` • `ϑ^α(Δ)^{t^α_τ} :=
  ϑᵗ(Δ + η + 1)` • `ϑ^α(ξ)^{t^α_τ} := 0` if `ϑ^α(ξ) > ϑ^α(Δ)`."  After it (p. 149): "Obviously in both definitions
  the respective case distinctions are disjoint and complete.  It is also easy to see that the assigned ordinals
  belong to the respective notation system."  (The bracket […] stands for the printed "such that `ϑᵗ(ξ) ≥ α` in
  order to define `ϑᵗ(ξ)^{t^τ_α}`", evidently `ϑ^α(ξ) ≥ α`, `ϑ^α(ξ)^{t^α_τ}`.  The star of `Γ^*` is printed without
  a base; ◇* shows that over `τ` and over `α` it gives the same condition here.  The proof of Lemma 6.3 (p. 149) also
  notes "`(Γ^{t^τ_α})^* ≥ α` iff `Γ^* ≥ α`".)
* (6.3) Lemma 6.3: "We have • `α⁺ = ϑ^α(Δ)`, • the restriction of `t^τ_α` to `Tᵗ_{α⁺}` is the identity, and • the
  restriction of `t^α_τ` to `T^α_{α⁺}` is the identity."
* (C) Convention 4.1: "Given a term `α = ϑᵗ(ξ) ∈ Tᵗ` we introduce the notational convention that `α = ϑᵗ(Δ + η)`
  automatically means that `ξ = Δ + η` is a decomposition such that `Ω₁ | Δ` and `η < Ω₁`. […] In a situation where
  some `α = ϑᵗ(Δ + η)` is fixed, we will write `α⁺` to denote the ordinal `ϑᵗ(Δ + η + 1)`."  And: "Clearly, for the
  argument of a `ϑᵗ`-term in `Tᵗ`, to be a nonzero multiple of `Ω₁` means to be a sum of `ϑ₁`-terms."
* (E) Lemma 4.3: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ`.  Then `τ < α ∈ E ⇔ Δ > 0`."
* (4.5) Lemma 4.5: "If `α = ϑᵗ(Δ + η) ∈ Tᵗ` and `ϑᵗ(Γ + ρ) ∈ (α, α⁺)` then `Γ < Δ`."
* (T) Def 3.22: "`Ω_m ⊆ T_m` • `ξ, η ∈ T_m ⇒ ξ + η ∈ T_m` • `ξ ∈ T_m ∩ Ω_{k+2} ⇒ ϑ_k(ξ) ∈ T_m` for `k ≥ m`."
* (Θ) Theorem 3.23: "`T_m ∩ Ω_{m+1} = θ_m = sup_{n≥m} ϑ_m(⋯(ϑ_n(0))⋯)`."
* (U) Remark after Corollary 3.24: "each `T_m` again gives rise to a notation system with parameters from `Ω_m` that
  provides a unique term for every ordinal which is element of some `Tⁿ_m` where `n > m`".
* (Z) After Def 3.1: "Note that we have `ϑⁿ_m(0) = Ω_m` for `m < n`".
* (W) Def 3.4: "Let `α ↦ ω̄_α` be the enumeration function of the additive principle numbers which are not epsilon
  numbers."  Lemma 4.2: "For any `m < ω` and any `α < Ω_{m+1}` we have `ϑ_m(1 + α) = ω̄_{Ω_m+α}`".
* (S) Def 3.28: "`Subᵗ_m(α) := {α}` for parameters `α < τ` • `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ) ∪ Subᵗ_m(η)` for `ξ, η ∈
  Tᵗ` s.t. `α =NF ξ + η > τ` • `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ)` if `k ≥ m`, `{α}` if `k < m`, for `α = ϑ_k(ξ)` where
  `ξ ∈ Tᵗ ∩ Ω_{k+2}`.  We define the additive principal parts of level `m` of `α ∈ Tᵗ` by `P_m(α) := Subᵗ_m(α) ∩ P ∩
  [Ω_m, Ω_{m+1})` and `α^{*m} := max(P_m(α) ∪ {0})`."  Convention 3.29: "instead of `*0` we will also write `*`."
* (L) Lemma 3.30: "For `m < ω` the function `ϑ_m ↾ Tᵗ ∩ Ω_{m+2}` is 1-1 and has values in `P ∩ [Ω_m, Ω_{m+1})`.  Let
  `α, γ ∈ Tᵗ ∩ Ω_{m+2}`.  Then `α^{*m} < ϑ_m(α)` and `ϑ_m(α) < ϑ_m(γ) ⇔ α < γ ∧ α^{*m} < ϑ_m(γ) ∨ ϑ_m(α) ≤ γ^{*m}`."

Notation.  `Δ := Δₙ = ϑ₁(⋯ϑₙ(0)⋯)` (`R2.Dl`: `Dl τ n = ϑᵗ(Δₙ)`, `R2.Dp`: `Dp τ n = ϑᵗ(Δₙ + 1)`, `η = 0` in C);
`Γ := Ω₁·M`, `1 ≤ M`, `Γ < B₂`; `β` ranges over the two bases `τ` and `α`.  `P` = the additive principal numbers, `E`
= the `ε`-numbers.  A **countable part** of a term is a maximal countable subterm; a **leaf** of a code is as in
`R2.CitedUc` (`Uc.ucDat z` = the largest leaf, `0` if none).

Our steps (common to both axioms).
* (◇K) **The canonical term of `Γ` and its countable parts.**  `Γ` is a code below `B₂`.  Its term over `β` (unique by
  U) is the canonical term of `R2.CitedUc`: below `ε_{Ω₁+1}` the step ◇L of `R2.ukVt_tr3` (the `=NF`-sum of terms
  `ϑ₁(e)`, `ϑ₁(e) = ω^{Ω₁+e}` by Lemma 4.2), on `[ε_{Ω₁+1}, X)` the step ◇K′ of `R2.CitedTl`, on `[X, B₂)` the step
  ◇K″ of `R2.CitedUc` (`ϑ₁`-arguments `< ε_{Ω₂+1}·2 < Ω₃`, built by `+`, `ϑ₁`, `ϑ₂` and the countable parts).  These
  steps give: **every countable part of `Γ` is `≤` a leaf of `Γ`, and every leaf of `Γ` is finite, a countable part,
  `1 +` a countable part, or a countable `λ = Σ ω^{l_i}·k_i` of countable parts `l_i`** (the last one is the Veblen
  index of an atom `F_λ(y)` of ◇K′; ◇K, ◇K′, ◇K″ there; below `ε_{Ω₁+1}` the leaves are exactly the countable parts and
  `ucDat Γ = rjDat Γ`).  `Γ = Ω₁·M` with `M ≥ 1` has no countable additive component, so all its `=NF` components are
  additive principal `≥ Ω₁` and `< Ω₂`, i.e. `ϑ₁`-terms (L: `ϑ₀`-values are `< Ω₁`, `ϑ_k`-values for `k ≥ 2` are
  `≥ Ω₂`, parameters are `< τ`; this is the remark of C).
* (◇*) **`Γ^{*β} < α ⇔ ucDat Γ < α`**, for `β ∈ {τ, α}`.  By S, `Sub(Γ)` consists of the sum nodes, the `ϑ₁`- and
  `ϑ₂`-nodes of the canonical term (all `≥ Ω₁`, so not in `[β, Ω₁)`; the third clause with `k ≥ 1 ≥ 0 = m` keeps the
  argument's subterms, the second clause the components') and of the subterms of its countable parts; so `P₀(Γ) =
  ⋃_c P₀(c)` over the countable parts `c`.  For a countable part `c`: if `c < α`, every element of `P₀(c)` is `≤ c <
  α` (a parameter `c < β` has `Sub = {c}`; the subterms of a countable term are its components, `≤ c`, and the
  subterms of arguments `ξ` of `ϑ₀`-terms, whose `P₀`-parts are `≤ ξ^* < ϑ₀(ξ)` by L); if `c ≥ α`, its first `=NF`
  component `c₁` satisfies `c₁ ≥ α` (`α ∈ P`: a sum of components `< α` is `< α`), and `c₁ ∈ Sub(c) ∩ P ∩ [β, Ω₁)`
  (S), so `c^{*β} ≥ α`.  Hence `Γ^{*β} < α` iff every countable part is `< α`.  By ◇K and `ω ≤ α`, `α` a limit, this
  holds iff every leaf is `< α` (a leaf `≤ 1 + c` with `c < α` is `< α`; a leaf `Σ ω^{l_i}·k_i` with all `l_i < α`
  is `< α` since `α ∈ E` (◇2); a part `≤` a leaf), i.e. iff `ucDat Γ < α`.
  Over `α` every countable part `< α` is a parameter, so then `Γ^{*α} = 0`; over `τ` a part in `[τ, α)` is a term of
  `Tᵗ ∩ Ω₁` and `Γ^{*τ} < α`.  Negatively: `α ≤ ucDat Γ` iff `Γ^{*β} ≥ α` for both `β`.
* (◇M) **Membership of the leaves.**  `α ∈ Tᵗ ∩ Ω₁` (C, T) and `Tᵗ ∩ Ω₁` is an initial segment of `Ω₁` (Θ: `Tᵗ ∩
  Ω₁ = θ₀`, with U for the parameters `< τ`); so every countable `c < α` has "the unique notation for `ξ` in `Tᵗ`" of
  the first clause of `t^α_τ`, and is a parameter of `T^α` (T, first clause, `Ω₀ = α`).
* (◇2) **`α`, `α⁺`, `ϑ^α(Δ)`.**  `α = ϑᵗ(Δ) ∈ Tᵗ`, `Δ > 0`, so `τ < α ∈ E` (E); `α⁺ = ϑᵗ(Δ + 1)` (C); `α⁺ = ϑ^α(Δ)`
  (6.3, first item).  `Δ^{*β} = 0` (`Δ` has no `ϑ₀`-subterm; its only countable subterm is the parameter `0`).
* (◇ξ) **The case and the side conditions.**  `Γ < B₂ < Ω₂`, so every `ξ = Γ + ρ` with `ρ < Ω₁` is in `Ω₂` and its
  decomposition of C is `Γ + ρ` (`Ω₁ ∣ Γ`, unique).  For `ξ ∈ T^β` with `b := ϑ^β(ξ) < α⁺`: `b ∈ T^β` (T); `ξ^{*β} < b`
  (L); over `β = α`, L with `Δ^{*α} = 0` and `b < ϑ^α(Δ)` gives `ξ < Δ`; over `β = τ` Lemma 4.5 gives `Γ < Δ` once
  `α < b`.  `b ∈ T^β_{α⁺}`: `b ∈ P₀(b)` and every other element of `P₀(b)` lies in `P₀(ξ)` (S), so is `≤ ξ^{*β} < b`;
  hence `b^{*β} = b < α⁺` (6.1).  `Γ` (the sum of the uncountable components of `ξ`, in `T^β` by T) and `ρ` (the
  countable part, whose components are components of `ξ`) have `P₀ ⊆ P₀(ξ)` (S), so `Γ, ρ ∈ T^β_{α⁺}`. -/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- **[W07a] Definition 6.2 (p. 148) and Lemma 6.3 (p. 149), the subcase "`Γ > 0` and `Γ^* < α`" of both
translations, at every level `Γ = Ω₁·M`, `1 ≤ M`, `Γ < B₂`, with data `ucDat Γ < α`; with the remark after Def 6.2
(p. 149), Convention 4.1 and Lemma 4.3 (p. 142), Lemma 4.5 (p. 143), Definition 6.1 (p. 148), Definition 3.22,
Theorem 3.23 (p. 139), the Remark after Corollary 3.24 (p. 140), Definition 3.28 (p. 141), Lemma 3.30 (p. 142)**
(texts 6.1, 6.2, 6.3, C, E, 4.5, T, Θ, U, S, L of the module docstring).  For `τ ∈ E ∩ Ω₁`, `n ≥ 1`, `α := Dl τ n`,
`α⁺ := Dp τ n`, `1 ≤ M` with `Ω₁·M < B₂` and `ucDat (Ω₁·M) < α`, and `ρ < Ω₁`: (i) if `Ω₁·M + ρ ∈ T^α` and
`ϑ^α(Ω₁·M + ρ) < α⁺` then `Ω₁·M + (α + ρ) ∈ Tᵗ` and `ϑ^α(Ω₁·M + ρ) = ϑᵗ(Ω₁·M + (α + ρ))`; (ii) if `Ω₁·M + (α + ρ) ∈
Tᵗ` and `ϑᵗ(Ω₁·M + (α + ρ)) < α⁺` then `Ω₁·M + ρ ∈ T^α` and `ϑᵗ(Ω₁·M + (α + ρ)) = ϑ^α(Ω₁·M + ρ)`.

Our steps (with ◇K, ◇*, ◇M, ◇2, ◇ξ of the module docstring).
* (◇3) **Part (i), `t^α_τ`.**  Let `ξ := Γ + ρ ∈ T^α`, `b := ϑ^α(ξ) < α⁺`.  `α < b`: E over the base `α` (`Γ > 0`).  So
  `b ∈ (α, ϑ^α(Δ))` (◇2), the second case of `t^α_τ`, with `Γ ≤ ξ < Δ` and `ξ^{*α} < ϑ^α(Δ)` (◇ξ).  By ◇* (`β = α`)
  `Γ^{*α} < α`, and `Γ > 0`: the second subcase, `b^{t^α_τ} := ϑᵗ(Γ^{t^α_τ} + α + ρ^{t^α_τ})`.  `b ∈ T^α_{α⁺}` (◇ξ),
  so by 6.3 (third item) `b^{t^α_τ}` denotes `b`, and by the remark after 6.2 it is a term of `Tᵗ`, so its argument
  `Γ^{t^α_τ} + α + ρ^{t^α_τ}` is a term of `Tᵗ` (T; `α ∈ Tᵗ`).  `Γ, ρ ∈ T^α_{α⁺}` (◇ξ), so by 6.3 (third item)
  `Γ^{t^α_τ}`, `ρ^{t^α_τ}` denote `Γ`, `ρ` (the leaves `< α` of `Γ` get their notation in `Tᵗ` by ◇M).  So `b =
  ϑᵗ(Γ + α + ρ) = ϑᵗ(Ω₁·M + (α + ρ))` and `Ω₁·M + (α + ρ) ∈ Tᵗ`.
* (◇4) **Part (ii), `t^τ_α`.**  Let `ξ' := Γ + (α + ρ) ∈ Tᵗ`, `b' := ϑᵗ(ξ') < α⁺`; `b' ∈ Tᵗ` (◇ξ).  `α < b'`: by L
  (`m = 0`, `α = ϑ₀(Δ)`, `γ = ξ'`) it suffices that `α ≤ ξ'^{*τ}` (second disjunct): the first additive component `c`
  of the countable part `α + ρ ≥ α` of `ξ'` is `≥ α` (`α ∈ P`) and is a component of the `=NF`-sum `ξ'` (the
  components of `Γ` are `ϑ₁`-terms `≥ Ω₁ > c`, ◇K), so `c ∈ P₀(ξ')` (S) and `ξ'^{*τ} ≥ α`.  So `b' ∈ (α, α⁺)`, the
  second case of `t^τ_α`; `ξ' = Γ + ρ'` with `ρ' := α + ρ < Ω₁` is the decomposition of C, `Γ < Δ` (4.5), `α ≤
  ξ'^{*τ} < b' < α⁺` (L).  By ◇* (`β = τ`) `Γ^{*τ} < α`, `Γ > 0`: the second subcase, `b'^{t^τ_α} := ϑ^α(Γ^{t^τ_α} +
  (−α + ρ')^{t^τ_α})`, and `−α + ρ' = ρ`.  `b' ∈ Tᵗ_{α⁺}` (◇ξ), so by 6.3 (second item) `b'^{t^τ_α}` denotes `b'`, a
  term of `T^α` (remark).  `Γ ∈ Tᵗ_{α⁺}` (`Γ^{*τ} < α`), so `Γ^{t^τ_α}` denotes `Γ` (6.3; its countable parts `< α`
  become constants by the first clause).  `ρ = −α + ρ'`: if `ρ ≥ α·ω` then `ρ' = ρ`; otherwise the components of `ρ`
  are the components of `ρ'` after the first one (`α`); in both cases they are components of `ξ'`, so `ρ ∈ Tᵗ` (T)
  and `ρ^{*τ} ≤ ξ'^{*τ} < α⁺`; by 6.3 `ρ^{t^τ_α}` denotes `ρ`.  So `b' = ϑ^α(Γ + ρ) = ϑ^α(Ω₁·M + ρ)`, and `Γ + ρ`,
  the argument of the term `b'^{t^τ_α}` of `T^α`, is in `T^α`.
* (Remark) At `n = 1`, `Δ₁ = Ω₁ ≤ Γ`, so `ϑ^β(Γ + ρ) ≥ ϑ^β(Δ)` (L) and both parts are vacuous.  For `n ≥ 2` they are
  not (`R2.urVt_tr2`, the levels below `ε_{Ω₁+1}`); at the new levels, for `n ≥ 3`: `Γ = ε_{Ω₁+1} = ϑ₁(Ω₂)` (as in
  `R2.CitedSs`; `Ω₂ = ϑ₂(0)` by Z) has the single countable part `0`, `ucDat Γ` is finite, so `< α`; `Γ < Δ₃ =
  ϑ₁(ϑ₂(Ω₃))` (Z; L at `m = 1`: `Ω₂ < ϑ₂(Ω₃)`, `(ϑ₂(Ω₃))^{*1} = 0`), and `Γ^{*α} = 0`, so `ϑ^α(Γ) < ϑ^α(Δ₃) = α⁺`
  by L. -/
axiom uvVt_trL {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {n : ℕ} (hn : 1 ≤ n) {M ρ : Ordinal.{0}}
    (hM1 : 1 ≤ M) (hMB : Om1 * M < Uc.ucB) (hMα : Uc.ucDat (Om1 * M) < Dl τ n) (hρ1 : ρ < Om1) :
    (Om1 * M + ρ ∈ Tset (Dl τ n) → vt (Dl τ n) (Om1 * M + ρ) < Dp τ n →
      Om1 * M + (Dl τ n + ρ) ∈ Tset τ ∧ vt (Dl τ n) (Om1 * M + ρ) = vt τ (Om1 * M + (Dl τ n + ρ))) ∧
    (Om1 * M + (Dl τ n + ρ) ∈ Tset τ → vt τ (Om1 * M + (Dl τ n + ρ)) < Dp τ n →
      Om1 * M + ρ ∈ Tset (Dl τ n) ∧ vt τ (Om1 * M + (Dl τ n + ρ)) = vt (Dl τ n) (Om1 * M + ρ))

/-- **[W07a] Definition 6.2 (p. 148) and Lemma 6.3 (p. 149), the subcase "`Γ^* ≥ α`" of both translations, at every
level `Γ = Ω₁·M`, `1 ≤ M`, `Γ < B₂`, with data `α ≤ ucDat Γ`; with the remark after Def 6.2 (p. 149), Convention 4.1
and Lemma 4.3 (p. 142), Lemma 4.5 (p. 143), Definition 6.1 (p. 148), Definition 3.22, Theorem 3.23 (p. 139), the
Remark after Corollary 3.24 (p. 140), Definition 3.28 (p. 141), Lemma 3.30 (p. 142)** (texts 6.1, 6.2, 6.3, C, E,
4.5, T, Θ, U, S, L of the module docstring).  For `τ ∈ E ∩ Ω₁`, `n ≥ 1`, `α := Dl τ n`, `α⁺ := Dp τ n`, `1 ≤ M` with
`Ω₁·M < B₂` and `α ≤ ucDat (Ω₁·M)`, and `ρ < Ω₁`: (i) if `Ω₁·M + ρ ∈ T^α` and `ϑ^α(Ω₁·M + ρ) < α⁺` then `Ω₁·M + ρ ∈
Tᵗ` and `ϑ^α(Ω₁·M + ρ) = ϑᵗ(Ω₁·M + ρ)`; (ii) if `Ω₁·M + ρ ∈ Tᵗ` and `ϑᵗ(Ω₁·M + ρ) < α⁺` then `Ω₁·M + ρ ∈ T^α` and
`ϑᵗ(Ω₁·M + ρ) = ϑ^α(Ω₁·M + ρ)`.

Our steps (with ◇K, ◇*, ◇M, ◇2, ◇ξ of the module docstring).
* (◇3) **Part (i), `t^α_τ`.**  Let `ξ := Γ + ρ ∈ T^α`, `b := ϑ^α(ξ) < α⁺`.  `α < b`: E over the base `α` (`Γ > 0`).  So
  `b ∈ (α, ϑ^α(Δ))` (◇2), the second case of `t^α_τ`, with `Γ ≤ ξ < Δ` and `ξ^{*α} < ϑ^α(Δ)` (◇ξ).  By ◇* (`β = α`,
  negatively) `Γ^{*α} ≥ α`: the third subcase, `b^{t^α_τ} := ϑᵗ(Γ^{t^α_τ} + ρ^{t^α_τ})`.  `b ∈ T^α_{α⁺}` (◇ξ), so by
  6.3 (third item) `b^{t^α_τ}` denotes `b`; by the remark after 6.2 it is a term of `Tᵗ`, and so are the assigned
  `Γ^{t^α_τ}`, `ρ^{t^α_τ}`, so its argument is a term of `Tᵗ` (T, second clause).  `Γ, ρ ∈ T^α_{α⁺}` (◇ξ), so by 6.3
  `Γ^{t^α_τ}`, `ρ^{t^α_τ}` denote `Γ`, `ρ`.  So `b = ϑᵗ(Γ + ρ)` and `Γ + ρ ∈ Tᵗ`.
* (◇4) **Part (ii), `t^τ_α`.**  Let `ξ := Γ + ρ ∈ Tᵗ`, `b := ϑᵗ(ξ) < α⁺`; `b ∈ Tᵗ` (◇ξ).  `α < b`: by ◇* (`β = τ`,
  negatively) and `P₀(Γ) ⊆ P₀(ξ)`, `α ≤ Γ^{*τ} ≤ ξ^{*τ}`, so L (`m = 0`, second disjunct `ϑ₀(Δ) = α ≤ ξ^{*τ}`)
  gives `α < b`.  So `b ∈ (α, α⁺)`, the second case of `t^τ_α`; `ξ = Γ + ρ` is the decomposition of C, `Γ < Δ` (4.5),
  `α ≤ ξ^{*τ} < b < α⁺` (L).  By ◇* `Γ^{*τ} ≥ α`: the third subcase, `b^{t^τ_α} := ϑ^α(Γ^{t^τ_α} + ρ^{t^τ_α})`.
  `b ∈ Tᵗ_{α⁺}` (◇ξ), so by 6.3 (second item) `b^{t^τ_α}` denotes `b`, a term of `T^α` (remark); `Γ, ρ ∈ Tᵗ_{α⁺}`
  (◇ξ), so `Γ^{t^τ_α}`, `ρ^{t^τ_α}` denote `Γ`, `ρ` (6.3), terms of `T^α` by the same remark.  So `b = ϑ^α(Γ + ρ)`
  and `Γ + ρ ∈ T^α` (T, second clause).
* (Remark) At `n = 1` both parts are vacuous (as in `uvVt_trL`).  For `n ≥ 2` they are not (`R2.ukVt_tr3`, the levels
  below `ε_{Ω₁+1}`); at the new levels, for `n ≥ 3`: `Γ = ω^{ε_{Ω₁+1} + α} = ϑ₁(ε_{Ω₁+1} + α)` (◇K: Lemma 4.2 with the
  non-`ε` additive principal numbers above `ε_{Ω₁+1}`) has the countable part `α`, so `α ≤ ucDat Γ`; `Γ ∈ Tᵗ` (T),
  `Γ < Δ₃`, and `Γ^{*τ} = α < α⁺`, so `ϑᵗ(Γ) < ϑᵗ(Δ₃ + 1) = α⁺` by L (`Γ < Δ₃ + 1`). -/
axiom uvVt_trH {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {n : ℕ} (hn : 1 ≤ n) {M ρ : Ordinal.{0}}
    (hM1 : 1 ≤ M) (hMB : Om1 * M < Uc.ucB) (hMα : Dl τ n ≤ Uc.ucDat (Om1 * M)) (hρ1 : ρ < Om1) :
    (Om1 * M + ρ ∈ Tset (Dl τ n) → vt (Dl τ n) (Om1 * M + ρ) < Dp τ n →
      Om1 * M + ρ ∈ Tset τ ∧ vt (Dl τ n) (Om1 * M + ρ) = vt τ (Om1 * M + ρ)) ∧
    (Om1 * M + ρ ∈ Tset τ → vt τ (Om1 * M + ρ) < Dp τ n →
      Om1 * M + ρ ∈ Tset (Dl τ n) ∧ vt τ (Om1 * M + ρ) = vt (Dl τ n) (Om1 * M + ρ))

end Googology.Trans.PoR.InaccPsi.R2
