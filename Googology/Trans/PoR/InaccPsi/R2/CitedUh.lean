import Googology.Trans.PoR.InaccPsi.R2.CitedUe
import Googology.Trans.PoR.InaccPsi.R2.CitedRj

set_option autoImplicit false

/-!
# Wilken 2007 §6: the translations of Definition 6.2 at every level `Γ = Ω₁·M`, `1 ≤ M < ε_{Ω₁+1}`, data `< τ`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

One axiom, `uhVt_tr`: the statement of `R2.ueVt_tr` with the countable level `1 ≤ q < τ` replaced by a code
`1 ≤ M < ε_{Ω₁+1}` (`Gg.ggE`) whose countable data `Rj.rjDat M` (the largest countable leaf of the hereditary Cantor
normal form of `M` over `{0, Ω₁}`) is below `τ`.  For `M < Ω₁`, `rjDat M = M`, so `R2.ueVt_tr` is the special case
(`Uh.uhVt_tr_ue` in `R2.UhTerm`).  It is the same printed subcase ("`Γ > 0` and `Γ^* < α`") of both translations of
[W07a] Def 6.2, read with Lemma 6.3; only the step that computes the term of `Γ` (◇1 below) is longer.  It does not
follow from the earlier `Cited*` axioms: `R2.vt_wbar` is the case `Γ = 0`, `R2.ueVt_tr` has `Γ < Ω₁·Ω₁`, and the
Lemma 3.30 facts of `R2.CitedRj` / `R2.CitedTf` compare `ϑᵗ`-values over ONE base only.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- **[W07a] Definition 6.2 (p. 148) and Lemma 6.3 (p. 149), the subcase "`Γ > 0` and `Γ^* < α`" of both
translations, at every level `Γ = Ω₁·M` with `1 ≤ M < ε_{Ω₁+1}` and countable data `< τ`, with Convention 4.1 and
Lemma 4.3 (p. 142), Lemma 4.5 (p. 143), Definition 6.1 (p. 148), Definition 3.4 (p. 132), Definition 3.22 (p. 139),
Theorem 3.23 (p. 139), the Remark after Corollary 3.24 (p. 140), Definition 3.28 (p. 141), Lemma 3.30 (p. 142),
Lemma 4.2 (p. 142), the remark after Definition 3.1.**  For `τ ∈ E ∩ Ω₁`, `n ≥ 1`, `α := Dl τ n = ϑᵗ(Δₙ)`,
`α⁺ := Dp τ n = ϑᵗ(Δₙ + 1)`, a code `1 ≤ M < ε_{Ω₁+1}` with `rjDat M < τ` and `ρ < Ω₁`: (i) if `Ω₁·M + ρ ∈ T^α` and
`ϑ^α(Ω₁·M + ρ) < α⁺` then `ϑ^α(Ω₁·M + ρ) = ϑᵗ(Ω₁·M + (α + ρ))`; (ii) if `Ω₁·M + (α + ρ) ∈ Tᵗ` and
`ϑᵗ(Ω₁·M + (α + ρ)) < α⁺` then the same equation holds.

Literal texts (all of [W07a], checked against the paper; `Tᵗ_α`, `t^τ_α`, `t^α_τ` as printed there):
* (6.1) Def 6.1: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ`.  The restriction of `Tᵗ` to `α`, written as `Tᵗ_α`, is defined by
  `Tᵗ_α := {β ∈ Tᵗ | β^{*τ} < α}`."
* (6.2) Def 6.2: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ` where `Δ > 0`.  We define (partially correct) translations `t^τ_α` from
  `Tᵗ` to `T^α` and `t^α_τ` from `T^α` to `Tᵗ`.  `t^τ_α : Tᵗ → T^α` is defined as follows: • `ξ^{t^τ_α} := ξ` if
  `ξ < α` thus becoming a constant • `ξ^{t^τ_α} := ξ₁^{t^τ_α} + ξ₂^{t^τ_α}` if `ξ₁, ξ₂ ∈ Tᵗ` s.t. `ξ =NF ξ₁ + ξ₂ > α`
  • `ϑ_k(ξ)^{t^τ_α} := ϑ_k(ξ^{t^τ_α})` if `ξ ∈ Tᵗ ∩ Ω_{k+2}` and `k > 0` • If `ξ ∈ Tᵗ ∩ Ω₂` such that `ϑᵗ(ξ) ≥ α` in
  order to define `ϑᵗ(ξ)^{t^τ_α}` we distinguish between four cases: • `α^{t^τ_α} = ϑᵗ(Δ + η)^{t^τ_α} := ϑ^α(0)`
  • If `ϑᵗ(ξ) ∈ (α, α⁺)` we distinguish between three subcases.  `ξ` has a form `ξ = Γ + ρ` where `Γ < Δ` (cf. 4.5)
  and `α ≤ (Γ + ρ)^{*τ} < α⁺`.  • `ϑᵗ(ξ)^{t^τ_α} := ϑ^α(1 + (−α + ρ)^{t^τ_α})` if `Γ = 0` • `ϑᵗ(ξ)^{t^τ_α} :=
  ϑ^α(Γ^{t^τ_α} + (−α + ρ)^{t^τ_α})` if `Γ > 0` and `Γ^{*τ} < α` • `ϑᵗ(ξ)^{t^τ_α} := ϑ^α(Γ^{t^τ_α} + ρ^{t^τ_α})` if
  `Γ^{*τ} ≥ α` • `(α⁺)^{t^τ_α} = ϑᵗ(Δ + η + 1)^{t^τ_α} := ϑ^α(Δ)` • `ϑᵗ(ξ)^{t^τ_α} := 0` if `ϑᵗ(ξ) > α⁺`.
  `t^α_τ : T^α → Tᵗ` is defined as follows: • `ξ^{t^α_τ} := ξ` if `ξ < α` taking the unique notation for `ξ` in
  `Tᵗ` • `ξ^{t^α_τ} := ξ₁^{t^α_τ} + ξ₂^{t^α_τ}` if `ξ₁, ξ₂ ∈ T^α` s.t. `ξ =NF ξ₁ + ξ₂ > α` • `ϑ_k(ξ)^{t^α_τ} :=
  ϑ_k(ξ^{t^α_τ})` if `ξ ∈ T^α ∩ Ω_{k+2}` and `k > 0` • For `ξ ∈ T^α ∩ Ω₂` […] we distinguish between four cases:
  • `ϑ^α(0)^{t^α_τ} := ϑᵗ(Δ + η)` • If `ϑ^α(ξ) ∈ (α, ϑ^α(Δ))` (regarding `Δ` to be represented in `T^α`) we
  distinguish between three subcases: `ξ` has a form `ξ = Γ + ρ` where `Γ < Δ` and `(Γ + ρ)^{*α} < ϑ^α(Δ)`.
  • `ϑ^α(ξ)^{t^α_τ} := ϑᵗ(α + (−1 + ρ)^{t^α_τ})` if `Γ = 0` • `ϑ^α(ξ)^{t^α_τ} := ϑᵗ(Γ^{t^α_τ} + α + ρ^{t^α_τ})` if
  `Γ > 0` and `Γ^{*α} < α` • `ϑ^α(ξ)^{t^α_τ} := ϑᵗ(Γ^{t^α_τ} + ρ^{t^α_τ})` if `Γ^{*α} ≥ α` • `ϑ^α(Δ)^{t^α_τ} :=
  ϑᵗ(Δ + η + 1)` • `ϑ^α(ξ)^{t^α_τ} := 0` if `ϑ^α(ξ) > ϑ^α(Δ)`."  After it (p. 149): "Obviously in both definitions
  the respective case distinctions are disjoint and complete.  It is also easy to see that the assigned ordinals
  belong to the respective notation system."  (The bracket […] stands for the printed "such that `ϑᵗ(ξ) ≥ α` in
  order to define `ϑᵗ(ξ)^{t^τ_α}`", evidently `ϑ^α(ξ) ≥ α`, `ϑ^α(ξ)^{t^α_τ}`.)
* (6.3) Lemma 6.3: "We have • `α⁺ = ϑ^α(Δ)`, • the restriction of `t^τ_α` to `Tᵗ_{α⁺}` is the identity, and • the
  restriction of `t^α_τ` to `T^α_{α⁺}` is the identity."
* (C) Convention 4.1: "Given a term `α = ϑᵗ(ξ) ∈ Tᵗ` we introduce the notational convention that `α = ϑᵗ(Δ + η)`
  automatically means that `ξ = Δ + η` is a decomposition such that `Ω₁ | Δ` and `η < Ω₁`. […] In a situation where
  some `α = ϑᵗ(Δ + η)` is fixed, we will write `α⁺` to denote the ordinal `ϑᵗ(Δ + η + 1)`."  And: "Clearly, for the
  argument of a `ϑᵗ`-term in `Tᵗ`, to be a nonzero multiple of `Ω₁` means to be a sum of `ϑ₁`-terms."
* (E) Lemma 4.3: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ`.  Then `τ < α ∈ E ⇔ Δ > 0`."
* (4.5) Lemma 4.5: "If `α = ϑᵗ(Δ + η) ∈ Tᵗ` and `ϑᵗ(Γ + ρ) ∈ (α, α⁺)` then `Γ < Δ`."  Proof: "Using Lemma 3.30 we
  see that `ϑᵗ(Δ + η) < ϑᵗ(Γ + ρ) < ϑᵗ(Δ + η + 1)` can only hold if `Γ < Δ` and `α ≤ (Γ + ρ)^{*τ} < α⁺`."
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
`Γ := Ω₁·M`.  `P` = the additive principal numbers, `E` = the `ε`-numbers.  A countable **leaf** of `M` is a
countable remainder or a countable exponent met when `M` is written in Cantor normal form and every exponent and
remainder `≥ Ω₁` again (with `Ω₁ = ω^{Ω₁}` as an atom); `rjDat M` is the largest leaf (`rjDat M = M` for `M < Ω₁`).

Our steps.
* (◇0) **`ϑ₁` below `ε_{Ω₁+1}`.**  By W (`m = 1`, `a < Ω₂`) `ϑ₁(1 + a) = ω̄_{Ω₁+a}`.  The members of `P ∖ E` below
  `Ω₁` have order type `Ω₁` (`Ω₁ ∈ E`, and `E ∩ Ω₁` is a closed unbounded proper part of `P ∩ Ω₁` with complement of
  type `Ω₁`), and from `Ω₁` on the members of `P ∖ E` below `ε_{Ω₁+1}` are exactly the `ω^{Ω₁+1+a}` (no `ε`-number
  lies in `(Ω₁, ε_{Ω₁+1})`); so `ω̄_{Ω₁+a} = ω^{Ω₁+1+a}` for `Ω₁ + 1 + a < ε_{Ω₁+1}`, and with Z (`ϑ₁(0) = Ω₁ =
  ω^{Ω₁}`): **`ϑ₁(e) = ω^{Ω₁+e} = Ω₁·ω^e` for every `e < ε_{Ω₁+1}`**.
* (◇1) **The term of `Γ`, and `Γ^* = 0` over both bases.**  Write `M =CNF ω^{m₁}·k₁ + ⋯ + ω^{m_j}·k_j` (`j ≥ 1` as
  `M ≥ 1`, `0 < k_l < ω`); every `m_l ≤ M < ε_{Ω₁+1}`.  By ◇0, `Γ = Ω₁·M = ϑ₁(m₁)·k₁ + ⋯ + ϑ₁(m_j)·k_j`, a sum of
  `ϑ₁`-terms with non-increasing values in `P`.  Each exponent `m_l`, if `m_l ≥ Ω₁`, is again written `m_l =CNF
  Σ ω^{e}·k` with `ω^e = ϑ₁(−Ω₁ + e)` for `e ≥ Ω₁` (◇0, `e = Ω₁ + (−Ω₁ + e)`), the leaves of `−Ω₁ + e` being leaves
  of `e`; an exponent `m_l < Ω₁` (in particular all of them when `M < Ω₁`) and every countable remainder met on the
  way are leaves.  Recursively (the exponents strictly decrease: `log_ω z < z` for `Ω₁ < z < ε_{Ω₁+1}`), `Γ` is built
  by the clauses of T (third clause with `k = 1 ≥ 0` and arguments `< ε_{Ω₁+1} < Ω₂ < Ω₃`; second clause) from
  `ϑ₁(0) = Ω₁` and the leaves of `M`, each `≤ rjDat M < τ`; a countable ordinal `< τ` is a parameter of `Tᵗ` and,
  as `τ < α`, of `T^α` (T, first clause, `Ω₀ = τ` resp. `α`).  So `Γ ∈ Tᵗ` and `Γ ∈ T^α`, and by U this term is the
  unique term of `Γ` over either base.  By S its subterms are: sums and `ϑ₁`-terms, all `≥ Ω₁`, and the leaves,
  which are parameters `< τ ≤ α` with `Sub = {itself}` (S, first clause; a leaf `c < τ` is not split further, so
  also a countable remainder `r` of `M` with `Ω₁·r = Σ ϑ₁(b)` contributes only its exponents `b ≤ r < τ`).  None of
  them lies in `P ∩ [τ, Ω₁)` resp. `P ∩ [α, Ω₁)`, so `P₀(Γ) = ∅` over both bases and **`Γ^{*τ} = Γ^{*α} = 0 < α`**.
  In particular `Γ > 0` is the multiple-of-`Ω₁` part of Convention C for every argument `Γ + ρ'` with `ρ' < Ω₁` (C:
  the decomposition with `Ω₁ | Γ`, `ρ' < Ω₁` is unique), and `Γ < ε_{Ω₁+1}` (`Ω₁·M < ε_{Ω₁+1}` as `ε_{Ω₁+1} ∈ E` is
  closed under `·`).  Moreover `Γ^{t^α_τ}` and `Γ^{t^τ_α}` are the term `Γ` itself (first clauses: the leaves `< τ <
  α` stay constants; second clauses: the sums are `≥ Ω₁ > α`; third clauses: `ϑ₁` is kept), so they denote `Γ`.
* (◇2) **`α`, `α⁺`, and `ϑ^α(Δ)`.**  `α = ϑᵗ(Δ) ∈ Tᵗ` with `Δ > 0`, so by E `τ < α ∈ E`; `α⁺ = ϑᵗ(Δ + 1)` (C), and
  by Lemma 6.3 (first item) `α⁺ = ϑ^α(Δ)`.
* (◇3) **Part (i), the translation `t^α_τ`.**  Let `ξ := Γ + ρ ∈ T^α` (hypothesis) and `β := ϑ^α(ξ) < α⁺`
  (hypothesis).  `ξ < Ω₂` (`Γ < ε_{Ω₁+1} < Ω₂`, `ρ < Ω₁`, `Ω₂` additive principal), so `β ∈ T^α` (T).  `α < β`:
  E applied over the base `α` to `ϑ^α(Γ + ρ)` with `Γ > 0` (◇1) gives `α < β ∈ E`.  So `β ∈ (α, ϑ^α(Δ))` (◇2), the
  second case of `t^α_τ`.  `ξ = Γ + ρ` is the decomposition of C (◇1), and the printed side conditions hold: L
  (`m = 0`, over `α`) gives `ξ^{*α} < ϑ^α(ξ) = β < ϑ^α(Δ)`, and (`Γ < Δ`) by L, `β < ϑ^α(Δ)` with `ξ^{*α} < β`
  excludes `ϑ^α(ξ) ≤ Δ^{*α}` (`Δ^{*α} = 0`: `Δ` has no `ϑ₀`-subterm), so `ξ < Δ` and `Γ ≤ ξ < Δ`.  As `Γ > 0` and
  `Γ^{*α} = 0 < α` (◇1), the second subcase applies: `β^{t^α_τ} = ϑᵗ(Γ^{t^α_τ} + α + ρ^{t^α_τ})`.
  `β ∈ T^α_{α⁺}`: `β ∈ P₀(β)` (S, L: `β ∈ P ∩ [α, Ω₁)`) and every element of `P₀(β)` other than `β` lies in `P₀(ξ)`,
  so is `≤ ξ^{*α} < β`; hence `β^{*α} = β < α⁺` (6.1).  So by Lemma 6.3 (third item) `β^{t^α_τ}` denotes `β` (and is
  a term of `Tᵗ`, the remark after 6.2).  Likewise `ρ ∈ T^α_{α⁺}`: `ρ` is the countable part of `ξ`, its components
  are components of `ξ` (S, the `=NF`-sum `ξ`), so `ρ ∈ T^α` (T) and `ρ^{*α} ≤ ξ^{*α} < α⁺`; by Lemma 6.3 (third
  item) `ρ^{t^α_τ}` denotes `ρ`.  `Γ^{t^α_τ}` denotes `Γ` (◇1).  So `β = ϑᵗ(Γ + α + ρ) = ϑᵗ(Ω₁·M + (α + ρ))`.
* (◇4) **Part (ii), the translation `t^τ_α`.**  Let `ξ' := Γ + (α + ρ) ∈ Tᵗ` (hypothesis) and `β' := ϑᵗ(ξ') < α⁺`
  (hypothesis).  `ξ' < Ω₂` as in ◇3, so `β' ∈ Tᵗ` (T).  `α < β'`: by L (`m = 0` over `τ`, `α = ϑ₀(Δ)`,
  `γ = ξ'`) it suffices that `α ≤ ξ'^{*τ}` (second disjunct; then `α ≤ ξ'^{*τ} < ϑ₀(ξ') = β'`).  The countable part
  `α + ρ` of `ξ'` is `≥ α`; its first additive component `c` satisfies `c ≥ α` (`α ∈ P`), and `c` is a component of
  the `=NF`-sum `ξ'` (S; the components of `Γ` are `ϑ₁`-terms `≥ Ω₁ > c`), hence a subterm with `c ∈ P ∩ [τ, Ω₁)`
  (`c ≥ α > τ`), i.e. `c ∈ P₀(ξ')`, and `ξ'^{*τ} ≥ c ≥ α`.  So `β' ∈ (α, α⁺)`, the second case of `t^τ_α`:
  `ξ' = Γ + ρ'` with `ρ' := α + ρ < Ω₁` is the decomposition of C (◇1), `Γ > 0`, `Γ^{*τ} = 0 < α` (◇1), so the second
  subcase applies: `β'^{t^τ_α} = ϑ^α(Γ^{t^τ_α} + (−α + ρ')^{t^τ_α})`, and `−α + ρ' = ρ`.  `β' ∈ Tᵗ_{α⁺}`: as in ◇3
  (over `τ`), `β'^{*τ} = β' < α⁺` (6.1).  So by Lemma 6.3 (second item) `β'^{t^τ_α}` denotes `β'`.  `ρ = −α + ρ'`
  lies in `Tᵗ_{α⁺}`: if `ρ ≥ α·ω` then `ρ' = α + ρ = ρ`; otherwise the components of `ρ` are the components of `ρ'`
  after the first one (`α`); in both cases they are components of `ξ'`, so `ρ ∈ Tᵗ` (T) and `ρ^{*τ} ≤ ξ'^{*τ} < β' <
  α⁺`; by Lemma 6.3 (second item) `ρ^{t^τ_α}` denotes `ρ`.  `Γ^{t^τ_α}` denotes `Γ` (◇1).  So `β' = ϑ^α(Γ + ρ) =
  ϑ^α(Ω₁·M + ρ)`.
* (Remark) At `n = 1`, `Δ₁ = Ω₁ ≤ Γ`, so `ϑ^α(Γ + ρ) ≥ ϑ^α(Δ) = α⁺` (L) and both parts are vacuous; for `n ≥ 2`,
  `Δₙ ≥ ϑ₁(Ω₂) ≥ ε_{Ω₁+1} > Γ`. -/
axiom uhVt_tr {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {n : ℕ} (hn : 1 ≤ n) {M ρ : Ordinal.{0}}
    (hM1 : 1 ≤ M) (hME : M < Gg.ggE) (hMτ : Rj.rjDat M < τ) (hρ1 : ρ < Om1) :
    (Om1 * M + ρ ∈ Tset (Dl τ n) → vt (Dl τ n) (Om1 * M + ρ) < Dp τ n →
      vt (Dl τ n) (Om1 * M + ρ) = vt τ (Om1 * M + (Dl τ n + ρ))) ∧
    (Om1 * M + (Dl τ n + ρ) ∈ Tset τ → vt τ (Om1 * M + (Dl τ n + ρ)) < Dp τ n →
      vt τ (Om1 * M + (Dl τ n + ρ)) = vt (Dl τ n) (Om1 * M + ρ))

end Googology.Trans.PoR.InaccPsi.R2
