import Googology.Trans.PoR.InaccPsi.R2.CitedRj
import Googology.Trans.PoR.InaccPsi.R2.UvTr

set_option autoImplicit false

/-!
# Wilken 2007 §6: the subcase `Γ^* < α` of Definition 6.2 at every level with data below `α`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

Formerly one axiom, now the theorem `urVt_tr2` (proved as `R2.Uv.uvVt_tr2` from the axiom `R2.uvVt_trL` of
`R2.CitedUv`, its case `Γ < ε_{Ω₁+1}`, where `Uc.ucDat Γ = Rj.rjDat Γ`).
It is the printed subcase "`Γ > 0` and `Γ^* < α`" of both translations of [W07a] Def 6.2, read with
Lemma 6.3, at every level `Γ = Ω₁·M` with `1 ≤ M`, `Γ < ε_{Ω₁+1}` and countable data `rjDat Γ < α` (`Rj.rjDat`: the
largest countable leaf of the hereditary Cantor normal form over `{0, Ω₁}`).  It is the exact twin of `R2.ukVt_tr3`
(data `≥ α`, the subcase `Γ^* ≥ α`): the two hypotheses `rjDat Γ < α` and `α ≤ rjDat Γ` split every level, and the
step ◇* (copied from `R2.ukVt_tr3`) shows that `rjDat Γ < α` is exactly the printed condition `Γ^* < α` over either
base.  It contains `R2.uhVt_tr` (data `rjDat M < τ`, so `rjDat Γ ≤ rjDat M < τ < α`), which becomes the theorem
`R2.Ur.urVt_tr_uh`; the new levels are the **gap levels**, data in `[τ, α)`, whose countable leaves are terms of
`Tᵗ` (not parameters) but parameters of `T^α`.  Net count of axioms: `+1` (`urVt_tr2`) `−1` (`uhVt_tr`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- **[W07a] Definition 6.2 (p. 148) and Lemma 6.3 (p. 149), the subcase "`Γ > 0` and `Γ^* < α`" of both
translations, at every level `Γ = Ω₁·M`, `1 ≤ M`, `Γ < ε_{Ω₁+1}`, with countable data `rjDat Γ < α`; with the remark
after Def 6.2 (p. 149), Convention 4.1 and Lemma 4.3 (p. 142), Lemma 4.5 (p. 143), Definition 6.1 (p. 148),
Definition 3.22 (p. 139), Theorem 3.23 (p. 139), the Remark after Corollary 3.24 (p. 140), Definition 3.28 (p. 141),
Lemma 3.30 (p. 142), Definition 3.4 (p. 132), Lemma 4.2 (p. 142), the remark after Definition 3.1.**  For
`τ ∈ E ∩ Ω₁`, `n ≥ 1`, `α := Dl τ n = ϑᵗ(Δₙ)`, `α⁺ := Dp τ n = ϑᵗ(Δₙ + 1)`, `1 ≤ M` with `Ω₁·M < ε_{Ω₁+1}` and
`rjDat (Ω₁·M) < α`, and `ρ < Ω₁`: (i) if `Ω₁·M + ρ ∈ T^α` and `ϑ^α(Ω₁·M + ρ) < α⁺` then `Ω₁·M + (α + ρ) ∈ Tᵗ` and
`ϑ^α(Ω₁·M + ρ) = ϑᵗ(Ω₁·M + (α + ρ))`; (ii) if `Ω₁·M + (α + ρ) ∈ Tᵗ` and `ϑᵗ(Ω₁·M + (α + ρ)) < α⁺` then
`Ω₁·M + ρ ∈ T^α` and `ϑᵗ(Ω₁·M + (α + ρ)) = ϑ^α(Ω₁·M + ρ)`.

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
  order to define `ϑᵗ(ξ)^{t^τ_α}`", evidently `ϑ^α(ξ) ≥ α`, `ϑ^α(ξ)^{t^α_τ}`.  The star of "`Γ^* < α`" is printed
  without a base; ◇* shows that over `τ` and over `α` it gives the same condition here.  The proof of Lemma 6.3
  (p. 149) also notes "`(Γ^{t^τ_α})^* ≥ α` iff `Γ^* ≥ α`".)
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
`Γ := Ω₁·M`; `β` ranges over the two bases `τ` and `α`.  `P` = the additive principal numbers, `E` = the
`ε`-numbers.

Our steps.
* (◇0) **`ϑ₁` below `ε_{Ω₁+1}`** (as in `R2.uhVt_tr`, `R2.ukVt_tr3`).  By W (`m = 1`) `ϑ₁(1 + a) = ω̄_{Ω₁+a}`; the
  members of `P ∖ E` in `[Ω₁, ε_{Ω₁+1})` are exactly the `ω^{Ω₁+1+a}` (no `ε`-number lies in `(Ω₁, ε_{Ω₁+1})`, and
  `P ∖ E` below `Ω₁` has order type `Ω₁`), so with Z (`ϑ₁(0) = Ω₁ = ω^{Ω₁}`): **`ϑ₁(e) = ω^{Ω₁+e}` for every
  `e < ε_{Ω₁+1}`**; these values do not depend on the base `β` (`Ω₀ = β` enters only `ϑ₀`).
* (◇L) **The leaves of `Γ`, and their maximum `rjDat Γ`** (the step ◇L of `R2.ukVt_tr3`, unchanged).  For `Ω₁ ≤ z <
  ε_{Ω₁+1}` write `z =CNF ω^{g₁}·k₁ + ⋯ + ω^{g_j}·k_j + r` with `g₁ > ⋯ > g_j ≥ Ω₁` and `r < Ω₁`; by ◇0 `ω^{g_i} =
  ϑ₁(e_i)`, `e_i := −Ω₁ + g_i`, so the term of `z` over `β` (unique by U; built by T, clauses two and three) is the
  `=NF`-sum of the `ϑ₁(e_i)` (`k_i` times each) and of the term of `r`.  Its **leaves** (maximal countable subterms)
  are `r` (if `r > 0`), `e_i` if `e_i < Ω₁`, and recursively the leaves of `e_i` if `e_i ≥ Ω₁`; by induction along
  the recursion defining `rjDat` their maximum (or `0`) is `rjDat z` (with `rjDat(Ω₁ + e) = e` for `0 < e < Ω₁`,
  `rjDat Ω₁ = 0`, `rjDat(Ω₁ + e) = rjDat e` for `e ≥ Ω₁`, the Lean theorem `Si.si_rjDat_Om1_add`).  For `Γ = Ω₁·M`
  all CNF exponents are `≥ Ω₁` and `r = 0`, so `max(Lf(Γ) ∪ {0}) = rjDat Γ`.
* (◇*) **`Γ^{*β} < α ⇔ rjDat Γ < α`**, for `β ∈ {τ, α}` (the step ◇* of `R2.ukVt_tr3`, read negatively).  By S,
  `P₀(Γ) = ⋃_{c ∈ Lf(Γ)} P₀(c)` (the sum and `ϑ₁`-nodes are `≥ Ω₁`).  For a leaf `c < α` every element of `P₀(c)` is
  `≤ c < α` (a parameter `c < β` has `Sub = {c}`; the subterms of a countable term are its components, `≤ c`, and
  the subterms of arguments `ξ` of `ϑ₀`-terms, whose `P₀`-parts are `≤ ξ^* < ϑ₀(ξ)` by L); a leaf `c ≥ α` has its
  first `=NF` component in `P₀(c)` and `≥ α`.  So `Γ^{*β} < α` iff every leaf is `< α` iff `rjDat Γ < α` (◇L).
  Over `α` every leaf is a parameter (`< α`), so even `Γ^{*α} = 0`; over `τ` a leaf `c ∈ [τ, α)` (a **gap leaf**) is
  a term of `Tᵗ ∩ Ω₁`, and `Γ^{*τ} ≤ rjDat Γ < α`.
* (◇M) **`Γ ∈ Tᵗ` and `Γ ∈ T^α` whenever its leaves are.**  `α ∈ Tᵗ ∩ Ω₁` (C, T), and `Tᵗ ∩ Ω₁` is an initial
  segment of `Ω₁` (Θ: `Tᵗ ∩ Ω₁ = θ₀`, the remark U for parameters `< τ`), so every leaf `c < α` is in `Tᵗ` and
  "the unique notation for `ξ` in `Tᵗ`" of the first clause of `t^α_τ` exists; over `α` each leaf `c < α` is a
  parameter (T, first clause, `Ω₀ = α`).  By ◇L and T (clauses two and three) `Γ ∈ Tᵗ` and `Γ ∈ T^α`, and by U
  this term is the unique term of `Γ` over either base.  `Γ > 0` is the multiple-of-`Ω₁` part of Convention C for
  every argument `Γ + ρ'` with `ρ' < Ω₁` (C: the decomposition is unique).
* (◇2) **`α`, `α⁺`, `ϑ^α(Δ)`** (as in `R2.uhVt_tr`).  `α = ϑᵗ(Δ) ∈ Tᵗ`, `Δ > 0`, so `τ < α ∈ E` (E); `α⁺ = ϑᵗ(Δ + 1)`
  (C); `α⁺ = ϑ^α(Δ)` (6.3, first item).  `Δ^{*β} = 0` (`Δ` has no `ϑ₀`-subterm; its only countable subterm is the
  parameter `0`).
* (◇3) **Part (i), `t^α_τ`.**  Let `ξ := Γ + ρ ∈ T^α`, `b := ϑ^α(ξ) < α⁺` (hypotheses).  `ξ < Ω₂` (`Γ < ε_{Ω₁+1} <
  Ω₂`), so `b ∈ T^α` (T).  `α < b`: E over the base `α` (`Γ > 0`, ◇M).  So `b ∈ (α, ϑ^α(Δ))` (◇2), the second case of
  `t^α_τ`.  The side conditions: `ξ^{*α} < b < ϑ^α(Δ)` (L), and L with `Δ^{*α} = 0` gives `ξ < Δ`, so `Γ ≤ ξ < Δ`.
  By ◇* (`β = α`) `Γ^{*α} < α` and `Γ > 0`: the second subcase, `b^{t^α_τ} := ϑᵗ(Γ^{t^α_τ} + α + ρ^{t^α_τ})`.
  `b ∈ T^α_{α⁺}`: `b ∈ P₀(b)` and every other element of `P₀(b)` lies in `P₀(ξ)` (S), so is `≤ ξ^{*α} < b`; hence
  `b^{*α} = b < α⁺` (6.1), and by 6.3 (third item) `b^{t^α_τ}` denotes `b`; by the remark after 6.2 it is a term of
  `Tᵗ`, so its argument `Γ^{t^α_τ} + α + ρ^{t^α_τ}` is a term of `Tᵗ` (T; `α ∈ Tᵗ`).  `Γ ∈ T^α_{α⁺}` (`P₀(Γ) ⊆
  P₀(ξ)`, S) and `ρ ∈ T^α_{α⁺}` (the countable part of `ξ`, its components are components of `ξ`), so by 6.3 (third
  item) `Γ^{t^α_τ}`, `ρ^{t^α_τ}` denote `Γ`, `ρ`.  So `b = ϑᵗ(Γ + α + ρ) = ϑᵗ(Ω₁·M + (α + ρ))` and `Ω₁·M + (α + ρ) ∈
  Tᵗ`.
* (◇4) **Part (ii), `t^τ_α`.**  Let `ξ' := Γ + (α + ρ) ∈ Tᵗ`, `b' := ϑᵗ(ξ') < α⁺` (hypotheses); `b' ∈ Tᵗ` as in ◇3.
  `α < b'`: by L (`m = 0` over `τ`, `α = ϑ₀(Δ)`, `γ = ξ'`) it suffices that `α ≤ ξ'^{*τ}` (second disjunct).  The
  countable part `α + ρ` of `ξ'` is `≥ α`; its first additive component `c` satisfies `c ≥ α` (`α ∈ P`), and `c` is a
  component of the `=NF`-sum `ξ'` (S; the components of `Γ` are `ϑ₁`-terms `≥ Ω₁ > c`), so `c ∈ P₀(ξ')` and
  `ξ'^{*τ} ≥ α`.  So `b' ∈ (α, α⁺)`, the second case of `t^τ_α`; `ξ' = Γ + ρ'` with `ρ' := α + ρ < Ω₁` is the
  decomposition of C (◇M), `Γ < Δ` (4.5), `α ≤ ξ'^{*τ} < b' < α⁺` (L).  By ◇* (`β = τ`) `Γ^{*τ} < α`, `Γ > 0`: the
  second subcase, `b'^{t^τ_α} := ϑ^α(Γ^{t^τ_α} + (−α + ρ')^{t^τ_α})`, and `−α + ρ' = ρ`.  As in ◇3 (over `τ`):
  `b'^{*τ} = b' < α⁺`, so by 6.3 (second item) `b'^{t^τ_α}` denotes `b'`, a term of `T^α` (remark).  `Γ ∈ Tᵗ_{α⁺}`
  (`Γ^{*τ} < α`, ◇*), so `Γ^{t^τ_α}` denotes `Γ` (6.3; its leaves `< α` become constants by the first clause).
  `ρ = −α + ρ'` lies in `Tᵗ_{α⁺}`: if `ρ ≥ α·ω` then `ρ' = ρ`; otherwise the components of `ρ` are the components of
  `ρ'` after the first one (`α`); in both cases they are components of `ξ'`, so `ρ ∈ Tᵗ` (T) and `ρ^{*τ} ≤ ξ'^{*τ} <
  α⁺`; by 6.3 `ρ^{t^τ_α}` denotes `ρ`.  So `b' = ϑ^α(Γ + ρ) = ϑ^α(Ω₁·M + ρ)`, and `Γ + ρ`, the argument of the term
  `b'^{t^τ_α}` of `T^α`, is in `T^α`.
* (Remark) At `n = 1`, `Δ₁ = Ω₁ ≤ Γ`, so `ϑ^β(Γ + ρ) ≥ ϑ^β(Δ)` (L) and both parts are vacuous; for `n ≥ 2` they are
  not, also at gap data: `M = τ` (`τ ∈ E`, so `Ω₁·τ = Ω₁·ω^τ = ϑ₁(τ)`, `rjDat(Ω₁·τ) = rjDat(Ω₁ + τ) = τ ∈ [τ, α)`,
  `ϑ^α(Ω₁·τ) < ϑ^α(Δ₂) = α⁺` by L as `Ω₁·τ < Δ₂` and `(Ω₁·τ)^{*α} = 0`). -/
theorem urVt_tr2 {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {n : ℕ} (hn : 1 ≤ n) {M ρ : Ordinal.{0}}
    (hM1 : 1 ≤ M) (hME : Om1 * M < Gg.ggE) (hMα : Rj.rjDat (Om1 * M) < Dl τ n) (hρ1 : ρ < Om1) :
    (Om1 * M + ρ ∈ Tset (Dl τ n) → vt (Dl τ n) (Om1 * M + ρ) < Dp τ n →
      Om1 * M + (Dl τ n + ρ) ∈ Tset τ ∧ vt (Dl τ n) (Om1 * M + ρ) = vt τ (Om1 * M + (Dl τ n + ρ))) ∧
    (Om1 * M + (Dl τ n + ρ) ∈ Tset τ → vt τ (Om1 * M + (Dl τ n + ρ)) < Dp τ n →
      Om1 * M + ρ ∈ Tset (Dl τ n) ∧ vt τ (Om1 * M + (Dl τ n + ρ)) = vt (Dl τ n) (Om1 * M + ρ)) :=
  Uv.uvVt_tr2 hτ hτ1 hn hM1 hME hMα hρ1

end Googology.Trans.PoR.InaccPsi.R2
