import Googology.Trans.PoR.InaccPsi.R2.CitedUh

set_option autoImplicit false

/-!
# Wilken 2007 §6: the third subcase of the translations of Definition 6.2 (`Γ^* ≥ α`)

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

One axiom, `ukVt_tr3`: the printed subcase "`Γ^* ≥ α`" of both translations of [W07a] Def 6.2, read with Lemma 6.3,
at every level `Γ = Ω₁·M` with `1 ≤ M`, `Γ < ε_{Ω₁+1}` and countable data `α ≤ rjDat Γ` (`Rj.rjDat`: the largest
countable leaf of the hereditary Cantor normal form over `{0, Ω₁}`).  There the translation keeps the argument:
`ϑ^α(Γ + ρ) = ϑᵗ(Γ + ρ)` (no `α` is inserted, unlike the subcase "`Γ^* < α`" of `R2.uhVt_tr`).  The step ◇* below shows
that `α ≤ rjDat Γ` is exactly the printed condition `Γ^* ≥ α`, over either base.  It does not follow from the earlier
`Cited*` axioms: `R2.vt_wbar` is the subcase `Γ = 0`, `R2.uhVt_tr` (and `R2.ueVt_tr`) the subcase `Γ^* < α`, and the
Lemma 3.30 facts of `R2.CitedRj` / `R2.CitedTf` / `R2.CitedUc` compare `ϑ`-values over ONE base only.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- **[W07a] Definition 6.2 (p. 148) and Lemma 6.3 (p. 149), the subcase "`Γ^* ≥ α`" of both translations, with the
remark after Def 6.2 (p. 149), Convention 4.1 and Lemma 4.3 (p. 142), Lemma 4.5 (p. 143), Definition 6.1 (p. 148),
Definition 3.22 (p. 139), Theorem 3.23 (p. 139), the Remark after Corollary 3.24 (p. 140), Definition 3.28 (p. 141),
Lemma 3.30 (p. 142), Lemma 4.2 (p. 142), the remark after Definition 3.1.**  For `τ ∈ E ∩ Ω₁`, `n ≥ 1`,
`α := Dl τ n = ϑᵗ(Δₙ)`, `α⁺ := Dp τ n = ϑᵗ(Δₙ + 1)`, `1 ≤ M` with `Ω₁·M < ε_{Ω₁+1}` and `α ≤ rjDat (Ω₁·M)`, and
`ρ < Ω₁`: (i) if `Ω₁·M + ρ ∈ T^α` and `ϑ^α(Ω₁·M + ρ) < α⁺` then `Ω₁·M + ρ ∈ Tᵗ` and `ϑ^α(Ω₁·M + ρ) = ϑᵗ(Ω₁·M + ρ)`;
(ii) if `Ω₁·M + ρ ∈ Tᵗ` and `ϑᵗ(Ω₁·M + ρ) < α⁺` then `Ω₁·M + ρ ∈ T^α` and `ϑᵗ(Ω₁·M + ρ) = ϑ^α(Ω₁·M + ρ)`.

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
  `Γ > 0` and `Γ^{*α} < α` • `ϑ^α(ξ)^{t^α_τ} := ϑᵗ(Γ^{t^α_τ} + ρ^{t^α_τ})` if `Γ^* ≥ α` • `ϑ^α(Δ)^{t^α_τ} :=
  ϑᵗ(Δ + η + 1)` • `ϑ^α(ξ)^{t^α_τ} := 0` if `ϑ^α(ξ) > ϑ^α(Δ)`."  After it (p. 149): "Obviously in both definitions
  the respective case distinctions are disjoint and complete.  It is also easy to see that the assigned ordinals
  belong to the respective notation system."  (The bracket […] stands for the printed "such that `ϑᵗ(ξ) ≥ α` in
  order to define `ϑᵗ(ξ)^{t^τ_α}`", evidently `ϑ^α(ξ) ≥ α`, `ϑ^α(ξ)^{t^α_τ}`.  The star of "`Γ^* ≥ α`" is printed
  without a base; ◇* shows that over `τ` and over `α` it gives the same condition here.)
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
* (◇0) **`ϑ₁` below `ε_{Ω₁+1}`** (as in `R2.uhVt_tr`).  By W (`m = 1`) `ϑ₁(1 + a) = ω̄_{Ω₁+a}`; the members of
  `P ∖ E` in `[Ω₁, ε_{Ω₁+1})` are exactly the `ω^{Ω₁+1+a}` (no `ε`-number lies in `(Ω₁, ε_{Ω₁+1})`, and `P ∖ E` below
  `Ω₁` has order type `Ω₁`), so with Z (`ϑ₁(0) = Ω₁ = ω^{Ω₁}`): **`ϑ₁(e) = ω^{Ω₁+e}` for every `e < ε_{Ω₁+1}`**; these
  values do not depend on the base `β` (`Ω₀ = β` enters only `ϑ₀`).
* (◇L) **The leaves of `Γ`, and their maximum `rjDat Γ`.**  For `Ω₁ ≤ z < ε_{Ω₁+1}` write `z =CNF ω^{g₁}·k₁ + ⋯ +
  ω^{g_j}·k_j + r` with `g₁ > ⋯ > g_j ≥ Ω₁` and `r < Ω₁`.  By ◇0 `ω^{g_i} = ϑ₁(e_i)`, `e_i := −Ω₁ + g_i`, so the
  term of `z` over `β` (unique by U; built by T, clauses two and three, as `ϑ₁` is applied below `Ω₃`) is the
  `=NF`-sum of the `ϑ₁(e_i)` (`k_i` times each) and of the term of `r`.  Its **leaves** (maximal countable subterms)
  are: `r` (if `r > 0`); `e_i` if `e_i < Ω₁` (an argument of `ϑ₁`); and, recursively, the leaves of `e_i` if
  `e_i ≥ Ω₁` (`e_i ≤ g_i ≤ z`, and `e_i < z` unless `z = ω^z`, impossible in `(Ω₁, ε_{Ω₁+1})`).  Let `Lf(z)` be this
  set, and `Lf(z) := {z}` for `z < Ω₁`.  Then **`max(Lf(z) ∪ {0}) = rjDat z`**, by induction along the recursion
  defining `rjDat` (`rjDat z = max(rjDat(log_ω z), rjDat(z mod ω^{log_ω z}))` for `Ω₁ < z`, `rjDat Ω₁ = 0`,
  `rjDat z = z` for `z < Ω₁`): `log_ω z = g₁ = Ω₁ + e₁` and `z mod ω^{g₁}` is the sum of the later parts; `Lf(z) =
  Lf'(e₁) ∪ Lf(z mod ω^{g₁})` with `Lf'(e) = {e}` for `e < Ω₁`, `Lf(e)` otherwise; and `rjDat(Ω₁ + e₁) = 0` for
  `e₁ = 0`, `= e₁` for `0 < e₁ < Ω₁` (the CNF of `Ω₁ + e₁` is `ω^{Ω₁} + e₁`), `= rjDat e₁` for `e₁ ≥ Ω₁` (the CNF of
  `Ω₁ + e₁` differs from that of `e₁` at most in the coefficient of `ω^{Ω₁}`; the Lean theorem
  `Si.si_rjDat_Om1_add`).  `z = Ω₁` is `ϑ₁(0)` with the leaf `0`.  For `Γ = Ω₁·M` (`M ≥ 1`) all CNF exponents are
  `≥ Ω₁` and `r = 0`, so the leaves of `Γ` are the leaves of the arguments `e_i`, and `max(Lf(Γ) ∪ {0}) = rjDat Γ`.
* (◇*) **`Γ^{*β} ≥ α ⇔ α ≤ rjDat Γ`**, for `β ∈ {τ, α}`.  By S, `Sub(Γ)` consists of the sum nodes and the
  `ϑ₁`-nodes of the term of `Γ` (all `≥ Ω₁`, so not in `[β, Ω₁)`) and of the subterms of its leaves (the third clause
  with `k = 1 ≥ 0` keeps the argument's subterms; the second clause the components'), so `P₀(Γ) = ⋃_{c ∈ Lf(Γ)}
  P₀(c)`.  For a leaf `c` over `β ≤ α`: if `c < α`, every element of `P₀(c)` is `≤ c < α` (a parameter `c < β` has
  `Sub = {c}`; the subterms of a countable term are its components, `≤ c`, and the subterms of arguments `ξ` of
  `ϑ₀`-terms, whose `P₀`-parts are `≤ ξ^* < ϑ₀(ξ)` by L); if `c ≥ α`, its first `=NF` component `c₁` satisfies
  `c₁ ≥ α` (`α ∈ P`: a sum of components `< α` is `< α`), `c₁ ∈ Sub(c) ∩ P ∩ [β, Ω₁)` (S), so `c^{*β} ≥ α`.  So
  `Γ^{*β} ≥ α` iff some leaf of `Γ` is `≥ α` iff `α ≤ rjDat Γ` (◇L).  (In particular the printed `Γ^*` of the third
  subcase is `≥ α` under our hypothesis whether it is read over `τ` or over `α`.)
* (◇2) **`α`, `α⁺`, `ϑ^α(Δ)`** (as in `R2.uhVt_tr`).  `α = ϑᵗ(Δ) ∈ Tᵗ`, `Δ > 0`, so `τ < α ∈ E` (E); `α⁺ = ϑᵗ(Δ + 1)`
  (C); `α⁺ = ϑ^α(Δ)` (6.3, first item).  `Δ^{*β} = 0` (`Δ` has no `ϑ₀`-subterm; its only countable subterm is the
  parameter `0`).
* (◇3) **Part (i), `t^α_τ`.**  Let `ξ := Γ + ρ ∈ T^α`, `b := ϑ^α(ξ) < α⁺` (hypotheses).  `ξ < Ω₂` (`Γ < ε_{Ω₁+1} <
  Ω₂`), so `b ∈ T^α` (T).  `α < b`: E over the base `α` (`Γ > 0` is the multiple-of-`Ω₁` part of `ξ` by C).  So
  `b ∈ (α, ϑ^α(Δ))` (◇2), the second case of `t^α_τ`.  The side conditions: `ξ^{*α} < b < ϑ^α(Δ)` (L), and L with
  `Δ^{*α} = 0` gives `ξ < Δ`, so `Γ ≤ ξ < Δ`.  By ◇* (`β = α`) `Γ^{*α} ≥ α`: the third subcase, `b^{t^α_τ} :=
  ϑᵗ(Γ^{t^α_τ} + ρ^{t^α_τ})`.  `b ∈ T^α_{α⁺}`: `b ∈ P₀(b)` and every other element of `P₀(b)` lies in `P₀(ξ)` (S), so
  is `≤ ξ^{*α} < b`; hence `b^{*α} = b < α⁺` (6.1), and by 6.3 (third item) `b^{t^α_τ}` denotes `b`; by the remark
  after 6.2 it is a term of `Tᵗ`, so its argument `Γ^{t^α_τ} + ρ^{t^α_τ}` is a term of `Tᵗ` (T: the subterms of a term
  are terms).  `Γ ∈ T^α_{α⁺}`: `Γ` is the sum of the uncountable components of `ξ` (C), in `T^α` (T, second clause),
  and `P₀(Γ) ⊆ P₀(ξ)` (S), so `Γ^{*α} ≤ ξ^{*α} < α⁺`; by 6.3 `Γ^{t^α_τ}` denotes `Γ`.  Likewise `ρ` (the countable
  part of `ξ`, its components are components of `ξ`): `ρ^{t^α_τ}` denotes `ρ`.  So `b = ϑᵗ(Γ + ρ)` and `Γ + ρ ∈ Tᵗ`.
* (◇4) **Part (ii), `t^τ_α`.**  Let `ξ := Γ + ρ ∈ Tᵗ`, `b := ϑᵗ(ξ) < α⁺` (hypotheses); `b ∈ Tᵗ` as in ◇3.  `α < b`:
  by ◇* (`β = τ`) and `P₀(Γ) ⊆ P₀(ξ)`, `α ≤ Γ^{*τ} ≤ ξ^{*τ}`, so L (`m = 0`, second disjunct `ϑ₀(Δ) = α ≤ ξ^{*τ}`)
  gives `α < b`.  So `b ∈ (α, α⁺)`, the second case of `t^τ_α`; `ξ = Γ + ρ` is the decomposition of C, `Γ < Δ` (4.5),
  `α ≤ ξ^{*τ} < b < α⁺` (L).  By ◇* (`β = τ`) `Γ^{*τ} ≥ α`: the third subcase, `b^{t^τ_α} := ϑ^α(Γ^{t^τ_α} +
  ρ^{t^τ_α})`.  As in ◇3 (over `τ`): `b^{*τ} = b < α⁺`, so `b ∈ Tᵗ_{α⁺}` and by 6.3 (second item) `b^{t^τ_α}` denotes
  `b`, a term of `T^α` (remark); `Γ, ρ ∈ Tᵗ_{α⁺}` (`Γ^{*τ}, ρ^{*τ} ≤ ξ^{*τ} < α⁺`), so `Γ^{t^τ_α}`, `ρ^{t^τ_α}` denote
  `Γ`, `ρ` (6.3).  So `b = ϑ^α(Γ + ρ)` and `Γ + ρ ∈ T^α`.
* (Remark) At `n = 1`, `Δ₁ = Ω₁ ≤ Γ`, so `ϑ^β(Γ + ρ) ≥ ϑ^β(Δ)` (L) and both parts are vacuous; for `n ≥ 2` they are
  not (e.g. `M = α` countable: `rjDat(Ω₁·α) = rjDat(Ω₁ + α) = α`, `Ω₁·α = ϑ₁(α) ∈ Tᵗ`, `ϑᵗ(Ω₁·α) < α⁺` by L as
  `Ω₁·α < Δ₂` and `(Ω₁·α)^{*τ} = α < α⁺`). -/
axiom ukVt_tr3 {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {n : ℕ} (hn : 1 ≤ n) {M ρ : Ordinal.{0}}
    (hM1 : 1 ≤ M) (hME : Om1 * M < Gg.ggE) (hMα : Dl τ n ≤ Rj.rjDat (Om1 * M)) (hρ1 : ρ < Om1) :
    (Om1 * M + ρ ∈ Tset (Dl τ n) → vt (Dl τ n) (Om1 * M + ρ) < Dp τ n →
      Om1 * M + ρ ∈ Tset τ ∧ vt (Dl τ n) (Om1 * M + ρ) = vt τ (Om1 * M + ρ)) ∧
    (Om1 * M + ρ ∈ Tset τ → vt τ (Om1 * M + ρ) < Dp τ n →
      Om1 * M + ρ ∈ Tset (Dl τ n) ∧ vt τ (Om1 * M + ρ) = vt (Dl τ n) (Om1 * M + ρ))

end Googology.Trans.PoR.InaccPsi.R2
