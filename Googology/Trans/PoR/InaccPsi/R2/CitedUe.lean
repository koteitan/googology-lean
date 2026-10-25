import Googology.Trans.PoR.InaccPsi.R2.Cited
import Googology.Trans.PoR.InaccPsi.R2.CitedW
import Googology.Trans.PoR.InaccPsi.R2.CitedUh

set_option autoImplicit false

/-!
# Wilken 2007 §6: the translations of Definition 6.2 at a constant level `Γ = Ω₁·q > 0`, and `π(α⁺)`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

One axiom, `ueDp_pi`, and one theorem, `ueVt_tr` (an axiom until `R2.CitedUh`; now the case `M = q < Ω₁` of
`R2.uhVt_tr`, since `Rj.rjDat q = q`).
* `ueVt_tr` (**[W07a] Definition 6.2 and Lemma 6.3, the subcase "`Γ > 0` and `Γ^* < α`" of both translations**):
  for `α = ϑᵗ(Δₙ) = Dl τ n` (`n ≥ 1`), `α⁺ = Dp τ n`, a countable level `1 ≤ q < τ` and `ρ < Ω₁`:
  `ϑ^α(Ω₁·q + ρ) = ϑᵗ(Ω₁·q + α + ρ)` whenever the left side lies in `T^α` below `α⁺` (translation `t^α_τ`), and the
  same equation whenever the right side lies in `Tᵗ` below `α⁺` (translation `t^τ_α`).
* `ueDp_pi` (**[W07a] Definition 5.1 and Definition 3.28 at `α⁺ = ϑᵗ(Δₙ + 1)`**): `α⁺ ∈ Tᵗ[σ]` and
  `π_{σ,τ}(ϑᵗ(Δₙ + 1)) = ϑ^σ(Δₙ + 1)`.

Neither follows from the `Cited*` axioms before `R2.CitedUh`: `R2.vt_wbar` describes `ϑᵗ` only at countable arguments
(the case `Γ = 0` of Definition 6.2, used in `Ub.ubTr`), and the constant `Dp` was so far described only by
`R2.Dp_spec` (membership, `Dp τ n = Dl (Dl τ n) n`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- **Theorem (the case `M = q < Ω₁` of `R2.uhVt_tr`).**  The text below is its source and argument as first cited.
**[W07a] Definition 6.2 (p. 148) and Lemma 6.3 (p. 149), the subcase "`Γ > 0` and `Γ^* < α`" of both
translations, with Convention 4.1 and Lemma 4.3 (p. 142), Lemma 4.5 (p. 143), Definition 6.1 (p. 148), Definition 3.22
(p. 139), the Remark after Corollary 3.24 (p. 140), Definition 3.28 (p. 141), Lemma 3.30 (p. 142), Lemma 4.2
(p. 142).**  For `τ ∈ E ∩ Ω₁`, `n ≥ 1`, `α := Dl τ n = ϑᵗ(Δₙ)`, `α⁺ := Dp τ n = ϑᵗ(Δₙ + 1)`, `1 ≤ q < τ` and
`ρ < Ω₁`: (i) if `Ω₁·q + ρ ∈ T^α` and `ϑ^α(Ω₁·q + ρ) < α⁺` then `ϑ^α(Ω₁·q + ρ) = ϑᵗ(Ω₁·q + (α + ρ))`; (ii) if
`Ω₁·q + (α + ρ) ∈ Tᵗ` and `ϑᵗ(Ω₁·q + (α + ρ)) < α⁺` then the same equation holds.

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
* (U) Remark after Corollary 3.24: "each `T_m` again gives rise to a notation system with parameters from `Ω_m` that
  provides a unique term for every ordinal which is element of some `Tⁿ_m` where `n > m`".
* (S) Def 3.28: "`Subᵗ_m(α) := {α}` for parameters `α < τ` • `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ) ∪ Subᵗ_m(η)` for `ξ, η ∈
  Tᵗ` s.t. `α =NF ξ + η > τ` • `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ)` if `k ≥ m`, `{α}` if `k < m`, for `α = ϑ_k(ξ)` where
  `ξ ∈ Tᵗ ∩ Ω_{k+2}`.  We define the additive principal parts of level `m` of `α ∈ Tᵗ` by `P_m(α) := Subᵗ_m(α) ∩ P ∩
  [Ω_m, Ω_{m+1})` and `α^{*m} := max(P_m(α) ∪ {0})`."  Convention 3.29: "instead of `*0` we will also write `*`."
* (L) Lemma 3.30: "For `m < ω` the function `ϑ_m ↾ Tᵗ ∩ Ω_{m+2}` is 1-1 and has values in `P ∩ [Ω_m, Ω_{m+1})`.  Let
  `α, γ ∈ Tᵗ ∩ Ω_{m+2}`.  Then `α^{*m} < ϑ_m(α)` and `ϑ_m(α) < ϑ_m(γ) ⇔ α < γ ∧ α^{*m} < ϑ_m(γ) ∨ ϑ_m(α) ≤ γ^{*m}`."
* (W) Lemma 4.2: "For any `m < ω` and any `α < Ω_{m+1}` we have `ϑ_m(1 + α) = ω̄_{Ω_m+α}`"; after Def 3.1: "Note that
  we have `ϑⁿ_m(0) = Ω_m` for `m < n`".

Notation.  `Δ := Δₙ = ϑ₁(⋯ϑₙ(0)⋯)` (`R2.Dl`: `Dl τ n = ϑᵗ(Δₙ)`, `R2.Dp`: `Dp τ n = ϑᵗ(Δₙ + 1)`, `η = 0` in C);
`Γ := Ω₁·q`.  `P` = the additive principal numbers.

Our steps.
* (◇1) **The term of `Γ`, and `Γ^* = 0` over both bases.**  Write `q =ANF ω^{e₁} + ⋯ + ω^{e_j}` (`j ≥ 1` as `q ≥ 1`),
  so every `eᵢ ≤ q < τ < α`.  By W and the remark after Def 3.1 (`m = 1`): `ϑ₁(0) = Ω₁` and `ϑ₁(1 + a) =
  ω̄_{Ω₁+a} = ω^{Ω₁+1+a}` for `a < Ω₁` (below `Ω₁ = ω^{Ω₁}` the additive principal non-`ε`-numbers have order type
  `Ω₁`, and there is no `ε`-number in `(Ω₁, Ω₁·ω)`), hence `ϑ₁(e) = Ω₁·ω^e` for every `e < Ω₁`.  So `Γ = Ω₁·q =
  ϑ₁(e₁) + ⋯ + ϑ₁(e_j)` with `ϑ₁(e₁) ≥ ⋯ ≥ ϑ₁(e_j)` in `P`; by T (`eᵢ < τ ≤ Ω₀` are parameters; third clause with
  `k = 1 ≥ 0`; second clause) `Γ ∈ Tᵗ` and `Γ ∈ T^α`, and by U this `=NF`-sum of `ϑ₁`-terms over parameters is the
  term of `Γ` over either base.  By S its subterms are `Γ`'s partial sums (`≥ Ω₁`), the `ϑ₁(eᵢ)` (`≥ Ω₁`) and the
  parameters `eᵢ` (`< τ ≤ α`); none lies in `P ∩ [τ, Ω₁)` resp. `P ∩ [α, Ω₁)`, so `P₀(Γ) = ∅` and `Γ^{*τ} = Γ^{*α} =
  0 < α`.  In particular `Γ > 0` is the multiple-of-`Ω₁` part of Convention C for every argument `Γ + ρ'` with
  `ρ' < Ω₁` (C: the decomposition with `Ω₁ | Γ`, `ρ' < Ω₁` is unique).  Moreover `Γ^{t^α_τ}` and `Γ^{t^τ_α}` are the
  term `Γ` itself (first clauses: parameters `< τ < α` stay constants; second clauses: the sums are `> α`; third
  clauses: `ϑ₁` is kept), so they denote `Γ`.
* (◇2) **`α`, `α⁺`, and `ϑ^α(Δ)`.**  `α = ϑᵗ(Δ) ∈ Tᵗ` with `Δ > 0`, so by E `τ < α ∈ E`; `α⁺ = ϑᵗ(Δ + 1)` (C), and
  by Lemma 6.3 (first item) `α⁺ = ϑ^α(Δ)`.
* (◇3) **Part (i), the translation `t^α_τ`.**  Let `ξ := Γ + ρ ∈ T^α` (hypothesis) and `β := ϑ^α(ξ) < α⁺`
  (hypothesis).  `ξ < Ω₂` (`Γ = Ω₁·q < Ω₁·Ω₁ < Ω₂`, `ρ < Ω₁`, `Ω₂` additive principal), so `β ∈ T^α` (T).  `α < β`:
  E applied over the base `α` to `ϑ^α(Γ + ρ)` with `Γ > 0` (◇1) gives `α < β ∈ E`.  So `β ∈ (α, ϑ^α(Δ))` (◇2), the
  second case of `t^α_τ`.  `ξ = Γ + ρ` is the decomposition of C (◇1), and the printed side conditions hold: L
  (`m = 0`, over `α`) gives `ξ^{*α} < ϑ^α(ξ) = β < ϑ^α(Δ)`, and (`Γ < Δ`) by L, `β < ϑ^α(Δ)` with `ξ^{*α} < β`
  excludes `ϑ^α(ξ) ≤ Δ^{*α}` (`Δ^{*α} = 0`: `Δ` has no `ϑ₀`-subterm), so `ξ < Δ` and `Γ ≤ ξ < Δ`.  As `Γ > 0` and
  `Γ^{*α} = 0 < α` (◇1), the second subcase applies: `β^{t^α_τ} = ϑᵗ(Γ^{t^α_τ} + α + ρ^{t^α_τ})`.
  `β ∈ T^α_{α⁺}`: `β ∈ P₀(β)` (S, L: `β ∈ P ∩ [α, Ω₁)`) and every element of `P₀(β)` other than `β` lies in `P₀(ξ)`,
  so is `≤ ξ^{*α} < β`; hence `β^{*α} = β < α⁺` (6.1).  So by Lemma 6.3 (third item) `β^{t^α_τ}` denotes `β` (and is
  a term of `Tᵗ`, the remark after 6.2).  Likewise `ρ ∈ T^α_{α⁺}`: `ρ` is the countable part of `ξ`, its components
  are components of `ξ` (S, the `=NF`-sum `ξ`), so `ρ ∈ T^α` (T) and `ρ^{*α} ≤ ξ^{*α} < α⁺`; by Lemma 6.3 (third
  item) `ρ^{t^α_τ}` denotes `ρ`.  `Γ^{t^α_τ}` denotes `Γ` (◇1).  So `β = ϑᵗ(Γ + α + ρ) = ϑᵗ(Ω₁·q + (α + ρ))`.
* (◇4) **Part (ii), the translation `t^τ_α`.**  Let `ξ' := Γ + (α + ρ) ∈ Tᵗ` (hypothesis) and `β' := ϑᵗ(ξ') < α⁺`
  (hypothesis).  `ξ' < Ω₂` as in ◇3, so `β' ∈ Tᵗ` (T).  `α < β'`: by L (`m = 0` over `τ`, `α = ϑ₀(Δ)`,
  `γ = ξ'`) it suffices that `α ≤ ξ'^{*τ}` (second disjunct; then `α ≤ ξ'^{*τ} < ϑ₀(ξ') = β'`).  The countable part
  `α + ρ` of `ξ'` is `≥ α`; its first additive component `c` satisfies `c ≥ α` (`α ∈ P`), and `c` is a component of
  the `=NF`-sum `ξ'` (S), hence a subterm with `c ∈ P ∩ [τ, Ω₁)` (`c ≥ α > τ`), i.e. `c ∈ P₀(ξ')`, and `ξ'^{*τ} ≥ c ≥
  α`.  So `β' ∈ (α, α⁺)`, the second case of `t^τ_α`: `ξ' = Γ + ρ'` with `ρ' := α + ρ < Ω₁` is the decomposition of C
  (◇1), `Γ > 0`, `Γ^{*τ} = 0 < α` (◇1), so the second subcase applies: `β'^{t^τ_α} = ϑ^α(Γ^{t^τ_α} +
  (−α + ρ')^{t^τ_α})`, and `−α + ρ' = ρ`.  `β' ∈ Tᵗ_{α⁺}`: as in ◇3 (over `τ`), `β'^{*τ} = β' < α⁺` (6.1).  So by
  Lemma 6.3 (second item) `β'^{t^τ_α}` denotes `β'`.  `ρ = −α + ρ'` lies in `Tᵗ_{α⁺}`: if `ρ ≥ α·ω` then
  `ρ' = α + ρ = ρ`; otherwise the components of `ρ` are the components of `ρ'` after the first one (`α`); in both
  cases they are components of `ξ'`, so `ρ ∈ Tᵗ` (T) and `ρ^{*τ} ≤ ξ'^{*τ} < β' < α⁺`; by Lemma 6.3 (second item)
  `ρ^{t^τ_α}` denotes `ρ`.  `Γ^{t^τ_α}` denotes `Γ` (◇1).  So `β' = ϑ^α(Γ + ρ) = ϑ^α(Ω₁·q + ρ)`. -/
theorem ueVt_tr {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {n : ℕ} (hn : 1 ≤ n) {q ρ : Ordinal.{0}}
    (hq1 : 1 ≤ q) (hqτ : q < τ) (hρ1 : ρ < Om1) :
    (Om1 * q + ρ ∈ Tset (Dl τ n) → vt (Dl τ n) (Om1 * q + ρ) < Dp τ n →
      vt (Dl τ n) (Om1 * q + ρ) = vt τ (Om1 * q + (Dl τ n + ρ))) ∧
    (Om1 * q + (Dl τ n + ρ) ∈ Tset τ → vt τ (Om1 * q + (Dl τ n + ρ)) < Dp τ n →
      vt τ (Om1 * q + (Dl τ n + ρ)) = vt (Dl τ n) (Om1 * q + ρ)) := by
  have hqO : q < Om1 := hqτ.trans hτ1
  exact uhVt_tr hτ hτ1 hn hq1 (hqO.trans Rj.rj_Om1_lt_E) (by rw [Rj.rjDat_small hqO]; exact hqτ) hρ1

/-- **[W07a] Definition 5.1 (p. 144), Definition 3.28 (p. 141), Definition 3.22 (p. 139), Convention 4.1 (p. 142).**
For bases `σ < τ` (countable `ε`-numbers) and `n ≥ 1`: `α⁺ = Dp τ n = ϑᵗ(Δₙ + 1) ∈ Tᵗ[σ]` and
`π_{σ,τ}(ϑᵗ(Δₙ + 1)) = ϑ^σ(Δₙ + 1) = Dp σ n`.

Literal texts ([W07a]):
* (P) Def 5.1: "Let `τ ∈ E` and `Tᵗ` be the notation system over `τ`.  Further, let `σ ∈ {1} ∪ (E ∩ τ)`.  We define
  `Tᵗ[σ] := {α ∈ Tᵗ | Parᵗ(α) ⊆ σ}` and `π_{σ,τ} : Tᵗ[σ] → T^σ` by the following clauses: • `π_{σ,τ}(ξ) := ξ` if
  `ξ < σ` • `π_{σ,τ}(ξ) := π_{σ,τ}(ξ₁) + π_{σ,τ}(ξ₂)` if `ξ =NF ξ₁ + ξ₂ > τ` • `π_{σ,τ}(ξ) := ϑ_k(π_{σ,τ}(η))` if
  `ξ = ϑ_k(η)` for some `k > 0` and `η ∈ Tᵗ[σ] ∩ Ω_{k+2}` • `π_{σ,τ}(ξ) := ϑ^σ(π_{σ,τ}(η))` if `ξ = ϑᵗ(η)` for some
  `η ∈ Tᵗ[σ] ∩ Ω₂`."
* (S) Def 3.28: "`Subᵗ_m(α) := {α}` for parameters `α < τ` • `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ) ∪ Subᵗ_m(η)` for `ξ, η ∈
  Tᵗ` s.t. `α =NF ξ + η > τ` • `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ)` if `k ≥ m`, `{α}` if `k < m`, for `α = ϑ_k(ξ)` where
  `ξ ∈ Tᵗ ∩ Ω_{k+2}`.  […] The set of parameters `< τ` used in the unique term denoting some `α ∈ Tᵗ` is denoted by
  `Parᵗ(α) := Subᵗ₀(α) ∩ τ`."
* (T) Def 3.22: "`Ω_m ⊆ T_m` • `ξ, η ∈ T_m ⇒ ξ + η ∈ T_m` • `ξ ∈ T_m ∩ Ω_{k+2} ⇒ ϑ_k(ξ) ∈ T_m` for `k ≥ m`."
* (C) Convention 4.1: "In a situation where some `α = ϑᵗ(Δ + η)` is fixed, we will write `α⁺` to denote the ordinal
  `ϑᵗ(Δ + η + 1)`."

Our steps.  `Δ := Δₙ = ϑ₁(ϑ₂(⋯ϑₙ(0)⋯))`, a term built by T from the parameter `0` and the functions `ϑ_k`, `k ≥ 1`,
with arguments below `Ω_{k+2}`; `Δ ≥ Ω₁ > τ`.  `Δ + 1` is an `=NF`-sum (`1 ∈ P`, `1 ≤ Δ`) `> τ` of the term `Δ` and
the parameter `1 < τ`, so `Δ + 1 ∈ Tᵗ ∩ Ω₂` and `α⁺ = ϑᵗ(Δ + 1) ∈ Tᵗ` (T).  By S (the third clause with `k ≥ 0` keeps
the subterms of the arguments, the second keeps both summands) `Subᵗ₀(α⁺) = {α⁺, Δ + 1, 1} ∪ Subᵗ₀(Δ)`, and
`Subᵗ₀(Δ)` consists of `ϑ_k`-terms (`≥ Ω₁`) and `0`; so `Parᵗ(α⁺) = Subᵗ₀(α⁺) ∩ τ = {0, 1} ⊆ σ` (`σ ∈ E`, so
`σ > 1`), i.e. `α⁺ ∈ Tᵗ[σ]` (P).  By P: fourth clause, `π(α⁺) = ϑ^σ(π(Δ + 1))`; second clause, `π(Δ + 1) = π(Δ) +
π(1)`; first clause, `π(1) = 1` and `π(0) = 0`; third clause (`k > 0`) down the term `Δ`, `π(Δ) = Δ`.  So
`π_{σ,τ}(α⁺) = ϑ^σ(Δ + 1)`, which is `Dp σ n` (C, over the base `σ`). -/
axiom ueDp_pi {σ τ : Ordinal.{0}} (h : Bases σ τ) {n : ℕ} (hn : 1 ≤ n) :
    Dp τ n ∈ TB τ σ ∧ pi σ τ (Dp τ n) = Dp σ n

end Googology.Trans.PoR.InaccPsi.R2
