import Googology.Trans.PoR.InaccPsi.R2.CitedRk

set_option autoImplicit false

/-!
# Cited facts of Wilken 2007, as axioms, ONCE for the level `Δ = ε_{Ω₁+1} = ϑ₁(Ω₂)`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

Same conventions as `R2.CitedRj` and `R2.CitedRk` (`Ω₁ = Om1`, `Ω₂ = OmTwo`, `Tset τ = Tᵗ`, `Par τ = Parᵗ`,
`vt τ = ϑᵗ = ϑ₀`, `pi σ τ = π_{σ,τ}`, every base `τ` a countable `ε`-number; `ε_{Ω₁+1} = Gg.ggE` the least
`ε`-number above `Ω₁`; a **code** is an `M < ε_{Ω₁+1}`, `rjDat M` the largest countable leaf of its hereditary Cantor
normal form over `{0, Ω₁}`, with the junk value `rjDat ε_{Ω₁+1} = 0`).  The arguments `Ω₁·M + η` of `R2.CitedRj` stop
below `ε_{Ω₁+1}`; here the next argument `ε_{Ω₁+1} + η = Ω₁·ε_{Ω₁+1} + η` (`η < Ω₁`) is cited, the first level
with `Δ = ε_{Ω₁+1}` (Convention 4.1).

What is **not** restated (checked first, every `Cited*` file of `R2`): `vt_memTwo`, `vt_rep`, `vt_E_iff`,
`pi_vt_two` (`R2.CitedEv`), `vt_mem`, `pi_vt`, `vt_wbar` (`R2.CitedW`), `vzT_add`, `pi_add`, `pi_bijOn`,
`om1_opow_TB_all` (`R2.Cited`), `vzRem_T` (`R2.CitedVz`), `rjArg_mem`, `rjVt_lt`, `rjLt_of_vt_lt`, `rjLevel_lt_vt`
(`R2.CitedRj`, all for `M < ε_{Ω₁+1}` only), `rkArg_dat` (`R2.CitedRk`), the axioms of `R2.CitedLq`, `R2.CitedLg`,
`R2.CitedLv`, `R2.CitedLu`, `R2.CitedLz`, `R2.CitedLt`, `R2.CitedXt`, `R2.CitedEps`, `R2.CitedL`, `R2.CitedR1`.
None of them mentions the term `ϑ₁(Ω₂)`, the ordinal `ε_{Ω₁+1}` in `Tᵗ`, or an argument `≥ ε_{Ω₁+1}`.

Literal texts (all of [W07a]; checked against the paper):
* (D) Def 3.1: "Let `n ∈ (0, ω)`.  Descending from `m = n − 1` down to `m = 0` we define sets of ordinals
  `Cⁿ_m(α, β)` where `β < Ω_{m+1}` and ordinals `ϑⁿ_m(α)` by simultaneous recursion on `α < Ω_{m+2}`.  For each
  `β < Ω_{m+1}` the set `Cⁿ_m(α, β)` is defined inductively by • `Ω_m ∪ β ⊆ Cⁿ_m(α, β)` • `ξ, η ∈ Cⁿ_m(α, β) ⇒ ξ + η ∈
  Cⁿ_m(α, β)` • `ξ ∈ Cⁿ_m(α, β) ∩ Ω_{k+2} ⇒ ϑⁿ_k(ξ) ∈ Cⁿ_m(α, β)` for `m < k < n` • `ξ ∈ Cⁿ_m(α, β) ∩ α ⇒ ϑⁿ_m(ξ) ∈
  Cⁿ_m(α, β)`.  Having defined `ϑⁿ_m(ξ)` for all `ξ < α` and `Cⁿ_m(α, β)` for every `β < Ω_{m+1}` we set `ϑⁿ_m(α) :=
  min({ξ < Ω_{m+1} | Cⁿ_m(α, ξ) ∩ Ω_{m+1} ⊆ ξ ∧ α ∈ Cⁿ_m(α, ξ)} ∪ {Ω_{m+1}})`.  Note that we have `ϑⁿ_m(0) = Ω_m` for
  `m < n`."
* (B) Lemma 3.3: "Let `α < Ω_{m+2}` and `β < Ω_{m+1}`. … (b) `ϑⁿ_m(α) ∈ P ∩ [Ω_m, Ω_{m+1}]`."
* (W) Lemma 3.5: "Let `m < n`.  For every `α < Ω_{m+1}` we have `ϑⁿ_m(1 + α) = ω̄_{Ω_m+α}`."  Def 3.4: "Let `α ↦
  ω̄_α` be the enumeration function of the additive principle numbers which are not epsilon numbers."
* (EX) Corollary 3.21: "Let `m < n`.  `Tⁿ_m ⊆ Tⁿ⁺¹_m` and for `k` such that `m ≤ k < n` the functions `ϑⁿ_k` and
  `ϑⁿ⁺¹_k` agree on `Tⁿ_m ∩ Ω_{k+2}`."
* (T) Def 3.22: "For `m < ω` we set `θ_m := sup_{n>m} θⁿ_m`.  We define a function `ϑ_m : θ_{m+1} → Ω_{m+1}` by
  `ϑ_m(α) := ϑⁿ_m(α)` for `α < θⁿ_{m+1}` where `n > m` is large enough to satisfy `α < θⁿ_{m+1}`.  `T_m` is defined
  inductively as follows: • `Ω_m ⊆ T_m` • `ξ, η ∈ T_m ⇒ ξ + η ∈ T_m` • `ξ ∈ T_m ∩ Ω_{k+2} ⇒ ϑ_k(ξ) ∈ T_m` for
  `k ≥ m`."
* (Θ) Corollary 3.24: "For every `k ≥ m` we have `sup(T_m ∩ Ω_{k+2}) = θ_{k+1}`.  For `m < n` we have `Tⁿ_m ∩ Ω_{m+1}
  = θⁿ_m = ϑ_m(⋯(ϑ_n(0))⋯)`."
* (S) Def 3.28: "`Subᵗ_m(α) := {α}` for parameters `α < τ`; `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ) ∪ Subᵗ_m(η)` for `ξ, η ∈
  Tᵗ` s.t. `α =NF ξ + η > τ`; `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ)` if `k ≥ m`, `{α}` if `k < m`, for `α = ϑ_k(ξ)` where
  `ξ ∈ Tᵗ ∩ Ω_{k+2}`.  We define the additive principal parts of level `m` of `α ∈ Tᵗ` by `P_m(α) := Subᵗ_m(α) ∩ P ∩
  [Ω_m, Ω_{m+1})` and `α^{*m} := max(P_m(α) ∪ {0})`.  The set of parameters `< τ` used in the unique term denoting
  some `α ∈ Tᵗ` is denoted by `Parᵗ(α) := Subᵗ₀(α) ∩ τ`."
* (L) Lemma 3.30: "For `m < ω` the function `ϑ_m ↾ Tᵗ ∩ Ω_{m+2}` is 1-1 and has values in `P ∩ [Ω_m, Ω_{m+1})`.
  Let `α, γ ∈ Tᵗ ∩ Ω_{m+2}`.  Then `α^{*m} < ϑ_m(α)` and `ϑ_m(α) < ϑ_m(γ) ⇔ α < γ ∧ α^{*m} < ϑ_m(γ) ∨ ϑ_m(α) ≤
  γ^{*m}`."
* (C) Convention 4.1: "Given a term `α = ϑᵗ(ξ) ∈ Tᵗ` we introduce the notational convention that `α = ϑᵗ(Δ + η)`
  automatically means that `ξ = Δ + η` is a decomposition such that `Ω₁ | Δ` and `η < Ω₁`."
* (E) Lemma 4.3: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ`.  Then `τ < α ∈ E ⇔ Δ > 0`."
* (P) Def 5.1: "Let `τ ∈ E` and `Tᵗ` be the notation system over `τ`.  Further, let `σ ∈ {1} ∪ (E ∩ τ)`.  We define
  `Tᵗ[σ] := {α ∈ Tᵗ | Parᵗ(α) ⊆ σ}` and `π_{σ,τ} : Tᵗ[σ] → T^σ` by the following clauses: • `π_{σ,τ}(ξ) := ξ` if
  `ξ < σ` • `π_{σ,τ}(ξ) := π_{σ,τ}(ξ₁) + π_{σ,τ}(ξ₂)` if `ξ =NF ξ₁ + ξ₂ > τ` • `π_{σ,τ}(ξ) := ϑ_k(π_{σ,τ}(η))` if
  `ξ = ϑ_k(η)` for some `k > 0` and `η ∈ Tᵗ[σ] ∩ Ω_{k+2}` • `π_{σ,τ}(ξ) := ϑ^σ(π_{σ,τ}(η))` if `ξ = ϑᵗ(η)` for some
  `η ∈ Tᵗ[σ] ∩ Ω₂`."

Our steps (used in every docstring below; `E₁ := ε_{Ω₁+1}`, `τ` a countable `ε`-number, `Ω₀ = τ`).
* (◇1) `ϑ₁(0) = Ω₁` (the note of D, `1 < n`) and `ϑ₁(m) = ω^{Ω₁+m}` for `1 ≤ m < E₁` (W with `m = 1`: `ϑ₁(1 + a) =
  ω̄_{Ω₁+a}`; the members of `P ∖ E` from `Ω₁` on below `E₁` are the `ω^{Ω₁+1+a}`, as no `ε`-number lies in `(Ω₁,
  E₁)`).  `ϑ₁` does not depend on `τ`: by D, `τ = Ω₀` enters only `Cⁿ₀`.
* (◇2) **`E₁ = ϑ₁(Ω₂)`, a term of `Tᵗ`.**  Fix `n ≥ 3` with `Ω₂ < θⁿ₂` (T: `n` large enough; by Θ with `m = 0`, `k
  = 1`, `Ω₂ + 1 ∈ T₀ ∩ Ω₃` lies below `θ₂ = sup_n θⁿ₂`, and the `θⁿ₂ = Tⁿ₂ ∩ Ω₃` grow with `n` by EX), so `ϑ₁(Ω₂)
  = ϑⁿ₁(Ω₂)`.  `Ω₂ = ϑⁿ₂(0)` (note of D, `2 < n`) and `= ϑ₂(0) ∈ T₀` (T: `0 ∈ Ω₀`, third clause with `k = 2`), so
  `ϑ₁(Ω₂) ∈ T₀` (third clause, `k = 1`, `Ω₂ ∈ T₀ ∩ Ω₃`).  Upper bound: put `X := E₁ ∪ [Ω₂, ∞)`.  `X` contains `Ω₁ ∪
  E₁` and satisfies every clause of D for `Cⁿ₁(Ω₂, E₁)`: a sum of two members of `E₁` is in `E₁` (`E₁ ∈ P`), a sum
  with a summand `≥ Ω₂` is `≥ Ω₂`; `ϑⁿ_k(ξ) ≥ Ω_k ≥ Ω₂` for `1 < k < n` (B); for `ξ ∈ X ∩ Ω₂ = E₁`, `ϑⁿ₁(ξ) = Ω₁` or
  `ω^{Ω₁+ξ} < E₁` (◇1, W).  So `Cⁿ₁(Ω₂, E₁) ⊆ X` (D: "defined inductively"), i.e. `Cⁿ₁(Ω₂, E₁) ∩ Ω₂ ⊆ E₁`, and
  `Ω₂ = ϑⁿ₂(0) ∈ Cⁿ₁(Ω₂, E₁)` (third clause, `k = 2`, `0 ∈ Ω₁`); as `E₁ < Ω₂`, D gives `ϑⁿ₁(Ω₂) ≤ E₁`.  Lower bound:
  `a₀ := 0`, `a_{j+1} := ϑ₁(a_j)` (`a₁ = Ω₁`, `a_{j+1} = ω^{Ω₁+a_j}`, `sup_j a_j = E₁` by ◇1) are in `T₀ ∩ Ω₂`;
  `P₁(a_j) ⊆ {a₁, …, a_j}` (S), `(Ω₂)^{*1} = 0` (S: `Sub₁(ϑ₂(0)) = {Ω₂, 0}`); by induction `(a_j)^{*1} = a_j <
  ϑ₁(Ω₂)` and L (`m = 1`, `α = a_j < γ = Ω₂`) gives `a_{j+1} < ϑ₁(Ω₂)`.  So `E₁ ≤ ϑ₁(Ω₂)`.
* (◇S) **The subterms.**  By S (third clause, `k = 1 ≥ 0`, `k = 2 ≥ 0`; `0` a parameter), `Subᵗ₀(ϑ₁(Ω₂)) = {E₁, Ω₂,
  0}`: so `Parᵗ(E₁) = {0}` and `P₀(E₁) = ∅` (`E₁, Ω₂ ∉ [τ, Ω₁)`, `0 ∉ P`).  For `η ∈ Tᵗ ∩ Ω₁`, `η > 0`, the term of
  `E₁ + η` is `ϑ₁(Ω₂) + η` (`η < Ω₁ < E₁`), so `P₀(E₁ + η) = P₀(η)` (S, second clause; `E₁ + η ∉ P`); for `η = 0`,
  `P₀(E₁) = ∅ = P₀(0)`.  Every member of `P₀(η)` is `≤ η` (L: `β^* < ϑ₀(β)` along the term of `η`; step ★1 of
  `R2.CitedLu`), so **`(E₁ + η)^* ≤ η`**.
* (◇T) `E₁ + η ∈ Tᵗ ∩ Ω₂` for `η ∈ Tᵗ ∩ Ω₁` (◇2, T second clause; `E₁ + η < E₁ + Ω₁ < Ω₂`), and `Ω₁ ∣ E₁`
  (`Ω₁·E₁ = ω^{Ω₁+E₁} = E₁`), so `ϑᵗ(E₁ + η)` has `Δ = E₁ > 0`, `η` as in C.
* (◇*) For a code `M' < E₁` with `rjDat M' ∈ Tᵗ` and `η' ∈ Tᵗ ∩ Ω₁`: `Ω₁·M' + η' ∈ Tᵗ ∩ Ω₂` and `(Ω₁·M' + η')^* ≤
  max(rjDat M', η')` (steps □2 and □* of `R2.CitedRj`; for `M' < Ω₁`, `rjDat M' = M'`, steps ◆β, ◆* of `R2.CitedLv`).
  For `M' = E₁`: `Ω₁·E₁ + η' = E₁ + η'`, `rjDat E₁ = 0 ∈ Tᵗ`, and `(E₁ + η')^* ≤ η'` (◇S).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Googology.Trans.PoR.InaccPsi.R2.Rj

/-- **[W07a] Def 3.1, Lemma 3.3 (b), Lemma 3.5, Corollary 3.21, Def 3.22, Corollary 3.24, Def 3.28, Lemma 3.30
(`m = 1`)** (texts D, B, W, EX, T, Θ, S, L): `ε_{Ω₁+1} ∈ Tᵗ` for every base `τ`.

Our steps.  ◇2 of the module docstring: `ε_{Ω₁+1} = ϑ₁(Ω₂)` and `ϑ₁(Ω₂) ∈ T₀ = Tᵗ` (T, third clause twice). -/
axiom ssE_mem {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) : Gg.ggE ∈ Tset τ

/-- **[W07a] Def 5.1 (first and third clauses), Def 3.28, Def 3.1, Lemma 3.3 (b), Lemma 3.5, Def 3.22, Corollary
3.24, Lemma 3.30 (`m = 1`)** (texts P, S, D, B, W, T, Θ, EX, L): for bases `σ < τ` (`σ ∈ E ∩ τ`):
`ε_{Ω₁+1} ∈ Tᵗ[σ]` and `π_{σ,τ}(ε_{Ω₁+1}) = ε_{Ω₁+1}`.

Our steps.  `ε_{Ω₁+1} = ϑ₁(Ω₂)` (◇2) with `Parᵗ(ε_{Ω₁+1}) = {0} ⊆ σ` (◇S; `0 < σ`), so `ε_{Ω₁+1} ∈ Tᵗ[σ]` (P).  P,
third clause with `k = 2`, `η = 0 ∈ Tᵗ[σ] ∩ Ω₄`: `π_{σ,τ}(Ω₂) = π_{σ,τ}(ϑ₂(0)) = ϑ₂(π_{σ,τ}(0)) = ϑ₂(0) = Ω₂` (first
clause, `0 < σ`); third clause with `k = 1`, `η = Ω₂ ∈ Tᵗ[σ] ∩ Ω₃` (`Parᵗ(Ω₂) = {0}`, S): `π_{σ,τ}(ϑ₁(Ω₂)) =
ϑ₁(Ω₂)`.  The `ϑ₁` of `T^σ` is the same function (◇1), so the value is `ε_{Ω₁+1}` again (◇2 over the base `σ`). -/
axiom ssE_TB {σ τ : Ordinal.{0}} (h : Bases σ τ) : Gg.ggE ∈ TB τ σ ∧ pi σ τ Gg.ggE = Gg.ggE

/-- **[W07a] Lemma 3.30, the direction `⇐`, with Def 3.28, Def 3.22, Convention 4.1** (texts L, S, T, C, and ◇):
for `M' ≤ ε_{Ω₁+1}` (a code, or `ε_{Ω₁+1}` itself) with `rjDat M' ∈ Tᵗ`, `η', η ∈ Tᵗ ∩ Ω₁`, `Ω₁·M' + η' <
ε_{Ω₁+1} + η`, and `rjDat M', η'` below `ϑᵗ(ε_{Ω₁+1} + η)`: `ϑᵗ(Ω₁·M' + η') < ϑᵗ(ε_{Ω₁+1} + η)`.

Our steps.  `α := Ω₁·M' + η'` and `γ := ε_{Ω₁+1} + η` lie in `Tᵗ ∩ Ω₂` (◇*, ◇T).  `α^* ≤ max(rjDat M', η') <
ϑ₀(γ)` (◇*, the hypotheses).  So `α < γ ∧ α^* < ϑ₀(γ)`, the first disjunct of the right side of L (`m = 0`), and
`ϑ₀(α) < ϑ₀(γ)`. -/
axiom ssVt_lt {τ M' η' η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM'E : M' ≤ Gg.ggE)
    (hM'T : rjDat M' ∈ Tset τ) (hη' : η' ∈ Tset τ) (hη'Ω : η' < Om1) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (harg : Om1 * M' + η' < Gg.ggE + η) (hd' : rjDat M' < vt τ (Gg.ggE + η))
    (hη'v : η' < vt τ (Gg.ggE + η)) :
    vt τ (Om1 * M' + η') < vt τ (Gg.ggE + η)

/-- **[W07a] Lemma 3.30, the direction `⇒`, with Def 3.28** (texts L, S, and ◇): for `ξ ∈ Tᵗ ∩ Ω₂` and `η ∈ Tᵗ ∩ Ω₁`
with `η < ϑᵗ(ξ)`: `ϑᵗ(ξ) < ϑᵗ(ε_{Ω₁+1} + η)` implies `ξ < ε_{Ω₁+1} + η`.

Our steps.  `γ := ε_{Ω₁+1} + η ∈ Tᵗ ∩ Ω₂` (◇T) and `γ^* ≤ η < ϑ₀(ξ)` (◇S, the hypothesis).  L (`m = 0`, `α = ξ`):
`ϑ₀(ξ) < ϑ₀(γ)` gives `ξ < γ ∧ ξ^* < ϑ₀(γ)` or `ϑ₀(ξ) ≤ γ^*`; the second is impossible.  So `ξ < γ`. -/
axiom ssLt_of_vt_lt {τ ξ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hξ : ξ ∈ Tset τ) (hξ2 : ξ < OmTwo)
    (hη : η ∈ Tset τ) (hηΩ : η < Om1) (hηξ : η < vt τ ξ) (h : vt τ ξ < vt τ (Gg.ggE + η)) :
    ξ < Gg.ggE + η

/-- **[W07a] Lemma 3.30 (`α^* < ϑ₀(α)`), Lemma 4.3, Def 3.28, Convention 4.1** (texts L, E, S, C, and ◇): for `η ∈ Tᵗ ∩
Ω₁`: `η < ϑᵗ(ε_{Ω₁+1} + η)`.

Our steps.  `γ := ε_{Ω₁+1} + η ∈ Tᵗ ∩ Ω₂` with `Δ = ε_{Ω₁+1} > 0` (◇T).  L (`m = 0`): `γ^* < ϑ₀(γ) =: a`.  E: `τ < a
∈ E`.  Every additive component of `η` is `< τ` or `≤` a member of `P₀(η) = P₀(γ)` (◇S; step ★1 of `R2.CitedLu`:
the components of `η ≥ τ` are `ϑ₀`-terms, members of `P₀(η)`), hence `< a`; `a ∈ P`, so `η < a` (for `η = 0`: `a >
τ > 0`). -/
axiom ssLevel_lt {τ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    η < vt τ (Gg.ggE + η)

end Googology.Trans.PoR.InaccPsi.R2
