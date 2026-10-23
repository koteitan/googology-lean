import Googology.Trans.PoR.InaccPsi.R2.CitedRj

set_option autoImplicit false

/-!
# A cited fact of Wilken 2007, as an axiom, ONCE for every level `Ω₁ ≤ M < ε_{Ω₁+1}`: the data of the argument

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

Same conventions as `R2.CitedRj` (`Ω₁ = Om1`, `Ω₂ = OmTwo`, `Tset τ = Tᵗ`, `vt τ = ϑᵗ = ϑ₀`, every base `τ` a countable
`ε`-number; a **code** is an `M < ε_{Ω₁+1} = Gg.ggE`, `rjDat M` the largest countable leaf of its hereditary Cantor
normal form over `{0, Ω₁}`).

What is **not** restated (checked first): `R2.CitedRj` (`rjArg_mem` is the direction "data in `Tᵗ` ⇒ argument in
`Tᵗ`"), `R2.CitedLq`, `R2.CitedLg`, `R2.CitedLv`, `R2.CitedLu`.  The axiom below is **the converse of `rjArg_mem` at
every level**.  The converse at `M = Ω₁·γ + β` (`γ ∈ Tᵗ` and `β ∈ Tᵗ`) is a theorem derived from it (`Rk.rkArg_T`,
`Rk.rkArgT_gamma`, with the closure of `Tᵗ ∩ Ω₁` under `ω^·` and `+` and the theorem `Rj.rjArgT_beta`).

Literal texts (all of [W07a]; as quoted in `R2.CitedRj` and checked again against the paper):
* (T) Def 3.22: "`Ω_m ⊆ T_m` • `ξ, η ∈ T_m ⇒ ξ + η ∈ T_m` • `ξ ∈ T_m ∩ Ω_{k+2} ⇒ ϑ_k(ξ) ∈ T_m` for `k ≥ m`."
* (Θ) Theorem 3.23: "`T_m ∩ Ω_{m+1} = θ_m = sup_{n≥m} ϑ_m(⋯(ϑ_n(0))⋯)`."
* (U) Remark after Corollary 3.24: "each `T_m` again gives rise to a notation system with parameters from `Ω_m` that
  provides a unique term for every ordinal which is element of some `Tⁿ_m` where `n > m`".
* (Z) After Def 3.1: "Note that we have `ϑⁿ_m(0) = Ω_m` for `m < n`".
* (W) Def 3.4: "Let `α ↦ ω̄_α` be the enumeration function of the additive principle numbers which are not epsilon
  numbers."  Lemma 4.2: "For any `m < ω` and any `α < Ω_{m+1}` we have `ϑ_m(1 + α) = ω̄_{Ω_m+α}`".
* (S) Def 3.28: "`Subᵗ_m(α) := {α}` for parameters `α < τ`; `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ) ∪ Subᵗ_m(η)` for
  `ξ, η ∈ Tᵗ` s.t. `α =NF ξ + η > τ`; `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ)` if `k ≥ m`, `{α}` if `k < m`, for `α = ϑ_k(ξ)`
  where `ξ ∈ Tᵗ ∩ Ω_{k+2}`.  …  `P_m(α) := Subᵗ_m(α) ∩ P ∩ [Ω_m, Ω_{m+1})` and `α^{*m} := max(P_m(α) ∪ {0})`."
* (L) Lemma 3.30: "For `m < ω` the function `ϑ_m ↾ Tᵗ ∩ Ω_{m+2}` is 1-1 and has values in `P ∩ [Ω_m, Ω_{m+1})`.  Let
  `α, γ ∈ Tᵗ ∩ Ω_{m+2}`.  Then `α^{*m} < ϑ_m(α)` and `ϑ_m(α) < ϑ_m(γ) ⇔ α < γ ∧ α^{*m} < ϑ_m(γ) ∨ ϑ_m(α) ≤ γ^{*m}`."
* (E) Lemma 4.3: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ`.  Then `τ < α ∈ E ⇔ Δ > 0`."
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Googology.Trans.PoR.InaccPsi.R2.Rj

/-- **[W07a] Def 3.22, Theorem 3.23, the Remark after Corollary 3.24, Def 3.28, Lemma 3.30 (`m = 1`), Lemma 4.2, the
remark after Def 3.1, Lemma 4.3** (texts T, Θ, U, S, L, W, Z, E): for a code `Ω₁ ≤ M < ε_{Ω₁+1}` and `η < Ω₁`
with `Ω₁·M + η ∈ Tᵗ`: `rjDat M ∈ Tᵗ` (**the converse of `R2.rjArg_mem`**).

Our steps.
* (★1) `ϑ₁(0) = Ω₁` (Z) and `ϑ₁(m) = ω^{Ω₁+m}` for `1 ≤ m < ε_{Ω₁+1}` (W: `ϑ₁(1 + a) = ω̄_{Ω₁+a}`; the non-`ε`
  additive principal numbers below `Ω₁` have order type `Ω₁`, and there is no `ε`-number in `(Ω₁, ε_{Ω₁+1})`); so
  `m ↦ ϑ₁(m)` is strictly increasing on `[0, Ω₂)` (W: `ω̄` is an enumeration) and `Ω₁·ω^m = ϑ₁(m)`.
* (★2) `ε_{Ω₁+1} ≤ ϑ₁(Ω₂)`: put `a₀ = 0`, `a_{k+1} = ϑ₁(a_k)` (`a₁ = Ω₁`, `a₂ = ω^{Ω₁·2}`, …, `sup_k a_k =
  ε_{Ω₁+1}` by ★1); every `a_k ∈ Tᵗ ∩ Ω₂` (T, `Ω₁ = ϑ₁(0)`).  `Ω₂ = ϑ₂(0) ∈ Tᵗ` (Z, T) and `(Ω₂)^{*1} = 0` (S: `Ω₂`
  is not in `[Ω₁, Ω₂)` and its only subterm is `0 ∉ P`).  By induction on `k`: `P₁(a_k) ⊆ {a₁, …, a_k}` (S), so
  `(a_k)^{*1} = a_k < ϑ₁(Ω₂)` (i.h.; `a₀^{*1} = 0`), and `a_k < Ω₂`, so L (`m = 1`, `α = a_k`, `γ = Ω₂`) gives
  `a_{k+1} = ϑ₁(a_k) < ϑ₁(Ω₂)`.
* (★3) **The argument of a `ϑ₁`-summand.**  Let `s = ϑ₁(ζ) ∈ Tᵗ` be a term (`ζ ∈ Tᵗ ∩ Ω₃`, T, S) with value
  `s = ω^{Ω₁+m} < ε_{Ω₁+1}`.  If `ζ ≥ Ω₂`: `ζ = Ω₂` or L (`α = Ω₂`, `γ = ζ`, `Ω₂ < ζ`, `(Ω₂)^{*1} = 0 < ϑ₁(ζ)`)
  gives `ϑ₁(Ω₂) ≤ ϑ₁(ζ) = s < ε_{Ω₁+1} ≤ ϑ₁(Ω₂)` (★2), impossible.  So `ζ < Ω₂`, and `ϑ₁(ζ) = ϑ₁(m)` with both
  arguments in `[0, Ω₂)` gives `ζ = m` (★1); hence `m ∈ Tᵗ`.
* (★4) **Every code `z ∈ Tᵗ ∩ [Ω₁, ε_{Ω₁+1})` has all its leaves in `Tᵗ`**, by induction on `z`.  By U the term of
  `z` is unique; its additive components (S, second clause) are in `Tᵗ`; a component `≥ Ω₁` is additive principal in
  `[Ω₁, Ω₂)`, hence not a parameter (`< τ`), not a `ϑ₀`-value (`< Ω₁`, L), not a `ϑ_k`-value for `k ≥ 2` (`≥ Ω₂`,
  L), so it is a `ϑ₁`-term `ϑ₁(ζ) = ω^{e}` (`e ≥ Ω₁`); by ★3 with `m = −Ω₁ + e` (★1: `ω^e = ϑ₁(−Ω₁ + e)` for `e > Ω₁`,
  `ζ = 0` for `e = Ω₁`), `−Ω₁ + e ∈ Tᵗ`, so `e = Ω₁ + (−Ω₁ + e) ∈ Tᵗ` (T) and `e < z`; the leaves of `e` are those of
  `−Ω₁ + e` (or none for `e = Ω₁`) and are in `Tᵗ` by the i.h. at `e` (if `e > Ω₁`).  The components `< Ω₁` lie in
  `Tᵗ ∩ Ω₁`, and so does their sum, the countable remainder of `z` (T).  The leaves of `z` (the countable remainders
  and countable exponents of its hereditary normal form) are exactly these remainders and the leaves of the exponents
  `e` of its components, all in `Tᵗ`.
* (★5) **The claim.**  `ξ := Ω₁·M + η ∈ Tᵗ ∩ Ω₂` (`M < ε_{Ω₁+1}`).  By U the term of `ξ` is unique; its additive
  components are in `Tᵗ` (S, second clause), and as in ★4 each component `≥ Ω₁` is a `ϑ₁`-term; these components sum
  to `Δ := Ω₁·M` (the part of `ξ` that is a multiple of `Ω₁`), and the components `< Ω₁` sum to `η`.  For
  `M =CNF Σ ω^{e_l}·k_l + r` (`e_l ≥ Ω₁`, `r < Ω₁`, `r =ANF Σ ω^{b_i}`): `Δ = Σ ω^{Ω₁+e_l}·k_l + Σ ω^{Ω₁+b_i}`.  For a
  component `ω^{Ω₁+e_l} = ϑ₁(e_l)` (★1) ★3 gives `e_l ∈ Tᵗ`, and ★4 (with `e_l ∈ [Ω₁, ε_{Ω₁+1})`) puts the leaves of
  `e_l` in `Tᵗ`.  For a component `ω^{Ω₁+b_i} = ϑ₁(b_i)` (`b_i ≥ 1`) or `= Ω₁ = ϑ₁(0)` (`b_i = 0`), ★3 gives
  `b_i ∈ Tᵗ`; so `r = Σ ω^{b_i} ∈ Tᵗ ∩ Ω₁ = θ₀` (Θ: `θ₀` is a supremum of values `ϑ₀(ϑ₁(⋯))`, which are `ε`-numbers by E
  (`Δ = ϑ₁(⋯) > 0`); so `θ₀` is closed under `ω^·` and `+`).  The leaves of `M` are `r` and the leaves of the `e_l` (`rjDat`: the recursion through `log_ω` and the
  remainder), all in `Tᵗ`; `rjDat M` is one of them (or `0 ∈ Tᵗ`, a parameter, if there is none). -/
axiom rkArg_dat {τ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Om1 ≤ M) (hME : M < Gg.ggE)
    (hηΩ : η < Om1) (h : Om1 * M + η ∈ Tset τ) : rjDat M ∈ Tset τ

end Googology.Trans.PoR.InaccPsi.R2
