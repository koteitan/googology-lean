import Googology.Trans.PoR.InaccPsi.R2.Cited

set_option autoImplicit false

/-!
# Wilken 2007 §6: the base change commutes with the localization `α = ϑᵗ(Δₙ)` on `[α, α⁺)`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

One axiom, `tvSeg_pi`: for bases `σ < τ` (countable `ε`-numbers), `n ≥ 1`, `α = ϑᵗ(Δₙ) = Dl τ n`, `α' = ϑ^σ(Δₙ) =
Dl σ n`, and `y ∈ T^α[σ]` with `α ≤ y < α⁺ = Dp τ n`:
`π_{σ,τ}(y) ∈ T^{α'}[σ]` and `π_{σ,α'}(π_{σ,τ}(y)) = π_{σ,α}(y)`.
It is the statement `TrInner` of the round-95 reduction (`R2.Tr.trComm_iff_inner`) in the form "the outer base
change `π_{σ,τ}` is, on the segment `[α, α⁺)` read in `T^α`, the base change `α ↦ α'` of that segment"; it is not a
consequence of the earlier `Cited*` axioms, which describe `π` only through order, `+`, `Par`, `ht`, `lh` and the
inner parameters only through Lemma 6.10 (`R2.par_track`, one direction).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- **[W07a] Definition 6.2 and Lemma 6.3 (p. 148–149), with Definition 5.1 and Lemma 5.3 (p. 144), Convention 4.1
(p. 142), Lemma 4.3 (p. 142), Definition 3.22 (p. 139), the Remark after Corollary 3.24 (p. 140), Definition 3.28
(p. 141), Lemma 3.30 (p. 142), Definition 6.1 (p. 148).**  For bases `σ < τ`, `n ≥ 1`, `α = ϑᵗ(Δₙ)`, `α' = ϑ^σ(Δₙ)`
and `y ∈ T^α[σ]` with `α ≤ y < α⁺`: `π_{σ,τ}(y) ∈ T^{α'}[σ]` and `π_{σ,α'}(π_{σ,τ}(y)) = π_{σ,α}(y)`.

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
  ϑᵗ(Δ + η + 1)` • `ϑ^α(ξ)^{t^α_τ} := 0` if `ϑ^α(ξ) > ϑ^α(Δ)`."  After it (p. 149): "It is also easy to see that the
  assigned ordinals belong to the respective notation system.  By recursion on the definitions it is easy to verify
  that `ϑ_k`-functions are only applied to ordinals from the respective notation system below `Ω_{k+2}`."
  (The bracket […] stands for the printed "such that `ϑᵗ(ξ) ≥ α` in order to define `ϑᵗ(ξ)^{t^τ_α}`", evidently
  `ϑ^α(ξ) ≥ α`, `ϑ^α(ξ)^{t^α_τ}`; only the four cases listed after it are used.)
* (6.3) Lemma 6.3: "We have • `α⁺ = ϑ^α(Δ)`, • the restriction of `t^τ_α` to `Tᵗ_{α⁺}` is the identity, and • the
  restriction of `t^α_τ` to `T^α_{α⁺}` is the identity."
* (C) Convention 4.1: "Given a term `α = ϑᵗ(ξ) ∈ Tᵗ` we introduce the notational convention that `α = ϑᵗ(Δ + η)`
  automatically means that `ξ = Δ + η` is a decomposition such that `Ω₁ | Δ` and `η < Ω₁`. […] In a situation where
  some `α = ϑᵗ(Δ + η)` is fixed, we will write `α⁺` to denote the ordinal `ϑᵗ(Δ + η + 1)`."  And: "for the argument of
  a `ϑᵗ`-term in `Tᵗ`, to be a nonzero multiple of `Ω₁` means to be a sum of `ϑ₁`-terms."
* (E) Lemma 4.3: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ`.  Then `τ < α ∈ E ⇔ Δ > 0`."
* (P) Def 5.1: "Let `τ ∈ E` and `Tᵗ` be the notation system over `τ`.  Further, let `σ ∈ {1} ∪ (E ∩ τ)`.  We define
  `Tᵗ[σ] := {α ∈ Tᵗ | Parᵗ(α) ⊆ σ}` and `π_{σ,τ} : Tᵗ[σ] → T^σ` by the following clauses: • `π_{σ,τ}(ξ) := ξ` if
  `ξ < σ` • `π_{σ,τ}(ξ) := π_{σ,τ}(ξ₁) + π_{σ,τ}(ξ₂)` if `ξ =NF ξ₁ + ξ₂ > τ` • `π_{σ,τ}(ξ) := ϑ_k(π_{σ,τ}(η))` if
  `ξ = ϑ_k(η)` for some `k > 0` and `η ∈ Tᵗ[σ] ∩ Ω_{k+2}` • `π_{σ,τ}(ξ) := ϑ^σ(π_{σ,τ}(η))` if `ξ = ϑᵗ(η)` for some
  `η ∈ Tᵗ[σ] ∩ Ω₂`."
* (Π) Lemma 5.3: "(b) `π_{σ,τ}` preserves `<`.  (c) `π_{σ,τ}` preserves ordinal addition."  Its proof: "At first,
  note that `Tᵗ[σ]` is closed under ordinal addition and decomposition into additive principal numbers.  Clearly,
  `Tᵗ[σ] ∩ τ = σ`, `π_{σ,τ}(ξ) ≥ σ` for every `ξ ∈ Tᵗ[σ] − τ`, and if `ξ ∈ Tᵗ[σ] ∩ P` we have `π_{σ,τ}(ξ) ∈ T^σ ∩ P`.
  Another simple observation is that for every `k < ω` and `ξ ∈ Tᵗ[σ] ∩ [Ω_k, Ω_{k+1})` we get `π_{σ,τ}(ξ) ∈ T^σ ∩
  [Ω_k, Ω_{k+1})`, where for `k = 0` of course `Ω₀ = τ` in the former and `Ω₀ = σ` in the latter expression."
* (T) Def 3.22: "`Ω_m ⊆ T_m` • `ξ, η ∈ T_m ⇒ ξ + η ∈ T_m` • `ξ ∈ T_m ∩ Ω_{k+2} ⇒ ϑ_k(ξ) ∈ T_m` for `k ≥ m`."
* (U) Remark after Corollary 3.24: "each `T_m` again gives rise to a notation system with parameters from `Ω_m` that
  provides a unique term for every ordinal which is element of some `Tⁿ_m` where `n > m`".
* (S) Def 3.28: "`Subᵗ_m(α) := {α}` for parameters `α < τ` • `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ) ∪ Subᵗ_m(η)` for `ξ, η ∈
  Tᵗ` s.t. `α =NF ξ + η > τ` • `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ)` if `k ≥ m`, `{α}` if `k < m`, for `α = ϑ_k(ξ)` where
  `ξ ∈ Tᵗ ∩ Ω_{k+2}`.  We define the additive principal parts of level `m` of `α ∈ Tᵗ` by `P_m(α) := Subᵗ_m(α) ∩ P ∩
  [Ω_m, Ω_{m+1})` and `α^{*m} := max(P_m(α) ∪ {0})`.  The set of parameters `< τ` used in the unique term denoting
  some `α ∈ Tᵗ` is denoted by `Parᵗ(α) := Subᵗ₀(α) ∩ τ`."  Convention 3.29: "instead of `*0` we will also write `*`."
* (L) Lemma 3.30: "For `m < ω` the function `ϑ_m ↾ Tᵗ ∩ Ω_{m+2}` is 1-1 and has values in `P ∩ [Ω_m, Ω_{m+1})`.  Let
  `α, γ ∈ Tᵗ ∩ Ω_{m+2}`.  Then `α^{*m} < ϑ_m(α)` and […]".

Notation.  `Δ := Δₙ = ϑ₁(⋯ϑₙ(0)⋯)` (`R2.Dl`: `Dl τ n = ϑᵗ(Δₙ)`, `R2.Dp`: `Dp τ n = ϑᵗ(Δₙ + 1)`); `Δ` is a nonzero
multiple of `Ω₁` built from `ϑ_k` (`k ≥ 1`) and the parameter `0` only.  `α := ϑᵗ(Δ)`, `α⁺ := ϑᵗ(Δ + 1)`,
`α' := ϑ^σ(Δ)`, `α'⁺ := ϑ^σ(Δ + 1)` (C, `η = 0`).  `q := π_{σ,τ}`, `r := π_{σ,α}`, `r' := π_{σ,α'}`.  `t := t^α_τ`
(second part of 6.2 for the pair `τ, α`), `t' := t^σ_{α'}` (first part of 6.2 for the pair `σ, α'`).  For a term `ζ`
of `T^α` with parameters `< σ`, `s(ζ)` is the expression obtained from `ζ` by writing `ϑ^{α'}` for every `ϑ^α`; for a
term `e` of `Tᵗ`, `q̂(e)` is the expression obtained by writing `ϑ^σ` for every `ϑᵗ`.  A "`ϑ₀`-subterm" of a term over
the base `β` is a subterm `ϑ^β(·)`.  "Term of `x`" means the unique term (U).

Our steps.
* (★0) **`π` is substitution of the base.**  By induction along the four clauses of P: for `e ∈ Tᵗ[σ]` (its term),
  `q(e)` is the value of `q̂(e)` (clause 1 keeps parameters `< σ`, clauses 2, 3 commute with `+`, `ϑ_k`, clause 4
  writes `ϑ^σ` for `ϑᵗ`).  The same holds for `r` (`ϑ^α ↦ ϑ^σ`) and `r'` (`ϑ^{α'} ↦ ϑ^σ`); P applies, since `σ ∈ E`,
  `σ < τ < α` and `σ < α'` (E).  The leaves of every term are parameters, and by S and L every subterm that is not a
  parameter is an `=NF`-sum above the base, a `ϑ₀`-term (value `≥` base, L) or a `ϑ_k`-term `k ≥ 1` (value `≥ Ω₁`, L),
  so `Par` of a term is the set of its parameter leaves, and `P₀` of a term is the set of its `ϑ₀`-subterms (sums are
  not additive principal; parameters are below the base).
* (★1) (a) `τ < α ∈ E`, `σ < α' ∈ E` (E, `Δ > 0`); `α, α⁺ ∈ Tᵗ[σ]`, `α', α'⁺ ∈ T^σ` (T; their only parameter is
  `0 < σ`, S); `q(α) = α'`, `q(α⁺) = α'⁺` (★0, `Δ` has no `ϑᵗ`).  (b) 6.3 for `(τ, α)`: `α⁺ = ϑ^α(Δ)` and `t` is the
  identity on `T^α_{α⁺}`; 6.3 for `(σ, α')`: `α'⁺ = ϑ^{α'}(Δ)` and `t'` is the identity on `T^σ_{α'⁺}`.  As `t(ζ)` is
  a term of `Tᵗ` (the remark after 6.2), "identity" means: `t(ζ)` denotes `ζ`, so by U it is the term of `ζ` in
  `Tᵗ`; likewise `t'(e)` is the term in `T^{α'}` of the value of `e`.  (c) For a countable `ζ ∈ T^α` with
  `α ≤ ζ < α⁺`: every `ϑ₀`-subterm of `ζ` has value `≤ ζ` (L, `α^{*0} < ϑ₀(α)`, applied down the term), so
  `ζ^{*α} ≤ ζ < α⁺` and `ζ ∈ T^α_{α⁺}` (6.1).
* (★2) **Main claim**, by induction on the length of a term `ζ` of `T^α` with `Par^α(ζ) ⊆ σ` and `ζ^{*α} < α⁺`:
  (i) `t(ζ) ∈ Tᵗ[σ]`; every `ϑᵗ`-subterm of `t(ζ)` has value in `[α, α⁺)`; `t(ζ)` has a `ϑᵗ`-subterm iff `ζ` has a
  `ϑ^α`-subterm.  (ii) `q(ζ) ∈ T^σ_{α'⁺}` and `t'(q̂(t(ζ))) = s(ζ)`.  (By ★0 and ★1b, `q̂(t(ζ))` is the term of
  `q(ζ)` in `T^σ`, and the values of its `ϑ^σ`-subterms are the `q`-images of those of `t(ζ)`, which lie in
  `[α', α'⁺)` by (i), Π(b), ★1a; so `(q ζ)^{*σ} < α'⁺` (★0) follows from (i) in every case below.)  Subterms of `ζ`
  satisfy the hypotheses (S: `Sub` of a subterm is a subset).
  (1) `ζ < α` a parameter: `ζ ∈ Par^α(ζ) ⊆ σ`.  `t(ζ) = ζ` (first clause of `t`; the term of `ζ < σ < τ` in `Tᵗ` is
  the parameter `ζ`), `q̂(ζ) = ζ`, `t'(ζ) = ζ` (`ζ < α'`, first clause of `t'`) `= s(ζ)`.  No `ϑ`-subterms.
  (2) `ζ =NF ζ₁ + ζ₂ > α`: `t(ζ) = t(ζ₁) + t(ζ₂)` (second clause of `t`); by ★1b these denote `ζ₁, ζ₂`, so this is the
  `=NF`-sum term of `ζ > τ` in `Tᵗ`, and `Parᵗ(t ζ) = Parᵗ(t ζ₁) ∪ Parᵗ(t ζ₂) ⊆ σ` (S); (i) by the IH.  `q̂(t ζ) =
  q̂(t ζ₁) + q̂(t ζ₂)` with values `q(ζ₁), q(ζ₂)`; `q(ζ) = q(ζ₁) + q(ζ₂)` (Π c) is an `=NF`-sum (Π b and "`π(ξ) ∈ P` for
  `ξ ∈ P`") above `q(α) = α'` (Π b, ★1a), so `t'(q̂ t ζ) = t'(q̂ t ζ₁) + t'(q̂ t ζ₂)` (second clause of `t'`)
  `= s(ζ₁) + s(ζ₂) = s(ζ)`.
  (3) `ζ = ϑ_k(η)`, `k ≥ 1`: `t(ζ) = ϑ_k(t η)` (third clause), `Parᵗ(t ζ) = Parᵗ(t η) ⊆ σ` (S, `k ≥ 0`); `q̂(t ζ) =
  ϑ_k(q̂(t η))`; `t'` gives `ϑ_k(t'(q̂ t η)) = ϑ_k(s η) = s(ζ)` (third clause of `t'`).
  (4) `ζ = ϑ^α(0) = α`: `t(ζ) = ϑᵗ(Δ)` (fourth clause of `t`, first case, `η = 0`), parameters `{0} ⊆ σ`, its only
  `ϑᵗ`-subterm is itself (value `α`); `q̂(t ζ) = ϑ^σ(Δ)` (value `α'`); `t'(ϑ^σ(Δ)) = ϑ^{α'}(0)` (fourth clause of `t'`,
  first case) `= s(ζ)`.
  (5) `ζ = ϑ^α(ξ) > α`: `ζ ∈ P^α₀(ζ)`, so `ζ ≤ ζ^{*α} < α⁺ = ϑ^α(Δ)` (★1b); by 6.2 (`t`, second case) `ξ = Γ + ρ` with
  `Ω₁ | Γ`, `ρ < Ω₁` (C), `Γ < Δ`.  The terms of `ξ`, `Γ`, `ρ` are (`=NF`-sums of components of) the subterm `ξ`
  (S), shorter than `ζ`, with parameters in `Par^α(ζ)` and `^{*α}` at most `ξ^{*α} < ζ` (L); so the IH applies to
  `ξ, Γ, ρ`, and to `−1 + ρ` (`= ρ` if `ρ ≥ ω`, a natural number, case 1, otherwise).  If `Γ = 0` then `ρ ≥ 1`.
  By the fourth clause of `t` (second case) and ★1b (`t` is the identity on `Γ, ρ, −1+ρ`), `t(ζ) = ϑᵗ(ν)` with
  (A) `ν = α + (−1 + ρ)` if `Γ = 0`; (B) `ν = Γ + α + ρ` if `Γ > 0`, `Γ^{*α} < α`; (C′) `ν = Γ + ρ` if `Γ^{*α} ≥ α`.
  The components of `ν` are components of `Γ`, `α`, `ρ`, `−1+ρ`; so (i): `Parᵗ(t ζ) ⊆ Parᵗ(t Γ) ∪ {0} ∪ Parᵗ(t ρ)
  ⊆ σ` (S, ★0), and the `ϑᵗ`-subterms of `t(ζ)` are `t(ζ)` (value `ζ ∈ (α, α⁺)`), possibly `α`, and those of `t(Γ),
  t(ρ)` (IH); `t(ζ)` and `ζ` both have one.  (ii): `q(ζ) = ϑ^σ(q ν)` (P, fourth clause; `ν ∈ Tᵗ[σ] ∩ Ω₂`) with
  `q ν = α' + (−1 + q ρ)` (A; `q` fixes natural numbers and keeps `≥ ω`, Π b), `q Γ + α' + q ρ` (B), `q Γ + q ρ` (C′)
  (Π c, ★1a); `q(ζ) ∈ (α', α'⁺)` (Π b, ★1a).  Per C, `q ν = Γ' + ρ'` with `Γ' = q Γ` (`q` maps the `ϑ₁`-terms of `Γ`
  to `ϑ₁`-terms, ★0, additive principal `≥ Ω₁` by L, hence multiples of `Ω₁`; `Γ' = 0 ⇔ Γ = 0`; `Γ' < Δ` from
  `Γ < Δ`, Π b and `q(Δ) = Δ`) and `ρ' = α' + (−1 + q ρ)`, `α' + q ρ`, `q ρ` (countable, Π "intervals").
  The subcase of `t'` (6.2, first part, at `(σ, α')`) matches:
  `Γ' = 0 ⇔ (A)`; for `Γ > 0`, `Γ'^{*σ}` is `0` or the value of a `ϑ^σ`-subterm of `q̂(t Γ)` (★0), these values lie in
  `[α', α'⁺)` (IH (i) for `Γ`, Π b), so `Γ'^{*σ} ≥ α' ⇔ t(Γ)` has a `ϑᵗ`-subterm `⇔ Γ` has a `ϑ^α`-subterm (IH (i))
  `⇔ Γ^{*α} ≥ α` (★0: `P^α₀(Γ)` = its `ϑ^α`-subterms, values `≥ α`).  The three subcases of `t'` give
  `ϑ^{α'}(1 + (−α' + ρ')^{t'})`, `ϑ^{α'}(Γ'^{t'} + (−α' + ρ')^{t'})`, `ϑ^{α'}(Γ'^{t'} + ρ'^{t'})`, where `−α' + ρ' =
  −1 + q ρ` (A), `q ρ` (B), and by ★1b the `^{t'}` are the identity on these values (they lie in `T^σ_{α'⁺}`, IH
  (ii)); so in each case `t'(q̂ t ζ) = ϑ^{α'}(w)` with `w` the term in `T^{α'}` of the ordinal `1 + (−1 + q ρ) = q ρ =
  q ξ` (A, `ρ ≥ 1`) resp. `q Γ + q ρ = q ξ` (B, C′; Π c).  By the IH (ii) for `ξ` and ★1b, that term is `s(ξ)`.  So
  `t'(q̂ t ζ) = ϑ^{α'}(s ξ) = s(ζ)`.
* (★3) **Conclusion.**  Let `y ∈ T^α[σ]`, `α ≤ y < α⁺`, `ζ` its term in `T^α`: `Par^α(ζ) ⊆ σ` and `ζ^{*α} < α⁺`
  (★1c).  By ★1b `t(ζ)` is the term of `y` in `Tᵗ`, so `y ∈ Tᵗ[σ]` (★2 i) and `π_{σ,τ}(y)` is defined; by ★0, ★2 (ii)
  and ★1b, `s(ζ) = t'(q̂(t ζ))` is the term of `q(y)` in `T^{α'}`.  Its parameter leaves are those of `ζ`, so
  `Par^{α'}(q y) = Par^α(y) ⊆ σ` (★0): `π_{σ,τ}(y) ∈ T^{α'}[σ]`.  Finally by ★0, `r'(q y)` is the value of `s(ζ)` with
  `ϑ^σ` written for `ϑ^{α'}`, and `r(y)` the value of `ζ` with `ϑ^σ` written for `ϑ^α`: the same expression.  So
  `π_{σ,α'}(π_{σ,τ}(y)) = π_{σ,α}(y)`. -/
axiom tvSeg_pi {σ τ : Ordinal.{0}} (h : Bases σ τ) {n : ℕ} (hn : 1 ≤ n) {y : Ordinal.{0}}
    (hy : y ∈ TB (Dl τ n) σ) (h1 : Dl τ n ≤ y) (h2 : y < Dp τ n) :
    pi σ τ y ∈ TB (Dl σ n) σ ∧ pi σ (Dl σ n) (pi σ τ y) = pi σ (Dl τ n) y

end Googology.Trans.PoR.InaccPsi.R2
