import Googology.Trans.PoR.InaccPsi.R2.CitedL
import Googology.Trans.PoR.InaccPsi.R2.CitedW

set_option autoImplicit false

/-!
# Cited facts of Wilken 2007, as axioms, ONCE for the arguments `Ω₁·β + η` of every constant level `β < τ`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.

Same conventions as `R2.Cited`, `R2.CitedEv`, `R2.CitedVz`, `R2.CitedLz`, `R2.CitedLt`, `R2.CitedXt` (`Ω₁ = ω₁`,
`Ω₂ = ω₂ = OmTwo`, `Tset τ = Tᵗ = T₀` over the base `τ`, `vt τ = ϑᵗ = ϑ₀`, `lhT τ = lhᵗ`, `lg = logend`, `TB τ σ =
Tᵗ[σ]`, `pi σ τ = π_{σ,τ}`, every base `τ` a countable `ε`-number, `Bases σ τ`: `σ, τ ∈ E`, `σ < τ < Ω₁`).  A
**level** is an ordinal `β < τ`; it is a parameter of `Tᵗ` (Def 3.28: "`Subᵗ_m(α) := {α}` for parameters `α < τ`").
The axioms speak of `vt τ` only at elements of `Tᵗ ∩ Ω₂`: `Ω₁·β + η` with `β < τ`, `η ∈ Tᵗ ∩ Ω₁`, and `Ω₁·τ`.
They replace the per-level axioms of `R2.CitedVz` (`Ω₁·n + η`), `R2.CitedLz` (`Ω₁·ω + η`), `R2.CitedLt`
(`Ω₁·ω + η`, `Ω₁·(ω+1)`), `R2.CitedEv` (`Ω₁ + η`) and `R2.CitedXt` (`Ω₁·ω`): those are proved from these in
`R2.LuOld` (they are not deleted).

Literal texts used below (all of [W07a] unless said otherwise; checked against the PDFs):
* (T) Def 3.22: "`T_m` is defined inductively as follows: • `Ω_m ⊆ T_m` • `ξ, η ∈ T_m ⇒ ξ + η ∈ T_m`
  • `ξ ∈ T_m ∩ Ω_{k+2} ⇒ ϑ_k(ξ) ∈ T_m` for `k ≥ m`."  Convention 3.25: "we will indicate this explicitly in
  writing `ϑᵗ` and `Tᵗ` instead of `ϑ₀` and `T₀`."
* (Θ) Theorem 3.23: "For `m < ω` we have `T_m = ⋃_{n>m} Tⁿ_m` and `T_m ∩ Ω_{m+1} = θ_m = sup_{n≥m} ϑ_m(⋯(ϑ_n(0))⋯)`"
  (so `Tᵗ ∩ Ω₁` is an initial segment of the ordinals).
* (U) Remark after Cor 3.24: "each `T_m` again gives rise to a notation system with parameters from `Ω_m` that
  provides a unique term for every ordinal which is element of some `Tⁿ_m` where `n > m` (again refining the
  clause for ordinal addition as we did for the systems `Tⁿ_m`)".  §2: "We write `ξ =ANF ξ₁ + ⋯ + ξₙ` if
  `ξ₁, …, ξₙ ∈ P`, `ξ₁ ≥ ⋯ ≥ ξₙ` (`ξ` given in additive normal form).  For convenience we also write
  `ξ =NF η + ρ` provided `η =ANF η₁ + ⋯ + ηₙ` for some `η₁, …, ηₙ`, and `ηₙ ≥ ρ ∈ P`."
* (Z) Remark after Def 3.1: "Note that we have `ϑⁿ_m(0) = Ω_m` for `m < n`" (so `ϑ₁(0) = Ω₁`); proof of
  Lemma 3.27: "We have `ϑ₀(0) = τ`".
* (S) Def 3.28: "`Subᵗ_m(α) := {α}` for parameters `α < τ`; `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ) ∪ Subᵗ_m(η)` for
  `ξ, η ∈ Tᵗ` s.t. `α =NF ξ + η > τ`; `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ)` if `k ≥ m` (`{α}` if `k < m`) for
  `α = ϑ_k(ξ)` where `ξ ∈ Tᵗ ∩ Ω_{k+2}`.  We define the additive principal parts of level `m` of `α ∈ Tᵗ` by
  `P_m(α) := Subᵗ_m(α) ∩ P ∩ [Ω_m, Ω_{m+1})` and `α^{*m} := max(P_m(α) ∪ {0})`.  The set of parameters `< τ` used
  in the unique term denoting some `α ∈ Tᵗ` is denoted by `Parᵗ(α) := Subᵗ₀(α) ∩ τ`."  Convention 3.29: "instead
  of `*₀` we will also write `*`".
* (L) Lemma 3.30: "For `m < ω` the function `ϑ_m ↾ Tᵗ ∩ Ω_{m+2}` is 1-1 and has values in `P ∩ [Ω_m, Ω_{m+1})`.
  Let `α, γ ∈ Tᵗ ∩ Ω_{m+2}`.  Then `α^{*m} < ϑ_m(α)` and
  `ϑ_m(α) < ϑ_m(γ) ⇔ α < γ ∧ α^{*m} < ϑ_m(γ) ∨ ϑ_m(α) ≤ γ^{*m}`."
* (C) Convention 4.1: "Given a term `α = ϑᵗ(ξ) ∈ Tᵗ` we introduce the notational convention that
  `α = ϑᵗ(Δ + η)` automatically means that `ξ = Δ + η` is a decomposition such that `Ω₁ | Δ` and `η < Ω₁`. …
  In a situation where some `α = ϑᵗ(Δ + η)` is fixed, we will write `α⁺` to denote the ordinal `ϑᵗ(Δ + η + 1)`."
* (W) Def 3.4: "Let `α ↦ ω̄_α` be the enumeration function of the additive principle numbers which are not epsilon
  numbers."  Lemma 4.2: "For any `m < ω` and any `α < Ω_{m+1}` we have `ϑ_m(1 + α) = ω̄_{Ω_m+α}`" (proof: "for
  `m = 0` by convention we have `Ω₀ = τ` and `ϑ₀ = ϑᵗ`").
* (E) Lemma 4.3: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ`.  Then `τ < α ∈ E ⇔ Δ > 0`."
* (G) Def 4.11: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ` such that `α > τ` be given.  We define `ζᵗ_α := logend(η)` if
  `η < sup_{σ<η} ϑᵗ(Δ + σ)`, `0` otherwise."
* (LOC) Def 4.6: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ`, `α ≥ τ`.  We define a finite sequence of ordinals as follows.  Set
  `α₀ := τ`.  Suppose that `αₙ` is already defined and `αₙ < α`.  Let `αₙ₊₁` be the element `ϑᵗ(ξ)` of `Pᵗ(α) −
  (αₙ + 1)` with maximal `ξ`.  This yields a finite sequence `τ = α₀ < ⋯ < αₙ = α` for some `n < ω` which we call the
  `τ`-localization of `α`."  Convention 6.6: "we call the sequence `(α, β₁^{t^α_τ}, …, β_m^{t^α_τ} = β^{t^α_τ})` the
  `α`-localization of `β^{t^α_τ} = β` in `Tᵗ`" (`(α = β₀, …, β_m = β)` the `α`-localization of `β` in `T^α`).
* (D) Def 6.1: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ`.  The restriction of `Tᵗ` to `α`, written as `Tᵗ_α`, is defined by
  `Tᵗ_α := {β ∈ Tᵗ | β^{*τ} < α}`."
* (TR) Lemma 6.3: "We have • `α⁺ = ϑ^α(Δ)`, • the restriction of `t^τ_α` to `Tᵗ_{α⁺}` is the identity, and • the
  restriction of `t^α_τ` to `T^α_{α⁺}` is the identity."
* (I) Def 7.1: "Let `α = ϑᵗ(Δ + η)` where `Δ > 0`.  We define `ι_{τ,α} : Tᵗ_α → T^α` by recursion on the
  definition of `Tᵗ` as follows: • `ι_{τ,α}(ξ) := ξ` if `ξ < α` • `ι_{τ,α}(ξ) := ι_{τ,α}(ξ₁) + ι_{τ,α}(ξ₂)` if
  `ξ =NF ξ₁ + ξ₂ > Ω₁` • `ι_{τ,α}(ξ) := ϑ_k(ι_{τ,α}(η))` if `ξ = ϑ_{k+1}(η)` where `k < ω`.  Note that
  `ι_{τ,α}(ϑ₁(η)) = ϑ^α(ι_{τ,α}(η))`."
* (Λ) Def 7.5: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ` such that `α > τ`.  We define `λᵗ_α := ι_{τ,α}(Δ) + ζᵗ_α` if `α ∈ E`,
  `ζᵗ_α` otherwise."
* (CR) Def 7.15: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ`, `α ≥ τ`, and `(τ = α₀, …, αₙ = α)` be the `τ`-localization of `α`.
  Define `cr(τ, α) := min{i ∈ {1, …, n − 1} | λᵗ_{αᵢ} ≥ α}` if that exists, `n` otherwise."  The remark after it:
  "Therefore we can consistently refer to the critical index of the `α`-localization of `β` in `Tᵗ`, cf.
  Convention 6.6."
* (P) Def 5.1: "Let `τ ∈ E` and `Tᵗ` be the notation system over `τ`.  Further, let `σ ∈ {1} ∪ (E ∩ τ)`.  We define
  `Tᵗ[σ] := {α ∈ Tᵗ | Parᵗ(α) ⊆ σ}` and `π_{σ,τ} : Tᵗ[σ] → Tᵟ` by the following clauses: • `π_{σ,τ}(ξ) := ξ` if
  `ξ < σ` • `π_{σ,τ}(ξ) := π_{σ,τ}(ξ₁) + π_{σ,τ}(ξ₂)` if `ξ =NF ξ₁ + ξ₂ > τ` • `π_{σ,τ}(ξ) := ϑ_k(π_{σ,τ}(η))` if
  `ξ = ϑ_k(η)` for some `k > 0` and `η ∈ Tᵗ[σ] ∩ Ω_{k+2}` • `π_{σ,τ}(ξ) := ϑ^σ(π_{σ,τ}(η))` if `ξ = ϑᵗ(η)` for some
  `η ∈ Tᵗ[σ] ∩ Ω₂`."
* (H) [W07b] Def 4.1: "For `α ∈ Tᵗ ∩ Ω₁` we define an ordinal `lhᵗ(α) ∈ Tᵗ ∩ Ω₁` by recursion on `hᵗ(α)` as
  follows. • `lhᵗ(α) := 0` if `α ≤ τ` • `lhᵗ(α) := α` if `α =NF α₁ + α₂ ≥ τ` • If `α = ϑᵗ(Δ + η) > τ` we set
  `δ := (λᵗ_α)^*`. • `lhᵗ(α) := α + λᵗ_α` if `δ ≤ α`, i.e. `Δ < ϑ₁(1)` • If `δ > α` let `(α = δ₀, …, δ_m = δ)` be
  the `α`-localization of `δ` in `Tᵗ`.  `lhᵗ(α) := lhᵗ(δᵢ) + λᵗ_α` if `i := cr(α, δ) < m`, `lhᵗ(δ) + ρ` where
  `ρ := −δ + λᵗ_α` otherwise."; after it: "Note that `(λᵗ_α)^*` is the maximum additive principal number less than
  or equal to `λᵗ_α`."

Our steps on the levels (used in every docstring below; `β < τ` a level, `η ∈ Tᵗ ∩ Ω₁`):
* (★1) (of `R2.CitedEv`) For `η ∈ Tᵗ ∩ Ω₁`: `η^* ≤ η`, and every additive component of `η` is `< τ` or `≤ η^*`.
* (★p) For `1 ≤ b ≤ τ`: `ϑ₁(b) = Ω₁·ω^b`, and `ϑ₁(0) = Ω₁ = Ω₁·ω⁰` (Z).  By (W) with `m = 1`: `ϑ₁(1 + a) = ω̄_{Ω₁+a}`.
  `(P ∖ E) ∩ Ω₁` has order type `Ω₁` (it lies in `Ω₁`, and `c ↦ ω^{c+1}` maps `Ω₁` strictly increasingly into it), and
  the elements of `P ∖ E` from `Ω₁ = ω^{Ω₁}` on are `ω^{Ω₁+1+a}` (`a < ε_{Ω₁+1}`), so `ω̄_{Ω₁+a} = ω^{Ω₁+1+a} =
  Ω₁·ω^{1+a}`; with `b = 1 + a` (`a = b − 1` for finite `b`, `a = b` for infinite `b`), `ϑ₁(b) = Ω₁·ω^b`.  For `b < τ`,
  `b` is a parameter (T, first clause: `Ω₀ = τ ⊆ T₀`), `b ∈ T₀ ∩ Ω₃`, so `ϑ₁(b) ∈ T₀` (T, third clause, `k = 1 ≥ 0`);
  for `b = τ`, `τ = ϑ₀(0) ∈ T₀` (Z; T, third clause, `k = 0`), so again `ϑ₁(τ) ∈ T₀`.  Subterms (S, third clause,
  `k = 1 ≥ 0`): `Subᵗ₀(ϑ₁(b)) = {ϑ₁(b)} ∪ Subᵗ₀(b)`, with `Subᵗ₀(b) = {b}` for `b < τ` and `Subᵗ₀(τ) = {τ, 0}`.
* (★β) For a level `β < τ` with Cantor normal form `β = ω^{b₁}·k₁ + ⋯ + ω^{bⱼ}·kⱼ` (`b₁ > ⋯ > bⱼ`, all `< τ`):
  `Ω₁·β = Ω₁·ω^{b₁}·k₁ + ⋯ + Ω₁·ω^{bⱼ}·kⱼ`, the `=NF`-sum (§2: the summands `Ω₁·ω^{bᵢ} = ϑ₁(bᵢ)` are additive
  principal and non-increasing) of `k₁ + ⋯ + kⱼ` terms `ϑ₁(bᵢ) ∈ T₀` (★p); so `Ω₁·β ∈ T₀` (T, second clause), and
  `Ω₁·β + η ∈ Tᵗ ∩ Ω₂` (T, second clause; `Ω₁·β + η < Ω₁·τ + Ω₁ < Ω₂`).  Its term (U) is the `=NF`-sum of these
  `ϑ₁`-terms followed by the components of `η` (`η < Ω₁ ≤ Ω₁·ω^{bⱼ}`).  By (S) its `Subᵗ₀` consists of its partial sums
  with at least two summands, the `ϑ₁(bᵢ)`, the parameters `bᵢ < τ`, and the `Subᵗ₀` of the components of `η`.  The
  partial sums with at least two summands are not in `P`, the `ϑ₁(bᵢ)` are `≥ Ω₁`, the `bᵢ` are `< τ`; so
  `P₀(Ω₁·β + η) = P₀(η)` and **`(Ω₁·β + η)^* = η^*`**; in particular `(Ω₁·β)^* = 0`.  For `β = 0` this is trivial.
  `Parᵗ(Ω₁·ω^b) = {b} ∩ τ` for `b < τ` (S).
* (★τ) `Ω₁·τ = Ω₁·ω^τ = ϑ₁(τ) ∈ Tᵗ ∩ Ω₂` (★p, `ω^τ = τ` as `τ ∈ E`), and `P₀(Ω₁·τ) = Subᵗ₀(ϑ₁(τ)) ∩ P ∩ [τ, Ω₁) =
  {Ω₁·τ, τ, 0} ∩ P ∩ [τ, Ω₁) = {τ}` (`τ = ϑ₀(0) ∈ P`), so **`(Ω₁·τ)^* = τ`**.
* (★ι) For `α = ϑᵗ(Ω₁·β + η)` with `1 ≤ β < τ` (or `α = ϑᵗ(Ω₁·τ)`): `Δ := Ω₁·β` (`Δ := Ω₁·τ`) is the `Δ` of (C), `α ∈ Tᵗ`
  (T, third clause), `τ < α ∈ E` (E, `Δ > 0`), and `Δ ∈ Tᵗ_α` (D: `Δ^* = 0 < α`, resp. `τ < α`).  By (I) (second
  clause for the `=NF`-sums `> Ω₁`, the note for `ϑ₁(bᵢ)`, first clause for `bᵢ < α`): `ι_{τ,α}(Δ) = ϑ^α(b₁)·k₁ + ⋯ +
  ϑ^α(bⱼ)·kⱼ`, and `ϑ^α(b) = α·ω^b` (for `b = 0`: `ϑ^α(0) = α`, Z at the base `α`; for `b ≥ 1`: (W) at the base `α`
  (`m = 0`, `Ω₀ = α`), `ϑ^α(1 + a) = ω̄_{α+a} = ω^{α+1+a}`, as `(P ∖ E) ∩ α` has order type `α`); so **`ι_{τ,α}(Ω₁·β) =
  α·β`** (and `ι_{τ,α}(Ω₁·τ) = ϑ^α(τ) = α·ω^τ = α·τ`, `τ < α`).  This agrees with the proof of [W07a] Lemma 4.3 quoted in
  `R2.CitedLt` ("`λᵗ_α = α·ξ` for `ξ > 0` such that `Δ = Ω·ξ`" when `ζᵗ_α = 0`).
* (★ζ) `ζᵗ_α = luZeta τ β η` (G): `η < sup_{σ<η} ϑᵗ(Ω₁·β + σ)` holds iff `η < ϑᵗ(Ω₁·β + σ)` for some `σ < η` (each
  `σ < η` lies in `Tᵗ` by Θ, so `ϑᵗ(Ω₁·β + σ)` is a term by ★β and T; a supremum exceeds `η` iff one of its members
  does).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- The regular successor cardinal Ω₂ = ω₂. -/
noncomputable def OmTwo : Ordinal.{0} := Ordinal.omega 2

open Classical in
/-- **`ζᵗ_α` of [W07a] Def 4.11** for `α = ϑᵗ(Ω₁·β + η)` (step ★ζ of the module docstring): `logend(η)` if
`η < ϑᵗ(Ω₁·β + σ)` for some `σ < η`, else `0`. -/
noncomputable def luZeta (τ β η : Ordinal.{0}) : Ordinal.{0} :=
  if ∃ σ, σ < η ∧ η < vt τ (Om1 * β + σ) then lg η else 0

/-- **[W07a] Def 3.22, the remark after Def 3.1, Lemma 4.2 (`m = 1`), Def 3.4** (texts T, Z, W): for `b ≤ τ`,
`Ω₁·ω^b ∈ Tᵗ`.

Our steps.  Step ★p of the module docstring: `Ω₁·ω^b = ϑ₁(b)` (for `b = 0`, `Ω₁·ω⁰ = Ω₁ = ϑ₁(0)` by Z), and `ϑ₁(b) ∈ T₀`
by the third clause of T with `k = 1 ≥ m = 0` and `b ∈ T₀ ∩ Ω₃` (`b < τ = Ω₀ ⊆ T₀` by the first clause, or `b = τ =
ϑ₀(0) ∈ T₀`).  For `b = 1` this is the axiom `vzOm1w_T` of `R2.CitedVz`. -/
axiom luOm1_opow_T {τ b : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hb : b ≤ τ) : Om1 * ω ^ b ∈ Tset τ

/-- **[W07a] Def 5.1 (first and third clauses), Def 3.28, Def 3.22, Lemma 4.2 (`m = 1`)** (texts P, S, T, W, Z): for
bases `σ < τ` and `b < σ`, `Ω₁·ω^b ∈ Tᵗ[σ]` and `π_{σ,τ}(Ω₁·ω^b) = Ω₁·ω^b`.

Our steps.  `Ω₁·ω^b = ϑ₁(b)` is a term of `Tᵗ` (★p).  By S (third clause, `k = 1 ≥ 0`) and the first clause (`b < τ` a
parameter), `Subᵗ₀(ϑ₁(b)) = {ϑ₁(b), b}`, so `Parᵗ(Ω₁·ω^b) = {b}` (`Ω₁·ω^b ≥ Ω₁ > τ`), and `{b} ⊆ σ`: `Ω₁·ω^b ∈ Tᵗ[σ]`
(P); also `b ∈ Tᵗ[σ] ∩ Ω₃` (`Parᵗ(b) = {b}`).  P, third clause (`ξ = ϑ₁(b)`, `k = 1 > 0`): `π_{σ,τ}(ϑ₁(b)) =
ϑ₁(π_{σ,τ}(b))`; P, first clause (`b < σ`): `π_{σ,τ}(b) = b`.  So `π_{σ,τ}(Ω₁·ω^b)` is the term `ϑ₁(b)` of `Tᵟ`, and
there too `ϑ₁(b) = Ω₁·ω^b` (★p for the system over `σ`; Z for `b = 0`).  For `b = 1` this is the axiom `xtOm1w_TB` of
`R2.CitedXt`, for `b = 0` the axiom `pi_Om1` of `R2.Cited`. -/
axiom luOm1_opow_TB {σ τ b : Ordinal.{0}} (h : Bases σ τ) (hb : b < σ) :
    Om1 * ω ^ b ∈ TB τ σ ∧ pi σ τ (Om1 * ω ^ b) = Om1 * ω ^ b

/-- **[W07a] Lemma 3.30, the direction `⇐`, with Def 3.28** (texts L, S, U, ★1, ★β): for levels `β', β < τ` and
`η', η ∈ Tᵗ ∩ Ω₁` with `Ω₁·β' + η' < Ω₁·β + η` and `η' < ϑᵗ(Ω₁·β + η)`: `ϑᵗ(Ω₁·β' + η') < ϑᵗ(Ω₁·β + η)`.

Our steps.  `α := Ω₁·β' + η'` and `γ := Ω₁·β + η` lie in `Tᵗ ∩ Ω₂` (★β), and `α < γ`.  By ★β and ★1,
`α^* = η'^* ≤ η' < ϑ₀(γ)`.  So the first disjunct of the right side of Lemma 3.30 (`m = 0`) holds:
`α < γ ∧ α^* < ϑ₀(γ)`, and `ϑ₀(α) < ϑ₀(γ)`.  (The axioms `vzVt_lt`, `vzVt_lt_w`, `lzVt_lt_w`, `lzVt_lt_ww`,
`ltVt_lt_w1`, `vt_Om1_add_lt` are its cases `β', β ∈ {m, n, ω, ω + 1}`.) -/
axiom luVt_lt {τ β' η' β η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hβ' : β' < τ) (hη' : η' ∈ Tset τ)
    (hη'1 : η' < Om1) (hβ : β < τ) (hη : η ∈ Tset τ) (hη1 : η < Om1)
    (hlt : Om1 * β' + η' < Om1 * β + η) (h : η' < vt τ (Om1 * β + η)) :
    vt τ (Om1 * β' + η') < vt τ (Om1 * β + η)

/-- **[W07a] Lemma 3.30, the direction `⇐`, at `γ = Ω₁·τ`, with Def 3.28** (texts L, S, ★1, ★β, ★τ): for a level
`β' < τ` and `η' ∈ Tᵗ ∩ Ω₁` with `η' < ϑᵗ(Ω₁·τ)`: `ϑᵗ(Ω₁·β' + η') < ϑᵗ(Ω₁·τ)`.

Our steps.  `α := Ω₁·β' + η' ∈ Tᵗ ∩ Ω₂` (★β) and `γ := Ω₁·τ ∈ Tᵗ ∩ Ω₂` (★τ); `α < Ω₁·(β' + 1) ≤ Ω₁·τ = γ` (`η' < Ω₁`,
`β' + 1 < τ`).  By ★β and ★1, `α^* = η'^* ≤ η' < ϑ₀(γ)`.  So the first disjunct of the right side of Lemma 3.30
(`m = 0`) holds and `ϑ₀(α) < ϑ₀(γ)`. -/
axiom luVt_lt_top {τ β' η' : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hβ' : β' < τ) (hη' : η' ∈ Tset τ)
    (hη'1 : η' < Om1) (h : η' < vt τ (Om1 * τ)) : vt τ (Om1 * β' + η') < vt τ (Om1 * τ)

/-- **[W07a] Lemma 3.30, the direction `⇒`, with Def 3.28** (texts L, S, ★1, ★β): for `ξ ∈ Tᵗ ∩ Ω₂`, a level
`β < τ` and `η ∈ Tᵗ ∩ Ω₁` with `η < ϑᵗ(ξ)`: `ϑᵗ(ξ) < ϑᵗ(Ω₁·β + η)` implies `ξ < Ω₁·β + η`.

Our steps.  `γ := Ω₁·β + η ∈ Tᵗ ∩ Ω₂` (★β).  By ★β and ★1, `γ^* = η^* ≤ η < ϑᵗ(ξ)`.  Lemma 3.30 with `m = 0`,
`α = ξ`: `ϑ₀(ξ) < ϑ₀(γ)` gives `ξ < γ ∧ ξ^* < ϑ₀(γ)` or `ϑ₀(ξ) ≤ γ^*`; the second is impossible.  So `ξ < γ`.  (The
axioms `vzLt_of_vt_lt`, `vzLt_of_vt_lt_w`, `lzLt_of_vt_lt_ww`, `ltLt_of_vt_lt_w1`, `vt_lt_Om1_add` are its cases
`β ∈ {n, ω, ω + 1, 1}`.) -/
axiom luLt_of_vt_lt {τ ξ β η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hξ : ξ ∈ Tset τ) (hξ2 : ξ < OmTwo)
    (hβ : β < τ) (hη : η ∈ Tset τ) (hη1 : η < Om1) (hηξ : η < vt τ ξ)
    (h : vt τ ξ < vt τ (Om1 * β + η)) : ξ < Om1 * β + η

/-- **[W07a] Lemma 3.30, the direction `⇒`, at `γ = Ω₁·τ`, with Def 3.28** (texts L, S, ★τ): for `ξ ∈ Tᵗ ∩ Ω₂` with
`τ < ϑᵗ(ξ)`: `ϑᵗ(ξ) < ϑᵗ(Ω₁·τ)` implies `ξ < Ω₁·τ`.

Our steps.  `γ := Ω₁·τ ∈ Tᵗ ∩ Ω₂` and `γ^* = τ` (★τ).  Lemma 3.30 (`m = 0`, `α = ξ`): `ϑ₀(ξ) < ϑ₀(γ)` gives
`ξ < γ ∧ ξ^* < ϑ₀(γ)` or `ϑ₀(ξ) ≤ γ^* = τ`; the second is excluded by `τ < ϑ₀(ξ)`.  So `ξ < γ`. -/
axiom luLt_of_vt_lt_top {τ ξ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hξ : ξ ∈ Tset τ) (hξ2 : ξ < OmTwo)
    (hτξ : τ < vt τ ξ) (h : vt τ ξ < vt τ (Om1 * τ)) : ξ < Om1 * τ

/-- **[W07a] Lemma 3.30 (`α^* < ϑ₀(α)`), Lemma 4.3, Def 3.28** (texts L, E, S, ★1, ★β): for a level `1 ≤ β < τ` and
`η ∈ Tᵗ ∩ Ω₁`, `η < ϑᵗ(Ω₁·β + η)`.

Our steps.  `γ := Ω₁·β + η ∈ Tᵗ ∩ Ω₂` (★β).  Lemma 3.30 (`m = 0`): `γ^* < ϑ₀(γ)`, and `γ^* = η^*` (★β).  By Lemma 4.3
(`Δ = Ω₁·β > 0`), `τ < ϑ₀(γ) ∈ E ⊆ P`.  By ★1 every additive component of `η` is `< τ` or `≤ η^*`, so it is
`< ϑ₀(γ)`; as `ϑ₀(γ)` is additive principal, `η < ϑ₀(γ)` (for `η = 0` as `ϑ₀(γ) > τ > 0`).  (The axioms `vzLt_vt_self`,
`ltLt_vt_self_w`, `lt_vt_Om1_add` are its cases `β ∈ {n, ω, 1}`.) -/
axiom luLt_vt_self {τ β η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hβ1 : 1 ≤ β) (hβ : β < τ)
    (hη : η ∈ Tset τ) (hη1 : η < Om1) : η < vt τ (Om1 * β + η)

/-- **[W07b] Def 4.1, the case `δ ≤ α`, with [W07a] Def 7.5, Def 7.1, Def 6.1, Def 4.11, Lemma 4.3, Lemma 4.2,
Def 3.4, Def 3.28, the remark after Def 3.1 and the proof of Lemma 3.27** (texts H, Λ, I, D, G, E, W, S, Z, ★ι, ★ζ):
for a finite level `1 ≤ β < ω` and `η ∈ Tᵗ ∩ Ω₁`, `α := ϑᵗ(Ω₁·β + η)`: `lhᵗ(α) = α + (α·β + ζᵗ_α)`.

Our steps.  `α = ϑᵗ(Δ + η)`, `Δ = Ω₁·β` (C), `α ∈ Tᵗ`, `τ < α ∈ E` (★ι).  `ζᵗ_α = luZeta τ β η` (★ζ).  `ι_{τ,α}(Δ) = α·β`
(★ι), so `λᵗ_α = α·β + ζᵗ_α` (Λ, `α ∈ E`).  `ζᵗ_α ≤ η < α` (`logend(η) ≤ η`; the axiom `luLt_vt_self`), so
`α·β ≤ λᵗ_α < α·β + α = α·(β + 1) < α·ω`; the maximum additive principal number `≤ λᵗ_α` is `α` (the next one after `α`
is `α·ω`): `δ = (λᵗ_α)^* = α ≤ α` (also `Δ = Ω₁·β < Ω₁·ω = ϑ₁(1)`, ★p), so (H) gives `lhᵗ(α) = α + λᵗ_α`.  (The axioms
`vzLhT_fix`, `vzLhT_lim`, `lhT_Om1_add` are its cases with `ζᵗ_α = 0` resp. `logend(η)`.) -/
axiom luLhT_fin {τ β η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hβ1 : 1 ≤ β) (hβω : β < ω)
    (hη : η ∈ Tset τ) (hη1 : η < Om1) :
    lhT τ (vt τ (Om1 * β + η)) = vt τ (Om1 * β + η) + (vt τ (Om1 * β + η) * β + luZeta τ β η)

/-- **[W07b] Def 4.1, the case `δ > α` with `cr(α, δ) = m`, with [W07a] Def 7.5, Def 7.1, Def 6.1, Def 4.11,
Def 4.6, Def 7.15 (and the remark after it), Convention 6.6, Convention 4.1, Lemma 6.3, Lemma 4.2, Lemma 4.3, Lemma 3.30,
Def 3.4, Def 3.28, Def 3.22** (texts H, Λ, I, D, G, LOC, CR, TR, C, W, E, L, S, T, ★ι, ★ζ, ★p): for an infinite level
`ω ≤ β < τ`, `η ∈ Tᵗ ∩ Ω₁`, `α := ϑᵗ(Ω₁·β + η)`, `b₁ := log_ω β` (the leading exponent) and `δ := α·ω^{b₁}`:
`lhᵗ(α) = lhᵗ(δ) + (−δ + (α·β + ζᵗ_α))`.

Our steps.  `α = ϑᵗ(Δ + η)`, `Δ = Ω₁·β`, `α ∈ Tᵗ`, `τ < α ∈ E` (★ι); `ζᵗ_α = luZeta τ β η` (★ζ), `ι_{τ,α}(Δ) = α·β` (★ι),
`λᵗ_α = α·β + ζᵗ_α` (Λ).
* `δ = (λᵗ_α)^*` (H, the note): `β = ω^{b₁}·k₁ + β'` with `1 ≤ k₁ < ω`, `β' < ω^{b₁}`, `b₁ ≥ 1`; `α·β = ω^{α+b₁}·k₁ + α·β'`
  and `ζᵗ_α ≤ η < α` (axiom `luLt_vt_self`), so `ω^{α+b₁} ≤ λᵗ_α < ω^{α+b₁}·(k₁ + 1) < ω^{α+b₁+1}`: the maximum additive
  principal number `≤ λᵗ_α` is `ω^{α+b₁} = α·ω^{b₁}`.  `δ > α` (`b₁ ≥ 1`), so the second branch of (H) applies.
* The `α`-localization of `δ` in `Tᵗ` (LOC, Convention 6.6): in `T^α`, `δ = α·ω^{b₁} = ϑ^α(b₁)` (★ι: (W) at the base
  `α`), and `Sub^α₀(ϑ^α(b₁)) = {ϑ^α(b₁)} ∪ Sub^α₀(b₁) = {δ, b₁}` (S; `b₁ ≤ β < τ < α` is a parameter of `T^α`), so the
  only `ϑ^α`-subterm of `δ` is `δ` itself and the localization is `(α = δ₀, δ₁ = δ)`, `m = 1`.  `δ ∈ T^α_{α⁺}` (D:
  `δ^{*α} = δ < α⁺ = ϑ^α(Δ)` (TR), as `b₁ < Ω₁ ≤ Δ` and `b₁^{*α} = 0`, L), hence `δ^{t^α_τ} = δ` (TR).
* `cr(α, δ)` (CR with `n = m = 1`, and the remark after it): `{1, …, n − 1} = ∅`, so `cr(α, δ) = m`, and (H) gives
  `lhᵗ(α) = lhᵗ(δ) + ρ` with `ρ := −δ + λᵗ_α = −δ + (α·β + ζᵗ_α)`.
For `β = ω` (`δ = α·ω`) this is the computation in the docstrings of the axioms `vzLhT_w`, `ltLhT_w_lim` of `R2.CitedVz`,
`R2.CitedLt`; for `β = ω + 1` that of `ltLhT_w1`.  (The value `lhᵗ(δ)` is not part of this axiom: `R2.LuTh` computes the
`R₁⁺`-reach of `δ ∈ Tᵗ ∩ P ∖ E` from [W07b] Theorem 2.2 and Theorem 5.3, the axioms `le1R_thm22`, `lh_eq_lhT`.) -/
axiom luLhT_inf {τ β η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hβω : ω ≤ β) (hβ : β < τ)
    (hη : η ∈ Tset τ) (hη1 : η < Om1) :
    lhT τ (vt τ (Om1 * β + η)) =
      lhT τ (vt τ (Om1 * β + η) * ω ^ log ω β) +
        ((vt τ (Om1 * β + η) * β + luZeta τ β η) - vt τ (Om1 * β + η) * ω ^ log ω β)

/-- **[W07b] Def 4.1, the case `δ > α` with `cr(α, δ) = m`, at `α = ϑᵗ(Ω₁·τ)`, with [W07a] Def 7.5, Def 7.1, Def 6.1,
Def 4.11, Def 4.6, Def 7.15, Convention 6.6, Lemma 6.3, Lemma 4.2, Lemma 4.3, Lemma 3.30, Def 3.28** (texts H, Λ, I, D,
G, LOC, CR, TR, W, E, L, S, ★τ, ★ι): for `α := ϑᵗ(Ω₁·τ)`, `lhᵗ(α) = lhᵗ(α·τ)`.

Our steps.  `Δ := Ω₁·τ = ϑ₁(τ)`, `α = ϑᵗ(Δ + 0)` (C), `α ∈ Tᵗ`, `τ < α ∈ E` (★τ, E).  `ζᵗ_α = 0` (G: `η = 0`).
`Δ ∈ Tᵗ_α` (D: `Δ^* = τ < α`, ★τ).  `ι_{τ,α}(ϑ₁(τ)) = ϑ^α(ι_{τ,α}(τ)) = ϑ^α(τ)` (I: the note, and the first clause, `τ < α`),
and `ϑ^α(τ) = ϑ^α(1 + τ) = ω̄_{α+τ} = ω^{α+1+τ} = ω^{α+τ} = α·ω^τ = α·τ` ((W) at the base `α`, ★ι; `1 + τ = τ`, `ω^τ = τ`).  So
`λᵗ_α = α·τ` (Λ), and `δ = (λᵗ_α)^* = α·τ > α` (it is additive principal): the second branch of (H).  In `T^α`,
`Sub^α₀(ϑ^α(τ)) = {ϑ^α(τ), τ}` (S; `τ < α` is a parameter of `T^α`), so the `α`-localization of `δ` is `(α, δ)`, `m = 1`
(LOC, Convention 6.6; `δ ∈ T^α_{α⁺}` as `δ < α⁺ = ϑ^α(Δ)`, TR and L with `τ < Ω₁ ≤ Δ`); `cr(α, δ) = m` (CR), and
`ρ = −δ + λᵗ_α = 0`.  So `lhᵗ(α) = lhᵗ(δ) + 0 = lhᵗ(α·τ)`. -/
axiom luLhT_top {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) :
    lhT τ (vt τ (Om1 * τ)) = lhT τ (vt τ (Om1 * τ) * τ)

end Googology.Trans.PoR.InaccPsi.R2
