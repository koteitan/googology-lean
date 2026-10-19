import Googology.Trans.PoR.InaccPsi.R2.CitedEps
import Googology.Trans.PoR.InaccPsi.R2.CitedL
import Googology.Trans.PoR.InaccPsi.R2.EpsQ
import Googology.Trans.PoR.InaccPsi.R2.CitedLu

/-!
# Cited facts of Wilken 2007, as axioms: the terms `ϑᵗ(ξ)` with `ξ < Ω₂`, the base change at them, and the
reach of `ϑᵗ(Ω₁ + η)`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.

Same conventions as `R2.Cited`, `R2.CitedW`, `R2.CitedEps`, `R2.CitedL` (`Ω₁ = ω₁`, `Tset τ = Tᵗ = T₀` over the
base `τ`, `Par τ = Parᵗ`, `vt τ = ϑᵗ = ϑ₀`, `pi σ τ = π_{σ,τ}`, `lhT τ = lhᵗ`, every base `τ` a countable
`ε`-number, so `τ ∈ {1} ∪ E`).  `Ω₂` is "the regular cardinal successor of `Ω₁`" ([W07a] §3: "Let
`τ ∈ {1} ∪ E` and set `Ω₀ := τ`.  Further, let `Ω₁` be an uncountable regular cardinal number greater than
`τ` and `Ωᵢ₊₁` for `i ∈ (0, ω)` be the regular cardinal successor of `Ωᵢ`"); with `Ω₁ = ω₁` this is `ω₂`
(`OmTwo`).  In Lean `vt τ` is a function on all ordinals; the axioms below speak of it only at elements `ξ` of
`Tᵗ` below `Ω₂`, where [W07a] Def 3.22 defines `ϑ₀(ξ)` ("`ξ ∈ T_m ∩ Ω_{k+2} ⇒ ϑ_k(ξ) ∈ T_m` for `k ≥ m`",
`k = m = 0`).

Literal texts used below (all of [W07a] unless said otherwise):
* (T) Def 3.22: "`T_m` is defined inductively as follows: • `Ω_m ⊆ T_m` • `ξ, η ∈ T_m ⇒ ξ + η ∈ T_m`
  • `ξ ∈ T_m ∩ Ω_{k+2} ⇒ ϑ_k(ξ) ∈ T_m` for `k ≥ m`."  Convention 3.25: "we will indicate this explicitly in
  writing `ϑᵗ` and `Tᵗ` instead of `ϑ₀` and `T₀`."
* (U) Remark after Cor 3.24: "each `T_m` again gives rise to a notation system with parameters from `Ω_m`
  that provides a unique term for every ordinal which is element of some `Tⁿ_m` where `n > m` (again
  refining the clause for ordinal addition as we did for the systems `Tⁿ_m`)"; Thm 3.23: "`T_m = ⋃_{n>m}
  Tⁿ_m`".  §2: "we also write `ξ =NF η + ρ` provided `η =ANF η₁ + ⋯ + ηₙ` for some `η₁, …, ηₙ`, and
  `ηₙ ≥ ρ ∈ P`".
* (Z) Remark after Def 3.1: "Note that we have `ϑⁿ_m(0) = Ω_m` for `m < n`"; with Def 3.22 (`ϑ_m(α) :=
  ϑⁿ_m(α)` for `n` large): `ϑ₁(0) = Ω₁`.  Proof of Lemma 3.27: "We have `ϑ₀(0) = τ`".
* (S) Def 3.28: "`Subᵗ_m(α) := {α}` for parameters `α < τ`; `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ) ∪ Subᵗ_m(η)` for
  `ξ, η ∈ Tᵗ` s.t. `α =NF ξ + η > τ`; `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ)` if `k ≥ m` (`{α}` if `k < m`) for
  `α = ϑ_k(ξ)` where `ξ ∈ Tᵗ ∩ Ω_{k+2}`.  We define the additive principal parts of level `m` of `α ∈ Tᵗ` by
  `P_m(α) := Subᵗ_m(α) ∩ P ∩ [Ω_m, Ω_{m+1})` and `α^{*m} := max(P_m(α) ∪ {0})`.  The set of parameters
  `< τ` used in the unique term denoting some `α ∈ Tᵗ` is denoted by `Parᵗ(α) := Subᵗ₀(α) ∩ τ`."
  Convention 3.29: "instead of `*₀` we will also write `*`".  Remark 5 after it: "`Par^{ε₀}(ω + 1) = {ω + 1}`
  and `Par^{ε₀}(ε₀ + ω + 1) = {1, ω}`" (a parameter is atomic; a sum above `τ` is split).
* (L) Lemma 3.30: "For `m < ω` the function `ϑ_m ↾ Tᵗ ∩ Ω_{m+2}` is 1-1 and has values in
  `P ∩ [Ω_m, Ω_{m+1})`.  Let `α, γ ∈ Tᵗ ∩ Ω_{m+2}`.  Then `α^{*m} < ϑ_m(α)` and
  `ϑ_m(α) < ϑ_m(γ) ⇔ α < γ ∧ α^{*m} < ϑ_m(γ) ∨ ϑ_m(α) ≤ γ^{*m}`."
* (C) Convention 4.1: "Given a term `α = ϑᵗ(ξ) ∈ Tᵗ` we introduce the notational convention that
  `α = ϑᵗ(Δ + η)` automatically means that `ξ = Δ + η` is a decomposition such that `Ω₁ | Δ` and
  `η < Ω₁`. … So, `Δ = 0` iff `ξ < Ω₁`".
* (E) Lemma 4.3: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ`.  Then `τ < α ∈ E ⇔ Δ > 0`."
* (G) Def 4.11: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ` such that `α > τ` be given.  We define `ζᵗ_α := logend(η)` if
  `η < sup_{σ<η} ϑᵗ(Δ + σ)`, `0` otherwise."  §2: "`logend(α)` is defined to be `0` if `α = 0` and `αₙ` if
  `α =CNF ω^{α₁} + ⋯ + ω^{αₙ}`."
* (P) Def 5.1: "Let `τ ∈ E` … let `σ ∈ {1} ∪ (E ∩ τ)`.  We define `Tᵗ[σ] := {α ∈ Tᵗ | Parᵗ(α) ⊆ σ}` and
  `π_{σ,τ} : Tᵗ[σ] → Tᵟ` by the following clauses: … • `π_{σ,τ}(ξ) := ϑ^σ(π_{σ,τ}(η))` if `ξ = ϑᵗ(η)` for
  some `η ∈ Tᵗ[σ] ∩ Ω₂`."
* (I) Def 7.1: "Let `α = ϑᵗ(Δ + η)` where `Δ > 0`.  We define `ι_{τ,α} : Tᵗ_α → T^α` by recursion on the
  definition of `Tᵗ` as follows: • `ι_{τ,α}(ξ) := ξ` if `ξ < α` • `ι_{τ,α}(ξ) := ι_{τ,α}(ξ₁) + ι_{τ,α}(ξ₂)` if
  `ξ =NF ξ₁ + ξ₂ > Ω₁` • `ι_{τ,α}(ξ) := ϑ_k(ι_{τ,α}(η))` if `ξ = ϑ_{k+1}(η)` where `k < ω`.  Note that
  `ι_{τ,α}(ϑ₁(η)) = ϑ^α(ι_{τ,α}(η))`."  Def 6.1: "`Tᵗ_α := {β ∈ Tᵗ | β^{*τ} < α}`".
* (Λ) Def 7.5: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ` such that `α > τ`.  We define `λᵗ_α := ι_{τ,α}(Δ) + ζᵗ_α` if
  `α ∈ E`, `ζᵗ_α` otherwise."
* (H) [W07b] Def 4.1: "For `α ∈ Tᵗ ∩ Ω₁` we define an ordinal `lhᵗ(α) ∈ Tᵗ ∩ Ω₁` by recursion on `hᵗ(α)`
  as follows. • `lhᵗ(α) := 0` if `α ≤ τ` • `lhᵗ(α) := α` if `α =NF α₁ + α₂ ≥ τ` • If `α = ϑᵗ(Δ + η) > τ` we
  set `δ := (λᵗ_α)^*`. • `lhᵗ(α) := α + λᵗ_α` if `δ ≤ α`, i.e. `Δ < ϑ₁(1)` • If `δ > α` …"; after it: "Note
  that `(λᵗ_α)^*` is the maximum additive principal number less than or equal to `λᵗ_α`."

Two facts on `α^* = α^{*0}` used below (our steps, from (S), (U), (L)):
* (★1) For `η ∈ Tᵗ ∩ Ω₁`: `η^* ≤ η`, and every additive component of `η` is `< τ` or `≤ η^*`.  By induction on
  the unique term of `η` (U), which below `Ω₁` is a parameter, an `=NF`-sum above `τ`, or `ϑ₀(ξ)` (a term
  `ϑ_k(ξ)` with `k ≥ 1` has a value `≥ Ω_k`, (L)).  A parameter: `Subᵗ₀(η) = {η} ⊆ τ`, so `P₀(η) = ∅`, `η^* = 0`,
  and the components of `η` are `≤ η < τ`.  `η = ϑ₀(ξ)`: `P₀(η) = {η} ∪ P₀(ξ)` ((S), `k = m = 0`), and
  `max(P₀(ξ) ∪ {0}) = ξ^* < ϑ₀(ξ) = η` (L), so `η^* = η`, the only component of `η`.  `η =NF η₁ + η₂ > τ`:
  `η` is not additive principal, so `P₀(η) = P₀(η₁) ∪ P₀(η₂)`, `η^* = max(η₁^*, η₂^*) ≤ max(η₁, η₂) ≤ η`, and the
  components of `η` are those of `η₁` and of `η₂`, each `< τ` or `≤ ηᵢ^* ≤ η^*`.
* (★2) For `η ∈ Tᵗ ∩ Ω₁`: `(Ω₁ + η)^* = η^*`.  Let `η =ANF η₁ + ⋯ + ηₙ`.  The term of `Ω₁ + η` is the `=NF`-sum
  `(⋯((Ω₁ + η₁) + η₂)⋯) + ηₙ` (§2: `Ω₁ ≥ η₁ ≥ ⋯ ≥ ηₙ`, all in `P`), with `Ω₁ = ϑ₁(0)` (Z); so by (S)
  `Subᵗ₀(Ω₁ + η) = {Ω₁ + η₁ + ⋯ + ηⱼ | j ≤ n} ∪ {Ω₁, 0} ∪ ⋃ⱼ Subᵗ₀(ηⱼ)` (`Subᵗ₀(ϑ₁(0)) = {ϑ₁(0)} ∪ Subᵗ₀(0)`,
  `k = 1 ≥ m = 0`), where for `η < τ` the `ηⱼ` are parameters.  The sums and `Ω₁` are `≥ Ω₁` and `0` is not in
  `P`, so `P₀(Ω₁ + η) = ⋃ⱼ P₀(ηⱼ)`.  The same union is `P₀(η)`: for `η < τ` both are empty; for `η ≥ τ` the term
  of `η` is the `=NF`-sum of its components (or the single component), and its partial sums with `≥ 2`
  summands are not in `P`.

The axioms (9 facts, no constant):
1. `Om1_add_T` (T, Z, U, S): for `η ∈ Tᵗ ∩ Ω₁`, `Ω₁ + η ∈ Tᵗ`, and each parameter of `Ω₁ + η` is `0` or `≤` a
   parameter of `η`.
2. `vt_memTwo` (T, L, S): for `ξ ∈ Tᵗ ∩ Ω₂`, `ϑᵗ(ξ) ∈ Tᵗ ∩ P ∩ [τ, Ω₁)` and `Parᵗ(ϑᵗ(ξ)) = Parᵗ(ξ)`.
3. `vt_rep` (T, U, L): an additive principal `x ∈ Tᵗ ∩ [τ, Ω₁)` is `ϑᵗ(ξ)` for some `ξ ∈ Tᵗ ∩ Ω₂`.
4. `vt_E_iff` (E, C): for `ξ ∈ Tᵗ ∩ Ω₂`, `τ < ϑᵗ(ξ) ∈ E ⇔ Ω₁ ≤ ξ`.
5. `vt_lt_Om1_add` (L, ★): for `ξ ∈ Tᵗ ∩ Ω₂` and `η ∈ Tᵗ ∩ Ω₁` with `η < ϑᵗ(ξ)`,
   `ϑᵗ(ξ) < ϑᵗ(Ω₁ + η) ⇒ ξ < Ω₁ + η`.
6. `vt_Om1_add_lt` (L, ★): for `η' < η` in `Tᵗ ∩ Ω₁` with `η' < ϑᵗ(Ω₁ + η)`, `ϑᵗ(Ω₁ + η') < ϑᵗ(Ω₁ + η)`.
7. `lt_vt_Om1_add` (L, E, ★): for `η ∈ Tᵗ ∩ Ω₁`, `η < ϑᵗ(Ω₁ + η)`.
8. `lhT_Om1_add` (H, Λ, I, G, Z, Def 6.1): for `η ∈ Tᵗ ∩ Ω₁`, `η ≠ 0`, with `η < ϑᵗ(Ω₁ + σ)` for some `σ < η`,
   `lhᵗ(ϑᵗ(Ω₁ + η)) = ϑᵗ(Ω₁ + η)·2 + logend(η)`.
9. `pi_vt_two` (P): `π_{σ,τ}(ϑᵗ(ξ)) = ϑ^σ(π_{σ,τ}(ξ))` for `ξ ∈ Tᵗ[σ] ∩ Ω₂` (the fourth clause of Def 5.1 for
   the arguments in `[Ω₁, Ω₂)`; `R2.CitedW.pi_vt` states it for `ξ < Ω₁`).

Consequences (proved in `R2.EvV` and `R2.EvZ`, not axioms): `ϑᵗ(Ω₁ + η) = ε_{τ+1+η}` for every `η` below the
least fixed point of `ε` above `τ` (the remark after Convention 4.1 of [W07a], "It will become clear that the
function `η ↦ ϑᵗ(Δ + η)` where `η < Ω₁`, which is immediately seen to be strictly increasing, enumerates the
ordinals of the interval `(τ, Ω₁)` of the same 'fixed point level' which is indicated by `Δ`", for
`Δ = Ω₁`), the base change of `ε_{ρ+c}`, and the `R₁⁺`-reach `lh(ε_{τ+1+η}) = ε_{τ+1+η}·2 + logend(η)`
([W07b] Theorem 5.3, `lh_eq_lhT`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal


private theorem lu_nat_lt_E {x : Ordinal.{0}} (hx : InE x) (n : ℕ) : (n : Ordinal.{0}) < x :=
  (natCast_lt_omega0 n).trans (omega0_lt_inE hx)

private theorem lu_one_lt_E {x : Ordinal.{0}} (hx : InE x) : (1 : Ordinal.{0}) < x := by
  have hh := lu_nat_lt_E hx 1
  rwa [Nat.cast_one] at hh

private theorem lu_one_cast (η : Ordinal.{0}) : Om1 * 1 + η = Om1 + η := by rw [mul_one]

private theorem lu_zeta_lim {τ β η : Ordinal.{0}}
    (h : ∃ σ, σ < η ∧ η < vt τ (Om1 * β + σ)) : luZeta τ β η = lg η := by
  simp [luZeta, h]

/-- **[W07a] Def 3.22, the remark after Def 3.1, Def 3.28** (texts T, Z, U, S of the module docstring): for
`η ∈ Tᵗ ∩ Ω₁`, `Ω₁ + η ∈ Tᵗ`, and every parameter of `Ω₁ + η` is `0` or at most a parameter of `η`.

Our steps.  Membership: `0 ∈ Ω₀ = τ ⊆ T₀` (first clause), so `ϑ₁(0) ∈ T₀` (third clause, `k = 1 ≥ m = 0`,
`0 ∈ T₀ ∩ Ω₃`), and `ϑ₁(0) = Ω₁` (Z); with `η ∈ T₀`, `Ω₁ + η ∈ T₀` (second clause).  Parameters: by (★2) of the
module docstring, `Subᵗ₀(Ω₁ + η) = {Ω₁ + η₁ + ⋯ + ηⱼ | j ≤ n} ∪ {Ω₁, 0} ∪ ⋃ⱼ Subᵗ₀(ηⱼ)` (`η =ANF η₁ + ⋯ + ηₙ`), so
`Parᵗ(Ω₁ + η) = {0} ∪ ⋃ⱼ (Subᵗ₀(ηⱼ) ∩ τ)`.  For `η < τ` (a parameter, `Parᵗ(η) = {η}`) each `ηⱼ` is a parameter
with `Subᵗ₀(ηⱼ) = {ηⱼ}` and `ηⱼ ≤ η`.  For `η ≥ τ` the term of `η` is the `=NF`-sum of its components (§2), so
`Subᵗ₀(ηⱼ) ⊆ Subᵗ₀(η)` and `Subᵗ₀(ηⱼ) ∩ τ ⊆ Parᵗ(η)`.  In both cases every element of `Parᵗ(Ω₁ + η)` is `0` or
`≤` an element of `Parᵗ(η)`. -/
axiom Om1_add_T {τ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hη : η ∈ Tset τ) (hη1 : η < Om1) :
    Om1 + η ∈ Tset τ ∧ ∀ p ∈ Par τ (Om1 + η), p = 0 ∨ ∃ q ∈ Par τ η, p ≤ q

/-- **[W07a] Def 3.22, Lemma 3.30, Def 3.28** (texts T, L, S): for `ξ ∈ Tᵗ ∩ Ω₂`, `ϑᵗ(ξ) ∈ Tᵗ`, its value
is an additive principal number in `[τ, Ω₁)`, and `Parᵗ(ϑᵗ(ξ)) = Parᵗ(ξ)`.

Our steps.  `ϑ₀(ξ) ∈ T₀` is the third clause of Def 3.22 with `k = m = 0` (`ξ ∈ T₀ ∩ Ω₂`).  Lemma 3.30 with
`m = 0` (`Ω₀ = τ`): the value lies in `P ∩ [Ω₀, Ω₁) = P ∩ [τ, Ω₁)`; `P` (the additive principal numbers,
nonzero) is `Indec` here.  By (S) with `k = m = 0`, `Subᵗ₀(ϑ₀(ξ)) = {ϑ₀(ξ)} ∪ Subᵗ₀(ξ)`, and `ϑ₀(ξ) ≥ τ` is not
in `τ`, so `Parᵗ(ϑ₀(ξ)) = Subᵗ₀(ξ) ∩ τ = Parᵗ(ξ)`.  (For `ξ < Ω₁` this is the axiom `vt_mem` of `R2.CitedW`.) -/
axiom vt_memTwo {τ ξ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hξ : ξ ∈ Tset τ) (hξ2 : ξ < OmTwo) :
    vt τ ξ ∈ Tset τ ∧ τ ≤ vt τ ξ ∧ vt τ ξ < Om1 ∧ Indec (vt τ ξ) ∧ Par τ (vt τ ξ) = Par τ ξ

/-- **[W07a] Def 3.22, the remark after Cor 3.24 and Thm 3.23, Lemma 3.30** (texts T, U, L): an additive
principal `x ∈ Tᵗ` with `τ ≤ x < Ω₁` is `ϑᵗ(ξ)` for some `ξ ∈ Tᵗ ∩ Ω₂`.

Our steps.  By (U) `x` has a unique term built by the three clauses of Def 3.22 (with `+` refined to `=NF`).
Its outermost clause is not the first (`x ≥ τ = Ω₀`, so `x` is not a parameter), not an `=NF`-sum `ξ₁ + ξ₂`
(then `ξ₂ ≤ ` the last summand of `ξ₁`, so `0 < ξ₁, ξ₂ < x` with `ξ₁ + ξ₂ = x`, and `x` would not be additive
principal), and not `ϑ_k(ξ)` with `k ≥ 1` (by Lemma 3.30 its value lies in `[Ω_k, Ω_{k+1})`, so it is
`≥ Ω₁ > x`).  So it is `ϑ₀(ξ)` with `ξ ∈ T₀ ∩ Ω₂` (third clause, `k = m = 0`). -/
axiom vt_rep {τ x : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hxT : x ∈ Tset τ) (hτx : τ ≤ x)
    (hx1 : x < Om1) (hxP : Indec x) : ∃ ξ, ξ ∈ Tset τ ∧ ξ < OmTwo ∧ vt τ ξ = x

/-- **[W07a] Lemma 4.3 with Convention 4.1** (texts E, C): for `ξ ∈ Tᵗ ∩ Ω₂`, `τ < ϑᵗ(ξ) ∈ E` iff
`Ω₁ ≤ ξ`.

Our steps.  `α = ϑᵗ(ξ) ∈ Tᵗ` (Def 3.22, `ξ ∈ Tᵗ ∩ Ω₂`); write `ξ = Δ + η` with `Ω₁ | Δ`, `η < Ω₁`
(Convention 4.1); "`Δ = 0` iff `ξ < Ω₁`", so `Δ > 0` iff `Ω₁ ≤ ξ`, and Lemma 4.3 reads
`τ < α ∈ E ⇔ Ω₁ ≤ ξ`. -/
axiom vt_E_iff {τ ξ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hξ : ξ ∈ Tset τ) (hξ2 : ξ < OmTwo) :
    (τ < vt τ ξ ∧ InE (vt τ ξ)) ↔ Om1 ≤ ξ

/-- **[W07a] Lemma 3.30, the direction `⇒`, with Def 3.28** (texts L, S, ★): for `ξ ∈ Tᵗ ∩ Ω₂` and
`η ∈ Tᵗ ∩ Ω₁` with `η < ϑᵗ(ξ)`, `ϑᵗ(ξ) < ϑᵗ(Ω₁ + η)` implies `ξ < Ω₁ + η`.

Our steps.  `γ := Ω₁ + η ∈ Tᵗ ∩ Ω₂` (axiom `Om1_add_T`; `Ω₁ + η < Ω₁·2 < Ω₂`).  By (★2) and (★1) of the
module docstring, `γ^* = η^* ≤ η < ϑᵗ(ξ)`.  Lemma 3.30 with `m = 0`, `α = ξ`: `ϑ₀(ξ) < ϑ₀(γ)` gives
`ξ < γ ∧ ξ^* < ϑ₀(γ)` or `ϑ₀(ξ) ≤ γ^*`; the second is impossible.  So `ξ < γ`. Proved from `CitedLu`. -/
theorem vt_lt_Om1_add {τ ξ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hξ : ξ ∈ Tset τ)
    (hξ2 : ξ < OmTwo) (hη : η ∈ Tset τ) (hη1 : η < Om1) (hηξ : η < vt τ ξ)
    (h : vt τ ξ < vt τ (Om1 + η)) : ξ < Om1 + η := by
  rw [← lu_one_cast] at h ⊢
  exact luLt_of_vt_lt hτ hτ1 hξ hξ2 (lu_one_lt_E hτ) hη hη1 hηξ h

/-- **[W07a] Lemma 3.30, the direction `⇐`, with Def 3.28** (texts L, S, ★): for `η' < η` in `Tᵗ ∩ Ω₁` with
`η' < ϑᵗ(Ω₁ + η)`, `ϑᵗ(Ω₁ + η') < ϑᵗ(Ω₁ + η)` (the remark after Convention 4.1: "immediately seen to be
strictly increasing").

Our steps.  `α := Ω₁ + η'` and `γ := Ω₁ + η` lie in `Tᵗ ∩ Ω₂` (axiom `Om1_add_T`), and `α < γ`.  By (★2) and
(★1), `α^* = η'^* ≤ η' < ϑ₀(γ)`.  So the first disjunct of the right side of Lemma 3.30 (`m = 0`) holds:
`ϑ₀(α) < ϑ₀(γ)`. Proved from `CitedLu`. -/
theorem vt_Om1_add_lt {τ η' η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hη' : η' ∈ Tset τ)
    (hη : η ∈ Tset τ) (hη1 : η < Om1) (hη'η : η' < η) (h : η' < vt τ (Om1 + η)) :
    vt τ (Om1 + η') < vt τ (Om1 + η) := by
  have h' : η' < vt τ (Om1 * 1 + η) := by rw [lu_one_cast]; exact h
  have := luVt_lt hτ hτ1 (lu_one_lt_E hτ) hη' (hη'η.trans hη1) (lu_one_lt_E hτ) hη hη1
    ((add_lt_add_iff_left _).2 hη'η) h'
  rwa [lu_one_cast, lu_one_cast] at this

/-- **[W07a] Lemma 3.30, Lemma 4.3, Def 3.28** (texts L, E, S, ★): for `η ∈ Tᵗ ∩ Ω₁`, `η < ϑᵗ(Ω₁ + η)`.

Our steps.  `γ := Ω₁ + η ∈ Tᵗ ∩ Ω₂` (axiom `Om1_add_T`).  Lemma 3.30: `γ^* < ϑ₀(γ)`, and `γ^* = η^*` (★2).  By
Lemma 4.3 (`γ ≥ Ω₁`, so `Δ > 0`), `τ < ϑ₀(γ) ∈ E ⊆ P`.  By (★1) every additive component of `η` is `< τ` or
`≤ η^*`, so it is `< ϑ₀(γ)`; as `ϑ₀(γ)` is additive principal, `η < ϑ₀(γ)` (for `η = 0` as `ϑ₀(γ) > τ > 0`). Proved from `CitedLu`. -/
theorem lt_vt_Om1_add {τ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hη : η ∈ Tset τ) (hη1 : η < Om1) :
    η < vt τ (Om1 + η) := by
  rw [← lu_one_cast]; exact luLt_vt_self hτ hτ1 le_rfl (lu_one_lt_E hτ) hη hη1

/-- **[W07b] Def 4.1 with [W07a] Def 7.5, Def 7.1, Def 6.1, Def 4.11, the remark after Def 3.1 and the
proof of Lemma 3.27** (texts H, Λ, I, G, Z): for `η ∈ Tᵗ ∩ Ω₁`, `η ≠ 0`, with `η < ϑᵗ(Ω₁ + σ)` for some
`σ < η`, and `α := ϑᵗ(Ω₁ + η)`: `lhᵗ(α) = α·2 + logend(η)` (`logend = lg`, see `R2.CitedW`; `η ≠ 0`).

Our steps.  `α = ϑᵗ(Δ + η)` with `Δ = Ω₁` (`Ω₁ | Ω₁`, `η < Ω₁`: Convention 4.1); `α ∈ Tᵗ` (axioms `Om1_add_T`,
`vt_memTwo`) and `τ < α ∈ E` (Lemma 4.3, `Δ > 0`).
* `ζᵗ_α` (G): `η < ϑᵗ(Ω₁ + σ) ≤ sup_{σ'<η} ϑᵗ(Δ + σ')` for the given `σ < η`; hence `ζᵗ_α = logend(η)`.
* `ι_{τ,α}(Δ)` (I): `Δ = Ω₁ = ϑ₁(0)` (Z), and `Δ ∈ Tᵗ_α` (`Δ^* = max(P₀(ϑ₁(0)) ∪ {0}) = 0 < α`: `Subᵗ₀(ϑ₁(0)) =
  {Ω₁, 0}`, Def 6.1); by the note after Def 7.1, `ι_{τ,α}(ϑ₁(0)) = ϑ^α(ι_{τ,α}(0))`, and `ι_{τ,α}(0) = 0` (first
  clause, `0 < α`); `ϑ^α(0) = α` (proof of Lemma 3.27 at the base `α`: "We have `ϑ₀(0) = τ`").  So
  `ι_{τ,α}(Δ) = α`.
* `λᵗ_α` (Λ): `α ∈ E`, so `λᵗ_α = ι_{τ,α}(Δ) + ζᵗ_α = α + logend(η)`.
* `lhᵗ(α)` (H): `α = ϑᵗ(Δ + η) > τ`; `logend(η) ≤ η < α` (axiom `lt_vt_Om1_add`), so the maximum additive
  principal number `≤ α + logend(η)` is `α` (`α ∈ P`, and `α·2 > α + logend(η)`): `δ = (λᵗ_α)^* = α ≤ α` (also
  `Δ = Ω₁ = ϑ₁(0) < ϑ₁(1)`), so `lhᵗ(α) = α + λᵗ_α = α + α + logend(η) = α·2 + logend(η)`. Proved from `CitedLu`. -/
theorem lhT_Om1_add {τ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hη : η ∈ Tset τ) (hη1 : η < Om1)
    (_hη0 : η ≠ 0) (hlim : ∃ σ, σ < η ∧ η < vt τ (Om1 + σ)) :
    lhT τ (vt τ (Om1 + η)) = vt τ (Om1 + η) * 2 + lg η := by
  have hlim' : ∃ σ, σ < η ∧ η < vt τ (Om1 * 1 + σ) := by
    obtain ⟨σ, h1, h2⟩ := hlim; exact ⟨σ, h1, by rw [lu_one_cast]; exact h2⟩
  have h := luLhT_fin hτ hτ1 le_rfl one_lt_omega0 hη hη1
  rw [lu_zeta_lim hlim', lu_one_cast, mul_one, ← add_assoc, ← mul_two_eq] at h
  exact h

/-- **[W07a] Def 5.1, fourth clause** (text P): `π_{σ,τ}(ϑᵗ(ξ)) = ϑ^σ(π_{σ,τ}(ξ))` for `ξ ∈ Tᵗ[σ] ∩ Ω₂`.
The clause is literally for every `η ∈ Tᵗ[σ] ∩ Ω₂`; the axiom `pi_vt` of `R2.CitedW` is its case `ξ < Ω₁`.
Here `σ, τ` satisfy `Bases σ τ` (`σ ∈ E ∩ τ`, `τ ∈ E`, `τ < Ω₁`), as in Def 5.1. -/
axiom pi_vt_two {σ τ ξ : Ordinal.{0}} (h : Bases σ τ) (hξ : ξ ∈ TB τ σ) (hξ2 : ξ < OmTwo) :
    pi σ τ (vt τ ξ) = vt σ (pi σ τ ξ)

end Googology.Trans.PoR.InaccPsi.R2
