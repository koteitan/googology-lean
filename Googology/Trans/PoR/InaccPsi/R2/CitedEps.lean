import Googology.Trans.PoR.InaccPsi.R2.CitedW
import Googology.Trans.PoR.InaccPsi.R2.OTerm

/-!
# Cited facts of Wilken 2007, as axioms: the terms `ϑᵗ(Ω₁ + k)`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

Same conventions as `R2.Cited` and `R2.CitedW` (`Ω₁ = ω₁`, `Tset τ = Tᵗ`, `Par τ = Parᵗ`, `vt τ = ϑᵗ`,
`Dl τ n = ϑ₀(ϑ₁(⋯ϑₙ(0)⋯))` over `τ`, every base `τ` a countable `ε`-number).  `eN x` (`R2.OTerm`) is the
least `ε`-number above `x`; in the notation of [W07a] §2 this is `x^E` ("`α^P` for example denotes the
least additive principal number strictly greater than `α`"; `E` is the class of `ε`-numbers).
`vt τ` is a function on all ordinals in Lean; [W07a] Def 3.22 defines `ϑ₀ = ϑᵗ` on `θ₁`, which contains
`Ω₁ + k` (`k < ω`, see 2. below).  The axioms of `R2.CitedW` are stated only for countable arguments;
the axioms below are the only ones about `vt τ` at an argument `≥ Ω₁`.

1. `Dl_one_eq`: `ϑᵗ(ϑ₁(0)) = τ^E`, i.e. `Dl τ 1 = eN τ`.  Literal texts:
   * [W07a] Corollary 3.24: "For every `k ≥ m` we have `sup(T_m ∩ Ω_{k+2}) = θ_{k+1}`.  For `m < n` we
     have `Tⁿ_m ∩ Ω_{m+1} = θⁿ_m = ϑ_m(⋯(ϑ_n(0))⋯)`."  With `m = 0`, `n = 1`: `θ¹₀ = ϑ₀(ϑ₁(0))`, which
     is `Dl τ 1` (the term of [W07a] Lemma 3.27, the definition of `Dl` in `R2.Cited`).
   * [W07a] proof of Lemma 3.20: "First of all, note that we have `θⁿ_n = θⁿ_{n−1} = Ω^E_{n−1} <
     Ω^E_n = θ^{n+1}_n` by Lemma 3.5."  With `n = 1`: `θ¹₀ = Ω^E₀`, and `Ω₀ := τ` ([W07a] §3: "Let
     `τ ∈ {1} ∪ E` and set `Ω₀ := τ`").
   Our steps: the two equations give `Dl τ 1 = θ¹₀ = τ^E = eN τ`.  The hypotheses: `τ ∈ E` (so
   `τ ∈ {1} ∪ E`), and `Ω₁ = ω₁` is an uncountable regular cardinal above the countable `τ` (the
   setting of [W07a] §3, as in `R2.Cited`).  (The same value follows from [W07a] Def 3.13 with `n = 1`,
   `θ¹₀ = sup_{k<ω} (ϑ¹₀)^{(k)}(0)`, and Lemma 3.5, `ϑ¹₀(1 + α) = ω̄_{τ+α}`: the iterates are
   `τ < ω̄_{τ+τ} < ⋯` with supremum `τ^E`; this is the reason "by Lemma 3.5" given in the text.)
   It agrees with the axiom `Dl_E` of `R2.Cited` (`τ < Dl τ 1 ∈ E`, [W07a] Lemma 4.3).
2. `vt_Om1_mem`: `ϑᵗ(Ω₁ + k) ∈ Tᵗ`, `Parᵗ(ϑᵗ(Ω₁ + k)) ⊆ {0, 1}`, and `ϑᵗ(Ω₁) = Dl τ 1`.  Literal texts:
   * [W07a] remark after Def 3.1: "Note that we have `ϑⁿ_m(0) = Ω_m` for `m < n`"; with Def 3.22
     ("`ϑ_m(α) := ϑⁿ_m(α)` for `α < θⁿ_{m+1}` where `n > m` is large enough") and `0 < θⁿ₂`: `ϑ₁(0) = Ω₁`.
   * [W07a] Def 3.22, the inductive definition of `T_m` (here `m = 0`, `T₀ = Tᵗ`, Convention 3.25):
     "`Ω_m ⊆ T_m`; `ξ, η ∈ T_m ⇒ ξ + η ∈ T_m`; `ξ ∈ T_m ∩ Ω_{k+2} ⇒ ϑ_k(ξ) ∈ T_m` for `k ≥ m`."
   * [W07a] §2: "we also write `ξ =NF η + ρ` provided `η =ANF η₁ + ⋯ + ηₙ` for some `η₁, …, ηₙ`, and
     `ηₙ ≥ ρ ∈ P`".
   * [W07a] Def 3.28: "`Subᵗ_m(α) := {α}` for parameters `α < τ`; `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ) ∪
     Subᵗ_m(η)` for `ξ, η ∈ Tᵗ` s.t. `α =NF ξ + η > τ`; `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ)` if `k ≥ m`
     (`{α}` if `k < m`) for `α = ϑ_k(ξ)` where `ξ ∈ Tᵗ ∩ Ω_{k+2}`"; "`Parᵗ(α) := Subᵗ₀(α) ∩ τ`".
   * [W07a] Lemma 3.30: "For `m < ω` the function `ϑ_m ↾ Tᵗ ∩ Ω_{m+2}` is 1-1 and has values in
     `P ∩ [Ω_m, Ω_{m+1})`."
   Our steps: `0 ∈ Ω₀ = τ ⊆ T₀`, so `ϑ₁(0) = Ω₁ ∈ T₀` (third clause, `k = 1`, `0 ∈ T₀ ∩ Ω₃`); `1 < ω < τ`,
   so `1 ∈ T₀`; so `Ω₁ + k ∈ T₀` (second clause, `k` times) and `Ω₁ + k < Ω₂`; so `ϑ₀(Ω₁ + k) ∈ T₀`
   (third clause, `k = m = 0`).  Subterms: `Sub₀(ϑ₀(Ω₁ + k)) = {ϑ₀(Ω₁ + k)} ∪ Sub₀(Ω₁ + k)`;
   `Sub₀(Ω₁) = Sub₀(ϑ₁(0)) = {ϑ₁(0)} ∪ Sub₀(0) = {Ω₁, 0}` (`k = 1 ≥ m = 0`; `0 < τ` is a parameter);
   for `j < k`, `Ω₁ + (j + 1) =NF (Ω₁ + j) + 1 > τ` (`Ω₁ + j =ANF Ω₁ + 1 + ⋯ + 1`, last summand
   `≥ 1 ∈ P`), so `Sub₀(Ω₁ + (j + 1)) = {Ω₁ + (j + 1)} ∪ Sub₀(Ω₁ + j) ∪ {1}`.  The members below `τ` are
   `0` and (for `k > 0`) `1` (`ϑ₀(Ω₁ + k) ≥ Ω₀ = τ` by Lemma 3.30, and the `Ω₁ + j` are `≥ Ω₁ > τ`):
   `Par ⊆ {0, 1}`.  Finally `ϑᵗ(Ω₁) = ϑ₀(ϑ₁(0)) = Dl τ 1` (the term of Lemma 3.27).
3. `vt_Om1_succ`: `ϑᵗ(Ω₁ + (k + 1)) = ϑ^α(Ω₁)` for `α = ϑᵗ(Ω₁ + k)`, i.e. `= Dl α 1`.  Literal texts:
   * [W07a] Def 6.1/6.2 fix "`α = ϑᵗ(Δ + η) ∈ Tᵗ` where `Δ > 0`"; Convention 4.1: "`α = ϑᵗ(Δ + η)`
     automatically means that `ξ = Δ + η` is a decomposition such that `Ω₁ | Δ` and `η < Ω₁`", and "we
     will write `α⁺` to denote the ordinal `ϑᵗ(Δ + η + 1)`".
   * [W07a] Lemma 6.3: "We have `α⁺ = ϑ^α(Δ)`, ..."; before it: "`t^α_τ` will be shown to work correctly
     on `ϑ^α(Δ) + 1`", and in Def 6.2 "(regarding `Δ` to be represented in `T^α`)".
   * [W07a] Lemma 4.3: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ`.  Then `τ < α ∈ E ⇔ Δ > 0`."
   Our steps: `α = ϑᵗ(Ω₁ + k) ∈ Tᵗ` (2.), with `Δ = Ω₁` (`Ω₁ | Ω₁`, `Δ > 0`) and `η = k < Ω₁`.  By
   Lemma 4.3 `α` is an `ε`-number `> τ` (so `T^α` is defined, `α ∈ {1} ∪ E`), and `α < Ω₁` (Lemma 3.30).
   `α⁺ = ϑᵗ(Ω₁ + k + 1)`, and `Δ = Ω₁` is represented in `T^α` by `ϑ₁(0)`, so Lemma 6.3 reads
   `ϑᵗ(Ω₁ + (k + 1)) = ϑ^α(ϑ₁(0)) = Dl α 1`.  For `k = 0` this is the axiom `Dp_spec` of `R2.Cited`
   (`ϑᵗ(Δ₁ + 1) = Dl (Dl τ 1) 1`).

Consequence (proved in `R2.EpsK`, not an axiom): `ϑᵗ(Ω₁ + k) = ε_{τ+1+k}`, by induction on `k` from 1.
and 3. (each step `Dl α 1 = eN α` is 1. at the base `α`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- **[W07a] Corollary 3.24** (`m = 0`, `n = 1`: `θ¹₀ = ϑ₀(ϑ₁(0))`) and **the proof of Lemma 3.20**
(`θ¹₀ = Ω^E₀`, `Ω₀ = τ`): `ϑᵗ(ϑ₁(0)) = τ^E`, the least `ε`-number above `τ`. -/
axiom Dl_one_eq {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) : Dl τ 1 = eN τ

/-- **[W07a] Def 3.22** (the inductive definition of `T₀`), §2 (`=NF`), **Def 3.28** (`Sub`, `Par`), **Lemma 3.30**
(values of `ϑ₀` in `[τ, Ω₁)`) and the remark after **Def 3.1** (`ϑ₁(0) = Ω₁`): for `k < ω`,
`ϑᵗ(Ω₁ + k) ∈ Tᵗ` with `Parᵗ(ϑᵗ(Ω₁ + k)) ⊆ {0, 1}`, and `ϑᵗ(Ω₁) = ϑ₀(ϑ₁(0)) = Dl τ 1`. -/
axiom vt_Om1_mem {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (k : ℕ) :
    vt τ (Om1 + (k : Ordinal.{0})) ∈ Tset τ ∧
      ↑(Par τ (vt τ (Om1 + (k : Ordinal.{0})))) ⊆ ({0, 1} : Set Ordinal.{0}) ∧
      vt τ Om1 = Dl τ 1

/-- **[W07a] Lemma 6.3** (`α⁺ = ϑ^α(Δ)`), with Convention 4.1 (`α⁺ = ϑᵗ(Δ + η + 1)`) and Lemma 4.3, for
`α = ϑᵗ(Ω₁ + k)` (`Δ = Ω₁`, `η = k`): `ϑᵗ(Ω₁ + (k + 1)) = ϑ^α(ϑ₁(0)) = Dl α 1`. -/
axiom vt_Om1_succ {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (k : ℕ) :
    vt τ (Om1 + ((k + 1 : ℕ) : Ordinal.{0})) = Dl (vt τ (Om1 + (k : Ordinal.{0}))) 1

end Googology.Trans.PoR.InaccPsi.R2
