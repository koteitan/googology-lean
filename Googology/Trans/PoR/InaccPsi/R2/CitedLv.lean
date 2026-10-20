import Googology.Trans.PoR.InaccPsi.R2.CitedLu

set_option autoImplicit false

/-!
# Cited facts of Wilken 2007, as axioms, ONCE for the arguments `Ω₁·β + η` of every level `τ ≤ β < Ω₁`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.

Same conventions as `R2.CitedLu` (`Ω₁ = Om1`, `Ω₂ = OmTwo`, `Tset τ = Tᵗ`, `vt τ = ϑᵗ`, `lhT τ = lhᵗ`, `lg = logend`,
`TB τ σ = Tᵗ[σ]`, `pi σ τ = π_{σ,τ}`).  `R2.CitedLu` states the facts for the constant levels `β < τ`; here the level
`β` is itself a term: `β ∈ Tᵗ` with `τ ≤ β < Ω₁` (by Theorem 3.23 quoted in `R2.CitedLu`, text Θ, `Tᵗ ∩ Ω₁` is an
initial segment, so this is every `β` below the countable ordinal `Tᵗ ∩ Ω₁`).

Literal texts used below (all of [W07a] unless said otherwise; the full quotations of the texts T, Θ, U, Z, S, L, C,
W, E, G, LOC, D, TR, I, Λ, CR, P, H are in the module docstring of `R2.CitedLu`):
* (T) Def 3.22: "`ξ, η ∈ T_m ⇒ ξ + η ∈ T_m`" and "`ξ ∈ T_m ∩ Ω_{k+2} ⇒ ϑ_k(ξ) ∈ T_m` for `k ≥ m`."
* (W) Lemma 4.2: "For any `m < ω` and any `α < Ω_{m+1}` we have `ϑ_m(1 + α) = ω̄_{Ω_m+α}`"; (Z) "Note that we have
  `ϑⁿ_m(0) = Ω_m` for `m < n`".
* (S) Def 3.28: "`Subᵗ_m(α) := {α}` for parameters `α < τ`; `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ) ∪ Subᵗ_m(η)` for `ξ, η ∈ Tᵗ`
  s.t. `α =NF ξ + η > τ`; `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ)` if `k ≥ m` … for `α = ϑ_k(ξ)` …  `P_m(α) := Subᵗ_m(α) ∩ P ∩
  [Ω_m, Ω_{m+1})` and `α^{*m} := max(P_m(α) ∪ {0})`."
* (L) Lemma 3.30: "For `m < ω` the function `ϑ_m ↾ Tᵗ ∩ Ω_{m+2}` is 1-1 and has values in `P ∩ [Ω_m, Ω_{m+1})`.  Let
  `α, γ ∈ Tᵗ ∩ Ω_{m+2}`.  Then `α^{*m} < ϑ_m(α)` and
  `ϑ_m(α) < ϑ_m(γ) ⇔ α < γ ∧ α^{*m} < ϑ_m(γ) ∨ ϑ_m(α) ≤ γ^{*m}`."
* (E) Lemma 4.3: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ`.  Then `τ < α ∈ E ⇔ Δ > 0`."
* (I) Def 7.1: "`ι_{τ,α}(ξ) := ξ` if `ξ < α` • `ι_{τ,α}(ξ) := ι_{τ,α}(ξ₁) + ι_{τ,α}(ξ₂)` if `ξ =NF ξ₁ + ξ₂ > Ω₁` •
  `ι_{τ,α}(ξ) := ϑ_k(ι_{τ,α}(η))` if `ξ = ϑ_{k+1}(η)` where `k < ω`.  Note that `ι_{τ,α}(ϑ₁(η)) = ϑ^α(ι_{τ,α}(η))`."
* (Λ) Def 7.5: "`λᵗ_α := ι_{τ,α}(Δ) + ζᵗ_α` if `α ∈ E`, `ζᵗ_α` otherwise."
* (P) Def 5.1: "`π_{σ,τ}(ξ) := ξ` if `ξ < σ` • `π_{σ,τ}(ξ) := π_{σ,τ}(ξ₁) + π_{σ,τ}(ξ₂)` if `ξ =NF ξ₁ + ξ₂ > τ` •
  `π_{σ,τ}(ξ) := ϑ_k(π_{σ,τ}(η))` if `ξ = ϑ_k(η)` for some `k > 0` and `η ∈ Tᵗ[σ] ∩ Ω_{k+2}` • `π_{σ,τ}(ξ) :=
  ϑ^σ(π_{σ,τ}(η))` if `ξ = ϑᵗ(η)` for some `η ∈ Tᵗ[σ] ∩ Ω₂`."
* (H) [W07b] Def 4.1: "If `α = ϑᵗ(Δ + η) > τ` we set `δ := (λᵗ_α)^*`. • `lhᵗ(α) := α + λᵗ_α` if `δ ≤ α`, i.e. `Δ <
  ϑ₁(1)` • If `δ > α` let `(α = δ₀, …, δ_m = δ)` be the `α`-localization of `δ` in `Tᵗ`.  `lhᵗ(α) := lhᵗ(δᵢ) + λᵗ_α` if
  `i := cr(α, δ) < m`, `lhᵗ(δ) + ρ` where `ρ := −δ + λᵗ_α` otherwise."; after it: "Note that `(λᵗ_α)^*` is the maximum
  additive principal number less than or equal to `λᵗ_α`."

Our steps on a level `β ∈ Tᵗ`, `τ ≤ β < Ω₁` (used in every docstring below):
* (◆β) Write `β =ANF ω^{b₁} + ⋯ + ω^{bⱼ}` (§2 of [W07a]; `b₁ ≥ ⋯ ≥ bⱼ`, `b₁ ≥ τ ≥ 1` as `β ≥ τ = ω^τ`).  The exponents
  `bᵢ ≤ β` lie in `Tᵗ ∩ Ω₁` (Θ).  By W with `m = 1` and Z, `ϑ₁(bᵢ) = Ω₁·ω^{bᵢ}` (step ★p of `R2.CitedLu`, which uses
  only
  `bᵢ < Ω₁`), and `ϑ₁(bᵢ) ∈ T₀` (T, third clause, `k = 1 ≥ 0`, `bᵢ ∈ T₀ ∩ Ω₃`).  So `Ω₁·β = ϑ₁(b₁) + ⋯ + ϑ₁(bⱼ)` is a
  `=NF`-sum of terms of `T₀`, `Ω₁·β ∈ T₀`, and `Ω₁·β + η ∈ Tᵗ ∩ Ω₂` for `η ∈ Tᵗ ∩ Ω₁` (T, second clause; `Ω₁·β + η <
  Ω₁·(β + 1) < Ω₂`).
* (◆*) By S (second and third clauses) the level-zero subterms of `Ω₁·β + η` are its partial sums with at least two
  summands (not in `P`), the `ϑ₁(bᵢ)` (`≥ Ω₁`), and the members of `Subᵗ₀(bᵢ)` and `Subᵗ₀(η)`.  Every member of
  `Subᵗ₀(bᵢ)` in `[τ, Ω₁)` is a subterm of the term of `bᵢ`, hence `≤ bᵢ ≤ β`, and every member of `P₀(η)` is `≤ η`
  (step ★1 of `R2.CitedLu`).  So **`(Ω₁·β + η)^* ≤ max(β, η)`**.
* (◆<) For an `ε`-number `a > τ` with `(Ω₁·β + η)^* < a` and `ζ < a`: every exponent `bᵢ` is `< a` (its additive
  components are `< τ < a` or members of `Subᵗ₀(bᵢ) ∩ P ∩ [τ, Ω₁)`, `≤ (Ω₁·β + η)^* < a`, and `a` is additive
  principal),
  so `ω^{bᵢ} < a` and `β < a`; likewise the components of `η` are `< τ` or `≤ η^* < a`, so `η < a`.
* (◆ι) For `α = ϑᵗ(Ω₁·β + η)`: `Δ := Ω₁·β` is the `Δ` of Convention 4.1, `τ < α ∈ E` (E, `Δ > 0`), `β < α` (◆<
  with Lemma 3.30, `(Ω₁·β + η)^* < α`), and by I (second clause, the note for `ϑ₁(bᵢ)`, first clause for `bᵢ < α`):
  `ι_{τ,α}(Δ) = ϑ^α(b₁) + ⋯ + ϑ^α(bⱼ)`, with `ϑ^α(b) = α·ω^b` for `b < α` (W at the base `α`, `m = 0`, `Ω₀ = α`:
  `ϑ^α(1 +
  c) = ω̄_{α+c} = ω^{α+1+c}`, as `(P ∖ E) ∩ α` has order type `α`; step ★ι of `R2.CitedLu`); so **`ι_{τ,α}(Ω₁·β) =
  α·β`**.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- **[W07a] Def 3.22, Lemma 4.2 (`m = 1`), the remark after Def 3.1** (texts T, W, Z): for a level `β ∈ Tᵗ`,
`τ ≤ β < Ω₁`, and `η ∈ Tᵗ ∩ Ω₁`, `Ω₁·β + η ∈ Tᵗ`.

Our steps.  Step ◆β of the module docstring: `Ω₁·β = ϑ₁(b₁) + ⋯ + ϑ₁(bⱼ)` with `ϑ₁(bᵢ) = Ω₁·ω^{bᵢ} ∈ T₀` (T, third
clause, `k = 1 ≥ 0`; W, Z), so `Ω₁·β ∈ T₀` and `Ω₁·β + η ∈ T₀` (T, second clause). -/
axiom lvArg_mem {τ β η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hβ : β ∈ Tset τ)
    (hτβ : τ ≤ β) (hβ1 : β < Om1) (hη : η ∈ Tset τ) (hη1 : η < Om1) :
    Om1 * β + η ∈ Tset τ

/-- **[W07a] Def 5.1, Lemma 5.3, Lemma 4.2 (`m = 1`), Def 3.28** (texts P, W, Z, S, and Lemma 5.3: "(a) For `m < ω` and
`ξ ∈ Tᵗ[σ]` we have `P^σ_m(π_{σ,τ}(ξ)) = π_{σ,τ}[Pᵗ_m(ξ)]` and `Sub^σ_m(π_{σ,τ}(ξ)) = π_{σ,τ}[Subᵗ_m(ξ)]`. (b) `π_{σ,τ}`
preserves `<`. (c) `π_{σ,τ}` preserves ordinal addition. (d) `π_{σ,τ}` maps `Tᵗ[σ]` onto `T^σ`. (e) … `Parᵗ(α) =
Par^σ(π_{σ,τ}(α))` for `α ∈ Tᵗ[σ]`."): for bases `σ < τ` and a level `β ∈ Tᵗ[σ]`, `τ ≤ β < Ω₁`: `Ω₁·β ∈ Tᵗ[σ]` and
`π_{σ,τ}(Ω₁·β) = Ω₁·π_{σ,τ}(β)`.

Our steps.  `Ω₁·β = ϑ₁(b₁) + ⋯ + ϑ₁(bⱼ)` (◆β), with `β =ANF ω^{b₁} + ⋯ + ω^{bⱼ}`.  For `y ∈ Tᵗ ∩ Ω₁`:
`ω^y ∈ Tᵗ[σ] ⇔ y ∈ Tᵗ[σ]` and then `π_{σ,τ}(ω^y) = ω^{π_{σ,τ}(y)}`.  Indeed, for `y < τ` both are parameters, both sides
fail when `y ≥ σ`, and for `y < σ` it is the first clause of P; for `y ≥ τ` write `y = e + g` with `e` the largest epsilon number `≤ y`; by W (counting `P∖E` below `ω^y`),
`ω^y = ϑᵗ(e + (−1 + g))`, resp. `ϑᵗ(g)` when `e = τ`, so by S `Parᵗ(ω^y)` and `Parᵗ(y)` differ only by finite
ordinals, which are `< σ`; and `π_{σ,τ}` is by Lemma 5.3 (b)–(d) an isomorphism for `<` and `+` of `Tᵗ[σ]` onto
`T^σ`, so it maps the exponent of an additive principal number to the exponent of its image.  Since
`Parᵗ(β) = ⋃ᵢ Parᵗ(ω^{bᵢ})` (S), each `bᵢ ∈ Tᵗ[σ]`.  By S, `Parᵗ(Ω₁·β) = ⋃ᵢ Parᵗ(bᵢ) ⊆ σ`, so `Ω₁·β ∈ Tᵗ[σ]`.  P, second clause
(the sum is `> τ`), and third clause (`k = 1 > 0`): `π_{σ,τ}(Ω₁·β) = ϑ₁(π_{σ,τ}(b₁)) + ⋯ + ϑ₁(π_{σ,τ}(bⱼ))`.  By Lemma
5.3 (b), (c), `π_{σ,τ}(β) =ANF ω^{π_{σ,τ}(b₁)} + ⋯ + ω^{π_{σ,τ}(bⱼ)}`; with `ϑ₁(c) = Ω₁·ω^c` (W, Z, over `σ`):
`π_{σ,τ}(Ω₁·β) = Ω₁·π_{σ,τ}(β)`. -/
axiom lvPi_mul {σ τ β : Ordinal.{0}} (h : Bases σ τ) (hβ : β ∈ TB τ σ)
    (hτβ : τ ≤ β) (hβ1 : β < Om1) :
    Om1 * β ∈ TB τ σ ∧ pi σ τ (Om1 * β) = Om1 * pi σ τ β

/-- **[W07a] Lemma 3.30, the direction `⇐`, with Def 3.28** (texts L, S): for levels `β' ∈ Tᵗ ∩ Ω₁` and `β ∈ Tᵗ`,
`τ ≤ β < Ω₁`, and `η', η ∈ Tᵗ ∩ Ω₁` with `Ω₁·β' + η' < Ω₁·β + η`, `β' < ϑᵗ(Ω₁·β + η)` and `η' < ϑᵗ(Ω₁·β + η)`:
`ϑᵗ(Ω₁·β' + η') < ϑᵗ(Ω₁·β + η)`.

Our steps.  `α := Ω₁·β' + η'` and `γ := Ω₁·β + η` lie in `Tᵗ ∩ Ω₂` (◆β; for `β' < τ` step ★β of `R2.CitedLu`), and
`α < γ`.  By ◆* (★β, ★1 of `R2.CitedLu` for `β' < τ`), `α^* ≤ max(β', η') < ϑ₀(γ)`.  So the first disjunct of the
right side of Lemma 3.30 (`m = 0`) holds, and `ϑ₀(α) < ϑ₀(γ)`. -/
axiom lvVt_lt_gen {τ β' β η' η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1)
    (hβ' : β' ∈ Tset τ) (hβ'1 : β' < Om1)
    (hβ : β ∈ Tset τ) (hτβ : τ ≤ β) (hβ1 : β < Om1)
    (hη' : η' ∈ Tset τ) (hη'1 : η' < Om1) (hη : η ∈ Tset τ) (hη1 : η < Om1)
    (harg : Om1 * β' + η' < Om1 * β + η)
    (hβ'θ : β' < vt τ (Om1 * β + η)) (hη'θ : η' < vt τ (Om1 * β + η)) :
    vt τ (Om1 * β' + η') < vt τ (Om1 * β + η)

/-- **[W07a] Lemma 3.30, the direction `⇒`, with Def 3.28** (texts L, S): for `ξ ∈ Tᵗ ∩ Ω₂`, a level `β ∈ Tᵗ`,
`τ ≤ β < Ω₁`, and `η ∈ Tᵗ ∩ Ω₁` with `β < ϑᵗ(ξ)` and `η < ϑᵗ(ξ)`: `ϑᵗ(ξ) < ϑᵗ(Ω₁·β + η)` implies `ξ < Ω₁·β + η`.

Our steps.  `γ := Ω₁·β + η ∈ Tᵗ ∩ Ω₂` (◆β), and `γ^* ≤ max(β, η) < ϑᵗ(ξ)` (◆*).  Lemma 3.30 (`m = 0`, `α = ξ`):
`ϑ₀(ξ) < ϑ₀(γ)` gives `ξ < γ ∧ ξ^* < ϑ₀(γ)` or `ϑ₀(ξ) ≤ γ^*`; the second is impossible.  So `ξ < γ`. -/
axiom lvLt_of_vt_lt {τ ξ β η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1)
    (hξ : ξ ∈ Tset τ) (hξ2 : ξ < OmTwo)
    (hβ : β ∈ Tset τ) (hτβ : τ ≤ β) (hβ1 : β < Om1)
    (hη : η ∈ Tset τ) (hη1 : η < Om1) (hηξ : η < vt τ ξ)
    (hβξ : β < vt τ ξ) (h : vt τ ξ < vt τ (Om1 * β + η)) :
    ξ < Om1 * β + η

/-- **[W07a] Lemma 3.30 (`α^* < ϑ₀(α)`), Lemma 4.3, Def 3.28** (texts L, E, S): for a level `q ∈ Tᵗ`, `τ ≤ q < Ω₁`,
and `s ∈ Tᵗ ∩ Ω₁`: `q < ϑᵗ(Ω₁·q + s)` and `s < ϑᵗ(Ω₁·q + s)`.

Our steps.  `γ := Ω₁·q + s ∈ Tᵗ ∩ Ω₂` (◆β).  Lemma 3.30 (`m = 0`): `γ^* < ϑ₀(γ) =: a`.  By Lemma 4.3 (`Δ = Ω₁·q > 0`),
`τ < a ∈ E`.  By ◆< (with `γ^* < a`), `q < a` and `s < a`. -/
axiom lvLevel_lt_vt {τ q s : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1)
    (hq : q ∈ Tset τ) (hτq : τ ≤ q) (hq1 : q < Om1)
    (hs : s ∈ Tset τ) (hs1 : s < Om1) :
    q < vt τ (Om1 * q + s) ∧ s < vt τ (Om1 * q + s)

/-- **[W07b] Def 4.1, the case `δ > α` with `cr(α, δ) = m`, with [W07a] Def 7.5, Def 7.1, Def 6.1, Def 4.11, Def 4.6,
Def 7.15 (and the remark after it), Convention 6.6, Convention 4.1, Lemma 6.3, Lemma 4.2, Lemma 4.3, Lemma 3.30,
Def 3.28, Def 3.22** (texts H, Λ, I, D, G, LOC, CR, TR, C, W, E, L, S, T; the quotations of D, G, LOC, CR, TR, C are in
`R2.CitedLu`): for a level `β ∈ Tᵗ`, `τ ≤ β < Ω₁`, `η ∈ Tᵗ ∩ Ω₁`, `α := ϑᵗ(Ω₁·β + η)`, `b₁ := log_ω β` and `δ :=
α·ω^{b₁}`: `lhᵗ(α) = lhᵗ(δ) + (−δ + (α·β + ζᵗ_α))`.

Our steps.  `α = ϑᵗ(Δ + η)`, `Δ = Ω₁·β` (C), `α ∈ Tᵗ` (◆β, T), `τ < α ∈ E` and `β, η < α` (◆ι, ◆<, the axiom
`lvLevel_lt_vt`); `ζᵗ_α = luZeta τ β η` (G; step ★ζ of `R2.CitedLu`), `ζᵗ_α ≤ η < α`; `Δ ∈ Tᵗ_α` (D: `Δ^* ≤ β < α`,
◆*); `ι_{τ,α}(Δ) = α·β` (◆ι); so `λᵗ_α = α·β + ζᵗ_α` (Λ, `α ∈ E`).
* `δ = (λᵗ_α)^*` (H, the note): `β = ω^{b₁}·k₁ + β'` with `1 ≤ k₁ < ω`, `β' < ω^{b₁}`, `b₁ ≥ τ ≥ 1`; `α·β = ω^{α+b₁}·k₁
  + α·β'` and `ζᵗ_α < α`, so `ω^{α+b₁} ≤ λᵗ_α < ω^{α+b₁}·(k₁ + 1) < ω^{α+b₁+1}`: the maximum additive principal number
  `≤ λᵗ_α` is `ω^{α+b₁} = α·ω^{b₁} = δ`.  `δ > α` (`b₁ ≥ 1`; also `Δ ≥ Ω₁·ω = ϑ₁(1)`), so the second branch of H.
* The `α`-localization of `δ` in `Tᵗ` (LOC, Convention 6.6): in `T^α`, `δ = α·ω^{b₁} = ϑ^α(b₁)` (W at the base `α`, ◆ι,
  `b₁ ≤ β < α`), and `Sub^α₀(ϑ^α(b₁)) = {ϑ^α(b₁)} ∪ Sub^α₀(b₁) = {δ, b₁}` (S; `b₁ < α` is a parameter of `T^α`), so the
  only `ϑ^α`-subterm of `δ` in `[α, Ω₁)` is `δ` and the localization is `(α = δ₀, δ₁ = δ)`, `m = 1`.  `δ ∈ T^α_{α⁺}` (D:
  `δ^{*α} = δ < α⁺ = ϑ^α(Δ)` (TR), since `ϑ^α(Δ)` is an `ε`-number `> α` (E at the base `α`, `Δ > 0`) and `δ < ω^{α+α}`
  lies below the next `ε`-number after `α`), hence `δ^{t^α_τ} = δ` (TR).
* `cr(α, δ)` (CR with `n = m = 1`, and the remark after it): `{1, …, n − 1} = ∅`, so `cr(α, δ) = m`, and H gives
  `lhᵗ(α) = lhᵗ(δ) + ρ` with `ρ := −δ + λᵗ_α = −δ + (α·β + ζᵗ_α)`.
This is the computation of the axiom `luLhT_inf` of `R2.CitedLu` (there `β < τ`); the level `β ≥ τ` enters only through
`ι_{τ,α}(Ω₁·β) = α·β` (◆ι) and `b₁ < α`. -/
axiom lvLhT_gen {τ β η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hβ : β ∈ Tset τ)
    (hτβ : τ ≤ β) (hβ1 : β < Om1) (hη : η ∈ Tset τ) (hη1 : η < Om1) :
    lhT τ (vt τ (Om1 * β + η)) =
      lhT τ (vt τ (Om1 * β + η) * ω ^ log ω β) +
        ((vt τ (Om1 * β + η) * β + luZeta τ β η) - vt τ (Om1 * β + η) * ω ^ log ω β)

end Googology.Trans.PoR.InaccPsi.R2
