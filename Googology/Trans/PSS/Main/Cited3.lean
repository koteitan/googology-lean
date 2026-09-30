import Googology.Trans.PSS.Main.Cited2

/-!
# Cited facts for Theorem S⁺ and Theorem FIN: base transformation, `ht`, and bar at epsilons

These facts replace the three axioms `P1_isominimal` ([CW12] Cor 6.3), `exists_isominimal`
and `pwLe_of_covering` ([CW12] Core Structure Theorem (2)) in the proof of the Main
Theorem.  Their proofs in the papers do not use [W07c] (Wilken, JSL 72 (2007)), [C99] or
[W06].  Sources:

* [W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", Annals of Pure and
  Applied Logic 145 (2007) 130–161;
* [W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", Annals of Pure and
  Applied Logic 145 (2007) 162–175;
* [CW12] T. J. Carlson, G. Wilken, "Normal forms for elementary patterns", Journal of
  Symbolic Logic 77 (2012) 174–194.

Every axiom below takes **all** its hypotheses as explicit binders of its own statement
(no `variable` hypotheses, which Lean 4 drops from an `axiom` whose statement does not
mention them).

## Base transformation `π^{-1}_{γ,α}`

[W07a] Def 5.1 (p.144): for `τ ∈ E` and `σ ∈ {1} ∪ (E ∩ τ)`,
`T^τ[σ] := {α ∈ T^τ | Par^τ(α) ⊆ σ}` and `π_{σ,τ} : T^τ[σ] → T^σ`.  [W07a] Lemma 5.3,
Cor 5.4 (p.144–145): `π_{σ,τ}` is a `(<, +)`-isomorphism of `T^τ[σ]` onto `T^σ`.  Here it is
used through its inverse `piInv γ α := π^{-1}_{γ,α}` for epsilon numbers `1 < γ < α`, as a
function on the ordinals `< T¹ ∩ Ω_1`: by [W07b] Cor 5.10 (p.174),
`T^γ ∩ Ω_1 = min{β > γ | β <₁ ∞} = T¹ ∩ Ω_1` for every `γ ∈ E ∩ (1, T¹ ∩ Ω_1)`, so every
ordinal below `T1bound` is in `T^γ`, and `π^{-1}_{γ,α}` maps it into `T^α[γ] ∩ Ω_1`.

## `ht_σ`

[W07a] Def 3.26 and Lemma 3.27 (p.141): for `α < T^τ ∩ Ω_1`,
`ht_τ(α) = min{n | α < ϑ_0(⋯(ϑ_n(0))⋯)}`.  `htB σ α` is defined by this formula
(`towerR σ 0 n = ϑ^σ_0(⋯(ϑ^σ_n(0))⋯)`, with `varthetaR` of `Main/Cited2.lean`), so
`htB_mono` is a theorem; only the existence of `n` (`towerR_cofinal`) and [W07b] Lemma 4.5
(`htB_lh`) are cited.
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal

/-! ## `π^{-1}_{γ,α}` -/

/-- **`π^{-1}_{γ,α}`** ([W07a] Def 5.1, Cor 5.4): the inverse of the base transformation
`π_{γ,α} : T^α[γ] → T^γ`, as a function on ordinals (`piInv γ α x`).  A constant without a
definition; the axioms below state the cited facts about it, for epsilon numbers
`1 < γ < α < T¹ ∩ Ω_1` and arguments `x < T¹ ∩ Ω_1 = T^γ ∩ Ω_1` ([W07b] Cor 5.10). -/
axiom piInv : Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Ordinal.{0}

/-- **[W07a] Lemma 5.3 (b), Cor 5.4**: "`π_{σ,τ}` preserves `<`" and "`π_{σ,τ}` is a
`(<, +)`-isomorphism of `T^τ[σ]` and `T^σ`"; so its inverse preserves `<` on `T^γ ∩ Ω_1`. -/
axiom piInv_strictMono {γ α x y : Ordinal.{0}} (hγ : InE γ) (hα : InE α) (h1 : 1 < γ)
    (hγα : γ < α) (hαT : α < T1bound) (hxy : x < y) (hy : y < T1bound) :
    piInv γ α x < piInv γ α y

/-- **[W07a] Lemma 5.3 (c), Cor 5.4**: "`π_{σ,τ}` preserves ordinal addition" (for
`β, γ ∈ T^τ[σ]`, `π(β + γ) = π(β) + π(γ)`, proof of 5.3 (c)); so its inverse does. -/
axiom piInv_add {γ α x y : Ordinal.{0}} (hγ : InE γ) (hα : InE α) (h1 : 1 < γ)
    (hγα : γ < α) (hαT : α < T1bound) (hxy : x + y < T1bound) :
    piInv γ α (x + y) = piInv γ α x + piInv γ α y

/-- **[W07a] Def 5.1**, first clause: "`π_{σ,τ}(ξ) := ξ` if `ξ < σ`". -/
axiom piInv_fix {γ α x : Ordinal.{0}} (hγ : InE γ) (hα : InE α) (h1 : 1 < γ)
    (hγα : γ < α) (hαT : α < T1bound) (hx : x < γ) : piInv γ α x = x

/-- **[W07a] Def 5.1**, last clause, with `ϑ^τ(0) = τ` ([W07a] proof of Lemma 3.27 / Convention 3.25,
`Ω_0 = τ`): `π_{σ,τ}(τ) = π_{σ,τ}(ϑ^τ(0)) = ϑ^σ(π_{σ,τ}(0)) = ϑ^σ(0) = σ`, so
`π^{-1}_{γ,α}(γ) = α`. -/
axiom piInv_base {γ α : Ordinal.{0}} (hγ : InE γ) (hα : InE α) (h1 : 1 < γ)
    (hγα : γ < α) (hαT : α < T1bound) : piInv γ α γ = α

/-- **[W07b] Cor 5.7 (p.173) with Lemma 4.4 (p.166) and Theorem 5.3**: "Let `σ, τ ∈ E` and
`σ < τ`.  Then the restriction of `π_{σ,τ}` to the set `T^τ[σ] ∩ (τ, Ω_1)` preserves `<₁`,
and for every `α ∈ T^τ[σ] ∩ (τ, Ω_1)` we have `lh(π_{σ,τ}(α)) = π_{σ,τ}(lh(α))`"; Lemma 4.4:
"`lh^τ(α) ∈ T^τ[σ]`", and `lh = lh^τ` there (Thm 5.3).  Inverse form: for
`x ∈ (γ, T¹ ∩ Ω_1)` put `β := π^{-1}_{γ,α}(x) ∈ T^α[γ] ∩ (α, Ω_1)`; then
`lh(x) = π(lh β)`, i.e. `lh(π^{-1} x) = π^{-1}(lh x)`. -/
axiom piInv_lh {γ α x δ : Ordinal.{0}} (hγ : InE γ) (hα : InE α) (h1 : 1 < γ)
    (hγα : γ < α) (hαT : α < T1bound) (hγx : γ < x) (hx : x < T1bound) (hδ : IsLh x δ) :
    IsLh (piInv γ α x) (piInv γ α δ)

/-- **[W07b] Cor 5.7 (p.173)**: "for every `α ∈ T^τ[σ] ∩ (τ, Ω_1)` we have
`π_{σ,τ}(κ^τ_α) = κ^σ_{π_{σ,τ}(α)}`".  Inverse form, for `μ ∈ (γ, T¹ ∩ Ω_1)`:
`κ^α_{π^{-1}(μ)} = π^{-1}(κ^γ_μ)` (the domain `[0, θ_γ]` of `κ^γ` contains `μ`, since
`θ_γ = T¹ ∩ Ω_1` by [W07b] Cor 5.10). -/
axiom piInv_kap {γ α μ : Ordinal.{0}} (hγ : InE γ) (hα : InE α) (h1 : 1 < γ)
    (hγα : γ < α) (hαT : α < T1bound) (hγμ : γ < μ) (hμ : μ < T1bound) :
    kap α (piInv γ α μ) = piInv γ α (kap γ μ)

/-! ## Bar at epsilon numbers -/

/-- **[CW12] Lemma 5.7.1 (p.187), the case `α ∈ E`, with [W07b] Theorem 5.3.**  [CW12]
Lemma 5.7: "Let `α = ϑ^τ(∆ + η) ∈ T^τ`, `α > τ`.  1. We have
`ᾱ = max({γ ∈ (τ, α) ∩ E | π^{-1}_{γ,α}(λ^τ_γ) ≥ λ^τ_α} ∪ {τ})` if `α ∈ E`" (its proof: "In
case that `α ∈ L` the proof is the same as for 8.2 in [8]", i.e. [W07a] Lemma 8.2; the
known erratum of 5.7.1 concerns only the case `α ∉ E`).  Here `τ = 1` and `ᾱ` is the bar of
[CW12] Def 5.1 (`barO`).  Since `ᾱ` is the maximum, every epsilon `γ ∈ (ᾱ, α)` has
`π^{-1}_{γ,α}(λ^1_γ) < λ^1_α`; and `λ^1_β = λ_β` (the `≤₁`-`λ` of [W07b] Def 3.2, `lam`)
by [W07b] Theorem 5.3 ("We have `λ_α = λ^τ_α`"). -/
axiom lemma571_eps {α γ : Ordinal.{0}} (hα : InE α) (hαT : α < T1bound) (hγ : InE γ)
    (hbar : barO α < γ) (hγα : γ < α) : piInv γ α (lam γ) < lam α

/-! ## `ht_σ` -/

/-- `ϑ^σ_k(⋯(ϑ^σ_{k+n}(0))⋯)` in `T^σ` (`varthetaR`, [W07a] §3, Convention 3.25). -/
noncomputable def towerR (σ : Ordinal.{0}) : ℕ → ℕ → Ordinal.{0}
  | k, 0 => varthetaR σ k 0
  | k, n + 1 => varthetaR σ k (towerR σ (k + 1) n)

/-- **`ht_σ(x)`** ([W07a] Def 3.26), by the formula of [W07a] Lemma 3.27:
`ht_σ(x) = min{n | x < ϑ_0(⋯(ϑ_n(0))⋯)}` for `x < T^σ ∩ Ω_1`. -/
noncomputable def htB (σ x : Ordinal.{0}) : ℕ := sInf {n | x < towerR σ 0 n}

/-- **[W07a] Theorem 3.23 (p.140) and Lemma 3.27 (p.141), with [W07b] Cor 5.10.**
Theorem 3.23: "`T_m ∩ Ω_{m+1} = θ_m = sup_{n ≥ m} ϑ_m(⋯(ϑ_n(0))⋯)`", here at `m = 0` in the
system relativized to `σ` (Convention 3.25: `ϑ^σ = ϑ_0`, `Ω_0 = σ`); Lemma 3.27: "For
`α < T^τ ∩ Ω_1`, `ht_τ(α) = min{n | α < ϑ_0(⋯(ϑ_n(0))⋯)}`" (so the minimum exists).  And
`T^σ ∩ Ω_1 = T¹ ∩ Ω_1` for `σ ∈ {1} ∪ E`, `σ < T¹ ∩ Ω_1` ([W07b] Cor 5.10). -/
axiom towerR_cofinal {σ x : Ordinal.{0}} (hσ : σ = 1 ∨ InE σ) (hσT : σ < T1bound)
    (hx : x < T1bound) : ∃ n, x < towerR σ 0 n

/-- **[W07b] Lemma 4.5 (p.167)**: "Let `α = ϑ^τ(∆ + η)` where `∆ > 0`.  Then
`ht_α(lh^τ(α)) < ht_τ(α)`", for `τ ∈ {1} ∪ E`; with [W07b] Theorem 5.3
(`lh(α) = lh^τ(α)`), [W07a] Lemma 4.3 (`τ < α ∈ E` iff `∆ > 0`), [W07a] Lemma 6.3
(`lh^τ(α)^{t^τ_α} = lh^τ(α)`: the translation keeps the value, as used in the proof of 4.5),
and [W07a] Lemma 3.27 (`ht` as the minimum above, `htB`).  Every `α ∈ (τ, T¹ ∩ Ω_1)` is in
`T^τ` ([W07b] Cor 5.10). -/
axiom htB_lh {σ y δ : Ordinal.{0}} (hσ : σ = 1 ∨ InE σ) (hσy : σ < y) (hy : InE y)
    (hyT : y < T1bound) (hδ : IsLh y δ) : htB y δ < htB σ y

/-- `ht_σ` is weakly increasing on `T^σ ∩ Ω_1` ([W07a] Lemma 3.27, second sentence),
proved from the formula. -/
theorem htB_mono {σ x y : Ordinal.{0}} (hσ : σ = 1 ∨ InE σ) (hσT : σ < T1bound)
    (hxy : x ≤ y) (hy : y < T1bound) : htB σ x ≤ htB σ y := by
  have hne : ({n | y < towerR σ 0 n} : Set ℕ).Nonempty := towerR_cofinal hσ hσT hy
  have hmem : y < towerR σ 0 (htB σ y) := Nat.sInf_mem hne
  exact Nat.sInf_le (lt_of_le_of_lt hxy hmem)

end Googology.Trans.PSS.Main
