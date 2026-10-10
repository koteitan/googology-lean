import Googology.Trans.PoR.InaccPsi.R2.CitedR1

/-!
# Cited facts for the chain bound (Lemma L) and for parameters, as axioms

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.

Same conventions as `R2.Cited` and `R2.CitedR1` (`Ω₁ = ω₁`, `Tset τ = Tᵗ`, all bases countable, bases
in `{1} ∪ E`).  For `α ∈ Tᵗ` with `τ < α < Ω₁`, "`α = ϑᵗ(Δ + η)`" is read as "`α` is additive
principal" (the join stated in `R2.CitedR1`: [W07a] Def 3.22, Thm 3.23, Lemma 3.30), and
"`α = ϑᵗ(Δ + η)` with `Δ > 0`" as "`α` is an `ε`-number above `τ`" ([W07a] Lemma 4.3: "Let
`α = ϑᵗ(Δ + η) ∈ Tᵗ`. Then `τ < α ∈ E ⇔ Δ > 0`").

* `lhT` (constant): `lhᵗ(α)` of [W07b] Def 4.1.
* `lh_eq_lhT`: [W07b] Theorem 5.3 (last sentence, "`lh(α) = lhᵗ(α)`").
* `ht_lhT_lt`: [W07b] Lemma 4.5 ("Let `α = ϑᵗ(Δ + η)` where `Δ > 0`. Then `ht_α(lhᵗ(α)) < htᵗ(α)`").
* `Par_sub`: [W07a] Def 3.28 ("`Parᵗ(α) := Subᵗ₀(α) ∩ τ`").
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- `lhᵗ(α)`, the ordinal of [W07b] Def 4.1 ("For `α ∈ Tᵗ ∩ Ω₁` we define an ordinal
`lhᵗ(α) ∈ Tᵗ ∩ Ω₁` by recursion on `hᵗ(α)`").  A constant without definition. -/
axiom lhT : Ordinal.{0} → Ordinal.{0} → Ordinal.{0}

/-- **[W07b] Theorem 5.3**: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ`, `α > τ` … We have `λ_α = λᵗ_α` and
`lh(α) = lhᵗ(α)`."  Here for `τ ∈ {1} ∪ E` countable and an additive principal `α ∈ Tᵗ ∩ (τ, Ω₁)`
(the join of `R2.CitedR1`): `lhᵗ(α)` is the `R₁⁺`-reach of `α`. -/
axiom lh_eq_lhT {τ α : Ordinal.{0}} (hτ : τ = 1 ∨ InE τ) (hτ1 : τ < Om1) (hαT : α ∈ Tset τ)
    (hτα : τ < α) (hα1 : α < Om1) (hαP : Indec α) : IsLh1 α (lhT τ α)

/-- **[W07b] Lemma 4.5**: "Let `α = ϑᵗ(Δ + η)` where `Δ > 0`. Then `ht_α(lhᵗ(α)) < htᵗ(α)`" (the proof
notes `lhᵗ(α) < α⁺`, so `lhᵗ(α)^{t^τ_α} = lhᵗ(α)` and `ht_α` is applied to the ordinal `lhᵗ(α)`).
Here `Δ > 0` is read through [W07a] Lemma 4.3 as `α ∈ E`, `τ < α`. -/
axiom ht_lhT_lt {τ α : Ordinal.{0}} (hτ : τ = 1 ∨ InE τ) (hτ1 : τ < Om1) (hαT : α ∈ Tset τ)
    (hτα : τ < α) (hα1 : α < Om1) (hαE : InE α) : ht α (lhT τ α) < ht τ α

/-- **[W07a] Def 3.28**: "The set of parameters `< τ` used in the unique term denoting some
`α ∈ Tᵗ` is denoted by `Parᵗ(α) := Subᵗ₀(α) ∩ τ`", so `Parᵗ(α) ⊆ τ`. -/
axiom Par_sub {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {x : Ordinal.{0}}
    (hxT : x ∈ Tset τ) : ↑(Par τ x) ⊆ Set.Iio τ

end Googology.Trans.PoR.InaccPsi.R2
