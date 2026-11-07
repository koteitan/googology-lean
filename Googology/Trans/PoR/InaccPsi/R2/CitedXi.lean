import Googology.Trans.PoR.InaccPsi.R2.QtK

set_option autoImplicit false

/-!
# Cited: the parameters `P₀` of the ordinals below `θ`, and the translation `ι_{τ,α}` ([W07a] Def 3.10, Def 7.1)

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`θ = ConjT.th S = ψ_{Ω₂}(Ω_ω)` (it does not depend on `S`, ◇θ of `R2.CitedVd`), `K⁽⁰⁾_q = Ul.UlK S 0 q`, conventions
as in `R2.CitedVd` (`Tset τ = Tᵗ`, `Par τ = Parᵗ`, every base a countable `ε`-number).  Two new constants:

* `wP c`: **`P₀(c)`** (Def 3.10 at `m = 0`) of the unique term of `c` in `T₁` (every `c < θ` is in `T₁`: ◇θ).
  `wP_spec`: for a countable `c` and an `ε`-number `v`, `P₀(c) ⊆ v ⇔ c < v`; `P₀(Ω₁) = ∅`; for `Ω₁ ≤ c < θ` and a
  strongly critical `v ≤ Ω₁`, `P₀(c) ⊆ v ⇔ c ∈ K⁽⁰⁾_v` (◇V0 of `R2.CitedVd`).
* `wIo τ α`: **`ι_{τ,α}`** (Def 7.1) for `α ∈ Tᵗ ∩ E`, `τ < α < Ω₁`.  `WDom S α c` says `c ∈ Tᵗ_α ∩ Ω₂`: `c < α`, or
  `Ω₁ ≤ c < θ` with `P₀(c) ⊆ α`.  `wIo_spec`: `ι` is the identity below `α`, `ι(Ω₁) = α`, it preserves `<` and `+`
  on `WDom`, maps `WDom` into and onto `T^α ∩ Ω₁`, and `Par^α(ι(c)) ⊆ σ ⇔ P₀(c) ⊆ σ` for every `ε`-number `σ ≤ α`.

Literal texts (no new quotation): (I) Def 7.1 with Lemma 7.2 (b)–(d), as quoted in `R2.CitedRj` and `R2.CitedLg`;
(D) Def 6.1 (`Tᵗ_α := {β ∈ Tᵗ | β^{*τ} < α}`), as quoted in `R2.CitedLg`; (Q) Def 3.10 with Lemma 3.11, (U′) the
Remark after Corollary 3.15, and Def 3.6, as quoted in `R2.CitedUz`; (S) Def 3.28, (E) Lemma 4.3, (C) Convention 4.1,
(Θ) Theorem 3.23, (U) the remark after Cor 3.24, as quoted in `R2.CitedSy`; the steps ◇θ, ◇V0, ◇R of `R2.CitedVd`.

Our steps.
* (★P) `P₀` on `θ`.  By ◇θ every `c < θ` lies in `T₁ = ⋃ₙ Tⁿ₁`, with a unique term (U′); `P₀(c)` is computed along it
  (Q, Lemma 3.11 (a)).  For `c < Ω₁` the first clause of Q gives the additive components of `c`; they are all below an
  additive principal `v` iff `c < v`.  `Ω₁ = ϑ₁(0)`, so `P₀(Ω₁) = P₀(0) = ∅` (Q, third clause, and the empty sum).  For
  `Ω₁ ≤ c < θ` and strongly critical `v ≤ Ω₁`: ◇V0.
* (★D) The domain below `Ω₂`.  Let `α ∈ Tᵗ ∩ E`, `τ < α < Ω₁`.  `α` is additive principal and `≥ τ`, so its term is
  `ϑᵗ(ξ)` (U, T), `ξ = Δ + η` (C), and `Δ > 0` (E): `ι := ι_{τ,α}` is defined on `Tᵗ_α` (I).  `m := Tᵗ ∩ Ω₁` is an
  ordinal (Θ) containing `α`.  For `ξ < Ω₁`, `ξ^{*τ}` is the largest component of `ξ` above `τ` (Q), so `ξ ∈ Tᵗ_α ⇔
  ξ < α` (D; `α ⊆ m`).  For `Ω₁ ≤ ξ < Ω₂`: `ξ ∈ Tᵗ` gives `ξ < θ` (`Tᵗ ⊆ T₁`, ◇θ), and for `ξ < θ`, `ξ ∈ Tᵗ ⇔ P₀(ξ)
  ⊆ m` (Lemma 3.11 (b) with Def 3.6 at `m = 0`, as in ◇R), `ξ^{*τ} < α ⇔ P₀(ξ) ⊆ α` (`τ < α ⊆ m`).  So `Tᵗ_α ∩ Ω₂ =
  WDom S α`.
* (★ι) By I, `ι` is the identity below `α`, `ι(Ω₁) = ι(ϑ₁(0)) = ϑ^α(0) = α`, and `ι(Ω₂) = ι(ϑ₂(0)) = ϑ₁(0) = Ω₁`
  (`Ω₂ ∈ Tᵗ_α`, `P₀(Ω₂) = ∅`).  It preserves `<` (7.2 (b)) and `+` (7.2 (c)) and maps `Tᵗ_α` onto `T^α` (7.2 (d)); by
  the order and `ι(Ω₂) = Ω₁` it maps `WDom S α = Tᵗ_α ∩ Ω₂` into and onto `T^α ∩ Ω₁`.
* (★Par) For `c ∈ WDom S α`, `c ≥ Ω₁`: the maximal countable subterms `c₁, …, c_r` of the term of `c` (the countable
  summands of its `=NF` sums, U) have their components in `P₀(c) ⊆ α`, so they are below `α`; I keeps them (first
  clause) and replaces every `ϑ_{k+1}` by `ϑ_k`.  In `T^α` the `cᵢ` are parameters (below `α`), and by S (the `Sub` of
  a sum and of `ϑ_k(η)`, `k ≥ 0`, contains the `Sub` of the parts; the `Sub` of a parameter is itself) `Par^α(ι(c))`
  is `{c₁, …, c_r}`, with `0` for the subterms `ϑ_k(0)`.  `P₀(c)` is the set of the additive components of the `cᵢ`
  (Q).  So `Par^α(ι(c)) ⊆ σ ⇔ P₀(c) ⊆ σ` for every additive principal `σ`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Googology.Notation.InaccPsi

/-- **`P₀(c)`** ([W07a] Def 3.10, `m = 0`) of the unique term of `c ∈ T₁` (★P). -/
axiom wP : Ordinal.{0} → Finset Ordinal.{0}

/-- **[W07a] Def 3.10, Lemma 3.11, the Remark after Cor 3.15** (texts Q, U′, and ◇θ, ◇V0 of `R2.CitedVd`): `P₀` of a
countable ordinal is below an `ε`-number `v` iff the ordinal is; `P₀(Ω₁) = ∅`; for `Ω₁ ≤ c < θ` and strongly critical
`v ≤ Ω₁`, `P₀(c) ⊆ v` iff `c ∈ K⁽⁰⁾_v`.

Our steps.  (★P). -/
axiom wP_spec (S : InaccSeq.{0}) :
    (∀ c v : Ordinal.{0}, c < Om1 → InE v → ((∀ p ∈ wP c, p < v) ↔ c < v)) ∧ wP Om1 = ∅ ∧
    ∀ c v : Ordinal.{0}, Om1 ≤ c → c < ConjT.th S → SC v → v ≤ Om1 →
      ((∀ p ∈ wP c, p < v) ↔ Ul.UlK S 0 v c)

/-- `c ∈ Tᵗ_α ∩ Ω₂` (★D): `c < α`, or `Ω₁ ≤ c < θ` with `P₀(c) ⊆ α`. -/
def WDom (S : InaccSeq.{0}) (α c : Ordinal.{0}) : Prop :=
  c < α ∨ (Om1 ≤ c ∧ c < ConjT.th S ∧ ∀ p ∈ wP c, p < α)

/-- **`ι_{τ,α}`** ([W07a] Def 7.1). -/
axiom wIo : Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Ordinal.{0}

/-- **[W07a] Def 7.1, Lemma 7.2 (b)–(d), Def 6.1, Def 3.10, Lemma 3.11, Def 3.28, Def 3.22, Lemma 4.3, Convention 4.1,
Theorem 3.23** (texts I, D, Q, U′, S, T, E, C, Θ, U, and the steps): for `α ∈ Tᵗ ∩ E` with `τ < α < Ω₁`, on
`WDom S α = Tᵗ_α ∩ Ω₂`, `ι_{τ,α}` is the identity below `α`, sends `Ω₁` to `α`, preserves `<` and `+`, maps into and
onto `T^α ∩ Ω₁`, and `Par^α(ι(c)) ⊆ σ ⇔ P₀(c) ⊆ σ` for every `ε`-number `σ ≤ α` and `c ≥ Ω₁`.

Our steps.  (★D), (★ι), (★Par). -/
axiom wIo_spec (S : InaccSeq.{0}) {τ α : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hα : InE α)
    (hαT : α ∈ Tset τ) (hτα : τ < α) (hα1 : α < Om1) :
    (∀ c, c < α → wIo τ α c = c) ∧ wIo τ α Om1 = α ∧
    (∀ c d, WDom S α c → WDom S α d → c < d → wIo τ α c < wIo τ α d) ∧
    (∀ c d, WDom S α c → WDom S α d → WDom S α (c + d) → wIo τ α (c + d) = wIo τ α c + wIo τ α d) ∧
    (∀ c, WDom S α c → wIo τ α c ∈ Tset α ∧ wIo τ α c < Om1) ∧
    (∀ v, v ∈ Tset α → v < Om1 → ∃ c, WDom S α c ∧ wIo τ α c = v) ∧
    ∀ c, WDom S α c → Om1 ≤ c → ∀ σ, InE σ → σ ≤ α →
      (↑(Par α (wIo τ α c)) ⊆ Set.Iio σ ↔ ∀ p ∈ wP c, p < σ)

end Googology.Trans.PoR.InaccPsi.R2
