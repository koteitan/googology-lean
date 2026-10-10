import Googology.Trans.PoR.InaccPsi.R2.Cited
import Googology.Trans.PoR.InaccPsi.R2.Arith

/-!
# More cited facts on `R₁⁺`, as axioms (for INC1 and for `υ`)

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.
[G20] G. Wilken, "A glimpse of Σ₃-elementarity", in: Arai et al. (eds.), Advances in Mathematical
Logic, Springer 2021 (Chapter 21).

Same conventions as `R2.Cited` (`Ω₁ = ω₁`, `Tset τ = Tᵗ`, all bases countable).  [W07b] Lemma 2.1
and Theorem 2.2 are proved in Wilken, AML 45 (2006), which is not used; here, as in `R2.Cited`,
they are cited from their statement in [W07b] §2.

* `le1R_refl`, `le1R_limit`: [W07b] Lemma 2.1 (partial order; part (a)).
* `le1R_lim_P`: [W07b] §2, after Theorem 2.2 ("`α ≤₁ β` for some `β > α` iff `α ∈ Lim(P)`").
* `tauW`, `tauW_normal`, `ltInf1_iff_tauW`: [W07a] Def 9.1 (the enumeration `τ_ξ`, continuous at
  limits, `τ_{ρ+1} = T^{τ_ρ} ∩ Ω₁ > τ_ρ`) and [W07b] Cor 5.10 ("`α <₁ ∞` iff `α = τ_ρ` for some
  `ρ ∈ On`").
* `T_inter_Om1_one`: [W07b] Cor 5.10 for `τ = 1`; `T_one_bound`: [W07a] Thm 3.23 for `τ = 1`.
* `le1R_copy`: the `⇒` direction of the finite-set criterion [G20] Prop 21.6 for `R₁⁺`
  (`α ≤₁ β` iff `(α; 0, +, ≤, ≤₁) ≼_{Σ₁} (β; 0, +, ≤, ≤₁)`, [W07b] §1).
* `le1R_loc`: [W07b] Def 5.8 and Cor 5.9 (the `τ`-`≤₁`-localization).
* `claim56`: [W07b] Claim 5.6 (in the proof of Theorem 5.3), with Def 3.2 and Lemma 3.4 (b).

Every axiom with a base `τ` assumes `τ ∈ {1} ∪ E`, `τ < Ω₁`, as in [W07b] §4–5.  For `α ∈ Tᵗ` with
`τ < α < Ω₁`, "`α` is additive principal" is the case "`α = ϑᵗ(Δ + η)`" of [W07b] Thm 5.3 and
Cor 5.9: by [W07a] Def 3.22 and Thm 3.23 the elements of `Tᵗ ∩ [τ, Ω₁)` are the sums and the terms
`ϑ₀(ξ) = ϑᵗ(ξ)`, the latter are additive principal ([W07a] Lemma 3.30), and the unique normal form
of an additive principal number is not a proper sum; [W07b] §5 states the main theorem "for every
additive principal `α ∈ (τ, Tᵗ ∩ Ω₁)`".
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-! ## `R₁⁺` -/

/-- **[W07b] Lemma 2.1**: "`≤₁` is a partial ordering on the ordinals" (reflexive). -/
axiom le1R_refl (a : Ordinal.{0}) : le1R a a

/-- **[W07b] Lemma 2.1 (a)**: "Suppose `α ≤₁ β` for every `β ∈ [α, λ)` where `λ` is a limit ordinal
greater than `α`.  Then `α <₁ λ`." -/
axiom le1R_limit {a l : Ordinal.{0}} (hl : Order.IsSuccLimit l) (hal : a < l)
    (h : ∀ b, a ≤ b → b < l → le1R a b) : le1R a l

/-- **[W07b] §2, after Theorem 2.2**: "for any ordinal `α`, we have `α ≤₁ β` for some `β > α` if and
only if `α ∈ Lim(P) = L`" (the direction `⇒`; `L` = the limits of additive principal numbers). -/
axiom le1R_lim_P {a b : Ordinal.{0}} (h : le1R a b) (hab : a < b) :
    0 < a ∧ ∀ c < a, ∃ p, c < p ∧ p < a ∧ Indec p

/-! ## The `υ`-points -/

/-- `τ_ξ` of [W07a] Def 9.1 (`τ₀ = T¹ ∩ Ω₁`, `τ_{ρ+1} = T^{τ_ρ} ∩ Ω₁`, `τ_λ = sup_{ρ<λ} τ_ρ`).  A
constant without definition. -/
axiom tauW : Ordinal.{0} → Ordinal.{0}

/-- **[W07a] Def 9.1**: `ξ ↦ τ_ξ` is strictly increasing (`τ_{ρ+1} = T^{τ_ρ} ∩ Ω₁ > τ_ρ`, as
`τ_ρ = ϑ^{τ_ρ}(0) ∈ T^{τ_ρ}`) and continuous (`τ_λ = sup_{ρ<λ} τ_ρ` for limits `λ`). -/
axiom tauW_normal : Order.IsNormal tauW

/-- **[W07b] Cor 5.10**: "for every ordinal `α`, `α <₁ ∞` iff `α = τ_ρ` for some `ρ ∈ On`". -/
axiom ltInf1_iff_tauW (a : Ordinal.{0}) : LtInf1 a ↔ ∃ ρ, a = tauW ρ

/-- **[W07b] Cor 5.10** for `τ = 1`: `T¹ ∩ Ω₁ = min{α > 1 | α <₁ ∞}`. -/
axiom T_inter_Om1_one :
    ∃ m, 1 < m ∧ LtInf1 m ∧ (∀ a, 1 < a → LtInf1 a → m ≤ a) ∧
      ∀ a, a < Om1 → (a ∈ Tset 1 ↔ a < m)

/-- **[W07a] Theorem 3.23** for `τ = 1` ("`T_m ∩ Ω_{m+1} = θ_m = sup_{n≥m} ϑ_m(⋯(ϑ_n(0))⋯)`", `m = 0`),
with **Lemma 3.30** (the values of `ϑ₀` lie in `[Ω₀, Ω₁)`): `T¹ ∩ Ω₁` is bounded by a sequence of
countable ordinals `f n = ϑ₀(⋯ϑₙ(0)⋯)`. -/
axiom T_one_bound :
    ∃ f : ℕ → Ordinal.{0}, (∀ n, f n < Om1) ∧ ∀ a, a < Om1 → a ∈ Tset 1 → ∃ n, a < f n

/-! ## Copies (the finite-set criterion) -/

/-- **[G20] Prop 21.6** (`⇒`), for `R₁⁺` ([W07b] §1: `α ≤₁ β` iff `(α; 0, +, ≤, ≤₁) ≼_{Σ₁}
(β; 0, +, ≤, ≤₁)`, `+` as a graph): if `α ≤₁ β`, `X ⊆ α` and `Y ⊆ [α, β)` are finite, there is a
finite `Ỹ ⊆ α` and an isomorphism of `X ∪ Y` onto `X ∪ Ỹ` (for `≤`, the graph of `+` and `≤₁`) that
fixes `X`. -/
axiom le1R_copy {a b : Ordinal.{0}} (h : le1R a b) (X Y : Finset Ordinal.{0})
    (hX : ∀ x ∈ X, x < a) (hY : ∀ y ∈ Y, a ≤ y ∧ y < b) :
    ∃ Yt : Finset Ordinal.{0}, (∀ y ∈ Yt, y < a) ∧ ∃ φ : Ordinal.{0} → Ordinal.{0},
      Set.BijOn φ ↑(X ∪ Y) ↑(X ∪ Yt) ∧ (∀ x ∈ X, φ x = x) ∧ StrictMonoOn φ ↑(X ∪ Y) ∧
      (∀ x ∈ X ∪ Y, ∀ y ∈ X ∪ Y, ∀ z ∈ X ∪ Y, (x + y = z ↔ φ x + φ y = φ z)) ∧
      (∀ x ∈ X ∪ Y, ∀ y ∈ X ∪ Y, (le1R x y ↔ le1R (φ x) (φ y)))

/-! ## Localization and the obstruction of [W07b] §5 -/

/-- **[W07b] Def 5.8, Cor 5.9**: for `τ ∈ {1} ∪ E` and an additive principal `α ∈ Tᵗ ∩ (τ, Ω₁)`, the
`τ`-`≤₁`-localization `(β₁, …, β_m)` of `α` exists: "`τ < β₁ <₁ ⋯ <₁ β_m = α`, `β₁` is
`τ`-`≤₁`-minimal and for all `i` the ordinal `βᵢ` is the greatest `<₁`-predecessor of `βᵢ₊₁`"
("Iteration of this process until `τ`-`≤₁`-minimality is reached yields the `τ`-`≤₁`-localization
of `α`").  Here indexed `β 0, …, β n` with `β n = α`; `τ`-`≤₁`-minimal is [W07b] Def 3.2 ("for every
`β` such that `β <₁ α` we have `β ≤ τ`"). -/
axiom le1R_loc {τ α : Ordinal.{0}} (hτ : τ = 1 ∨ InE τ) (hτ1 : τ < Om1) (hαT : α ∈ Tset τ)
    (hτα : τ < α) (hα1 : α < Om1) (hαP : Indec α) :
    ∃ (n : ℕ) (β : ℕ → Ordinal.{0}), β n = α ∧ τ < β 0 ∧
      (∀ d, le1R d (β 0) → d < β 0 → d ≤ τ) ∧
      ∀ i < n, β i < β (i + 1) ∧ le1R (β i) (β (i + 1)) ∧
        ∀ d, le1R d (β (i + 1)) → d < β (i + 1) → d ≤ β i

/-- A covering of `S` into `R₁⁺` in the sense of [W07b] Def 5.1 ("an injection of `X` into `Y` which
preserves `≤` and `+`", and "`α ≤₁ β ⇒ h(α) ≤₁ h(β)`"); here the graph of `+` is kept in both
directions, which only makes the notion narrower. -/
def R1Cov (S : Set Ordinal.{0}) (h : Ordinal.{0} → Ordinal.{0}) : Prop :=
  StrictMonoOn h S ∧ (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, (x + y = z ↔ h x + h y = h z)) ∧
    ∀ x ∈ S, ∀ y ∈ S, le1R x y → le1R (h x) (h y)

/-- **[W07b] Claim 5.6** (proof of Theorem 5.3): "Suppose `τ < α = κᵗ_α ∈ P`.  There exist finite sets
`X ⊆ α` and `Z ⊆ [α, lh(α)]` with `α, lh(α) ∈ Z` such that there is no covering `h` of `X ∪ Z` with
`X ≤pw h[X] < h[Z] < α`."  Here for `τ ∈ {1} ∪ E` and an additive principal `α ∈ Tᵗ ∩ (τ, Ω₁)` that is
`τ`-`≤₁`-minimal: `α = κᵗ_ξ` for some `ξ ∈ (0, θ_τ]` ([W07b] Def 3.2, Lemma 3.3 (e), Cor 5.10), so
`α = κᵗ_α` by [W07b] Lemma 3.4 (b) ("For `α ∈ (0, θ_τ]` such that `κᵗ_α ∈ P` we have `κᵗ_α = α`");
`lh(α)` is an ordinal (`α < Tᵗ ∩ Ω₁ = min{α > τ | α <₁ ∞}`).  Stated for the coverings that fix `X`
(then `X ≤pw h[X]` holds), which is a special case. -/
axiom claim56 {τ α : Ordinal.{0}} (hτ : τ = 1 ∨ InE τ) (hτ1 : τ < Om1) (hαT : α ∈ Tset τ)
    (hτα : τ < α) (hα1 : α < Om1) (hαP : Indec α) (hmin : ∀ d, le1R d α → d < α → d ≤ τ) :
    ∃ l, IsLh1 α l ∧ ∃ X Z : Finset Ordinal.{0}, (∀ x ∈ X, x < α) ∧ (∀ z ∈ Z, α ≤ z ∧ z ≤ l) ∧
      α ∈ Z ∧ l ∈ Z ∧
      ¬ ∃ h, R1Cov ↑(X ∪ Z) h ∧ (∀ x ∈ X, h x = x) ∧ (∀ x ∈ X, ∀ z ∈ Z, x < h z) ∧
        ∀ z ∈ Z, h z < α

end Googology.Trans.PoR.InaccPsi.R2
