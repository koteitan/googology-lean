import Mathlib

/-!
# The cited facts, as axioms (the only axioms of `Googology.Trans.PoR.InaccPsi.R2`)

`R₂^C` itself (`Defs.lean`) is DEFINED from [C09] Def 5.3–5.4 and needs no axiom.  The axioms
below are about `R₁⁺ = (On; 0, +, ≤, ≤₁)` (Carlson's `R₁`, `≤₁` by `Σ₁`-elementarity) and
Wilken's notation systems `Tᵗ` with the base change `π_{σ,τ}`; they are what Lemma FRAG
(`Frag.lean`) uses.  Papers:

* [W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161;
* [W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.

[W07b] Lemma 2.1 and Theorem 2.2 are proved in Wilken, AML 45 (2006), which is not used; here
they are cited from their statement in [W07b] §2.

Conventions.  `Ω₁` is `ω₁` (`Ordinal.omega 1`): [W07a] §3 takes for `Ω₁` "an uncountable regular
cardinal number greater than `τ`"; every base `τ` below is countable (`τ < Ω₁`), so `ω₁` is a
legitimate choice.  `Tset τ` is the set of ordinals denoted in `Tᵗ` ([W07a] Conv. 3.25, Thm 3.23);
`Par τ α` is `Parᵗ(α)` ([W07a] Def 3.28); `pi σ τ` is `π_{σ,τ}` ([W07a] Def 5.1).  All three are
constants without a definition (the term systems are not formalized); the axioms state the
cited facts about them, always under `σ, τ ∈ E`, `σ < τ < Ω₁`.

The axioms (27 = 7 constants + 20 facts):
* constants: `le1R` (`≤₁` of `R₁⁺`), `Tset` (`Tᵗ`), `Par` (`Parᵗ`), `pi` (`π_{σ,τ}`), `ht` (`htᵗ`),
  `Dl` (`ϑᵗ(Δₙ)`), `Dp` (`ϑᵗ(Δₙ + 1)`);
* `R₁⁺`: `le1R_trans`, `le1R_le`, `le1R_of_le` ([W07b] Lemma 2.1, §1), `le1R_two_iff` ([W07b]
  remark after Thm 2.2);
* base change: `TB_inter_lt`, `pi_lt`, `pi_base`, `pi_Om1`, `pi_bijOn`, `pi_add`, `pi_ht_Par`
  ([W07a] Def 5.1, Lemma 5.3, Cor 5.4), `lh_pi` ([W07b] Lemma 4.4, Thm 5.3, Cor 5.7),
  `T_inter_Om1` ([W07b] Cor 5.10);
* terms: `Par_lt`, `Par_comps` ([W07a] Def 3.28), `ht_spec` ([W07a] Lemma 3.27), `Dl_spec`
  ([W07a] Def 3.26), `Dl_E` ([W07a] Lemma 4.3, Def 3.28), `Dp_spec` ([W07a] Conv. 4.1,
  Lemma 6.3), `par_track` ([W07a] Lemma 6.10 with Lemmas 6.3, 3.30).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-! ## `R₁⁺` -/

/-- **Carlson's `≤₁` of `R₁⁺`** ([W07b] §1): `α ≤₁ β` iff
`(α; 0, +, ≤₁) ≼_{Σ₁} (β; 0, +, ≤₁)`, by recursion on `β`.  A constant without definition. -/
axiom le1R : Ordinal.{0} → Ordinal.{0} → Prop

/-- `r = lh(α)` in `R₁⁺` ([W07b] Def 3.1): `r = max{β | α ≤₁ β}`. -/
def IsLh1 (a r : Ordinal.{0}) : Prop := le1R a r ∧ ∀ g, le1R a g → g ≤ r

/-- `α <₁ ∞` in `R₁⁺` ([W07b] §1: "`lh(α)` is defined to be `∞` if `α ≤₁ β` for every
`β ≥ α`"). -/
def LtInf1 (a : Ordinal.{0}) : Prop := ∀ g, a ≤ g → le1R a g

/-- `α ∈ E`: an epsilon number. -/
def InE (a : Ordinal.{0}) : Prop := ω ^ a = a

/-- `Ω₁ = ω₁`. -/
noncomputable def Om1 : Ordinal.{0} := Ordinal.omega 1

/-- **[W07b] Lemma 2.1**: "`≤₁` is a partial ordering on the ordinals" (transitive). -/
axiom le1R_trans {a b c : Ordinal.{0}} : le1R a b → le1R b c → le1R a c

/-- **[W07b] §1**: `α ≤₁ β` says that `(α; …)` is a substructure of `(β; …)`, so `α ≤ β`. -/
axiom le1R_le {a b : Ordinal.{0}} : le1R a b → a ≤ b

/-- **[W07b] Lemma 2.1 (b)**: "If `α ≤ β ≤ γ` and `α ≤₁ γ` then `α ≤₁ β`." -/
axiom le1R_of_le {a b c : Ordinal.{0}} (h1 : a ≤ b) (h2 : b ≤ c) (h : le1R a c) : le1R a b

/-- **[W07b] §2, after Theorem 2.2**: "For `ξ = α` the theorem yields `α ≤₁ α·2` if and only if
`α ∈ E`" (Theorem 2.2 is stated for `ξ ∈ (0, α]`, so `α > 0`). -/
axiom le1R_two_iff {a : Ordinal.{0}} (h : 0 < a) : le1R a (a * 2) ↔ InE a

/-! ## Wilken's notation systems and base change -/

/-- `Tᵗ ⊆ On`: the ordinals with a notation in Wilken's system over `τ` ([W07a] Conv. 3.25,
Def 3.22, Thm 3.23).  A constant without definition. -/
axiom Tset : Ordinal.{0} → Set Ordinal.{0}

/-- `Parᵗ(α)`: "the set of parameters `< τ` used in the unique term denoting some `α ∈ Tᵗ`"
([W07a] Def 3.28; a finite set, as a term has finitely many subterms).  A constant without
definition. -/
axiom Par : Ordinal.{0} → Ordinal.{0} → Finset Ordinal.{0}

/-- `Tᵗ[σ] := {α ∈ Tᵗ | Parᵗ(α) ⊆ σ}` ([W07a] Def 5.1). -/
def TB (τ σ : Ordinal.{0}) : Set Ordinal.{0} := {a | a ∈ Tset τ ∧ ↑(Par τ a) ⊆ Set.Iio σ}

/-- `π_{σ,τ} : Tᵗ[σ] → Tᵟ` ([W07a] Def 5.1); written `pi σ τ`.  A constant without
definition. -/
axiom pi : Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Ordinal.{0}

/-- The standing hypothesis of [W07a] §5 / [W07b] Lemma 4.4, Cor 5.7: `σ, τ ∈ E`, `σ < τ`
(here also `τ < Ω₁`). -/
def Bases (σ τ : Ordinal.{0}) : Prop := InE σ ∧ InE τ ∧ σ < τ ∧ τ < Om1

/-- **[W07a] proof of Lemma 5.3**: "Clearly, `Tᵗ[σ] ∩ τ = σ`." -/
axiom TB_inter_lt {σ τ : Ordinal.{0}} (h : Bases σ τ) {x : Ordinal.{0}} (hx : x < τ) :
    x ∈ TB τ σ ↔ x < σ

/-- **[W07a] Def 5.1**, first clause: "`π_{σ,τ}(ξ) := ξ` if `ξ < σ`". -/
axiom pi_lt {σ τ : Ordinal.{0}} (h : Bases σ τ) {x : Ordinal.{0}} (hx : x < σ) :
    pi σ τ x = x

/-- **[W07a] Def 5.1**, fourth clause with `η = 0`, and `ϑᵗ(0) = τ` ([W07a] proof of
Lemma 3.27: "We have `ϑ₀(0) = τ`"): `τ ∈ Tᵗ[σ]` and `π_{σ,τ}(τ) = ϑᵟ(0) = σ`. -/
axiom pi_base {σ τ : Ordinal.{0}} (h : Bases σ τ) : τ ∈ TB τ σ ∧ pi σ τ τ = σ

/-- **[W07a] Def 5.1**, third clause with `k = 1`, `η = 0`, and `ϑ₁(0) = Ω₁` ([W07a] remark
after Def 3.1: "`ϑᵐₙ(0) = Ωₘ` for `m < n`"): `Ω₁ ∈ Tᵗ[σ]` and `π_{σ,τ}(Ω₁) = Ω₁`. -/
axiom pi_Om1 {σ τ : Ordinal.{0}} (h : Bases σ τ) : Om1 ∈ TB τ σ ∧ pi σ τ Om1 = Om1

/-- **[W07a] Lemma 5.3 (b), (d)** (Cor 5.4): `π_{σ,τ}` is a strictly increasing map of `Tᵗ[σ]`
onto `Tᵟ`. -/
axiom pi_bijOn {σ τ : Ordinal.{0}} (h : Bases σ τ) :
    Set.BijOn (pi σ τ) (TB τ σ) (Tset σ) ∧ StrictMonoOn (pi σ τ) (TB τ σ)

/-- **[W07a] Lemma 5.3 (c)** with its proof ("`Tᵗ[σ]` is closed under ordinal addition"):
`π_{σ,τ}(β + γ) = π_{σ,τ}(β) + π_{σ,τ}(γ)` for `β, γ ∈ Tᵗ[σ]`. -/
axiom pi_add {σ τ : Ordinal.{0}} (h : Bases σ τ) {x y : Ordinal.{0}} (hx : x ∈ TB τ σ)
    (hy : y ∈ TB τ σ) : x + y ∈ TB τ σ ∧ pi σ τ (x + y) = pi σ τ x + pi σ τ y

/-- **[W07b] Lemma 4.4, Theorem 5.3, Corollary 5.7**: for `α ∈ Tᵗ[σ] ∩ (τ, Ω₁)`, `lh(α) = lhᵗ(α)`
(Thm 5.3, as used in the proof of Cor 5.7: "`lh(α) = lhᵗ(α)` for every `α ∈ Tᵗ ∩ (τ, Ω₁)`"),
`lhᵗ(α) ∈ Tᵗ ∩ Ω₁` (Def 4.1) and `lhᵗ(α) ∈ Tᵗ[σ]` (Lemma 4.4), and
`lh(π_{σ,τ}(α)) = π_{σ,τ}(lh(α))` (Cor 5.7). -/
axiom lh_pi {σ τ : Ordinal.{0}} (h : Bases σ τ) {x : Ordinal.{0}} (hx : x ∈ TB τ σ)
    (h1 : τ < x) (h2 : x < Om1) :
    ∃ l, IsLh1 x l ∧ l ∈ TB τ σ ∧ IsLh1 (pi σ τ x) (pi σ τ l)

/-- **[W07b] Corollary 5.10**: "For `τ ∈ {1} ∪ E` we have `Tᵗ ∩ Ω₁ = min{α > τ | α <₁ ∞}`"
(the minimum exists, and `Tᵗ ∩ Ω₁` is that ordinal, i.e. the set of the ordinals below it). -/
axiom T_inter_Om1 {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) :
    ∃ m, τ < m ∧ LtInf1 m ∧ (∀ a, τ < a → LtInf1 a → m ≤ a) ∧
      ∀ a, a < Om1 → (a ∈ Tset τ ↔ a < m)

/-! ## Heights, the points `ϑᵗ(Δₙ)`, `ϑᵗ(Δₙ + 1)`, and parameter tracking (for FRAG with several
bases) -/

/-- `Cl(X)` ([W07a] Def 2.1): the closure of `X` under `+` and `ξ ↦ ω^ξ`. -/
inductive Cl (X : Set Ordinal.{0}) : Ordinal.{0} → Prop
  | base {x : Ordinal.{0}} : x ∈ X → Cl X x
  | add {x y : Ordinal.{0}} : Cl X x → Cl X y → Cl X (x + y)
  | opow {x : Ordinal.{0}} : Cl X x → Cl X (ω ^ x)

/-- `Cl(X)` as a set. -/
def ClS (X : Set Ordinal.{0}) : Set Ordinal.{0} := {x | Cl X x}

/-- The additive components of `ξ`: `ξ₁, …, ξₙ` for `ξ =ANF ξ₁ + ⋯ + ξₙ` (from the Cantor
normal form `ω^{e₁}·k₁ + ⋯`, each `ω^{eᵢ}`). -/
noncomputable def comps (x : Ordinal.{0}) : List Ordinal.{0} := (CNF ω x).map fun p => ω ^ p.1

/-- `X` is closed under additive decomposition ([W07a] §2). -/
def DC (X : Set Ordinal.{0}) : Prop := ∀ x ∈ X, ∀ p ∈ comps x, p ∈ X

/-- `htᵗ : Tᵗ → ω` ([W07a] Def 3.26).  A constant without definition. -/
axiom ht : Ordinal.{0} → Ordinal.{0} → ℕ

/-- `Dl τ n = ϑ₀(ϑ₁(⋯ϑₙ(0)⋯))` over `τ` ([W07a] Lemma 3.27; `= ϑᵗ(Δₙ)` with
`Δₙ = ϑ₁(⋯ϑₙ(0)⋯)` for `n ≥ 1`, `Dl τ 0 = ϑᵗ(0) = τ`).  A constant without definition. -/
axiom Dl : Ordinal.{0} → ℕ → Ordinal.{0}

/-- `Dp τ n = ϑᵗ(Δₙ + 1)`, i.e. `α⁺` for `α = ϑᵗ(Δₙ)` ([W07a] Conv. 4.1).  A constant without
definition. -/
axiom Dp : Ordinal.{0} → ℕ → Ordinal.{0}

/-- **[W07a] Def 3.28**: for a parameter `ξ < τ`, `Subᵗ(ξ) = {ξ}`, so `Parᵗ(ξ) = {ξ}`. -/
axiom Par_lt {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {x : Ordinal.{0}} (hx : x < τ) :
    Par τ x = {x}

/-- **[W07a] Def 3.28** for `ξ =NF ξ₁ + ξ₂ > τ` (`Subᵗ(ξ) ⊇ Subᵗ(ξ₁) ∪ Subᵗ(ξ₂)`), applied to
the additive normal form `ξ =ANF ξ₁ + ⋯ + ξₙ ≥ τ` of an element of `Tᵗ`: a component `ξᵢ < τ` is
a parameter of `ξ`, and a component `ξᵢ ≥ τ` is a subterm of `ξ` (in `Tᵗ`, with
`Parᵗ(ξᵢ) ⊆ Parᵗ(ξ)`). -/
axiom Par_comps {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {x : Ordinal.{0}}
    (hxT : x ∈ Tset τ) (hτx : τ ≤ x) (hx1 : x < Om1) {p : Ordinal.{0}} (hp : p ∈ comps x) :
    (p < τ → p ∈ Par τ x) ∧ (τ ≤ p → p ∈ Tset τ ∧ Par τ p ⊆ Par τ x)

/-- **[W07a] Lemma 3.27**: "For `α < Tᵗ ∩ Ω₁`, `htᵗ(α) = min{n | α < ϑ₀(⋯(ϑₙ(0))⋯)}`" (the
minimum exists). -/
axiom ht_spec {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {x : Ordinal.{0}}
    (hxT : x ∈ Tset τ) (hx1 : x < Om1) :
    (∃ n, x < Dl τ n) ∧ ht τ x = sInf {n | x < Dl τ n}

/-- **[W07a] Def 3.26** (the largest `k` with a subterm `ϑₖ(η)` of `ϑ₀(ϑ₁(⋯ϑₙ(0)⋯))` is `n`), with
`ϑ₀(⋯ϑₙ(0)⋯) ∈ Tᵗ ∩ Ω₁`: `htᵗ(Dl τ n) = n + 1`. -/
axiom Dl_spec {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (n : ℕ) :
    Dl τ n ∈ Tset τ ∧ Dl τ n < Om1 ∧ ht τ (Dl τ n) = n + 1

/-- **[W07a] Lemma 4.3** ("for `α = ϑᵗ(Δ + η) ∈ Tᵗ`: `τ < α ∈ E ⇔ Δ > 0`", here `Δ = Δₙ > 0`)
and **Def 3.28** (the only parameter of `ϑᵗ(ϑ₁(⋯ϑₙ(0)⋯))` is `0`): for `n ≥ 1`,
`τ < ϑᵗ(Δₙ) ∈ E` and `Parᵗ(ϑᵗ(Δₙ)) ⊆ {0}`. -/
axiom Dl_E {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {n : ℕ} (hn : 1 ≤ n) :
    τ < Dl τ n ∧ InE (Dl τ n) ∧ ↑(Par τ (Dl τ n)) ⊆ ({0} : Set Ordinal.{0})

/-- **[W07a] Conv. 4.1, Lemma 6.3**: for `n ≥ 1` and `α = ϑᵗ(Δₙ)`, `α⁺ = ϑᵗ(Δₙ + 1)` is in
`Tᵗ ∩ Ω₁`, and "`α⁺ = ϑ^α(Δ)`" (Lemma 6.3, with `Δ = Δₙ`), i.e. `α⁺ = Dl α n`. -/
axiom Dp_spec {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {n : ℕ} (hn : 1 ≤ n) :
    Dp τ n ∈ Tset τ ∧ Dp τ n < Om1 ∧ Dp τ n = Dl (Dl τ n) n

/-- **[W07a] Lemma 5.3 (e)**: "`htᵗ(α) = htᵟ(π_{σ,τ}(α))` and `Parᵗ(α) = Parᵟ(π_{σ,τ}(α))` for
`α ∈ Tᵗ[σ]`". -/
axiom pi_ht_Par {σ τ : Ordinal.{0}} (h : Bases σ τ) {x : Ordinal.{0}} (hx : x ∈ TB τ σ) :
    ht σ (pi σ τ x) = ht τ x ∧ Par σ (pi σ τ x) = Par τ x

/-- **[W07a] Lemma 6.10**, with **Lemma 6.3** (the translation `t^α_τ` is the identity on
`T^α_{α⁺}`, so `Parᵗ(β^{t^α_τ})` is `Parᵗ` of the ordinal `β`) and **Lemma 3.30** (`β^* ≤ β` for
countable `β`, so `β ∈ T^α`, `β < α⁺` gives `β ∈ T^α_{α⁺}`), for `α = ϑᵗ(Δₙ)` (`n ≥ 1`), which is
in `Tᵗ ∩ E ∩ (τ, Ω₁)` (Lemma 4.3): "Let `τ ∈ E`, `α ∈ Tᵗ ∩ E ∩ (τ, Ω₁)`, and `β ∈ T^α_{α⁺}`.
Further, let `X ⊆ α` contain `0` and be closed under additive decomposition.  Suppose that
`⋃_{ξ∈X} Parᵗ(ξ) ∪ Parᵗ(α) ⊆ Cl(X ∩ τ)` and `Par^α(β) ⊆ Cl(X)`.  Then
`Parᵗ(β^{t^α_τ}) ⊆ Cl(X ∩ τ)`." -/
axiom par_track {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {n : ℕ} (hn : 1 ≤ n)
    {x : Ordinal.{0}} (hxT : x ∈ Tset (Dl τ n)) (hx1 : Dl τ n ≤ x) (hx2 : x < Dp τ n)
    {X : Set Ordinal.{0}} (hXa : X ⊆ Set.Iio (Dl τ n)) (h0 : (0 : Ordinal.{0}) ∈ X) (hDC : DC X)
    (hPX : ∀ ξ ∈ X, ↑(Par τ ξ) ⊆ ClS (X ∩ Set.Iio τ))
    (hPa : ↑(Par τ (Dl τ n)) ⊆ ClS (X ∩ Set.Iio τ))
    (hPx : ↑(Par (Dl τ n) x) ⊆ ClS X) :
    ↑(Par τ x) ⊆ ClS (X ∩ Set.Iio τ)

end Googology.Trans.PoR.InaccPsi.R2
