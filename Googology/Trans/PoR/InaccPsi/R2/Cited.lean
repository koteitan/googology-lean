import Mathlib

/-!
# The cited facts, as axioms (the only axioms of `Googology.Trans.PoR.InaccPsi.R2`)

`R₂^C` itself (`R2.Defs`) is DEFINED from [C09] Def 5.3–5.4 and needs no axiom.  The axioms
below are about `R₁⁺ = (On; 0, +, ≤, ≤₁)` (Carlson's `R₁`, `≤₁` by `Σ₁`-elementarity) and
Wilken's notation systems `Tᵗ` with the base change `π_{σ,τ}`; they are what Lemma FRAG
(`R2.Frag`) uses.  Papers:

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

The axioms (28 = 7 constants + 21 facts):
* constants: `le1R` (`≤₁` of `R₁⁺`), `Tset` (`Tᵗ`), `Par` (`Parᵗ`), `pi` (`π_{σ,τ}`), `ht` (`htᵗ`),
  `Dl` (`ϑᵗ(Δₙ)`), `Dp` (`ϑᵗ(Δₙ + 1)`);
* `R₁⁺`: `le1R_trans`, `le1R_le`, `le1R_of_le` ([W07b] Lemma 2.1, §1), `le1R_two_iff` ([W07b]
  remark after Thm 2.2);
* base change: `TB_inter_lt`, `pi_lt`, `pi_base`, `om1_opow_TB_all` (moved here from `R2.CitedSi`; the former axiom
  `luOm1_opow_TB` is its case `b < σ` and `pi_Om1` its case `b = 0`, both theorems), `pi_bijOn`, `pi_add`, `pi_ht_Par`
  ([W07a] Def 5.1, Lemma 5.3, Cor 5.4), `lh_pi` ([W07b] Lemma 4.4, Thm 5.3, Cor 5.7),
  `T_inter_Om1` ([W07b] Cor 5.10);
* terms: `vzT_add` ([W07a] Def 3.22; moved here unchanged from `R2.CitedVz`), `Par_lt`, `Par_comps_eq`
  ([W07a] Def 3.28; `Par_comps` is now a theorem from it), `ht_spec` ([W07a] Lemma 3.27), `Dl_spec`
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

/-- `π_{σ,τ} : Tᵗ[σ] → T^σ` ([W07a] Def 5.1); written `pi σ τ`.  A constant without
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

/-- **[W07a] Def 5.1 (first and third clauses), Lemma 5.3 (b), Def 3.22, the Remark after Corollary 3.24, the remark
after Def 3.1, Def 3.4 with Lemma 4.2 (`m = 1`), Def 3.28, Lemma 3.30 (`m = 1`)** (moved here from `R2.CitedSi`, where
it was stated with the bound `b < ε_{Ω₁+1}` written as `Gg.ggE`; here the same bound is written as "`b` lies below
every `ε`-number above `Ω₁`", which needs no definition): for bases `σ < τ` and `b < ε_{Ω₁+1}`: `Ω₁·ω^b ∈ Tᵗ[σ]` iff
`b ∈ Tᵗ[σ]`, and then `π_{σ,τ}(Ω₁·ω^b) = Ω₁·ω^{π_{σ,τ}(b)}`.  It contains the former axiom `luOm1_opow_TB` (`b < σ`,
now a theorem below) and `R2.siOm1_opow_TB` (now a theorem in `R2.CitedSi`).

Literal texts (all of [W07a]; checked against the paper):
* (P) Def 5.1: "Let `τ ∈ E` and `Tᵗ` be the notation system over `τ`.  Further, let `σ ∈ {1} ∪ (E ∩ τ)`.  We define
  `Tᵗ[σ] := {α ∈ Tᵗ | Parᵗ(α) ⊆ σ}` and `π_{σ,τ} : Tᵗ[σ] → T^σ` by the following clauses: • `π_{σ,τ}(ξ) := ξ` if
  `ξ < σ` • `π_{σ,τ}(ξ) := π_{σ,τ}(ξ₁) + π_{σ,τ}(ξ₂)` if `ξ =NF ξ₁ + ξ₂ > τ` • `π_{σ,τ}(ξ) := ϑ_k(π_{σ,τ}(η))` if
  `ξ = ϑ_k(η)` for some `k > 0` and `η ∈ Tᵗ[σ] ∩ Ω_{k+2}` • `π_{σ,τ}(ξ) := ϑ^σ(π_{σ,τ}(η))` if `ξ = ϑᵗ(η)` for some
  `η ∈ Tᵗ[σ] ∩ Ω₂`."
* (5.3) Lemma 5.3: "(b) `π_{σ,τ}` preserves `<`."
* (T) Def 3.22: "`Ω_m ⊆ T_m` • `ξ, η ∈ T_m ⇒ ξ + η ∈ T_m` • `ξ ∈ T_m ∩ Ω_{k+2} ⇒ ϑ_k(ξ) ∈ T_m` for `k ≥ m`."
* (U) Remark after Corollary 3.24: "each `T_m` again gives rise to a notation system with parameters from `Ω_m` that
  provides a unique term for every ordinal which is element of some `Tⁿ_m` where `n > m`".
* (Z) After Def 3.1: "Note that we have `ϑⁿ_m(0) = Ω_m` for `m < n`".
* (W) Def 3.4: "Let `α ↦ ω̄_α` be the enumeration function of the additive principle numbers which are not epsilon
  numbers."  Lemma 4.2: "For any `m < ω` and any `α < Ω_{m+1}` we have `ϑ_m(1 + α) = ω̄_{Ω_m+α}`".
* (S) Def 3.28: "`Subᵗ_m(α) := {α}` for parameters `α < τ`; `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ) ∪ Subᵗ_m(η)` for
  `ξ, η ∈ Tᵗ` s.t. `α =NF ξ + η > τ`; `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ)` if `k ≥ m`, `{α}` if `k < m`, for `α = ϑ_k(ξ)`
  where `ξ ∈ Tᵗ ∩ Ω_{k+2}`.  …  `P_m(α) := Subᵗ_m(α) ∩ P ∩ [Ω_m, Ω_{m+1})` and `α^{*m} := max(P_m(α) ∪ {0})`.  The
  set of parameters `< τ` used in the unique term denoting some `α ∈ Tᵗ` is denoted by `Parᵗ(α) := Subᵗ₀(α) ∩ τ`."
* (L) Lemma 3.30: "For `m < ω` the function `ϑ_m ↾ Tᵗ ∩ Ω_{m+2}` is 1-1 and has values in `P ∩ [Ω_m, Ω_{m+1})`.  Let
  `α, γ ∈ Tᵗ ∩ Ω_{m+2}`.  Then `α^{*m} < ϑ_m(α)` and `ϑ_m(α) < ϑ_m(γ) ⇔ α < γ ∧ α^{*m} < ϑ_m(γ) ∨ ϑ_m(α) ≤ γ^{*m}`."

Our steps (`ε_{Ω₁+1}` is the least `ε`-number above `Ω₁`; the hypothesis `hbE` says `b < ε_{Ω₁+1}`).
* (★1) `ϑ₁(0) = Ω₁` (Z) and `ϑ₁(m) = ω^{Ω₁+m}` for `1 ≤ m < ε_{Ω₁+1}` (W: `ϑ₁(1 + a) = ω̄_{Ω₁+a}`; the additive
  principal numbers below `Ω₁ = ω^{Ω₁}` that are not `ε`-numbers have order type `Ω₁`, and there is no `ε`-number in
  `(Ω₁, ε_{Ω₁+1})`, so `ω̄_{Ω₁+a} = ω^{Ω₁+1+a}`); hence `Ω₁·ω^m = ω^{Ω₁+m} = ϑ₁(m)` for every `m < ε_{Ω₁+1}`, and
  `m ↦ ϑ₁(m)` is strictly increasing on `[0, Ω₂)` (W: `ω̄` is an enumeration).  These hold over every base (the
  `ϑ₁`-function does not depend on `τ`: `Ω₀ = τ` enters `C_m` only for `m = 0`).
* (★2) `ε_{Ω₁+1} ≤ ϑ₁(Ω₂)`: `a₀ = 0`, `a_{k+1} = ϑ₁(a_k)` (`a₁ = Ω₁`, `a_{k+1} = ω^{Ω₁+a_k}`, `sup_k a_k = ε_{Ω₁+1}` by
  ★1) lie in `Tᵗ ∩ Ω₂` (T); `Ω₂ = ϑ₂(0) ∈ Tᵗ` (Z, T), `(Ω₂)^{*1} = 0` (S); by induction on `k`, `P₁(a_k) ⊆ {a₁, …, a_k}`
  (S), so `(a_k)^{*1} = a_k < ϑ₁(Ω₂)` and L (`m = 1`, `α = a_k`, `γ = Ω₂`) gives `a_{k+1} < ϑ₁(Ω₂)`.
* (★3) **The term of `Ω₁·ω^b`.**  Let `s := Ω₁·ω^b ∈ Tᵗ` (`b < ε_{Ω₁+1}`).  By U its term is unique; `s` is additive
  principal (so not an `=NF`-sum) in `[Ω₁, Ω₂)`, so it is not a parameter (`< τ`), not a `ϑ₀`-term (values `< Ω₁`, L
  at `m = 0`), not a `ϑ_k`-term for `k ≥ 2` (values `≥ Ω₂`, L): it is `ϑ₁(ζ)` with `ζ ∈ Tᵗ ∩ Ω₃` (T).  If `ζ ≥ Ω₂`:
  `ζ = Ω₂`, or L (`α = Ω₂ < γ = ζ`, `(Ω₂)^{*1} = 0 < ϑ₁(ζ)`) gives `ϑ₁(Ω₂) < ϑ₁(ζ)`; either way `ε_{Ω₁+1} ≤ ϑ₁(Ω₂) ≤
  s < ε_{Ω₁+1}` (★2), impossible.  So `ζ < Ω₂` and `ϑ₁(ζ) = ϑ₁(b)` gives `ζ = b` (★1, injective on `[0, Ω₂)`).  So
  `s ∈ Tᵗ` iff `b ∈ Tᵗ` (⇐: T, third clause, `k = 1 ≥ 0`, `b ∈ Tᵗ ∩ Ω₃`), and then the term of `s` is `ϑ₁(b)`.
* (★4) **Parameters.**  By S (third clause, `k = 1 ≥ 0`), `Subᵗ₀(ϑ₁(b)) = {ϑ₁(b)} ∪ Subᵗ₀(b)`, and `ϑ₁(b) ≥ Ω₁ > τ`,
  so `Parᵗ(s) = Subᵗ₀(b) ∩ τ = Parᵗ(b)`.  Hence `s ∈ Tᵗ[σ]` iff `b ∈ Tᵗ[σ]` (P: `Tᵗ[σ] = {α ∈ Tᵗ | Parᵗ(α) ⊆ σ}`).
* (★5) **The value of `π`.**  For `b ∈ Tᵗ[σ]` (`b < Ω₃`): P, third clause (`k = 1 > 0`, `η = b ∈ Tᵗ[σ] ∩ Ω₃`),
  `π_{σ,τ}(s) = ϑ₁(π_{σ,τ}(b))`.  The `a_k` of ★2 lie in `Tᵗ[σ]` (`Parᵗ(a_k) ⊆ {0}`, S, `0 < σ`) and `π_{σ,τ}(a_k) =
  a_k` (P, first clause at `a₀ = 0`, third clause at `a_{k+1}`, by induction).  As `b < ε_{Ω₁+1} = sup_k a_k`, `b < a_k`
  for some `k`, so `π_{σ,τ}(b) < π_{σ,τ}(a_k) = a_k < ε_{Ω₁+1}` (5.3).  So by ★1 (over the base `σ`) `ϑ₁(π_{σ,τ}(b)) =
  Ω₁·ω^{π_{σ,τ}(b)}`, i.e. `π_{σ,τ}(Ω₁·ω^b) = Ω₁·ω^{π_{σ,τ}(b)}`. -/
axiom om1_opow_TB_all {σ τ b : Ordinal.{0}} (h : Bases σ τ)
    (hbE : ∀ e : Ordinal.{0}, InE e → Om1 < e → b < e) :
    (Om1 * ω ^ b ∈ TB τ σ ↔ b ∈ TB τ σ) ∧ (b ∈ TB τ σ → pi σ τ (Om1 * ω ^ b) = Om1 * ω ^ pi σ τ b)

/-- **`Ω₁·ω^b ∈ Tᵗ[σ]` and `π_{σ,τ}(Ω₁·ω^b) = Ω₁·ω^b` for `b < σ`** (formerly an axiom, the case `b < σ` of
[W07a] Def 5.1, first and third clauses): proved from `om1_opow_TB_all` (`b < σ < τ < Ω₁` lies below every
`ε`-number above `Ω₁`), `TB_inter_lt` (`b ∈ Tᵗ[σ]`) and `pi_lt` (`π_{σ,τ}(b) = b`). -/
theorem luOm1_opow_TB {σ τ b : Ordinal.{0}} (h : Bases σ τ) (hb : b < σ) :
    Om1 * ω ^ b ∈ TB τ σ ∧ pi σ τ (Om1 * ω ^ b) = Om1 * ω ^ b := by
  have hbE : ∀ e : Ordinal.{0}, InE e → Om1 < e → b < e :=
    fun _ _ he => hb.trans (h.2.2.1.trans (h.2.2.2.trans he))
  obtain ⟨h1, h2⟩ := om1_opow_TB_all h hbE
  have hbT : b ∈ TB τ σ := (TB_inter_lt h (hb.trans h.2.2.1)).2 hb
  refine ⟨h1.2 hbT, ?_⟩
  rw [h2 hbT, pi_lt h hb]

/-- **[W07a] Def 5.1**, third clause with `k = 1`, `η = 0`, and `ϑ₁(0) = Ω₁` ([W07a] remark
after Def 3.1: "`ϑᵐₙ(0) = Ωₘ` for `m < n`"): `Ω₁ ∈ Tᵗ[σ]` and `π_{σ,τ}(Ω₁) = Ω₁`.  Proved: the case `b = 0` of
`luOm1_opow_TB` (`Ω₁·ω⁰ = Ω₁`; `0 < σ` as `σ ∈ E`). -/
theorem pi_Om1 {σ τ : Ordinal.{0}} (h : Bases σ τ) : Om1 ∈ TB τ σ ∧ pi σ τ Om1 = Om1 := by
  have h0 : (0 : Ordinal.{0}) < σ := by
    have h1 : (0 : Ordinal.{0}) < ω ^ σ := opow_pos σ omega0_pos
    have h2 : ω ^ σ = σ := h.1
    rwa [h2] at h1
  have := luOm1_opow_TB h h0
  rwa [opow_zero, mul_one] at this

/-- **[W07a] Lemma 5.3 (b), (d)** (Cor 5.4): `π_{σ,τ}` is a strictly increasing map of `Tᵗ[σ]`
onto `T^σ`. -/
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

/-- **[W07a] Def 3.22, second clause** (text T): "`ξ, η ∈ T_m ⇒ ξ + η ∈ T_m`", for `m = 0` (Convention 3.25:
`T₀ = Tᵗ`).  Literal; the hypotheses on `τ` are the standing setting (`τ ∈ E` countable).  (Moved here unchanged
from `R2.CitedVz`, same name and statement.) -/
axiom vzT_add {τ x y : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hx : x ∈ Tset τ) (hy : y ∈ Tset τ) :
    x + y ∈ Tset τ

/-- **[W07a] Def 3.28 (the clause for sums), with §2 (`=ANF`, `=NF`), Def 3.22, the remark after Cor 3.24 and
Lemma 3.30**: for `x ∈ Tᵗ` with `τ ≤ x`, every additive component of `x` lies in `Tᵗ`, and
`Parᵗ(x) = ⋃ {Parᵗ(p) | p an additive component of x}`.

Literal texts ([W07a]):
* (S) Def 3.28: "We define sets of subterms `Subᵗ_m(α)` for `m < ω` and notations `α` in `Tᵗ` by recursion on the
  build up of `Tᵗ`: • `Subᵗ_m(α) := {α}` for parameters `α < τ` • `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ) ∪ Subᵗ_m(η)` for
  `ξ, η ∈ Tᵗ` s.t. `α =NF ξ + η > τ` • `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ)` if `k ≥ m`, `{α}` if `k < m`, for
  `α = ϑ_k(ξ)` where `ξ ∈ Tᵗ ∩ Ω_{k+2}`. … The set of parameters `< τ` used in the unique term denoting some
  `α ∈ Tᵗ` is denoted by `Parᵗ(α) := Subᵗ₀(α) ∩ τ`."
* (A) §2: "We write `ξ =ANF ξ₁ + ⋯ + ξₙ` if `ξ₁, …, ξₙ ∈ P`, `ξ₁ ≥ ⋯ ≥ ξₙ` (`ξ` given in additive normal form).  For
  convenience we also write `ξ =NF η + ρ` provided `η =ANF η₁ + ⋯ + ηₙ` for some `η₁, …, ηₙ`, and `ηₙ ≥ ρ ∈ P`."
* (T) Def 3.22: "`T_m` is defined inductively as follows: • `Ω_m ⊆ T_m` • `ξ, η ∈ T_m ⇒ ξ + η ∈ T_m`
  • `ξ ∈ T_m ∩ Ω_{k+2} ⇒ ϑ_k(ξ) ∈ T_m` for `k ≥ m`."
* (U) Remark after Cor 3.24: "each `T_m` again gives rise to a notation system with parameters from `Ω_m` that
  provides a unique term for every ordinal which is element of some `Tⁿ_m` where `n > m` (again refining the
  clause for ordinal addition as we did for the systems `Tⁿ_m`)".
* (L) Lemma 3.30: "For `m < ω` the function `ϑ_m ↾ Tᵗ ∩ Ω_{m+2}` is 1-1 and has values in `P ∩ [Ω_m, Ω_{m+1})`."
* (5.7) Proof of Lemma 5.7 (for `ξ ∈ Tᵗ ∩ Ω₁`, `ξ =ANF ξ₁ + ⋯ + ξₙ`): "Case 2: `ξ₁ ≥ τ`.  Then
  `Parᵗ(ξ) = ⋃_{j=1}^n Parᵗ(ξⱼ)`" (the same identity below `Ω₁`).

Our steps.  Let `x =ANF x₁ + ⋯ + xₙ` (`n ≥ 1`, as `x ≥ τ > 0`); the components `p ∈ comps x` are the distinct
`xⱼ`.  By (U) `x` has a unique term, built by the clauses of (T) with sums refined to `=NF`-sums.  If that term is
a parameter then `x < τ`, excluded.  If it is `ϑ_k(ξ)`, then `x ∈ P` (L), so `n = 1`, `comps x = [x]`, and both
claims are trivial (`x ∈ Tᵗ`).  Otherwise it is an `=NF`-sum `ξ + η > τ` with `ξ, η ∈ Tᵗ` (S); as `η ∈ P` and the
last component of `ξ` is `≥ η` (A), `η = xₙ` and `ξ =ANF x₁ + ⋯ + xₙ₋₁` (the additive normal form is unique), and
by (S) `Parᵗ(x) = ({x} ∪ Subᵗ₀(ξ) ∪ Subᵗ₀(η)) ∩ τ = Parᵗ(ξ) ∪ Parᵗ(xₙ)` (`x > τ`).  Here `ξ ≥ x₁ ≥ τ` (if
`x₁ < τ`, every component is `< τ ∈ P` and `x < τ`), so by induction on `n` the claim for `ξ` (`n − 1` summands)
gives `x₁, …, xₙ₋₁ ∈ Tᵗ` and `Parᵗ(ξ) = ⋃_{j<n} Parᵗ(xⱼ)`; and `xₙ = η ∈ Tᵗ`.  So every component lies in `Tᵗ`
and `Parᵗ(x) = ⋃ⱼ Parᵗ(xⱼ)`. -/
axiom Par_comps_eq {τ x : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hxT : x ∈ Tset τ) (hτx : τ ≤ x) :
    (∀ p ∈ comps x, p ∈ Tset τ) ∧ ∀ q, q ∈ Par τ x ↔ ∃ p ∈ comps x, q ∈ Par τ p

/-- **[W07a] Def 3.28** for `ξ =NF ξ₁ + ξ₂ > τ` (`Subᵗ(ξ) ⊇ Subᵗ(ξ₁) ∪ Subᵗ(ξ₂)`), applied to
the additive normal form `ξ =ANF ξ₁ + ⋯ + ξₙ ≥ τ` of an element of `Tᵗ`: a component `ξᵢ < τ` is
a parameter of `ξ`, and a component `ξᵢ ≥ τ` is a subterm of `ξ` (in `Tᵗ`, with
`Parᵗ(ξᵢ) ⊆ Parᵗ(ξ)`).  Proved from `Par_comps_eq` and `Par_lt` (`Parᵗ(ξᵢ) = {ξᵢ}` for `ξᵢ < τ`). -/
theorem Par_comps {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {x : Ordinal.{0}}
    (hxT : x ∈ Tset τ) (hτx : τ ≤ x) (hx1 : x < Om1) {p : Ordinal.{0}} (hp : p ∈ comps x) :
    (p < τ → p ∈ Par τ x) ∧ (τ ≤ p → p ∈ Tset τ ∧ Par τ p ⊆ Par τ x) := by
  obtain ⟨hT, hiff⟩ := Par_comps_eq hτ hτ1 hxT hτx
  refine ⟨fun hpτ => (hiff p).2 ⟨p, hp, ?_⟩, fun _ => ⟨hT p hp, fun q hq => (hiff q).2 ⟨p, hp, hq⟩⟩⟩
  rw [Par_lt hτ hτ1 hpτ]
  exact Finset.mem_singleton_self p

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
