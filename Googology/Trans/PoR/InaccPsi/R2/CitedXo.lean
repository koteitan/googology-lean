import Googology.Trans.PoR.InaccPsi.R2.CitedXe

set_option autoImplicit false

/-!
# Wilken 2007 §6: the subcase "`Γ^* ≥ α`" of Definition 6.2 at the levels `B₂ ≤ Γ = Ω₁·M < θ`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

One axiom, `xoVt_trH`: the twin of `R2.uvVt_trH` (the printed subcase "`Γ^* ≥ α`" of [W07a] Def 6.2, read with Lemma
6.3) at every level `Γ = Ω₁·M` with `B₂ ≤ M < θ` (`B₂ = Uc.ucB = ψ_{Ω₂}(ε_{Ω₂+1})`, `θ = ConjT.th S =
ψ_{Ω₂}(Ω_ω)`).  It is the other subcase of `R2.xeVt_trL`; it is needed for levels whose leaves move (the leaves of
a level that are nested `ϑ`-terms in `[α, Ω₁)`).  The data are read as in `R2.CitedVd` (Part II) through the
`K⁽⁰⁾`-datum `d_S(M) = Vd.vdD S 0 M`, at a strongly critical `q` with `α ≤ q ≤ d_S(M)` (the datum is read only at
strongly critical points, ◇R of `R2.CitedVd`).  Below `B₂` the same statement is `R2.uvVt_trH` (with `ucDat`).

Literal texts: (6.1), (6.2), (6.3), (C), (E), (4.5), (T), (Θ), (U), (S), (L) exactly as quoted in the module
docstring of `R2.CitedUv` (word for word, pp. 132, 139–143, 148–149); (Q) Def 3.10 and Lemma 3.11, (T′) Def 3.22
as quoted in `R2.CitedVd`.  The case used here, from (6.2) as quoted there: "If `ϑᵗ(ξ) ∈ (α, α⁺)` we distinguish
between three subcases.  `ξ` has a form `ξ = Γ + ρ` where `Γ < Δ` (cf. 4.5) and `α ≤ (Γ + ρ)^{*τ} < α⁺`. […] •
`ϑᵗ(ξ)^{t^τ_α} := ϑ^α(Γ^{t^τ_α} + ρ^{t^τ_α})` if `Γ^* ≥ α`"; and for `t^α_τ`: "If `ϑ^α(ξ) ∈ (α, ϑ^α(Δ))` […]
`ξ` has a form `ξ = Γ + ρ` where `Γ < Δ` and `(Γ + ρ)^{*α} < ϑ^α(Δ)`. […] • `ϑ^α(ξ)^{t^α_τ} := ϑᵗ(Γ^{t^α_τ} +
ρ^{t^α_τ})` if `Γ^* ≥ α`"; (6.3) "We have • `α⁺ = ϑ^α(Δ)`, • the restriction of `t^τ_α` to `Tᵗ_{α⁺}` is the
identity, and • the restriction of `t^α_τ` to `T^α_{α⁺}` is the identity."  After 6.2 (p. 149): "Obviously in both
definitions the respective case distinctions are disjoint and complete.  It is also easy to see that the assigned
ordinals belong to the respective notation system."

Notation.  As in `R2.CitedUv`: `Δ := Δₙ`, `α := Dl τ n = ϑᵗ(Δₙ)`, `α⁺ := Dp τ n = ϑᵗ(Δₙ + 1)`; `Γ := Ω₁·M`; `β`
ranges over the two bases `τ` and `α`; `P₀(x)` = the parts of level `0` of `x ∈ Tⁿ₁` (Q).

Our steps.  The steps ◇M, ◇2 of `R2.CitedUv`, the steps ◇K‴, ◇R‴, ◇ξ‴ of `R2.CitedXe`, and the steps ◇θ, ◇V0, ◇m, ◇R,
◇S of `R2.CitedVd` (Part II) are used as written there; ◇* is replaced by:
* (◇*⁻) **`q` strongly critical with `α ≤ q ≤ d_S(M)` gives `Γ^{*β} ≥ α` for both bases `β ∈ {τ, α}` (whenever `Γ ∈
  T^β`).**  `d_S(M) < Ω₁` (`Vd.vdD_lt_Om1`, `M < θ`), so `q < Ω₁`.  By ◇R of `R2.CitedVd` (last sentence: `P₀(M) ⊆ v ⇔
  d_S(M) < v` for every strongly critical `v ≤ Ω₁`) at `v = q`: not `d_S(M) < q`, so `P₀(M) ⊄ q`: some `c ∈ P₀(M)`
  has `c ≥ q ≥ α`.  `c` is not finite (`α > ω`, E, ◇2), so `c ∈ P₀(Γ)` (◇R‴: `P₀(Γ) ∪ ω = P₀(M) ∪ ω`).  `c ∈ P ∩
  [Ω₀, Ω₁)` is a countable part of the `Tⁿ₁`-term of `Γ` (Q).  The term of `Γ` over `β` is obtained from its `Tⁿ₁`-term
  by writing every element of `P₀(Γ)` as a term of `T^β` (◇*‴ of `R2.CitedXe`; it exists since `Γ ∈ T^β`, and is the
  unique term of `T^β ∩ Ω₁` for the elements `≥ β`, ◇M with U); `c ≥ α ≥ β`, so `c` is a term of `T^β ∩ [β, Ω₁)`, and
  `c ∈ Sub^β_0(Γ)` (S: the subterms of `Γ` contain its countable parts, `Subᵗ_m(α) ∋ α`).  So `c ∈ Sub^β_0(Γ) ∩ P ∩
  [Ω₀, Ω₁)` with `Ω₀ = β` over the base `β` (T), and `Γ^{*β} = max(P^β_0(Γ) ∪ {0}) ≥ c ≥ α` (S).  As in `R2.CitedUv`
  (◇*, last sentence) the star printed without a base gives the same condition over `τ` and over `α` here.
* (◇3⁻) **Part (i), `t^α_τ`.**  ◇3 of `R2.uvVt_trH` verbatim, with ◇*⁻ (`β = α`) for ◇* and ◇ξ‴ for ◇ξ: `ξ := Γ + ρ ∈
  T^α`, `b := ϑ^α(ξ) < α⁺`; `α < b` (E over the base `α`, `Γ > 0`); `b ∈ (α, ϑ^α(Δ))` (◇2), the second case of
  `t^α_τ`, `Γ ≤ ξ < Δ`, `ξ^{*α} < ϑ^α(Δ)` (◇ξ‴); `Γ^{*α} ≥ α` (◇*⁻): the third subcase, `b^{t^α_τ} := ϑᵗ(Γ^{t^α_τ} +
  ρ^{t^α_τ})`; `b, Γ, ρ ∈ T^α_{α⁺}` (◇ξ‴), so by 6.3 (third item) and the remark after 6.2 `b = ϑᵗ(Γ + ρ)` and `Γ + ρ
  ∈ Tᵗ` (T, second clause).
* (◇4⁻) **Part (ii), `t^τ_α`.**  ◇4 of `R2.uvVt_trH` verbatim, with ◇*⁻ (`β = τ`): `ξ := Γ + ρ ∈ Tᵗ`, `b := ϑᵗ(ξ) <
  α⁺`; `α ≤ Γ^{*τ} ≤ ξ^{*τ}` (◇*⁻; `P₀(Γ) ⊆ P₀(ξ)`, S), so L (`m = 0`, second disjunct) gives `α < b`; the second case
  of `t^τ_α`, `ξ = Γ + ρ` the decomposition of C (◇K‴: `Ω₁ ∣ Γ`), `Γ < Δ` (4.5), `α ≤ ξ^{*τ} < b < α⁺` (L); the third
  subcase, `b^{t^τ_α} := ϑ^α(Γ^{t^τ_α} + ρ^{t^τ_α})`; `b, Γ, ρ ∈ Tᵗ_{α⁺}` (◇ξ‴), so by 6.3 (second item) and the
  remark `b = ϑ^α(Γ + ρ)` and `Γ + ρ ∈ T^α`.
* (◇S⁻) **`S`.**  The hypothesis names one `S`; by ◇S of `R2.CitedVd` (`d_S(M) < q ⇔ P₀(M) ⊆ q` for strongly critical
  `q ≤ Ω₁`, `θ = θ₁`) neither the hypothesis nor the conclusion depends on it.
* (Non-vacuity) For `n ≥ 2`, `Δₙ ≥ Δ₂ = ϑ₁(Ω₂) = ε_{Ω₁+1}` is an `ε`-number above `Ω₁`, so `Δₙ = Ω₁·Δₙ`, and `α =
  ϑᵗ(Δₙ)` is strongly critical: for `a', z < α`, `Ω₁·a' + z < Δₙ` and its parts are `< α`, so `φ(a', z) ≤ ϑᵗ(Ω₁·a' +
  z) < α` (◇m of `R2.CitedVd`, L).  Take `q = α` and `M = B₂ + α`: `d_S(B₂ + α) ≥ α` (the Lean theorem
  `Xo.xo_dat_ge`), `B₂ + α < θ`; for `n` large `Ω₁·M < Δₙ` (`sup_n Δₙ = θ`, Θ, ◇θ) and `Γ^{*τ} = α < α⁺`, so
  `ϑᵗ(Γ) < ϑᵗ(Δₙ + 1) = α⁺` (L): part (ii) applies with `ρ = 0`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Googology.Notation.InaccPsi

/-- **[W07a] Definition 6.2 (p. 148) and Lemma 6.3 (p. 149), the subcase "`Γ^* ≥ α`" of both translations, at every
level `Γ = Ω₁·M` with `B₂ ≤ M < θ`, data read through the `K⁽⁰⁾`-datum at a strongly critical `q` with `α ≤ q ≤
d_S(M)`; with the remark after Def 6.2 (p. 149), Convention 4.1 and Lemma 4.3 (p. 142), Lemma 4.5 (p. 143),
Definition 6.1 (p. 148), Definition 3.10 and Lemma 3.11 (b), Definition 3.22, Theorem 3.23 (p. 139), the Remark after
Corollary 3.24 (p. 140), Definition 3.28 (p. 141), Lemma 3.30 (p. 142)** (texts of the module docstring).  For `τ ∈ E
∩ Ω₁`, `n ≥ 1`, `α := Dl τ n`, `α⁺ := Dp τ n`, `B₂ ≤ M < θ`, a strongly critical `q` with `α ≤ q ≤ d_S(M)`, and `ρ <
Ω₁`: (i) if `Ω₁·M + ρ ∈ T^α` and `ϑ^α(Ω₁·M + ρ) < α⁺` then `Ω₁·M + ρ ∈ Tᵗ` and `ϑ^α(Ω₁·M + ρ) = ϑᵗ(Ω₁·M + ρ)`; (ii)
if `Ω₁·M + ρ ∈ Tᵗ` and `ϑᵗ(Ω₁·M + ρ) < α⁺` then `Ω₁·M + ρ ∈ T^α` and `ϑᵗ(Ω₁·M + ρ) = ϑ^α(Ω₁·M + ρ)`.

Our steps: ◇*⁻, ◇3⁻ (part (i)), ◇4⁻ (part (ii)), ◇S⁻ of the module docstring, with ◇M, ◇2 of `R2.CitedUv`, ◇K‴,
◇R‴, ◇ξ‴ of `R2.CitedXe` and ◇θ, ◇V0, ◇m, ◇R, ◇S of `R2.CitedVd`. -/
axiom xoVt_trH {S : InaccSeq.{0}} {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {n : ℕ} (hn : 1 ≤ n)
    {M ρ q : Ordinal.{0}} (hMB : Uc.ucB ≤ M) (hMθ : M < ConjT.th S) (hq : SC q) (hαq : Dl τ n ≤ q)
    (hqM : q ≤ Vd.vdD S 0 M) (hρ1 : ρ < Om1) :
    (Om1 * M + ρ ∈ Tset (Dl τ n) → vt (Dl τ n) (Om1 * M + ρ) < Dp τ n →
      Om1 * M + ρ ∈ Tset τ ∧ vt (Dl τ n) (Om1 * M + ρ) = vt τ (Om1 * M + ρ)) ∧
    (Om1 * M + ρ ∈ Tset τ → vt τ (Om1 * M + ρ) < Dp τ n →
      Om1 * M + ρ ∈ Tset (Dl τ n) ∧ vt τ (Om1 * M + ρ) = vt (Dl τ n) (Om1 * M + ρ))

end Googology.Trans.PoR.InaccPsi.R2
