import Googology.Trans.PoR.InaccPsi.R2.CitedVd
import Googology.Trans.PoR.InaccPsi.R2.CitedUv

set_option autoImplicit false

/-!
# Wilken 2007 §6: the subcase "`Γ > 0`, `Γ^* < α`" of Definition 6.2 at the levels `B₂ ≤ Γ = Ω₁·M < θ`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

One axiom, `xeVt_trL`: the twin of `R2.uvVt_trL` (the printed subcase "`Γ > 0` and `Γ^* < α`" of [W07a] Def 6.2, read
with Lemma 6.3) at every level `Γ = Ω₁·M` with `B₂ ≤ M < θ` (`B₂ = Uc.ucB = ψ_{Ω₂}(ε_{Ω₂+1})`, `θ = ConjT.th S =
ψ_{Ω₂}(Ω_ω)`), with the data read as in `R2.CitedVd` (Part II): through the `K⁽⁰⁾`-datum `d_S(M) = Vd.vdD S 0 M`
below a strongly critical `q ≤ α`.  Below `B₂` the same statement is `R2.uvVt_trL` (its range `Ω₁·M < B₂`, i.e. `M <
B₂`, is disjoint from `B₂ ≤ M`: `Xe.xe_twin_disj`).  The other subcase (`Γ^* ≥ α`, the twin of `R2.uvVt_trH`) is not
cited here (it is not used for constant levels).

Literal texts: (6.1), (6.2), (6.3), (C), (E), (4.5), (T), (Θ), (U), (S), (L) exactly as quoted in the module docstring
of `R2.CitedUv` (word for word, re-checked against the paper, pp. 132, 139–143, 148–149); the steps ◇M, ◇2 of
`R2.CitedUv` are used verbatim; (Q) Def 3.10 and Lemma 3.11, (T′) Def 3.22 as quoted in `R2.CitedVd`; the steps ◇θ,
◇V0, ◇m, ◇R, ◇S of `R2.CitedVd` (Part II) are used as written there.  For the reader the two texts the new steps
lean on:
* (6.2, the case used) "If `ϑᵗ(ξ) ∈ (α, α⁺)` we distinguish between three subcases.  `ξ` has a form `ξ = Γ + ρ`
  where `Γ < Δ` (cf. 4.5) and `α ≤ (Γ + ρ)^{*τ} < α⁺`. […] • `ϑᵗ(ξ)^{t^τ_α} := ϑ^α(Γ^{t^τ_α} + (−α + ρ)^{t^τ_α})`
  if `Γ > 0` and `Γ^* < α`"; and for `t^α_τ`: "If `ϑ^α(ξ) ∈ (α, ϑ^α(Δ))` […] `ξ` has a form `ξ = Γ + ρ` where `Γ < Δ`
  and `(Γ + ρ)^{*α} < ϑ^α(Δ)`. […] • `ϑ^α(ξ)^{t^α_τ} := ϑᵗ(Γ^{t^α_τ} + α + ρ^{t^α_τ})` if `Γ > 0` and `Γ^* < α`".
* (6.3) Lemma 6.3: "We have • `α⁺ = ϑ^α(Δ)`, • the restriction of `t^τ_α` to `Tᵗ_{α⁺}` is the identity, and • the
  restriction of `t^α_τ` to `T^α_{α⁺}` is the identity."

Notation.  As in `R2.CitedUv`: `Δ := Δₙ`, `α := Dl τ n = ϑᵗ(Δₙ)`, `α⁺ := Dp τ n = ϑᵗ(Δₙ + 1)`; `Γ := Ω₁·M`; `β`
ranges over the two bases `τ` and `α`; `P₀(x)` = the parts of level `0` of `x ∈ Tⁿ₁` (Q).

Our steps.  Only the steps ◇K and ◇* of `R2.CitedUv` change (they read the canonical term of a code below `B₂`); the
steps ◇M, ◇2, ◇ξ, ◇3, ◇4 are those of `R2.CitedUv` with the bound `B₂` replaced by `θ` and ◇* replaced by ◇*‴ below.
* (◇K‴) **The term of `Γ` and its `=NF` components.**  `M ∈ [B₂, θ)`, so `M < θ` and `Γ = Ω₁·M < θ` (`θ` is strongly
  critical above `Ω₁`); by ◇θ of `R2.CitedVd`, `Γ ∈ Tⁿ₁` for `n` large, with a unique term (U).  `M ≥ B₂ ≥ 1`, and `Γ =
  Ω₁·M = Σ ω^{Ω₁ + m_i}·k_i` over the Cantor terms `ω^{m_i}·k_i` of `M`, so every `=NF` component of `Γ` is additive
  principal in `[Ω₁, Ω₂)`, i.e. a `ϑ₁`-term (L: `ϑ₀`-values are `< Ω₁`, `ϑ_k`-values `≥ Ω₂` for `k ≥ 2`; the remark
  of C).  Hence `Γ` has no countable additive component, and for `ρ < Ω₁` the decomposition of C of `ξ = Γ + ρ` is
  `Γ + ρ` (`Ω₁ ∣ Γ`), with `ξ < Ω₂` (`θ < Ω₂`).
* (◇R‴) **The parts of `Γ`.**  By ◇R of `R2.CitedVd`: `P₀(Γ) ∪ ω = P₀(M) ∪ ω` (`Ω₁·ω^g = ω^{Ω₁+g}` is `ω^g` or a
  `ϑ₁`-term with the parts of `g`), and `P₀(M) ⊆ v ⇔ d_S(M) < v` for every strongly critical `v ≤ Ω₁` (◇R, last
  sentence; ◇V0).  So **`d_S(M) < q` for a strongly critical `q` gives `P₀(Γ) ⊆ q`** (the finite elements are `< q`).
* (◇*‴) **`d_S(M) < q ≤ α` with `q` strongly critical gives `Γ^{*β} < α` for both bases `β ∈ {τ, α}`.**  By ◇R‴,
  `P₀(Γ) ⊆ q ⊆ α`.  The term of `Γ` over a base `β` (T, U) is obtained from its `Tⁿ₁`-term by writing every element `c`
  of `P₀(Γ)` (Q: the additive components of the maximal countable subterms) as a term of `T^β`: a parameter if `c < β`,
  else its unique term of `T^β ∩ Ω₁` (◇M; `α ∈ Tᵗ ∩ Ω₁`, an initial segment, Θ).  By S, `Sub^β_0(Γ)` consists of the
  sum nodes and the `ϑ_k`-nodes, `k ≥ 1`, of this term (all `≥ Ω₁`, so not in `[β, Ω₁)`) and of `Sub^β_0(c)` for `c ∈
  P₀(Γ)`.  For `c ∈ P₀(Γ)`, `c < α`: a parameter `c < β` has `Sub = {c}`; a term `c ≥ β` has as subterms its `=NF`
  components (`≤ c`) and the subterms of the arguments `ζ` of its `ϑ₀`-subterms `ϑ₀(ζ) ≤ c`, whose `P`-parts in `[β,
  Ω₁)` are `≤ ζ^{*β} < ϑ₀(ζ) ≤ c` (L).  So every element of `P ∩ Sub^β_0(Γ) ∩ [β, Ω₁)` is `≤` some `c ∈ P₀(Γ)`, `c <
  α`, and `Γ^{*β} < α` (S: `Γ^{*β} = max(P₀^β(Γ) ∪ {0})`).  (Over `β = α` every `c < α` is a parameter and `Γ^{*α} =
  0`.)  Only this direction of ◇* of `R2.CitedUv` is used in ◇3 and ◇4.
* (◇ξ‴) ◇ξ of `R2.CitedUv` with "`Γ < B₂ < Ω₂`" replaced by "`Γ < θ < Ω₂`" (◇K‴); the rest verbatim (it uses only T,
  L, S, 4.5, 6.1, ◇2).
* (◇3‴) **Part (i), `t^α_τ`.**  ◇3 of `R2.CitedUv` verbatim, with ◇*‴ (`β = α`) for ◇*: `ξ := Γ + ρ ∈ T^α`, `b :=
  ϑ^α(ξ) < α⁺`; `α < b` (E over the base `α`, `Γ > 0`); `b ∈ (α, ϑ^α(Δ))` (◇2), the second case of `t^α_τ`, `Γ ≤ ξ <
  Δ`, `ξ^{*α} < ϑ^α(Δ)` (◇ξ‴); `Γ^{*α} < α` (◇*‴), `Γ > 0`: the second subcase, `b^{t^α_τ} := ϑᵗ(Γ^{t^α_τ} + α +
  ρ^{t^α_τ})`; `b, Γ, ρ ∈ T^α_{α⁺}` (◇ξ‴), so by 6.3 (third item) and the remark after 6.2, `b = ϑᵗ(Γ + α + ρ)` and
  `Γ + (α + ρ) ∈ Tᵗ`.
* (◇4‴) **Part (ii), `t^τ_α`.**  ◇4 of `R2.CitedUv` verbatim, with ◇*‴ (`β = τ`) for ◇*: `ξ' := Γ + (α + ρ) ∈ Tᵗ`,
  `b' := ϑᵗ(ξ') < α⁺`; `α < b'` (L, second disjunct: the first component of `α + ρ` is `≥ α` and is a component of
  `ξ'` since the components of `Γ` are `ϑ₁`-terms `≥ Ω₁`, ◇K‴); the second case of `t^τ_α`, `Γ < Δ` (4.5); `Γ^{*τ} <
  α` (◇*‴): the second subcase, `b'^{t^τ_α} := ϑ^α(Γ^{t^τ_α} + (−α + ρ')^{t^τ_α})`, `−α + ρ' = ρ`; `b', Γ, ρ ∈
  Tᵗ_{α⁺}` (◇ξ‴), so by 6.3 (second item) `b' = ϑ^α(Γ + ρ)` and `Γ + ρ ∈ T^α`.
* (◇S‴) **`S`.**  The hypothesis names one `S`; by ◇S of `R2.CitedVd` (`d_S(M) < q ⇔ P₀(M) ⊆ q`, `θ = θ₁`) neither the
  hypothesis nor the conclusion depends on it.
* (Non-vacuity) Take `M = B₂`: `Ω₁·B₂ = B₂` (`B₂` an `ε`-number `> Ω₁`), `d_S(B₂)` lies below every strongly critical
  `q` (the Lean theorem `Ww.ww_B_dat`), `B₂ < θ` (`Vd.vd_B_lt_th`).  `sup_n Δₙ = θ₁ = θ` (Θ, ◇θ), so `B₂ < Δₙ` for `n`
  large; with `τ ≥ Γ₀` take `q = Γ₀ ≤ τ < α`.  Then `B₂ ∈ T^α` (`P₀(B₂)` finite, 3.11 (b)), `B₂^{*α} = 0` and `B₂ <
  Δ`, so `ϑ^α(B₂) < ϑ^α(Δ) = α⁺` (L, 6.3): part (i) applies with `ρ = 0`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Googology.Notation.InaccPsi

/-- **[W07a] Definition 6.2 (p. 148) and Lemma 6.3 (p. 149), the subcase "`Γ > 0` and `Γ^* < α`" of both
translations, at every level `Γ = Ω₁·M` with `B₂ ≤ M < θ`, data read through the `K⁽⁰⁾`-datum below a strongly
critical `q ≤ α`; with the remark after Def 6.2 (p. 149), Convention 4.1 and Lemma 4.3 (p. 142), Lemma 4.5 (p. 143),
Definition 6.1 (p. 148), Definition 3.10 and Lemma 3.11 (b), Definition 3.22, Theorem 3.23 (p. 139), the Remark after
Corollary 3.24 (p. 140), Definition 3.28 (p. 141), Lemma 3.30 (p. 142)** (texts of the module docstring).  For `τ ∈ E
∩ Ω₁`, `n ≥ 1`, `α := Dl τ n`, `α⁺ := Dp τ n`, `B₂ ≤ M < θ`, a strongly critical `q ≤ α` with `d_S(M) < q`, and `ρ <
Ω₁`: (i) if `Ω₁·M + ρ ∈ T^α` and `ϑ^α(Ω₁·M + ρ) < α⁺` then `Ω₁·M + (α + ρ) ∈ Tᵗ` and `ϑ^α(Ω₁·M + ρ) = ϑᵗ(Ω₁·M + (α +
ρ))`; (ii) if `Ω₁·M + (α + ρ) ∈ Tᵗ` and `ϑᵗ(Ω₁·M + (α + ρ)) < α⁺` then `Ω₁·M + ρ ∈ T^α` and `ϑᵗ(Ω₁·M + (α + ρ)) =
ϑ^α(Ω₁·M + ρ)`.

Our steps: ◇K‴, ◇R‴, ◇*‴, ◇ξ‴, ◇3‴ (part (i)), ◇4‴ (part (ii)), ◇S‴ of the module docstring, with ◇M, ◇2 of
`R2.CitedUv` and ◇θ, ◇V0, ◇m, ◇R, ◇S of `R2.CitedVd`. -/
axiom xeVt_trL {S : InaccSeq.{0}} {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {n : ℕ} (hn : 1 ≤ n)
    {M ρ q : Ordinal.{0}} (hMB : Uc.ucB ≤ M) (hMθ : M < ConjT.th S) (hq : SC q) (hqα : q ≤ Dl τ n)
    (hMq : Vd.vdD S 0 M < q) (hρ1 : ρ < Om1) :
    (Om1 * M + ρ ∈ Tset (Dl τ n) → vt (Dl τ n) (Om1 * M + ρ) < Dp τ n →
      Om1 * M + (Dl τ n + ρ) ∈ Tset τ ∧ vt (Dl τ n) (Om1 * M + ρ) = vt τ (Om1 * M + (Dl τ n + ρ))) ∧
    (Om1 * M + (Dl τ n + ρ) ∈ Tset τ → vt τ (Om1 * M + (Dl τ n + ρ)) < Dp τ n →
      Om1 * M + ρ ∈ Tset (Dl τ n) ∧ vt τ (Om1 * M + (Dl τ n + ρ)) = vt (Dl τ n) (Om1 * M + ρ))

end Googology.Trans.PoR.InaccPsi.R2
