import Googology.Trans.PoR.InaccPsi.R2.CitedLu
import Googology.Trans.PoR.InaccPsi.R2.CitedEv

set_option autoImplicit false

/-!
# Wilken 2007, Lemma 3.27 / Corollary 3.24: `ϑ₀(ϑ₁(⋯ϑₙ(0)⋯))` is a `ϑᵗ`-value at an argument `≥ Ω₁·Ω₁`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

One axiom, `zfDl_vt`: for `n ≥ 2` the constant `Dl τ n` (`R2.Dl`, "`ϑ₀(⋯ϑₙ(0)⋯)` over `τ`", [W07a] Lemma 3.27) is
`ϑᵗ(Δ)` (`R2.vt`, `ϑ₀ = ϑᵗ`, Convention 3.25) for an argument `Δ ∈ Tᵗ ∩ Ω₂` with `Ω₁·Ω₁ ≤ Δ`.  With the Lean
theorem `Zf.zf_vt_SC` (a `ϑᵗ`-value at a level `≥ Ω₁` is strongly critical, from `R2.vdVt_lt` and `Gl.glA_veb_le`)
it gives `Za.ZaDlSC` (`Zf.zfDlSC`).  `Dl` is a constant of `R2.Cited` without definition; this axiom only identifies
its value as a `ϑᵗ`-value, with the argument bound read off the printed term.

Literal texts ([W07a]):
* (D) Definition 3.1 (p. 133): "Note that we have `ϑ^n_m(0) = Ω_m` for `m < n`."
* (T) Definition 3.22 (p. 139): "We define a function `ϑ_m : θ_{m+1} → Ω_{m+1}` by `ϑ_m(α) := ϑ^n_m(α)` for `α <
  θ_{m+1}` where `n > m` is large enough to satisfy `α < θ^n_{m+1}`.  `T_m` is defined inductively as follows: •
  `Ω_m ⊆ T_m` • `ξ, η ∈ T_m ⇒ ξ + η ∈ T_m` • `ξ ∈ T_m ∩ Ω_{k+2} ⇒ ϑ_k(ξ) ∈ T_m` for `k ≥ m`."
* (C) Convention 3.25 (p. 140): "In our setting the ordinal notations are relativized to `τ`.  Later on we will
  indicate this explicitly in writing `ϑ^τ` and `T^τ` instead of `ϑ₀` and `T₀`."  (§3, p. 133: "Let `τ ∈ {1} ∪ E`
  and set `Ω₀ := τ`.")
* (H) Lemma 3.27 (p. 141): "For `α < T^τ ∩ Ω₁`, `ht^τ(α) = min{n | α < ϑ₀(⋯(ϑₙ(0))⋯)}`."
* (K) Corollary 3.24 (p. 140): "For `m < n` we have `Tⁿ_m ∩ Ω_{m+1} = θⁿ_m = ϑ_m(⋯(ϑ_n(0))⋯)`."
* (S) Definition 3.28 (p. 141): "`Sub^τ_m(α) := {α} ∪ Sub^τ_m(ξ)` if `k ≥ m`, … for `α = ϑ_k(ξ)` where `ξ ∈ T^τ ∩
  Ω_{k+2}`.  We define the additive principal parts of level `m` of `α ∈ T^τ` by `P_m(α) := Sub^τ_m(α) ∩ P ∩ [Ω_m,
  Ω_{m+1})` and `α^{*m} := max(P_m(α) ∪ {0})`."  (with "`Sub^τ_m(α) := {α}` for parameters `α < τ`")
* (L) Lemma 3.30 (p. 142): "For `m < ω` the function `ϑ_m ↾ T^τ ∩ Ω_{m+2}` is 1-1 and has values in `P ∩ [Ω_m,
  Ω_{m+1})`.  Let `α, γ ∈ T^τ ∩ Ω_{m+2}`.  Then `α^{*m} < ϑ_m(α)` and `ϑ_m(α) < ϑ_m(γ) ⇔ (α < γ ∧ α^{*m} < ϑ_m(γ))
  ∨ ϑ_m(α) ≤ γ^{*m}`."
* (B) Definition 3.4 (p. 134): "Let `α ↦ ω̄_α` be the enumeration function of the additive principle numbers which
  are not epsilon numbers."
* (W) Lemma 4.2 (p. 142): "For any `m < ω` and any `α < Ω_{m+1}` we have `ϑ_m(1 + α) = ω̄_{Ω_m+α}`."

Our steps (`n ≥ 2`, `τ ∈ E ∩ Ω₁`, `Ω₀ = τ`, `T₀ = Tᵗ`, `ϑ₀ = ϑᵗ` by C).
* (◇1) **The term.**  Put `ξ := ϑ₂(⋯(ϑₙ(0))⋯)` (for `n = 2`, `ξ = ϑ₂(0)`) and `Δ := ϑ₁(ξ)`; then the ordinal of (H)
  and (K) (`m = 0`) is `ϑ₀(Δ)`, which is `Dl τ n` (the constant names exactly this ordinal) and `vt τ Δ` (C).
* (◇2) **`Δ ∈ Tᵗ ∩ Ω₂`.**  `0 ∈ Ω₀ = τ ⊆ T₀` (T, first clause; `τ > 0`).  `0 ∈ T₀ ∩ Ω_{n+2}`, so `ϑₙ(0) ∈ T₀` (T,
  third clause, `k = n ≥ 0`).  If `ϑ_{k+1}(ζ) ∈ T₀` then its value is in `[Ω_{k+1}, Ω_{k+2})` (L, `m = k + 1`), so
  it is in `T₀ ∩ Ω_{k+2}` and `ϑ_k(ϑ_{k+1}(ζ)) ∈ T₀` (T, third clause).  Descending from `k = n − 1` to `k = 1`:
  `ξ ∈ T₀ ∩ [Ω₂, Ω₃)` (for `n = 2`, `ξ = ϑ₂(0) = Ω₂` by D and T) and `Δ = ϑ₁(ξ) ∈ T₀ ∩ [Ω₁, Ω₂)` (L, `m = 1`).
* (◇3) **`ϑ₁(Ω₁) < Δ`.**  `Ω₁ = ϑ₁(0)` (D, T) is in `T₀ ∩ Ω₃` (T, third clause, `k = 1`).  Apply L with `m = 1`,
  `α = Ω₁`, `γ = ξ`: `α < γ` (`Ω₁ < Ω₂ ≤ ξ`); `Sub^τ₁(ϑ₁(0)) = {ϑ₁(0)} ∪ Sub^τ₁(0) = {Ω₁, 0}` (S, `k = 1 ≥ m = 1`;
  `0 < τ` a parameter), so `P₁(Ω₁) = {Ω₁}` and `α^{*1} = Ω₁`; `ϑ₁(ξ) ∈ [Ω₁, Ω₂)` (L) and `ϑ₁(ξ) ≠ ϑ₁(0) = Ω₁` (L,
  1-1, `ξ ≠ 0`), so `α^{*1} = Ω₁ < ϑ₁(ξ)`.  The first disjunct of L holds: `ϑ₁(Ω₁) < ϑ₁(ξ) = Δ`.
* (◇4) **`Ω₁·Ω₁ ≤ ϑ₁(Ω₁)`.**  `1 + Ω₁ = Ω₁ < Ω₂`, so W (`m = 1`, `α = Ω₁`) gives `ϑ₁(Ω₁) = ϑ₁(1 + Ω₁) = ω̄_{Ω₁+Ω₁}`.
  `ω̄` enumerates a subset of the additive principal numbers, whose enumeration is `ν ↦ ω^ν`; so `ω̄_ν ≥ ω^ν` for
  every `ν` (B; an enumeration of a subset is pointwise at least the enumeration of the whole class).  So
  `ϑ₁(Ω₁) ≥ ω^{Ω₁+Ω₁} = ω^{Ω₁}·ω^{Ω₁} = Ω₁·Ω₁` (`Ω₁ = ω^{Ω₁}`, `Ω₁` is an `ε`-number).
* (◇5) **Conclusion.**  `Δ ∈ Tᵗ` (◇2), `Ω₁·Ω₁ ≤ ϑ₁(Ω₁) < Δ` (◇3, ◇4), `Δ < Ω₂` (◇2), and `Dl τ n = ϑᵗ(Δ) = vt τ Δ`
  (◇1).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

/-- **[W07a] Lemma 3.27, Corollary 3.24, Definitions 3.1, 3.4, 3.22, 3.28, Convention 3.25, Lemmas 3.30, 4.2** (texts
H, K, D, B, T, S, C, L, W of the module docstring): for `τ ∈ E ∩ Ω₁` and `n ≥ 2`, `Dl τ n = ϑ₀(⋯(ϑₙ(0))⋯) = ϑᵗ(Δ)`
with `Δ = ϑ₁(⋯(ϑₙ(0))⋯) ∈ Tᵗ ∩ Ω₂` and `Ω₁·Ω₁ ≤ Δ`.

Our steps: ◇1 (the term), ◇2 (`Δ ∈ Tᵗ ∩ Ω₂`, from D, T, L), ◇3 (`ϑ₁(Ω₁) < Δ`, from D, T, S, L), ◇4 (`Ω₁·Ω₁ ≤
ϑ₁(Ω₁)`, from W, B), ◇5 of the module docstring. -/
axiom zfDl_vt {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {n : ℕ} (hn : 2 ≤ n) :
    ∃ Δ : Ordinal.{0}, Δ ∈ Tset τ ∧ Om1 * Om1 ≤ Δ ∧ Δ < OmTwo ∧ Dl τ n = vt τ Δ

end Googology.Trans.PoR.InaccPsi.R2
