import Googology.Trans.PoR.InaccPsi.R2.TcFn

set_option autoImplicit false

/-!
# Cited facts of Wilken 2007, as axioms, ONCE for every level `Γ_{Ω₁+1} ≤ μ < Γ'` and every code in `[Γ_{Ω₁+1}, Γ')`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

Same conventions as `R2.CitedSy` (`Ω₁ = Om1`, `Ω₂ = OmTwo`, `Tset τ = Tᵗ`, `Par τ = Parᵗ`, `vt τ = ϑᵗ = ϑ₀`, `pi σ τ =
π_{σ,τ}`, `TB τ σ = Tᵗ[σ]`, every base `τ` a countable `ε`-number, `φ(a, c) = veblen a c`, `E₁ = ε_{Ω₁+1}`).
`G := Γ_{Ω₁+1} = Gg.ggGam` (the least strongly critical ordinal above `Ω₁`), `G' := lgGam'` (the least strongly
critical ordinal above `G`).  A **code** is an ordinal `z < G'`.  Its **leaves** are read by `Tc.tcDat`: as by
`Ss.ssDat` in `R2.CitedSy`, with one more atom: `G` has no leaf.  (In `(Ω₁, G')` the only strongly critical ordinal is
`G`; every other `ε`-number `z` there is `φ(a, c)` with `a = invVeblen₁ z < z`, `c = invVeblen₂ z < z`.)  `tcDatL μ =
tcDat(Ω₁ + μ) = tcDat μ` for `μ ≥ E₁`; `tcDat = ssDat` below `G` (`Tc.tcDat_eq_ss`).

What is **not** restated (checked first, every `Cited*` file of `R2`): `R2.CitedSy` (the levels `E₁ < μ < G` and the
codes below `G`: the packages `Sv.SvCit G`, `Sv.SvCitPi G`), `R2.CitedSs` (the level `E₁`), `R2.CitedRj`, `R2.CitedRk`
(levels `< E₁`), `R2.CitedLq`, `R2.CitedLg`, `R2.CitedLv`, `R2.CitedLu`, `R2.CitedLz`, `R2.CitedLt`, `R2.CitedXt`,
`R2.CitedSi`, `R2.CitedEps`, `R2.CitedEv`, `R2.CitedW`, `R2.CitedVz`, `R2.Cited`, `R2.CitedL`, `R2.CitedR1`,
`R2.CitedCore`, `R2.CitedC09`, `R2.CitedBr`.  None of them mentions a level `≥ G`, the ordinal `G` or an ordinal in
`(G, G')` in `Tᵗ`, or `π` there.  The axioms below are exactly the fields of the hypothesis packages `Tc.TcCit G'`
(five) and `Tc.TcCitPi G'` (three).  The first sub-range `μ < ε_{G+1}` needs ◇G and ◇N only (its codes are built from
`Ω₁`, `G = ϑ₁(Ω₂²)`, the codes below `G` and countable leaves by `+` and `ω^·`); the levels `≥ ε_{G+1}` need ◇P′.

Literal texts (all of [W07a]; the same quotations as in `R2.CitedSy`, checked there against the paper):
* (D) Def 3.1: "Let `n ∈ (0, ω)`.  Descending from `m = n − 1` down to `m = 0` we define sets of ordinals `Cⁿ_m(α, β)`
  where `β < Ω_{m+1}` and ordinals `ϑⁿ_m(α)` by simultaneous recursion on `α < Ω_{m+2}`.  For each `β < Ω_{m+1}` the
  set `Cⁿ_m(α, β)` is defined inductively by • `Ω_m ∪ β ⊆ Cⁿ_m(α, β)` • `ξ, η ∈ Cⁿ_m(α, β) ⇒ ξ + η ∈ Cⁿ_m(α, β)`
  • `ξ ∈ Cⁿ_m(α, β) ∩ Ω_{k+2} ⇒ ϑⁿ_k(ξ) ∈ Cⁿ_m(α, β)` for `m < k < n` • `ξ ∈ Cⁿ_m(α, β) ∩ α ⇒ ϑⁿ_m(ξ) ∈ Cⁿ_m(α, β)`.
  Having defined `ϑⁿ_m(ξ)` for all `ξ < α` and `Cⁿ_m(α, β)` for every `β < Ω_{m+1}` we set `ϑⁿ_m(α) := min({ξ <
  Ω_{m+1} | Cⁿ_m(α, ξ) ∩ Ω_{m+1} ⊆ ξ ∧ α ∈ Cⁿ_m(α, ξ)} ∪ {Ω_{m+1}})`.  Note that we have `ϑⁿ_m(0) = Ω_m` for `m < n`."
* (B) Lemma 3.3: "Let `α < Ω_{m+2}` and `β < Ω_{m+1}`.  (a) `ϑⁿ_m(α) = Cⁿ_m(α, ϑⁿ_m(α)) ∩ Ω_{m+1}`.  (b) `ϑⁿ_m(α) ∈ P ∩
  [Ω_m, Ω_{m+1}]`.  (c) Let `ξ =ANF ξ₁ + ⋯ + ξ_l`.  Then `ξ ∈ Cⁿ_m(α, β)` iff `ξ₁, …, ξ_l ∈ Cⁿ_m(α, β)`."
* (W) Def 3.4: "Let `α ↦ ω̄_α` be the enumeration function of the additive principle numbers which are not epsilon
  numbers."  Lemma 3.5: "Let `m < n`.  For every `α < Ω_{m+1}` we have `ϑⁿ_m(1 + α) = ω̄_{Ω_m+α}`."  Lemma 4.2: "For
  any `m < ω` and any `α < Ω_{m+1}` we have `ϑ_m(1 + α) = ω̄_{Ω_m+α}`".
* (EX) Corollary 3.21: "Let `m < n`.  `Tⁿ_m ⊆ Tⁿ⁺¹_m` and for `k` such that `m ≤ k < n` the functions `ϑⁿ_k` and
  `ϑⁿ⁺¹_k` agree on `Tⁿ_m ∩ Ω_{k+2}`."
* (T) Def 3.22: "For `m < ω` we set `θ_m := sup_{n>m} θⁿ_m`.  We define a function `ϑ_m : θ_{m+1} → Ω_{m+1}` by
  `ϑ_m(α) := ϑⁿ_m(α)` for `α < θ_{m+1}` where `n > m` is large enough to satisfy `α < θⁿ_{m+1}`.  `T_m` is defined
  inductively as follows: • `Ω_m ⊆ T_m` • `ξ, η ∈ T_m ⇒ ξ + η ∈ T_m` • `ξ ∈ T_m ∩ Ω_{k+2} ⇒ ϑ_k(ξ) ∈ T_m` for
  `k ≥ m`."
* (Θ) Theorem 3.23 (its first part is cut): "… `T_m ∩ Ω_{m+1} = θ_m = sup_{n≥m} ϑ_m(⋯(ϑ_n(0))⋯)`."
* (U) Remark after Corollary 3.24: "each `T_m` again gives rise to a notation system with parameters from `Ω_m` that
  provides a unique term for every ordinal which is element of some `Tⁿ_m` where `n > m`".
* (S) Def 3.28: "`Subᵗ_m(α) := {α}` for parameters `α < τ`; `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ) ∪ Subᵗ_m(η)` for `ξ, η ∈
  Tᵗ` s.t. `α =NF ξ + η > τ`; `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ)` if `k ≥ m`, `{α}` if `k < m`, for `α = ϑ_k(ξ)` where `ξ ∈
  Tᵗ ∩ Ω_{k+2}`.  …  `P_m(α) := Subᵗ_m(α) ∩ P ∩ [Ω_m, Ω_{m+1})` and `α^{*m} := max(P_m(α) ∪ {0})`.  The set of
  parameters `< τ` used in the unique term denoting some `α ∈ Tᵗ` is denoted by `Parᵗ(α) := Subᵗ₀(α) ∩ τ`."
* (L) Lemma 3.30: "For `m < ω` the function `ϑ_m ↾ Tᵗ ∩ Ω_{m+2}` is 1-1 and has values in `P ∩ [Ω_m, Ω_{m+1})`.  Let
  `α, γ ∈ Tᵗ ∩ Ω_{m+2}`.  Then `α^{*m} < ϑ_m(α)` and `ϑ_m(α) < ϑ_m(γ) ⇔ α < γ ∧ α^{*m} < ϑ_m(γ) ∨ ϑ_m(α) ≤ γ^{*m}`."
* (C) Convention 4.1: "Given a term `α = ϑᵗ(ξ) ∈ Tᵗ` we introduce the notational convention that `α = ϑᵗ(Δ + η)`
  automatically means that `ξ = Δ + η` is a decomposition such that `Ω₁ | Δ` and `η < Ω₁`."
* (E) Lemma 4.3: "Let `α = ϑᵗ(Δ + η) ∈ Tᵗ`.  Then `τ < α ∈ E ⇔ Δ > 0`."
* (P) Def 5.1: "`Tᵗ[σ] := {α ∈ Tᵗ | Parᵗ(α) ⊆ σ}` and `π_{σ,τ} : Tᵗ[σ] → T^σ` by the following clauses:
  • `π_{σ,τ}(ξ) := ξ` if `ξ < σ` • `π_{σ,τ}(ξ) := π_{σ,τ}(ξ₁) + π_{σ,τ}(ξ₂)` if `ξ =NF ξ₁ + ξ₂ > τ` • `π_{σ,τ}(ξ) :=
  ϑ_k(π_{σ,τ}(η))` if `ξ = ϑ_k(η)` for some `k > 0` and `η ∈ Tᵗ[σ] ∩ Ω_{k+2}` • `π_{σ,τ}(ξ) := ϑ^σ(π_{σ,τ}(η))` if
  `ξ = ϑᵗ(η)` for some `η ∈ Tᵗ[σ] ∩ Ω₂`."
* (Π) Lemma 5.3: "(b) `π_{σ,τ}` preserves `<`.  (c) `π_{σ,τ}` preserves ordinal addition.  (d) `π_{σ,τ}` maps
  `Tᵗ[σ]` onto `T^σ`."

Our steps.  They are the steps ◇O, ◇P, ◇N, ◇K, ◇M, ◇I, ◇V, ◇Δ, ◇F, ◇π of `R2.CitedSy` with `G` replaced by `G'`, the
data `ssDat` by `tcDat`, and the following changes, written out in full.
* (◇O′) **Veblen facts below `G'`.**  `F_a`, `Y_a := L_a ∖ F_a`, `V(a, c) := φ(a, y_c)` (`y_c` the `c`-th element of
  `Y_a`) as in ◇O, with `L_a := {y | φ(a, y) > max(Ω₁, a)}`.  For `a < G` this is the `L_a` of ◇O (`(Ω₁, ∞)`, `[1, ∞)`,
  all `y` for `a < Ω₁`, `= Ω₁`, `> Ω₁`; a strongly critical `a < G` is `≤ Ω₁`); for `a = G` (`φ(G, 0) = G`) it is
  `[1, ∞)`; for the other `a ∈ (G, G')` (not strongly critical, `φ(a, 0) > a`) it is all `y`.  O1, O2 hold verbatim
  (O2 for `x ∈ F_a`, `x > max(Ω₁, a)`).  O3: `a < V(a, c)` by the definition of `L_a`, and `c ≤ y_c < φ(a, y_c)`.  O4:
  `V(a, c) < G'` for `a, c < G'` (O1 at `x = G'`).  O5 verbatim (for `a' < a`: `x := V(a, c) > a > a'`, `x ∈ ran φ(a, ·)
  ⊆ F_{a'}`, O2).  O6: an `ε`-number `z ∈ (Ω₁, G')`, `z ≠ G`, is `φ(a, c)` in normal form (`1 ≤ a < z`, `c < z`) and
  `z = V(a, c*)`, `c* := otp(Y_a ∩ c)`: with `p := max(F_a ∩ L_a ∩ (c + 1))` when it exists, `c = p + 1 + d`, `c* = p +
  d`; otherwise `c* = −(Ω₁ + 1) + c`, `−1 + c`, `c` for `a < Ω₁`, `a ∈ {Ω₁, G}`, the other `a`.
* (◇G) **The atom: `ϑ₁(Ω₂²) = G`.**  Fix `n ≥ 3` with `Ω₂² < θⁿ₂` and `C(α, β) := Cⁿ₁(α, β)` as in ◇P (h1–h4 there).
  `≤`: `Ω₂² = ϑⁿ₂(Ω₂)`, `Ω₂ = ϑⁿ₂(0)` (h1), so `Ω₂² ∈ C(Ω₂², G)` (D).  By induction on the generation of `C(Ω₂², G)`:
  every member `u < Ω₂` is `< G`, every member `Ω₂ ≤ u < Ω₂²` is `Ω₂·a' + c'` with `a', c' < G` (h3), every other member
  is `≥ Ω₂²`.  Generators: `Ω₁ ∪ G`; `ϑⁿ₂(x) < Ω₂²` has `x < Ω₂` (h2), `x < G`, value `Ω₂·ω^x`, `ω^x < G`; `ϑⁿ₂(x) ≥
  Ω₂²` otherwise, `ϑⁿ_k(x) ≥ Ω₃` for `k ≥ 3`; `ϑⁿ₁(ξ)`, `ξ ∈ C ∩ Ω₂²`: `ξ < Ω₂` gives `ϑⁿ₁(ξ) < G` (h4, `G` an
  `ε`-number), `ξ = Ω₂·a' + c'` with `1 ≤ a'`, `a', c' < G` gives `ϑⁿ₁(ξ) = V(a', c') < G` (◇P of `R2.CitedSy`, O4).
  Sums: `G` is additive principal; a sum with a summand `≥ Ω₂²` is `≥ Ω₂²`.  So `C(Ω₂², G) ∩ Ω₂ ⊆ G`, and D gives
  `ϑⁿ₁(Ω₂²) ≤ G`.  `≥`: suppose `ξ₀ := ϑⁿ₁(Ω₂²) < G`.  By B (a) `ξ₀ = C(Ω₂², ξ₀) ∩ Ω₂`; `Ω₁ = ϑⁿ₁(0) ∈ C`, so `Ω₁ <
  ξ₀`.  For `1 ≤ a', c' < ξ₀`: `Ω₂·a' + c' ∈ C ∩ Ω₂²` (h1, D), so `V(a', c') = ϑⁿ₁(Ω₂·a' + c') < ξ₀` (◇P of
  `R2.CitedSy`, `a', c' < G`); with h4 (`a' = 0`) `ξ₀` is closed under every `φ(a', ·)`, `a' < ξ₀` (a value `φ(a', y)`
  with `y < ξ₀` is `≤ max(Ω₁, a')`, `= y` or `V(a', c')`, `c' ≤ y`): `ξ₀` is strongly critical and `> Ω₁`, so `ξ₀ ≥ G`,
  a contradiction.  So `ϑ₁(Ω₂²) = G` (EX, T), and `ϑ₁` does not depend on `τ`.
* (◇P′) **The correspondence below `G'`: `ϑ₁(Ω₂·a + c) = V(a, c)` for `1 ≤ a < G'`, `c < G'`.**  The proof of ◇P in
  `R2.CitedSy` word for word, with `G` replaced by `G'` (`ζ = Ω₂·a + c < Ω₂·G' < Ω₂²`, so every `ξ ∈ C ∩ ζ` is `< Ω₂²`
  and the generators of ◇P are the only ones), O3–O5 of ◇O′, and in the step `≥`: a value `φ(a', y)` with `y < ξ₀` is
  `≤ max(Ω₁, a') < ξ₀` (`a' < a < ξ₀`), `= y`, or `V(a', c')` with `c' ≤ y`; so `ξ₀` is closed under every `φ(a', ·)`,
  `a' < a`, lies in `ran φ(a, ·)`, and `ξ₀ > max(Ω₁, a)` puts its index in `L_a`; the two cases `ξ₀ ∉ F_a`, `ξ₀ ∈ F_a`
  contradict `ξ₀ < v` as there.
* (◇K′) **The canonical term of a code `z ∈ [Ω₁, G')`.**  As ◇K, with the atom: `arg G = Ω₂² = ϑ₂(Ω₂) = ϑ₂(ϑ₂(0))`
  (◇G, h1; no countable part), and `arg φ(a, c) = Ω₂·a + c*` for every `ε`-number `φ(a, c) ∈ (Ω₁, G')`, `≠ G`, in
  normal form (◇P′, O6 of ◇O′), `Ω₂·a = Σ ϑ₂(a_i)·k_i` (h1; the `a_i < G' < Ω₂`).  Countable parts and leaves are
  related as in ◇K; `G` contributes none.  ◇M verbatim (the arguments of `ϑ₁`, `ϑ₂` are `< Ω₂² + 1 < Ω₃`).
* (◇I′) As ◇I; a component `y = G` of a code in `Tᵗ` is `ϑ₁(ζ)` with `ζ ∈ Tᵗ ∩ Ω₃`, and L (`m = 1`) over `κ` with ◇G
  gives `ζ = Ω₂²`; L (`m = 2`) and h1 give its `ϑ₂`-term `ϑ₂(ϑ₂(0))`.
* (◇V′), (◇Δ′) ◇V, ◇Δ verbatim with `tcDat` for `ssDat` (◇K′, ◇I′, ◇M; `P₀(G) = ∅`), for every code `M' < G'` and
  every level `G ≤ μ < G'` (`Ω₁ + μ = μ`, `tcDatL μ = tcDat μ`, `Δ_μ = Ω₁·μ > 0`).
* (◇F′) ◇F for `0 ≤ b < G'` and codes `y < G'`, with one more case: `lead(y) = G`.  If `G ∈ F_b` (`b < G`), `p = G ∈
  Tᵗ`, `Parᵗ(G) = {0}` (S: `Sub₀(G) = {G, Ω₂², Ω₂, 0}`).  Otherwise `b ≥ G` and every `p ∈ F_b` has `p = φ(b, p) > b ≥
  G`, so no `p ≤ y` with `lead(y) = G` exists.
* (◇π′) **Base change.**  (π0) `G ∈ Tᵗ[σ]` (`Parᵗ(G) = {0} ⊆ σ`) and `π(G) = ϑ₁(π(ϑ₂(ϑ₂(0)))) = ϑ₁(ϑ₂(ϑ₂(π 0))) =
  G` (P, third clause with `k = 1, 2`, first clause).  π1, π2, π3 of ◇π verbatim for the codes below `G'` (π3 for every
  `ε`-number `z ∈ (G, G')` in normal form, π2 for `G < ω^g < G'`), by induction on the ordinal with π0 for the atom, ◇P′
  over any base, ◇F′ for the largest fixed points, and O6 of ◇O′ (`π a` is `<`, `=`, `>` `Ω₁` and `G` as `a` is: π is
  strictly increasing with `π(Ω₁) = Ω₁`, `π(G) = G`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- **[W07a] Def 3.22, Theorem 3.23, Def 3.1, Lemma 3.3, Lemma 3.5, Lemma 4.2, Def 3.28, Lemma 3.30 (`m = 0, 1, 2`)**
(texts T, Θ, D, B, W, S, L): for a level `Γ_{Ω₁+1} ≤ μ < Γ'` with `tcDatL μ ∈ Tᵗ` and `η ∈ Tᵗ ∩ Ω₁`:
`Ω₁·(Ω₁ + μ) + η ∈ Tᵗ` (the field `mem` of `Tc.TcCit Γ'`).

Our steps.  ◇Δ′ of the module docstring with `M' = μ` (`tcDatL μ = tcDat μ`): `Ω₁·μ ∈ Tᵗ` by ◇V′ (V1) (the canonical
term of ◇K′, built by T from countable parts `≤` the leaves, which lie in the initial segment `θᵗ`, and the atom
`ϑ₁(ϑ₂(ϑ₂(0)))`), and `Ω₁·μ + η ∈ Tᵗ` (T, second clause). -/
axiom tcArg_mem {τ μ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hGμ : Gg.ggGam ≤ μ) (hμG : μ < lgGam')
    (hμT : Tc.tcDatL μ ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1) : Om1 * (Om1 + μ) + η ∈ Tset τ

/-- **[W07a] Def 3.22, Theorem 3.23, the Remark after Corollary 3.24, Def 3.1, Lemma 3.3, Lemma 3.5, Lemma 4.2,
Def 3.28, Lemma 3.30 (`m = 0, 1, 2`)** (texts T, Θ, U, D, B, W, S, L): for a level `Γ_{Ω₁+1} ≤ μ < Γ'` and `η < Ω₁`
with `Ω₁·(Ω₁ + μ) + η ∈ Tᵗ`: `tcDatL μ ∈ Tᵗ` (the field `dat`).

Our steps.  `ξ := Ω₁·μ + η` (`Ω₁ + μ = μ`).  By U its term is unique; its components are in `Tᵗ` (S, second clause),
and those `≥ Ω₁` sum to `Ω₁·μ` (`η < Ω₁`), which is in `Tᵗ` (T).  ◇V′ (V1) at the code `Ω₁·μ` (◇I′: the term is the
canonical term) and ◇Δ′: `tcDat μ ∈ Tᵗ`. -/
axiom tcArg_dat {τ μ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hGμ : Gg.ggGam ≤ μ) (hμG : μ < lgGam')
    (hηΩ : η < Om1) (h : Om1 * (Om1 + μ) + η ∈ Tset τ) : Tc.tcDatL μ ∈ Tset τ

/-- **[W07a] Lemma 3.30, the direction `⇐`, with Def 3.28** (texts L, S, and the steps ◇): for a level
`Γ_{Ω₁+1} ≤ μ < Γ'` and `M' ≤ Ω₁ + μ` with `tcDat M', tcDatL μ ∈ Tᵗ`, `η', η ∈ Tᵗ ∩ Ω₁`, `Ω₁·M' + η' < Ω₁·(Ω₁ + μ) +
η` and `tcDat M', η'` below `ϑᵗ(Ω₁·(Ω₁ + μ) + η)`: `ϑᵗ(Ω₁·M' + η') < ϑᵗ(Ω₁·(Ω₁ + μ) + η)` (the field `vt_lt`).

Our steps.  `α := Ω₁·M' + η'` and `γ := Ω₁·(Ω₁ + μ) + η` lie in `Tᵗ ∩ Ω₂` (◇Δ′; `M' ≤ μ < Γ'` is a code).
`α^* ≤ max(tcDat M', η') < ϑ₀(γ)` (◇Δ′, the hypotheses).  So `α < γ ∧ α^* < ϑ₀(γ)`, the first disjunct of the right
side of L (`m = 0`), and `ϑ₀(α) < ϑ₀(γ)`. -/
axiom tcVt_lt {τ M' η' μ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hGμ : Gg.ggGam ≤ μ) (hμG : μ < lgGam')
    (hM' : M' ≤ Om1 + μ) (hM'T : Tc.tcDat M' ∈ Tset τ) (hη' : η' ∈ Tset τ) (hη'Ω : η' < Om1)
    (hμT : Tc.tcDatL μ ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (harg : Om1 * M' + η' < Om1 * (Om1 + μ) + η) (hd' : Tc.tcDat M' < vt τ (Om1 * (Om1 + μ) + η))
    (hη'v : η' < vt τ (Om1 * (Om1 + μ) + η)) : vt τ (Om1 * M' + η') < vt τ (Om1 * (Om1 + μ) + η)

/-- **[W07a] Lemma 3.30, the direction `⇒`, with Def 3.28** (texts L, S, and the steps ◇): for a level
`Γ_{Ω₁+1} ≤ μ < Γ'` with `tcDatL μ ∈ Tᵗ`, `ξ ∈ Tᵗ ∩ Ω₂`, `η ∈ Tᵗ ∩ Ω₁`, `tcDatL μ, η < ϑᵗ(ξ)`:
`ϑᵗ(ξ) < ϑᵗ(Ω₁·(Ω₁ + μ) + η)` implies `ξ < Ω₁·(Ω₁ + μ) + η` (the field `lt_of`).

Our steps.  `γ := Ω₁·(Ω₁ + μ) + η ∈ Tᵗ ∩ Ω₂` and `γ^* ≤ max(tcDatL μ, η) < ϑ₀(ξ)` (◇Δ′, the hypotheses).  L (`m = 0`,
`α = ξ`): `ϑ₀(ξ) < ϑ₀(γ)` gives `ξ < γ ∧ ξ^* < ϑ₀(γ)` or `ϑ₀(ξ) ≤ γ^*`; the second is impossible.  So `ξ < γ`. -/
axiom tcLt_of_vt_lt {τ ξ μ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hGμ : Gg.ggGam ≤ μ) (hμG : μ < lgGam')
    (hξ : ξ ∈ Tset τ) (hξ2 : ξ < OmTwo) (hμT : Tc.tcDatL μ ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (hdξ : Tc.tcDatL μ < vt τ ξ) (hηξ : η < vt τ ξ) (h : vt τ ξ < vt τ (Om1 * (Om1 + μ) + η)) :
    ξ < Om1 * (Om1 + μ) + η

/-- **[W07a] Lemma 3.30 (`α^* < ϑ₀(α)`), Lemma 4.3, Def 3.28, Convention 4.1** (texts L, E, S, C, and the steps ◇):
for a level `Γ_{Ω₁+1} ≤ μ < Γ'` with `tcDatL μ ∈ Tᵗ` and `η ∈ Tᵗ ∩ Ω₁`: `tcDatL μ, η < ϑᵗ(Ω₁·(Ω₁ + μ) + η)` (the
field `level`).

Our steps.  `γ := Ω₁·μ + η ∈ Tᵗ ∩ Ω₂` (◇Δ′) with `Δ = Ω₁·μ > 0` (C).  L (`m = 0`): `γ^* < ϑ₀(γ) =: q`; E: `τ < q ∈ E`.
◇Δ′ (last clause, `ξ' = γ`): `tcDat μ < q`.  The additive components of `η` are `< τ` or `≤ η^* ≤ γ^*` (step ★1 of
`R2.CitedLu`; `P₀(η) ⊆ P₀(γ)`), hence `< q`, and `q` is additive principal: `η < q`. -/
axiom tcLevel_lt {τ μ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hGμ : Gg.ggGam ≤ μ) (hμG : μ < lgGam')
    (hμT : Tc.tcDatL μ ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    Tc.tcDatL μ < vt τ (Om1 * (Om1 + μ) + η) ∧ η < vt τ (Om1 * (Om1 + μ) + η)

/-- **[W07a] Def 5.1 (first and third clauses), Def 3.28, Def 3.22, Def 3.1, Lemma 3.3, Lemma 3.30** (texts P, S, T, D,
B, L, and the step ◇G): for bases `σ < τ`: `Γ_{Ω₁+1} ∈ Tᵗ[σ]` and `π_{σ,τ}(Γ_{Ω₁+1}) = Γ_{Ω₁+1}` (the field `gam` of
`Tc.TcCitPi Γ'`).

Our steps.  Step π0 of ◇π′ in the module docstring: `Γ_{Ω₁+1} = ϑ₁(ϑ₂(ϑ₂(0)))` (◇G, h1), a term of `Tᵗ` (T) with
`Parᵗ = {0} ⊆ σ` (S), and `π` keeps it (P, third clause with `k = 1, 2`, first clause). -/
axiom tcGam_TB {σ τ : Ordinal.{0}} (h : Bases σ τ) : Gg.ggGam ∈ TB τ σ ∧ pi σ τ Gg.ggGam = Gg.ggGam

/-- **[W07a] Def 5.1 (all four clauses), Lemma 5.3 (b)–(d), Def 3.28, Def 3.22, Def 3.1, Lemma 3.3, Lemma 3.5,
Lemma 4.2, Lemma 4.3, Lemma 3.30** (texts P, Π, S, T, D, B, W, E, L, and the steps ◇): for bases `σ < τ` and an
`ε`-number `φ(a, c) ∈ (Γ_{Ω₁+1}, Γ')` in normal form (`1 ≤ a`, `a, c < φ(a, c)`): `φ(a, c) ∈ Tᵗ[σ] ⇔ a, c ∈ Tᵗ[σ]`,
and then `π_{σ,τ}(φ(a, c)) = φ(π_{σ,τ}(a), π_{σ,τ}(c))` (the field `eps`).

Our steps.  Step π3 of ◇π′ (the term `ϑ₁(Ω₂·a + c*)` of ◇K′, ◇P′, ◇I′; the parameters through S; the value through P,
third clause with `k = 1, 2`, and the fixed-point shift of O6 (◇O′) kept by `π` through ◇F′, π0 for the atom). -/
axiom tcPhi_TB {σ τ a c : Ordinal.{0}} (h : Bases σ τ) (ha : 1 ≤ a) (haz : a < veblen a c)
    (hcz : c < veblen a c) (h1 : Gg.ggGam < veblen a c) (hG : veblen a c < lgGam') :
    (veblen a c ∈ TB τ σ ↔ a ∈ TB τ σ ∧ c ∈ TB τ σ) ∧
      (a ∈ TB τ σ → c ∈ TB τ σ → pi σ τ (veblen a c) = veblen (pi σ τ a) (pi σ τ c))

/-- **[W07a] Def 5.1 (first three clauses), Lemma 5.3 (b)–(d), Def 3.28, Def 3.22, Lemma 3.5, Lemma 4.2, Lemma 3.30**
(texts P, Π, S, T, W, L, and the steps ◇): for bases `σ < τ` and `g ≥ E₁`, not an `ε`-number, with `Γ_{Ω₁+1} < ω^g <
Γ'`: `ω^g ∈ Tᵗ[σ] ⇔ g ∈ Tᵗ[σ]`, and then `π_{σ,τ}(ω^g) = ω^{π_{σ,τ}(g)}` (the field `opow`).

Our steps.  Step π2 of ◇π′: `ω^g = ϑ₁(g⁻)` (◇N), `Parᵗ(ω^g) = Parᵗ(g⁻)` (S, `k = 1`), `π(ω^g) = ϑ₁(π(g⁻))` (P, third
clause), `π(g⁻) = (π g)⁻` (◇F′, π0, π3), and `ϑ₁((π g)⁻) = ω^{π g}` (◇N). -/
axiom tcOpow_TB {σ τ g : Ordinal.{0}} (h : Bases σ τ) (hg : Gg.ggE ≤ g) (hgE : ω ^ g ≠ g)
    (h1 : Gg.ggGam < ω ^ g) (hG : ω ^ g < lgGam') :
    (ω ^ g ∈ TB τ σ ↔ g ∈ TB τ σ) ∧ (g ∈ TB τ σ → pi σ τ (ω ^ g) = ω ^ pi σ τ g)

end Googology.Trans.PoR.InaccPsi.R2
