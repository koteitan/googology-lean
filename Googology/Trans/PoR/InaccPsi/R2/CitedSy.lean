import Googology.Trans.PoR.InaccPsi.R2.CitedSs
import Googology.Trans.PoR.InaccPsi.R2.SsFn
import Googology.Trans.PoR.InaccPsi.R2.TfSy

set_option autoImplicit false

/-!
# Cited facts of Wilken 2007, as axioms, ONCE for every Veblen level `ε_{Ω₁+1} < μ < Γ_{Ω₁+1}` and every Veblen code

**Round 92: this file has no axiom left.**  The seven facts below (the fields of `Sv.SvCit Γ_{Ω₁+1}` and
`Sv.SvCitPi Γ_{Ω₁+1}`) are theorems: the instances `M = Ω₁ + μ`, `E₁ < μ < Γ_{Ω₁+1}`, and the codes below
`Γ_{Ω₁+1}`, of the generic citation `R2.CitedTf`, with `Tf.tfDat = Ss.ssDat` below `Γ_{Ω₁+1}` (`R2.TfSy`).  The literal
texts and steps below (◇O, ◇P, ◇N, ◇K, ◇M, ◇I, ◇V, ◇Δ, ◇F, ◇π) are kept as their reading; `R2.CitedTf` states them once
for every level below `B_Γ`.

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

Same conventions as `R2.CitedRj`, `R2.CitedRk`, `R2.CitedSs` (`Ω₁ = Om1`, `Ω₂ = OmTwo`, `Tset τ = Tᵗ`, `Par τ = Parᵗ`,
`vt τ = ϑᵗ = ϑ₀`, `pi σ τ = π_{σ,τ}`, `TB τ σ = Tᵗ[σ]`, every base `τ` a countable `ε`-number).  `φ(a, c) = veblen a c`
(Mathlib, `φ(0, c) = ω^c`), `E₁ := ε_{Ω₁+1} = Gg.ggE`, `G := Γ_{Ω₁+1} = Gg.ggGam` (the least strongly critical
ordinal above `Ω₁`).  A **code** is an ordinal `z < G`.  Its **leaves** are read by `Ss.ssDat`: `z` if `z < Ω₁`; none
if `z = Ω₁`; for a non-`ε` `z ∈ (Ω₁, G)` the leaves of `log_ω z` and of `z mod ω^{log_ω z}`; for an `ε`-number
`z ∈ (Ω₁, G)`, `z = φ(a, c)` with `a = invVeblen₁ z`, `c = invVeblen₂ z` (`1 ≤ a < z`, `c < z`), the leaves of `a`
and `c`.  `ssDat z` is the largest leaf (`0` if there is none), `ssDatL μ = ssDat(Ω₁ + μ) = ssDat μ` for `μ ≥ E₁`.

What is **not** restated (checked first, every `Cited*` file of `R2`): `R2.CitedSs` (the level `μ = E₁` only:
`ssE_mem`, `ssE_TB`, `ssVt_lt`, `ssLt_of_vt_lt`, `ssLevel_lt`), `R2.CitedRj`, `R2.CitedRk` (levels `M < E₁`),
`R2.CitedLq`, `R2.CitedLg`, `R2.CitedLv`, `R2.CitedLu`, `R2.CitedLz`, `R2.CitedLt`, `R2.CitedXt`, `R2.CitedSi`,
`R2.CitedEps`, `R2.CitedEv`, `R2.CitedW`, `R2.CitedVz`, `R2.Cited` (`om1_opow_TB_all`: only `b < E₁`), `R2.CitedL`,
`R2.CitedR1`, `R2.CitedCore`, `R2.CitedC09`, `R2.CitedBr`.  None of them mentions a level in `(E₁, G)`, an
`ε`-number in `(E₁, G)` in `Tᵗ`, or `π` at such an ordinal.  The axioms below are exactly the fields of the
hypothesis packages `Sv.SvCit G` (five) and `Sv.SvCitPi G` (two).  The first sub-range `μ < ε_{Ω₁+2}` needs only ◇N
below (its codes are built from `Ω₁`, `E₁ = ϑ₁(Ω₂)` and countable leaves by `+` and `ω^·`); the generic levels need
◇P, the `ϑ₁ ↔ φ` correspondence on `[Ω₂, Ω₂·G)`, proved below from the definition D.

Literal texts (all of [W07a]; checked against the paper):
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
  any `m < ω` and any `α < Ω_{m+1}` we have `ϑ_m(1 + α) = ω̄_{Ω_m+α}`"; its proof adds: "for `m = 0` by
  convention we have `Ω₀ = τ`".
* (EX) Corollary 3.21: "Let `m < n`.  `Tⁿ_m ⊆ Tⁿ⁺¹_m` and for `k` such that `m ≤ k < n` the functions `ϑⁿ_k` and
  `ϑⁿ⁺¹_k` agree on `Tⁿ_m ∩ Ω_{k+2}`."
* (T) Def 3.22: "For `m < ω` we set `θ_m := sup_{n>m} θⁿ_m`.  We define a function `ϑ_m : θ_{m+1} → Ω_{m+1}` by
  `ϑ_m(α) := ϑⁿ_m(α)` for `α < θ_{m+1}` where `n > m` is large enough to satisfy `α < θⁿ_{m+1}`.  `T_m` is defined
  inductively as follows: • `Ω_m ⊆ T_m` • `ξ, η ∈ T_m ⇒ ξ + η ∈ T_m` • `ξ ∈ T_m ∩ Ω_{k+2} ⇒ ϑ_k(ξ) ∈ T_m` for
  `k ≥ m`."
* (Θ) Theorem 3.23 (its first part, `T_m = ⋃_{n>m} Tⁿ_m`, is cut): "… `T_m ∩ Ω_{m+1} = θ_m =
  sup_{n≥m} ϑ_m(⋯(ϑ_n(0))⋯)`."  Corollary 3.24: "For every `k ≥ m` we have `sup(T_m ∩ Ω_{k+2}) = θ_{k+1}`.
  For `m < n` we have `Tⁿ_m ∩ Ω_{m+1} = θⁿ_m = ϑ_m(⋯(ϑ_n(0))⋯)`."
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

Our steps (`τ` a countable `ε`-number; `x ∪ ω` adds the finite ordinals, all `< σ < τ`).
* (◇O) **Veblen facts.**  `F_a := {y | φ(a, y) = y}` (for `1 ≤ a`: `ε`-numbers; `F_a ⊆ F_{a'}` for `a' ≤ a`; `ran
  φ(a, ·) ⊆ F_{a'}` for `a' < a`; a limit `x > 0` closed under every `φ(a', ·)`, `a' < a`, is in `ran φ(a, ·)` for
  `a ≥ 1`: continuity gives `φ(a', x) = x`).  An `ε`-number `z ∈ (Ω₁, G)` is `φ(a, c)` with `1 ≤ a < z`, `c < z`, and
  `(a, c)` is unique (normal form).  `Ω₁ = φ(Ω₁, 0)`; for `a < Ω₁`, `φ(a, y) ≤ Ω₁ ⇔ y ≤ Ω₁`; for `a > Ω₁`,
  `φ(a, 0) > Ω₁`.  Put `L_a := {y | φ(a, y) > Ω₁}` (`(Ω₁, ∞)`, `[1, ∞)`, all `y`, for `a < Ω₁`, `= Ω₁`, `> Ω₁`),
  `Y_a := L_a ∖ F_a`, and `V(a, c) := φ(a, y_c)` with `y_c` the `c`-th element of `Y_a`: the enumeration of the
  values of `φ(a, ·)` above `Ω₁` that are not fixed points.
  (O1) For an `ε`-number `x > Ω₁`: the successor ordinals of `(Ω₁, x)` lie in `Y_a` (fixed points are limits) and
  have order type `x`, so `Y_a ∩ x` has order type `x`; likewise the non-`ε` ordinals below an `ε`-number `p` have
  order type `p`.  (O2) For `x ∈ F_a`, `x > Ω₁`, and `c < x`: `y_c < x` (O1), `V(a, c) < φ(a, x) = x`.  (O3) For
  `1 ≤ a < G`: `a < V(a, c)` (`a < φ(a, 0)` unless `a` is strongly critical, and a strongly critical `a < G` is
  `≤ Ω₁ < V(a, c)`) and `c ≤ y_c < φ(a, y_c)`.  (O4) `V(a, c) < G` for `a, c < G` (O1 at `x = G`).  (O5) If
  `Ω₂·a' + c' < Ω₂·a + c`, `1 ≤ a'`, `c' < V(a, c)`, then `V(a', c') < V(a, c)` (`a' = a`: `c' < c`; `a' < a`:
  `V(a, c) ∈ ran φ(a, ·) ⊆ F_{a'}`, O2).  (O6) An `ε`-number `z = φ(a, c) ∈ (Ω₁, G)` in normal form is
  `V(a, c*)`, `c* := otp(Y_a ∩ c) ≤ c`: if `p := max(F_a ∩ L_a ∩ (c + 1))` exists (`F_a` is closed), then `p < c`,
  `c = p + 1 + d` and `c* = p + d` (O1 at `x = p`);
  otherwise `c* = −(Ω₁ + 1) + c`, `−1 + c`, `c` for `a < Ω₁`, `= Ω₁`, `> Ω₁`.  So `c*` and `c` have the same Cantor
  normal form up to one copy of `Ω₁` and the finite tail.
* (◇P) **The correspondence: `ϑ₁(Ω₂·a + c) = V(a, c)` for `1 ≤ a < G`, `c < G`.**  Fix `n ≥ 3` with `Ω₂² < θⁿ₂`
  (Θ: `Ω₂² + 1 ∈ T₀ ∩ Ω₃`, below `θ₂ = sup_n θⁿ₂`; the `θⁿ₂` grow by EX), so `ϑ₁ = ϑⁿ₁` below `Ω₂²` (T); `C(α, β) :=
  Cⁿ₁(α, β)`.  (h1) `ϑⁿ₂(0) = Ω₂` (D), `ϑⁿ₂(x) = ω^{Ω₂+x} = Ω₂·ω^x` for `1 ≤ x < Ω₂`, `ϑⁿ₂(Ω₂) = Ω₂²` (W, `m = 2`:
  `ω̄_{Ω₂+α} = ω^{Ω₂+1+α}` below `ε_{Ω₂+1}`).  (h2) `ϑⁿ₂(x) ≥ Ω₂²` for `Ω₂ ≤ x < Ω₃` (W), `> Ω₂²` for `Ω₃ ≤ x < Ω₄`
  (D: `Ω₂ = ϑⁿ₂(0)` and `Ω₂² = ϑⁿ₂(Ω₂)` lie in `Cⁿ₂(x, β)`, as `0, Ω₂ < x`), `ϑⁿ_k(x) ≥ Ω₃` for `k ≥ 3` (B (b)).
  (h3) An element `u ∈ C(α, β)` with `Ω₂ ≤ u < Ω₂²` is a finite sum of generators (D) whose generators `≥ Ω₂` are
  `Ω₂·ω^x` with `x ∈ C(α, β) ∩ Ω₂` (h1, h2; a value `Ω₂` of `ϑⁿ₁` is `Ω₂·ω⁰`); so `u = Ω₂·a' + c'` with the Cantor
  exponents of `a'` and `c'` in `C(α, β)` (D, second clause).  (h4) `ϑⁿ₁(0) = Ω₁`, `ϑⁿ₁(1 + α) = ω̄_{Ω₁+α}` (D, W,
  `m = 1`), `ω^x ≤ ϑⁿ₁(x)` for `Ω₁ ≤ x < Ω₂`, and `ϑⁿ₁(x) < y` for an `ε`-number `y > Ω₁` with `x < y` (O1).
  Induction on `ζ = Ω₂·a + c`, `v := V(a, c)` (an `ε`-number in `(Ω₁, G)`, O3, O4).
  `≤`: the Cantor exponents `a_i` of `a` and `c` are `< v` (O3), so `ζ = Σ ϑⁿ₂(a_i)·k_i + c ∈ C(ζ, v)` (h1).  By
  induction on the generation of `C(ζ, v)`: every member `u < Ω₂` is `< v`, every member `Ω₂ ≤ u < Ω₂²` is `Ω₂·a' +
  c'` with `a', c' < v`.  Generators: `Ω₁ ∪ v`; `ϑⁿ₂(x) < Ω₂²` has `x < Ω₂` (h2), so `x < v` and it is `Ω₂·ω^x`, `ω^x
  < v`; `ϑⁿ_k(x) ≥ Ω₃` for `k ≥ 3`; `ϑⁿ₁(ξ)` with `ξ ∈ C ∩ ζ`: for `ξ < Ω₂` by h4, for `Ω₂ ≤ ξ < ζ` we have `ξ = Ω₂·a' +
  c'`, `1 ≤ a'`, `a', c' < v < G`, so `ϑⁿ₁(ξ) = V(a', c') < v` (i.h., O5).  Sums: `v` is additive principal and
  `Ω₂·a₁ + c₁ + Ω₂·a₂ + c₂ = Ω₂·(a₁ + a₂) + c₂` for `a₂ ≥ 1`.  So `C(ζ, v) ∩ Ω₂ ⊆ v`, and D gives `ϑⁿ₁(ζ) ≤ v`.
  `≥`: suppose `ξ₀ := ϑⁿ₁(ζ) < v`.  By D and B (a), `ζ ∈ C(ζ, ξ₀)` and `ξ₀ = C(ζ, ξ₀) ∩ Ω₂ ⊇ ξ₀`.  `Ω₁ = ϑⁿ₁(0) ∈ C`
  (`0 < ζ`), so `Ω₁ < ξ₀`; `ω^x ≤ ϑⁿ₁(x) ∈ C ∩ Ω₂` for `Ω₁ ≤ x < ξ₀` (h4): `ξ₀` is an `ε`-number.  B (c) and h3: every
  component `Ω₂·ω^{a_i}` of `ζ` is a generator `Ω₂·ω^x`, `x = a_i ∈ C ∩ Ω₂`, and `c ∈ C ∩ Ω₂`; so `a, c < ξ₀`.  For
  `1 ≤ a' < a`, `c' < ξ₀`: `Ω₂·a' + c' ∈ C ∩ ζ` (h1), so `V(a', c') = ϑⁿ₁(Ω₂·a' + c') < ξ₀` (i.h.); likewise
  `V(a, c') < ξ₀` for `c' < c`.  A value `φ(a', y)` with `y < ξ₀` is `≤ Ω₁`, or `= y`, or `V(a', c')` with `c' ≤ y`;
  so `ξ₀` is closed under every `φ(a', ·)`, `a' < a` (`a' = 0`: `ε`), and `ξ₀ ∈ ran φ(a, ·)` (◇O).  If `ξ₀ ∉ F_a`,
  `ξ₀ = V(a, c₀)` and `V(a, c') < ξ₀` for all `c' < c` gives `c ≤ c₀`, `v ≤ ξ₀`; if `ξ₀ ∈ F_a`, `v < ξ₀` (O2,
  `c < ξ₀`).  Both contradict `ξ₀ < v`.  So `ϑ₁(Ω₂·a + c) = V(a, c)`.  (`ϑ₁` does not depend on `τ`: D, `Ω₀ = τ`
  enters `Cⁿ_m` only for `m = 0`.)
* (◇N) **Powers.**  For a non-`ε` `e > Ω₁`: `p := max(E ∩ (e + 1)) ≥ Ω₁`, `e = p + d` (`d ≥ 1`); the non-`ε` ordinals
  below `e` have order type `p + (−1 + d)` (O1), so `ω^e = ω̄_{p+(−1+d)} = ϑ₁(e⁻)` (W, `m = 1`) with `e⁻ := d` if
  `p = Ω₁`, `e⁻ := p + (−1 + d)` if `p > Ω₁`.  The same at level `0` over a base `σ` (W, `Ω₀ = σ`): for a non-`ε`
  `x > σ`, `ω^x = ϑ^σ(x⁻)` with `p := max(E ∩ (x + 1)) ≥ σ`, `x⁻ := d` or `p + (−1 + d)`.  So `e`, `e⁻` (`x`, `x⁻`) have
  the same Cantor normal form up to `Ω₁` (`σ`) and the finite tail.
* (◇K) **The canonical term of a code `z ∈ [Ω₁, G)`.**  Its Cantor components `≥ Ω₁` are additive principal codes
  `y = ϑ₁(arg y)`: `arg Ω₁ = 0` (D), `arg ω^e = e⁻` (◇N), `arg φ(a, c) = Ω₂·a + c*` (normal form; ◇P, O6), where
  `Ω₂·a = Σ ϑ₂(a_i)·k_i` (h1) for `a =CNF Σ ω^{a_i}·k_i`; its components `< Ω₁` form the countable remainder.  The
  parts `e⁻`, `a_i`, `c*`, `a` are countable or codes `< z`; recursion gives a finite term.  Its **countable parts**
  (maximal countable subterms) are the countable remainders, the countable `e⁻`, `c*`, and the exponents `a_i` of a
  countable `a`.  By O6, ◇N: every countable part is `≤` a leaf of `z`, and every leaf of `z` is finite, a countable
  part `x`, `1 + x`, or a countable `a = Σ ω^{a_i}·k_i` of countable parts `a_i`.
* (◇M) If every leaf of `z` is `< κ` (`κ` a countable `ε`-number), then `z ∈ T^κ` by its canonical term (T: the
  countable parts are parameters `< κ`; the arguments of `ϑ₁`, `ϑ₂` are `< Ω₂² < Ω₃`).
* (◇I) **Identification.**  If a code `z ≥ Ω₁` lies in `Tᵗ`, its unique term (U) is the canonical term.  Its
  components are in `Tᵗ` (S, U); an additive principal component `y ≥ Ω₁` (`y < G < Ω₂`) is not a parameter, not a
  `ϑ₀`-value (`< Ω₁`, L), not a `ϑ_k`-value for `k ≥ 2` (`≥ Ω₂`, L): `y = ϑ₁(ζ)` with `ζ ∈ Tᵗ ∩ Ω₃`.  Let `κ` be a
  countable `ε`-number above `θᵗ := Tᵗ ∩ Ω₁` (Θ) and above the leaves of `y`.  `ϑ₁`, `ϑ₂` do not depend on the base,
  and the countable subterms of `ζ` are `< θᵗ < κ`, parameters of `T^κ`; so `ζ ∈ T^κ` (T, along the term), and
  `arg y ∈ T^κ` (◇M).  L (`m = 1`) over `κ`: `ϑ₁` is 1-1 on `T^κ ∩ Ω₃`, so `ζ = arg y`.  In `ζ = Ω₂·a + c*` a
  component `Ω₂·ω^{a_i} ∈ [Ω₂, Ω₃)` is a `ϑ₂`-term `ϑ₂(x)` (L), and L (`m = 2`) over `κ` with h1 gives `x = a_i`.
* (◇V) **Membership and data.**  `θᵗ` is an initial segment closed under `+` and `ω^·` (Θ: a supremum of the values
  `ϑ₀(ϑ₁(⋯))`, `ε`-numbers by E).  For a code `z ∈ [Ω₁, G)`: (V1) `z ∈ Tᵗ ⇔ ssDat z ∈ Tᵗ` (⇒: by ◇I every countable
  part is in `θᵗ`, so every leaf; ⇐: every countable part is `≤` a leaf, so in `θᵗ`, and T builds the canonical term).
  (V2) For `z ∈ Tᵗ`, `P₀(z)` is the union of the `P₀(x)` over the countable parts `x` (S: `Sub₀` descends through
  sums and every `ϑ_k`, `k ≥ 0`), whose members are `≤ x` (step ★1 of `R2.CitedLu`: L, `α^* < ϑ₀(α)`), so every member
  of `P₀(z)` is `≤ ssDat z`.  For an `ε`-number `q > τ` with `z^* < q`: each countable part has its additive
  components `< τ` or `≤ x^* ≤ z^*` (step ★1), so it is `< q`, and so is every leaf (`q ∈ E`): `ssDat z < q`.
* (◇Δ) **The argument.**  For a code `M'` (`M' < Ω₁` allowed) and `η' ∈ Tᵗ ∩ Ω₁`: `Ω₁·M'` is a code divisible by
  `Ω₁`; for `M' =CNF Σ ω^{m_l}·k_l + r` (`ω^{m_l} ≥ Ω₁`, `r =ANF Σ ω^{b_j} < Ω₁`), `Ω₁·M' = Σ ω^{Ω₁+m_l}·k_l + Σ
  ω^{Ω₁+b_j}`: its leaves are those of the `m_l` and the `b_j ≤ r`, and the leaves of `M'` are those of the `m_l` and
  `r = Σ ω^{b_j}`.  So (◇V): `Ω₁·M' ∈ Tᵗ ⇔ ssDat M' ∈ Tᵗ`; then `ξ' := Ω₁·M' + η' ∈ Tᵗ ∩ Ω₂` (T), `ξ'^* ≤ max(ssDat
  M', η')` (S: `P₀(ξ') = P₀(Ω₁·M') ∪ P₀(η')`); and `ssDat M' < q` for every `ε`-number `q > τ` with `ξ'^* < q`.  For
  `E₁ < μ < G`: `Ω₁ + μ = μ`, `ssDatL μ = ssDat μ`, `Δ_μ := Ω₁·(Ω₁ + μ) = Ω₁·μ > 0`.
* (◇F) **Largest fixed points.**  Let `0 ≤ b < G` (`F₀ = E`), `y ∈ Tᵗ` a code `≥ Ω₁` (for `b = 0` also `y ∈ Tᵗ ∩ [τ,
  Ω₁)`), and `p := max(F_b ∩ (y + 1))` with `p > Ω₁` (resp. `p ≥ τ`).  Then `p ∈ Tᵗ` and `Parᵗ(p) ⊆ Parᵗ(y) ∪ ω`.
  Induction on `y`: `p` is additive principal, so `p ≤ lead(y)`, a component of `y` (S).  If `lead(y) ∈ F_b`, `p =
  lead(y)`.  If `lead(y) = ω^e` is not an `ε`-number, `p ≤ e` (`p = ω^p`), and `e ∈ Tᵗ` with `Parᵗ(e) ∪ ω = Parᵗ(e⁻) ∪
  ω` (◇N, ◇I), `e < y`: i.h.  If `lead(y) = φ(a₂, c₂) ∉ F_b` (normal form), then `a₂ ≤ b` and `F_b ⊆ F_{a₂}`, so
  `p ∈ F_b`, `p = φ(a₂, p) < φ(a₂, c₂)` gives `p < c₂`; `c₂ ∈ Tᵗ` with `Parᵗ(c₂) ∪ ω = Parᵗ(c₂*) ∪ ω` (◇I,
  O6), `c₂ < y`: i.h.
* (◇π) **Base change** (`Bases σ τ`).  By induction on the ordinal, for codes and countable ordinals in `Tᵗ`:
  (π1) for `x ∈ Tᵗ ∩ Ω₁`, `ω^x ∈ Tᵗ[σ] ⇔ x ∈ Tᵗ[σ]` and then `π(ω^x) = ω^{π x}`; (π2) the same for codes `g ≥ Ω₁`
  with `ω^g < G`; (π3) for an `ε`-number `z = φ(a, c) ∈ (Ω₁, G)` in normal form, `z ∈ Tᵗ[σ] ⇔ a, c ∈ Tᵗ[σ]`, and then
  `π(z) = φ(π a, π c)`, again a normal form.  Membership: `Parᵗ(ϑ_k(ξ)) = Parᵗ(ξ)` for `k ≥ 1` and for `ϑ₀`-terms
  `≥ τ` (S), and parts differing only by `Ω₁`, `σ`, `τ` and the finite tail (◇N, O6) have the same parameters up to
  `ω` (`Parᵗ(Ω₁) = {0}`, `ϑ₁(0) = Ω₁`); so by ◇K, ◇I and the i.h. (π1, π2 for the `a_i`), `Parᵗ(z) ∪ ω = Parᵗ(a) ∪
  Parᵗ(c) ∪ ω`, `Parᵗ(ω^g) ∪ ω = Parᵗ(g) ∪ ω`, and ◇V gives the `Tᵗ`-membership.  Values: π is strictly increasing,
  additive, onto `T^σ` (Π), `π(n) = n`, `π(Ω₁) = Ω₁`, `π(τ) = π(ϑᵗ(0)) = ϑ^σ(0) = σ` (P).  (π3) P (third clause,
  `k = 1, 2`): `π(z) = ϑ₁(Ω₂·â + π(c*))`, `â = Σ ω^{π a_i}·k_i = π(a)` (Π (c), i.h.).  `π a` is `<`, `=`, `> Ω₁` as
  `a` is.  The `p` of O6 is in `Tᵗ[σ]` (◇F), and `π(p) ∈ F_{πa}` (i.h.: `p = φ(a₃, c₃)`, `a₃ > a`, `π p = φ(πa₃,
  πc₃)`).  If `F_{πa} ∩ L_{πa}` had a member `q` in `(π p, π c]` (in `(Ω₁, πc]`, resp. `[1, πc]`, if there is no `p`),
  the largest one is in `T^σ` (◇F over `σ`), `q = π q'` (Π (d)), `q' ∈ F_a` (i.h.), `p < q' ≤ c`: impossible.  And
  `πc ∉ F_{πa}` (i.h.).  So `(π c)* = π(c*)` (O6; `π(p + 1 + d) = π p + 1 + π d`), and `π(z) = V(πa, (πc)*) =
  φ(πa, πc)` (◇P over any base, O6).  (π1) `x < σ`: identity; `x ∈ [σ, τ)`: neither side in `Tᵗ[σ]`; `x` an
  `ε`-number: `π(x)` is one (`x = τ`: `σ`; `x > τ`: `x = ϑᵗ(Δ + η)`, `Δ > 0` (E), `π x = ϑ^σ(πΔ + πη)`, `πΔ > 0` a sum
  of `ϑ₁`-terms, E over `σ`); otherwise `ω^x = ϑᵗ(x⁻)` (◇N), `π(ω^x) = ϑ^σ(π(x⁻))` (P), and `π(x⁻) = (πx)⁻` as
  `π(p)` is the largest `ε`-number `≤ π x` (◇F over `τ` and `σ`, as in π3).  (π2) `ω^g = ϑ₁(g⁻)`, `π(ω^g) = ϑ₁(π(g⁻))`
  (P, `k = 1`), `π(g⁻) = (πg)⁻` as in π1.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- **Theorem (formerly an axiom)**: the instance `M = Ω₁ + μ` of `R2.tfArg_mem`.
**[W07a] Def 3.22, Theorem 3.23, Def 3.1, Lemma 3.3, Lemma 3.5, Lemma 4.2, Def 3.28, Lemma 3.30 (`m = 0, 1, 2`)**
(texts T, Θ, D, B, W, S, L): for a level `E₁ < μ < Γ_{Ω₁+1}` with `ssDatL μ ∈ Tᵗ` and `η ∈ Tᵗ ∩ Ω₁`:
`Ω₁·(Ω₁ + μ) + η ∈ Tᵗ` (the field `mem` of `Sv.SvCit Γ_{Ω₁+1}`).

Our steps.  ◇Δ of the module docstring with `M' = μ` (`ssDatL μ = ssDat μ`): `Ω₁·μ ∈ Tᵗ` by ◇V (V1) (the canonical
term of ◇K, built by T from countable parts `≤` the leaves, which lie in the initial segment `θᵗ`), and `Ω₁·μ + η ∈
Tᵗ` (T, second clause). -/
theorem syArg_mem {τ μ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hEμ : Gg.ggE < μ) (hμG : μ < Gg.ggGam)
    (hμT : Ss.ssDatL μ ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1) : Om1 * (Om1 + μ) + η ∈ Tset τ := by
  have _ := hEμ
  have hB : Om1 + μ < Tf.tfBG := (Tf.tf_Om1_add_lt_gg hμG).trans Tf.tf_gg_lt_BG
  exact tfArg_mem hτ hτ1 le_self_add hB (by rwa [Tf.tfDatL_eq_ss hμG]) hη hηΩ

/-- **Theorem (formerly an axiom)**: the instance `M = Ω₁ + μ` of `R2.tfArg_dat`.
**[W07a] Def 3.22, Theorem 3.23, the Remark after Corollary 3.24, Def 3.1, Lemma 3.3, Lemma 3.5, Lemma 4.2,
Def 3.28, Lemma 3.30 (`m = 0, 1, 2`)** (texts T, Θ, U, D, B, W, S, L): for a level `E₁ < μ < Γ_{Ω₁+1}` and `η < Ω₁` with
`Ω₁·(Ω₁ + μ) + η ∈ Tᵗ`: `ssDatL μ ∈ Tᵗ` (the field `dat` of `Sv.SvCit Γ_{Ω₁+1}`).

Our steps.  `ξ := Ω₁·μ + η` (`Ω₁ + μ = μ`).  By U its term is unique; its components are in `Tᵗ` (S, second clause),
and those `≥ Ω₁` sum to `Ω₁·μ` (`η < Ω₁`), which is in `Tᵗ` (T).  ◇V (V1) at the code `Ω₁·μ` (◇I: the term is the
canonical term) and ◇Δ: `ssDat μ ∈ Tᵗ`. -/
theorem syArg_dat {τ μ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hEμ : Gg.ggE < μ) (hμG : μ < Gg.ggGam)
    (hηΩ : η < Om1) (h : Om1 * (Om1 + μ) + η ∈ Tset τ) : Ss.ssDatL μ ∈ Tset τ := by
  have _ := hEμ
  have hB : Om1 + μ < Tf.tfBG := (Tf.tf_Om1_add_lt_gg hμG).trans Tf.tf_gg_lt_BG
  rw [← Tf.tfDatL_eq_ss hμG]; exact tfArg_dat hτ hτ1 le_self_add hB hηΩ h

/-- **Theorem (formerly an axiom)**: the instance `M = Ω₁ + μ` of `R2.tfVt_lt`.
**[W07a] Lemma 3.30, the direction `⇐`, with Def 3.28** (texts L, S, and the steps ◇): for a level
`E₁ < μ < Γ_{Ω₁+1}` and `M' ≤ Ω₁ + μ` with `ssDat M', ssDatL μ ∈ Tᵗ`, `η', η ∈ Tᵗ ∩ Ω₁`, `Ω₁·M' + η' < Ω₁·(Ω₁ + μ) +
η` and `ssDat M', η'` below `ϑᵗ(Ω₁·(Ω₁ + μ) + η)`: `ϑᵗ(Ω₁·M' + η') < ϑᵗ(Ω₁·(Ω₁ + μ) + η)` (the field `vt_lt`).

Our steps.  `α := Ω₁·M' + η'` and `γ := Ω₁·(Ω₁ + μ) + η` lie in `Tᵗ ∩ Ω₂` (◇Δ; `M' ≤ μ < Γ_{Ω₁+1}` is a code).
`α^* ≤ max(ssDat M', η') < ϑ₀(γ)` (◇Δ, the hypotheses).  So `α < γ ∧ α^* < ϑ₀(γ)`, the first disjunct of the right side
of L (`m = 0`), and `ϑ₀(α) < ϑ₀(γ)`. -/
theorem syVt_lt {τ M' η' μ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hEμ : Gg.ggE < μ) (hμG : μ < Gg.ggGam)
    (hM' : M' ≤ Om1 + μ) (hM'T : Ss.ssDat M' ∈ Tset τ) (hη' : η' ∈ Tset τ) (hη'Ω : η' < Om1)
    (hμT : Ss.ssDatL μ ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (harg : Om1 * M' + η' < Om1 * (Om1 + μ) + η) (hd' : Ss.ssDat M' < vt τ (Om1 * (Om1 + μ) + η))
    (hη'v : η' < vt τ (Om1 * (Om1 + μ) + η)) : vt τ (Om1 * M' + η') < vt τ (Om1 * (Om1 + μ) + η) := by
  have _ := hEμ
  have hB : Om1 + μ < Tf.tfBG := (Tf.tf_Om1_add_lt_gg hμG).trans Tf.tf_gg_lt_BG
  have hM'G : M' < Gg.ggGam := hM'.trans_lt (Tf.tf_Om1_add_lt_gg hμG)
  exact tfVt_lt hτ hτ1 le_self_add hB hM' (by rwa [Tf.tfDat_eq_ss M' hM'G]) hη' hη'Ω
    (by rwa [Tf.tfDatL_eq_ss hμG]) hη hηΩ harg (by rwa [Tf.tfDat_eq_ss M' hM'G]) hη'v

/-- **Theorem (formerly an axiom)**: the instance `M = Ω₁ + μ` of `R2.tfLt_of_vt_lt`.
**[W07a] Lemma 3.30, the direction `⇒`, with Def 3.28** (texts L, S, and the steps ◇): for a level
`E₁ < μ < Γ_{Ω₁+1}` with `ssDatL μ ∈ Tᵗ`, `ξ ∈ Tᵗ ∩ Ω₂`, `η ∈ Tᵗ ∩ Ω₁`, `ssDatL μ, η < ϑᵗ(ξ)`:
`ϑᵗ(ξ) < ϑᵗ(Ω₁·(Ω₁ + μ) + η)` implies `ξ < Ω₁·(Ω₁ + μ) + η` (the field `lt_of`).

Our steps.  `γ := Ω₁·(Ω₁ + μ) + η ∈ Tᵗ ∩ Ω₂` and `γ^* ≤ max(ssDatL μ, η) < ϑ₀(ξ)` (◇Δ, the hypotheses).  L (`m = 0`,
`α = ξ`): `ϑ₀(ξ) < ϑ₀(γ)` gives `ξ < γ ∧ ξ^* < ϑ₀(γ)` or `ϑ₀(ξ) ≤ γ^*`; the second is impossible.  So `ξ < γ`. -/
theorem syLt_of_vt_lt {τ ξ μ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hEμ : Gg.ggE < μ) (hμG : μ < Gg.ggGam)
    (hξ : ξ ∈ Tset τ) (hξ2 : ξ < OmTwo) (hμT : Ss.ssDatL μ ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (hdξ : Ss.ssDatL μ < vt τ ξ) (hηξ : η < vt τ ξ) (h : vt τ ξ < vt τ (Om1 * (Om1 + μ) + η)) :
    ξ < Om1 * (Om1 + μ) + η := by
  have _ := hEμ
  have hB : Om1 + μ < Tf.tfBG := (Tf.tf_Om1_add_lt_gg hμG).trans Tf.tf_gg_lt_BG
  exact tfLt_of_vt_lt hτ hτ1 le_self_add hB hξ hξ2 (by rwa [Tf.tfDatL_eq_ss hμG]) hη hηΩ
    (by rwa [Tf.tfDatL_eq_ss hμG]) hηξ h

/-- **Theorem (formerly an axiom)**: the instance `M = Ω₁ + μ` of `R2.tfLevel_lt`.
**[W07a] Lemma 3.30 (`α^* < ϑ₀(α)`), Lemma 4.3, Def 3.28, Convention 4.1** (texts L, E, S, C, and the steps ◇):
for a level `E₁ < μ < Γ_{Ω₁+1}` with `ssDatL μ ∈ Tᵗ` and `η ∈ Tᵗ ∩ Ω₁`: `ssDatL μ, η < ϑᵗ(Ω₁·(Ω₁ + μ) + η)` (the
field `level`).

Our steps.  `γ := Ω₁·μ + η ∈ Tᵗ ∩ Ω₂` (◇Δ) with `Δ = Ω₁·μ > 0` (C).  L (`m = 0`): `γ^* < ϑ₀(γ) =: q`; E: `τ < q ∈ E`.
◇Δ (last clause, `ξ' = γ`): `ssDat μ < q`.  The additive components of `η` are `< τ` or `≤ η^* ≤ γ^*` (step ★1 of
`R2.CitedLu`; `P₀(η) ⊆ P₀(γ)`), hence `< q`, and `q` is additive principal: `η < q`. -/
theorem syLevel_lt {τ μ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hEμ : Gg.ggE < μ) (hμG : μ < Gg.ggGam)
    (hμT : Ss.ssDatL μ ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    Ss.ssDatL μ < vt τ (Om1 * (Om1 + μ) + η) ∧ η < vt τ (Om1 * (Om1 + μ) + η) := by
  have _ := hEμ
  have hB : Om1 + μ < Tf.tfBG := (Tf.tf_Om1_add_lt_gg hμG).trans Tf.tf_gg_lt_BG
  rw [← Tf.tfDatL_eq_ss hμG]
  exact tfLevel_lt hτ hτ1 le_self_add hB (by rwa [Tf.tfDatL_eq_ss hμG]) hη hηΩ

/-- **Theorem (formerly an axiom)**: `R2.tfPhi_TB` below `Γ_{Ω₁+1}`.
**[W07a] Def 5.1 (all four clauses), Lemma 5.3 (b)–(d), Def 3.28, Def 3.22, Def 3.1, Lemma 3.3, Lemma 3.5,
Lemma 4.2, Lemma 4.3, Lemma 3.30** (texts P, Π, S, T, D, B, W, E, L, and the steps ◇): for bases `σ < τ` and an
`ε`-number `φ(a, c) ∈ (Ω₁, Γ_{Ω₁+1})` in normal form (`1 ≤ a`, `a, c < φ(a, c)`): `φ(a, c) ∈ Tᵗ[σ] ⇔ a, c ∈ Tᵗ[σ]`,
and then `π_{σ,τ}(φ(a, c)) = φ(π_{σ,τ}(a), π_{σ,τ}(c))` (the field `eps` of `Sv.SvCitPi Γ_{Ω₁+1}`).

Our steps.  Step π3 of ◇π in the module docstring (the term `ϑ₁(Ω₂·a + c*)` of ◇K, ◇P, ◇I; the parameters through
S; the value through P, third clause with `k = 1, 2`, and the fixed-point shift O6 kept by `π` through ◇F). -/
theorem syPhi_TB {σ τ a c : Ordinal.{0}} (h : Bases σ τ) (ha : 1 ≤ a) (haz : a < veblen a c)
    (hcz : c < veblen a c) (h1 : Om1 < veblen a c) (hG : veblen a c < Gg.ggGam) :
    (veblen a c ∈ TB τ σ ↔ a ∈ TB τ σ ∧ c ∈ TB τ σ) ∧
      (a ∈ TB τ σ → c ∈ TB τ σ → pi σ τ (veblen a c) = veblen (pi σ τ a) (pi σ τ c)) :=
  tfPhi_TB h ha haz hcz h1 (hG.trans Tf.tf_gg_lt_BG)

/-- **Theorem (formerly an axiom)**: `R2.tfOpow_TB` below `Γ_{Ω₁+1}`.
**[W07a] Def 5.1 (first three clauses), Lemma 5.3 (b)–(d), Def 3.28, Def 3.22, Lemma 3.5, Lemma 4.2, Lemma 3.30**
(texts P, Π, S, T, W, L, and the steps ◇): for bases `σ < τ` and `g ≥ E₁`, not an `ε`-number, with `ω^g <
Γ_{Ω₁+1}`: `ω^g ∈ Tᵗ[σ] ⇔ g ∈ Tᵗ[σ]`, and then `π_{σ,τ}(ω^g) = ω^{π_{σ,τ}(g)}` (the field `opow`).

Our steps.  Step π2 of ◇π: `ω^g = ϑ₁(g⁻)` (◇N), `Parᵗ(ω^g) = Parᵗ(g⁻)` (S, `k = 1`), `π(ω^g) = ϑ₁(π(g⁻))` (P, third
clause), `π(g⁻) = (π g)⁻` (◇F, π3), and `ϑ₁((π g)⁻) = ω^{π g}` (◇N). -/
theorem syOpow_TB {σ τ g : Ordinal.{0}} (h : Bases σ τ) (hg : Gg.ggE ≤ g) (hgE : ω ^ g ≠ g)
    (hG : ω ^ g < Gg.ggGam) :
    (ω ^ g ∈ TB τ σ ↔ g ∈ TB τ σ) ∧ (g ∈ TB τ σ → pi σ τ (ω ^ g) = ω ^ pi σ τ g) :=
  tfOpow_TB h hg hgE (hG.trans Tf.tf_gg_lt_BG)

end Googology.Trans.PoR.InaccPsi.R2
