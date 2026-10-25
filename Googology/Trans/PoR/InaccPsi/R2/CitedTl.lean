import Googology.Trans.PoR.InaccPsi.R2.CitedUc

set_option autoImplicit false

/-!
# The generic citation of Wilken 2007: Lemma 3.30, Def 3.28, Def 5.1 / Lemma 5.3 ONCE for every level `Ω₁ ≤ M < X`

**Round 98: this file has no axiom left.**  The eight facts below are theorems: the instances `M < X` (and the atoms
`F_β(y) < X`, the codes below `X`) of the generic citation `R2.CitedUc` (levels `Ω₁ ≤ M < B₂`, `X < B₂ < Ω₂`,
`Uc.uc_X_lt_B`), with `Uc.ucDat = Tl.tlDat` below `X` (`Uc.ucDat_lt_X`) and the parts of an atom `F_β(y) < X` equal to
`{β, y}` (`Uc.ucParts_F`, `Uc.ucRebuild_F`).  The literal texts and steps below are kept as their reading;
`R2.CitedUc` states them once for every level below `B₂`.

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

Conventions as in `R2.CitedTf` (`Ω₁ = Om1`, `Ω₂ = OmTwo`, `Tset τ = Tᵗ`, `Par τ = Parᵗ`, `vt τ = ϑᵗ = ϑ₀`, `pi σ τ =
π_{σ,τ}`, `TB τ σ = Tᵗ[σ]`, every base `τ` a countable `ε`-number, `φ(a, c) = veblen a c`, `E₁ = ε_{Ω₁+1}`).
`F_β = Rh.rhF β = veblenWith Γ β` (`F₀ = Γ`; for `β ≥ 1`, `F_β` enumerates the strongly critical common fixed points
of the `F_{β'}`, `β' < β`; `F_{β+1}` enumerates the fixed points of `F_β`).  `g(β) = F_β(0)` is normal and `X =
Tl.tlX` is its least fixed point above `Ω₁` (`B_Γ < X < Ω₂`, `Tl.tl_BG_lt_X`, `Tl.tlX_lt_Om2`).  A **code** is an
ordinal `z < X`.  Below `X` every strongly critical `z > Ω₁` is an **atom** `z = F_λ(y)` in normal form: `λ = Tl.tlLev
z` (the least `β` with `F_β(z) ≠ z`), `y = Tl.tlI λ z`, `λ, y < z` (`Tl.tl_nf`), and `(λ, y)` is the unique pair with
`z = F_λ(y)`, `y < F_λ(y)` (`Tl.tlLev_F`); `λ = 0` gives the atoms `Γ_ν` of `R2.CitedTf`.  The **leaves** of a code
are read by `Tl.tlDat`: as `Tf.tfDat` (`Tl.tlDat_eq_tf` below `B_Γ`), with the new clause: for an atom `F_λ(y)`,
`λ ≥ 1`, the leaves of `λ` and of `y` (`Tl.tlDat_F`).  The arguments are `ξ = Ω₁·M + η` with `η ∈ Tᵗ ∩ Ω₁`, for
**every** level `Ω₁ ≤ M < X` (Convention 4.1: `Δ = Ω₁·M`).

This file widens `R2.CitedTf` (levels `M < B_Γ`) to `X`; the eight axioms of `R2.CitedTf` are theorems derived from
the eight below (same names and statements, in `R2.CitedTf`), so the number of axioms does not change.  What is
**not** restated is the list of `R2.CitedTf` (checked first, every `Cited*` file of `R2`); none of those mentions an
atom `F_λ(y)` with `λ ≥ 1`, a code in `[B_Γ, X)` in `Tᵗ`, or `π` there.

Literal texts: (D) Def 3.1, (B) Lemma 3.3, (W) Def 3.4, Lemma 3.5, Lemma 4.2, (EX) Corollary 3.21, (T) Def 3.22,
(Θ) Theorem 3.23 (first part cut), Corollary 3.24, (U) the Remark after Corollary 3.24, (S) Def 3.28, (L) Lemma 3.30,
(C) Convention 4.1, (E) Lemma 4.3, (P) Def 5.1 (four clauses), (Π) Lemma 5.3 (b)–(d): **the quotations of
`R2.CitedSy`, word for word** (checked again against the paper for this file).  The ones used most:
* (D) Def 3.1 (end): "`ϑⁿ_m(α) := min({ξ < Ω_{m+1} | Cⁿ_m(α, ξ) ∩ Ω_{m+1} ⊆ ξ ∧ α ∈ Cⁿ_m(α, ξ)} ∪ {Ω_{m+1}})`.  Note
  that we have `ϑⁿ_m(0) = Ω_m` for `m < n`."  The set `Cⁿ_m(α, β)` is generated from `Ω_m ∪ β` by `+`, by `ξ ↦ ϑⁿ_k(ξ)`
  on `Ω_{k+2}` for `m < k < n`, and by `ξ ↦ ϑⁿ_m(ξ)` on `α`.
* (B) Lemma 3.3: "(a) `ϑⁿ_m(α) = Cⁿ_m(α, ϑⁿ_m(α)) ∩ Ω_{m+1}`.  (b) `ϑⁿ_m(α) ∈ P ∩ [Ω_m, Ω_{m+1}]`.  (c) Let `ξ =ANF ξ₁
  + ⋯ + ξ_l`.  Then `ξ ∈ Cⁿ_m(α, β)` iff `ξ₁, …, ξ_l ∈ Cⁿ_m(α, β)`."
* (L) Lemma 3.30: "For `m < ω` the function `ϑ_m ↾ Tᵗ ∩ Ω_{m+2}` is 1-1 and has values in `P ∩ [Ω_m, Ω_{m+1})`.  Let
  `α, γ ∈ Tᵗ ∩ Ω_{m+2}`.  Then `α^{*m} < ϑ_m(α)` and `ϑ_m(α) < ϑ_m(γ) ⇔ α < γ ∧ α^{*m} < ϑ_m(γ) ∨ ϑ_m(α) ≤ γ^{*m}`."
* (P) Def 5.1: "`Tᵗ[σ] := {α ∈ Tᵗ | Parᵗ(α) ⊆ σ}` and `π_{σ,τ} : Tᵗ[σ] → T^σ` by the following clauses: • `π_{σ,τ}(ξ)
  := ξ` if `ξ < σ` • `π_{σ,τ}(ξ) := π_{σ,τ}(ξ₁) + π_{σ,τ}(ξ₂)` if `ξ =NF ξ₁ + ξ₂ > τ` • `π_{σ,τ}(ξ) := ϑ_k(π_{σ,τ}(η))`
  if `ξ = ϑ_k(η)` for some `k > 0` and `η ∈ Tᵗ[σ] ∩ Ω_{k+2}` • `π_{σ,τ}(ξ) := ϑ^σ(π_{σ,τ}(η))` if `ξ = ϑᵗ(η)` for some
  `η ∈ Tᵗ[σ] ∩ Ω₂`."  (Π) Lemma 5.3: "(b) `π_{σ,τ}` preserves `<`.  (c) `π_{σ,τ}` preserves ordinal addition.
  (d) `π_{σ,τ}` maps `Tᵗ[σ]` onto `T^σ`."

Our steps.  They are the steps of `R2.CitedTf` (◇O*, ◇P*, ◇Γ, ◇K*, ◇I*, ◇V*, ◇Δ*, ◇F*, ◇π*, and through them those
of `R2.CitedSy`: h1–h4, ◇N, ◇M) with the bound `B_Γ` replaced by `X`, the data by `Tl.tlDat`, and the following
changes, in full.  `n ≥ 3` is fixed with `Ω₂²·3 < θⁿ₂` (Θ, EX), `C(α, β) := Cⁿ₁(α, β)`, so `ϑ₁ = ϑⁿ₁` below `Ω₂²·3`.
* (◇O′) **The hierarchy `F_β`.**  `Fix_β := {y | F_β(y) = y} = ran F_{β+1}` (closed); `ran F_β ⊆ Fix_{β'}` for `β' < β`;
  a strongly critical `x` with `F_{β'}(x) = x` for every `β' < β` is in `ran F_β` (`Rh.rhF_range`).  For `β < Ω₂`:
  `F_β(Ω₁) = Ω₁` if `β < Ω₁` (`Ω₁` is regular, `Tl.tl_rhF_lt`, continuity), `F_{Ω₁}(0) = Ω₁` (no countable `x` is fixed
  by `F_{x+1}`), and `F_β(0) > β` for `Ω₁ < β < X` (`β` is not a fixed point of `g`).  Put `L_β := {y | F_β(y) > max(Ω₁,
  β)}` (`(Ω₁, ∞)` for `β < Ω₁`, `[1, ∞)` for `β = Ω₁`, all `y` for `Ω₁ < β < X`), `Y_β := L_β ∖ Fix_β`, and `W(β, c) :=
  F_β(y_c)`, `y_c` the `c`-th element of `Y_β`: the enumeration of the values of `F_β` above `max(Ω₁, β)` that are not
  fixed points of `F_β`.  (Φ1) For `x ∈ Fix_β`, `x > max(Ω₁, β)`, and `c < x`: the successor ordinals of `(max(Ω₁, β),
  x)` lie in `Y_β` (values of `F_β` are limits) and have order type `x` (`x` is strongly critical), so `y_c < x` and
  `W(β, c) < F_β(x) = x`.  (Φ2) If `(β', c') < (β, c)` lexicographically and `β', c' < W(β, c)`, then `W(β', c') < W(β,
  c)` (`β' = β`: `c' < c`; `β' < β`: `W(β, c) ∈ ran F_β ⊆ Fix_{β'}`, Φ1). (Φ3) `max(Ω₁, β) < W(β, c)` and `c ≤ y_c <
  F_β(y_c)`.  (Φ4) If `ξ₀ > Ω₁` is strongly critical, `β ≤ ξ₀`, and `W(β', c') < ξ₀` for all `β' < β`, `c' < ξ₀`, then
  `ξ₀ ∈ ran F_β`: a value `F_{β'}(y)`, `y < ξ₀`, is `≤ max(Ω₁, β') < ξ₀`, `= y`, or `W(β', c'')` with `c'' ≤ y`, so
  `F_{β'}(ξ₀) = ξ₀` by continuity.  (Φ6) For an atom `z = F_λ(y)` in normal form (`λ < z`, `y < z`, `y ∉ Fix_λ`, so `y ∈
  Y_λ`): `z = W(λ, c)` with `c := otp(Y_λ ∩ y) ≤ y`; if `p := max(Fix_λ ∩ L_λ ∩ (y + 1))` exists, then `p < y`, `y = p +
  1 + d` and `c = p + d` (Φ1 at `x = p`); otherwise `c = −(Ω₁ + 1) + y`, `−1 + y`, `y` for `λ < Ω₁`, `= Ω₁`, `> Ω₁`.  So
  `c` and `y` have the same Cantor normal form up to one copy of `Ω₁` and the finite tail, and **the leaves of `c` and
  of `y` agree up to finite ones**.  For `λ = 0` this is the indexing of ◇Γ (`y = Ω₁ + 1 + c` below `B_Γ`).
* (◇Φ) **The correspondence: `ϑ₁(Ω₂² + Ω₂·β + c) = W(β, c)` for all `β, c < Ω₂`** (it contains ◇Γ, `β = 0`; for `β =
  1` the values are the fixed points of `Γ` above `Ω₁`; note `ϑ₁(Ω₂²·2)` is not of this form).  Induction on `ζ :=
  Ω₂² + Ω₂·β + c`; `v := W(β, c)` is strongly critical (Φ3: `v > Ω₁`).  Write `β =CNF Σ ω^{b_i}·k_i`.
  `≤`: `β, c < v` (Φ3), so the `b_i < v` and `ζ = ϑⁿ₂(ϑⁿ₂(0)) + Σ ϑⁿ₂(b_i)·k_i + c ∈ C(ζ, v)` (h1: `ϑⁿ₂(0) = Ω₂`,
  `ϑⁿ₂(Ω₂) = Ω₂²`, `ϑⁿ₂(x) = Ω₂·ω^x` for `1 ≤ x < Ω₂`).  By induction on the generation of `C(ζ, v)`: every member
  `u < Ω₂` is `< v`; every member in `[Ω₂, Ω₂²)` is `Ω₂·a' + c'` with `a', c' < v` (h3); every member in `[Ω₂², Ω₂²·2)`
  is `Ω₂² + Ω₂·β' + c'` with `β', c' < v`; all others are `≥ Ω₂²·2`.  Generators: `Ω₁ ∪ v`; `ϑⁿ₂(x)` is `Ω₂·ω^x` or
  `Ω₂` (`x < Ω₂`, so `x < v`, `ω^x < v`), `Ω₂²` (`x = Ω₂`), or `≥ Ω₂²·ω` (`Ω₂ < x < Ω₃`: `ϑⁿ₂(x) ≥ ϑⁿ₂(Ω₂ + 1) =
  ω̄_{Ω₂·2+1} = Ω₂²·ω`, W with `m = 2`; `Ω₃ ≤ x < Ω₄`: `ϑⁿ₂(x) > Ω₂²` is additive principal (h2, B (b))); `ϑⁿ_k(x) ≥
  Ω₃` for `k ≥ 3`; `ϑⁿ₁(ξ)` with `ξ ∈ C ∩ ζ`: `ξ < Ω₂` gives `ϑⁿ₁(ξ) < v` (h4); `ξ = Ω₂·a' + c'`, `1 ≤ a'`, `a', c'
  < v`, gives `V(a', c') < v` (◇P*, O4 at the strongly critical `q = v`); `ξ = Ω₂² + Ω₂·β' + c' < ζ` with `β', c' <
  v` has `(β', c') < (β, c)` lexicographically and `ϑⁿ₁(ξ) = W(β', c') < v` (i.h., Φ2).  Sums: `v` is additive
  principal; `u + (Ω₂² + w) = Ω₂² + w` for `u < Ω₂²`; `(Ω₂² + Ω₂·β₁ + c₁) + (Ω₂·a₂ + c₂) = Ω₂² + Ω₂·(β₁ + a₂) + c₂`
  for `a₂ ≥ 1` (and `= Ω₂² + Ω₂·β₁ + (c₁ + c₂)` for `a₂ = 0`), with `β₁ + a₂, c₁ + c₂ < v`; a sum with two summands
  `≥ Ω₂²` or one `≥ Ω₂²·2` is `≥ Ω₂²·2`.  So `C(ζ, v) ∩ Ω₂ ⊆ v`, and D gives `ϑⁿ₁(ζ) ≤ v`.
  `≥`: suppose `ξ₀ := ϑⁿ₁(ζ) < v`.  By D and B (a), `ζ ∈ C(ζ, ξ₀)` and `ξ₀ = C(ζ, ξ₀) ∩ Ω₂`.  As in ◇Γ (`R2.CitedTf`),
  `Ω₁ < ξ₀` and `ξ₀` is closed under every `φ(a', ·)`, `a' < ξ₀` (◇P*, h4: `Ω₂·a' + c' < Ω₂² ≤ ζ`): `ξ₀` is strongly
  critical.  By B (c) the components of `ζ` are in `C`: a component `Ω₂·ω^{b_i}` is additive principal in `[Ω₂, Ω₂²)`,
  so it is a generator `ϑⁿ₂(x)` with `x = b_i ∈ C ∩ Ω₂` (h1, h2), and `c ∈ C ∩ Ω₂`; so `b_i, c < ξ₀`, and `β < ξ₀`
  (`ξ₀` is an `ε`-number).  For `(β', c') < (β, c)` lexicographically with `β', c' < ξ₀`: `Ω₂² + Ω₂·β' + c' ∈ C ∩ ζ`
  (h1), so `W(β', c') = ϑⁿ₁(Ω₂² + Ω₂·β' + c') < ξ₀` (i.h.).  By Φ4 (with `β' < β`), `ξ₀ ∈ ran F_β`.  If `ξ₀ ∉ Fix_β`,
  then `ξ₀ = W(β, c₀)` (`ξ₀ > max(Ω₁, β)`), and `W(β, c') < ξ₀` for all `c' < c` gives `c ≤ c₀`, `v ≤ ξ₀`; if `ξ₀ ∈
  Fix_β`, `v < ξ₀` (Φ1, `c < ξ₀`).  Both contradict `ξ₀ < v`.  So `ϑ₁(Ω₂² + Ω₂·β + c) = W(β, c)` (EX, T), independent of
  `τ` (D: `Ω₀ = τ` enters `Cⁿ_m` only for `m = 0`).  `X` is not of this form (`λ, y < X` give `F_λ(y) < X`); the
  same two arguments at `ζ = Ω₂²·2` (`≤`: `v = X` is a fixed point of every `F_{β'}`, `β' < X`, Φ1; `≥`: by Φ4 `ξ₀ ∈
  ran F_{ξ₀}`, so `ξ₀ = F_{ξ₀}(0)`, a fixed point of `g` above `Ω₁`) give `ϑ₁(Ω₂²·2) = X`, where the citation stops
  (a remark, not used below).
* (◇K′) **The canonical term of a code `z ∈ [Ω₁, X)`.**  As ◇K* of `R2.CitedTf`, and for an atom `z = F_λ(y)` in
  normal form: **`arg z = Ω₂² + Ω₂·λ + c`** with `c` of Φ6 (◇Φ), where `Ω₂·λ = Σ ϑ₂(l_i)·k_i` for `λ =CNF Σ
  ω^{l_i}·k_i` (h1) and `Ω₂² = ϑ₂(ϑ₂(0))`.  The parts `l_i`, `λ`, `c` are countable or codes `< z`.  Its countable
  parts are those of the countable `c`, the exponents `l_i` of a countable `λ`, and those of the parts of `λ`, `c` that
  are codes; by Φ6 and ◇K* every countable part is `≤` a leaf of `z`, and every leaf of `z` (a leaf of `λ` or of `y`) is
  finite, a countable part `x`, `1 + x`, or a countable `λ = Σ ω^{l_i}·k_i` of countable parts `l_i`.  So ◇K's relation
  of countable parts and leaves holds for every code below `X`; ◇M verbatim (arguments of `ϑ₁`, `ϑ₂` are `< Ω₂²·2 <
  Ω₃`).
* (◇I′) As ◇I*; an additive principal component `y' ≥ Ω₁` of a code in `Tᵗ` is `ϑ₁(ζ)`, `ζ ∈ Tᵗ ∩ Ω₃`, and L
  (`m = 1`) over `κ` with ◇Φ gives `ζ = arg y'`; L (`m = 2`) and h1 give the `ϑ₂`-terms `ϑ₂(l_i)` of its components
  `Ω₂·ω^{l_i}` and `ϑ₂(ϑ₂(0))` of `Ω₂²`.
* (◇V′), (◇Δ′) ◇V*, ◇Δ* verbatim with `tlDat` for `tfDat` (◇K′, ◇I′, ◇M; `P₀(F_λ(y)) = P₀(λ) ∪ P₀(c)` by S along
  `ϑ₁(ϑ₂(ϑ₂(0)) + Σ ϑ₂(l_i)·k_i + c)`, and the leaves of `c`, `y` agree up to finite ones, Φ6), for every code `M' < X`
  (`M' < Ω₁` allowed) and every level `Ω₁ ≤ M < X`.
* (◇F′) ◇F* for `0 ≤ b < X` and codes `y < X` (an atom `lead(y) = F_λ(y₁)` is strongly critical: if `φ(b, lead(y)) =
  lead(y)`, `p = lead(y)`; otherwise `b ≥ lead(y)` and every `p ∈ F_b` has `p = φ(b, p) > b ≥ lead(y)`), and the same
  for the hierarchy: **for a code `λ < X` and a code `y ∈ Tᵗ` with `p := max(Fix_λ ∩ L_λ ∩ (y + 1))` existing, `p ∈ Tᵗ`
  and `Parᵗ(p) ⊆ Parᵗ(y) ∪ ω`.**  Induction on `y`: `p` is strongly critical, so `p ≤ lead(y)`, a component of `y` (S).
  If `lead(y) ∈ Fix_λ`, `p = lead(y)`.  If `lead(y) = ω^e` is not an `ε`-number, `p ≤ e` (◇N, i.h. at `e < y`).  If
  `lead(y) = φ(a₂, c₂)` is an `ε`-number, not strongly critical, `p = φ(a₂, p) < φ(a₂, c₂)` gives `p < c₂` (O6, i.h.).
  If `lead(y) = F_{λ₂}(y₂)` is an atom not in `Fix_λ`: `λ₂ ≤ λ` (`λ₂ > λ` would put it in `ran F_{λ₂} ⊆ Fix_λ`), so
  `p ∈ Fix_λ ⊆ Fix_{λ₂}`, `p = F_{λ₂}(p) < F_{λ₂}(y₂)` gives `p < y₂`, `y₂ ∈ Tᵗ` with `Parᵗ(y₂) ∪ ω = Parᵗ(c₂) ∪ ω`
  (◇I′, Φ6), `y₂ < y`: i.h.
* (◇π′) **Base change** (`Bases σ τ`), by induction on the ordinal, as ◇π* with (π0′) for an atom `z = F_λ(y)` in normal
  form: `Parᵗ(z) ∪ ω = Parᵗ(λ) ∪ Parᵗ(c) ∪ ω = Parᵗ(λ) ∪ Parᵗ(y) ∪ ω` (S along the term of ◇K′, Φ6, ◇F′); with ◇I′ and
  T, `z ∈ Tᵗ[σ] ⇔ λ, y ∈ Tᵗ[σ]`.  Then `π(z) = ϑ₁(ϑ₂(ϑ₂(π 0)) + Σ ϑ₂(π l_i)·k_i + π c) = ϑ₁(Ω₂² + Ω₂·π λ + π c)` (P,
  second and third clauses, `k = 1, 2`; Π (c)).  `π λ` is `<`, `=`, `> Ω₁` as `λ` is, and `π λ < π z` (Π (b)).  The
  `p` of Φ6 is in `Tᵗ[σ]` (◇F′), and `π p ∈ Fix_{πλ}` (i.h.: `p = F_{λ₃}(y₃)` in normal form with `λ₃ > λ`, `π p =
  F_{πλ₃}(πy₃)`, `πλ₃ > πλ`).  If `Fix_{πλ} ∩ L_{πλ}` had a member in `(π p, π y]` (in `L_{πλ} ∩ [0, π y]` if there is
  no `p`), the largest one is in `T^σ` (◇F′ over `σ`), it is `π q'` (Π (d)) with `q' ∈ Fix_λ` (i.h.), `p < q' ≤ y`:
  impossible.  And `π y ∉ Fix_{πλ}` (i.h.: an element of `Fix_{πλ}` is an atom of level `> πλ`, and π keeps levels).
  So `π(c)` is the index of `π y` in `Y_{πλ}` (Φ6; `π(p + 1 + d) = π p + 1 + π d`), and `π(z) = W(πλ, π c) = F_{πλ}(π
  y)` (◇Φ over `σ`), again a normal form.  For `λ = 0` this is π0 of ◇π*.  π1, π2, π3 of ◇π* verbatim for the codes
  below `X` (π3 for every `ε`-number `φ(a, c) ∈ (Ω₁, X)` in normal form, not strongly critical; π2 for `ω^g < X`),
  with π0′ for the atoms, ◇P* over any base, ◇F′ for the largest fixed points and O6 (`π a` is `<`, `=`, `> Ω₁` and an
  atom as `a` is).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- **[W07a] Def 3.22, Theorem 3.23, Def 3.1, Lemma 3.3, Lemma 3.5, Lemma 4.2, Def 3.28, Lemma 3.30 (`m = 0, 1, 2`)**
(texts T, Θ, D, B, W, S, L): for a level `Ω₁ ≤ M < X` with `tlDat M ∈ Tᵗ` and `η ∈ Tᵗ ∩ Ω₁`: `Ω₁·M + η ∈ Tᵗ`.

Our steps.  ◇Δ′ of the module docstring: `Ω₁·M ∈ Tᵗ` by ◇V′ (V1) (the canonical term of ◇K′, built by T from the
countable parts, `≤` the leaves, which lie in the initial segment `θᵗ`, the atoms `ϑ₁(ϑ₂(ϑ₂(0)) + Σ ϑ₂(l_i)·k_i +
c)`), and `Ω₁·M + η ∈ Tᵗ` (T, second clause). -/
theorem tlArg_mem {τ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Om1 ≤ M) (hMX : M < Tl.tlX)
    (hMT : Tl.tlDat M ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1) : Om1 * M + η ∈ Tset τ := by
  rw [← Uc.ucDat_lt_X hMX] at hMT
  exact ucArg_mem hτ hτ1 hM1 (hMX.trans Uc.uc_X_lt_B) hMT hη hηΩ

/-- **[W07a] Def 3.22, Theorem 3.23, the Remark after Corollary 3.24, Def 3.1, Lemma 3.3, Lemma 3.5, Lemma 4.2,
Def 3.28, Lemma 3.30 (`m = 0, 1, 2`)** (texts T, Θ, U, D, B, W, S, L): for a level `Ω₁ ≤ M < X` and `η < Ω₁` with
`Ω₁·M + η ∈ Tᵗ`: `tlDat M ∈ Tᵗ`.

Our steps.  By U the term of `Ω₁·M + η` is unique; its components are in `Tᵗ` (S, second clause), and those `≥ Ω₁` sum
to `Ω₁·M` (`η < Ω₁`), which is in `Tᵗ` (T).  ◇V′ (V1) at the code `Ω₁·M` (◇I′: the term is the canonical term) and
◇Δ′: `tlDat M ∈ Tᵗ`. -/
theorem tlArg_dat {τ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Om1 ≤ M) (hMX : M < Tl.tlX)
    (hηΩ : η < Om1) (h : Om1 * M + η ∈ Tset τ) : Tl.tlDat M ∈ Tset τ := by
  rw [← Uc.ucDat_lt_X hMX]
  exact ucArg_dat hτ hτ1 hM1 (hMX.trans Uc.uc_X_lt_B) hηΩ h

/-- **[W07a] Lemma 3.30, the direction `⇐`, with Def 3.28** (texts L, S, and the steps ◇): for a level
`Ω₁ ≤ M < X` and `M' ≤ M` with `tlDat M', tlDat M ∈ Tᵗ`, `η', η ∈ Tᵗ ∩ Ω₁`, `Ω₁·M' + η' < Ω₁·M + η` and `tlDat M', η'`
below `ϑᵗ(Ω₁·M + η)`: `ϑᵗ(Ω₁·M' + η') < ϑᵗ(Ω₁·M + η)`.

Our steps.  `α := Ω₁·M' + η'` and `γ := Ω₁·M + η` lie in `Tᵗ ∩ Ω₂` (◇Δ′; `M' ≤ M < X` is a code).  `α^* ≤ max(tlDat
M', η') < ϑ₀(γ)` (◇Δ′, the hypotheses).  So `α < γ ∧ α^* < ϑ₀(γ)`, the first disjunct of the right side of L (`m = 0`),
and `ϑ₀(α) < ϑ₀(γ)`. -/
theorem tlVt_lt {τ M' η' M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Om1 ≤ M) (hMX : M < Tl.tlX)
    (hM' : M' ≤ M) (hM'T : Tl.tlDat M' ∈ Tset τ) (hη' : η' ∈ Tset τ) (hη'Ω : η' < Om1)
    (hMT : Tl.tlDat M ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (harg : Om1 * M' + η' < Om1 * M + η) (hd' : Tl.tlDat M' < vt τ (Om1 * M + η))
    (hη'v : η' < vt τ (Om1 * M + η)) : vt τ (Om1 * M' + η') < vt τ (Om1 * M + η) := by
  rw [← Uc.ucDat_lt_X (hM'.trans_lt hMX)] at hM'T hd'
  rw [← Uc.ucDat_lt_X hMX] at hMT
  exact ucVt_lt hτ hτ1 hM1 (hMX.trans Uc.uc_X_lt_B) hM' hM'T hη' hη'Ω hMT hη hηΩ harg hd' hη'v

/-- **[W07a] Lemma 3.30, the direction `⇒`, with Def 3.28** (texts L, S, and the steps ◇): for a level
`Ω₁ ≤ M < X` with `tlDat M ∈ Tᵗ`, `ξ ∈ Tᵗ ∩ Ω₂`, `η ∈ Tᵗ ∩ Ω₁`, `tlDat M, η < ϑᵗ(ξ)`: `ϑᵗ(ξ) < ϑᵗ(Ω₁·M + η)`
implies `ξ < Ω₁·M + η`.

Our steps.  `γ := Ω₁·M + η ∈ Tᵗ ∩ Ω₂` and `γ^* ≤ max(tlDat M, η) < ϑ₀(ξ)` (◇Δ′, the hypotheses).  L (`m = 0`, `α = ξ`):
`ϑ₀(ξ) < ϑ₀(γ)` gives `ξ < γ ∧ ξ^* < ϑ₀(γ)` or `ϑ₀(ξ) ≤ γ^*`; the second is impossible.  So `ξ < γ`. -/
theorem tlLt_of_vt_lt {τ ξ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Om1 ≤ M) (hMX : M < Tl.tlX)
    (hξ : ξ ∈ Tset τ) (hξ2 : ξ < OmTwo) (hMT : Tl.tlDat M ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (hdξ : Tl.tlDat M < vt τ ξ) (hηξ : η < vt τ ξ) (h : vt τ ξ < vt τ (Om1 * M + η)) : ξ < Om1 * M + η := by
  rw [← Uc.ucDat_lt_X hMX] at hMT hdξ
  exact ucLt_of_vt_lt hτ hτ1 hM1 (hMX.trans Uc.uc_X_lt_B) hξ hξ2 hMT hη hηΩ hdξ hηξ h

/-- **[W07a] Lemma 3.30 (`α^* < ϑ₀(α)`), Lemma 4.3, Def 3.28, Convention 4.1** (texts L, E, S, C, and the steps ◇):
for a level `Ω₁ ≤ M < X` with `tlDat M ∈ Tᵗ` and `η ∈ Tᵗ ∩ Ω₁`: `tlDat M, η < ϑᵗ(Ω₁·M + η)`.

Our steps.  `γ := Ω₁·M + η ∈ Tᵗ ∩ Ω₂` (◇Δ′) with `Δ = Ω₁·M > 0` (C).  L (`m = 0`): `γ^* < ϑ₀(γ) =: q`; E: `τ < q ∈ E`.
◇Δ′ (last clause, `ξ' = γ`): `tlDat M < q`.  The additive components of `η` are `< τ` or `≤ η^* ≤ γ^*` (step ★1 of
`R2.CitedLu`; `P₀(η) ⊆ P₀(γ)`), hence `< q`, and `q` is additive principal: `η < q`. -/
theorem tlLevel_lt {τ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Om1 ≤ M) (hMX : M < Tl.tlX)
    (hMT : Tl.tlDat M ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    Tl.tlDat M < vt τ (Om1 * M + η) ∧ η < vt τ (Om1 * M + η) := by
  rw [← Uc.ucDat_lt_X hMX] at hMT ⊢
  exact ucLevel_lt hτ hτ1 hM1 (hMX.trans Uc.uc_X_lt_B) hMT hη hηΩ

/-- **[W07a] Def 5.1 (first three clauses), Lemma 5.3 (b)–(d), Def 3.28, Def 3.22, Def 3.1, Lemma 3.3, Lemma 3.5,
Lemma 4.2, Lemma 3.30** (texts P, Π, S, T, D, B, W, L, and the steps ◇): for bases `σ < τ` and an atom `F_β(y)` in
normal form (`y < F_β(y)`) with `Ω₁ < F_β(y) < X`: `F_β(y) ∈ Tᵗ[σ] ⇔ β, y ∈ Tᵗ[σ]`, and then `π_{σ,τ}(F_β(y)) =
F_{π_{σ,τ}(β)}(π_{σ,τ}(y))`.

Our steps.  Step π0′ of ◇π′: `F_β(y) = ϑ₁(Ω₂² + Ω₂·β + c)` (◇Φ, Φ6; `β < F_β(y)`: `β ≤ Ω₁ < F_β(y)`, or `Ω₁ < β <
X` and `F_β(y) ≥ F_β(0) > β`), the parameters through S, the value through P (`k = 1, 2`), Π (c), the shift Φ6 kept by
`π` through ◇F′, and ◇Φ over `σ`.  (`tfGam_TB` of `R2.CitedTf` is the case `β = 0`.) -/
theorem tlAtom_TB {σ τ β y : Ordinal.{0}} (h : Bases σ τ) (h1 : Om1 < Rh.rhF β y) (hX : Rh.rhF β y < Tl.tlX)
    (hy : y < Rh.rhF β y) :
    (Rh.rhF β y ∈ TB τ σ ↔ β ∈ TB τ σ ∧ y ∈ TB τ σ) ∧
      (β ∈ TB τ σ → y ∈ TB τ σ → pi σ τ (Rh.rhF β y) = Rh.rhF (pi σ τ β) (pi σ τ y)) := by
  obtain ⟨hA, hP⟩ := ucAtom_TB h (Rh.rhF_SC β y) h1 (hX.trans Uc.uc_X_lt_B)
  rw [Uc.ucParts_F hX hy] at hA hP
  rw [Uc.ucRebuild_F _ hX hy] at hP
  have hiff : (∀ x ∈ ({β, y} : Set Ordinal.{0}), x ∈ TB τ σ) ↔ β ∈ TB τ σ ∧ y ∈ TB τ σ := by
    constructor
    · intro H; exact ⟨H β (Set.mem_insert _ _), H y (Set.mem_insert_of_mem _ rfl)⟩
    · rintro ⟨hb, hy'⟩ x hx
      rcases hx with rfl | hx
      · exact hb
      · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hy'
  exact ⟨hA.trans hiff, fun hb hy' => hP (hiff.2 ⟨hb, hy'⟩)⟩

/-- **[W07a] Def 5.1 (all four clauses), Lemma 5.3 (b)–(d), Def 3.28, Def 3.22, Def 3.1, Lemma 3.3, Lemma 3.5,
Lemma 4.2, Lemma 4.3, Lemma 3.30** (texts P, Π, S, T, D, B, W, E, L, and the steps ◇): for bases `σ < τ` and an
`ε`-number `φ(a, c) ∈ (Ω₁, X)` in normal form (`1 ≤ a`, `a, c < φ(a, c)`): `φ(a, c) ∈ Tᵗ[σ] ⇔ a, c ∈ Tᵗ[σ]`, and then
`π_{σ,τ}(φ(a, c)) = φ(π_{σ,τ}(a), π_{σ,τ}(c))`.

Our steps.  Step π3 of ◇π′ (the term `ϑ₁(Ω₂·a + c*)` of ◇K′, ◇P*, ◇I′; the parameters through S; the value through P,
third clause with `k = 1, 2`, and the fixed-point shift of O6 kept by `π` through ◇F′; π0′ for the atoms). -/
theorem tlPhi_TB {σ τ a c : Ordinal.{0}} (h : Bases σ τ) (ha : 1 ≤ a) (haz : a < veblen a c)
    (hcz : c < veblen a c) (h1 : Om1 < veblen a c) (hX : veblen a c < Tl.tlX) :
    (veblen a c ∈ TB τ σ ↔ a ∈ TB τ σ ∧ c ∈ TB τ σ) ∧
      (a ∈ TB τ σ → c ∈ TB τ σ → pi σ τ (veblen a c) = veblen (pi σ τ a) (pi σ τ c)) :=
  ucPhi_TB h ha haz hcz h1 (hX.trans Uc.uc_X_lt_B)

/-- **[W07a] Def 5.1 (first three clauses), Lemma 5.3 (b)–(d), Def 3.28, Def 3.22, Lemma 3.5, Lemma 4.2, Lemma 3.30**
(texts P, Π, S, T, W, L, and the steps ◇): for bases `σ < τ` and `g ≥ E₁`, not an `ε`-number, with `ω^g < X`:
`ω^g ∈ Tᵗ[σ] ⇔ g ∈ Tᵗ[σ]`, and then `π_{σ,τ}(ω^g) = ω^{π_{σ,τ}(g)}`.

Our steps.  Step π2 of ◇π′: `ω^g = ϑ₁(g⁻)` (◇N), `Parᵗ(ω^g) = Parᵗ(g⁻)` (S, `k = 1`), `π(ω^g) = ϑ₁(π(g⁻))` (P, third
clause), `π(g⁻) = (π g)⁻` (◇F′, π0′, π3), and `ϑ₁((π g)⁻) = ω^{π g}` (◇N). -/
theorem tlOpow_TB {σ τ g : Ordinal.{0}} (h : Bases σ τ) (hg : Gg.ggE ≤ g) (hgE : ω ^ g ≠ g)
    (hX : ω ^ g < Tl.tlX) :
    (ω ^ g ∈ TB τ σ ↔ g ∈ TB τ σ) ∧ (g ∈ TB τ σ → pi σ τ (ω ^ g) = ω ^ pi σ τ g) :=
  ucOpow_TB h hg hgE (hX.trans Uc.uc_X_lt_B)

end Googology.Trans.PoR.InaccPsi.R2
