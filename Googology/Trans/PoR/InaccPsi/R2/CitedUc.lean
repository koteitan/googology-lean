import Googology.Trans.PoR.InaccPsi.R2.UcAt

set_option autoImplicit false

/-!
# The generic citation of Wilken 2007 ONCE for every level `Ω₁ ≤ M < B₂` (`B₂ = ψ_{Ω₂}(ε_{Ω₂+1})`)

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

Conventions as in `R2.CitedTl` (`Ω₁ = Om1`, `Ω₂ = OmTwo`, `Tset τ = Tᵗ`, `Par τ = Parᵗ`, `vt τ = ϑᵗ = ϑ₀`, `pi σ τ =
π_{σ,τ}`, `TB τ σ = Tᵗ[σ]`, every base `τ` a countable `ε`-number, `φ(a, c) = veblen a c`, `E₁ = ε_{Ω₁+1}`, `F_β =
Rh.rhF β`, `X = Tl.tlX`).  New objects (`R2.UcCmp` … `R2.UcAt`, all Lean-defined, no axiom):
* `E₂ = Uc.ucE = ε_{Ω₂+1}`; for `Ω₂ ≤ γ < E₂`, `γ = Ω₂^e·d + r` (`e = log_{Ω₂} γ < γ`, `0 < d < Ω₂`, `r < Ω₂^e`); the
  **components** `comps(γ)` (`Uc.ucComps`): `{γ}` for `γ < Ω₂`, else `comps(e) ∪ {d} ∪ comps(r)`; `C(γ) = max comps(γ)`
  (`Uc.ucC`); `ucMap f γ` replaces every component `x` by `f x`.
* **`H_γ = Uc.ucH γ`** (`γ < E₂`): the enumeration of the strongly critical `v > Ω₁` with `C(γ) < v` that are fixed
  points of every `H_{γ'}`, `γ' < γ`, with `C(γ') < v` (normal, `Uc.ucG_props`).  For `β < Ω₂`, `H_β` and `F_β` have
  the same values above `max(Ω₁, β)` and the same fixed points there (`Uc.uc_range_F`, `Uc.ucH_fix_iff_F`);
  `H_{Ω₂}(0) = X` (`Uc.ucH_Om2_zero`).
* **`B₂ = Uc.ucB`**: the least strongly critical `z > Ω₁` fixed by every `H_γ`, `γ < E₂`, `C(γ) < z`; `X < B₂ < Ω₂`
  (`Uc.uc_X_lt_B`, `Uc.ucB_lt_Om2`).  Every strongly critical `z ∈ (Ω₁, B₂)` is an **atom**: `F_λ(y)` (normal form of
  `R2.TlDat`) below `X`; from `X` on `z = H_λ(y)` with `λ = Uc.ucLev z` (the least `γ < E₂`, `C(γ) < z`, with
  `H_γ(z) ≠ z`) and `y = Uc.ucI λ z < z`, `C(λ) < z` (`Uc.uc_nf`).  Its **parts** (`Uc.ucParts z`): `λ, y` below `X`;
  `comps(λ), y` from `X` on; `Uc.ucRebuild f z = F_{f λ}(f y)`, resp. `H_{ucMap f λ}(f y)`.
* **The leaves** (`Uc.ucDat`): `Tl.tlDat` below `X`; on `[X, B₂)` the Cantor clause, the Veblen clause, and for an atom
  `H_λ(y)` the leaves of the components of `λ` and of `y`; a **code** is an ordinal `z < B₂`.

Literal texts.  (D) Def 3.1, (B) Lemma 3.3, (L) Lemma 3.30, (P) Def 5.1, (Π) Lemma 5.3 (b)–(d) as quoted in
`R2.CitedTl` (word for word); (T) Def 3.22, (Θ) Theorem 3.23, (EX) Corollary 3.21, (U), (S) Def 3.28,
(C) Convention 4.1, (E) Lemma 4.3 as quoted in `R2.CitedSy`; and
* (W) Def 3.4: "Let `α ↦ ω̄_α` be the enumeration function of the additive principle numbers which are not epsilon
  numbers."  Lemma 4.2: "For any `m < ω` and any `α < Ω_{m+1}` we have `ϑ_m(1 + α) = ω̄_{Ω_m+α}`."
* (T′) Def 3.22: "`T_m` is defined inductively as follows: • `Ω_m ⊆ T_m` • `ξ, η ∈ T_m ⇒ ξ + η ∈ T_m` • `ξ ∈ T_m ∩
  Ω_{k+2} ⇒ ϑ_k(ξ) ∈ T_m` for `k ≥ m`."
* (S′) Def 3.28: "`Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ) ∪ Subᵗ_m(η)` for `ξ, η ∈ Tᵗ` s.t. `α =NF ξ + η > τ`;
  `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ)` if `k ≥ m`, `{α}` if `k < m`, for `α = ϑ_k(ξ)` where `ξ ∈ Tᵗ ∩ Ω_{k+2}`. …
  `Parᵗ(α) := Subᵗ_0(α) ∩ τ`."

Our steps.  They are the steps of `R2.CitedTl` (◇O′, ◇Φ, ◇K′, ◇I′, ◇V′, ◇Δ′, ◇F′, ◇π′ and through them those of
`R2.CitedTf`, `R2.CitedSy`) for the codes below `X`, which are untouched, and the following for the codes in
`[X, B₂)`, in full.  Fix `n ≥ 4`; `C(α, β) := Cⁿ₁(α, β)`, `ϑ₁ = ϑⁿ₁`, `ϑ₂ = ϑⁿ₂` on the arguments used below (EX, Θ:
they are `< E₂·2 < θⁿ₂`, since `E₂ = ϑⁿ₂(ϑⁿ₃(0))`: `C(Ω₃, β)` for `ϑ₂` is the closure of `Ω₂ ∪ β` under `+` and
`ϑ₂(1 + α) = ω̄_{Ω₂+α}`, `α < Ω₃` (W), which is `E₂` for `β ≤ Ω₂`).
* (◇C) **Components.**  For `v` with `Ω₁ < v < Ω₂` strongly critical, `K_v := {γ < E₂ | comps(γ) ⊆ v}` is closed under
  `+` (in `γ₁ + γ₂` the terms of `γ₁` below the leading term of `γ₂` vanish, and two digits `d, d' < v` of the same
  exponent add to `d + d' < v`) and contains `v ∪ {Ω₂}` (`comps(Ω₂) = {1, 0}`).  The base-`ω` normal form of `γ ∈
  [Ω₂, E₂)` is `Σ ω^{Ω₂·e + δ}·k` over the terms `Ω₂^e·d` of `γ` and the base-`ω` terms `ω^δ·k` of the digits `d`, and
  `ω^{Ω₂·e + δ} = ω^{Ω₂ + α} = ϑ₂(α)` with `α = Ω₂·e' + δ`, `e = 1 + e'` (W, `m = 2`; `ϑ₂(0) = Ω₂`).  So `Ω₂·(Ω₂ +
  γ)` has a term built by `+` and `ϑ₂` from `ϑ₂(0)` and the base-`ω` exponents `δ` of the digits of `γ` and of its
  exponents (hereditarily), and the leaves of these `δ` are those of the components up to finite ones (`d = Σ ω^δ·k`).
* (◇H) **The hierarchy `H`.**  `Fix_γ := {y | H_γ(y) = y}`; `W₂(γ, c) := H_γ(y_c)`, `y_c` the `c`-th element of `Ord ∖
  Fix_γ` (the values at indices that are not fixed points).  (Ψ1) For `x ∈ Fix_γ` and `c < x`: the successor ordinals
  below `x` are not in `Fix_γ` (values are limits) and have order type `x`, so `y_c < x` and `W₂(γ, c) < H_γ(x) = x`.
  (Ψ2) If `(γ', c') < (γ, c)` lexicographically and `C(γ'), c' < W₂(γ, c)`, then `W₂(γ', c') < W₂(γ, c)` (`γ' = γ`:
  `c' < c`; `γ' < γ`: `W₂(γ, c)` is a value of `H_γ` with `C(γ')` below it, so in `Fix_{γ'}`; Ψ1).  (Ψ3) `Ω₁, C(γ) <
  W₂(γ, c)` and `c ≤ y_c`.  (Ψ4) If `ξ₀ > Ω₁` is strongly critical, `C(γ) < ξ₀`, and `W₂(γ', c') < ξ₀` for all `γ' <
  γ` with `C(γ') < ξ₀` and all `c' < ξ₀`, then `ξ₀` is a value of `H_γ`: for such `γ'` every `H_{γ'}(y)`, `y < ξ₀`, is
  `y` or `W₂(γ', c'')` with `c'' ≤ y`, hence `< ξ₀`, so `H_{γ'}(ξ₀) = ξ₀` by continuity, and the definition of `H_γ`
  applies.  (Ψ6) For an atom `z = H_λ(y)`, `y < z` (so `y ∉ Fix_λ`): `z = W₂(λ, c)` with `c := otp((Ord ∖ Fix_λ) ∩ y)`;
  if `p := max(Fix_λ ∩ (y + 1))` exists (`Fix_λ` is closed), `p < y`, `y = p + 1 + d` and `c = p + d` (Ψ1 at `x = p`);
  otherwise `c = y`.  So **`c` and `y` have the same leaves up to finite ones**.
* (◇Φ₂) **The correspondence (the own step past `Ω₂²·2`): `ϑ₁(Ω₂·(Ω₂ + γ) + c) = W₂(γ, c)` for all `γ < E₂`, `c <
  Ω₂`.**  For `γ < Ω₂` it is ◇Φ of `R2.CitedTl` (`W₂(β, c) = W(β, c)`: `H_β` and `F_β` agree above `max(Ω₁, β)`); `γ =
  Ω₂`, `c = 0` gives `ϑ₁(Ω₂²·2) = H_{Ω₂}(0) = X`.  Induction on `ζ := Ω₂·(Ω₂ + γ) + c`; `v := W₂(γ, c)` is strongly
  critical with `Ω₁, C(γ), c < v` (Ψ3).  `≤`: `comps(γ), c ⊆ v`, so `ζ ∈ C(ζ, v)` (◇C: the term of `ζ` is built from
  `ϑ₂(0)` and parts `< v` by `+`, `ϑ₂`).  By induction on the generation of `C(ζ, v)`: every member `u < Ω₂` is `< v`;
  every member in `[Ω₂, Ω₂²)` is `Ω₂·a' + c'` with `a', c' < v` (as in ◇Φ); every member in `[Ω₂², E₂)` is `Ω₂·(Ω₂ +
  γ') + c'` with `comps(γ') ⊆ v`, `c' < v` (◇C); all others are `≥ E₂`.  Generators: `Ω₁ ∪ v`; `ϑ₂(x)`, `x < Ω₃`, is
  `Ω₂` or `ω̄_{Ω₂+α}` (`x = 1 + α`, W), in `K_v` when `x` is (◇C), `≥ E₂` when `x ≥ E₂`; `ϑ₂(x)` with `Ω₃ ≤ x < Ω₄` is
  an `ε`-number (W and the injectivity in L: the `ω̄`-values are taken below `Ω₃`) above `Ω₂ = ϑ₂(0)`, so `≥ E₂`;
  `ϑ_k(x) ≥ Ω₃` for `k ≥ 3`; `ϑ₁(ξ)`, `ξ ∈ C ∩ ζ`: `ξ < Ω₂²` gives `ϑ₁(ξ) < v` (◇Φ, h4 and ◇P* below `Γ_{Ω₁+1}`, as
  in ◇Φ: `v` is closed under every `φ(a', ·)`, `a' < v`, and under `F_β`, `β < v`, being a value of `H_γ` with `γ ≥ Ω₂`,
  or `γ < Ω₂` and ◇Φ); `ξ = Ω₂·(Ω₂ + γ') + c' < ζ` with `comps(γ'), c' ⊆ v` has `(γ', c') < (γ, c)` lexicographically
  and `ϑ₁(ξ) = W₂(γ', c') < v` (i.h., Ψ2).  Sums: `v` is additively principal; `u + (Ω₂² + w) = Ω₂² + w` for `u <
  Ω₂²`; sums of members of `[Ω₂², E₂)` stay in it with components in `v` (◇C).  So `C(ζ, v) ∩ Ω₂ ⊆ v` and D gives
  `ϑ₁(ζ) ≤ v`.  `≥`: suppose `ξ₀ := ϑ₁(ζ) < v`.  By D and B (a), `ζ ∈ C(ζ, ξ₀)` and `ξ₀ = C(ζ, ξ₀) ∩ Ω₂`; as in ◇Φ,
  `Ω₁ < ξ₀` and `ξ₀` is strongly critical.  By B (c) the base-`ω` components `ϑ₂(α)` of `ζ` are in `C`, hence (L,
  injectivity, `m = 2`) their arguments, hereditarily, and the exponents `δ` of ◇C are in `C ∩ Ω₂ = ξ₀`; so
  `comps(γ) ⊆ ξ₀` (`ξ₀` is an `ε`-number, `d = Σ ω^δ·k < ξ₀`), `C(γ) < ξ₀`, and `c < ξ₀`.  For `(γ', c') < (γ, c)`
  lexicographically with `C(γ'), c' < ξ₀`: `Ω₂·(Ω₂ + γ') + c' ∈ C ∩ ζ` (◇C), so `W₂(γ', c') = ϑ₁(Ω₂·(Ω₂ + γ') + c') <
  ξ₀` (i.h.).  By Ψ4, `ξ₀` is a value of `H_γ`.  If `ξ₀ ∉ Fix_γ`, `ξ₀ = W₂(γ, c₀)` and `W₂(γ, c') < ξ₀` for all `c' < c`
  gives `c ≤ c₀`, `v ≤ ξ₀`; if `ξ₀ ∈ Fix_γ`, `v < ξ₀` (Ψ1, `c < ξ₀`).  Both contradict `ξ₀ < v`.  So `ϑ₁(Ω₂·(Ω₂ +
  γ) + c) = W₂(γ, c)`, independent of `τ` (D).  `B₂` is not of this form (`C(λ), y < B₂` give `H_λ(y) < B₂`).
* (◇K″) **The canonical term of a code `z ∈ [X, B₂)`.**  As ◇K′, and for an atom `z = H_λ(y)` in normal form: **`arg z
  = Ω₂·(Ω₂ + λ) + c`** with `c` of Ψ6 (◇Φ₂), the term of `Ω₂·(Ω₂ + λ)` that of ◇C.  Its countable parts are those of
  the exponents `δ` of ◇C and of `c`; by Ψ6, ◇C and ◇K′ every countable part is `≤` a leaf of `z`, and every leaf of
  `z` (a leaf of a component of `λ` or of `y`) is finite, a countable part, or `1 +` one.  So ◇K's relation of
  countable parts and leaves holds for every code below `B₂`; ◇M verbatim (arguments of `ϑ₁`, `ϑ₂` are `< E₂ < Ω₃`).
* (◇I″) As ◇I′; an additive principal component `y' ≥ X` of a code in `Tᵗ` is `ϑ₁(ζ)`, `ζ ∈ Tᵗ ∩ Ω₃`, and L (`m = 1`)
  with ◇Φ₂ gives `ζ = arg y'`; L (`m = 2`) and W give the `ϑ₂`-terms of its base-`ω` components.
* (◇V″), (◇Δ″) ◇V′, ◇Δ′ verbatim with `ucDat` for `tlDat` (◇K″, ◇I″, ◇M; `P₀(H_λ(y)) = P₀(λ-part) ∪ P₀(c)` by S along
  the term of ◇K″, and the leaves of `c`, `y` agree up to finite ones, Ψ6), for every code `M' < B₂` and every level
  `Ω₁ ≤ M < B₂`.
* (◇F″) ◇F′ for codes `y < B₂` and the hierarchy `H`: **for a level `λ < E₂` and a code `y ∈ Tᵗ` with `p := max(Fix_λ
  ∩ (y + 1))` existing, `p ∈ Tᵗ` and `Parᵗ(p) ⊆ Parᵗ(y) ∪ ω`.**  Induction on `y`: `p` is strongly critical, so `p ≤
  lead(y)`, a component of `y` (S).  If `lead(y) ∈ Fix_λ`, `p = lead(y)`.  If `lead(y)` is not strongly critical, as in
  ◇F′.  If `lead(y) = F_{λ₂}(y₂)` or `H_{λ₂}(y₂)` is an atom not in `Fix_λ`: if some component `x` of `λ₂` (resp.
  `λ₂` itself) is `≥ p`, then `p = max(Fix_λ ∩ (x + 1))` with `x` a part of `y`, `x < y` (i.h.); otherwise `C(λ₂) < p`,
  and `λ₂ > λ` would put `lead(y)` in `Fix_λ`, so `λ₂ ≤ λ`, `p ∈ Fix_λ ⊆ Fix_{λ₂}` (`p` is a value of `H_λ` with `C(λ₂)
  < p`, or a fixed point of `H_λ`), `p = H_{λ₂}(p) < H_{λ₂}(y₂)` gives `p ≤ y₂`, a part of `y` (◇I″, Ψ6): i.h.
* (◇π″) **Base change** (`Bases σ τ`), by induction on the ordinal, as ◇π′ with (π0″) for an atom `z = H_λ(y) ≥ X` in
  normal form: `Parᵗ(z) ∪ ω = ⋃ Parᵗ(comps(λ)) ∪ Parᵗ(y) ∪ ω` (S along the term of ◇K″, ◇C, Ψ6, ◇F″); with ◇I″ and T′,
  `z ∈ Tᵗ[σ] ⇔ comps(λ), y ⊆ Tᵗ[σ]`.  Then `π(z) = ϑ₁(π(Ω₂·(Ω₂ + λ)) + π c)` (P, third clause, `k = 1`; Π (c)), and
  `π(Ω₂·(Ω₂ + λ)) = Ω₂·(Ω₂ + ucMap π λ)`: by P (third clause, `k = 2`) every `ϑ₂(1 + α)` goes to `ϑ₂(1 + π α)`, `π`
  is additive (Π (c)) and commutes with `ω^·` on the digits (the step π2 of ◇π′ and ◇N), so every term `Ω₂^e·d` goes to
  `Ω₂^{ucMap π e}·π d` (i.h. at `e < γ`); `π` keeps `<` (Π (b)), so `ucMap π λ` is again in normal form.  The `p` of
  Ψ6 is in `Tᵗ[σ]` (◇F″) and `π p ∈ Fix_{ucMap π λ}`; no fixed point of `H_{ucMap π λ}` lies in `(π p, π y]` (the
  largest one would be `π q'` with `q' ∈ Fix_λ ∩ (p, y]`, Π (d), ◇F″ over `σ`); `π y ∉ Fix_{ucMap π λ}`.  So `π c` is
  the index of `π y` (Ψ6; `π(p + 1 + d) = π p + 1 + π d`) and `π(z) = W₂(ucMap π λ, π c) = H_{ucMap π λ}(π y)` (◇Φ₂ over
  `σ`), again a normal form.  Below `X` this is π0′ of `R2.CitedTl`.  π1, π2, π3 of ◇π′ verbatim for the codes below
  `B₂` (π3 for every `ε`-number `φ(a, c) ∈ (Ω₁, B₂)` in normal form, π2 for `ω^g < B₂`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- **[W07a] Def 3.22, Theorem 3.23, Def 3.1, Lemma 3.3, Lemma 3.5, Lemma 4.2, Def 3.28, Lemma 3.30 (`m = 0, 1, 2`)**
(texts T, T′, Θ, D, B, W, S, L): for a level `Ω₁ ≤ M < B₂` with `ucDat M ∈ Tᵗ` and `η ∈ Tᵗ ∩ Ω₁`: `Ω₁·M + η ∈ Tᵗ`.

Our steps.  ◇Δ″ of the module docstring: `Ω₁·M ∈ Tᵗ` by ◇V″ (V1) (the canonical term of ◇K′/◇K″ built by T′ from the
countable parts, `≤` the leaves), and `Ω₁·M + η ∈ Tᵗ` (T′, second clause). -/
axiom ucArg_mem {τ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Om1 ≤ M) (hMB : M < Uc.ucB)
    (hMT : Uc.ucDat M ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1) : Om1 * M + η ∈ Tset τ

/-- **[W07a] Def 3.22, Theorem 3.23, the Remark after Corollary 3.24, Def 3.1, Lemma 3.3, Lemma 3.5, Lemma 4.2,
Def 3.28, Lemma 3.30 (`m = 0, 1, 2`)** (texts T, Θ, U, D, B, W, S, L): for a level `Ω₁ ≤ M < B₂` and `η < Ω₁` with
`Ω₁·M + η ∈ Tᵗ`: `ucDat M ∈ Tᵗ`.

Our steps.  By U the term of `Ω₁·M + η` is unique; its components `≥ Ω₁` sum to `Ω₁·M ∈ Tᵗ` (S, T); ◇V″ (V1) at the
code `Ω₁·M` (◇I″) and ◇Δ″: `ucDat M ∈ Tᵗ`. -/
axiom ucArg_dat {τ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Om1 ≤ M) (hMB : M < Uc.ucB)
    (hηΩ : η < Om1) (h : Om1 * M + η ∈ Tset τ) : Uc.ucDat M ∈ Tset τ

/-- **[W07a] Lemma 3.30, the direction `⇐`, with Def 3.28** (texts L, S, and the steps ◇): for a level `Ω₁ ≤ M < B₂`
and `M' ≤ M` with `ucDat M', ucDat M ∈ Tᵗ`, `η', η ∈ Tᵗ ∩ Ω₁`, `Ω₁·M' + η' < Ω₁·M + η` and `ucDat M', η'` below
`ϑᵗ(Ω₁·M + η)`: `ϑᵗ(Ω₁·M' + η') < ϑᵗ(Ω₁·M + η)`.

Our steps.  `α := Ω₁·M' + η'`, `γ := Ω₁·M + η ∈ Tᵗ ∩ Ω₂` (◇Δ″), `α^* ≤ max(ucDat M', η') < ϑ₀(γ)` (◇Δ″); the first
disjunct of L (`m = 0`). -/
axiom ucVt_lt {τ M' η' M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Om1 ≤ M) (hMB : M < Uc.ucB)
    (hM' : M' ≤ M) (hM'T : Uc.ucDat M' ∈ Tset τ) (hη' : η' ∈ Tset τ) (hη'Ω : η' < Om1)
    (hMT : Uc.ucDat M ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (harg : Om1 * M' + η' < Om1 * M + η) (hd' : Uc.ucDat M' < vt τ (Om1 * M + η))
    (hη'v : η' < vt τ (Om1 * M + η)) : vt τ (Om1 * M' + η') < vt τ (Om1 * M + η)

/-- **[W07a] Lemma 3.30, the direction `⇒`, with Def 3.28** (texts L, S, and the steps ◇): for a level
`Ω₁ ≤ M < B₂` with `ucDat M ∈ Tᵗ`, `ξ ∈ Tᵗ ∩ Ω₂`, `η ∈ Tᵗ ∩ Ω₁`, `ucDat M, η < ϑᵗ(ξ)`: `ϑᵗ(ξ) < ϑᵗ(Ω₁·M + η)`
implies `ξ < Ω₁·M + η`.

Our steps.  `γ := Ω₁·M + η ∈ Tᵗ ∩ Ω₂`, `γ^* ≤ max(ucDat M, η) < ϑ₀(ξ)` (◇Δ″); L (`m = 0`, `α = ξ`): the second
disjunct `ϑ₀(ξ) ≤ γ^*` is impossible, so `ξ < γ`. -/
axiom ucLt_of_vt_lt {τ ξ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Om1 ≤ M) (hMB : M < Uc.ucB)
    (hξ : ξ ∈ Tset τ) (hξ2 : ξ < OmTwo) (hMT : Uc.ucDat M ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (hdξ : Uc.ucDat M < vt τ ξ) (hηξ : η < vt τ ξ) (h : vt τ ξ < vt τ (Om1 * M + η)) : ξ < Om1 * M + η

/-- **[W07a] Lemma 3.30 (`α^* < ϑ₀(α)`), Lemma 4.3, Def 3.28, Convention 4.1** (texts L, E, S, C, and the steps ◇):
for a level `Ω₁ ≤ M < B₂` with `ucDat M ∈ Tᵗ` and `η ∈ Tᵗ ∩ Ω₁`: `ucDat M, η < ϑᵗ(Ω₁·M + η)`.

Our steps.  `γ := Ω₁·M + η ∈ Tᵗ ∩ Ω₂` (◇Δ″), `Δ = Ω₁·M > 0` (C); L: `γ^* < ϑ₀(γ) =: q`, E: `τ < q ∈ E`; ◇Δ″ (last
clause): `ucDat M < q`; the additive components of `η` are `< τ` or `≤ γ^*`, and `q` is additively principal:
`η < q`. -/
axiom ucLevel_lt {τ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Om1 ≤ M) (hMB : M < Uc.ucB)
    (hMT : Uc.ucDat M ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    Uc.ucDat M < vt τ (Om1 * M + η) ∧ η < vt τ (Om1 * M + η)

/-- **[W07a] Def 5.1 (first three clauses), Lemma 5.3 (b)–(d), Def 3.28, Def 3.22, Def 3.1, Lemma 3.3, Lemma 3.5,
Lemma 4.2, Lemma 3.30** (texts P, Π, S, S′, T, T′, D, B, W, L, and the steps ◇): for bases `σ < τ` and an atom `z`
(strongly critical, `Ω₁ < z < B₂`): `z ∈ Tᵗ[σ]` iff every part of `z` is (`Uc.ucParts z`: `λ, y` for `z = F_λ(y) <
X`, the components of `λ` and `y` for `z = H_λ(y) ≥ X`), and then `π_{σ,τ}(z)` is `z` rebuilt from the images of its
parts (`F_{πλ}(πy)`, resp. `H_{ucMap π λ}(πy)`).

Our steps.  Below `X`: π0′ of `R2.CitedTl` (◇Φ, Φ6, ◇F′).  From `X` on: π0″ of ◇π″ (◇Φ₂, ◇C, Ψ6, ◇F″; the
parameters through S, the value through P with `k = 1, 2`, Π (b), (c), and ◇Φ₂ over `σ`). -/
axiom ucAtom_TB {σ τ z : Ordinal.{0}} (h : Bases σ τ) (hSC : Googology.Notation.InaccPsi.SC z) (h1 : Om1 < z)
    (hB : z < Uc.ucB) :
    (z ∈ TB τ σ ↔ ∀ x ∈ Uc.ucParts z, x ∈ TB τ σ) ∧
      ((∀ x ∈ Uc.ucParts z, x ∈ TB τ σ) → pi σ τ z = Uc.ucRebuild (pi σ τ) z)

/-- **[W07a] Def 5.1 (all four clauses), Lemma 5.3 (b)–(d), Def 3.28, Def 3.22, Def 3.1, Lemma 3.3, Lemma 3.5,
Lemma 4.2, Lemma 4.3, Lemma 3.30** (texts P, Π, S, T, D, B, W, E, L, and the steps ◇): for bases `σ < τ` and an
`ε`-number `φ(a, c) ∈ (Ω₁, B₂)` in normal form (`1 ≤ a`, `a, c < φ(a, c)`): `φ(a, c) ∈ Tᵗ[σ] ⇔ a, c ∈ Tᵗ[σ]`, and then
`π_{σ,τ}(φ(a, c)) = φ(π_{σ,τ}(a), π_{σ,τ}(c))`.

Our steps.  Step π3 of ◇π′ for the codes below `B₂` (the term `ϑ₁(Ω₂·a + c*)` of ◇K′, ◇P*, ◇I″; the parameters
through S; the value through P, third clause with `k = 1, 2`, the fixed-point shift kept by `π` through ◇F″; π0″ for
the atoms). -/
axiom ucPhi_TB {σ τ a c : Ordinal.{0}} (h : Bases σ τ) (ha : 1 ≤ a) (haz : a < veblen a c)
    (hcz : c < veblen a c) (h1 : Om1 < veblen a c) (hB : veblen a c < Uc.ucB) :
    (veblen a c ∈ TB τ σ ↔ a ∈ TB τ σ ∧ c ∈ TB τ σ) ∧
      (a ∈ TB τ σ → c ∈ TB τ σ → pi σ τ (veblen a c) = veblen (pi σ τ a) (pi σ τ c))

/-- **[W07a] Def 5.1 (first three clauses), Lemma 5.3 (b)–(d), Def 3.28, Def 3.22, Lemma 3.5, Lemma 4.2, Lemma 3.30**
(texts P, Π, S, T, W, L, and the steps ◇): for bases `σ < τ` and `g ≥ E₁`, not an `ε`-number, with `ω^g < B₂`:
`ω^g ∈ Tᵗ[σ] ⇔ g ∈ Tᵗ[σ]`, and then `π_{σ,τ}(ω^g) = ω^{π_{σ,τ}(g)}`.

Our steps.  Step π2 of ◇π′ for the codes below `B₂`: `ω^g = ϑ₁(g⁻)` (◇N), `Parᵗ(ω^g) = Parᵗ(g⁻)` (S, `k = 1`),
`π(ω^g) = ϑ₁(π(g⁻))` (P, third clause), `π(g⁻) = (π g)⁻` (◇F″, π0″, π3), and `ϑ₁((π g)⁻) = ω^{π g}` (◇N). -/
axiom ucOpow_TB {σ τ g : Ordinal.{0}} (h : Bases σ τ) (hg : Gg.ggE ≤ g) (hgE : ω ^ g ≠ g)
    (hB : ω ^ g < Uc.ucB) :
    (ω ^ g ∈ TB τ σ ↔ g ∈ TB τ σ) ∧ (g ∈ TB τ σ → pi σ τ (ω ^ g) = ω ^ pi σ τ g)

end Googology.Trans.PoR.InaccPsi.R2
