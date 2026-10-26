import Googology.Trans.PoR.InaccPsi.R2.VdBase

set_option autoImplicit false

/-!
# The generic citation of Wilken 2007 ONCE for every level `Ω₁ ≤ M < θ` (`θ = ψ_{Ω₂}(Ω_ω)`), widening `R2.CitedUc`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

The eight axioms below replace the eight axioms of `R2.CitedUc` (levels `M < B₂`, `B₂ = ψ_{Ω₂}(ε_{Ω₂+1})`), which are
now their instances below `B₂`, with the same names and statements.  Each axiom has two branches: below `B₂` it is the
former statement (readings `Uc.ucDat`, `Uc.ucParts`, `Uc.ucRebuild`, steps of Part I below); on `[B₂, θ)` it reads the
data through the visibility closure `K⁽⁰⁾` and the atoms through the lifted hierarchy `Hˡ` (Part II).  The second
branch is stated for one `S` in a hypothesis (`∃ S`) and for every `S` in a conclusion (`∀ S`); ◇S below shows that
the readings do not depend on `S`.

Conventions of Part I as in `R2.CitedTl` (`Ω₁ = Om1`, `Ω₂ = OmTwo`, `Tset τ = Tᵗ`, `Par τ = Parᵗ`, `vt τ = ϑᵗ = ϑ₀`,
`pi σ τ = π_{σ,τ}`, `TB τ σ = Tᵗ[σ]`, every base `τ` a countable `ε`-number, `φ(a, c) = veblen a c`, `E₁ = ε_{Ω₁+1}`,
`F_β = Rh.rhF β`, `X = Tl.tlX`).  Objects of Part I (`R2.UcCmp` … `R2.UcAt`, all Lean-defined, no axiom):
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
Objects of Part II (`R2.VdBase`, all Lean-defined, no axiom; `R2.VdEq` identifies them with `R2.UlK`, `R2.UlUB`):
* `K⁽ⁱ⁾_q = Vd.VdK S i q = Ul.UlK S i q` (the closure of `q ∪ {0, I_n, I_ω}` under `+`, `φ`, `Ω_·` and every `ψ_π`, `π
  ≠ Ω_{i+1}`); **the `K⁽⁰⁾`-datum** `d_S(x) := Vd.vdD S 0 x` (the least `m` with `x ∈ K⁽⁰⁾_{m+1}`; `d_S(x) < q ↔ x ∈
  K⁽⁰⁾_q` for strongly critical `q`, `Ul.ul_vis`); it is defined for every ordinal, and on the ordinals of the notation
  `d_S(x) < q ↔ uiDat x < q` (`Vd.vd_dat_ui`), below `B₂` `d_S(x) < q ↔ ucDat x < q` (`Vd.vd_dat_uc`), both for every
  strongly critical `q ≤ Ω₁`.  Below `θ` it is countable (`Vd.vdD_lt_Om1`).
* **`Hˡ_γ = Vd.vdH S γ = Ul.ulH S 1 γ`** (the lifted hierarchy at `Ω₂`, every level `γ`); `Fix_γ`, `idx_γ` and `W₁(γ,
  c) = Hˡ_γ(idx_γ(c))` as in `R2.CitedUz` (◇X).  **The normal form** of a strongly critical `z ∈ (Ω₁, θ)`: `z =
  Hˡ_λ(y)`, `λ = Vd.vdLev S z < Ω₃` the least level below `Ω₃` visible at `z` (`d¹(λ) < z`, i.e. `λ ∈ K⁽¹⁾_z`) with
  `Hˡ_λ(z) ≠ z`, `y = Vd.vdI S λ z < z` (`Vd.vd_nf_ex`, `Vd.vd_nf`); below `B₂` it is the normal form of `R2.UcDat`
  (`Vd.vdLev_eq_uc`).
* `Vd.VdDatIn P M`, `Vd.VdDatAll P M` (some / every reading of the data of `M` satisfies `P`), `Vd.VdLtIn M v`,
  `Vd.VdLtAll M v` (some / every reading lies below `v`; on `[B₂, θ)` through a strongly critical `q ≤ v`, resp. every
  strongly critical `q ≥ v`, since `d_S` is read only at strongly critical points), `Vd.VdRng x` (`x < B₂`, or `x < θ`).

Literal texts.  (D) Def 3.1, (B) Lemma 3.3, (L) Lemma 3.30, (P) Def 5.1, (Π) Lemma 5.3 (b)–(d) as quoted in
`R2.CitedTl` (word for word); (T) Def 3.22, (EX) Corollary 3.21, (U), (S) Def 3.28, (C) Convention 4.1, (E) Lemma 4.3
as quoted in `R2.CitedSy`; (M) Lemma 3.2 (b), (I) Lemma 3.7 with Def 3.6, (R) Lemma 3.8 and Corollary 3.9, (Θⁿ) Def 3.13
and Theorem 3.14, (U′) the Remark after Corollary 3.15 as quoted in `R2.CitedUz`; and
* (W) Def 3.4: "Let `α ↦ ω̄_α` be the enumeration function of the additive principle numbers which are not epsilon
  numbers."  Lemma 4.2: "For any `m < ω` and any `α < Ω_{m+1}` we have `ϑ_m(1 + α) = ω̄_{Ω_m+α}`."
* (T′) Def 3.22: "`T_m` is defined inductively as follows: • `Ω_m ⊆ T_m` • `ξ, η ∈ T_m ⇒ ξ + η ∈ T_m` • `ξ ∈ T_m ∩
  Ω_{k+2} ⇒ ϑ_k(ξ) ∈ T_m` for `k ≥ m`."
* (S′) Def 3.28: "`Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ) ∪ Subᵗ_m(η)` for `ξ, η ∈ Tᵗ` s.t. `α =NF ξ + η > τ`;
  `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ)` if `k ≥ m`, `{α}` if `k < m`, for `α = ϑ_k(ξ)` where `ξ ∈ Tᵗ ∩ Ω_{k+2}`. …
  `Parᵗ(α) := Subᵗ_0(α) ∩ τ`."
* (Θ) Theorem 3.23: "For `m < ω` we have `T_m = ⋃_{n>m} Tⁿ_m` and `T_m ∩ Ω_{m+1} = θ_m = sup_{n≥m} ϑ_m(⋯(ϑ_n(0))⋯)`."
* (Q) Def 3.10: "Let `m < n`.  By recursion on the definition of `Tⁿ_{m+1}` we define `Pⁿ_m(ξ) ⊆_fin Ω_{m+1}` for every
  `ξ ∈ Tⁿ_{m+1}`.  • `Pⁿ_m(ξ) := {ξ₁, …, ξ_r}`, provided `ξ =ANF ξ₁ + ⋯ + ξ_r < Ω_{m+1}` • `Pⁿ_m(ξ) := Pⁿ_m(ξ₁) ∪
  Pⁿ_m(ξ₂)`, if `ξ₁, ξ₂ ∈ Tⁿ_{m+1}` and `ξ =NF ξ₁ + ξ₂ > Ω_{m+1}` • `Pⁿ_m(ξ) := Pⁿ_m(η)`, provided `ξ = ϑⁿ_k(η)`, `η ∈
  Tⁿ_{m+1} ∩ Ω_{k+2}`, `m < k < n`.  We define `ξ^{*ⁿ_m} := max((Pⁿ_m(ξ) − Ω_m) ∪ {0})` for `ξ ∈ Tⁿ_{m+1}`."
  Lemma 3.11: "For `n > 0` and `m ∈ {0, …, n − 1}` we have (a) `Pⁿ_m` is well defined.  (b) Let `α < Ω_{m+2}` and `β <
  Ω_{m+1}`.  For every `ξ ∈ Tⁿ_{m+1}` we have `ξ ∈ Cⁿ_m(α, β) ⇔ Pⁿ_m(ξ) ⊆ Cⁿ_m(α, β)`."

Part I.  Our steps for the codes below `B₂`.
They are the steps of `R2.CitedTl` (◇O′, ◇Φ, ◇K′, ◇I′, ◇V′, ◇Δ′, ◇F′, ◇π′ and through them those of
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

Part II.  Our steps for `[B₂, θ)`, in full.  Fix `S`; `θ = ConjT.th S`; `ϑ_j := ϑⁿ_j`, `T_m := Tⁿ_m`, `P_m := Pⁿ_m`
for `n` large (EX, Θ); the steps ◇X, ◇K, ◇CL, ◇D (`D(k)`, `VIS(k)` for every `k ≥ 1`), ◇B, ◇F of `R2.CitedUz` are used
as written there; "Lean" marks a theorem of the repository or of `R2.VdNF`, `R2.VdDat`.
* (◇θ) **`θ = T₁ ∩ Ω₂`, so every ordinal below `θ` is in some `Tⁿ₁`.**  `≤`: ◇B, ◇F of `R2.CitedUz` (`T₁ ∩ Ω₂ =
  θ₁ = sup_n θⁿ₁`, `θⁿ₁ ⊆ θ`).  `≥`: `θ = sup_n ψ_{Ω₂}(E_n)`, `E_n = ε_{Ω_n+1}` (`Us.us_top_sup`), and `ψ_{Ω₂}(E_n) ∈
  T₁`: `E_n = V_n(1, 0) = ϑ_n(Ω_{n+1})` (D(n) (V)); `ψ_{Ω_n}(E_n) = Hˡ⁽ⁿ⁻¹⁾_{E_n}(0)` (`Us.us_top_E`) `=
  W_{n−1}(E_n, 0) = ϑ_{n−1}(Ω_n·(Ω_n + E_n))` (D(n−1) (H); `0` is not fixed); `ψ_{Ω_{k+1}}(E_n) =
  Hˡ⁽ᵏ⁾_{ψ_{Ω_{k+2}}(E_n)}(0)` (`Us.us_step_E`) `= ϑ_k(Ω_{k+1}·(Ω_{k+1} + ψ_{Ω_{k+2}}(E_n)))` for `k = n − 2, …, 1`
  (D(k) (H)).  Every argument is built by `+` and `ϑ_j` from `ϑ_j(0) = Ω_j` (T′), so `ψ_{Ω₂}(E_n) ∈ T₁ ∩ Ω₂`, an
  ordinal (Θ).  So `θ = θ₁` does not depend on `S`, and `[Ω₁, θ) ⊆ T₁ ∩ Ω₂ = ⋃_n θⁿ₁ = ⋃_n Tⁿ₁ ∩ Ω₂` (Θⁿ).
* (◇V0) **`VIS(0)`: for `x ∈ Tⁿ₁` and strongly critical `v ≤ Ω₁`: `P₀(x) ⊆ v ⇔ x ∈ K⁽⁰⁾_v`.**  By induction on the
  unique term of `x` (U′, Q), exactly as `VIS(k)` of `R2.CitedUz` with `k = 0`: (Q1) `x < Ω₁`: `P₀(x)` = the additive
  components, `x ∈ K⁽⁰⁾_v ⇔ x < v` (`Ul.ulK_lt_W` at `s = 0`, `Ω₀ = 0 < v`); (Q2) sums: the components of a member are
  members (`Uo.uoK_lead_tail`, `Ul.ulK_dec`); (Q3) `x = ϑ_j(η)`, `0 < j < n`, `P₀(x) = P₀(η)`: by `D(j)` (C), (V), (H)
  and the ψ-facts at `i = 0 < j` (`Uz.uz_idx_veb`, `Uo.uoK_veb`, `Uz.uz_idx_H`, `Uz.uz_parts`, and (L1) `Uz.uz_L1` with
  `i = 0`, `s = j`): `x ∈ K⁽⁰⁾_v ⇔ η ∈ K⁽⁰⁾_v`; then the i.h. at `η`.
* (◇m) **`m := Tᵗ ∩ Ω₁` is a strongly critical ordinal `> τ`.**  It is an ordinal (Θ at `m = 0`), contains `τ = ϑᵗ(0)`
  and is closed under `+` (T′).  For `1 ≤ a`, `y ∈ m`: `Ω₁·a + y ∈ Tᵗ ∩ Ω₂` (`Ω₁·ω^{a_i} = ω^{Ω₁ + a_i} = ϑ₁(x_i)` by
  D(1) (C), T′), and `φ(a, y) ≤ u := ϑᵗ(Ω₁·a + y)`, by induction on `(a, y)`: `u = Cᵗ(Ω₁·a + y, u) ∩ Ω₁` (B (a)), so
  for `a' < a`, `z < u`: `Ω₁·a' + z ∈ C ∩ (Ω₁·a + y)` (D, `a', z ∈ C`), `φ(a', z) ≤ ϑᵗ(Ω₁·a' + z) ∈ C ∩ Ω₁ = u` (i.h.,
  D); so `u` is a fixed point of every `φ(a', ·)`, `a' < a` (normality), i.e. `u = φ(a, w)`; and `φ(a, y') ≤ ϑᵗ(Ω₁·a +
  y') < u` for `y' < y` (i.h., L), so `w ≥ y`.  For `a = 0`: `ω^y ≤ ω̄_{τ+y} = ϑᵗ(1 + y)` (W).  So `φ(a, y) ∈ m` for
  `a, y ∈ m`: `m` is strongly critical.
* (◇R) **The reading of membership.**  For `M ∈ [B₂, θ)` and `η ∈ Tᵗ ∩ Ω₁`: `M ∈ Tⁿ₁` (◇θ), `γ := Ω₁·M + η ∈ Tⁿ₁`,
  and `P₀(γ) ∪ ω = P₀(M) ∪ comps(η) ∪ ω` (Q; `Ω₁·ω^g = ω^{Ω₁+g}` is `ω^g` or a `ϑ₁`-term with the parts of `g`, D(1)
  (C)).  By 3.11 (b) (`m = 0`, `β = 0`, `α < Ω₂` large; `Tⁿ₀ = Cⁿ₀(Ω₂, 0)`, Θ, EX): `γ ∈ Tᵗ ⇔ P₀(γ) ⊆ Tᵗ ∩ Ω₁ = m`
  ⇔ `γ ∈ K⁽⁰⁾_m` (◇V0, ◇m) ⇔ `M ∈ K⁽⁰⁾_m ∧ η < m` (`Uz.uz_parts` at `k = 0`, `Ul.ulK_lt_W`) ⇔ `d_S(M) ∈ Tᵗ ∧ η ∈ Tᵗ`
  (`Ul.ul_vis`, Θ).  The same with `M` alone: `P₀(M) ⊆ v ⇔ d_S(M) < v` for every strongly critical `v ≤ Ω₁`.
* (◇S) **The readings do not depend on `S`.**  For `M ∈ [B₂, θ)` and strongly critical `q ≤ Ω₁`: `d_S(M) < q ⇔ P₀(M) ⊆
  q` (◇R, for every `S`), and the right side mentions no `S`; `θ = θ₁` (◇θ).  So `∃ S` in a hypothesis and `∀ S` in a
  conclusion say the same.  Likewise the normal form: `z = Hˡ_λ(y) = W₁(λ, c)` (D(1) (H), `c` the index of `y` in `Ord ∖
  Fix_λ`, ◇X) and `z = ϑ₁(Ω₂·(Ω₂ + λ) + c)` with a unique argument (L, `m = 1`), so `λ`, `y` are `S`-free.
* (◇Δ‴) **Lemma 3.30 at a level `M ∈ [B₂, θ)`.**  `γ := Ω₁·M + η ∈ Tᵗ ∩ Ω₂` (◇R), `γ^{*0} ≤ max P₀(γ)` (Q), and every
  element of `P₀(γ)` is `≤ γ^{*0}`, finite, or `< τ ≤ ϑᵗ(γ)` (Q: `P₀(γ) − Ω₀ = P₀(γ) − τ`).  (a) `vdArg_mem`,
  `vdArg_dat`: ◇R.  (b) `vdVt_lt`: from `d_S(M') < q ≤ v := ϑᵗ(γ)`, `q` strongly critical: `P₀(M') ⊆ q ⊆ v` (◇R), so
  `α^{*0} ≤ max(P₀(M') ∪ comps(η')) < v` for `α := Ω₁·M' + η'` (with `M' < B₂`, Part I ◇Δ″); the first disjunct of L.
  (c) `vdLt_of_vt_lt`: `d_S(M) < q ≤ ϑᵗ(ξ)` gives `γ^{*0} < ϑᵗ(ξ)`, the second disjunct of L is impossible, so `ξ < γ`.
  (d) `vdLevel_lt`: L gives `γ^{*0} < ϑᵗ(γ) =: v`, and `τ < v ∈ E` (E, C: `Δ = Ω₁·M > 0`); so `P₀(M) ⊆ v` (the elements
  below `τ` are below `v`), hence `P₀(M) ⊆ q` and `d_S(M) < q` for every strongly critical `q ≥ v` (◇R); `η < v` as in
  ◇Δ″.  (The `K⁽⁰⁾`-datum is read only at strongly critical points: `d_S(Ω₁ + φ(2, 0)) = 0`, while the countable part
  `φ(2, 0)` may exceed `ϑᵗ(γ)`; hence the forms of `Vd.VdLtIn`, `Vd.VdLtAll`.)
* (◇F‴) **Fixed points.**  For `λ ∈ Tᵗ ∩ Ω₃` and `y ∈ Tᵗ ∩ Ω₂` with `p := max(Fix_λ ∩ (y + 1))` existing (`Fix_λ` is
  closed): `p ∈ Tᵗ` and `Parᵗ(p) ⊆ Parᵗ(y) ∪ ω`.  As ◇F″ of Part I, by induction on `y`, with visibility in place of
  components: `p` is strongly critical, so `p ≤ lead(y)`, an additive component of `y` (S).  If `lead(y) ∈ Fix_λ`, `p =
  lead(y)`.  If `lead(y)` is not strongly critical, as in ◇F′.  If `lead(y) = Hˡ_{λ₂}(y₂)` is an atom in normal form not
  in `Fix_λ`: if `λ₂ ∉ K⁽¹⁾_p`, `VIS(1)` (◇D of `R2.CitedUz`) gives `x ∈ P₁(λ₂)` with `p ≤ x`, and `x < lead(y)`
  (`λ₂ ∈ K⁽¹⁾_{lead(y)}`, `Ul.ulH_D_lt`), `x` a part of `y` (S along the term `ϑ₁(Ω₂·(Ω₂ + λ₂) + c₂)`), so `p =
  max(Fix_λ ∩ (x + 1))` and the i.h. at `x`; otherwise `λ₂ ∈ K⁽¹⁾_p`, and `λ₂ > λ` would put `lead(y)` in `Fix_λ`
  (`Uc.ucG_fix_lower`: `λ ∈ K⁽¹⁾_p ⊆ K⁽¹⁾_{lead(y)}`), so `λ₂ ≤ λ`, `p ∈ Fix_{λ₂}`, `p < Hˡ_{λ₂}(y₂)` gives `p ≤ y₂`,
  a part of `y` (◇X: `y₂` and `c₂` have the same parameters up to finite ones): i.h.
* (◇Ω₂) **The factor `Ω₂`.**  For `x ∈ Tᵗ ∩ Ω₃`: `Ω₂·x ∈ Tᵗ ⇔ x ∈ Tᵗ`, `Parᵗ(Ω₂·x) ∪ ω = Parᵗ(x) ∪ ω`, and for `x ∈
  Tᵗ[σ]`: `π(Ω₂·x) = Ω₂·π(x)`.  `Ω₂·x = Σ ω^{Ω₂ + x_i}·k_i` over the Cantor terms `ω^{x_i}·k_i` of `x`; `ω^{Ω₂ + x_i}
  = ϑ₂(1 + α_i)` with `idx_ε(Ω₂ + α_i) = Ω₂ + x_i` (D(2) (C), ◇X), and `Ω₂ = ϑ₂(0)`; S and P (third clause, `k = 2`),
  Π (c), and `π(idx_ε(w)) = idx_ε(π w)` (`π` keeps `+`, `<` and maps the `ε`-numbers of `Tᵗ[σ]`, the `ϑ_j`-values of
  the forms (V), (H) and `Ω_j`, to `ε`-numbers, and is onto `T^σ`, Π (d)).
* (◇π‴) **Atoms** (`Bases σ τ`): a strongly critical `z ∈ [B₂, θ)` with normal form `Hˡ_λ(y)`.  By ◇θ, D(1) (H) and L:
  `z = ϑ₁(ζ)`, `ζ = Ω₂·(Ω₂ + λ) + c`, `c` the index of `y` (◇X: `y = p + 1 + (c − p)` with `p = max(Fix_λ ∩ (y + 1))`,
  or `y = c`).  `z ∈ Tᵗ ⇔ ζ ∈ Tᵗ` (T′, U) with `Parᵗ(z) = Parᵗ(ζ)` (S); `ζ ∈ Tᵗ[σ] ⇔ λ, c ∈ Tᵗ[σ]` (◇Ω₂, Π (c)), and `c
  ∈ Tᵗ[σ] ⇔ y ∈ Tᵗ[σ]` (◇F‴).  So `z ∈ Tᵗ[σ] ⇔ λ, y ∈ Tᵗ[σ]`.  Then `π(z) = ϑ₁(π ζ)` (P, `k = 1`) `= ϑ₁(Ω₂·(Ω₂ + π λ) +
  π c)` (◇Ω₂, Π (c)) `= W₁(π λ, π c)` (D(1) (H) over `σ`; `ϑ₁` does not depend on the base, D) `= Hˡ_{π λ}(π y)`: `π p ∈
  Fix_{π λ}` (`p` is a value `W₁(λ'', c'')` with `λ < λ''`, `λ ∈ K⁽¹⁾_p`; `π` keeps `<` and `VIS(1)` over `σ`), no fixed
  point of `Hˡ_{π λ}` lies in `(π p, π y]` (it would be `π q'`, Π (d), with `q' ∈ Fix_λ ∩ (p, y]` by the same argument
  backwards), and `π(p + 1 + d) = π p + 1 + π d` (Π (c)): `idx_{πλ}(π c) = π y`.
* (◇π3‴) `φ(a, c)`, `ω^g` below `θ`: π3, π2 of ◇π′ verbatim, by induction on the ordinal, with the atoms of `[B₂, θ)`
  read by ◇π‴ and the codes below `B₂` by Part I.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2.Vd

/-- **[W07a] Def 3.22, Theorem 3.23, Def 3.10, Lemma 3.11 (b), Def 3.1, Lemma 3.3, Lemma 3.5, Lemma 4.2, Def 3.28,
Lemma 3.30 (`m = 0, 1, 2`)** (texts T, T′, Θ, Q, D, B, W, S, L, and the steps): for a level `Ω₁ ≤ M < θ` with a
reading of its data in `Tᵗ` (`ucDat M` below `B₂`; `d_S(M)` for some `S` with `B₂ ≤ M < θ`) and `η ∈ Tᵗ ∩ Ω₁`:
`Ω₁·M + η ∈ Tᵗ`.

Our steps.  Below `B₂`: ◇Δ″ (Part I).  On `[B₂, θ)`: ◇R (with ◇θ, ◇V0, ◇m). -/
axiom vdArg_mem {τ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Om1 ≤ M)
    (hMT : VdDatIn (· ∈ Tset τ) M) (hη : η ∈ Tset τ) (hηΩ : η < Om1) : Om1 * M + η ∈ Tset τ

/-- **[W07a] Def 3.22, Theorem 3.23, Def 3.10, Lemma 3.11 (b), the Remark after Corollary 3.24, Def 3.28, Lemma 3.30**
(texts T, Θ, Q, U, S, L, and the steps): for a level `Ω₁ ≤ M` and `η < Ω₁` with `Ω₁·M + η ∈ Tᵗ`: every reading of the
data of `M` is in `Tᵗ` (`ucDat M` if `M < B₂`; `d_S(M)` for every `S` with `B₂ ≤ M < θ`).

Our steps.  Below `B₂`: ◇V″ (V1), ◇Δ″ (Part I).  On `[B₂, θ)`: ◇R, for every `S` (◇S). -/
axiom vdArg_dat {τ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Om1 ≤ M) (hηΩ : η < Om1)
    (h : Om1 * M + η ∈ Tset τ) : VdDatAll (· ∈ Tset τ) M

/-- **[W07a] Lemma 3.30, the direction `⇐`, with Def 3.10 and Def 3.28** (texts L, Q, S, and the steps): for a level
`Ω₁ ≤ M < θ` and `M' ≤ M` whose data are read in `Tᵗ`, `η', η ∈ Tᵗ ∩ Ω₁`, `Ω₁·M' + η' < Ω₁·M + η`, a reading of the
data of `M'` below `ϑᵗ(Ω₁·M + η)` (on `[B₂, θ)` through a strongly critical `q ≤ ϑᵗ(Ω₁·M + η)`) and `η'` below it:
`ϑᵗ(Ω₁·M' + η') < ϑᵗ(Ω₁·M + η)`.

Our steps.  Below `B₂`: ◇Δ″.  On `[B₂, θ)`: ◇Δ‴ (b). -/
axiom vdVt_lt {τ M' η' M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Om1 ≤ M)
    (hM' : M' ≤ M) (hM'T : VdDatIn (· ∈ Tset τ) M') (hη' : η' ∈ Tset τ) (hη'Ω : η' < Om1)
    (hMT : VdDatIn (· ∈ Tset τ) M) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (harg : Om1 * M' + η' < Om1 * M + η) (hd' : VdLtIn M' (vt τ (Om1 * M + η)))
    (hη'v : η' < vt τ (Om1 * M + η)) : vt τ (Om1 * M' + η') < vt τ (Om1 * M + η)

/-- **[W07a] Lemma 3.30, the direction `⇒`, with Def 3.10 and Def 3.28** (texts L, Q, S, and the steps): for a level
`Ω₁ ≤ M < θ` with its data read in `Tᵗ`, `ξ ∈ Tᵗ ∩ Ω₂`, `η ∈ Tᵗ ∩ Ω₁`, a reading of the data of `M` below `ϑᵗ(ξ)`
(on `[B₂, θ)` through a strongly critical `q ≤ ϑᵗ(ξ)`) and `η < ϑᵗ(ξ)`: `ϑᵗ(ξ) < ϑᵗ(Ω₁·M + η)` implies `ξ < Ω₁·M + η`.

Our steps.  Below `B₂`: ◇Δ″.  On `[B₂, θ)`: ◇Δ‴ (c). -/
axiom vdLt_of_vt_lt {τ ξ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Om1 ≤ M)
    (hξ : ξ ∈ Tset τ) (hξ2 : ξ < OmTwo) (hMT : VdDatIn (· ∈ Tset τ) M) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (hdξ : VdLtIn M (vt τ ξ)) (hηξ : η < vt τ ξ) (h : vt τ ξ < vt τ (Om1 * M + η)) : ξ < Om1 * M + η

/-- **[W07a] Lemma 3.30 (`α^* < ϑ₀(α)`), Lemma 4.3, Def 3.10, Def 3.28, Convention 4.1** (texts L, E, Q, S, C, and the
steps): for a level `Ω₁ ≤ M < θ` with its data read in `Tᵗ` and `η ∈ Tᵗ ∩ Ω₁`: every reading of the data of `M` lies
below `ϑᵗ(Ω₁·M + η)` (`ucDat M` below `B₂`; on `[B₂, θ)`, `d_S(M)` below every strongly critical `q ≥ ϑᵗ(Ω₁·M + η)`,
for every `S`), and `η < ϑᵗ(Ω₁·M + η)`.

Our steps.  Below `B₂`: ◇Δ″.  On `[B₂, θ)`: ◇Δ‴ (d), ◇S. -/
axiom vdLevel_lt {τ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Om1 ≤ M)
    (hMT : VdDatIn (· ∈ Tset τ) M) (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    VdLtAll M (vt τ (Om1 * M + η)) ∧ η < vt τ (Om1 * M + η)

/-- **[W07a] Def 5.1 (first three clauses), Lemma 5.3 (b)–(d), Def 3.28, Def 3.22, Def 3.1, Lemma 3.3, Lemma 3.5,
Lemma 4.2, Lemma 3.30** (texts P, Π, S, S′, T, T′, D, B, W, L, and the steps): for bases `σ < τ` and an atom `z`
(strongly critical, `Ω₁ < z`): if `z < B₂`, `z ∈ Tᵗ[σ]` iff every part of `z` is (`Uc.ucParts z`), and then
`π_{σ,τ}(z)` is `z` rebuilt from the images of its parts (`Uc.ucRebuild`); if `B₂ ≤ z < θ` (any `S`), with the normal
form `z = Hˡ_λ(y)`: `z ∈ Tᵗ[σ] ⇔ λ, y ∈ Tᵗ[σ]`, and then `π_{σ,τ}(z) = Hˡ_{π λ}(π y)`.

Our steps.  Below `B₂`: π0′ of `R2.CitedTl` below `X`, π0″ of ◇π″ on `[X, B₂)` (Part I).  On `[B₂, θ)`: ◇π‴ (with
◇θ, ◇Ω₂, ◇F‴, D(1), D(2) of `R2.CitedUz`, ◇S). -/
axiom vdAtom_TB {σ τ z : Ordinal.{0}} (h : Bases σ τ) (hSC : SC z) (h1 : Om1 < z) :
    (z < Uc.ucB → (z ∈ TB τ σ ↔ ∀ x ∈ Uc.ucParts z, x ∈ TB τ σ) ∧
      ((∀ x ∈ Uc.ucParts z, x ∈ TB τ σ) → pi σ τ z = Uc.ucRebuild (pi σ τ) z)) ∧
    ∀ S : InaccSeq.{0}, Uc.ucB ≤ z → z < ConjT.th S →
      (z ∈ TB τ σ ↔ vdLev S z ∈ TB τ σ ∧ vdI S (vdLev S z) z ∈ TB τ σ) ∧
      (vdLev S z ∈ TB τ σ → vdI S (vdLev S z) z ∈ TB τ σ →
        pi σ τ z = vdH S (pi σ τ (vdLev S z)) (pi σ τ (vdI S (vdLev S z) z)))

/-- **[W07a] Def 5.1 (all four clauses), Lemma 5.3 (b)–(d), Def 3.28, Def 3.22, Def 3.1, Lemma 3.3, Lemma 3.5,
Lemma 4.2, Lemma 4.3, Lemma 3.30** (texts P, Π, S, T, D, B, W, E, L, and the steps): for bases `σ < τ` and an
`ε`-number `φ(a, c) ∈ (Ω₁, θ)` in normal form (`1 ≤ a`, `a, c < φ(a, c)`; `φ(a, c) < B₂` or `< θ` for some `S`):
`φ(a, c) ∈ Tᵗ[σ] ⇔ a, c ∈ Tᵗ[σ]`, and then `π_{σ,τ}(φ(a, c)) = φ(π_{σ,τ}(a), π_{σ,τ}(c))`.

Our steps.  Step π3 of ◇π′ below `B₂` (Part I) and ◇π3‴ on `[B₂, θ)`. -/
axiom vdPhi_TB {σ τ a c : Ordinal.{0}} (h : Bases σ τ) (ha : 1 ≤ a) (haz : a < veblen a c)
    (hcz : c < veblen a c) (h1 : Om1 < veblen a c) (hB : VdRng (veblen a c)) :
    (veblen a c ∈ TB τ σ ↔ a ∈ TB τ σ ∧ c ∈ TB τ σ) ∧
      (a ∈ TB τ σ → c ∈ TB τ σ → pi σ τ (veblen a c) = veblen (pi σ τ a) (pi σ τ c))

/-- **[W07a] Def 5.1 (first three clauses), Lemma 5.3 (b)–(d), Def 3.28, Def 3.22, Lemma 3.5, Lemma 4.2, Lemma 3.30**
(texts P, Π, S, T, W, L, and the steps): for bases `σ < τ` and `g ≥ E₁`, not an `ε`-number, with `ω^g < B₂` or `ω^g <
θ` for some `S`: `ω^g ∈ Tᵗ[σ] ⇔ g ∈ Tᵗ[σ]`, and then `π_{σ,τ}(ω^g) = ω^{π_{σ,τ}(g)}`.

Our steps.  Step π2 of ◇π′ below `B₂` (Part I) and ◇π3‴ on `[B₂, θ)`. -/
axiom vdOpow_TB {σ τ g : Ordinal.{0}} (h : Bases σ τ) (hg : Gg.ggE ≤ g) (hgE : ω ^ g ≠ g)
    (hB : VdRng (ω ^ g)) :
    (ω ^ g ∈ TB τ σ ↔ g ∈ TB τ σ) ∧ (g ∈ TB τ σ → pi σ τ (ω ^ g) = ω ^ pi σ τ g)

end Googology.Trans.PoR.InaccPsi.R2
