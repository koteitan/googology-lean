import Googology.Trans.PoR.InaccPsi.R2.TfDat

set_option autoImplicit false

/-!
# The generic citation of Wilken 2007: Lemma 3.30, Def 3.28, Def 5.1 / Lemma 5.3 ONCE for every level `Ω₁ ≤ M < B_Γ`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

Conventions as in `R2.CitedRj`, `R2.CitedSy`, `R2.CitedTc` (`Ω₁ = Om1`, `Ω₂ = OmTwo`, `Tset τ = Tᵗ`, `Par τ = Parᵗ`,
`vt τ = ϑᵗ = ϑ₀`, `pi σ τ = π_{σ,τ}`, `TB τ σ = Tᵗ[σ]`, every base `τ` a countable `ε`-number, `φ(a, c) = veblen a c`,
`E₁ = ε_{Ω₁+1} = Gg.ggE`).  `Γ_ν = gamma ν` enumerates the strongly critical ordinals; `Γ_{Ω₁} = Ω₁`
(`Tf.tf_gamma_Om1`) and `Γ_{Ω₁+1} = Gg.ggGam` (`Tf.tf_ggGam`).  `B_Γ = Tf.tfBG` is the least fixed point of `Γ` above
`Ω₁` (`B_Γ < Ω₂`, `Tf.tfBG_lt_Om2`).  A **code** is an ordinal `z < B_Γ`.  Below `B_Γ` every strongly critical `z > Ω₁`
is an **atom** `Γ_ν` with `Ω₁ < ν < z` (`Tf.tf_idx_lt`), `ν = Ω₁ + 1 + c`, `c := −(Ω₁ + 1) + ν < B_Γ` (the atoms
`ψ_{Ω₂}(c)`; for orientation only, no step uses `ψ`); every other `ε`-number `z ∈ (Ω₁, B_Γ)` is `φ(a, c)` in normal form
(`1 ≤ a < z`, `c < z`, `a = invVeblen₁ z`, `c = invVeblen₂ z`).  The **leaves** of a code are read by `Tf.tfDat`: `z`
for `z < Ω₁`; none for `Ω₁`; for an atom `Γ_ν` the leaves of `c = −(Ω₁ + 1) + ν`; for `φ(a, c)` the leaves of `a` and
`c`; for any other `z ∈ (Ω₁, B_Γ)` the leaves of `log_ω z` and of `z mod ω^{log_ω z}`; `tfDat z` is the largest leaf
(`0` if none).  `tfDat = rjDat` below `E₁` (`Tf.tfDat_eq_rj`), `= Ss.ssDat` below `Γ_{Ω₁+1}` (`Tf.tfDat_eq_ss`), `=
Tc.tcDat` below `Γ'` (`Tf.tfDat_eq_tc`).  The arguments are `ξ = Ω₁·M + η` with `η ∈ Tᵗ ∩ Ω₁`, for **every** level
`Ω₁ ≤ M < B_Γ` (Convention 4.1: `Δ = Ω₁·M`).

This file replaces the range-wise citations of the same facts: `R2.CitedRj` (`rjArg_mem`, `rjVt_lt`, `rjLt_of_vt_lt`,
`rjLevel_lt_vt`: `M < E₁`), `R2.CitedRk` (`rkArg_dat`), `R2.CitedSs` (five facts at `M = E₁`), `R2.CitedSy` (seven, `E₁
< μ < Γ_{Ω₁+1}`) and `R2.CitedTc` (eight, `Γ_{Ω₁+1} ≤ μ < Γ'`): those 25 axioms are theorems derived from the 8 below
(same names and statements, in the same files).  What is **not** restated (checked first, every `Cited*` file of `R2`):
`rjLhT` ([W07b] Def 4.1, stays in `R2.CitedRj`), `R2.CitedLq` (`M = Ω₁·γ + β`, a special case placed earlier in the
imports), `R2.CitedLg`, `R2.CitedLv`, `R2.CitedLu`, `R2.CitedLz`, `R2.CitedLt`, `R2.CitedXt` (levels `M < Ω₁`),
`om1_opow_TB_all`, `pi_Om1`, `pi_add`, `pi_lt`, `pi_vt`, `vzT_add`, `T_inter_Om1`, `Par_comps_eq` (`R2.Cited`,
`R2.CitedW`), `vt_memTwo`, `vt_E_iff`, `vt_rep` (`R2.CitedEv`), `R2.CitedSi`, `R2.CitedEps`, `R2.CitedVz`, `R2.CitedL`,
`R2.CitedR1`, `R2.CitedCore`, `R2.CitedC09`, `R2.CitedBr`.  None of them mentions an atom `Γ_ν`, `ν > Ω₁ + 1`, a code in
`[Γ', B_Γ)` in `Tᵗ`, or `π` there.

Literal texts: (D) Def 3.1, (B) Lemma 3.3, (W) Def 3.4, Lemma 3.5, Lemma 4.2, (EX) Corollary 3.21, (T) Def 3.22,
(Θ) Theorem 3.23 (first part cut), Corollary 3.24, (U) the Remark after Corollary 3.24, (S) Def 3.28, (L) Lemma 3.30,
(C) Convention 4.1, (E) Lemma 4.3, (P) Def 5.1 (four clauses), (Π) Lemma 5.3 (b)–(d): **the quotations of
`R2.CitedSy` and `R2.CitedTc`, word for word** (checked there against the paper).  The two used most:
* (L) Lemma 3.30: "For `m < ω` the function `ϑ_m ↾ Tᵗ ∩ Ω_{m+2}` is 1-1 and has values in `P ∩ [Ω_m, Ω_{m+1})`.  Let
  `α, γ ∈ Tᵗ ∩ Ω_{m+2}`.  Then `α^{*m} < ϑ_m(α)` and `ϑ_m(α) < ϑ_m(γ) ⇔ α < γ ∧ α^{*m} < ϑ_m(γ) ∨ ϑ_m(α) ≤ γ^{*m}`."
* (D) Def 3.1 (end): "`ϑⁿ_m(α) := min({ξ < Ω_{m+1} | Cⁿ_m(α, ξ) ∩ Ω_{m+1} ⊆ ξ ∧ α ∈ Cⁿ_m(α, ξ)} ∪ {Ω_{m+1}})`.  Note
  that we have `ϑⁿ_m(0) = Ω_m` for `m < n`."

Our steps.  They are the steps of `R2.CitedSy` (◇O, ◇P, ◇N, ◇K, ◇M, ◇I, ◇V, ◇Δ, ◇F, ◇π, with h1–h4 of ◇P) and
`R2.CitedTc` (◇G) with the bound `G` replaced by `B_Γ`, the data by `Tf.tfDat`, and the following changes, in full.
* (◇O*) **Veblen facts below `B_Γ`.**  `F_a`, `Y_a := L_a ∖ F_a`, `V(a, c) := φ(a, y_c)` as in ◇O with `L_a := {y |
  φ(a, y) > max(Ω₁, a)}`: `(Ω₁, ∞)` for `a < Ω₁`, `[1, ∞)` for `a = Ω₁` and for an atom `a` (`φ(a, 0) = a`), all `y`
  for the other `a > Ω₁`.  O1, O2 verbatim.  O3 for every `a ≥ 1`: `a < V(a, c)` (`y_c ≥ 1` when `φ(a, 0) ≤ max(Ω₁,
  a)`), `c ≤ y_c`.  O4: `V(a, c) < q` for `a, c < q`, `q` strongly critical `> Ω₁` (`q ∈ F_a`, O1 at `x = q`).  O5
  verbatim.  O6 for every `ε`-number `z ∈ (Ω₁, B_Γ)` that is not an atom, with this `L_a`.
* (◇P*) **`ϑ₁(Ω₂·a + c) = V(a, c)` for all `1 ≤ a < Ω₂`, `c < Ω₂`.**  The proof of ◇P word for word: `ζ = Ω₂·a + c <
  Ω₂²`, so every `ξ ∈ C ∩ ζ` is `< Ω₂²` and the generators of ◇P are the only ones; it uses O3 and O5 (not the bound
  `G`: the bound in ◇P is `v` itself).
* (◇Γ) **The atoms: `ϑ₁(Ω₂² + c) = Γ_{Ω₁+1+c}` for `c < B_Γ`.**  Induction on `c`; `v := Γ_{Ω₁+1+c}` (strongly critical,
  `Ω₁ < v < B_Γ`, and `c < v`: else `c = Ω₁ + 1 + c = Γ_c` would be a fixed point of `Γ` in `(Ω₁, B_Γ)`). Fix `n ≥ 3`
  with `Ω₂²·2 < θⁿ₂` and `C(α, β) := Cⁿ₁(α, β)` as in ◇P.  (h2*) `ϑⁿ₂(x) ≥ ϑⁿ₂(Ω₂ + 1) = ω̄_{Ω₂·2+1} = Ω₂²·ω` for `Ω₂ <
  x < Ω₃` (W, `m = 2`; `ω̄` is increasing), `ϑⁿ₂(x) > Ω₂²` is additive principal, so `≥ Ω₂²·ω`, for `Ω₃ ≤ x < Ω₄` (h2, B
  (b)), `ϑⁿ_k(x) ≥ Ω₃` for `k ≥ 3`.  `≤`: `ζ := Ω₂² + c ∈ C(ζ, v)` (`Ω₂² = ϑⁿ₂(ϑⁿ₂(0))`, h1; `c < v`).  By induction on
  the generation of `C(ζ, v)`: every member `u < Ω₂` is `< v`; every member in `[Ω₂, Ω₂²)` is `Ω₂·a' + c'` with `a', c'
  < v` (h3); every member in `[Ω₂², Ω₂²·2)` is `Ω₂² + Ω₂·a' + c'` with `a', c' < v`; all others are `≥ Ω₂²·2`.
  Generators: `Ω₁ ∪ v`; `ϑⁿ₂(x)` is `Ω₂·ω^x` (`x < v`, `ω^x < v`), `Ω₂²`, or `≥ Ω₂²·ω` (h1, h2*); `ϑⁿ_k(x) ≥ Ω₃` for `k
  ≥ 3`; `ϑⁿ₁(ξ)` with `ξ ∈ C ∩ ζ`: `ξ < Ω₂` gives `ϑⁿ₁(ξ) < v` (h4); `ξ = Ω₂·a' + c'`, `1 ≤ a'`, gives `V(a', c') < v`
  (◇P*, O4 at `q = v`); `Ω₂² ≤ ξ < Ω₂² + c < Ω₂² + Ω₂` gives `ξ = Ω₂² + c'`, `c' < c`, and `ϑⁿ₁(ξ) = Γ_{Ω₁+1+c'} < v`
  (i.h.).  Sums: `v` is additive principal; a sum with two summands `≥ Ω₂²` or one `≥ Ω₂²·ω` is `≥ Ω₂²·2`.  So `C(ζ, v)
  ∩ Ω₂ ⊆ v`, and D gives `ϑⁿ₁(ζ) ≤ v`.  `≥`: suppose `ξ₀ := ϑⁿ₁(ζ) < v`.  By B (a) `ξ₀ = C(ζ, ξ₀) ∩ Ω₂`; `Ω₁ = ϑⁿ₁(0) ∈
  C`, so `Ω₁ < ξ₀`; by B (c) the components of `c` are in `C`, so `c < ξ₀`.  For `1 ≤ a'`, `a', c' < ξ₀`: `Ω₂·a' + c' ∈
  C ∩ ζ`, so `V(a', c') = ϑⁿ₁(Ω₂·a' + c') < ξ₀` (◇P*); with h4 `ξ₀` is closed under every `φ(a', ·)`, `a' < ξ₀` (a value
  `φ(a', y)`, `y < ξ₀`, is `≤ max(Ω₁, a')`, `= y`, or `V(a', c')` with `c' ≤ y`): `ξ₀ = Γ_μ` is strongly critical with
  `μ > Ω₁`.  For `c' < c`: `Ω₂² + c' ∈ C ∩ ζ`, so `Γ_{Ω₁+1+c'} = ϑⁿ₁(Ω₂² + c') < ξ₀` (i.h.), `μ > Ω₁ + 1 + c'`.  So `μ ≥
  Ω₁ + 1 + c` and `ξ₀ ≥ v`, a contradiction.  So `ϑ₁(Ω₂² + c) = Γ_{Ω₁+1+c}` (EX, T), independent of `τ`.  (◇G of
  `R2.CitedTc` is the case `c = 0`.)  `B_Γ` itself is not of this form (`c < B_Γ` gives `Γ_{Ω₁+1+c} < Γ_{B_Γ} = B_Γ`):
  it is the first strongly critical ordinal above `Ω₁` whose argument is not `Ω₂² + c`, where the citation stops.
* (◇K*) **The canonical term of a code `z ∈ [Ω₁, B_Γ)`.**  As ◇K: `arg Ω₁ = 0`, `arg ω^e = e⁻` (◇N), `arg φ(a, c) =
  Ω₂·a + c*` for every `ε`-number `φ(a, c) ∈ (Ω₁, B_Γ)` that is not an atom (◇P*, O6 of ◇O*), and **`arg Γ_ν = Ω₂² +
  c`**, `c = −(Ω₁ + 1) + ν`, `Ω₂² = ϑ₂(ϑ₂(0))` (◇Γ, h1).  The parts `e⁻`, `a_i`, `c*`, `c` are countable or codes `< z`.
  The countable parts of an atom are those of `c`, the leaves of `Γ_ν` are those of `c` (`tfDat`), so ◇K's relation of
  countable parts and leaves holds for every code below `B_Γ`; ◇M verbatim (arguments of `ϑ₁`, `ϑ₂` are `< Ω₂²·2 < Ω₃`).
* (◇I*) As ◇I; a component `y = Γ_ν` of a code in `Tᵗ` is `ϑ₁(ζ)`, `ζ ∈ Tᵗ ∩ Ω₃`, and L (`m = 1`) over `κ` with ◇Γ
  gives `ζ = Ω₂² + c`; L (`m = 2`) and h1 give the `ϑ₂`-term `ϑ₂(ϑ₂(0))` of its component `Ω₂²`.
* (◇V*), (◇Δ*) ◇V, ◇Δ verbatim with `tfDat` for `ssDat` (◇K*, ◇I*, ◇M; `P₀(Γ_ν) = P₀(c)`), for every code `M' < B_Γ`
  (`M' < Ω₁` allowed, `tfDat M' = M'`) and every level `Ω₁ ≤ M < B_Γ` (`Δ = Ω₁·M > 0`; the leaves of `Ω₁·M` are those
  of `M`, up to finite ones).
* (◇F*) ◇F for `0 ≤ b < B_Γ` and codes `y < B_Γ`, with the case `lead(y) = Γ_ν`: if `Γ_ν ∈ F_b`, `p = Γ_ν ∈ Tᵗ` and
  `Parᵗ(p) ⊆ Parᵗ(y)` (a component, S); otherwise `b ≥ Γ_ν`, and every `p ∈ F_b` has `p = φ(b, p) > b ≥ lead(y)`.
* (◇π*) **Base change** (`Bases σ τ`), by induction on the ordinal.  (π0) For an atom `Γ_ν`, `ν = Ω₁ + 1 + c`:
  `Parᵗ(Γ_ν) = Parᵗ(c) ∪ {0}` (S along `ϑ₁(ϑ₂(ϑ₂(0)) + c)`) and `Parᵗ(ν) = Parᵗ(c) ∪ {0, 1}` (`Ω₁ = ϑ₁(0)`); with ◇I*
  and T, `Γ_ν ∈ Tᵗ[σ] ⇔ c ∈ Tᵗ[σ] ⇔ ν ∈ Tᵗ[σ]`.  Then `π(Γ_ν) = ϑ₁(ϑ₂(ϑ₂(π 0)) + π c) = ϑ₁(Ω₂² + π c)` (P, second and
  third clauses, `k = 1, 2`) and `π ν = Ω₁ + 1 + π c` (Π (c), `π(Ω₁) = Ω₁`, `π 1 = 1`); `π c` is a code `< B_Γ` (by the
  induction, `π` keeps the shape of the canonical term and changes only countable parts, and `B_Γ` is closed under `+`,
  `φ` and `x ↦ Γ_x`), so ◇Γ over `σ` gives `π(Γ_ν) = Γ_{Ω₁+1+πc} = Γ_{π ν}`.  π1, π2, π3 of ◇π verbatim for the codes
  below `B_Γ` (π3 for every `ε`-number `φ(a, c) ∈ (Ω₁, B_Γ)` in normal form, π2 for `ω^g < B_Γ`), with π0 for the atoms,
  ◇P* over any base, ◇F* for the largest fixed points and O6 of ◇O* (`π a` is `<`, `=`, `>` `Ω₁` and an atom as `a` is).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- **[W07a] Def 3.22, Theorem 3.23, Def 3.1, Lemma 3.3, Lemma 3.5, Lemma 4.2, Def 3.28, Lemma 3.30 (`m = 0, 1, 2`)**
(texts T, Θ, D, B, W, S, L): for a level `Ω₁ ≤ M < B_Γ` with `tfDat M ∈ Tᵗ` and `η ∈ Tᵗ ∩ Ω₁`: `Ω₁·M + η ∈ Tᵗ`.

Our steps.  ◇Δ* of the module docstring: `Ω₁·M ∈ Tᵗ` by ◇V* (V1) (the canonical term of ◇K*, built by T from the
countable parts, `≤` the leaves, which lie in the initial segment `θᵗ`, and the atoms `ϑ₁(ϑ₂(ϑ₂(0)) + c)`), and
`Ω₁·M + η ∈ Tᵗ` (T, second clause). -/
axiom tfArg_mem {τ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Om1 ≤ M) (hMB : M < Tf.tfBG)
    (hMT : Tf.tfDat M ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1) : Om1 * M + η ∈ Tset τ

/-- **[W07a] Def 3.22, Theorem 3.23, the Remark after Corollary 3.24, Def 3.1, Lemma 3.3, Lemma 3.5, Lemma 4.2,
Def 3.28, Lemma 3.30 (`m = 0, 1, 2`)** (texts T, Θ, U, D, B, W, S, L): for a level `Ω₁ ≤ M < B_Γ` and `η < Ω₁` with
`Ω₁·M + η ∈ Tᵗ`: `tfDat M ∈ Tᵗ`.

Our steps.  By U the term of `Ω₁·M + η` is unique; its components are in `Tᵗ` (S, second clause), and those `≥ Ω₁` sum
to `Ω₁·M` (`η < Ω₁`), which is in `Tᵗ` (T).  ◇V* (V1) at the code `Ω₁·M` (◇I*: the term is the canonical term) and
◇Δ*: `tfDat M ∈ Tᵗ`. -/
axiom tfArg_dat {τ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Om1 ≤ M) (hMB : M < Tf.tfBG)
    (hηΩ : η < Om1) (h : Om1 * M + η ∈ Tset τ) : Tf.tfDat M ∈ Tset τ

/-- **[W07a] Lemma 3.30, the direction `⇐`, with Def 3.28** (texts L, S, and the steps ◇): for a level
`Ω₁ ≤ M < B_Γ` and `M' ≤ M` with `tfDat M', tfDat M ∈ Tᵗ`, `η', η ∈ Tᵗ ∩ Ω₁`, `Ω₁·M' + η' < Ω₁·M + η` and `tfDat M', η'`
below `ϑᵗ(Ω₁·M + η)`: `ϑᵗ(Ω₁·M' + η') < ϑᵗ(Ω₁·M + η)`.

Our steps.  `α := Ω₁·M' + η'` and `γ := Ω₁·M + η` lie in `Tᵗ ∩ Ω₂` (◇Δ*; `M' ≤ M < B_Γ` is a code).  `α^* ≤ max(tfDat
M', η') < ϑ₀(γ)` (◇Δ*, the hypotheses).  So `α < γ ∧ α^* < ϑ₀(γ)`, the first disjunct of the right side of L (`m = 0`),
and `ϑ₀(α) < ϑ₀(γ)`. -/
axiom tfVt_lt {τ M' η' M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Om1 ≤ M) (hMB : M < Tf.tfBG)
    (hM' : M' ≤ M) (hM'T : Tf.tfDat M' ∈ Tset τ) (hη' : η' ∈ Tset τ) (hη'Ω : η' < Om1)
    (hMT : Tf.tfDat M ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (harg : Om1 * M' + η' < Om1 * M + η) (hd' : Tf.tfDat M' < vt τ (Om1 * M + η))
    (hη'v : η' < vt τ (Om1 * M + η)) : vt τ (Om1 * M' + η') < vt τ (Om1 * M + η)

/-- **[W07a] Lemma 3.30, the direction `⇒`, with Def 3.28** (texts L, S, and the steps ◇): for a level
`Ω₁ ≤ M < B_Γ` with `tfDat M ∈ Tᵗ`, `ξ ∈ Tᵗ ∩ Ω₂`, `η ∈ Tᵗ ∩ Ω₁`, `tfDat M, η < ϑᵗ(ξ)`: `ϑᵗ(ξ) < ϑᵗ(Ω₁·M + η)`
implies `ξ < Ω₁·M + η`.

Our steps.  `γ := Ω₁·M + η ∈ Tᵗ ∩ Ω₂` and `γ^* ≤ max(tfDat M, η) < ϑ₀(ξ)` (◇Δ*, the hypotheses).  L (`m = 0`, `α = ξ`):
`ϑ₀(ξ) < ϑ₀(γ)` gives `ξ < γ ∧ ξ^* < ϑ₀(γ)` or `ϑ₀(ξ) ≤ γ^*`; the second is impossible.  So `ξ < γ`. -/
axiom tfLt_of_vt_lt {τ ξ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Om1 ≤ M) (hMB : M < Tf.tfBG)
    (hξ : ξ ∈ Tset τ) (hξ2 : ξ < OmTwo) (hMT : Tf.tfDat M ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (hdξ : Tf.tfDat M < vt τ ξ) (hηξ : η < vt τ ξ) (h : vt τ ξ < vt τ (Om1 * M + η)) : ξ < Om1 * M + η

/-- **[W07a] Lemma 3.30 (`α^* < ϑ₀(α)`), Lemma 4.3, Def 3.28, Convention 4.1** (texts L, E, S, C, and the steps ◇):
for a level `Ω₁ ≤ M < B_Γ` with `tfDat M ∈ Tᵗ` and `η ∈ Tᵗ ∩ Ω₁`: `tfDat M, η < ϑᵗ(Ω₁·M + η)`.

Our steps.  `γ := Ω₁·M + η ∈ Tᵗ ∩ Ω₂` (◇Δ*) with `Δ = Ω₁·M > 0` (C).  L (`m = 0`): `γ^* < ϑ₀(γ) =: q`; E: `τ < q ∈ E`.
◇Δ* (last clause, `ξ' = γ`): `tfDat M < q`.  The additive components of `η` are `< τ` or `≤ η^* ≤ γ^*` (step ★1 of
`R2.CitedLu`; `P₀(η) ⊆ P₀(γ)`), hence `< q`, and `q` is additive principal: `η < q`. -/
axiom tfLevel_lt {τ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Om1 ≤ M) (hMB : M < Tf.tfBG)
    (hMT : Tf.tfDat M ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    Tf.tfDat M < vt τ (Om1 * M + η) ∧ η < vt τ (Om1 * M + η)

/-- **[W07a] Def 5.1 (first three clauses), Lemma 5.3 (b)–(d), Def 3.28, Def 3.22, Def 3.1, Lemma 3.3, Lemma 3.5,
Lemma 4.2, Lemma 3.30** (texts P, Π, S, T, D, B, W, L, and the steps ◇): for bases `σ < τ` and an atom `Γ_ν`, `Ω₁ <
ν`, `Γ_ν < B_Γ`: `Γ_ν ∈ Tᵗ[σ] ⇔ ν ∈ Tᵗ[σ]`, and then `π_{σ,τ}(Γ_ν) = Γ_{π_{σ,τ}(ν)}`.

Our steps.  Step π0 of ◇π*: `Γ_ν = ϑ₁(Ω₂² + c)`, `c = −(Ω₁ + 1) + ν` (◇Γ), the parameters through S, the value through
P (`k = 1, 2`), Π (c) and ◇Γ over `σ`.  (`tcGam_TB` of `R2.CitedTc` is the case `ν = Ω₁ + 1`.) -/
axiom tfGam_TB {σ τ ν : Ordinal.{0}} (h : Bases σ τ) (h1 : Om1 < ν) (hB : gamma ν < Tf.tfBG) :
    (gamma ν ∈ TB τ σ ↔ ν ∈ TB τ σ) ∧ (ν ∈ TB τ σ → pi σ τ (gamma ν) = gamma (pi σ τ ν))

/-- **[W07a] Def 5.1 (all four clauses), Lemma 5.3 (b)–(d), Def 3.28, Def 3.22, Def 3.1, Lemma 3.3, Lemma 3.5,
Lemma 4.2, Lemma 4.3, Lemma 3.30** (texts P, Π, S, T, D, B, W, E, L, and the steps ◇): for bases `σ < τ` and an
`ε`-number `φ(a, c) ∈ (Ω₁, B_Γ)` in normal form (`1 ≤ a`, `a, c < φ(a, c)`): `φ(a, c) ∈ Tᵗ[σ] ⇔ a, c ∈ Tᵗ[σ]`, and then
`π_{σ,τ}(φ(a, c)) = φ(π_{σ,τ}(a), π_{σ,τ}(c))`.

Our steps.  Step π3 of ◇π* (the term `ϑ₁(Ω₂·a + c*)` of ◇K*, ◇P*, ◇I*; the parameters through S; the value through P,
third clause with `k = 1, 2`, and the fixed-point shift of O6 (◇O*) kept by `π` through ◇F*; π0 for the atoms). -/
axiom tfPhi_TB {σ τ a c : Ordinal.{0}} (h : Bases σ τ) (ha : 1 ≤ a) (haz : a < veblen a c)
    (hcz : c < veblen a c) (h1 : Om1 < veblen a c) (hB : veblen a c < Tf.tfBG) :
    (veblen a c ∈ TB τ σ ↔ a ∈ TB τ σ ∧ c ∈ TB τ σ) ∧
      (a ∈ TB τ σ → c ∈ TB τ σ → pi σ τ (veblen a c) = veblen (pi σ τ a) (pi σ τ c))

/-- **[W07a] Def 5.1 (first three clauses), Lemma 5.3 (b)–(d), Def 3.28, Def 3.22, Lemma 3.5, Lemma 4.2, Lemma 3.30**
(texts P, Π, S, T, W, L, and the steps ◇): for bases `σ < τ` and `g ≥ E₁`, not an `ε`-number, with `ω^g < B_Γ`:
`ω^g ∈ Tᵗ[σ] ⇔ g ∈ Tᵗ[σ]`, and then `π_{σ,τ}(ω^g) = ω^{π_{σ,τ}(g)}`.

Our steps.  Step π2 of ◇π*: `ω^g = ϑ₁(g⁻)` (◇N), `Parᵗ(ω^g) = Parᵗ(g⁻)` (S, `k = 1`), `π(ω^g) = ϑ₁(π(g⁻))` (P, third
clause), `π(g⁻) = (π g)⁻` (◇F*, π0, π3), and `ϑ₁((π g)⁻) = ω^{π g}` (◇N). -/
axiom tfOpow_TB {σ τ g : Ordinal.{0}} (h : Bases σ τ) (hg : Gg.ggE ≤ g) (hgE : ω ^ g ≠ g)
    (hB : ω ^ g < Tf.tfBG) :
    (ω ^ g ∈ TB τ σ ↔ g ∈ TB τ σ) ∧ (g ∈ TB τ σ → pi σ τ (ω ^ g) = ω ^ pi σ τ g)

end Googology.Trans.PoR.InaccPsi.R2
