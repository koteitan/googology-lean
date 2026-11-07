import Googology.Trans.PoR.InaccPsi.R2.CitedRj

set_option autoImplicit false

/-!
# Cited: [W07b] Def 4.1 ONCE for every Veblen level `Δ = Ω₁·M`, `ε_{Ω₁+1} ≤ M < Γ_{Ω₁+1}`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.

`R2.CitedRj` (`rjLhT`) computes `lhᵗ(α)` for `α = ϑᵗ(Ω₁·M + η)` with `Ω₁ ≤ M < E₁ = ε_{Ω₁+1}`: there `δ = (λᵗ_α)^*` is
the only element of its `α`-localization above `α`, so `cr = m`.  For the Veblen levels `E₁ ≤ M < Γ_{Ω₁+1}` the
leading exponent `l := log_ω(Ω₁·M)` may contain `ε`-codes, the localization of `δ` may be longer, and `cr < m` occurs.
The one axiom below gives both branches of Def 4.1 there, in closed form:

* `qfL M = log_ω(Ω₁·M)` (the leading exponent), `qfC M = ω^{log_ω(qfL M)}` (its leading additive principal part),
  `QfCr M` (**the condition `cr < m`**: `ω^l` is not an `ε`-number, `c := qfC M` is one, `l = c + x` with
  `x ≤ log_ω(a_c)`, `a_c = invVeblen₁ c` the Veblen level of `c`);
* `qfLhT`: **`lhᵗ(α) = lhᵗ(Θ_α(c)) + (Θ_α(Ω₁·M) + ζ)` if `QfCr M`, and `lhᵗ(α) = lhᵗ(Θ_α(ω^l)) + (Θ_α(Ω₁·M − ω^l) +
  ζ)` otherwise** (`ζ = ζᵗ_α = lqZeta τ (Ω₁·M) η`, `Θ_α = Gg.ggTh α`).  The second branch is the formula of `rjLhT`.

Conventions as in `R2.CitedRj`, `R2.CitedTf` (`Ω₁ = Om1`, `Ω₂ = OmTwo`, `Tset τ = Tᵗ`, `vt τ = ϑᵗ`, `lhT τ = lhᵗ`,
`lg = logend`, every base `τ` a countable `ε`-number, a code is an ordinal below `B_Γ`, its leaves are read by
`Tf.tfDat`, `φ(a, c) = veblen a c`).  What is not restated (checked first): `rjLhT` (`M < E₁`, `R2.CitedRj`),
`lh_eq_lhT` (`R2.CitedL`), `luLhT_fin`, `luLhT_inf`, `luLhT_top`, `lvLhT_gen` (the levels `M < Ω₁`), the generic
Lemma 3.30 facts of `R2.CitedTf`.  None of them computes `lhᵗ` at a level `M ≥ E₁`.

Literal texts: those of `R2.CitedRj` (T, Θ, U, W, S, L, C, E, G, LOC, D, TR, I, Λ, CR, H), quoted there word for word.

Our steps (`τ` a countable `ε`-number, `E₁ ≤ M < Γ_{Ω₁+1}` with `tfDat M ∈ Tᵗ`, `η ∈ Tᵗ ∩ Ω₁`, `α := ϑᵗ(Ω₁·M + η)`
strongly critical, `Δ := Ω₁·M`; used in the docstring of `qfLhT`):
* (☆1) `α = ϑᵗ(Δ + η)` with `Ω₁ ∣ Δ`, `η < Ω₁` (C); `Δ + η ∈ Tᵗ` (`tfArg_mem`), `τ < α ∈ E` (E, `Δ > 0`), and the
  leaves of `M` and `η` lie below `α` (`tfLevel_lt`), so `Δ ∈ Tᵗ_α` (D: `Δ^* < α`, step ◇Δ* of `R2.CitedTf`).
* (☆ι) **`ι_{τ,α}(z) = Θ_α(z)` for every code `z ∈ Tᵗ_α` below `Γ_{Ω₁+1}`.**  The canonical term of such a code (◇K* of
  `R2.CitedTf`) is built by `+` from `Ω₁ = ϑ₁(0)`, countable parts `< α`, powers `ω^e = ϑ₁(e⁻)` (◇N of `R2.CitedSy`)
  and `ε`-numbers `φ(a, c) = ϑ₁(Ω₂·a + c*)` (◇P* and O6 of `R2.CitedTf`).  By I, `ι := ι_{τ,α}` is the identity below
  `α`, additive (Lemma 7.2 (c)), strictly increasing (7.2 (b)), `ι(Ω₁) = ϑ^α(0) = α` (the note of I; Z at the base
  `α`), `ι(ω^e) = ϑ^α(ι(e⁻)) = ω^{ι(e)}` (W at the base `α`, as ★ι of `R2.CitedLu`), and `ι(φ(a, c)) = ϑ^α(Ω₁·ι(a) +
  ι(c*)) = φ(ι(a), ι(c))` (the note of I with the second and third clauses of I inside the argument, then ◇P* and O6 at
  the base `α` one cardinal down: `ϑ^α(Ω₁·a' + c') = V(a', c')` for `1 ≤ a' < Ω₁`, the fixed-point shift kept by `ι`
  as `ι` keeps `<`).  So `ι` maps the codes over `α` below `Γ_{Ω₁+1}` (`Gg.GgCl α`: generated from `[0, α)` and `Ω₁`
  by `+` and `φ`) onto the closure of `α + 1` under `+` and `φ`, which is the ordinal `Γ_{α+1}`; a strictly
  increasing map of a set of ordinals onto an ordinal is the order type function, `Θ_α`.  In particular `ι(Δ) =
  Θ_α(Δ)`, and `λᵗ_α = Θ_α(Δ) + ζᵗ_α` (Λ, `α ∈ E`) with `ζᵗ_α = lqZeta τ Δ η < α` (G, as in `rjLhT`).
* (☆δ) `δ := (λᵗ_α)^*` (H, the note) is the leading additive principal part of `Θ_α(Δ)` (`ζᵗ_α < α ≤` it):
  `δ = Θ_α(D)`, `D := ω^l`, `l := log_ω Δ` (☆ι: `Θ_α` keeps the Cantor normal form).  `Δ ≥ Ω₁·E₁ > ϑ₁(1) = Ω₁·ω`, so
  `δ > α`: the second branch of H.  `δ ∈ (α, α⁺)` (`α⁺ = ϑ^α(Δ) ≥ ϑ^α(Ω₁·Ω₁) = Γ_{α+1} > δ`, TR, E and L at the base
  `α`), so `δ^{t^α_τ} = δ` (TR).
* (☆loc) **The `α`-localization of `δ`.**  By I clause by clause, with S and U (`ι` keeps normal forms by 7.2 (b),
  (c)): the additive principal subterms of `ι(z)` in `[α, Ω₁)` of `T^α` are the images `ι(p)` of the `ϑ₁`-subterms `p ∈
  [Ω₁, Ω₂)` of the canonical term of `z`, and the argument of `ι(p) = ϑ^α(ι(arg p))` is `ι(arg p)`, ordered as `arg p`
  (7.2 (b)).  For an `ε`-code `p = φ(a_p, b_p)`, `arg p = Ω₂·a_p + b_p* ≥ Ω₂`; for a power `p = ω^e`, `arg p = e⁻ <
  Ω₂`.  So LOC (with Convention 6.6) picks at each step, among the subterms of `D` above the previous element, the
  `ε`-code with the largest `(a_p, b_p)`, or the power with the largest exponent if no `ε`-code is left; the sequence
  ends with `δ = ι(D)`.  For an element `δ_i = ι(p)`, `i < m`: if `p` is an `ε`-code, `δ_i = ϑ^α(Ω₁·ι(a_p) + ι(b_p*))`
  has `λ^α_{δ_i} = δ_i·ι(a_p) + ζ^α_{δ_i}` (Λ; ◆ι of `R2.CitedLv`: `ι_{α,δ_i}(Ω₁·β) = δ_i·β` for `β < δ_i`), which is
  `< ω^{ι(p) + log_ω ι(a_p) + 1}` (`ζ < δ_i`); if `p` is a power, `λ^α_{δ_i} = ζ^α_{δ_i} < δ_i` (Λ).
  - (a) `D` an `ε`-code (`ω^l = l`): every `δ_i`, `i < m`, is `< δ`, so `λ^α_{δ_i} < δ_i·δ_i < δ` (`ι(a_p) < δ_i`, `δ`
    an `ε`-number above `δ_i`): `cr(α, δ) = m` (CR).
  - (b) `D` a power and `c := ω^{log_ω l}` an `ε`-code with `l = c + x`, `x < c` (`QfCr`'s `l < c + c`): `c` is a
    subterm of `l`, and no subterm `q ≥ c` of `D` other than `c` has a larger argument (`q ∈ Sub(c)` gives `q ≤ c`, `q ∈
    Sub(x)` gives `q ≤ x < c`, `q = D` is a power), so `ι(c) = δ_i` for some `i < m`.  `λ^α_{ι(c)} ≥ δ = ω^{ι(c) + ι(x)}`
    iff `ι(x) ≤ log_ω ι(a_c)` iff `x ≤ log_ω a_c` (`Θ_α` keeps `<` and `log_ω`).  An earlier `δ_j < ι(c)` has `λ^α_{δ_j} <
    δ_j·δ_j < ι(c) ≤ δ`.  So `cr(α, δ) = i < m` iff `x ≤ log_ω a_c`, i.e. iff `QfCr M`.
  - (c) Otherwise every `ε`-element `δ_j = ι(p)` has `ι(p) + log_ω ι(a_p) + 1 ≤ ι(l)` (`p < c` gives `p + p < c ≤ l`;
    `p = c` with `l ≥ c + c`, or with `l = c + x`, `x > log_ω a_c`), so `λ^α_{δ_j} < ω^{ι(l)} = δ`: `cr(α, δ) = m`.
* (☆H) H: if `cr(α, δ) = i < m`, `lhᵗ(α) = lhᵗ(δ_i) + λᵗ_α = lhᵗ(Θ_α(c)) + (Θ_α(Δ) + ζᵗ_α)`; otherwise `lhᵗ(α) =
  lhᵗ(δ) + (−δ + λᵗ_α) = lhᵗ(Θ_α(ω^l)) + (Θ_α(Δ − ω^l) + ζᵗ_α)` (`Θ_α` additive, `ω^l ≤ Δ`).  The values `lhᵗ(Θ_α(c))`,
  `lhᵗ(Θ_α(ω^l))` are not part of the axiom (they are reaches of points of `(α, Γ_{α+1})`: `lh_eq_lhT`, `Qf.qf_lh`,
  `Lu.lu_lh_opow`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- The leading exponent `log_ω(Ω₁·M)`. -/
noncomputable def qfL (M : Ordinal.{0}) : Ordinal.{0} := log ω (Om1 * M)

/-- The leading additive principal part `ω^{log_ω l}` of `l = log_ω(Ω₁·M)`. -/
noncomputable def qfC (M : Ordinal.{0}) : Ordinal.{0} := ω ^ log ω (qfL M)

/-- **The condition `cr(α, δ) < m`** of [W07b] Def 4.1 at the Veblen level `M` (step ☆loc (b)). -/
def QfCr (M : Ordinal.{0}) : Prop :=
  ω ^ qfL M ≠ qfL M ∧ ω ^ qfC M = qfC M ∧ qfL M < qfC M + qfC M ∧ qfL M - qfC M ≤ log ω (invVeblen₁ (qfC M))

/-- **[W07b] Def 4.1, both branches (`cr(α, δ) < m` and `= m`), with [W07a] Def 7.5, Def 7.1, Lemma 7.2 (b)–(d),
Def 6.1, Def 4.11, Def 4.6, Def 7.15, Convention 6.6, Convention 4.1, Lemma 6.3, Lemma 4.2, Lemma 4.3, Lemma 3.30,
Def 3.28, Def 3.22, the Remark after Corollary 3.24** (texts H, Λ, I, D, G, LOC, CR, TR, C, W, E, L, S, T, U): for a
Veblen level `E₁ ≤ M < Γ_{Ω₁+1}` with `tfDat M ∈ Tᵗ`, `η ∈ Tᵗ ∩ Ω₁` and `α := ϑᵗ(Ω₁·M + η)` strongly critical:
**if `QfCr M`, `lhᵗ(α) = lhᵗ(Θ_α(c)) + (Θ_α(Ω₁·M) + ζᵗ_α)`; otherwise `lhᵗ(α) = lhᵗ(Θ_α(ω^l)) + (Θ_α(Ω₁·M − ω^l) +
ζᵗ_α)`**, `l = qfL M`, `c = qfC M`, `ζᵗ_α = lqZeta τ (Ω₁·M) η`.

Our steps.  ☆1, ☆ι (`λᵗ_α = Θ_α(Ω₁·M) + ζᵗ_α`), ☆δ (`δ = Θ_α(ω^l) > α`, the second branch of H), ☆loc (the
localization and `cr(α, δ)`: (a), (c) give `m`, (b) gives the index of `Θ_α(c)` exactly when `QfCr M`), ☆H.  The
hypothesis that `α` is strongly critical is kept so that ☆ι applies verbatim (codes over `α` in the sense of
`Gg.GgCl`). -/
axiom qfLhT {τ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Gg.ggE ≤ M) (hMG : M < Gg.ggGam)
    (hMT : Tf.tfDat M ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (hSC : Googology.Notation.InaccPsi.SC (vt τ (Om1 * M + η))) :
    (QfCr M → lhT τ (vt τ (Om1 * M + η)) =
      lhT τ (Gg.ggTh (vt τ (Om1 * M + η)) (qfC M)) +
        (Gg.ggTh (vt τ (Om1 * M + η)) (Om1 * M) + lqZeta τ (Om1 * M) η)) ∧
    (¬ QfCr M → lhT τ (vt τ (Om1 * M + η)) =
      lhT τ (Gg.ggTh (vt τ (Om1 * M + η)) (ω ^ qfL M)) +
        (Gg.ggTh (vt τ (Om1 * M + η)) (Om1 * M - ω ^ qfL M) + lqZeta τ (Om1 * M) η))

end Googology.Trans.PoR.InaccPsi.R2
