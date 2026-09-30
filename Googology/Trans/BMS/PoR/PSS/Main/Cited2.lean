import Googology.Trans.BMS.PoR.PSS.Main.LocSpec

/-!
# Cited facts for E1 and E2: Wilken's `ι_{τ,α}`, `t^α_τ`, `λ^τ` and the `≤₁`-localization

E1 and E2 (`Main/E12.lean`) use four more results of

* [W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", Annals of Pure
  and Applied Logic 145 (2007) 130–161;
* [W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", Annals of Pure
  and Applied Logic 145 (2007) 162–175.

This file gives the definitions they speak about, as syntactic operations on the
terms of `T¹` (`TR/Term.lean`, `τ = 1`), and states the results as axioms.

## Definitions

* `varthetaR τ k`: the functions `ϑ_k` of the relativized system `T^τ`
  ([W07a] §3, Convention 3.25: `ϑ^τ = ϑ_0` over `τ`, with `Ω_0 = τ`).  A constant
  without a definition, like `vartheta` of `TR/Cited.lean`.
* `AT`: terms of `T^α` whose parameters are ordinals `< α` given by their notation in
  `T¹` (`prm p`), and `ϑ_k(ξ)` (`th k ξ`, `ϑ_0 = ϑ^α`).  `AT.valR α` is the value.
* `iotaP`, `iotaS`: **`ι_{τ,α}`** ([W07a] Def 7.1) on `T^τ_α`.
* `embS`: an element `Δ` of `T¹` (a multiple of `Ω_1` whose `ϑ_0`-subterms are
  `< α`) read in `T^α` ("regarding `∆` to be represented in `T^α`", Def 6.2).
* `tP`, `tL`, `tS`: **`t^α_τ`** ([W07a] Def 6.2, the translation from `T^α` to `T^τ`),
  for `α = ϑ^τ(Δ + η)` given by its term `a`.
* `zetaT`: **`ζ^τ_α`** ([W07a] Def 4.11); `lamT`: **`λ^τ_α`** ([W07a] Def 7.5).

## The axioms

* [W07b] Theorem 5.3 (`λ` part, `τ = 1`): `thm53_lam`.
* [W07a] remark after Def 7.5 (from Cor 7.3 and Lemma 6.3): `iota_delta_t`.
* [W07a] Cor 7.3: `cor73_lt`, `cor73_delta`.
* [W07a] Lemma 6.3 (first item): `lemma63_plus`.
* [W07b] Cor 5.9 (`τ = 1`, the part used): `cor59`.
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal

/-! ## The relativized system `T^α` -/

/-- **The functions `ϑ_k` of `T^τ`** ([W07a] §3, relativized to `τ`; Convention 3.25:
`ϑ^τ := ϑ_0` over `τ`, where `Ω_0 = τ`).  A constant without a definition; the axioms
below state the cited facts about its values. -/
axiom varthetaR : Ordinal.{0} → ℕ → Ordinal.{0} → Ordinal.{0}

/-- A term of `T^α` ([W07a] §3 with `τ := α`): a parameter `prm p`, an ordinal `< α`
given by its (unique) notation `p` in `T¹`, or `ϑ_k(ξ)` (`th k ξ`), where `ξ` is a sum,
the list of its summands, the leftmost first.  `th 0 ξ` is `ϑ^α(ξ)`. -/
inductive AT where
  | prm (p : WP)
  | th (k : ℕ) (a : List AT)

/-- The level of a term of `T^α`: `0` for a parameter. -/
def AT.lvl : AT → ℕ
  | .prm _ => 0
  | .th k _ => k

mutual
/-- The value of a term of `T^α` (the base `α` is the first argument). -/
noncomputable def AT.valR (τ : Ordinal.{0}) : AT → Ordinal.{0}
  | .prm p => p.val
  | .th k a => varthetaR τ k (AT.valRS τ a)

/-- The value of a sum of `T^α`: the ordinal sum, the leftmost summand first. -/
noncomputable def AT.valRS (τ : Ordinal.{0}) : List AT → Ordinal.{0}
  | [] => 0
  | p :: l => AT.valR τ p + AT.valRS τ l
end

mutual
/-- `ξ` has a `ϑ^α`-subterm (a `th 0` subterm; parameters are atomic). -/
def AT.hasTh0 : AT → Bool
  | .prm _ => false
  | .th 0 _ => true
  | .th (_ + 1) a => AT.hasTh0S a

/-- A summand of the sum has a `ϑ^α`-subterm. -/
def AT.hasTh0S : List AT → Bool
  | [] => false
  | p :: l => AT.hasTh0 p || AT.hasTh0S l
end

/-- The parameter `1`. -/
def AT.isOne : AT → Bool
  | .prm p => decide (p = TR.one)
  | .th _ _ => false

/-! ## `ι_{τ,α}` ([W07a] Def 7.1) -/

mutual
/-- **`ι_{τ,α}`** ([W07a] Def 7.1) on a principal term of `T^τ_α`, `τ = 1`:
`ι(ξ) := ξ` for `ξ < α` (a `ϑ_0`-term of `T^τ_α` is below `α`, and becomes a parameter),
and `ι(ϑ_{k+1}(η)) := ϑ_k(ι(η))`.  On sums `ι` is additive (`iotaS`). -/
def iotaP : WP → AT
  | .th 0 b => .prm (.th 0 b)
  | .th (k + 1) b => .th k (iotaS b)

/-- `ι_{τ,α}` on a sum: `ι(ξ_1 + ξ_2) := ι(ξ_1) + ι(ξ_2)`. -/
def iotaS : List WP → List AT
  | [] => []
  | p :: l => iotaP p :: iotaS l
end

mutual
/-- A term of `T¹` whose `ϑ_0`-subterms are below `α`, read in `T^α`: the
`ϑ_0`-subterms become parameters, and `ϑ_{k+1}` stays `ϑ_{k+1}`. -/
def embP : WP → AT
  | .th 0 b => .prm (.th 0 b)
  | .th (k + 1) b => .th (k + 1) (embS b)

/-- A sum of `T¹` read in `T^α`. -/
def embS : List WP → List AT
  | [] => []
  | p :: l => embP p :: embS l
end

/-! ## `t^α_τ` ([W07a] Def 6.2) -/

/-- The case `ϑ^α(ξ)` of `t^α_τ` ([W07a] Def 6.2), for `α = ϑ^τ(Δ + η)` given by its term
`a` (`Δ = argD a.arg`, `η = argE a.arg`), from `ξ` (`x`) and the translations `ys` of the
summands of `ξ`:

* `ϑ^α(0)^t := ϑ^τ(Δ + η) = α`;
* for `ϑ^α(ξ) ∈ (α, ϑ^α(Δ))`, with `ξ = Γ + ρ` (`Γ` the summands of level `≥ 1`,
  Convention 4.1): `ϑ^τ(α + (−1 + ρ)^t)` if `Γ = 0`; `ϑ^τ(Γ^t + α + ρ^t)` if `Γ > 0` and
  `Γ^* < α`; `ϑ^τ(Γ^t + ρ^t)` if `Γ^* ≥ α`;
* `ϑ^α(Δ)^t := ϑ^τ(Δ + η + 1)`;
* `ϑ^α(ξ)^t := 0` if `ϑ^α(ξ) > ϑ^α(Δ)`.

`Γ^* ≥ α` is read as "`Γ` has a `ϑ^α`-subterm": `Γ^*` is the largest element of
`P^α_0(Γ) = Sub^α_0(Γ) ∩ P ∩ [α, Ω_1)` ([W07a] Def 3.28 with `Ω_0 = α`), and the principal
subterms with values in `[α, Ω_1)` are the `ϑ^α`-subterms ([W07a] Lemma 3.30: `ϑ^α`-values
lie in `[α, Ω_1)`, `ϑ_k`-values for `k ≥ 1` in `[Ω_k, Ω_{k+1})`; parameters are `< α`).
`−1 + ρ` drops a first summand `1` (for `ρ ≥ ω` it is `ρ`).  Sums are written as
concatenations, whose values are the ordinal sums. -/
noncomputable def tTop (a : WP) (x : List AT) (ys : List (List WP)) : List WP :=
  if x.isEmpty then [a]
  else if (AT.th 0 x).valR a.val < (AT.th 0 (embS (argD a.arg))).valR a.val then
    if (x.takeWhile (fun q => decide (1 ≤ q.lvl))).isEmpty then
      [.th 0 (a :: (if (x.head?.map AT.isOne) = some true then (ys.drop 1).flatten
        else ys.flatten))]
    else
      let n := (x.takeWhile (fun q => decide (1 ≤ q.lvl))).length
      if AT.hasTh0S (x.take n) then [.th 0 ((ys.take n).flatten ++ (ys.drop n).flatten)]
      else [.th 0 ((ys.take n).flatten ++ a :: (ys.drop n).flatten)]
  else if (AT.th 0 x).valR a.val = (AT.th 0 (embS (argD a.arg))).valR a.val then
    [.th 0 (a.arg ++ [TR.one])]
  else []

mutual
/-- **`t^α_τ`** ([W07a] Def 6.2), `τ = 1`, on a principal term of `T^α`:
a parameter `ξ < α` goes to its notation in `T^τ`; `ϑ_k(ξ)^t := ϑ_k(ξ^t)` for `k > 0`;
`ϑ^α(ξ)` by `tTop`. -/
noncomputable def tP (a : WP) : AT → List WP
  | .prm p => [p]
  | .th (k + 1) x => [.th (k + 1) (tL a x).flatten]
  | .th 0 x => tTop a x (tL a x)

/-- The translations of the summands of a sum of `T^α`. -/
noncomputable def tL (a : WP) : List AT → List (List WP)
  | [] => []
  | q :: l => tP a q :: tL a l
end

/-- **`t^α_τ`** on a sum: `(ξ_1 + ξ_2)^t := ξ_1^t + ξ_2^t`. -/
noncomputable def tS (a : WP) (x : List AT) : List WP := (tL a x).flatten

/-! ## `ζ^τ_α` and `λ^τ_α` -/

/-- **`ζ^τ_α`** ([W07a] Def 4.11), `τ = 1`, for `α = ϑ^τ(Δ + η)`:
`logend(η)` if `η < sup_{σ < η} ϑ^τ(Δ + σ)`, and `0` otherwise.  The condition is read with
[W07a] Lemma 4.4 (as for `barT` in `Main/Loc.lean`): for `η > 0`,
`η = sup_{σ < η} ϑ^τ(Δ + σ)` iff `η` is a sup-point (`supPt`), and `η ≤` the supremum
always; for `η = 0` the supremum is `0`. -/
noncomputable def zetaT (a : WP) : Ordinal.{0} :=
  open Classical in
  if argE a.arg ≠ [] ∧ ¬ supPt (argD a.arg) (argE a.arg) then logend (WP.valS (argE a.arg))
  else 0

/-- **`λ^τ_α`** ([W07a] Def 7.5), `τ = 1`, for `α = ϑ^τ(Δ + η) > τ`:
`ι_{τ,α}(Δ) + ζ^τ_α` if `α ∈ E`, and `ζ^τ_α` otherwise. -/
noncomputable def lamT (a : WP) : Ordinal.{0} :=
  open Classical in
  if InE a.val then AT.valRS a.val (iotaS (argD a.arg)) + zetaT a else zetaT a

/-! ## [W07b] Theorem 5.3 -/

/-- **[W07b] Theorem 5.3** (`τ = 1`): "Let `α = ϑ^τ(∆ + η) ∈ T^τ`, `α > τ`, and
`(τ = α_0, …, α_n = α)` be its localization. Then `κ^τ_α = lh(α_i) + α` if
`i := cr(τ, α) < n`, `α` otherwise. We have `λ_α = λ^τ_α` and `lh(α) = lh^τ(α)`."
Stated here: `λ_α = λ^τ_α` (`lam` is `λ_τ` of [W07b] Def 3.2 at `τ := α`). -/
axiom thm53_lam {a : WP} (ha : NFP a) (h0 : a.lvl = 0) (h1 : 1 < a.val) : lam a.val = lamT a

/-! ## [W07a] Corollary 7.3, Lemma 6.3 and the remark after Definition 7.5 -/

/-- **The remark after [W07a] Def 7.5**: "Note that in the case `α ∈ E` we have `∆ > 0`
whence `ι_{τ,α}` is defined and `ι_{τ,α}(∆) < α^+` by Corollary 7.3 which gives
`ι_{τ,α}(∆)^{t^α_τ} = ι_{τ,α}(∆)`."  (`τ = 1`; `∆ > 0` is `argD a.arg ≠ []`.)  As values:
the translation of `ι_{τ,α}(∆)` to `T^τ` denotes the ordinal `ι_{τ,α}(∆)`. -/
axiom iota_delta_t {a : WP} (ha : NFP a) (h0 : a.lvl = 0) (hΔ : argD a.arg ≠ []) :
    AT.valRS a.val (iotaS (argD a.arg)) = WP.valS (tS a (iotaS (argD a.arg)))

/-- **[W07a] Corollary 7.3** (first part): "`ι_{τ,α}` is a `(<, +)`-isomorphism of
`T^τ_α` and `T^α`", for `α = ϑ^τ(∆ + η)` with `∆ > 0` (Def 7.1), `τ = 1`.  Here
`T^τ_α = {β ∈ T^τ | β^* < α}` ([W07a] Def 6.1): the `ϑ_0`-subterms of `β` are below `α`.
Stated for the order. -/
axiom cor73_lt {a : WP} (ha : NFP a) (h0 : a.lvl = 0) (hΔ : argD a.arg ≠ []) {x y : List WP}
    (hx : NFS x) (hy : NFS y) (hx0 : ∀ s ∈ starS 0 x, s.val < a.val)
    (hy0 : ∀ s ∈ starS 0 y, s.val < a.val) :
    WP.valS x < WP.valS y ↔ AT.valRS a.val (iotaS x) < AT.valRS a.val (iotaS y)

/-- **[W07a] Corollary 7.3** (second part): "`ι_{τ,α}(∆) < α^+`", where
`α^+ := ϑ^τ(∆ + η + 1)` ([W07a] Convention 4.1), `τ = 1`. -/
axiom cor73_delta {a : WP} (ha : NFP a) (h0 : a.lvl = 0) (hΔ : argD a.arg ≠ []) :
    AT.valRS a.val (iotaS (argD a.arg)) < (WP.th 0 (a.arg ++ [TR.one])).val

/-- **[W07a] Lemma 6.3** (first item): "`α^+ = ϑ^α(∆)`", for `α = ϑ^τ(∆ + η)` with
`∆ > 0` (Def 6.2), `τ = 1`; `∆` is read in `T^α` (`embS`). -/
axiom lemma63_plus {a : WP} (ha : NFP a) (h0 : a.lvl = 0) (hΔ : argD a.arg ≠ []) :
    (WP.th 0 (a.arg ++ [TR.one])).val = (AT.th 0 (embS (argD a.arg))).valR a.val

/-! ## [W07b] Corollary 5.9 -/

/-- **[W07b] Corollary 5.9** (`τ = 1`): "Let `α ∈ T^τ`, `α > τ`, be of a form
`ϑ^τ(∆+η)` and let its `τ`-localization be given by `(τ = α_0, …, α_n = α)`. The
`τ`-`≤₁`-localization `(β_1, …, β_m)` of `α` is included in the `τ`-localization of `α`.
The greatest `<₁`-predecessor of `α` in the interval `(τ, α)` is `α_i` where
`i ∈ {1, …, n − 1}` is maximal such that `λ^τ_{α_i} ≥ α`, if this exists. Otherwise, `α` is
`τ`-`≤₁`-minimal."

Stated here without the characterization of `i` by `λ^τ`: either some `α_i` with
`i ∈ [1, n − 1]` (an element of `(loc b).dropLast`, [W07a] Def 4.6 as `loc`) is the greatest
`<₁`-predecessor of `α` in `(τ, α)`, or `α` is `τ`-`≤₁`-minimal. -/
axiom cor59 {b : WP} (hb : NFP b) (h0 : b.lvl = 0) (h1 : 1 < b.val) :
    (∃ γ ∈ (loc b).dropLast, le1 γ.val b.val ∧ γ.val ≠ b.val ∧
        ∀ δ, 1 < δ → δ < b.val → le1 δ b.val → δ ≤ γ.val) ∨ MinT 1 b.val

end Googology.Trans.PSS.Main
