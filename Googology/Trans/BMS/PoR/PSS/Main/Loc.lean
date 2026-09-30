import Googology.Trans.BMS.PoR.PSS.TR
import Mathlib.Data.List.MinMax

/-!
# Localization and the bar operator on `T¹`

This file defines two syntactic operations of Wilken and Carlson–Wilken on the
terms of `T¹` (`TR/Term.lean`, `τ = 1`):

* **localization** ([W07a] Def 4.6): for `α = ϑ_0(Δ + η)`, `α_0 := τ = 1`, and
  while `α_n < α`, `α_{n+1}` is the element `ϑ_0(ξ)` of `P(α) - (α_n + 1)` with
  the largest argument `ξ`.  `P(α)` is the set of the `ϑ_0`-subterms of `α`
  ([W07a] Def 3.28 with `m = 0`: `Sub_0` decomposes everything, so
  `P_0(α) = Sub_0(α) ∩ P ∩ [Ω_0, Ω_1)` is the set of all `ϑ_0`-subterms).
  `loc α` is the list `[α_1, …, α_n]`, and `locPred α` is `α_{n-1}`
  (`τ = 1` when `n = 1`).
* **bar** ([CW12] Def 5.1): for `α = ϑ_0(Δ + η) > τ`,
  - if `η = η' + η_0` with `η_0 ∈ P` and `η' = 0` or `η =_NF η' + η_0`, and
    either `η_0 = 1` or `η' < sup_{σ < η'} ϑ_0(Δ + σ)`, then
    `ᾱ := ϑ_0(Δ + η')`;
  - otherwise `ᾱ := α_{n-1}`.

  Here `Δ` is the part of the argument of level `≥ 1` (a multiple of `Ω_1`) and
  `η < Ω_1` the rest ([W07a] Convention 4.1).  On a term of `T¹` the argument is
  a non-increasing list of principal terms, so `η = η' + η_0` in normal form means
  that `η_0` is the last summand and `η'` the others.

  The condition `η' < sup_{σ < η'} ϑ_0(Δ + σ)` is read with [W07a] Lemma 4.4:
  for `η' > 0`, `η' = sup_{σ < η'} ϑ_0(Δ + σ)` iff `η'` has the form
  `ϑ_0(Γ + ρ)` with `Γ > Δ` and `η' > Δ^*` (`supPt`); since `η' ≤` that
  supremum always, `η' < sup` iff `η' > 0` and not `supPt`.  For `η' = 0` the
  supremum is empty, so the condition is false.

The operations use the values of terms (`TR/Cited.lean`), so they are
noncomputable.  `barO` lifts `bar` to ordinals: an additive principal ordinal
below `Ω_1` that is the value of a principal term of `T¹` of level `0` has one
such term (`eq_of_val_eq`), and `barO β` is the value of its bar.
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal

noncomputable section

open Classical

/-- `P(α)` of [W07a] Def 3.28 (`τ = 1`, `m = 0`): the `ϑ_0`-subterms of `p`,
`p` itself included when it has level `0`. -/
def sub0 (p : WP) : List WP := starP 0 p

/-- One step of the localization: among the `ϑ_0`-subterms of `α` with value above
`cur`, the one with the largest argument. -/
def locStep (α : WP) (cur : Ordinal.{0}) : Option WP :=
  ((sub0 α).filter (fun q => decide (cur < q.val))).argmax (fun q => WP.valS q.arg)

/-- The localization from the value `cur`, with fuel. -/
def locFrom (α : WP) : ℕ → Ordinal.{0} → List WP
  | 0, _ => []
  | n + 1, cur =>
    match locStep α cur with
    | none => []
    | some q => q :: locFrom α n q.val

/-- **The localization** of `α` ([W07a] Def 4.6, `τ = 1`): the list
`[α_1, …, α_n]`; `α_0 = τ = 1` is left out.  The fuel is the number of
`ϑ_0`-subterms, enough since the values strictly increase. -/
def loc (α : WP) : List WP := locFrom α (sub0 α).length 1

/-- `α_{n-1}`: the element of the localization before `α`, or `τ = 1` (`one`)
when the localization is `(τ, α)`. -/
def locPred (α : WP) : WP :=
  match (loc α).dropLast.getLast? with
  | some q => q
  | none => TR.one

/-- The part `Δ` of the argument of `ϑ_0(Δ + η)` of level `≥ 1`. -/
def argD (a : List WP) : List WP := a.takeWhile (fun q => decide (1 ≤ q.lvl))

/-- The part `η < Ω_1` of the argument of `ϑ_0(Δ + η)`. -/
def argE (a : List WP) : List WP := a.dropWhile (fun q => decide (1 ≤ q.lvl))

/-- **Sup-points** ([W07a] Lemma 4.4): `η` has the form `ϑ_0(Γ + ρ)` with
`Γ > Δ` and `η > Δ^*` (`Δ^*` the largest `ϑ_0`-subterm of `Δ`, or `0`).  By
Lemma 4.4 this is `η = sup_{σ < η} ϑ_0(Δ + σ)` for `η > 0`. -/
def supPt (Δ η : List WP) : Prop :=
  ∃ q, η = [q] ∧ q.lvl = 0 ∧ WP.valS Δ < WP.valS (argD q.arg) ∧
    ∀ s ∈ starS 0 Δ, s.val < q.val

/-- **The bar operator** of [CW12] Def 5.1 on a principal term `α = ϑ_0(Δ + η)`
of `T¹` with `α > 1`. -/
def barT (α : WP) : WP :=
  match (argE α.arg).getLast? with
  | none => locPred α
  | some η0 =>
    let η' := (argE α.arg).dropLast
    if η0 = TR.one ∨ (η' ≠ [] ∧ ¬ supPt (argD α.arg) η') then .th 0 (argD α.arg ++ η')
    else locPred α

/-- **Bar on ordinals**: the bar of the principal term of `T¹` of level `0` with
value `β` (`0` if there is none). -/
def barO (β : Ordinal.{0}) : Ordinal.{0} :=
  if h : ∃ p : WP, NFP p ∧ p.lvl = 0 ∧ p.val = β then (barT h.choose).val else 0

end

end Googology.Trans.PSS.Main
