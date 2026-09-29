import Googology.Trans.PSS.TR.Term
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.SetTheory.Ordinal.Exponential

/-!
# The cited facts on Wilken's `ϑ`-functions

`proof/TR.md` §1 cites facts on Wilken's `ϑ`-functions from three papers:

* [W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", Annals of Pure
  and Applied Logic 145 (2007) 130–161;
* [W24] G. Wilken, "Fundamental sequences based on localization",
  arXiv:2410.15953 (v4);
* [WW11] A. Weiermann, G. Wilken, "Ordinal arithmetic with simultaneously
  defined theta-functions", Mathematical Logic Quarterly 57 (2011) 116–132.

This file states them as axioms.  **These are the only axioms of the
translation `𝒯`** (besides Lean's `propext`, `Classical.choice`,
`Quot.sound`).  Everything else about `𝒯` is proved from them.

## The setting

* `Om m` is `Ω_m`: `Ω_0 = 1 = τ` and `Ω_m = ℵ_m` for `m ≥ 1`.
* `vartheta m` is Wilken's `ϑ_m` ([W07a] §3 with `τ = 1`), a constant with no
  definition here.  Only its values at the terms of `T¹` are used.
* `WP.val`, `WP.valS`: the value of a principal term and of a sum.
* `NFP p`, `NFS x`: `p` (resp. `x`) is a term of `T¹` ([W07a] Def 3.22): sums
  are non-increasing sums of principal terms, and in `ϑ_m(ξ)` every summand of
  `ξ` has level `≤ m + 1`, i.e. `ξ < Ω_{m+2}`.  By [W07a] Lemma 3.30 no other
  normal-form condition is needed.
* `PT`: the terms of `T^{Ω_j}`, which may contain parameters `α < Ω_j`
  ([W24] §2).  They are used only in (Min).

## The axioms

* (L) `val_level`, `val_isPrincipal`, `vartheta_zero`, `vartheta_inj`;
* (C) `star_lt_val`, `val_lt_val_iff`;
* (E) `eps_iff`;
* (Exp) `val_exp`, `val_exp_eps`;
* (Seg) `seg`;
* (Min) `vartheta_min`.

(Inc) of `proof/TR.md` §1 is not an axiom: on `T¹` it follows from (C)
(`inc_lt`, `inc_le` in `TR/LCBase.lean`).  (Min) is stated but not used: the
C1 sub-case of `(B j₀)` is proved by the size induction of the general case
(`base_C1` in `TR/BaseC1.lean`), as `proof/TR-2.md` §7 suggests.  So the proof of
Lemma TR uses the axioms (L), (C), (E), (Exp) and (Seg).
-/

namespace Googology.Trans.PSS.TR

open Ordinal Cardinal

/-- `Ω_m`: `Ω_0 = 1` (`= τ`) and `Ω_m = ℵ_m` for `m ≥ 1`. -/
noncomputable def Om : ℕ → Ordinal.{0}
  | 0 => 1
  | m + 1 => (ℵ_ ((m + 1 : ℕ) : Ordinal.{0})).ord

/-- **Wilken's `ϑ_m`** ([W07a] §3, with `τ = 1`; [W24] §2).  It is a constant
without a definition; the axioms below state the cited facts about its values
on `T¹`. -/
axiom vartheta : ℕ → Ordinal.{0} → Ordinal.{0}

mutual
/-- The value of a principal term: `val (ϑ_m(ξ)) = ϑ_m(val ξ)`. -/
noncomputable def WP.val : WP → Ordinal.{0}
  | .th m a => vartheta m (WP.valS a)

/-- The value of a sum: the ordinal sum of its summands, the leftmost first. -/
noncomputable def WP.valS : List WP → Ordinal.{0}
  | [] => 0
  | p :: l => p.val + WP.valS l
end

@[simp] theorem WP.val_th (m : ℕ) (a : List WP) : (WP.th m a).val = vartheta m (WP.valS a) := by
  rw [WP.val]

@[simp] theorem WP.valS_nil : WP.valS [] = 0 := by rw [WP.valS]

@[simp] theorem WP.valS_cons (p : WP) (l : List WP) : WP.valS (p :: l) = p.val + WP.valS l := by
  rw [WP.valS]

/-- **The terms of `T¹`** ([W07a] Def 3.22): `ϑ_m(ξ)` where `ξ` is a non-increasing
sum of terms of `T¹` whose summands have level `≤ m + 1` (so `ξ < Ω_{m+2}`). -/
inductive NFP : WP → Prop
  | th {m : ℕ} {a : List WP} (hn : ∀ q ∈ a, NFP q) (hl : ∀ q ∈ a, q.lvl ≤ m + 1)
      (hd : a.Pairwise (fun p q => q.val ≤ p.val)) : NFP (.th m a)

/-- A sum of `T¹`: a non-increasing sum of principal terms of `T¹`. -/
def NFS (x : List WP) : Prop := (∀ p ∈ x, NFP p) ∧ x.Pairwise (fun p q => q.val ≤ p.val)

/-- The exponent base of (Exp): `0` at level `0` and `Ω_m` at level `m ≥ 1`. -/
noncomputable def expBase (m : ℕ) : Ordinal.{0} := if m = 0 then 0 else Om m

/-! ## Terms with parameters, for (Min) -/

/-- A term of `T^{Ω_j}`: parameters `prm α` (with `α < Ω_j`, see `PNF`), and
`ϑ_m(ξ)` with `ξ` a sum. -/
inductive PT where
  | prm (α : Ordinal.{0})
  | th (m : ℕ) (a : List PT)

/-- The level of a term with parameters (`0` for a parameter). -/
def PT.lvl : PT → ℕ
  | .prm _ => 0
  | .th m _ => m

mutual
/-- The value of a term with parameters. -/
noncomputable def PT.val : PT → Ordinal.{0}
  | .prm α => α
  | .th m a => vartheta m (PT.valS a)

/-- The value of a sum of terms with parameters. -/
noncomputable def PT.valS : List PT → Ordinal.{0}
  | [] => 0
  | p :: l => p.val + PT.valS l
end

mutual
/-- The `ϑ_m`-subterms of `p` not inside a `ϑ_k` with `k < m`; a parameter has
none. -/
def PT.starP (m : ℕ) : PT → List PT
  | .prm _ => []
  | .th k a => if k < m then [] else if k = m then .th k a :: PT.starS m a else PT.starS m a

/-- The `ϑ_m`-subterms of a sum not inside a `ϑ_k` with `k < m`. -/
def PT.starS (m : ℕ) : List PT → List PT
  | [] => []
  | p :: l => PT.starP m p ++ PT.starS m l
end

/-- **The terms of `T^{Ω_j}`**: parameters are additive principal ordinals below
`Ω_j`; sums are non-increasing; in `ϑ_m(ξ)` the summands of `ξ` have level
`≤ m + 1`. -/
inductive PNF (j : ℕ) : PT → Prop
  | prm {α : Ordinal.{0}} (hα : α < Om j) (hp : IsPrincipal (· + ·) α) (h0 : α ≠ 0) :
      PNF j (.prm α)
  | th {m : ℕ} {a : List PT} (hn : ∀ q ∈ a, PNF j q) (hl : ∀ q ∈ a, q.lvl ≤ m + 1)
      (hd : a.Pairwise (fun p q => q.val ≤ p.val)) : PNF j (.th m a)

/-- A sum of `T^{Ω_j}`. -/
def PNFS (j : ℕ) (x : List PT) : Prop :=
  (∀ p ∈ x, PNF j p) ∧ x.Pairwise (fun p q => q.val ≤ p.val)

/-! ## (L) Levels -/

/-- **(L), levels** ([W07a] Lemma 3.30): the value of a principal term
`ϑ_m(ξ)` of `T¹` lies in `[Ω_m, Ω_{m+1})`. -/
axiom val_level {p : WP} (hp : NFP p) : Om p.lvl ≤ p.val ∧ p.val < Om (p.lvl + 1)

/-- **(L), principal values** ([W07a] Lemma 3.30; `ϑ_m`-values lie in the class
`P` of additive principal numbers): the value of a principal term of `T¹` is
additive principal. -/
axiom val_isPrincipal {p : WP} (hp : NFP p) : IsPrincipal (· + ·) p.val

/-- **(L), base values** ([W07a] §3, `τ = 1`): `ϑ_0(0) = 1 = τ` and
`ϑ_m(0) = Ω_m` for `m ≥ 1`. -/
axiom vartheta_zero (m : ℕ) : vartheta m 0 = Om m

/-- **(L), injectivity** ([W07a] Lemma 3.30): `ϑ_m` is 1-1 on `T ∩ Ω_{m+2}`. -/
axiom vartheta_inj {m : ℕ} {a c : List WP} (ha : NFP (.th m a)) (hc : NFP (.th m c))
    (h : (WP.th m a).val = (WP.th m c).val) : WP.valS a = WP.valS c

/-! ## (C) Comparison -/

/-- **(C), first part** ([W07a] Lemma 3.30 = [W24] Prop 2.3): `β^{⋆_m} < ϑ_m(β)`,
i.e. every `ϑ_m`-subterm of `β` not inside a `ϑ_k` with `k < m` is below
`ϑ_m(β)`. -/
axiom star_lt_val {m : ℕ} {a : List WP} (h : NFP (.th m a)) :
    ∀ s ∈ starS m a, s.val < (WP.th m a).val

/-- **(C), the comparison** ([W07a] Lemma 3.30 = [W24] Prop 2.3): for terms of
`T¹` of one level `m`,
`ϑ_m(α) < ϑ_m(γ) ⟺ (α < γ ∧ α^{⋆_m} < ϑ_m(γ)) ∨ ϑ_m(α) ≤ γ^{⋆_m}`.
Here `ξ^{⋆_m}` is the largest `ϑ_m`-subterm of `ξ` not inside a `ϑ_k` with
`k < m`, or `0` if there is none. -/
axiom val_lt_val_iff {m : ℕ} {a c : List WP} (ha : NFP (.th m a)) (hc : NFP (.th m c)) :
    (WP.th m a).val < (WP.th m c).val ↔
      (WP.valS a < WP.valS c ∧ ∀ s ∈ starS m a, s.val < (WP.th m c).val) ∨
        ∃ s ∈ starS m c, (WP.th m a).val ≤ s.val

/-! ## (E) Epsilon numbers -/

/-- **(E)** ([W24] Lemma 2.4, all levels; [W07a] Lemma 4.3 for level 0):
`ϑ_j(Δ + η)`, with `Δ` the part of the argument of level `≥ j + 1`, is an epsilon
number above `Ω_j` iff `Δ > 0`. -/
axiom eps_iff {j : ℕ} {a : List WP} (h : NFP (.th j a)) :
    (∃ q ∈ a.head?, j + 1 ≤ q.lvl) ↔
      (Om j < (WP.th j a).val ∧ ω ^ (WP.th j a).val = (WP.th j a).val)

/-! ## (Exp) Powers of `ω` -/

/-- **(Exp)** ([WW11] Lemma 2.12(b); [W07a] Lemma 4.2): for `ξ < Ω_{m+1}` not of
the form `ε + n` (with `ε` an epsilon number `ϑ_m(Δ + η)`, `Δ > 0`, and `n < ω`),
`ϑ_m(ξ) = ω^{Ω_m + ξ}` for `m ≥ 1` and `ϑ_0(ξ) = ω^ξ`.  So `ω^Z = ϑ_m(-Ω_m + Z)`
for `Z ∈ [Ω_m, Ω_{m+1})`, as in `omega_exp` of `por/tr.py`. -/
axiom val_exp {m : ℕ} {a : List WP} (h : NFP (.th m a)) (ha : ∀ q ∈ a, q.lvl ≤ m)
    (hne : isEpsPlusN a m = false) : (WP.th m a).val = ω ^ (expBase m + WP.valS a)

/-- **(Exp), the fixed points** ([WW11] Lemma 2.12(b); [W07a] Lemma 4.2): for
`ξ = ε + n` with `ε` an epsilon number `ϑ_m(Δ + η)` (`Δ > 0`) and `n < ω`,
`ϑ_m(ε + n) = ω^{ε + n + 1}`. -/
axiom val_exp_eps {m : ℕ} {a : List WP} (h : NFP (.th m a)) (he : isEpsPlusN a m = true) :
    (WP.th m a).val = ω ^ (WP.valS a + 1)

/-! ## (Seg) The countable part is an ordinal -/

/-- **(Seg)** ([W24] Thm 2.1; [W07a] Theorem 3.23: `T_m ∩ Ω_{m+1} = θ_m`):
`T¹ ∩ Ω_1` is an ordinal.  Every ordinal below the value of a sum of `T¹` that
is below `Ω_1` is the value of a sum of `T¹`. -/
axiom seg {x : List WP} (hx : NFS x) (h1 : WP.valS x < Om 1) {β : Ordinal.{0}}
    (hβ : β < WP.valS x) : ∃ u, NFS u ∧ WP.valS u = β

/-! ## (Min) Minimality -/

/-- **(Min)** ([W24] Prop 2.2), the minimality half: `ϑ_j(α)` is the least
additive principal `θ ≥ Ω_j` with `α^{⋆_j} < θ` and
`∀ β ∈ T^{Ω_j} ∩ α (β^{⋆_j} < θ → ϑ_j(β) < θ)`.  Here `β` ranges over the terms
of `T^{Ω_j}`, which may contain parameters below `Ω_j` (`PNFS j`).
(`proof/TR.md` §1 writes `θ ≥ Ω_j`; the minimum is over additive principal
`θ`, as in Wilken's definition of `ϑ_j`.) -/
axiom vartheta_min {j : ℕ} {a : List WP} (h : NFP (.th j a)) {θ : Ordinal.{0}}
    (hθ : IsPrincipal (· + ·) θ) (hΩ : Om j ≤ θ) (h1 : ∀ s ∈ starS j a, s.val < θ)
    (h2 : ∀ β : List PT, PNFS j β → PT.valS β < WP.valS a →
      (∀ s ∈ PT.starS j β, s.val < θ) → vartheta j (PT.valS β) < θ) :
    (WP.th j a).val ≤ θ

end Googology.Trans.PSS.TR
