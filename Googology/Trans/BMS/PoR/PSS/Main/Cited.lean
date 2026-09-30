import Googology.Trans.BMS.PoR.PSS.Main.Loc

/-!
# The cited facts on `R₁⁺` (Carlson's `≤₁`) as axioms

The main chain of `proof/PROOF.md` uses results from four papers:

* [C01] T. J. Carlson, "Elementary patterns of resemblance", Annals of Pure and
  Applied Logic 108 (2001) 19–77;
* [W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", Annals of Pure
  and Applied Logic 145 (2007) 130–161;
* [W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", Annals of Pure
  and Applied Logic 145 (2007) 162–175;
* [CW12] T. J. Carlson, G. Wilken, "Normal forms for elementary patterns",
  Journal of Symbolic Logic 77 (2012) 174–194.

This file states the facts that are used as axioms, together with the
definitions they speak about.  The facts on Wilken's `ϑ`-terms that `𝒯` needs
are in `TR/Cited.lean`.

## The structure `R₁`

`R₁ = (On; 0, +, ≤, ≤₁)`, where `+` is the graph of ordinal addition and
`α ≤₁ β` iff `(α; 0, +, ≤, ≤₁)` is a `Σ₁`-elementary substructure of
`(β; 0, +, ≤, ≤₁)` ([C01] §1, [W07b] §1; defined by recursion on `β`).  Carlson
calls it `R₁`; it is the `R₁⁺` of the conjecture.  Here `≤₁` is the constant
`le1` without a definition; the axioms below state the cited facts about it.

## Definitions

* `Pr α`: `α` is additive principal (`α ∈ P`, so `α ≠ 0`).  `InL α`: `α ∈ L`, a
  limit of additive principal numbers.  `nextL α`: `α^L`, the least element of
  `L` above `α`.  `logend α`: the exponent of the last summand of the Cantor
  normal form of `α` (`0` for `α = 0`).
* `IsLh α β`: `β = lh(α) = max{β | α ≤₁ β}` ([W07b] Def 3.1).
* `MinT τ α`: `α` is `τ`-`≤₁`-minimal; `kap τ ξ` is `κ^τ_ξ`, `theta τ` is
  `θ_τ` and `lam τ` is `λ_τ` ([W07b] Def 3.2).
* `T1bound`: `T¹ ∩ Ω_1` of [W07a] Theorem 3.23, the supremum of the values of
  the sums of `T¹` below `Ω_1`.
* Patterns ([C01] §4, [CW12] p.176): `ANF`, `ClosedSet`, `IsoVia`, `PwLe`,
  `CoveringVia`, `Isominimal`, `CoreR1`.
* `InP1 α`: the closure of `{0, 1, α}` under additive decomposition, `lh` and bar
  (the right side of [CW12] Cor 6.3 (2); only this closure is used, not its identity
  with Carlson–Wilken's `P_1(α)`).

## The axioms

* [W07b] Lemma 2.1: `le1_refl`, `le1_trans`, `le1_le` (`≤₁` is a partial order
  contained in `≤`), `le1_limit` (a), `le1_of_le` (b); (c) follows from (b).
* [W07b] Theorem 2.2: `le1_add_iff`.  [W07b] §2 after Theorem 2.2:
  `exists_le1_gt_iff`.
* [W07b] Lemma 3.3 (b), (c), (d): `kap_small`, `kap_add`, `kap_theta`.
* [W07b] Lemma 3.4 (a), (b): `lam_spec`, `kap_principal`.
* [W07b] Corollary 5.10 (`τ = 1`): `le1_T1bound`, `not_lt1_infty`.
* ([CW12] Core Structure Theorem (2) and Corollary 6.3 are **not** used: the Main
  Theorem gets isominimality from Theorem LEAST, `Main/Least.lean`, and finiteness of
  `P_1(α)` from Theorem FIN, `Main/Fin.lean`; their cited facts are in `Main/Cited3.lean`.)
* The identification of the core with `ψ_0(Ω_ω)`: `core_eq_psi` (C3 and the
  outside assumption M13 of `proof/PROOF.md` §1.4).  It is used only in
  Cor 7.2 (b′).
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal

/-! ## `≤₁` -/

/-- **Carlson's `≤₁`** on the ordinals ([C01] §1; [W07b] §1):
`α ≤₁ β` iff `(α; 0, +, ≤, ≤₁) ≼_{Σ₁} (β; 0, +, ≤, ≤₁)`.  It is a constant
without a definition; the axioms of this file state the cited facts about it. -/
axiom le1 : Ordinal.{0} → Ordinal.{0} → Prop

/-! ## Classes of ordinals -/

/-- `α ∈ P`: `α` is an additive principal number (so `α ≠ 0`). -/
def Pr (α : Ordinal.{0}) : Prop := IsPrincipal (· + ·) α ∧ α ≠ 0

/-- `α ∈ L = Lim(P)` ([W07a] §2): `α ∈ P` is a proper supremum of elements of
`P`, i.e. every `β < α` lies below some `γ ∈ P` with `γ < α`. -/
def InL (α : Ordinal.{0}) : Prop := Pr α ∧ ∀ β < α, ∃ γ, Pr γ ∧ β < γ ∧ γ < α

/-- `α ∈ E`: `α` is an epsilon number, `ω^α = α`. -/
def InE (α : Ordinal.{0}) : Prop := ω ^ α = α

/-- `α^L`: the least element of `L` above `α`. -/
noncomputable def nextL (α : Ordinal.{0}) : Ordinal.{0} := sInf {γ | α < γ ∧ InL γ}

/-- `logend α` ([W07a] §2): `0` if `α = 0`, and the exponent `α_n` of the last
summand if `α =_CNF ω^{α_1} + ⋯ + ω^{α_n}`.  It is defined here as the largest
`γ` with `ω^γ ∣ α` (left division), which is `α_n`. -/
noncomputable def logend (α : Ordinal.{0}) : Ordinal.{0} :=
  if α = 0 then 0 else sSup {γ | ω ^ γ ∣ α}

/-! ## The reach and the relativized connectivity components -/

/-- `β = lh(α)` ([W07b] Def 3.1): `β` is the largest ordinal with `α ≤₁ β`.
(`lh(α) = ∞`, i.e. `α <₁ ∞`, when there is no such `β`.) -/
def IsLh (α β : Ordinal.{0}) : Prop := le1 α β ∧ ∀ γ, le1 α γ → γ ≤ β

/-- `α` is **`τ`-`≤₁`-minimal** ([W07b] Def 3.2): `α ≥ τ`, and every `β <₁ α`
satisfies `β ≤ τ`. -/
def MinT (τ α : Ordinal.{0}) : Prop := τ ≤ α ∧ ∀ β, le1 β α → β ≠ α → β ≤ τ

/-- The class of the `τ`-`≤₁`-minimal ordinals. -/
def MinSet (τ : Ordinal.{0}) : Set Ordinal.{0} := {α | MinT τ α}

open Classical in
/-- The class enumerated by `kap τ`: the `τ`-`≤₁`-minimal ordinals, followed (if
they form a set) by all ordinals above them.  The extension makes the
enumeration total; on its domain `[0, θ_τ]` it is `κ^τ`. -/
noncomputable def kapSet (τ : Ordinal.{0}) : Set Ordinal.{0} :=
  if BddAbove (MinSet τ) then MinSet τ ∪ Set.Ioi (sSup (MinSet τ)) else MinSet τ

/-- **`κ^τ_ξ`** ([W07b] Def 3.2): the enumeration of the `τ`-`≤₁`-minimal
ordinals (on the domain `[0, θ_τ]`, where `MinT τ (kap τ ξ)`). -/
noncomputable def kap (τ ξ : Ordinal.{0}) : Ordinal.{0} := enumOrd (kapSet τ) ξ

/-- **`θ_τ`** ([W07b] Def 3.2): the supremum of the domain of `κ^τ`. -/
noncomputable def theta (τ : Ordinal.{0}) : Ordinal.{0} := sSup {ξ | MinT τ (kap τ ξ)}

/-- **`λ_τ`** ([W07b] Def 3.2): the largest `λ ≤ θ_τ` with `τ ≤₁ κ^τ_λ`. -/
noncomputable def lam (τ : Ordinal.{0}) : Ordinal.{0} :=
  sSup {ξ | ξ ≤ theta τ ∧ le1 τ (kap τ ξ)}

/-! ## `T¹ ∩ Ω_1` -/

/-- The values below `Ω_1` of the sums of `T¹` (`NFS`, [W07a] Def 3.22). -/
def T1set : Set Ordinal.{0} := {v | ∃ u, NFS u ∧ WP.valS u < Om 1 ∧ WP.valS u = v}

/-- **`T¹ ∩ Ω_1`** ([W07a] Theorem 3.23), as an ordinal: the supremum of
`T1set`, which is an initial segment of the ordinals (`TR.seg`). -/
noncomputable def T1bound : Ordinal.{0} := sSup T1set

/-! ## Patterns -/

/-- `ξ =_ANF ξ_1 + ⋯ + ξ_n` ([W07a] §2): a non-increasing list of additive
principal numbers (its sum is `l.sum`). -/
def ANF (l : List Ordinal.{0}) : Prop := (∀ x ∈ l, Pr x) ∧ l.Pairwise (fun a b => b ≤ a)

/-- **Closed** ([C01] p.20; [CW12] §2): `0 ∈ X`, and whenever
`ξ_1 + ⋯ + ξ_m ∈ X` with `ξ_1 ≥ ⋯ ≥ ξ_m` indecomposable, also every `ξ_i` and
every partial sum `ξ_1 + ⋯ + ξ_i` is in `X`. -/
def ClosedSet (X : Set Ordinal.{0}) : Prop :=
  0 ∈ X ∧ ∀ l, ANF l → l.sum ∈ X → (∀ x ∈ l, x ∈ X) ∧ ∀ i, (l.take i).sum ∈ X

/-- An **isomorphism** of substructures of `R₁` ([C01] §1): a bijection `g` of `X`
onto `Y` that keeps and reflects `≤`, the graph of `+`, and `≤₁`.  (It sends
`0` to `0`, since `0` is the only `a` with `a + a = a`.) -/
def IsoVia (X Y : Set Ordinal.{0}) (g : Ordinal.{0} → Ordinal.{0}) : Prop :=
  Set.BijOn g X Y ∧ StrictMonoOn g X ∧
    (∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a + b = c ↔ g a + g b = g c) ∧
    (∀ a ∈ X, ∀ b ∈ X, le1 a b ↔ le1 (g a) (g b))

/-- `A ≤_pw B` ([C01] p.20; [CW12] p.176): `A` and `B` have the same size and the
`i`-th element of `A` is at most the `i`-th element of `B`; i.e. the order
isomorphism of `A` onto `B` does not decrease. -/
def PwLe (A B : Set Ordinal.{0}) : Prop :=
  ∃ g : Ordinal.{0} → Ordinal.{0}, Set.BijOn g A B ∧ StrictMonoOn g A ∧ ∀ a ∈ A, a ≤ g a

/-- **A covering of `X` onto `Q`** ([C01] Def 5.1; [CW12] p.176): a bijection of
`X` onto `Q` that keeps and reflects `≤` and the graph of `+` (an embedding of the
arithmetic part), and keeps `≤₁`: `a ≤₁ b → h(a) ≤₁ h(b)`.  ([CW12] also asks the
range to be closed; the axioms below state it separately.) -/
def CoveringVia (X Q : Set Ordinal.{0}) (h : Ordinal.{0} → Ordinal.{0}) : Prop :=
  Set.BijOn h X Q ∧ StrictMonoOn h X ∧
    (∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a + b = c ↔ h a + h b = h c) ∧
    (∀ a ∈ X, ∀ b ∈ X, le1 a b → le1 (h a) (h b))

/-- **Isominimal** ([CW12] p.176, which follows [C01] p.25): a finite closed set
of ordinals that is minimal in the pointwise order among the finite sets of
ordinals isomorphic to it. -/
def Isominimal (X : Finset Ordinal.{0}) : Prop :=
  ClosedSet (X : Set Ordinal.{0}) ∧
    ∀ Y : Finset Ordinal.{0}, (∃ g, IsoVia X Y g) → PwLe Y X → Y = X

/-- **The core of `R₁`** ([C01] §1; [CW12] p.176): the union of the isominimal
sets. -/
def CoreR1 : Set Ordinal.{0} := {β | ∃ X : Finset Ordinal.{0}, Isominimal X ∧ β ∈ X}

/-! ## `P_1(α)` -/

/-- **`P_1(α)`** ([CW12] Cor 6.3 (2), `τ = 1`): the closure of `{0, 1, α}` under
additive decomposition, `lh` on `(1, T¹ ∩ Ω_1)`, and bar on the additive principal
elements of `(1, T¹ ∩ Ω_1)`.  ([CW12] §6 writes `lh_τ`, which is `lh` on
`(τ, τ^∞)` ([CW12] p.190; [W07b] Theorem 5.3), and `τ^∞ = T¹ ∩ Ω_1` for `τ = 1`
([W07b] Cor 5.10); bar is `barO`, [CW12] Def 5.1.) -/
inductive InP1 (α : Ordinal.{0}) : Ordinal.{0} → Prop
  | zero : InP1 α 0
  | one : InP1 α 1
  | self : InP1 α α
  | comp {l : List Ordinal.{0}} : ANF l → InP1 α l.sum → ∀ x ∈ l, InP1 α x
  | psum {l : List Ordinal.{0}} : ANF l → InP1 α l.sum → ∀ i, InP1 α (l.take i).sum
  | lh {β δ : Ordinal.{0}} : InP1 α β → 1 < β → β < T1bound → IsLh β δ → InP1 α δ
  | bar {β : Ordinal.{0}} : InP1 α β → Pr β → 1 < β → β < T1bound → InP1 α (barO β)

/-! ## [W07b] Lemma 2.1 -/

/-- **[W07b] Lemma 2.1** (proved in [W06] §3): "`≤₁` is a partial ordering on the
ordinals" — reflexivity. -/
axiom le1_refl (α : Ordinal.{0}) : le1 α α

/-- **[W07b] Lemma 2.1**: "`≤₁` is a partial ordering on the ordinals" —
transitivity. -/
axiom le1_trans {α β γ : Ordinal.{0}} : le1 α β → le1 β γ → le1 α γ

/-- **[W07b] §1, [C01] §1**: `α ≤₁ β` means that `(α; …)` is a substructure of
`(β; …)`, so `α ≤ β`.  (With `le1_refl`, `le1_trans` this makes `≤₁` a partial
order, [W07b] Lemma 2.1.) -/
axiom le1_le {α β : Ordinal.{0}} : le1 α β → α ≤ β

/-- **[W07b] Lemma 2.1 (a)**: "Suppose `α ≤₁ β` for every `β ∈ [α, λ)` where `λ`
is a limit ordinal greater than `α`.  Then `α <₁ λ`." -/
axiom le1_limit {α l : Ordinal.{0}} (hl : Order.IsSuccLimit l) (hα : α < l)
    (h : ∀ β, α ≤ β → β < l → le1 α β) : le1 α l

/-- **[W07b] Lemma 2.1 (b)**: "If `α ≤ β ≤ γ` and `α ≤₁ γ` then `α ≤₁ β`." -/
axiom le1_of_le {α β γ : Ordinal.{0}} (h1 : α ≤ β) (h2 : β ≤ γ) (h : le1 α γ) : le1 α β

/-! ## [W07b] Theorem 2.2 -/

/-- **[W07b] Theorem 2.2** (proved in [W06] §3): "For `α ∈ On` and
`ξ ∈ (0, α]` we have `α ≤₁ α + ξ ⇔ α = ω^{α'}` for some `α'` with
`logend(α') ≥ ξ`." -/
axiom le1_add_iff {α ξ : Ordinal.{0}} (h0 : 0 < ξ) (hξ : ξ ≤ α) :
    le1 α (α + ξ) ↔ ∃ α', α = ω ^ α' ∧ ξ ≤ logend α'

/-- **[W07b] §2, after Theorem 2.2**: "for any ordinal `α`, we have `α ≤₁ β` for
some `β > α` if and only if `α ∈ Lim(P) = L`". -/
axiom exists_le1_gt_iff (α : Ordinal.{0}) : (∃ β, α < β ∧ le1 α β) ↔ InL α

/-! ## [W07b] Lemmas 3.3 and 3.4

[W07b] states and proves them "for the case that `θ_τ ∈ On`", i.e. when the
`τ`-`≤₁`-minimal ordinals form a set; this is the hypothesis `BddAbove`. -/

/-- **[W07b] Lemma 3.3 (b)**: "`κ^τ_0 = τ`, and for every `α ∈ (0, τ^L)` we have
`κ^τ_α = τ + α = lh(κ^τ_α)`" (in particular `α` is in the domain of `κ^τ`). -/
axiom kap_small {τ : Ordinal.{0}} (hb : BddAbove (MinSet τ)) {ξ : Ordinal.{0}} (h0 : 0 < ξ)
    (hξ : ξ < nextL τ) : MinT τ (kap τ ξ) ∧ kap τ ξ = τ + ξ ∧ IsLh (τ + ξ) (τ + ξ)

/-- **[W07b] Lemma 3.3 (c)**: "`κ^τ_{α+β} = lh(κ^τ_α) + β = lh(κ^τ_{α+β})` for all
`α ∈ (0, θ_τ)`, `β ∈ (0, lh(κ^τ_α)^L)`."  (The proof notes that for
`α ∈ (0, θ_τ)`, `κ^τ_α` is defined and not `<₁ ∞`, so `lh(κ^τ_α)` exists; and
`α + β` lies in the domain of `κ^τ`.) -/
axiom kap_add {τ : Ordinal.{0}} (hb : BddAbove (MinSet τ)) {ξ : Ordinal.{0}} (h0 : 0 < ξ)
    (hξ : ξ < theta τ) :
    ∃ δ, IsLh (kap τ ξ) δ ∧ ∀ β, 0 < β → β < nextL δ →
      MinT τ (kap τ (ξ + β)) ∧ kap τ (ξ + β) = δ + β ∧ IsLh (δ + β) (δ + β)

/-- **[W07b] Lemma 3.3 (d)**: "`θ_τ` is a limit ordinal in the domain of
`κ^τ`." -/
axiom kap_theta {τ : Ordinal.{0}} (hb : BddAbove (MinSet τ)) :
    MinT τ (kap τ (theta τ)) ∧ Order.IsSuccLimit (theta τ)

/-- **[W07b] Lemma 3.4 (a)**: "`λ_τ` in Definition 3.2 is an ordinal.  We therefore
have `λ_τ ≤ θ_τ`, `τ ≤₁ κ^τ_{λ_τ}`, `lh(τ) = lh(κ^τ_{λ_τ})`."  (`lh(τ) =
lh(κ^τ_{λ_τ})` includes the case that both are `∞`.) -/
axiom lam_spec {τ : Ordinal.{0}} (hb : BddAbove (MinSet τ)) :
    lam τ ≤ theta τ ∧ le1 τ (kap τ (lam τ)) ∧ ∀ β, IsLh τ β ↔ IsLh (kap τ (lam τ)) β

/-- **[W07b] Lemma 3.4 (b)**: "For `α ∈ (0, θ_τ]` such that `κ^τ_α ∈ P` we have
`κ^τ_α = α`." -/
axiom kap_principal {τ : Ordinal.{0}} (hb : BddAbove (MinSet τ)) {ξ : Ordinal.{0}}
    (h0 : 0 < ξ) (hξ : ξ ≤ theta τ) (hP : Pr (kap τ ξ)) : kap τ ξ = ξ

/-! ## [W07b] Corollary 5.10 -/

/-- **[W07b] Corollary 5.10**, `τ = 1`: "`T¹ ∩ Ω_1 = min{α > τ | α <₁ ∞}`" —
`T¹ ∩ Ω_1 <₁ ∞`. -/
axiom le1_T1bound {γ : Ordinal.{0}} (h : T1bound ≤ γ) : le1 T1bound γ

/-- **[W07b] Corollary 5.10**, `τ = 1`: "`T¹ ∩ Ω_1 = min{α > τ | α <₁ ∞}`" —
no `α ∈ (1, T¹ ∩ Ω_1)` satisfies `α <₁ ∞` (`α ≤₁ β` for all `β ≥ α`). -/
axiom not_lt1_infty {α : Ordinal.{0}} (h1 : 1 < α) (h : α < T1bound) : ∃ β, α ≤ β ∧ ¬ le1 α β

/-! ## The core and `ψ_0(Ω_ω)` -/

/-- **C3 with M13** (`proof/PROOF.md` §1.4): `Core(R₁) = ψ_0(Ω_ω)`.  Sources:
[C01] Theorem 5.12 (the core is the least `κ` with `κ ≤₁ ∞`); [W07b] Cor 5.10
(this is `T¹ ∩ Ω_1`); [W07a] Theorem 3.23, Cor 3.24 and [B86] (both are
`|Π¹₁-CA₀|`); and the outside assumption M13 that the Lean constant
`Ord.psi (Ord.Omega ω) 0` is Buchholz's `ψ_0(Ω_ω)`.  Used only for the reading
of Cor 7.2 (b) as "`Core(R₁) \ {0}`". -/
axiom core_eq_psi : CoreR1 = Set.Iio (Googology.Notation.ExBuchholz.Ord.psi (Googology.Notation.ExBuchholz.Ord.Omega ω) 0)

end Googology.Trans.PSS.Main
