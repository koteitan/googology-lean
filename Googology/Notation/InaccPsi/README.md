[← Back](../README.md) | [English](README.md) | [Japanese](README-ja.md)

# InaccPsi: Buchholz's ψ over the first ω weakly inaccessible cardinals

This directory defines an ordinal collapsing function over ω weakly inaccessible
cardinals `I_0 < I_1 < ⋯` and their supremum `I_ω`, and a notation system for it.

- **Base.** The collapsing function over one weakly inaccessible cardinal `I` is
  Definition 4.2 of W. Buchholz, *A simplified version of local predicativity*
  (in P. Aczel, H. Simmons, S. S. Wainer (eds.), *Proof Theory*, Cambridge University
  Press 1992, 115–147). W. Pohlers, *Subsystems of set theory and second order number
  theory* (Handbook of Proof Theory, Elsevier 1998, Chapter IV), §3.4.4, presents the
  same definition together with the facts (155)–(179) and a sketch of the term system.
- **Extension.** The extension to `ω` weakly inaccessible cardinals is new here (koteitan
  and Claude). G. Wilken, *A glimpse of Σ₃-elementarity* (2020), p. 421, claims without
  a definition that "the Skolem-hull notation system derived from the first ω-many
  weakly inaccessible cardinals" covers the core of `R₂⁺`. The system here is one way to
  make that phrase precise; nothing says that it is the system Wilken had in mind.

## 1. Hypotheses and notation

- `Ω_0 = 0` and `Ω_ξ = ω_ξ` (the ordinal of `ℵ_ξ`) for `ξ ≥ 1`. So `ξ ↦ Ω_ξ` enumerates
  `{0}` and the uncountable cardinals. It is strictly increasing and continuous.
- `φ(ξ, η)` is the binary Veblen function, `φ(0, η) = ω^η`. `1 = φ(0, 0)`.
- `SC` is the class of strongly critical ordinals: `γ > 0` with `φ(ξ, η) < γ` for all
  `ξ, η < γ`. Every uncountable cardinal is in `SC`.
- **Hypothesis.** `I : ℕ → Ord` is strictly increasing, and every `I_n` is an uncountable
  regular cardinal with `Ω_{I_n} = I_n` (a weakly inaccessible cardinal). We put
  `I_ω = sup_n I_n`; then also `Ω_{I_ω} = I_ω`. We do **not** assume that the `I_n` are
  the first `ω` weakly inaccessible cardinals: nothing below needs it.
- `R = {I_n | n < ω} ∪ {Ω_{s+1} | s ∈ Ord}`. Every member of `R` is an uncountable regular
  cardinal. These are the subscripts at which ψ collapses.

## 2. The definition

By recursion on `α`, define sets `Cl(α, β)` and ordinals `ψ_κ(α)` (`κ ∈ R`):

- `Cl(α, β)` is the least set `X` such that
  - `β ⊆ X`, `0 ∈ X`, `I_n ∈ X` for every `n < ω`, and `I_ω ∈ X`;
  - `ξ, η ∈ X` ⇒ `ξ + η ∈ X`, `φ(ξ, η) ∈ X`, `Ω_ξ ∈ X`;
  - `ξ, π ∈ X`, `ξ < α`, `π ∈ R` ⇒ `ψ_π(ξ) ∈ X`.
- `ψ_κ(α) = min {β | κ ∈ Cl(α, β) ∧ Cl(α, β) ∩ κ ⊆ β}`.

For one inaccessible `I` (all `I_n` equal to `I`, no `I_ω`) this is Buchholz's
definition. The only changes are the constants `I_n`, `I_ω` and the subscript class `R`.

## 3. Facts about ψ

`κ` ranges over `R`. The numbers in brackets are Pohlers's.

**F1 (monotone).** `α ≤ α'` and `β ≤ β'` ⇒ `Cl(α, β) ⊆ Cl(α', β')`. [155]

**F2 (size).** `|Cl(α, β)| ≤ max(|β|, ℵ_0)`. [157] — The set is the union of `ω`
stages; each stage applies finitely many finitary operations to the previous one and
adds `ω + 1` constants.

**F3.** `κ ∈ Cl(α, β)` for some `β < κ`. — If `κ = I_n` it is a constant. If
`κ = Ω_{s+1}` take `β = s + 1 < κ`: then `s ∈ Cl`, `s + 1 = s + φ(0,0) ∈ Cl`,
`Ω_{s+1} ∈ Cl`.

**F4 (collapsing).** `ψ_κ(α) < κ`, `κ ∈ Cl(α, ψ_κ(α))`, `Cl(α, ψ_κ(α)) ∩ κ ⊆ ψ_κ(α)`,
and `ψ_κ(α) ∉ Cl(α, ψ_κ(α))`. [160] — Start from the `β₀ < κ` of F3 and put
`β_{n+1} = sup(Cl(α, β_n) ∩ κ)`. By F2 and the regularity of `κ`, `β_{n+1} < κ`. Then
`β = sup_n β_n < κ` (as `cf κ > ω`) satisfies the condition, since `Cl(α, β)` is the
union of the `Cl(α, β_n)`. The last claim: `ψ_κ(α) ∈ Cl ∩ κ ⊆ ψ_κ(α)` is impossible.

**F5.** `α₀ < α` and `α₀ ∈ Cl(α, ψ_κ(α))` ⇒ `ψ_κ(α₀) < ψ_κ(α)`. [161] — `ψ_κ(α₀)` is in
`Cl(α, ψ_κ(α)) ∩ κ ⊆ ψ_κ(α)`, and it is not `ψ_κ(α)` by F4.

**F6.** `ψ_κ(α) ∈ SC`. [163] — `0 ∈ Cl ∩ κ` gives `ψ_κ(α) > 0`; for `ξ, η < ψ_κ(α)`,
`φ(ξ, η) ∈ Cl ∩ κ` because `κ ∈ SC`.

**F7 (cardinals).** `Ω_σ ∈ Cl(α, β)` ⇒ `σ ∈ Cl(α, β)`. [164] — By induction on the
generation of `x ∈ Cl(α, β)`: if `x = Ω_σ` then `σ ∈ Cl(α, β)`.
- `x < β`: `σ ≤ Ω_σ < β`.
- `x ∈ {0, I_n, I_ω}`: `Ω` is injective and these are fixed points of `Ω`, so `σ = x`.
- `x = ξ + η`: `Ω_σ` is `0` or additively principal, so `η = Ω_σ` or `η = 0 ∧ ξ = Ω_σ`.
- `x = φ(ξ, η)`: `Ω_σ ∈ SC` (or `σ = 0`), so `ξ = Ω_σ` or `η = Ω_σ`.
- `x = Ω_ξ`: `ξ = σ`.
- `x = ψ_π(ξ)`: if `σ = Ω_σ` then `σ = x ∈ Cl`. Otherwise `σ < Ω_σ = ψ_π(ξ) =: γ`, so
  `σ ∈ γ ⊆ Cl(ξ, γ)`, hence `Ω_σ ∈ Cl(ξ, γ) ∩ π ⊆ γ`, i.e. `γ < γ`. Impossible.

**F8 (successors).** `s + 1 ∈ Cl(α, β)` ⇒ `s ∈ Cl(α, β)`. — Same induction:
`ξ + η = s + 1` with `η ≠ 0` forces `η = t + 1`, `s = ξ + t`; `φ`-values that are
successors equal `1`; `Ω`-values and `ψ`-values are `0` or limits (F6).

**F9 (successor subscripts).** For `κ = Ω_{s+1}`: `Ω_s < ψ_κ(α) < Ω_{s+1}`, so `ψ_κ(α)`
is not a cardinal (for `s = 0`: `ψ_κ(α)` is countable). [167] — `κ ∈ Cl(α, ψ_κ(α))`
(F4), so `s + 1` and `s` are in it (F7, F8). As `s < κ`, `s ∈ Cl ∩ κ`, so `Ω_s ∈ Cl ∩ κ
⊆ ψ_κ(α)`.

**F10 (inaccessible subscripts).** For `κ = I_n`: `Ω_{ψ_κ(α)} = ψ_κ(α)`, and
`I_{n-1} < ψ_κ(α) < I_n` when `n ≥ 1` (`Ω_1 < ψ_κ(α)` when `n = 0`). [170] — `I_{n-1}`
(resp. `Ω_1`) is in `Cl ∩ κ`. For the fixed point: let `γ = ψ_κ(α)` and
`Ω_σ ≤ γ < Ω_{σ+1}`. `I_n` is a limit cardinal, so `Ω_{σ+1} < I_n`, hence
`Ω_{σ+1} ∉ Cl(α, γ)` (else `Ω_{σ+1} < γ`), hence `σ ∉ Cl(α, γ)`, hence `σ ≥ γ`. So
`Ω_σ ≥ σ ≥ γ ≥ Ω_σ`: `γ = σ = Ω_σ`.

**F11 (monotone in the argument).** `ξ ≤ α` ⇒ `ψ_κ(ξ) ≤ ψ_κ(α)` and
`Cl(ξ, ψ_κ(ξ)) ⊆ Cl(α, ψ_κ(α))`. [168] — `κ ∈ Cl(ξ, ψ_κ(α))`: for `κ = I_n` it is a
constant; for `κ = Ω_{s+1}`, `s < Ω_s < ψ_κ(α)` (F9). And
`Cl(ξ, ψ_κ(α)) ∩ κ ⊆ Cl(α, ψ_κ(α)) ∩ κ ⊆ ψ_κ(α)`.

**F12 (strictly monotone at normal arguments).** If `α₀ < α` and
`α₀ ∈ Cl(α₀, ψ_κ(α₀))`, then `ψ_κ(α₀) < ψ_κ(α)`. — By F11 `α₀ ∈ Cl(α, ψ_κ(α))`; apply F5.

## 4. The term system

### Terms

```
t ::= 0 | I_n | I_ω | t + t | φ(t, t) | Ω_t | ψ^S_s(t) | ψ^I_n(t)       (n ∈ ℕ)
```

`ψ^S_s(a)` denotes `ψ_{Ω_{s+1}}(a)` and `ψ^I_n(a)` denotes `ψ_{I_n}(a)`. The value
`|t|` of a term is the obvious ordinal. Subscripts are not general terms: a subscript in
`R` is either a successor cardinal, given by `s`, or an `I_n`, given by `n`.

### Kinds

- **SC terms**: `I_n`, `I_ω`, `Ω_a`, `ψ^S_s(a)`, `ψ^I_n(a)`.
- **principal terms**: SC terms and `φ(a, b)`.
- **fixed-point terms** `F`: `I_n`, `I_ω`, `ψ^I_n(a)` (values `x` with `Ω_x = x`).
- **cardinal terms** `K`: `F` and `Ω_a`.

### Normal forms `NF`

- `0`, `I_n`, `I_ω` are in `NF`.
- `a + b` is in `NF` iff `a` is a principal `NF` term, `b ≠ 0` is in `NF`, and the first
  summand of `b` is `≤ a`.
- `φ(a, b)` is in `NF` iff `a, b ∈ NF`, `a < φ(a, b)` and `b < φ(a, b)`.
- `Ω_a` is in `NF` iff `a ∈ NF`, `a ≠ 0` and `a ∉ F`.
- `ψ^S_s(a)` is in `NF` iff `s, a ∈ NF` and `K_{c}(a) < a`, where `c = card(Ω_s)` below.
- `ψ^I_n(a)` is in `NF` iff `a ∈ NF` and `K_{ψ^I_n(a)}(a) < a`.

Here `<` is the comparison below, and `K_μ(a) < a` means that every member of the
finite set `K_μ(a)` is `< a`.

### The set `K_μ(a)`

For a term `μ`, `K_μ(a)` is the finite set of arguments of the collapses in `a` that are
not below `μ` (Pohlers's Definition 3.4.4.2):

- `K_μ(0) = K_μ(I_n) = K_μ(I_ω) = ∅`;
- `K_μ(a + b) = K_μ(a) ∪ K_μ(b)`, `K_μ(φ(a, b)) = K_μ(a) ∪ K_μ(b)`;
- for an SC term `a < μ`: `K_μ(a) = ∅`;
- for `a ≥ μ`: `K_μ(Ω_b) = K_μ(b)`, `K_μ(ψ^S_s(b)) = {b} ∪ K_μ(s) ∪ K_μ(b)`,
  `K_μ(ψ^I_n(b)) = {b} ∪ K_μ(b)`.

**Soundness (the easy half of Pohlers's (178)).** If `a ∈ NF` and every member of
`K_μ(a)` is `< α`, then `|a| ∈ Cl(α, |μ|)`. — Induction on `a`; each clause of `K`
matches a clause of `Cl`. The other half is not needed for the well-ordering.

It follows that `ψ^S_s(a) ∈ NF` gives `|a| ∈ Cl(|a|, Ω_{|s|}) ⊆ Cl(|a|, ψ_{Ω_{|s|+1}}(|a|))`
(F9), and `ψ^I_n(a) ∈ NF` gives `|a| ∈ Cl(|a|, ψ_{I_n}(|a|))`. So F12 applies to the
arguments of normal collapses.

### The cardinal part `card(t)`

`card(t)` is a cardinal term or `0`, with `|card(t)|` the cardinality-level of `|t|`
(the largest `Ω_σ ≤ |t|`, or `0`):

- `card(0) = 0`; `card(a + b) = card(a)`; `card(φ(a, b)) = max(card(a), card(b))`;
- `card(t) = t` for `t ∈ K`;
- `card(ψ^S_s(a)) = card(Ω_s)`, where `card(Ω_s)` means `0` if `s = 0`, `s` if `s ∈ F`,
  and `Ω_s` otherwise.

### Comparison

`a < b` on terms is defined by recursion on `size(a) + size(b)`:

1. `0 < b` iff `b ≠ 0`; `a < 0` never.
2. Sums (a principal term is a sum with one summand): compare the lists of summands
   lexicographically, a proper prefix being smaller.
3. `φ(a, b)` vs `φ(c, d)`: `a < c ∧ b < φ(c, d)`, or `a = c ∧ b < d`, or
   `c < a ∧ φ(a, b) < d`.
4. `φ(a, b)` vs an SC term `s` (for strongly critical `γ`: `φ(ξ, γ) = γ` when `ξ < γ`, and
   `φ(γ, 0) = γ`):
   - if `a < s`: compare `b` with `s`;
   - if `a = s`: `φ(a, b) = s` when `b = 0`, and `φ(a, b) > s` otherwise;
   - if `a > s`: `φ(a, b) > s`.

   These are identities of ordinals, so they hold for every `φ(a, b)`, normal or not. The
   `NF` conditions `a < φ(a, b)` and `b < φ(a, b)` exclude `φ(s, 0)` and `φ(a, s)` with
   `a < s`.
5. SC terms among themselves:
   - `Ω_a < Ω_c` iff `a < c`; for `f ∈ F`: `Ω_a < f` iff `a < f`, and `f < Ω_a` iff
     `f < a`;
   - `I_n < I_m` iff `n < m`; `I_n < I_ω`; `ψ^I_n(a) < I_m` iff `n ≤ m`;
     `I_m < ψ^I_n(a)` iff `m < n`; `ψ^I_n(a) < I_ω`;
     `ψ^I_n(a) < ψ^I_m(b)` iff `n < m ∨ (n = m ∧ a < b)`;
   - `ψ^S_s(a) < ψ^S_t(b)` iff `s < t ∨ (s = t ∧ a < b)`;
   - for a cardinal term `k`: `ψ^S_s(a) < k` iff `card(Ω_s) < k`, and `k < ψ^S_s(a)` iff
     `k ≤ card(Ω_s)`.

### Main theorem

On `NF` terms, `a < b ⟺ |a| < |b|`. Hence `|·|` is injective on `NF`, and `(NF, <)` is
a strict well-order, isomorphic to a set of ordinals. Proved in `Correct.lean` for every
`InaccSeq`: `Term.cmp_eq_compare`, `Term.eq_of_val_eq`, `Term.isWellOrder_cmp`.

The facts used, by clause:
- 3, 4: the Veblen function (Mathlib) and F6;
- 5, first line: `Ω` strictly increasing, fixed points;
- 5, second line: F10;
- 5, third and fourth lines: F9 and F12 (through the soundness of `K`).

## 5. What is not done here

- **Completeness.** Every ordinal of `Cl(ε_{I_ω+1}, 0)` is the value of an `NF` term
  (Pohlers's (174)–(177) and the other half of (178)). Not needed for the well-order.
- **Recursive regular ordinals.** As in Buchholz and Pohlers, the cardinals are true
  cardinals. Replacing them by recursively regular ordinals is not attempted.
- **Wilken's claim.** Whether the countable part of the system covers `Core(R₂⁺)` is
  open.

## 6. Files

| file | contents |
|---|---|
| `Hyp.lean` | `Ω`, the hypothesis structure `InaccSeq`, `R`, basic facts on cardinals and `SC` |
| `Ord.lean` | `Cl`, `ψ`, F1–F4 |
| `Facts.lean` | F5–F12 |
| `Term.lean` | terms, values, kinds, `card`, `K`, the comparison, `NF` |
| `Correct.lean` | soundness of `K`, the main theorem |
