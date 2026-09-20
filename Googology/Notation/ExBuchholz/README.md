[← Back](../../../README.md) | [English](README.md) | [Japanese](README-ja.md)

# ExBuchholz

Extended Buchholz's psi — Maksudov's extension of Buchholz's collapsing
function, in which the subscript of `ψ` may be any ordinal the system itself
names instead of a numeral at most `ω`.

```
C_v^0(a)     = {b | b < Ω_v}
C_v^(n+1)(a) = {b + c, ψ_u(e) | u, b, c, e ∈ C_v^n(a) ∧ e < a}
C_v(a)       = ⋃_{n<ω} C_v^n(a)
ψ_v(a)       = min {g | g ∉ C_v(a)}
```

`Ω_0 = 1` and `Ω_v` is the initial ordinal of cardinality `ℵ_v` for `v > 0`.
The countable limit is `p0(Λ)`, `Λ` the first omega fixed point.

## The term type

One inductive type with three recursive arguments — no mutual and no nested
induction, so every recursion is structural.

```lean
inductive Term where
  | nil  : Term                       -- 0
  | cons : Term → Term → Term → Term  -- ψ_a(b) + t
```

A term is a finite sum of principal terms `ψ_a(b)`. The subscript is a term,
which is the whole content of the extension.

## Files

| file | contents |
|---|---|
| `Basic.lean` | `Term`, `cmp`, `lt`, `le`, decidability, `cmp_self`, `cmp_swap`, `cmp_eq_iff` |
| `Order.lean` | `lt_irrefl`, `lt_trans`, `lt_trichotomy`, `lt_asymm` |
| `Std.lean` | `G`, `isOT`, `OT`, decidability |
| `WF.lean` | `not_wellFounded_lt`, `cmp_cons_cons'`, `OT_head`, `OT_tail`, `OT_tail_head_le`, `OTLt`, `acc_nil` |

## The order

`cmp` is the dictionary order on the list of principal terms, with a proper
prefix counting as smaller, and principal terms compared by
`(subscript, argument)` lexicographically. That is Buchholz's `(<1)`–`(<3)`
with the subscript generalised from a numeral to a term.

`Order.lean` proves it is a strict linear order. Those three facts are what
`OrdHom.injective` in `Googology.Core.Morphism` consumes, so a translation
into this system is injective as soon as it is order-preserving.

## Standard forms

`ψ_a(b)` is standard when every subterm of `b` that `ψ_a` can still reach lies
strictly below `b`; a sum is standard when its principal terms are weakly
decreasing. The collecting function `G` is Buchholz's, except that the
subscript `c` of an inner `ψ_c(d)` is itself a term and so is collected
alongside `d`.

`isOT` is a `Bool`-valued decision procedure, so `#guard` checks small cases
by computation. Those in `Std.lean` include `ε₀ = ψ_0(Ω)` being standard,
`1 + ω` not being standard because the principal terms increase, and
`ψ_0(ψ_0(Ω))` not being standard because `Ω` is not below the argument.

## Status

| | |
|---|---|
| term type, order, decidability | done |
| strict linear order | done |
| `G`, standard forms, decidability | done |
| the unrestricted order is *not* well founded | done |
| the order as a lexicographic product; standard form inherited by the parts | done |
| well-foundedness of `OTLt` | **not done** — see below |
| fundamental sequences, a `Rewrite` value | **not done** |
| evaluation into the ordinals | **not done** |

Nothing here is `sorry`-free by exception: the files contain no `sorry` and no
`axiom`.

### What is and is not sourced

The `ψ` definition above is Maksudov's, as stated on the Googology Wiki. The
notation system for it is due to p進大好きbot; the `G` and standard-form
clauses here are written out as the natural extension of Buchholz (1986) §2,
and have **not** been calibrated against a reference implementation. The
`#guard` lines are the only evidence so far, and they cover a handful of small
terms. Treat the order as settled and the standard-form predicate as
provisional until a calibration file exists.

## Why standard forms are needed

`WF.lean` proves that the order on *all* terms is not well founded:

```
Ω > ψ_0(Ω) > ψ_0(ψ_0(Ω)) > ψ_0(ψ_0(ψ_0(Ω))) > ⋯
```

descends forever, because `cmp` compares subscripts first and `0 < ψ_0(0)`.
The chain leaves `OT` at its third term. So `not_wellFounded_lt` is not a
defect; it is the reason the standard-form condition exists.

## What remains for well-foundedness

`WellFounded OTLt` splits in two along `cmp_cons_cons'`.

1. **Principal terms.** `∀ a b, OT (ψ_a(b)) → Acc OTLt (ψ_a(b))`. This is the
   collapsing argument and carries all the content. Either Buchholz's
   syntactic route through the sets `W_u` and the Bachmann property — which
   needs fundamental sequences first — or an evaluation into the ordinals with
   well-foundedness pulled back along an `OrdHom`.
2. **Sums.** Granting 1, every standard form is accessible. Structural
   induction reduces this to accessibility for a lexicographic product. The
   nested induction does not close directly, because a term below `cons a b r`
   with a smaller head carries an unrelated tail; `OT_tail_head_le` repairs it,
   and the induction then runs on the number of leading copies of the head.

The header of `WF.lean` states both in full.

## Naming

`ExBuchholz`, not `EBuchholz` or `EBP`. mathlib spells "extended X" with an
`E` prefix — `ENat`, `EReal`, `ENNReal`, `EMetricSpace` — but that reading
breaks in front of a surname: `EBuchholz` is indistinguishable from an initial,
"E. Buchholz". `Ex` says "extended" and nothing else.

## Sources

- Extended Buchholz's function, Googology Wiki.
  https://googology.miraheze.org/wiki/Extended_Buchholz%27s_function
- W. Buchholz, A new system of proof-theoretic ordinal functions,
  Annals of Pure and Applied Logic 32 (1986) 195–207.
