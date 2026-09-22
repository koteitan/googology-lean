[← Back](README.md) | [English](plan.md) | [Japanese](plan-ja.md)

# Plan and current position

This file says what the whole argument looks like and exactly where the work
has got to. It is the one place to look before picking up the next piece.
[spec.md](spec.md) is the companion: what the library is and the rules it is
written by.

## What the library is for

A googological system — BMS, DBMS, the Y sequence — is a rewriting system on
matrices or sequences, and the question about it is whether every expansion
chain terminates. The library answers that question the standard way: by
finding a measure into a well-ordered set that strictly decreases on every
step.

So there are two halves and a bridge.

```
Notation/<System>/     the systems themselves, and the notation systems
Trans/                 translations between them
Core/                  the shared theorems: measure ⟹ termination
```

The whole point is that each half is proved once. A new system supplies its
three fields and one measure; everything else is a theorem it inherits.

## The chain for one system

Reading it backwards is how it gets built.

```
BMS terminates
  ⇐ Sim BMS ExBuchholz                    a translation
  ⇐ WellFounded OTLt                      the target is well founded
  ⇐ every standard principal term is accessible
  ⇐ val is strictly monotone on OT        the notation system is correct
  ⇐ the ordinal facts about ψ
```

`Core` supplies every `⇐` except the last two, which are mathematics about the
particular notation system.

## Where the work is

### `Core/` — complete

| file | contents |
|---|---|
| `WF.lean` | `not_descending`, `not_wellFounded_of_descending` |
| `Rewrite.lean` | `Rewrite`, `Terminates`, `WF`, `terminates_of_wf`, `wf_of_measure`, `terminates_of_measure` |
| `Std.lean` | `Rewrite.Std`, standard forms and generators |
| `Morphism.lean` | `OrdHom`, `Sim`, `StepHom`, `Equiv`, `Eval`, and the transfer theorems |

`Googology/Rank.lean` sits beside it: a well-founded system carries an ordinal
measure of its own, the rank of its one-step relation. That needs mathlib, so
it is not part of `Core`.

No `sorry`, no external dependency. A project that only wants termination can
import this and nothing else.

### `Notation/ExBuchholz/` — the pilot, in progress

| file | state |
|---|---|
| `Basic.lean` | done — terms, `cmp`, decidability |
| `Order.lean` | done — strict linear order, the non-strict order |
| `Std.lean` | done — `G`, `isOT`, `OT`, decidable |
| `WF.lean` | done — `not_wellFounded_lt`, `cmp_cons_cons'`, the `OT` structure lemmas, `OTLt` |
| `Sum.lean` | done — `wellFounded_OTLt` given accessibility of the principal terms |
| `Ord.lean` | done — `ψ` on the ordinals, the cardinality bound, downward closure, additive principality |
| `Eval.lean` | done — `val`, `Lam`, `val_mem_CSet`, the two `ψ` comparison helpers |
| `Mono.lean` | done — the simultaneous induction, `val_lt_val`, `OTLt_wf` |
| `FS.lean` | done except one lemma — `dom`, `fs`, `fs_lt`, `dom_eq_one_or_tw`, `step_lt`, `exb` |

**`ExBuchholz` is finished as a notation system**: `OTLt_wf` says the order on
its standard forms is well founded, with no hypothesis.

### `Notation/BMS/` — done

Bashicu matrices with any number of rows. `bms_terminates r` holds for every
`r`; `r = 1, 2, 3` are the primitive, pair and trio sequences.

The termination proof itself is
[koteitan/bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) —
labels in `R_r` and Σ-elementary substructures — which this package requires.
`Notation/BMS/Basic.lean` supplies the three fields of `Rewrite` and one
`Subrelation.wf`; `Core` supplies the rest. `Pat.StdR` there is `Rewrite.Rel`
here, written out by hand, so the fit needed no adaptation.

### `Trans/` — empty

### Other systems — not started

## Well-foundedness of ExBuchholz — done

```
val is strictly monotone on OT:  x < y → OT x → OT y → val x < val y
```

discharges the hypothesis of `wellFounded_OTLt` through `OrdHom.wf`, and
`OTLt_wf` is the unconditional statement.

Weak monotonicity of `ψ_v` is not enough: `ψ_v(a) = ψ_v(a+1)` does happen,
whenever `a` is not reachable inside `C_v(a)`. Strictness is what the
standard-form condition buys. Four steps:

| # | step | state |
|---|---|---|
| 1 | a small member of the closure lies below `ψ_v(a)` | done (`mem_CSet_of_le`, `lt_psi_of_mem`) |
| 2 | hence `ψ_v(a)` is additively principal | done (`isPrincipal_add_psi`) |
| 3a | the **subscript** is always in its own closure | done (`val_mem_CSet`, via `val_lt_Lam`) |
| 3b | the **argument** is too, which is where `G` is read | done (`val_mem_CSet_arg`) |
| 4 | assemble the comparison of terms into the comparison of values | done (`val_lt_val`) |

### Why 3b and 4 went together

3b needs 4. Reading `G a (cons c d r)` splits on `a ≤ c`; in the other branch
`c < a` holds syntactically and the proof needs `val c < val a`, which is 4.
And 4 needs 3b, for the case where two principal terms share a subscript.

So they are one simultaneous induction. The measure is `size x` for the
monotonicity half and `size a + size t` for the closure half — the left term
alone, because a call at `(z, b)` for `z` collected by `G` from `b` has no
bound in terms of the right one. Every call strictly decreases:

* 4 at `(cons a b t, cons c d u)` calls 4 at `(a,c)`, `(b,d)`, `(t,u)` and at
  `(t, ψ_c(d))`, and 3b at `(a,b)`;
* 3b at `(a, cons c d r)` calls 3b at `(a,c)`, `(a,d)`, `(a,r)` and 4 at
  `(c,a)`.

That is `Mono.lean`.

## Next

1. **The tower invariant of Buchholz's case 4.** `TowerOT`, and now the only
   thing the library assumes: for `ψ_A(B)` in the configuration of case 4,
   every rung `W_i` of the tower is standard and `G_A` sees in it only things
   below `B[W_i]`. Everything else on the route to `exb.WF` is proved —
   3.2(b), 3.4, 3.5, `SubBound`, 3.6 and 3.3 itself. It is checked by
   computation in `test/ExBuchholzCheck.lean`, over all 651 standard case-4
   forms of size at most 8 on five rungs; and so is what it feeds: every one
   of the 3835 countable standard forms of size at most 8, expanded at any of
   `0`–`4`, stays standard and countable and decreases — and the same at size
   9, 15890 forms; every standard form of size at most 6 stays standard when
   expanded at any standard index of size at most 3; and ε₀, ψ_0(Ω+Ω),
   ψ_0(ψ_1(1)), ψ_0(Ω_2) and ψ_0(ψ_Ω(0)) all run down to `0` with every
   intermediate term standard;
2. add `Trans/BMS/ExBuchholz`. BMS termination no longer needs it, so what the
   translation buys is the **value**: which ordinal a matrix names;
4. add DBMS and the Y sequence.

## Conventions

* every claim is a Lean theorem with no `sorry` and no added axiom;
* `#guard` lines are computations on small cases, not theorems, and are kept
  visibly separate;
* `Core` never imports mathlib; a notation system imports it only when it
  evaluates into the ordinals.
