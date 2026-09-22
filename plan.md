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
`Notation/BMS/Any.lean` goes further: expansion ends from **any** array, so
`bmsAll r` — the rule with no standardness condition — terminates as well,
and both `bms r` and `Notation.DBMS.dbms r` sit inside it.

The termination proof itself is
[koteitan/bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) —
labels in `R_r` and Σ-elementary substructures — which this package requires.
`Notation/BMS/Basic.lean` supplies the three fields of `Rewrite` and one
`Subrelation.wf`; `Core` supplies the rest. `Pat.StdR` there is `Rewrite.Rel`
here, written out by hand, so the fit needed no adaptation.

### `Trans/` — one row done

`Trans/BMS/` translates a one-row Bashicu matrix into an extended Buchholz
term and back: `read` and `unread` for the reading, `OneRow.lean` for what
`BM4.expand` does to one row, `Commute.lean` for the commutation with `[ ]`,
`Cut.lean` and `Entries.lean` for the bookkeeping, and `Prim.lean` and
`Bms.lean` for the `StepHom` and the ordinal it gives.

### `Notation/DBMS/` — done

The same rule with the generators whose column `i` holds `i - k` in row `k`.
`dbms_terminates`, `dbms_wf` and `dbmsEval` hold at every number of rows, by
the inclusion into `bmsAll`.

### Other systems — the Y sequence, not started

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

1. **Done: extended Buchholz terms terminate.** `System.lean` carries
   `exbOT`, the expansion system on the countable standard forms, and
   `exbOT_wf` and `exbOT_terminates` are proved outright. The route was
   3.2(b), 3.4, 3.5, `SubBound`, 3.6, 3.3 and the Bachmann property, and all
   of them are now theorems with no hypothesis left. It agrees with the
   computation in `test/ExBuchholzCheck.lean`: every one of the 3835
   countable standard forms of size at most 8, expanded at any of `0`–`4`,
   stays standard and countable and decreases — and the same at size 9, 15890
   forms; and ε₀, ψ_0(Ω+Ω), ψ_0(ψ_1(1)), ψ_0(Ω_2) and ψ_0(ψ_Ω(0)) all run
   down to `0` with every intermediate term standard;
2. **Done for one row: which ordinal a Bashicu matrix names.** `Trans/BMS/`
   carries the chain. `read` splits a row at the entries that are not above
   the current level and sends a block to `ψ_0` of what the block above it
   reads as; `read_expandL` says the reading turns expansion into `[ ]`, up
   to the renumbering `N ↦ N + 1` that the two conventions differ by;
   `entries_expand` matches `BM4.expand` on `BM4.Arr 1` against the rule on
   the entries; and `bmsOrdEval` is the value that comes out, with
   `bms_one_terminates` falling out as well — one row terminating by the
   well-ordering of extended Buchholz's ψ rather than by the labelling proof.
   It is settled both ways: `lt_e0_iff_allNil` says a standard form is below
   `ψ_0(Ω)` exactly when its subscripts are all `0`, and `exists_read` says
   every one of those is read off a matrix. So one row misses nothing below
   `ψ_0(Ω)` and names nothing above it.

   The states of `prim` — matrices whose term is a standard form — are
   exactly the standard one-row matrices: `std_entries_iff`. And
   `primEquivE0` is an `Equiv`: the primitive sequence system and the standard
   forms below `ψ_0(Ω)` are one system written two ways, not two systems that
   simulate each other. `fs_lub` says what `[ ]` is there — the term is the
   least upper bound of `X[0] < X[1] < ⋯`. The way in is
   `exists_le_fs`, that `[ ]` converges below `ψ_0(Ω)`, which makes the
   descent from a generator land on any given matrix. What is left as a check
   rather than a theorem is that `Pat.Std` and the reference implementation
   agree on which matrices those are; they do on all 1024 sequences of length
   5 with entries below 4 (`test/TransCheck.lean`).

   Two rows reach `ψ_0(Ω_ω)`, not the Bachmann–Howard ordinal: the
   correspondence table in
   [yaBMS](https://github.com/koteitan/yaBMS) has `(0,0)(1,1)(2,2) = ψ_0(Ω_2)`,
   which is exactly the Bachmann–Howard ordinal, and `(0,0)(1,1)(2,2)(3,3) =
   ψ_0(Ω_3)`, so the generators climb through every finite subscript and the
   limit is `ψ_0(Ω_ω)`. That also fits the pattern: the `r`-row generators
   start where the `(r-1)`-row system ends — `(0)(1)⋯(n)` gives `ω↑↑n` with
   limit `ε₀ = ψ_0(Ω)`, which is `(0,0)(1,1)`; and `(0,0,0)(1,1,1) =
   ψ_0(Ω_ω)`. So a two-row reading has to use `ψ` at every finite subscript,
   not just `ψ_0` and `ψ_1`. Three rows on are open, so `r = 2` is the next
   target. The first piece is in:
   `BMS/Rows.lean` pins the bad root down for any number of rows, and
   `BMS/TwoRow.lean` reads the two-row column map off — `m₀` is `0` or `1`,
   and at `1` row `0` takes an increment on the columns whose bad-part
   position is a row-`0` ancestor of the bad root. `BMS/Anc.lean` says what
   that ancestor relation is on the entries, and computes it, and
   `BMS/Entries2.lean` puts the two together: `expand2L` is the whole rule
   written on the entries, and `entries2_expand` says it is `BM4.expand`. It
   runs, and agrees with the reference implementation on every two-row matrix
   of length at most `4` with entries below `3` — `46` standard forms, `138`
   expansions, all matching (`test/TransCheck.lean`). `BMS/Pair.lean`
   packages it as a `Rewrite` with its generators, and carries termination
   across. `BMS/EntriesR.lean` does the same for **any** number of rows:
   `parent A k` and `anc A k` at every row, and `expandRL` with
   `entriesR_expand`. So every Bashicu matrix expansion runs, which the array
   form does not. At three rows it agrees with the reference implementation on
   all `72` expansions of the `24` standard matrices of length at most `3`
   with entries below `3`. `BMS/Agree.lean` ties the three rules together —
   `expandRL` at one and two rows is `expandL` and `expand2L` — and packages
   the general one as `bmsL r`, with `bmsL_terminates` and `bmsLStd`.
   `BMS/Same.lean` ties the systems together: `bmsL 0` is `prim` and `bmsL 1`
   is `pairL`, as `Equiv`s.

   So the mechanical side of two rows is finished. What is left is the
   reading, and it is not a mechanical job. A two-row reading has to use `ψ`
   at every finite subscript, and writing one down means reconstructing the
   ordinal analysis of the pair sequences. A correspondence table is not
   enough to do that from: it fixes the map at twenty points and leaves the
   rule to be guessed, and a guessed rule that happens to fit twenty points
   is exactly the failure this repository refuses to commit for the Y
   sequence. The sources checked do not state a rule. The
   [wiki article](https://googology.fandom.com/ja/wiki/%E3%83%9A%E3%82%A2%E6%95%B0%E5%88%97%E6%95%B0)
   derives the correspondence example by example, approximating with the Hardy
   hierarchy, and stops at each named ordinal; it never writes the map down.
   What would make this tractable is a stated definition of the map — not a
   table of its values, and not a derivation of them one at a time. The commutation after that will meet the clause
   of `[ ]` that one row never reaches, the tower;
4. **DBMS done, the Y sequence not.** `Notation/DBMS/` has the expansion
   system: the rule is BM4's, and only the generators differ — column `i`
   holds `i - k` in row `k` rather than `i`. Termination holds at every number
   of rows, and not because of the generators: `Notation.BMS.terminates_any`
   says expansion ends from any array at all, standard or not, because the
   label whose height descends is the `Λ`-chain, which never looks at the
   array. The `Std` hypothesis of the imported `Pat.terminates` is about what
   an array names, not about whether it halts. One row is done, by the same translation as BMS.
   The Y sequence is **not** going in yet, and the reason is worth recording.
   Its official definition is a program, not a set of equations: the
   [wiki article](https://googology.fandom.com/ja/wiki/Y%E6%95%B0%E5%88%97)
   states the expansion function only in outline and points at
   [Naruyoko/YNySequence](https://github.com/Naruyoko/YNySequence) as the
   definition, which is 477 lines of imperative JavaScript over mutable
   arrays. Termination is an open problem, so there would be no theorem at the
   end. And the article records that several third-party formalizations
   produced infinite loops and disagreed with the official expansion of
   `(1,2,4,8,10,8)`, which is exactly the failure a transcription invites.
   Putting a definition here that does not match the program would be worse
   than having none. What it would take: transcribe the expansion function as
   a total function with the loop bounds proved, then calibrate against the
   reference implementation on enough inputs to believe it.

## Where the frontier is

Everything mechanical is done. Expansion is a function that runs, at any
number of rows, and it is `BM4.expand`; the systems are `Rewrite`s with their
generators; the one-row, two-row and general forms are proved to be one
another. One row is settled all the way to the ordinals, in both directions
and as an equivalence.

Two things are left, and neither is a Lean problem.

* **A reading for two rows and up.** It needs a stated definition of the map
  from matrices to ordinals. The sources checked give worked values, not a
  rule, and a rule guessed to fit them is not worth committing.
* **The Y sequence.** Its official definition is a program and its
  termination is open; see item 4.

## Conventions

* every claim is a Lean theorem with no `sorry` and no added axiom;
* `#guard` lines are computations on small cases, not theorems, and are kept
  visibly separate;
* `Core` never imports mathlib; a notation system imports it only when it
  evaluates into the ordinals.
