[← Back](README.md) | [English](memo.md) | [Japanese](memo-ja.md)

# Memo: the argument and where the work has got to

What is left to do is in [plan.md](plan.md); this file keeps the reasoning and the history.

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
measure of its own, the rank of its one-step relation, and `StepHom.rank_map`
says an embedding onto the steps keeps it. `Trans.BMS.rank_prim_eq_val` says
that at one row it is the value of the term. That needs mathlib, so it is not
part of `Core`.

No `sorry`, no external dependency. A project that only wants termination can
import this and nothing else.

### `Notation/ExBuchholz/` — the pilot, done

| file | state |
|---|---|
| `Basic.lean` | done — terms, `cmp`, decidability |
| `Order.lean` | done — strict linear order, the non-strict order |
| `Std.lean` | done — `G`, `isOT`, `OT`, decidable |
| `WF.lean` | done — `not_wellFounded_lt`, `cmp_cons_cons'`, the `OT` structure lemmas, `OTLt` |
| `Sum.lean` | done — `wellFounded_OTLt` given accessibility of the principal terms |
| `Ord.lean` | done — `ψ` on the ordinals, the cardinality bound, downward closure, additive principality |
| `Opow.lean` | done — the closed forms of `ψ_0`: `ω^a` below `ε₀`, `ε₀·ω^a` below `ε₁`, and the first two steps of a normal form theorem |
| `Level.lean` | done — the same at every subscript: `ψ_v(a) ≤ Ω_v·ω^a`, with equality below the first fixed point, and `ψ_v(Ω_{v+1})` is that fixed point |
| `Eps.lean` | done — `ψ_0(Ω·(n+1)) = ε_n` at every finite `n`, by one induction, and `ψ_0(Ω·ω) = ε_ω` with `ψ_1(1) = Ω·ω` |
| `Ladder.lean` | done — the same at every `γ < ζ₀` with the ε function, by division by `Ω` |
| `LadderV.lean` | done — the same at every subscript: `ψ_v(Ω_{v+1}·(1+γ)) = ε^v_γ` below `ζ^v` |
| `Eval.lean` | done — `val`, `Lam`, `val_mem_CSet`, the two `ψ` comparison helpers |
| `Mono.lean` | done — the simultaneous induction, `val_lt_val`, `OTLt_wf` |
| `FS.lean` | done — `dom`, `fs`, `fs_lt`, `dom_eq_one_or_tw`, `step_lt`, `exb` |
| `Closure.lean` | done — Buchholz 3.4, 3.5, 3.6, the Bachmann property, and 3.3 from it: `bachmann`, `OTFS_thm`, `Trian_fs_thm` |
| `System.lean` | done — `exbOT` on the countable standard forms, `exbOT_wf`, `exbOT_terminates` |
| `NF.lean` | done — the ordinal side of the normal form theorem: `M`, `M_mem_of_comp`, `M_psi_mem`, `arg_mem_of_psi_mem` |
| `Onto.lean` | done — `val` is onto `C_0(Λ)`: `Vals_eq`, `valEquiv`, `existsUnique_OT_of_lt_psi_Lam` |

**`ExBuchholz` is finished**: `OTLt_wf` says the order on its standard forms
is well founded with no hypothesis, and `exbOT_terminates` says the expansion
system on the countable ones ends, also with no hypothesis. `Vals_eq` says
`val` is onto `C_0(Λ)`, so with `val_inj_of_OT` it is the order isomorphism
the source states, and every ordinal below `ψ_0(Λ)` has exactly one standard
form.

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

### `Trans/` — one row done, the hierarchy, and the first two-row ordinals

`Trans/BMS/` translates a one-row Bashicu matrix into an extended Buchholz
term and back: `read` and `unread` for the reading, `OneRow.lean` for what
`BM4.expand` does to one row, `Commute.lean` for the commutation with `[ ]`,
`Cut.lean` and `Entries.lean` for the bookkeeping, and `Prim.lean` and
`Bms.lean` for the `StepHom` and the ordinal it gives.

It also relates the systems to each other. `EntriesR.lean` writes the rule on
the entries at every number of rows, `Agree.lean` says the one-row, two-row
and general rules are one rule, `Same.lean` says the general system at one and
two rows **is** the primitive and pair sequence system, and `ZeroRow.lean`
says a row of zeros underneath changes neither the rule nor the ordinal, so
`bmsL r` sits inside `bmsL s` whenever `r ≤ s`.

`Eps0.lean` closes one row as ordinals — it names exactly those below `ε₀` —
and carries `val`'s surjectivity up to `ε₁`, `EpsN.lean` carries it to every
`ε_n`, `Arg.lean` and `EpsBig.lean` carry it to `ε_{ε₀}` and `Zeta.lean` to `ζ₀`,
`RankVal.lean` says the rank of the system is that same ordinal and computes
the first two-row ranks, and `Append.lean` says expansion never reaches back
across a block, which makes the rank additive over blocks.

### `Notation/DBMS/` — done

The same rule with the generators whose column `i` holds `i - k` in row `k`.
`dbms_terminates`, `dbms_wf` and `dbmsEval` hold at every number of rows, by
the inclusion into `bmsAll`.

### `Notation/Y/` — done

The official expansion, transcribed from the program, with `ySys` and its
seeds; see item 4. Termination is a theorem here: `WellFounded.lean`, from
the proof ported into `WellOrder/`.

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
   `ψ_0(Ω)` and names nothing above it. And as ordinals, not only as terms:
   `Ord.psi_Omega_one` says `ψ_0(Ω)` **is** `ε₀`, `exists_OT_of_lt_eps0` says
   `val` is onto the ordinals below it — Cantor normal form, with
   `Ord.psi_zero_eq_opow` for `ψ_0(a) = ω^a` there — and so
   `exists_matrix_of_lt_eps0` with `val_read_lt_eps0` says the one-row
   matrices name the ordinals below `ε₀` and no others. `rank_prim_eq_val`
   closes the loop: the rank of the expansion relation, which needs no
   notation system to define, **is** that value. So calling
   `Rewrite.rankEval` the ordinal a matrix names is justified where both are
   defined. One row of DBMS is the same system and gets the same two
   statements. And it gives the first two-row ordinal: `rank_pairGen` says
   the generator `(0,0)(1,1)` has rank `ε₀`, because it expands into one-row
   matrices with a zero row underneath and `BMS/Embed.lean` carries their
   ordinals across. So the pair sequence system starts where the primitive
   sequence system ends — with no two-row reading, which there still is
   not. `rank_gen_eq_iSup` is the same at every number of rows: the
   `r + 2`-row generator's rank is the limit of the `r + 1`-row generators'
   ranks. `BMS/Append.lean` adds the additive structure: expansion never
   reaches back across a column whose row-`0` entry is `0`, so the rank is
   additive over those blocks — `rank_appendState` — and `n` copies of a block
   have `n` times its rank. The other half is `expandRL_of_m0_zero`: with
   `m₀ = 0` the expansion is a fixed part and a block repeated `N + 1` times,
   so `rank_mul_omega0` multiplies that block's rank by `ω`. Three two-row
   values come out: `(0,0)(1,0)` is `ω`, as the zero row demands,
   `(0,0)(1,1)(1,0)` is `ε₀·ω`, and `(0,0)(1,1)(0,0)(1,0)` is `ε₀ + ω`. `rank_split_mul_omega0`
   packages the two so that a matrix of that shape costs three lines, both
   hypotheses being `rfl`. Every rank they produce lies in the closure of
   `{1, ε₀}` under `+` and `·ω` — that is what the three rules add up to, and
   the matrices above are the instances proved, not a claim that the whole
   closure is realised. One instance is a family rather than a single
   matrix: `rank_MkState` says `(0,0)(1,1)(1,0)ᵏ` has rank `ε₀·ω^k` for every
   `k`, so the two-row system's ordinal is at least `ε₀·ω^ω`. That is far
   below what the sources put it at, and it is what the rank reaches without
   a reading. What they do not reach is the rank of the later
   generators `(0,0)(1,1)(2,2)` and beyond, whose expansions are neither
   zero-row matrices nor block repetitions.

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
   is exactly the failure the Y sequence was kept out for until its program
   was transcribed. The sources checked do not state a rule. The
   [wiki article](https://googology.fandom.com/ja/wiki/%E3%83%9A%E3%82%A2%E6%95%B0%E5%88%97%E6%95%B0)
   derives the correspondence example by example, approximating with the Hardy
   hierarchy, and stops at each named ordinal; it never writes the map down.
   What would make this tractable is a stated definition of the map — not a
   table of its values, and not a derivation of them one at a time. The commutation after that will meet the clause
   of `[ ]` that one row never reaches, the tower;
4. **DBMS done, the Y sequence defined.** `Notation/DBMS/` has the expansion
   system: the rule is BM4's, and only the generators differ — column `i`
   holds `i - k` in row `k` rather than `i`. Termination holds at every number
   of rows, and not because of the generators: `Notation.BMS.terminates_any`
   says expansion ends from any array at all, standard or not, because the
   label whose height descends is the `Λ`-chain, which never looks at the
   array. The `Std` hypothesis of the imported `Pat.terminates` is about what
   an array names, not about whether it halts. One row is done, by the same translation as BMS.
   `Notation/Y/` has the Y sequence (1-Y). Its official definition is a
   program, `script.js` of
   [Naruyoko/YNySequence](https://github.com/Naruyoko/YNySequence), and
   `Yukito.lean` is koteitan's statement-by-statement transcription of it, from
   [koteitan/1y-expand-equiv](https://github.com/koteitan/1y-expand-equiv).
   `ySys` is the system on the sequences reachable from `(1, h+1)`, and
   `test/YCheck.lean` compares `expand` with the program's own output on 213
   cases, `(1,2,4,8,10,8)` among them — all agree. Termination is now a
   theorem here (2026-09-23 below). It was first a citation: Phyrion's
   [1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean)
   proves it for an independently defined expansion, and `expand_eq` in
   1y-expand-equiv proves that expansion equal to this one, both in Lean
   4.33.1. Importing Phyrion's project would have meant moving this library
   and its dependencies to Lean 4.33.1 and pulling in a BMS snapshot that
   carries no license. [koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por)
   removed that snapshot, and its files and those of 1y-expand-equiv were
   ported down to Lean 4.30.0 instead.

## Where the frontier is

Everything mechanical is done. Expansion is a function that runs, at any
number of rows, and it is `BM4.expand`; the systems are `Rewrite`s with their
generators; the one-row, two-row and general forms are proved to be one
another. One row is settled all the way to the ordinals, in both directions
and as an equivalence.

The hierarchy is settled too: `BMS/ZeroRow.lean` says a row of zeros
underneath changes nothing at every number of rows, and the generator
`(0,…,0)(1,…,1)` with `r + 2` rows expands at `N` to the generators with
`r + 1` rows and that zero row already in place, so `bmsL r` sits inside
`bmsL (r + 1)`, and inside `bmsL s` for every `s ≥ r`, the same for all
matrices. `rank_zeroRow` adds that the ordinal is the same on both sides, so
the extra row names nothing new.

One row is now settled as ordinals too. `val` is onto the ordinals below
`ε₀` — `Trans.BMS.exists_OT_of_lt_eps0`, by Cantor normal form, with
`Ord.psi_zero_eq_opow` for `ψ_0(a) = ω^a` there and `Ord.psi_Omega_one` for
`ψ_0(Ω) = ε₀` — so `exists_matrix_of_lt_eps0` and `val_read_lt_eps0` say the
one-row matrices name the ordinals below `ε₀` and no others.

The notation system itself is settled as well: **`val` is an order
isomorphism from the standard forms onto `C_0(Λ)`**, which is what the source
states. `Notation.ExBuchholz.Term.Vals_eq` is the onto half and `valEquiv`
packages it with the injective half, so every ordinal below `ψ_0(Λ)` is the
value of exactly one standard form (`existsUnique_OT_of_lt_psi_Lam`), and the
countable standard forms name exactly those (`val_lt_psi_Lam_iff`). In the
term order the standard forms below a countable `X` are the ordinals below
`val X` (`belowEquiv`): the order type below `X` is the ordinal `X` names. That
is the form a reading of another system can use without a commutation with
`[ ]`: match its standard states to these terms in order, and the order type
below a state is the value of its term.

The step that had blocked it was the collapse clause. The standard form of
`ψ_u(e)` needs an argument that lies in its own closure, and that argument is
in general larger than `e` — `ψ_0(ε₀) = ψ_0(Ω)`, and the standard form uses
`Ω`. `Notation/ExBuchholz/NF.lean` moves the argument up to `M(e)`, the least
member of `C_u(e)` at or above `e`, which changes neither the closure nor the
value (`Ord.psi_M_eq`), and shows that `M` does not leave any set closed under
`+`, `Ω_·` and the collapses below `e`. `M` of an ordinal is read off `M` of
its Cantor-normal-form summands (`Ord.M_mem_of_comp`), and `M` of a summand
`ψ_t(η)` is `ψ_t(M(η))`, `Ω_{t+1}` or `Ω_{M(t)}` (`Ord.M_psi_mem`). With the
set of values in that role, an induction on `e` gives the term; with `C_v(β)`
in it, the same argument gives Buchholz's reading of the closure through `G`
(`Term.G_lt_of_mem_CSet`), which turns "`M(e)` is in its own closure" into the
standard-form condition.

The constructions in `Trans/BMS/` that reach `ε₁`, `ε_ω`, `ε_{ε₀}` and `ζ₀`
came first and stay: they build the terms by hand and say which term names
which ordinal, which the general theorem does not.

What is left is one problem, and it is not a Lean problem.

* **A reading for two rows and up.** It needs a stated definition of the map
  from matrices to ordinals, and there is one for three rows:
  [koteitan/trio](https://github.com/koteitan/trio) writes down the map from
  `ψ_0(Ω_α)` to the standard forms of the trio sequence system — the `z < 2`
  fragment of the three-row matrices — on its
  [algorithm page](https://github.com/koteitan/trio/blob/main/ebp2bms/algorithm/1/README-en.md),
  with the values in its
  [table](https://github.com/koteitan/trio/blob/main/ebp2bms/sheet/1/README-en.md).
  `Trans/BMS/Trio.lean` transcribes the `α < ε₀` half of it as
  `omegaIndexMatrix` and calibrates it against twenty rows of that table,
  including `ψ_0(Ω_1) = ε₀` as `(0,0)(1,1)` and `ψ_0(Ω_2)` as
  `(0,0)(1,1)(2,2)`, which is where the yaBMS table puts the Bachmann–Howard
  ordinal as well. That is a transcription and `#guard`s, not a theorem, except for the
  shape of the output: `WF3_omegaIndexMatrix` and `WF3_trioMatrix` prove every
  column is three rows deep with `z < 2`. What is not proved is that the map
  lands in standard forms, that it is monotone, and that it turns `[ ]` into
  the fundamental sequence — the three things the one-row case has. The first two were checked outside Lean against the
  reference implementation on those twenty matrices: all twenty are standard
  forms, and each compares `<` with the next as `α` increases. The third does
  **not** hold on the nose: `BM4.expand` at three rows and the canonical
  fundamental sequence of the notation system are different assignments.
  `ψ_0(Ω_{ω^ω})` is the smallest case seen — the matrix expands to the one
  for `ψ_0(Ω_{ω³})` where `X[1]` of the term is `ψ_0(Ω_ω)` — so what a
  commutation theorem would have to compare is cofinality, not equality. The `ε₀ ≤ α < Λ` half of the algorithm, where the
  embedding of the exponent becomes the whole ordinal notation rather than the
  primitive sequence, is not transcribed yet.

  Without a reading, the rank
  reaches single values without it — `rank_pairGen`, `rank_gen_eq_iSup`,
  `rank_succAll`, `rank_omegaAll` — but only where the expansions are already understood:
  the generators, the columns that have no parent, and the block repetitions
  that `BMS/Append.lean` reaches. `(0,0)(1,1)(2,1)` is none of those — `m₀`
  is `1` there, so the copies are incremented — and `(0,0)(1,1)(2,0)` repeats
  `(1,1)`, which does not start a block and so carries no rank of its own.
  Where the rank does reach, the ordinal has a name as well: each of those
  values is the value of an extended Buchholz term (`rank_genAll_val` and the
  five beside it), so for those matrices the question is answered in the
  notation system too.

## Conventions

* every claim is a Lean theorem with no `sorry` and no added axiom;
* `#guard` lines are computations on small cases, not theorems, and are kept
  visibly separate;
* `Core` never imports mathlib; a notation system imports it only when it
  evaluates into the ordinals.

## 2026-09-23: two rows, and the rank of extended Buchholz terms

- Pair sequences are translated into the ordinals through the `Trans` of
  koteitan/pss-proof, a Lake dependency. `Trans/PSS/` proves that its
  expansion is `expand2L`, maps its Buchholz terms onto the standard extended
  Buchholz terms below `ψ_0(Ω_ω)`, and proves that the rank of a pair sequence
  is `1 + val` of its term; the pair sequence system reaches `ψ_0(Ω_ω)`.
- `Notation/ExBuchholz/Cofinal.lean` proves that the fundamental sequence is
  cofinal for every countable standard form, the tower case included, and
  `RankVal.lean` that the rank of `exbOT` is `val`.
- The one-row DBMS translation is not injective literally: a state of
  `dbms 1` carries values outside its matrix. `Trans/DBMS/Tables.lean`
  proves the counterexample and injectivity on the entries.
- ω-Y with the expansion of Phyrion's Lean formalization (weak magma, no
  extraction) was re-proved by patterns of resemblance
  ([koteitan/wmwy-wo-por](https://github.com/koteitan/wmwy-wo-por), 2026-09-23).
  It is treated as a sequence system distinct from the official ω-Y
  (weak-magma ω-Y). The official ω-Y is treated in koteitan/wy-wo-por.

## 2026-09-23: the Y sequence terminates here

- `Notation/Y/WellOrder/` is a port of koteitan/1y-wo-por (`ZeroY/`, `OneY/`,
  `Por/`; Apache-2.0) and koteitan/1y-expand-equiv (`Equiv/` without its copy
  of the transcription) from Lean 4.33.1 to Lean 4.30.0: 203 modules, about
  40,000 lines. Only the imports and seven proofs changed. In Lean 4.30.0 a
  `match` written in a statement keeps a `save_info` annotation on its
  alternatives, and after the `match` is reduced `omega` cannot see a
  subtraction under it; the tactic `strip_mdata` of `WellOrder/Port.lean`
  removes the annotations. `Equiv/Row0.lean` needed one more change, because
  `Por.BMS.greatestBelow?` is not defined by recursion as the unlicensed
  `YesMetaZFC` version was.
- `Notation/Y/WellFounded.lean` joins `Por.expansion_wellFounded` and
  `Yukito.expand_eq`. `expand_eq_numeric` says that `expand` is
  `OneY.Numeric.expand` on every legal sequence, the empty one included, with
  the fuel of `Basic.lean`. From it: `ySys_wf`, `ySys_terminates`,
  `yStd_terminates`, `yEval` on the standard forms, `yLegal_wf` and
  `yLegal_terminates` on every legal sequence, and `yStd_strictWellOrder`,
  the lexicographic well-order of the standard forms.
- The non-standard column of the README counts `yLegal`, whose states are all
  sequences with positive entries and first entry `1`. Nothing is proved for
  other sequences.

## 2026-09-23: goal records and the README check

- Section 7 of [spec.md](spec.md) says how the goals are recorded. The records
  are in `Googology/Core/Goals.lean`, `Googology/Goals/Basic.lean` and
  `Googology/Goals.lean`: 18 records, 77 lines of the audit.
- The README is not generated. `scripts/check_readme.py` reads the audit and
  the tables of `README.md` and `README-ja.md`, and exits `1` on a mismatch.
- `lake build` (the default targets) builds the records and prints the audit,
  because `test/GoalsAudit.lean` is in the `Test` library. The check:

  ```sh
  lake env lean test/GoalsAudit.lean > audit.txt
  python3 scripts/check_readme.py --audit audit.txt
  ```

  The output of `lake build` or of `leanman check` can also be piped into
  `--audit -`. On 2026-09-23 the check exits `0`. The axioms are `propext`,
  `Classical.choice` and `Quot.sound`.
- Where a record states less than the README text:
  - "BMS with at most 2 rows" is recorded on the entries (`prim`, `pairL`),
    not on the arrays of `bms 1` and `bms 2`. On the arrays, "injective" fails
    for the same reason as for one-row DBMS.
  - Extended Buchholz's ψ, "surjective": the image is the ordinals below
    $`\psi_0(\Lambda)`$, not all of $`C_0(\Lambda)`$. `exbOTStd` has
    `Standard := True`; it is not the set reachable from the generators.
  - `bmsNotation`, `dbmsNotation` and `bmsToSucc` cover `r + 1` rows for
    every `r`.
  - Rows with no map (for example "BMS with 3 rows or more") have no record.
    Under 7.5 of spec.md their cells are empty.
- Five cells that are ❌ can be proved in a few lines from existing theorems.
  This was checked in a scratch file, but they are not wired, so that the
  README keeps matching. They are in [plan.md](plan.md).
- Five cells found by the goal-record audit became ✅ (2026-09-23): pair sequences → extended Buchholz's ψ preserves the rank (`pairToExb_rank`), BMS `r` rows → `r+1` rows is injective (`bmsToSucc_injective`), DBMS `r` rows → BMS `r` rows commutes with expansion, is injective and preserves the rank (`dbmsToBms_commutes`, `dbmsToBms_injective`, `dbmsToBms_rank`). All are in the Bridges section of `Googology/Goals.lean`.

## 2026-09-23: one-row DBMS on the matrices

- A standard form of DBMS is its matrix. The states of `dbms 1` are arrays,
  and an array also holds values outside its matrix, so two standard arrays
  can be one standard form. The author decided to state injectivity on the
  matrices.
- `Trans/DBMS/OneRowL.lean` defines `dbmsL1`, one-row DBMS on the entries:
  a state is the list of entries of a standard array, the step is `expandL`,
  and the empty list halts. `dbmsL1Std` names the generators `(0)(1)⋯(n)`.
  `dbmsToL1` maps the arrays onto it as a `StepHom` and keeps the rank and
  the ordinal. `dbmsL1EquivPrim` says it is the primitive sequence system.
- The records `dbmsOneRowOrd` and `dbmsToPrim` now use `dbmsL1`. The ordinal
  table row "one-row DBMS" is ✅ in all six columns, and the cell one-row
  DBMS → primitive sequences is ✅✅✅✅✅✅.
- The counterexample on the arrays (`dbmsOrdEval_not_injective`,
  `dbmsHom_not_injective`) stays. It is a true statement about the
  representation `Arr 1`, not about the standard forms.
- Five trio and pair items (2026-09-23, branch `feature/trio-pair`).
  - The map of `Trio.lean` lands in the standard forms of three-row BMS for `α < ε₀` (`trioMatrix_std`, `Trans/BMS/TrioStd.lean`).
  - It preserves and reflects the order and is injective (`omegaIndexMatrix_lt_iff`, `omegaIndexMatrix_injective`, `Trans/BMS/TrioMono.lean`). The cell extended Buchholz's ψ → trio sequences / injective became ✅.
  - Rules 1–10 (`ε₀ ≤ α < Λ`) are transcribed (`Trans/BMS/TrioRules.lean`) and checked by 875 `#guard`s (`TrioRulesSheet.lean`). Of 813 rows, 28 non-standard rows are skipped; of the other 785, 744 agree with the table and 41 agree with the reference program but not with the table.
  - Cofinality: koteitan/trio's `trio_cofinality` and its 16 dependency files are in `Trans/BMS/TrioCof/`, with a proved bridge to this library's BMS (`trio_cofinal`, `trioStd_cofinal`, `Trans/BMS/TrioCofinal.lean`).
  - Pair sequences → extended Buchholz's ψ does not preserve expansion and does not commute with it (`Trans/PSS/Expansion.lean`, `pairToExb_not_preserves`, `pairToExb_not_commutes`). The counterexample is the generator `(0,0)(1,1)` with `[0]`.
- DBMS `r` rows → `r + 1` rows is proved (2026-09-23, `Trans/DBMS/ZeroRow.lean`), with a proof that it is not surjective; the table cell is ✅✅✅✅❌✅(*3). Surjectivity of the BMS map can be refuted the same way (added to the plan).
- Trio cofinality restated with the ψ terms (2026-09-23, `Trans/BMS/TrioCofPsi.lean`): two-way cofinal at a limit `α`; the successor case stays in the plan.
- The transcription of rules 1–10 agrees with `trioMatrix` below `ε₀` for depth at most 201 (`TrioRulesE0.lean`). The derived `==` on `Ex` is opaque, so `predBeta` was rewritten with a pattern match (same behaviour). Fuel 200 fails on the tower of depth 203.
- The 41 rows are decided (`TRIO-SHEET-41.md`): no transcription error; rules right on 17, table right on 22, 1 open, 1 out of scope.
- BMS `r` rows → `r+1` rows is not surjective (`ZeroRowSurj.lean`); footnote (*4) in the table.
- The translation of two-row DBMS into the ordinals, with all six properties (`Trans/DBMS/TwoRow.lean`); the README row is split into "DBMS with 2 rows" (all ✅) and "DBMS with 3 rows or more".
- One pair-sequence step goes to one or more ψ steps (`Trans/PSS/Steps.lean`, `Goals/PairReach.lean`).
- Trio cofinality at a successor (`TrioSucc.lean`), and rules 1–10 with depth fuel agreeing for every `α < ε₀` (`TrioRulesFuel.lean`), are proved (2026-09-23).
- Rules 1–10 fixed in four places (`TrioRules2.lean`, 2026-09-23): the table's matrix on the 22 table-right rows, the other standard rows unchanged. The same fix is needed in koteitan/trio's `tools/probe_eps_range.py`.
- Row 3480 decided (`TrioRow3480.lean`, 2026-09-23): the label is right, and both the table and the rules are wrong; the right matrix `c2` is proved standard in Lean.
- The number of ψ steps for one pair step has no bound (`PSS/StepBound.lean`, `Goals/PairStepBound.lean`). The family found numerically uses `[2]`; the proved family uses `[0]`.
- The DBMS rank is reduced, for every number of rows, to the ranks of the block contents (`DBMS/Blocks.lean`); at 3 rows the first generators are computed (`DBMS/ThreeRow.lean`). The content system `C_3` is not inside the 3-row BMS standard forms (yaBMS).
- On terms whose subscripts are 0 or 1, the trio map gives standard forms and preserves the order (`TrioTree*.lean`). Because of fuel 200, two terms at depths 206 and 207 get the same matrix. `ofTerm` reads `ψ_0(Ω+1)` as `ε₀^{ε₀^ω}`, which disagrees with the table's row for `ε₀·ω`.
- Rows 4746, 4747, 4752 and 4753: the table is confirmed (`TrioSheet41Confirm.lean`). The printed label of row 3552 is fixed by Fix E (`TrioRules3.lean`). "lies above" in the 41-row note was wrong and is now "lies below".
- The generators of the content system `C_3` are lifted BMS generators, and the conjecture that 3-row DBMS and BMS have the same ordinal is stated (`DBMS/ThreeRowLift.lean`); no counterexample on about 600 standard forms.
- The necessary condition on standard lists of blocks is proved (`DBMS/BlocksStd.lean`); at 3 rows, on all 43597 lists of at most 8 columns, standard = contents lexicographically non-increasing.
- Fix N (`TrioRulesNonLast.lean`): in the tower regimes a leaf that is not last is upgraded at once, which fixes the order of `Ω_{Ω_Ω}+Ω_{Ω_2}+1`. The rules now exist in four versions; merging them is added to the plan.
