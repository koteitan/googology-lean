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

### `Notation/OmegaY/` — done

The official ω-Y: the rule of Naruyoko's program, `Official.lean`, with
`omegaYSys`, its seeds `(1, h+2)` and `omegaYAll` on every list. Termination
is a theorem here: `WellFounded.lean`, from the proof ported into
`WellOrder/`.

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
   matrices with a zero row underneath and `BMS/BMS/Embed.lean` carries their
   ordinals across. So the pair sequence system starts where the primitive
   sequence system ends — with no two-row reading, which there still is
   not. `rank_gen_eq_iSup` is the same at every number of rows: the
   `r + 2`-row generator's rank is the limit of the `r + 1`-row generators'
   ranks. `BMS/common/Append.lean` adds the additive structure: expansion never
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
   `BMS/common/Rows.lean` pins the bad root down for any number of rows, and
   `BMS/common/TwoRow.lean` reads the two-row column map off — `m₀` is `0` or `1`,
   and at `1` row `0` takes an increment on the columns whose bad-part
   position is a row-`0` ancestor of the bad root. `BMS/common/Anc.lean` says what
   that ancestor relation is on the entries, and computes it, and
   `BMS/common/Entries2.lean` puts the two together: `expand2L` is the whole rule
   written on the entries, and `entries2_expand` says it is `BM4.expand`. It
   runs, and agrees with the reference implementation on every two-row matrix
   of length at most `4` with entries below `3` — `46` standard forms, `138`
   expansions, all matching (`test/TransCheck.lean`). `BMS/common/Pair.lean`
   packages it as a `Rewrite` with its generators, and carries termination
   across. `BMS/common/EntriesR.lean` does the same for **any** number of rows:
   `parent A k` and `anc A k` at every row, and `expandRL` with
   `entriesR_expand`. So every Bashicu matrix expansion runs, which the array
   form does not. At three rows it agrees with the reference implementation on
   all `72` expansions of the `24` standard matrices of length at most `3`
   with entries below `3`. `BMS/common/Agree.lean` ties the three rules together —
   `expandRL` at one and two rows is `expandL` and `expand2L` — and packages
   the general one as `bmsL r`, with `bmsL_terminates` and `bmsLStd`.
   `BMS/common/Same.lean` ties the systems together: `bmsL 0` is `prim` and `bmsL 1`
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

The hierarchy is settled too: `BMS/BMS/ZeroRow.lean` says a row of zeros
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
  `Trans/ExBuchholz/BMS/Trio/Trio.lean` transcribes the `α < ε₀` half of it as
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
  that `BMS/common/Append.lean` reaches. `(0,0)(1,1)(2,1)` is none of those — `m₀`
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
  `dbms 1` carries values outside its matrix. `Trans/DBMS/ExBuchholz/Tables.lean`
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

## 2026-09-26: the official ω-Y terminates here

- `Notation/OmegaY/WellOrder/` is a port of koteitan/wy-wo-por (revision
  `7038635`, Apache-2.0) from Lean 4.33.1 to Lean 4.30.0: 493 modules, which with
  `Official.lean` are the import closure of `wellFounded_step`. The 0-Y modules and the BMS layer are
  imported from `Notation/Y/WellOrder/` instead of copied. The namespace
  `Por` of the ω-Y model is renamed to `OmegaY.Por`, because ten names clash
  with the 1-Y model. Every file sets `backward.do.legacy false`, so that
  Lean 4.30.0 elaborates `do` blocks as Lean 4.33.1 does; 23 files needed
  proof changes, no statement changed.
- The rule, `OmegaY/Official/Build.lean` of wy-wo-por, is moved to
  `Notation/OmegaY/Official.lean`, as `Yukito.lean` sits in `Notation/Y/`.
- `OmegaY.Official.expand` returns `Except`. `Basic.lean` reads an error as
  `()`, so a step is total; `()` is standard already, so no standard form is
  added. That no error occurs on a standard form is not proved; none occurs on
  the 474 fixtures of `test/OmegaYCheck.lean`.
- The non-standard column counts `omegaYAll`, whose states are all lists of
  naturals. The ported theorem has no condition on the list, so this needs no
  more than the error case.
- `OmegaY/` imports `Y/WellOrder/ZeroY/`, an exception to layering rule 2 of
  `spec.md`, like `DBMS/` importing `BMS/`.

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
- `Trans/DBMS/BMS/OneRowL.lean` defines `dbmsL1`, one-row DBMS on the entries:
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
  - The map of `Trio.lean` lands in the standard forms of three-row BMS for `α < ε₀` (`trioMatrix_std`, `Trans/ExBuchholz/BMS/Trio/TrioStd.lean`).
  - It preserves and reflects the order and is injective (`omegaIndexMatrix_lt_iff`, `omegaIndexMatrix_injective`, `Trans/ExBuchholz/BMS/Trio/TrioMono.lean`). The cell extended Buchholz's ψ → trio sequences / injective became ✅.
  - Rules 1–10 (`ε₀ ≤ α < Λ`) are transcribed (`Trans/ExBuchholz/BMS/Trio/TrioRules.lean`) and checked by 875 `#guard`s (`TrioRulesSheet.lean`). Of 813 rows, 28 non-standard rows are skipped; of the other 785, 744 agree with the table and 41 agree with the reference program but not with the table.
  - Cofinality: koteitan/trio's `trio_cofinality` and its 16 dependency files are in `Trans/BMS/common/TrioCof/`, with a proved bridge to this library's BMS (`trio_cofinal`, `trioStd_cofinal`, `Trans/BMS/common/TrioCofinal.lean`).
  - Pair sequences → extended Buchholz's ψ does not preserve expansion and does not commute with it (`Trans/BMS/ExBuchholz/PSS/Expansion.lean`, `pairToExb_not_preserves`, `pairToExb_not_commutes`). The counterexample is the generator `(0,0)(1,1)` with `[0]`.
- DBMS `r` rows → `r + 1` rows is proved (2026-09-23, `Trans/DBMS/DBMS/ZeroRow.lean`), with a proof that it is not surjective; the table cell is ✅✅✅✅❌✅(*3). Surjectivity of the BMS map can be refuted the same way (added to the plan).
- Trio cofinality restated with the ψ terms (2026-09-23, `Trans/ExBuchholz/BMS/Trio/TrioCofPsi.lean`): two-way cofinal at a limit `α`; the successor case stays in the plan.
- The transcription of rules 1–10 agrees with `trioMatrix` below `ε₀` for depth at most 201 (`TrioRulesE0.lean`). The derived `==` on `Ex` is opaque, so `predBeta` was rewritten with a pattern match (same behaviour). Fuel 200 fails on the tower of depth 203.
- The 41 rows are decided (`TRIO-SHEET-41.md`): no transcription error; rules right on 17, table right on 22, 1 open, 1 out of scope.
- BMS `r` rows → `r+1` rows is not surjective (`ZeroRowSurj.lean`); footnote (*4) in the table.
- The translation of two-row DBMS into the ordinals, with all six properties (`Trans/DBMS/ExBuchholz/TwoRow.lean`); the README row is split into "DBMS with 2 rows" (all ✅) and "DBMS with 3 rows or more".
- One pair-sequence step goes to one or more ψ steps (`Trans/BMS/ExBuchholz/PSS/Steps.lean`, `Goals/PairReach.lean`).
- Trio cofinality at a successor (`TrioSucc.lean`), and rules 1–10 with depth fuel agreeing for every `α < ε₀` (`TrioRulesFuel.lean`), are proved (2026-09-23).
- Rules 1–10 fixed in four places (`TrioRules2.lean`, 2026-09-23): the table's matrix on the 22 table-right rows, the other standard rows unchanged. The same fix is needed in koteitan/trio's `tools/probe_eps_range.py`.
- Row 3480 decided (`TrioRow3480.lean`, 2026-09-23): the label is right, and both the table and the rules are wrong; the right matrix `c2` is proved standard in Lean.
- The number of ψ steps for one pair step has no bound (`BMS/ExBuchholz/PSS/StepBound.lean`, `Goals/PairStepBound.lean`). The family found numerically uses `[2]`; the proved family uses `[0]`.
- The DBMS rank is reduced, for every number of rows, to the ranks of the block contents (`DBMS/BMS/Blocks.lean`); at 3 rows the first generators are computed (`DBMS/BMS/ThreeRow.lean`). The content system `C_3` is not inside the 3-row BMS standard forms (yaBMS).
- On terms whose subscripts are 0 or 1, the trio map gives standard forms and preserves the order (`TrioTree*.lean`). Because of fuel 200, two terms at depths 206 and 207 get the same matrix. `ofTerm` reads `ψ_0(Ω+1)` as `ε₀^{ε₀^ω}`, which disagrees with the table's row for `ε₀·ω`.
- Rows 4746, 4747, 4752 and 4753: the table is confirmed (`TrioSheet41Confirm.lean`). The printed label of row 3552 is fixed by Fix E (`TrioRules3.lean`). "lies above" in the 41-row note was wrong and is now "lies below".
- The generators of the content system `C_3` are lifted BMS generators, and the conjecture that 3-row DBMS and BMS have the same ordinal is stated (`DBMS/BMS/ThreeRowLift.lean`); no counterexample on about 600 standard forms.
- The necessary condition on standard lists of blocks is proved (`DBMS/BMS/BlocksStd.lean`); at 3 rows, on all 43597 lists of at most 8 columns, standard = contents lexicographically non-increasing.
- Fix N (`TrioRulesNonLast.lean`): in the tower regimes a leaf that is not last is upgraded at once, which fixes the order of `Ω_{Ω_Ω}+Ω_{Ω_2}+1`. The rules now exist in four versions; merging them is added to the plan.
- Standard lists of blocks are characterized for any number of rows by "each content reachable from the earlier ones" (`DBMS/BMS/BlocksSuff.lean`), without rank injectivity or the lexicographic order.
- Reaching implies lexicographically `≤` for any number of rows (`DBMS/BMS/BlocksLex.lean`). "Standard ⟺ contents lexicographically non-increasing" is equivalent to `LexReach r` (the converse: lexicographically `≤` implies reaching), also to `ReachTotal r` and to `LexCof r`. At 3 rows, `LexCof 2` has no counterexample on 668746 pairs from 1157 contents.
- The rule versions are merged into `TrioRulesAll` (Fixes A–E and N); all existing checks pass. Fixes E and N both apply only on 8 hand-made probes, all standard.
- One half of the 3-row DBMS = BMS conjecture is proved (`DBMS/BMS/ThreeRowLower.lean`): `rkL 2 (bgen3 n) ≤ rkL 2 (cgen 2 (n+2))`, so ord(3-row BMS) ≤ ord(3-row DBMS). When the last column is `(x,0,0)` the lift does not commute with expansion; `liftTail` handles it. For n = 2 a candidate map T3 (raise row 2 of column 1 from 0 to 1) sends content states to BMS standard forms and keeps the order on 11731 cases; `T3(lift(G[N])) = G[N+1]` holds for n = 1, 2 but fails for n = 3.
- `LexReach r` is proved for every `r` (`DBMS/BMS/LexReachThree.lean`), without looking at the entries: `M[N+1]` reaches `M[N]`, so everything reached from one state is totally ordered by reaching (induction on rank), and the generators reach each other. Hence standard lists of blocks ⟺ contents in `C_{r+1}`, lexicographically non-increasing.
- Fix `mul-normalize` (`ExBuchholz/BMS/Trio/TrioFixMulNormalize.lean`) is the first of the separate patches on `TrioRulesAll`. The derived `==` on `Ex` does not unfold in proofs, so the patch uses patterns. The Python program of koteitan/trio has the same `mul` and `power` and needs the same `mkExp` fix to stay equal to the Lean.
- Fix `fuel` (`ExBuchholz/BMS/Trio/TrioFixFuel*.lean`): no rule changes, only the fuel. Two fuel-200 reads remain (`lvl` in `cmpAtomWith`, `cmpExp` in `add`); both are called only on atoms or constants (`lvl_atom`). Deep uncountable towers such as `Ω_{Ω_{…}}` at depth 150 do not finish computing, because the builder recomputes the same argument many times.
- Fix L and Fix S (`ExBuchholz/BMS/Trio/TrioFixLastLeaf.lean`, `ExBuchholz/BMS/Trio/TrioFixStretch.lean`) are patches on `TrioRulesAll`. Fix L's case D and the leaf value `N(r)+1` of case K are supported by BMS expansions and the sheet, not derived. Fix S has a scope leak: the between-digit storey gate `!laidS` (line 276) also acts under an uncountable regime; the gate `!(laidS && (regime.bind lvlO).isNone)` gives the same matrices on 1,225 labels and 1,848 probes, to be applied at merge. `TrioFixLastLeafSheet` needs `LEANMAN_TIMEOUT=1500` for a check.
- Fix `ofterm` (`ExBuchholz/BMS/Trio/TrioFixOfTerm.lean`) fixes only the reader. The counterexample to the order theorem is `α = ε_{ε₀} < β = ε_{ε₀^{ε₀^ω}}` with `M(β) < M(α)`; the fault is rule 1's `strip`, which writes `ω^{ε₀·ω}` as the tree of `ψ_0(ψ_0(Ω+1))` instead of `ψ_0(Ω+ψ_0(Ω+1))`. The identity `ψ_a(b_hi + b_lo) = ω^(P + b_lo)` is proved only for `ψ_0(Ω+t)`, `t < ε₁`, and needs the normal form in general (`ψ_0(Ω+ε₁+1) = ε₁`).
- `DBMS/BMS/ThreeRowUpperRefute.lean`: `C₀ = (0,0,0)(1,1,0)(2,2,1)(3,1,0)` is reached from `cgen 2 4`, and `t3 (C₀[1])` is not trio-standard, because the inner block `(3,0,0)(4,1,0)(5,2,1)` is also a lifted form that `t3` does not raise. The rank still goes down there, through a trio-standard `a` with `(t3 C₁)[k] = a[k+1]`.
- Heavy sheet files (minutes each) go to the separate library `GoogologySheets` (root `GoogologySheets.lean`), which is not a default target: with many agents checking at once, a default build that runs them holds the exclusive lock for an hour. Their verification is the `leanman check` of each file. The first ones are the `TrioFixStripSheet*` files.
- DBMS n = 2 (`DBMS/BMS/ThreeRowUpperNC*.lean`, `ThreeRowUpperRP*.lean`): the last open statement `T3nPushStd` is about trio-standardness. The paths from `t3n C` to `t3n (pushL C y)` take up to 119 expansion steps with no common shape, and the library characterizes `TrioStdL` only as the set reached from the generators; a proof likely needs a theory of which 3-row matrices are trio-standard.

## 2026-10-24: details moved out of the plan

When the plan was shortened, its previous body was moved here unchanged.

- Wilken's claim (A glimpse of Σ₃-elementarity, 2020, p. 421; repeated in Pure Σ₂-elementarity beyond the core, 2021, §1): "the segment of countable ordinals denoted by the Skolem-hull notation system derived from the first ω-many weakly inaccessible cardinals covers (the domain of) Core(R₂⁺)". R₂⁺ = (Ord; 0, +, ≤, ≤₁, ≤₂), and its core is the union of the least realizations of its finite patterns. Statement, results and experiments: [Trans/PoR/InaccPsi](Googology/Trans/PoR/InaccPsi/README.md). Our reading: the core equals the set of countable values of the [InaccPsi](Googology/Notation/InaccPsi/README.md) terms whose collapse arguments are below I_ω (the supremum of the inaccessibles), that is the ordinals below ψ_{Ω₁}(I_ω). R₂⁺ has two definitions: Carlson's by coverings (R₂^C, used first) and Wilken's by Σₙ-elementarity (R₂^S). Wilken's points υ_ι: υ₁ = ψ_{Ω₁}(Ω_ω) is the core of R₁⁺, and υ_{ι+1} is the same construction over υ_ι. A chain of length n is n additive principal numbers that are pairwise ≤₂. Done: the countable values form an initial segment (Lean); in R₂^C the core is the supremum of the least chains (Theorem CC, refereed); below υ_{ω·ω} the claim holds in both R₂^C and R₂^S: every ordinal there is in the core and is the value of a term (refereed; the step υ_{ξ+1} ≤ ψ_{Ω₁}(A + θ) is proved through the simultaneously defined ϑ-functions of Weiermann–Wilken 2011, refereed twice, and its InaccPsi side is in Lean); the exact names υ_{1+η} = ψ_{Ω₁}(Ω_ω + θ·η) for every η < Γ₀, where θ = ψ_{Ω₂}(Ω_ω) (Theorem T: the upper half refereed twice, the lower half once; it uses a map from InaccPsi values into Wilken's ϑ-system; so υ₁ = ψ_{Ω₁}(Ω_ω) needs no proof-theoretic citation; the induction up to η = ω·ω is in Lean), and the same names for every η below Ξ₁, the first fixed point of ι ↦ υ_ι (Theorem T+, refereed twice); the names of the fixed points Ξ_α = ψ_{Ω₁}(Ω_ω + ω^(θ+Ω₁)·α) up to Φ₁ = ψ_{Ω₁}(Ω_ω + ω^(θ+Ω₁·2)), the first fixed point of α ↦ Ξ_α (refereed twice; the name of Φ₁ once); so in R₂^C the claim holds up to Φ₁ (refereed twice), then up to Λ_ε = ψ_{Ω₁}(Ω_ω + ω^(θ+ε_{Ω₁+1}+1)) (refereed once; every υ-point below a bound υ* has an InaccPsi name, see the item on the full analysis), then up to ρ_{Λ′+ω²} = ψ_{Ω₁}(Ω_ω + ω^(θ+ε_{ζ_{Ω₁+1}+1}) + ω^(θ+2)), where ζ_{Ω₁+1} is the least fixed point of α ↦ ε_α above Ω₁ (refereed once), then up to ρ_{Λ_fp+ω²} = ψ_{Ω₁}(Ω_ω + ω^(θ+ψ_{Ω₂}(Ω₂)+1) + ω^(θ+2)), where ψ_{Ω₂}(Ω₂) is the least fixed point of α ↦ Γ_α above Ω₁ (refereed once), then up to ρ_{Λ_fp2+ω²} = ψ_{Ω₁}(Ω_ω + ω^(θ+ψ_{Ω₂}(Ω₂·2)+1) + ω^(θ+2)), where ψ_{Ω₂}(Ω₂·2) is the second fixed point of α ↦ Γ_α above Ω₁ (refereed once), then up to υ* = ψ_{Ω₁}(Ω_ω + Ω₂) and up to ν_P = ψ_{Ω₁}(Ω_ω + ω^(θ₂+2) + ω^(θ+2)) with θ₂ = ψ_{Ω₃}(Ω_ω) (refereed twice; that this point is ν_P, refereed once), then up to X₃ = ψ_{Ω₁}(Ω_ω + ω^(θ₂+2) + ω^(θ+3)·2) (refereed once), then up to X₄ = ψ_{Ω₁}(Ω_ω + ω^(θ₂+2) + ω^(G₂+1)·2) with G₂ = ψ_{Ω₂}(Ω_ω + ω^(θ₂+2)) (refereed once; ν_C ≥ X₄), then, given FRAG, up to X₅ = ψ_{Ω₁}(Ω_ω + ω^(θ₂+2) + ω^(ω^(G₂+Ω₁)+1) + ω^(G₂+1)) (refereed once; ν_C ≥ X₅), then, given FRAG, up to X₈ = ψ_{Ω₁}(Ω_ω + ω^(θ₂+2) + ω^(ε_{G₂+1}+1) + ω^(G₂+1)), where ε_{G₂+1} is the first ε-number above G₂ (refereed twice; ν_C ≥ X₈), then, given FRAG, up to X₉ = ψ_{Ω₁}(Ω_ω + ω^(θ₂+Ω₁) + ω^(G(Ω₁)+1) + ω^(G₂+1)), where G(Ω₁) = ψ_{Ω₂}(Ω_ω + ω^(θ₂+Ω₁)) (refereed twice; ν_C ≥ X₉), then, given FRAG, up to X₁₁ = ψ_{Ω₁}(Ω_ω + ω^(θ₂+Φ₂) + ω^(G(Φ₂)+1) + ω^(G₂+1)), where Φ₂ = ψ_{Ω₃}(Ω₃) and G(ζ) = ψ_{Ω₂}(Ω_ω + θ₂·ζ) (refereed once; ν_C ≥ X₁₁; the first range past the first index fixed point), then, given FRAG, up to X₁₂ = ψ_{Ω₁}(Ω_ω + ω^(θ₂+Φ^χ₂) + ω^(G(Φ^χ₂)+1) + ω^(G₂+1)), where Φ^χ₂ = ψ_{Ω₃}(Ω₃^Ω₃) (refereed once; ν_C ≥ X₁₂), then, given FRAG, up to X₁₃ = ψ_{Ω₁}(Ω_ω + ω^(θ₂+Φ^ϑ₂) + ω^(G(Φ^ϑ₂)+1) + ω^(G₂+1)), where Φ^ϑ₂ = ψ_{Ω₃}(ε_{Ω₃+1}) (refereed once; ν_C ≥ X₁₃), then, given FRAG, up to X₁₄ = ψ_{Ω₁}(Ω_ω + ω^(θ₂·2) + ω^(G(θ₂)+1) + ω^(G₂+1)) (refereed once; ν_C ≥ X₁₄), then, given FRAG, up to X₁₅ = ψ_{Ω₁}(Ω_ω + Ω₃ + ω^(G(Ω₃)+1) + ω^(G₂+1)), where G(Ω₃) = ψ_{Ω₂}(Ω_ω + Ω₃) (refereed twice; ν_C ≥ X₁₅), then, given FRAG, up to X₁₆ = ψ_{Ω₁}(Ω_ω + Ω₃ + θ₂ + ω^(G(Ω₃+1)+1)·2), where G(Ω₃+1) = ψ_{Ω₂}(Ω_ω + Ω₃ + θ₂) (refereed twice; ν_C ≥ X₁₆), then, given FRAG, up to X₁₇ = ψ_{Ω₁}(Ω_ω + Ω₃·ω + θ₂ + ω^(G(Ω₃·ω+1)+1)·2) (refereed once; ν_C ≥ X₁₇), then, given FRAG, up to X₁₈ = ψ_{Ω₁}(Ω_ω + ζ̂₂ + ω^(G(ζ̂₂)+1)·2), where ζ̂₂ = θ₃·(ω+1) + φ(ω, ψ_{Ω₃}(Ω_ω + θ₃·(ω+1)) + 1)·ω and θ₃ = ψ_{Ω₄}(Ω_ω) (refereed twice; ν_C ≥ X₁₈), then, given FRAG, up to X₁₉ = ψ_{Ω₁}(Ω_ω + ζ̂_ε + ω^(G(ζ̂_ε)+1)·2), where ζ̂_ε = θ₃·ω² + ε_{g₃+1} and g₃ = ψ_{Ω₃}(Ω_ω + θ₃·ω²) (refereed once; ν_C ≥ X₁₉), then, given FRAG, up to X₂₁ = ψ_{Ω₁}(Ω_ω + ζ̂_H + ω^(G(ζ̂_H)+1)·2), where ζ̂_H = θ₃·Ω₃ + ω^(ĝ₃+g₃) and ĝ₃ = ψ_{Ω₃}(Ω_ω + θ₃·Ω₃) (the first proof refereed twice; it used exact long reaches that are false for some codes, and the repaired proof is refereed once; ν_C ≥ X₂₁), then, given FRAG, up to X₂₂ = ψ_{Ω₁}(Ω_ω + θ₄·ω² + ω^(G(θ₄·ω²)+1)·2) with θ₄ = ψ_{Ω₅}(Ω_ω), and up to X₂₃ = ψ_{Ω₁}(Ω_ω + ζ̂₂₃ + ω^(G(ζ̂₂₃)+1)·2), where ζ̂₂₃ = θ₄·Ω₄ + ε_{ĝ₄+1} and ĝ₄ = ψ_{Ω₃}(Ω_ω + θ₄·Ω₄) (refereed once, after the repair of a blocking point in the exact long reaches they use; that proof is not valid as written, but both points lie below ν_C, which is proved again), then, given FRAG, up to L(ω+1) = ψ_{Ω₁}(Ω_ω·2 + ω^(P′+1) + P′) with P′ = ψ_{Ω₂}(Ω_ω·2), which is exactly the first point where R₂^C and R₂^S stop being skeletal: ν_C = ν_S = L(ω+1) (proved again in the forty-first round with the corrected exact long reaches, refereed once; the first proof, refereed once and audited, used exact long reaches that are false for some codes), so Wilken's claim holds in R₂^C on all of [0, ν_C], given FRAG, and the hypothesis LOW, ν_C ≤ ψ_{Ω₁}(Ω_ω·2), is false; then, given FRAG, above ν_C, with the calculus in the gaps above ν_C run again on the corrected long reaches (forty-second round, refereed once; the counts below are those of the first proofs, which were not proved as written from the fortieth round on): up to X_A = ψ_{Ω₁}(Ω_ω·2 + ω^(P′+1) + P′ + ω^(θ+3)·2) (refereed once), up to L(ω²) = ψ_{Ω₁}(Ω_ω·2 + ω^(P′+2)) (refereed twice, by two independent proofs), up to L(Ω₁·ω) = ψ_{Ω₁}(Ω_ω·2 + ω^(P′+Ω₁+1)) (refereed once), up to L(ε_{Φ_Ω+1}) = ψ_{Ω₁}(Ω_ω·2 + ω^(P′+ε_{ψ_{Ω₂}(Ω₂)+1})) with Φ_Ω = ψ_{Ω₂}(Ω₂) (refereed once; up to L(Ω₁·ω+ω+1) refereed twice, by two independent proofs), and up to L(G₂) = ψ_{Ω₁}(Ω_ω·2 + ω^(P′+G₂)) with G₂ = ψ_{Ω₂}(Ω_ω + ω^(θ₂+2)) and θ₂ = ψ_{Ω₃}(Ω_ω) (refereed once; up to L(ε_{Φ_Ω+1}+ω²) refereed twice, by two independent proofs), and up to L(Ω₂+Φ^{P′}·ω) = ψ_{Ω₁}(Ω_ω·2 + Ω₂ + ω^(Φ^{P′}+1)) with Φ^{P′} = ψ_{Ω₂}(Ω_ω·2+Ω₂) (refereed once; up to L(G(Ω₁)·ω) = ψ_{Ω₁}(Ω_ω·2 + ω^(P′+G(Ω₁)+1)), G(Ω₁) = ψ_{Ω₂}(Ω_ω + ω^(θ₂+Ω₁)), refereed twice, by two independent proofs), and up to Z^Λ = L(θ′₂·ω²) = ψ_{Ω₁}(Ω_ω·2 + ω^(θ′₂+2)) with θ′₂ = ψ_{Ω₃}(Ω_ω·2), then (forty-third to forty-eighth rounds, refereed once each) up to Z^FP, Z^W, Z^WW, Z^V = L(θ′₂·ψ_{Ω₃}(0)), Z^θ = L(θ′₂·θ₂) with θ₂ = ψ_{Ω₃}(Ω_ω), and Z^{Ω₃} = L(Ω₃) = ψ_{Ω₁}(Ω_ω·2 + Ω₃), and R₂^C and R₂^S agree on every relation with right end below Z^{Ω₃}; **this is the frontier now** (see the item on the full analysis); in R₂^S the claim holds on [0, Z^θ), Z^θ = ψ_{Ω₁}(Ω_ω·2 + ω^(θ′₂+θ₂)) (forty-eighth round, refereed once; on [0, Z^V) by two independent proofs, refereed twice; earlier on [0, F_ν), past υ_{ω³} and ν_C); the restarts Θ_1 = ψ_{Ω₁}(Ω_ω + ω^(θ·2)) and Θ_A = ψ_{Ω₁}(Ω_ω + ε_{θ+ω}) have these names (refereed twice); every pattern without a chain of length 3 lies below the least ≤₁-predecessor of the least chain of length 3 (Lemma DOM₂, refereed); finite-set tests for ≤₁ and ≤₂ in R₂^S (refereed); in R₂^C, every ordinal below ρ_{Θ_dω} (a restart far above Λ_ε, see the item on the full analysis) is in the core (refereed once); Lemma FRAG (moving several υ-points at once keeps 0, +, ≤, ≤₁ of R₁⁺) is proved (refereed twice, the second time by an independent audit); the ≤₂-pairs and the blocks of R₂⁺ below Λ_ε, in both definitions, with the exact reach of every restart (Theorem BLK^O, refereed once; up to Ξ_ω refereed twice); the ≤₂ relation that conv prints never has a chain of length 3 (refereed once)
  - upper bound (the core is contained in ψ_{Ω₁}(I_ω))
    - Paused on 2026-10-17 (the work is now Lean only; the paper results below are not machine-checked): R₂^S versus R₂^C. Write β₀ ("the first difference") for the least ordinal β at which some relation α ≤₁ β or α ≤₂ β differs between the two structures. Where it stands (details in the README of Trans/PoR/InaccPsi, §3; given FRAG; refereed once unless said): the two structures agree on every relation with right end below Z^{Ω₃} = L(Ω₃) = ψ_{Ω₁}(Ω_ω·2 + Ω₃), so β₀ > Z^{Ω₃} (from the item on the full analysis); Wilken's claim holds in R₂^S on [0, Z^θ), Z^θ = L(θ′₂·θ₂) = ψ_{Ω₁}(Ω_ω·2 + ω^(θ′₂+θ₂)), θ₂ = ψ_{Ω₃}(Ω_ω) (forty-eighth round; on [0, Z^V), Z^V = L(θ′₂·ψ_{Ω₃}(0)), by two independent proofs, refereed twice): the reach of Z^V is now proved inside the range of an induction (CAP^V), which removed the blocking point of the last round; every relation of R₂^S with right end at most β₀ holds in R₂^C; by Carlson's "Categoricity for patterns of order 2" (https://arxiv.org/abs/1104.1686) the two cores are isomorphic, and (E) (R₂^C has no extra ≤₂ relation up to its core) is equivalent to "the two cores are equal". Left: the R₂^S side above Z^θ (the step past Z^θ needs the reach of Z^θ; the full analysis now proves it, and this combination needs a review; then the base points between Z^θ and Z^{Ω₃}); (E), the same as "the core of R₂^S has no gap" (Carlson 2009, p. 97, says it "will be established elsewhere"): below the core of R₂^C, every relation that Carlson's clauses give in R₂^S must hold in R₂^S, which below the least fan apex x_F means clause-2 rigidity at every such point from Z^{Ω₃} on; the extra pairs at fan apexes and caps (the loading condition FAN-LOAD is a conjecture); (R) and o_k = ω in R₂^S without FRAG (both follow from (E)); the converse for ≤₁ at successor stages above the core of R₂^C (not needed for the cores); R₂^S = R₂^C above Z^{Ω₃}, and the place of β₀
    - for every n, find an explicit chain of length n below ψ_{Ω₁}(I_ω), written as InaccPsi values (research; for n = 3 there is now a conjecture, see next item). Known (refereed once): for an upper bound it is enough to find one <₂-pair a <₂ c below the bound and a second left end b <₂ c between them; no such pair is yet given by InaccPsi terms
    - locate the least chain of length 3: c₀ < c₁ < c₂, pairwise ≤₂, with least ≤₁-predecessor m₃. Write θ₀ = ψ_{Ω₁}(ψ_{I₀}(0)), the least countable value that needs an inaccessible, and call a point with two ≤₂-successors a fan. Known (Trans/PoR/InaccPsi): in R₂^C, c₀ is the least point with an infinite ≤₁-chain of ≤₂-successors, c₀ > m₃ > the first fan > T_ω (the limit of the levels of nested pairs), and c₂ < ω₁^CK; the first fan of R₂^C is described completely, its ≤₁-predecessors have order type ω², and the least of them, m_F, is above ν_C (refereed once). Left, the upper half: an upper bound for c₀ by an InaccPsi term (conjecture: c₀ < ψ_{Ω₁}(I₁); the covering argument bounds a point only by other points, never by a term; splitting the bound into a start and a cost per step is equivalent to the bound itself, so it is no reduction, refereed once) and names for c₀, c₁, c₂ (Conjecture C3′, with no derivation left: m₃ = ψ_{Ω₁}(E), and the chain is ψ_{Ω₁}(E + P), ψ_{Ω₁}(E + ω^(P+1)), ψ_{Ω₁}(E + ω^(P+1) + P), with E = ε_{I₀+1} and P = θ = ψ_{Ω₂}(Ω_ω)); whether the least points with n ≤₂-successors in a ≤₁-chain (n = 2, 3, …) have their limit below m₃, and whether c₀ is the least point with arbitrarily many; names for the first fan (conjecture: x_F = ψ_{Ω₁}(B + ω^(P_B+2)) with P_B = ψ_{Ω₂}(B), with the base B = I₀; the support is analogy only, and the bases I₀·2 and ψ_{I₀}(0)·2 fit the checks too; an upper bound such as x_F < ψ_{Ω₁}(I₀·ω) is open); an upper bound for m_F: write CH_k for k pairs in a row, u₁ <₂ v₁ < u₂ <₂ v₂ < … < u_k <₂ v_k, with every u_i ≤₁ v_k. Known (refereed once): every pattern with no fan and no right end ≤₁ to a larger point lies below the least realization of some CH_k, so m_F is the limit of the points of CH_1, CH_2, …, and m_F ≤ t exactly when every CH_k has its point below t. CH_1 is below υ_ω, but CH_2 is already above ν_C, beyond every point with a proved InaccPsi bound. If every CH_k is below ψ_{Ω₁}(I₀) and a step condition (HQ) holds along the ≤₁-predecessors of the fan, then x_F < ψ_{Ω₁}(I₀·2). New (refereed once): the point of CH_2 is below t exactly when one point a below t has three relations: a <₂ b, a pair c <₂ d with b < c, and a ≤₁ d (no two of them are enough), and such a point lies above ν_C; the point of CH_k is the least left end whose reach holds k−1 more chains. Splitting the bound into a start and a cost per step (STEP-CH) is not equivalent to this form: only one direction holds, for a class closed under the step. Left: an InaccPsi bound for the point of CH_2 (it needs names for points above ν_C (names are now proved up to υ* = ψ_{Ω₁}(Ω_ω + Ω₂) and the exact structure up to ρ_{Λ_fp2+ω²}, refereed once), the exact structure of R₂^C there, or an order embedding of Carlson's closure there), a bound for one more pair of the chain (STEP-CH), (HQ), and whether the chains attached to a point v of the fan reach the next point (REL-SHARP; only ≤ is proved); whether I₀ ≤₂ β for some β > I₀; the proof that collapsing an InaccPsi hull does not keep ≤₁ (the referee's repair is not yet reviewed). The lower half: whether the first fan needs an inaccessible. Its least ≤₁-predecessor m_F is ≥ θ₀ exactly when every ordinal below θ₀ lies below the least realization of some pattern with no fan in which no right end of a <₂-pair is ≤₁ to a larger point of the pattern (refereed once); then the first fan needs an inaccessible (the converse, whether θ₀ can lie between m_F and the fan, is open). Now (refereed once) m_F ≥ θ₀ holds exactly when some CH_k has its point ≥ θ₀; the point of conv(SRO) lies between those of CH_1 and CH_2; the earlier sufficient hypothesis FF_N (the least realizations of a family of fan-free configurations climb to θ₀) is now the same as m_F ≥ θ₀. New (refereed once): every pattern with no fan and no configuration L1p (a pair inside the reach of an earlier left end, beyond its right end) lies below the point of CH_2, so the point of CH_2 is ≥ θ₀ if the lower-bound program gives patterns without L1p. This follows from the lower-bound program below θ₀ (the item "extend the map" below). The same hypothesis gives an inaccessible in m₃ and the chain; so does the weaker one that the least points with n ≤₂-successors in a ≤₁-chain climb to θ₀. Also: Lemma DOM_k for every k (a pattern without a chain of length k+1 lies below the least chain of length k+1; conjecture) and its fan form in R₂^S; in R₂^S, the converse half of Theorem CP3 ("an infinite ≤₁-chain of ≤₂-successors gives a chain"); RIGHT (every right end of a <₂-pair is a υ-point) in R₂^C above β₀ (it is proved in R₂^S)
    - in R₂^S, is the uniform finite-set test for ≤₂ (one copy for all sizes at once) also necessary? (Wilken 2021, p. 6, says yes for R₂ without +)
    - base changes that keep 0, +, ≤, ≤₁ and ≤₂. Done (refereed twice, the second time by an independent audit): Theorem FRAG2, a map of Lemma FRAG keeps ≤₂ on a finite set exactly when it keeps the reach and the <₂-pairs of the υ-points of the set, wherever R₂⁺ is "skeletal" (the points that are not υ-points have their R₁⁺ reach, and every <₂-pair is υ_ξ <₂ υ_{ξ+1}). The map of Lemma FRAG equals a plain substitution map, so it does not depend on the auxiliary choices in its construction (refereed twice). R₂^S is skeletal up to ν_P = υ_{Λ*+ω·ω}, where Λ* is the first restart whose reach leaves its own region (refereed once). The first point ν where R₂^S stops being skeletal is found exactly (refereed once): ν is the top of the least <₂-pair that has another <₂-pair nested inside it; ν = υ_μ is a restart with ω³ dividing μ; the only new pair with right end ≤ ν is (a₀, ν), where a₀ = υ_Λ with ω³ dividing Λ; no point ≤ ν is ≤₁ to anything above ν. The description of the skeletal regime holds up to ν (Theorem SKEL⁺). In R₂^C the first non-skeletal point ν_C is the top of the least nested pair, it is at most ν and above ν_P, and it equals ν unless R₂^C has exactly one extra "ghost" pair below ν, whose shape is known (Theorem NU-CT, refereed once); so the two structures agree below ν_C, every ordinal up to ν_C is in the core of R₂^C, and no fan of R₂^C is at or below ν_C (refereed once). The least realization of a pair with a nested pair is written with υ-indices, and as InaccPsi terms relative to the name of a₀ (refereed once). Beyond the skeleton: FRAG2 needs only its first condition (FRAG2-W), it holds with an extra "cut" datum (FRAG2-C), and one base change between any two ε-bases works under Wilken's side condition (FRAG2-1E); all refereed once, with their stated hypotheses, and the hypothesis INC1 they used is now proved. Whether ν_C = ν is now a question about R₂^S alone (refereed once): it follows from two statements about R₂^S below ν, NOLIM (no point outside the first block of level 2 is a limit of arbitrarily long ≤₁-chains of restarts with long reach; proved up to ν_P) and o₂ = ω (the first block of level 2 has exactly ω points below its left end a₀). New (refereed once): in R₂^C every level of nested pairs has exactly ω points below its left end (o_k = ω for every k), proved from Carlson's minimality against coverings, with no base change; so in R₂^C the shape of the name of ν holds (ν_C is the (ω+1)-th point of its level), and so does the finite base change between gaps. In R₂^S: ν_C = ν implies o₂ = ω, and given NOLIM the two are equivalent; NOLIM is the same as "in every gap of level 2, the least limit of arbitrarily long chains of long restarts is the next point of the level" (all refereed once). Two attempts at o₂ = ω in R₂^S did not succeed (refereed once each): an argument with Σ₂ sentences needs two gaps with equal index lengths, which is false under the conjectured names; a global substitution map between gaps is an isomorphism exactly when the reaches of the moved restarts correspond, and the simple shift map already fails this. New: in R₂^C NOLIM holds (refereed once; it uses SKEL⁺, which now has a complete proof, refereed once): a point inside a gap that is a limit of arbitrarily long chains could be moved down by a covering that sends the restarts above it onto such a chain below it; and ν_C = ν holds exactly when NOLIM and o₂ = ω both hold in R₂^S (refereed once). The name of ν (conjecture: ψ_{Ω₁}(Ω_ω·2 + ω^(θ′+1) + θ′) with θ′ = ψ_{Ω₂}(Ω_ω·2)) is equivalent to o₂ = ω together with two statements about υ-indices (refereed once). A base change between the gaps of a level, in its finite form, is equivalent to o_k = ω (refereed once; the referee notes that this only restates a known clause, so it is not progress on o_k = ω); on the first segment of every gap of level 2, Wilken's map is already such a base change (refereed once, given Lemma ST of FRAG). Now, given FRAG (refereed once): ν_C = ν = ψ_{Ω₁}(Ω_ω·2 + ω^(θ′+1) + θ′), so there is no ghost, the name of ν holds, and o₂ = ω holds in R₂^S (it follows from ν_C = ν); the base change that moves the point ψ_{Ω₁}(Ω_ω·2 + θ′·n) to ψ_{Ω₁}(Ω_ω·2 + ω^(θ′+1)) keeps 0, +, ≤, ≤₁, ≤₂ below ψ_{Ω₁}(Ω_ω·2 + θ′·(n+1)), and every finite set of the last gap lies in its image for large n. Left: o₂ = ω, NOLIM and the name of ν without FRAG; for the levels above ν, a base change between gaps that is onto (it needs a hull for level 2, or a substitution map whose skipped restarts never change where the reach of a moved restart cuts its domain); that the InaccPsi side of these names needs nothing new; the ranges claimed for FRAG2-W and FRAG2-C (the referee's fix: claim them only below ν); moving several ε-bases that are not υ-points at once (FRAG-E), and nested cut data; base changes that move several points L(e) = ψ_{Ω₁}(Ω_ω·2 + P′·e) at once above L(θ′₂·(ω+1) + G″(ω+1)·ω). Done above ν (refereed once): a form of FRAG2 whose fixed set may contain pairs (FRAG2^rel), and a base change that moves several points L(e) at once, each with its gap, below the frontier L(θ′₂·(ω+1) + G″(ω+1)·ω) (FRAG″; its restriction to the gaps below the frontier refereed twice)
    - another way: theories with n inaccessibles prove that a chain of length n exists (needs a set-theoretic sufficient condition for <₂, which is not known)
  - Paused on 2026-10-17 (the work is now Lean only; the paper results below are not machine-checked): full analysis: hull systems over every base, with collapsing functions for all Ω_ξ and I_n defined at once, compared with InaccPsi; a structure theorem for ≤₁ and ≤₂ of R₂⁺ up to the bound (the analogue of Wilken 2021, Thm 4.2); the least realizations written as terms; Conjecture CH (the least chain of length k+2 needs k inaccessibles). Words: a restart is υ_λ with λ a nonzero multiple of ω·ω; its reach is the largest place it is ≤₁ to; level k is the structure of k nested <₂-pairs, and T_ω is the limit of the levels; L(e) = ψ_{Ω₁}(Ω_ω·2 + P′·e) with P′ = ψ_{Ω₂}(Ω_ω·2), θ′₂ = ψ_{Ω₃}(Ω_ω·2) and G″(ζ) = ψ_{Ω₂}(Ω_ω·2 + θ′₂·ζ); the restarts of level 3 are the L(λ″) with λ″ a nonzero multiple of ω². Where it stands (details in the README of Trans/PoR/InaccPsi; refereed once unless said): exact names ψ_{Ω₁}(Ω_ω + θ·η) of all υ-points below a point above ψ_{Ω₁}(I_ω) (Theorem GEN); without FRAG the claim holds in R₂^C on [0, X₄]; given FRAG, ν_C = ν_S = L(ω+1) and the claim holds in R₂^C on [0, Z^{Ω₃}], Z^{Ω₃} = L(Ω₃) = ψ_{Ω₁}(Ω_ω·2 + Ω₃) (forty-eighth round): at every restart b = L(λ″) of level 3 below Z^{Ω₃} the reach is r(b) = k″\_b(o_b(c″)), the o_b(c″)-th point above L(λ″+ω+1) that is closed relative to b, with the code c″ read at b; every normal multiplier ζ below Ω₃ is read by G″(ζ) ↦ L(λ″+1+ζ′), where ζ′ is ζ with every Ω_k lowered to Ω_{k−1} and its constants read at b (the same shift keeps normal forms and order for any increasing reading of the constants); below Φ^{P′} = ψ_{Ω₂}(Ω_ω·2 + Ω₂) the offsets do not depend on the base; the links of every code below Φ^{P′} are pinned; the reach of Z^θ = L(θ′₂·θ₂) is proved; no long restart of level 3 is crossed below Z^{Ω₃}; several steps have two independent proofs (refereed twice), the last one up to Z^θG = ψ_{Ω₁}(Ω_ω·2 + ω^(θ′₂+θ₂) + ω^(G″(ω²)+1)); LOW is false. Left: the claim above Z^{Ω₃} (above X₄ without FRAG). The next steps: the reading of the multipliers from Ω₃ on (there the reading is no longer the shift; conjecture THETA″^READ up to θ′₃·ω², θ′₃ = ψ_{Ω₄}(Ω_ω·2); four lemmas one level up are missing: the domain lemma with uncountable constants, the plateau and onto lemmas, the margin with constants, the ceiling) and the pins at the links of codes in [Φ^{P′}, G″(ω²)) (they need the L-point pin at the n-th L-point of a link and the far pin through several gaps at an arbitrary image); with them a proved implication puts the first crossing of a long restart of level 3 at the code G″(θ′₃·ω²) (conjecture: the next frontier is ψ_{Ω₁}(Ω_ω·2 + ω^(θ′₃+2))), and the counting for such crossings one level up; the codes below P₃ = ψ_{Ω₂}(Ω_ω·3) (every restart below ψ_{Ω₁}(Ω_ω·3) has a code below P₃) with the caps CAP-0 and CAP-1 one level up (CAP-0 holds below Z^{Ω₃}); and the least triple nest (its top in R₂^C is above Z^{Ω₃}; conjecture: its top is ν₃ = ψ_{Ω₁}(Ω_ω·3 + ω^(P₃+1) + P₃)). For ν₃, what is proved are implications (refereed once each): the least pair of R₂^S that is not skeletal at level 3 ends at or above ν₃, given CAP-0 up to ψ_{Ω₁}(Ω_ω·3), CAP-1, a long-class lemma at level 4 and the left-end lemma one level up (all four open); and the triple nest is at ν₃, given that lower half, the exact reaches of the restarts that cross L₃(ω) = ψ_{Ω₁}(Ω_ω·3 + ω^(P₃+1)) (open), and FRAG with the gap calculus above ψ_{Ω₁}(Ω_ω·3) (outline). The block structure at L₃(ω), whose ≤₁-predecessors are cofinal, no longer blocks this: the skeleton of a region of level 3 holds below the first pair that is not skeletal whatever its ≤₁-predecessors are, since the restarts that cross it are never left ends of skeletal pairs (forty-fourth round, refereed once). The R₂^C side of ν₃ needs one more step (an outline). Also left: the computed reach at Θ_dω (known only to lie between δ·ω and the next block top); the exact offsets between Λ_fp2 and Θ_1 (they need the hull lemma: with H(g) = ψ_{Ω₁}(Ω_ω + θ·g), below θ the InaccPsi hull of (Ω_ω + θ·g, H(g)) and Wilken's hull over the base Ω₁ with parameters below H(g) have the same elements); the exact reaches above Θ_A (the proposed rule is off by one at the block top, the referee's repair is not yet reviewed, and for candidates between δ_j·ω and the next block top the needed pin and the rule are now proved, refereed once); that the assignments between ordinals and patterns are elementary recursive (only an outline); for the levels above ν_S: in R₂^S, that each block has exactly ω points below its left end (o_k = ω; proved in R₂^C; in R₂^S it is equivalent to the pinning statement of that level and follows from (E), and given FRAG it holds at level 2), the exact reaches of the restarts of each level, the gaps as base-changed copies, and the names (conjecture: ψ_{Ω₁}(Ω_ω·k), ψ_{Ω₁}(Ω_ω·k + ω^(P_k+1)), ψ_{Ω₁}(Ω_ω·k + ω^(P_k+1) + P_k) with P_k = ψ_{Ω₂}(Ω_ω·k)); the reach of T_ω (conjecture: one more than the right end of the least pair of infinite depth above T_ω), and "given FRAG, T_ω ≤₁ ρ_{T_ω+ω·ω}" (the rest of its proof needs a new review); the reaches of the long skeleton codes and of the levels above (all codes are known up to Z^{Ω₃}); names for the points above L(ω+1) that are not υ-points; the hull systems, the least realizations as terms, Conjecture CH, and the part up to the bound (needs operators that no available paper defines)
  - lower bound (every ordinal below ψ_{Ω₁}(I_ω) is in the core). Write θ₀ = ψ_{Ω₁}(ψ_{I₀}(0)), the least countable value that needs an inaccessible (proved). Proved: the lower bound below θ₀ reduces to an order-preserving map from the terms whose value is an ε-number into the standard trio matrices, and, on the matrix side, to the single step "the pattern of the n-th term of the fundamental sequence of a matrix lies below the pattern of the matrix"; the map is order-preserving on a fragment of the terms, and the step holds on the family (0,0,0)(1,1,1)(1,1,0)(2,2,1) followed by m copies of (2,0,0), given the output shapes of conv. Certified (replayed): 1,389 of 1,422 neighbour pairs of 1,423 matrices below SRO, 478 of 496 on the fragment, 648 of 658 fundamental-sequence steps; the rest undecided, none refuted
    - extend the map to all terms below θ₀ whose value is an ε-number, and prove the fundamental-sequence step for all standard matrices below SRO (the step: for a limit matrix A and every n, the pattern of A[n] lies below the pattern of A). Where it stands (refereed): all 3,166 sample matrices between V₃ and SRO are done: the step holds for every n on each of them (each is the sample part of an infinite class; the last 3 were done with a marker for a chain with a constant label, refereed once). Left for the step: only the general statement, for all standard matrices below SRO. This needs a classification of all matrices into classes where the method works, with engines uniform over the matrix; markers for growth patterns not in the sample (a chain over a chain, nests of nests, period more than 2); and a rule that builds the derivation from the shape (now the data are found by a search for each matrix). Or else an order-preserving map, which needs fundamental sequences for InaccPsi. Left on the side of the terms, in this order: the base at level 1 and up (arguments Ω_ω + ζ with ζ < θ); uncountable multipliers and tails; successor indices such as Ω_{ξ+1}; uncountable indices such as Ω_{Ω_ω}; what blocks these four: no order comparison is proved between trio matrices and InaccPsi terms with an uncountable inner argument or index. The route without matrices maps terms straight to fan-free patterns (native codes): now the point of CH_2 is at least Z_ω = sup_n Z_n, and every pattern whose chain number (the longest chain of pairs linked by the configuration L1p) is at most k−1 lies below the point of CH_k; so a code may use a chain number that grows with the target (RED-TOWER); with one L1p configuration the point of CH_3 is at least Z″\_ω > Z_ω, and with pair blocks (one pair supplies every level, free levels supply the stage) it is at least θ_{Ξ[ω]}(0), the limit over all stages below ω^ω (refereed once); the native bound θ_{Ξ₂}(0) for CH_2 is at least ψ_{Ω₁}(Ω_ω + ω^(θ+ψ_{Ω₂}(ε_{Ω₂+1}))), the first native bound with a proved InaccPsi name, still below υ* (refereed once); now natively the point of CH_2 is at least Θ_1 = ψ_{Ω₁}(Ω_ω + ω^(θ·2)), and the point of CH_3 is past υ*: at least Z″\_ω > θ_{Ξ′\_ω}(0) ≥ υ*, with Ξ′\_ω = ψ_{Ω₂}(Ω_ω + ω^(θ₂+Ω₂)), and by a transfer θ_{Ξ′\_ω}(0) ≥ ψ_{Ω₁}(Ω_ω + ω^(θ₂+Ω₂)) (refereed once); now the counting rule for ψ over the base Ω_ω and the two lemmas on the parameters are proved for every stage below ω^ω, and natively the point of CH_3 is past ψ_{Ω₁}(Ω_ω·ω), the first native bound above the known bounds of other kinds (refereed once; it rests on Theorem GEN-EXT); now Theorem GEN holds for every η, so natively the point of CH_3 is at least ψ_{Ω₁}(Ω_ω·ω^ω) (refereed once); now an element that is ≤₁ to a larger element but lies in no pair supplies free levels without a second pair, so natively the point of CH_3 is at least ψ_{Ω₁}(Ω_ω·ε₀) (refereed once); now a stage label can be a whole code of a lower system, put inside the pair of the pair block, so natively the point of CH_3 is at least ψ_{Ω₁}(Ω_ω·Θ_1), the point of CH_k is at least the (k−2)-fold iterate of T ↦ ψ_{Ω₁}(Ω_ω·T) at Θ_1, and their limit is at least ψ_{Ω₁}(Ω_ω·Ω₁), the least fixed point of that map (refereed once). Now the ordinal side handles stage labels of level Ω₁ (they must carry parameters), but a system of the same code shape with such labels gives nothing new: its labels alone already reach as far, so it is never the first native bound past ψ_{Ω₁}(Ω_ω·Ω₁) (refereed once). Now a stage label can be a point inside the pair of the code (a pair block refers by the reach of its left end to the point of the label's own code, which lies there anyway), and a block with a smaller label is copied by first reflecting the pair at its own left end; so natively, with the one chain number 3, the point of CH_3 is at least ψ_{Ω₁}(Ω_ω·Ω₂) (refereed once). Now the step that had a blocking point (the end point of a stage is the least element of its set over all ordinals, not only over the values of terms) has a second proof (refereed once, so twice in all), and with labels of every finite level and the start of the ω-top the point of CH_3 is at least ψ_{Ω₁}(Ω_ω^2·ω^ω); and with stages coded by regions in which each label gets its own decoration (an element e with e ≤₁ (a value) + (the label's value)), still with the one chain number 3, it is at least ψ_{Ω₁}(ε_{Ω_ω+1}) (refereed once; this refutes the guess that the chain number must grow without bound below ε_{Ω_ω+1}). Now, giving each ε-number above Ω_ω (each "atom") its own unit with one pair, so with chain number 4, the point of CH_4 is at least ψ_{Ω₁}(Ω_{ω+1}); this covers ε_{Ω_ω+1}, the Veblen functions over Ω_ω and the labels below Ω_{ω+1}, and ψ_{Ω₁}(Ω_{ω+1}) = sup_m ψ_{Ω₁}(S_m) with S₁ = Ω_ω, S_{m+1} = ψ_{Ω_{ω+1}}(Ω_ω·S_m) is proved (refereed once). Now, with one more unit for Ω_{ω+1} itself, still with chain number 4, the point of CH_4 is at least ψ_{Ω₁}(Ω_{ω+1} + ψ_{Ω_{ω+1}}(Ω_{ω+1})), which is above ψ_{Ω₁}(Ω_{ω+1}+1) (refereed once). Now the right end of a unit's own pair stands for Ω_{ω+1}, and digit units code the part of the collapse argument above Ω_{ω+1}; still with chain number 4, the point of CH_4 is at least ψ_{Ω₁}(Ω_{ω+1}² + ψ_{Ω_{ω+1}}(Ω_{ω+1}²)), past ψ_{Ω₁}(Ω_{ω+1}·2) (refereed once). Next (refereed once): three general lemmas on the ordinal side for every stage (which stages are good, a cover of the closure by fewer stages, and ψ at a limit stage as the supremum over the good earlier stages; their abstract cores checked in Lean), and the hosting lemmas for tree units (one unit per position value) and for units without pairs for the atoms above Ω_{ω+1}; and the general stage lemma that joins them to the stage systems, whose blocking point is now repaired by a lemma BUMP (every earlier stage lies below an earlier stage in the closure of the current one; refereed once): so the point of CH_4 is at least ψ_{Ω₁}(ε_{Ω_{ω+1}+1}) and at least ψ_{Ω₁}(Ω_{ω+2}), and, with units without pairs that carry inner scopes and sources, at least ψ_{Ω₁}(Ω_{ω+n}) for every n, so every term below ψ_{Ω₁}(Ω_{ω·2}) gets a code for CH_4 (refereed once). New (refereed once): every reading of a value below ψ_{I₀}(0) is a finite tree; the atoms between Ω_ω and ψ_{I₀}(0) are ordered by index, then kind, then argument, so objects can carry their index instead of a multiplicity, for every index, towers of Ω's included; one pair source hosts every scope coded this way, at any depth; but the scheme with nested pairs is not proved: when the objects sit inside the unit pair a fresh code can land above the host objects (a blocking point), and one hosting case (a fresh collapse with a non-empty inner scope whose next host is larger) is open; a hosting graded by a well-founded capacity gives only bounded depth, while past Ω_{ω·2} every depth occurs. Left there: for CH_2, one finite top without L1p that hosts the tops of all n; with chain number 3, codes past ε_{Ω_ω+1} (the region calculus never raises the nesting depth); with chain number 4, past ψ_{Ω₁}(Ω_{ω·2}), where the stage sets need levels and nesting without bound: nested pairs cost one more link at every depth, so codes for CH_5; there the open hosting case is now hosted when sources carry markers in the right order, no capacity graded by depth works, but a capacity for each unit in dictionary order works up to ψ_{Ω₁}(S\*) (refereed once; S\* as in the item on the first inaccessible), and what stands in the way past it is α ≥ Γ₀ (conjecture LEX-SELF) and the placement of fresh codes (refereed once; the conjecture that such codes reach every term below ψ_{Ω₁}(Ω_{Ω₁}) is withdrawn); then Ω_{Ω₁} and the tower of Ω's, which need units for Ω indexed by their own argument codes (the ordinal side of this path is proved: θ₀ = sup_m ψ_{Ω₁}(u_m) with u₁ = Ω₁, u_{m+1} = Ω_{u_m}, refereed once); for CH_2, codes past Θ_1; then the region above Θ_1, then the levels of Ω up to SRO; or a grammar that follows conv, with codes for the collapse arguments too, so that every term below θ₀ gets a code. When this is done it gives the lower bound below θ₀, and it also shows that the first fan needs an inaccessible
    - then the segment from θ₀ to ψ_{Ω₁}(I₀), which needs collapses ψ_{I₀}
    - conv and chains of length 3. Proved (refereed once): for every input, the ≤₂ relation that conv prints has no x <₂ y <₂ z, so no chain of length 3; if conv(M) is a pattern, then by Lemma DOM₂ its point is below the least ≤₁-predecessor of the least chain of length 3. Left: prove that conv(M) is a pattern for standard M. For the closure of the printed relation under Carlson's rules, the absence of chains of length 3 follows from a condition BAR_R (a node that can start a pair and lies between two right ends of another pair is not ≤₁ to the upper one); BAR_R has 0 failures on 12,963 matrices but fails on some non-standard inputs, so its proof must use standardness
  - the first inaccessible: prove that the pattern conv(SRO), SRO = (0,0,0)(1,1,1)(2,1,1)(3,1,0)(2,0,0), has its point at θ₀ = ψ_{Ω₁}(ψ_{I₀}(0)) (conjecture; it is above the patterns of the terms of its fundamental sequence for n ≤ 4, and below the chain pattern CH_2 of the item on the least chain, so it would give m_F > θ₀; both refereed once); find where I₁ is first needed. Where it stands: the point of CH_2 is above ν_C and, by native codes, at least Z_ω and at least Θ_1 = ψ_{Ω₁}(Ω_ω + ω^(θ·2)); natively the point of CH_3 is at least ψ_{Ω₁}(Ω_ω·Ω₂), with the stage labels as points inside the pair of the code (refereed once), at least ψ_{Ω₁}(Ω_ω^2·ω^ω) with stage labels of every finite level (the repaired step refereed twice), and at least ψ_{Ω₁}(ε_{Ω_ω+1}) with regions of label decorations (refereed once); natively the point of CH_4 is at least ψ_{Ω₁}(Ω_{ω+1}), with a unit of one pair for each ε-number above Ω_ω (refereed once), at least ψ_{Ω₁}(Ω_{ω+1} + ψ_{Ω_{ω+1}}(Ω_{ω+1})), with one more unit for Ω_{ω+1} itself (refereed once), and at least ψ_{Ω₁}(Ω_{ω+1}² + ψ_{Ω_{ω+1}}(Ω_{ω+1}²)), with digit units, in which the right end of the unit's own pair stands for Ω_{ω+1} and one digit codes each term of the part of the argument above Ω_{ω+1} (refereed once); natively the point of CH_5 is at least ψ_{Ω₁}(S\*), past ψ_{Ω₁}(Ω_{ω·2}) (refereed once, see below); all far below θ₀ (conjecture: CH_2 is above θ₀). Left: native codes for every term below θ₀, either below CH_2 or, by RED-TOWER, with a chain number that may grow with the term (native codes now reach every term below ψ_{Ω₁}(ε_{Ω_ω+1}) with chain number 3 and every term below ψ_{Ω₁}(Ω_{ω·2}) with chain number 4: the point of CH_4 is at least ψ_{Ω₁}(Ω_{ω+n}) for every n, with tree units, units without pairs that carry inner scopes and sources, three general lemmas for the ordinal side of every stage, and the general stage lemma, whose blocking point is repaired by a lemma BUMP; refereed once). Left: past Ω_{ω·2} (the stage sets need levels and nesting without bound; nested pairs cost one more link at every depth, so CH_5; with objects that carry their index and one pair source for every scope (refereed once), and now sources with markers (refereed once), the hosting case of a fresh collapse with a non-empty inner scope whose next host is larger is hosted when the markers are in the right order; no fixed shape, no capacity graded by depth and no chain number growing with the depth does it (refereed once); now (refereed once) a capacity for each unit, compared in dictionary order (index, kind, a value α, a bound n minus the depth), does it, and gives the first native bound past ψ_{Ω₁}(Ω_{ω·2}): the point of CH_5 is at least ψ_{Ω₁}(S\*), with S\* = e\* + ψ_{Ω_{ω+1}}(e\*) and e\* = Ω_{ω·2} + ψ_{Ω_{ω+2}}(Ω_{ω·2})·ω^ω; past S\* the capacities need α ≥ Γ₀ (conjecture LEX-SELF: α can be read off each unit's own boundary codes; with it CH_5 would reach θ₀, an outline); the one-marker code REP^ρ is set aside; left also the placement of fresh codes when the objects sit inside the unit pair (a blocking point, not repaired); the conjecture up to Ω_{Ω₁} with CH_5 is withdrawn), then Ω_{Ω₁} and the tower of Ω's, with units for Ω indexed by their own argument codes (only an outline, with no ordinal side; on the ordinal side θ₀ = sup_m ψ_{Ω₁}(u_m), u₁ = Ω₁, u_{m+1} = Ω_{u_m}, is proved, refereed once); this gives m_F ≥ θ₀ and so that the first fan needs an inaccessible; and the exact value θ₀ for conv(SRO)
  - Lean: the order type of the terms bounded by X is ψ_{Ω₁}(X); Wilken's systems and the two maps between them and InaccPsi (now only on paper)
    - R₂^C in Lean, and the chain to ν_C: the whole library builds with no sorry; the details are in the Lean files and the git history, the cited axioms on [LEAN.md](Googology/Trans/PoR/InaccPsi/LEAN.md).
      - Proved: ≤₁ and ≤₂ of R₂^C from Carlson 2009, the core, FRAG, Theorem CP, ν_C = T_C < Ω₁ is a restart, υ_{ι(η)} = P(η) = ψ_{Ω₁}(Ω_ω + θ·η), L(ξ) = P(Ω_ω + P'·ξ), and m* = L(0) and every L(n+1) are restarts.
      - Axioms: 97 cited axioms in 20 files (Wilken's two 2007 papers, Wilken 2020, Wilken 2025, Carlson 2009), each audited with no fatal or blocking point; Lean's three standard axioms not counted. Round 86 merged two π axioms on Ω₁·ω^b into one; both are now theorems.
      - Frontier, with no hypothesis: BLK^O, the exact reaches, ENUM-REACH (UPPER and LOWER) and the cap hold at every restart below ι(Γ_{Ω₁+1+ε_{Ω₁+1}^ω}), υ-fixed points included; it comes from gated layers for every code in [ε_{Ω₁+1}, ε_{Ω₁+1}^ω).
      - Place, with no hypothesis: P(Γ_{Ω₁+1+ε_{Ω₁+1}^ω}) < P(Ω₂) < L(0) = m* < L(ω) < L(ω+1); every point below P(Γ_{Ω₁+Ω₁^ω}) has an R₂^C-reach below L(0). Frontiers with codes below Ω₂ lie below ι(Ω₂), so this method cannot reach L(0).
      - Moves, in a window that B_n moves: the lh move at x = ϑ^τ(Ω₁·M + η), Ω₁ ≤ M < ε_{Ω₁+1}; B_n commutes with ϑ^β at countable arguments for every ε-base β, and with ϑ^τ below ε_{Ω₁+1} at every υ-point τ; all with no hypothesis. RtPiComm and RkLhTopE hold if SmPiHom holds.
      - Atoms: ψ_{Ω₂}(0) < s ≤ ψ_{Ω₂}(Ω₂^{Ω₂^{Ω₂}}) moves if every smaller code moves; if E is closed above its own top, ψ_{Ω₂}(Ω₂^{Ω₂^E}) (1 ≤ E < ε_{Ω₂+1}) moves when the codes below it move and a size bound holds, and ψ_{Ω₂}(β + Ω₂^{X₀+Ω₂^E}) when also its offset and base move.
      - ν_C and TC: if UPPER, LOWER and the cap hold at the restarts, then L(ω+1) ≤ ν_C and L(n+1) ≤₁ υ_{L(n+1)·2} for every n. TC holds at every restart left end if the cap, L(ω) ≤₁ L(ω+1) and CL hold.
      - Road T (gwRS.giFam_road): ν_C = L(ω+1), L(ω) <₂ L(ω+1) and the reaches, if UPPER, LOWER and the cap hold at the restarts λ ≥ ι(Γ_{Ω₁+1+ε_{Ω₁+1}^ω}), and CL, EQ, EMB₂ and TC at the remaining left ends hold.
      - Road R (slRoad_W): EQ, TC, EMB₂, T, CL, m* ≤₁ L(1), ν_C = L(ω+1), L(ω) <₂ L(ω+1), if UPPER, LOWER, O(λ) ≤ c(λ), the cap, EQ at the top, the top condition, the move, the supply SlSupW (LC-STRICT gives it) and the gaps above υ_{a+a·ω} (a = m*, L(n+1)) hold.
      - Road E (smRoadE_nu): TC, EMB₂, ν_C = L(ω+1), L(ω) <₂ L(ω+1) and the reaches, if UPPER, LOWER and the cap hold at λ ≥ ι(Γ_{Ω₁+Ω₁^ω}), and EQ, L(ω+1) ≤ ν_C, SmPiHom (SePiHom2 with c_n ≤ τ), T and CL hold.
      - Left 1: the code ε_{Ω₁+1}^ω (needs Lemma IMG for a given term); codes up to ζ_{Ω₁+1}; from there, read codes through ϑ^x(Ω₁·α + β); the tops ϑ^x(Ω₁²·k + …), first failing at ϑ^x(Ω₁²·2); past ι(Ω₂) a new method up to L(0); then UPPER, LOWER, cap in [L(0), L(ω+1)).
      - Left 2: SlSupW and the targets in [υ_{a+a·ω}, L(n+2)) for CL and m* ≤₁ L(1); SmPiHom at arguments ≥ ε_{Ω₁+1} (needs a ψ_{Ω₂}–ϑ₁ link) and at non-υ σ; atoms: the closure condition at an atom, E ≥ ε_{Ω₂+1}, ψ₃-atoms, θ, EQ above θ. Older: Λ_ε…, LIFT, NU-OMEGA, R₂^S.
- BMS → PoR converter conv (a program that turns a Bashicu matrix M into a pattern of resemblance conv(M)). Write ord(P) for the ordinal that a pattern P stands for (the least place where P occurs in R₁⁺ or R₂⁺ = (Ord; 0, +, ≤, ≤₁, ≤₂)). The goal is M < M' ⇔ ord(conv(M)) < ord(conv(M')). Matrices are compared lexicographically; υ₁ = ψ₀(Ω_ω)
  - ✅ M < (0,0,0)(1,1,1) (2-row matrices = pair sequences; ord(conv(M)) = 1 + the ordinal of M): proved on paper and in Lean without sorry, from cited facts only; the Lean proof no longer uses Wilken's JSL 72 paper ([Trans/BMS/PoR/PSS/POR.md](Googology/Trans/BMS/PoR/PSS/POR.md))
  - ✅ (0,0,0)(1,1,1) ≤ M < (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(2,0,0) (3-row matrices = trio sequences, ord(conv(M)) < υ_{ω·ω}; program por/phi3def2.py, [Trans/BMS/PoR/Trio/POR.md](Googology/Trans/BMS/PoR/Trio/POR.md)): order preserved on all standard matrices, proved on paper and refereed (Theorem S, first up to (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(1,1,0)(2,2,1), whose ord is υ_{ω+1}, then on the whole range; [Trans/BMS/PoR/Trio/R2PLUS.md](Googology/Trans/BMS/PoR/Trio/R2PLUS.md)). In this range ord is computed: the <₂-pairs are exactly υ_{ω·k} <₂ υ_{ω·k+1} (k ≥ 1), and inside each block between them ≤₁ is that of R₁⁺ (Theorems A, B). R₂⁺ has two definitions, R₂^C (Carlson's, by coverings; the checking program uses it) and R₂^S (by Σ_n-elementarity); they agree below υ_{ω·ω} (Theorems EQ, EQB). Theorem 2.2 of Wilken 2007 ([W07b]; its proof was only in Wilken 2006, not available) and Cases 2 and 3 of Claim 5.5(b) in [W07b] (only sketched there) are proved on paper and refereed
  - (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(2,0,0) ≤ M < (0,0,0)(1,1,1)(2,2,2): the program gives a pattern, but it breaks the order in this range. For a limit matrix X write X[n] for the n-th term of its fundamental sequence (X[n] < X[n+1]). At 26 limits X (all of them ≥ (0,0,0)(1,1,1)(2,1,1)(3,1,0)(2,1,0)(3,2,1)(4,2,1)(5,2,0)(3,2,1), the first one found), ord(conv(X[n])) does not increase with n: 41 pairs X[n], X[n+1] get the same pattern, 3 pairs are certified in the reverse order, 14 more are certified "≥"
    - ✅ (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(2,0,0) ≤ M < (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(2,0,0)(2,0,0) (ord(conv(M)) < υ_{ω·ω·ω}): order preserved on all standard matrices, and ord(conv(M)) computed, proved on paper and refereed, with the new Lemma FRAG (in R₁⁺, moving several υ-points at once, together with the parameters that depend on them, keeps 0, +, ≤ and ≤₁). The order proof was refereed once; the full proof of FRAG was refereed once (2026-10), and the 6 minor points of the first review are fixed
    - fix the gap at X = 905 (2,0,0) = (0,0,0)(1,1,1)(2,1,0)(3,2,1)(4,2,0)(2,0,0) and at X' = 946 (2,0,0) = (0,0,0)(1,1,1)(2,1,1)(2,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(4,2,0)(2,0,0) (sheet rows 907, 947): ord(conv(X[n])) < ord(R) for all n (R the sheet's reading) is proved on paper and refereed, with no hypothesis (Lemma CF: every standard M < X is ≤ some X[n]; the Shape Lemma for all n; R is covered by Carlson 2009, Lemma 15.11); the same at X'
      - prove sup_n ord(conv(X[n])) = ord(R). Write s = sup_n ord(conv(X[n])) and b = ord(R). Let γ be the least place of the pattern R without its point (it lies above b), γ_n the same for conv(X[n]), and Cov(α) the set of patterns that have a copy below α. Proved and refereed: s = b holds if and only if Cov(γ) is the union of the Cov(γ_n) (Theorem RED2). Left: this equality, neither proved nor refuted, at X and at X'. Its smallest case is at (0,0,0)(1,1,1)(2,0,0), and is open too
      - prove that conv is right on every X[n]. Proved in the direction the fix needs: ord(conv(X[n][k])) < ord(conv(X[n])) for all n, k, at X and X', where X[n][k] is the k-th term of the fundamental sequence of X[n] (Theorem L, given the shape of conv(X[n][k]), checked on 48 + 30 cases). Left: that ord(conv(X[n])) is not too large, i.e. equals sup_k ord(conv(X[n][k])); it is a statement of the same kind as Cov(γ) = the union of the Cov(γ_n)
      - the rule `lastt` (decide `last` inside the new root term in (C2-5-4-1) and (KI-5)) is now in por/phi3def2.py and [por/ALGORITHM-2.md](Googology/Trans/BMS/PoR/Trio/por/ALGORITHM-2.md). It gives conv(X) = R; the fit stays 1057 rows; 0 of the 2,973 matrices of the 7 test sets change; it changes 196 matrices, among them 51 that start (0,0,0)(1,1,1)(2,2,1)(3,1,1). Without it conv broke the order at (0,0,0)(1,1,1)(2,2,1)(3,1,1)(4,1,0)(5,2,1)(6,2,1)(7,2,0); with it, 0 violations on the 69 pairs tested around them
        - prove that the value it gives is exactly the limit (at (0,0,0)(1,1,1)(2,2,1)(3,1,1)(4,1,0)(5,2,1)(6,2,0) and 14 more matrices it is certified below the old value), the strict order on the other 35 changed matrices (only ≤ is certified), and decide the 39 pairs around them that stay undecided
    - find which pattern is wrong at the 26 limits where ord(conv(X[n])) does not increase, and repair the rule (the same happens with and without `lastt`). Examples: at (0,0,0)(1,1,1)(2,2,0)(3,3,1)(4,3,0)(3,3,1)(4,3,0), conv(X[1]) = conv(X[2]) = conv(X[3]); at (0,0,0)(1,1,1)(2,2,1)(3,2,1)(2,2,1)(3,1,1)(4,2,1)(5,2,1), ord(conv(X)) < ord(conv(X[0])) is certified
    - prove that ord(conv(X[n])) increases with n for every limit X from (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(2,0,0) up to (0,0,0)(1,1,1)(2,1,1)(3,1,0)(2,1,0)(3,2,1)(4,2,1)(5,2,0)(3,2,1). Proved for every limit X ≤ (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(2,0,0) (refereed), and below (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(2,0,0)(2,0,0) (from Theorem S there). Checked on the 1,114 limits of the test sets in this range: 3,342 pairs n ≤ 2 certified "<", 7 undecided. Needed: a proof that the certificate of Lemma LL (the "link ladder", refereed: a covering of conv(X[n]) into conv(X[n+1]) with room at the last link gives "<") always exists, and the base case at the bad root of nested limits
    - ord from (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(2,0,0)(2,0,0) (ord υ_{ω·ω·ω}) up. Write the reach of a point for the largest place it is ≤₁ to. The program gives υ_{ω·ω·ω} the reach "top of its block + 2" and (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(3,0,0) (ord υ_{ω^ω}) the reach "top of its block + ω". Proved: for every restart up to the ω-th fixed point of υ the reach is exactly "top of its first block + its offset" (refereed twice), which is the value the program gives on all 25 restarts tested; above it, up to Λ_ε, the reach is exactly "top + O(λ)" with an offset O defined by recursion (refereed once; the program agrees on 13 more restarts). Left: the order proof above (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(2,0,0)(2,0,0), then terms whose head has Ω₂-level structure (needs new ordinal arithmetic)
    - sheet rows that do not fit: 1334/1335/1434/1435 (a level more than the cut chain of the last summand), bare extra up-kids (1490, 1503, 1504, 1515, 1516, 1583), 1582, 569, 1476, 1489, 575, 709, 1409, 1460, 1577; fixed rows 601/718/1348/1401 where the fix and the converter differ
  - M ≥ (0,0,0)(1,1,1)(2,2,2): not tested
  - the whole program: shorten the definition of phi3def2.py (the level-column list, lh₁) and replace its named cases lwpos, lnest, kcross by general rules
- Table of translations into the ordinals
  - DBMS with 3 rows and up
    - surjectivity (the image is known exactly): show that 3-row DBMS has the same ordinal as 3-row BMS
      - prove the upper bound `rkL 2 (cgen 2 (n+2)) ≤ rkL 2 (bgen3 n)` for `n ≥ 2` (then 3-row DBMS and BMS have the same ordinal; the lower bound and `n = 1` are proved)
        - `n = 2`: reduced to one statement (`DBMS/BMS/ThreeRowUpperNC*.lean`, `ThreeRowUpperRP*.lean`; `RPLastShape` is proved)
          - prove `TrioPushStd` (a statement about trio matrices only; `T3nPushStd` follows, `DBMS/BMS/ThreeRowUpperPushBMS.lean`; 0 failures on 48,438 cases). It is a standardness question of the kind koteitan/trio treats as its hard core
- Table of translations between notations
  - extended Buchholz ψ → trio sequences (✅❌❌✅❌❌)
    - preserves the rank: for all of `ψ_0(Λ)`, the image lies in the standard forms of 3-row BMS and preserves the order
      - fix the rules (fixes go on top of `TrioRulesAll`)
        - after Fix nonlast-other2: pairs still out of order after a leaf that shares its value with a lower top (`Ω_{Ω_{ω+2}}` 52, `Ω_{Ω_{Ω_ω}}` 24, `Ω_{Ω_{ω^2+1}}` 22, `Ω_{Ω_{ω^2}}` 8, `Ω_{Ω_{ω+1}}` 6), the mark above rule 6's storey after `Ω_{Ω_{ω^2}}`, and 117 non-standard matrices after `Ω_{Ω_{ω·2}}` ([TRIO-FIX-NONLAST2.md](Googology/Trans/ExBuchholz/BMS/Trio/TRIO-FIX-NONLAST2.md))
        - after Fix L: fix the other levels of the same kind after `Ω_{Ω_Ω}` (`Ω_{ω+1}`, `Ω_{Ω+ω+1}`, `Ω_{Ω+ω·2}`, `Ω_{Ω·2+1}`, `Ω_{Ω·3}`, `Ω_{Ω^2}`, `Ω_{Ω_2·2}`, …) and case K inside a chain (`Ω_{Ω_{Ω_2+1}}` after `Ω_{Ω_{Ω_Ω}}`) ([TRIO-FIX-LASTLEAF.md](Googology/Trans/ExBuchholz/BMS/Trio/TRIO-FIX-LASTLEAF.md))
        - after Fix U2: 22 rule-9 faults remain outside the claimed domain; infinite levels, limit and countable `u` ([TRIO-FIX-U2.md](Googology/Trans/ExBuchholz/BMS/Trio/TRIO-FIX-U2.md))
        - after Fix S: fix `Ω_ω·Ω^2+…`, `Ω_{ω^2}·Ω+Ω_ω·2` and the `Ω_ω+Ω_2+…` family (a lifted copy inside storeys laid by the end-of-unit rule) ([TRIO-FIX-STRETCH.md](Googology/Trans/ExBuchholz/BMS/Trio/TRIO-FIX-STRETCH.md))
        - merge the separate fix patches (`TrioFix*.lean`) into one rule set once they are done
      - for `ψ_0(Ω_2) ≤ α < Λ`, prove that the image of rules 1–10 lies in the standard forms and preserves the order (done for terms whose subscripts are `0` or `1`)
      - prove `CalibRd200` (the rule map of Fix `strip` equals `trioE2` up to reading depth 200; proved up to 100, false at 201; `CalibSt` without a bound is false because of the fuel) ([BMS/Trio/TrioFixStripCalibNo.lean](Googology/Trans/ExBuchholz/BMS/Trio/TrioFixStripCalibNo.lean))
      - prove that the fuel `max 200 (depth of α)` of `TrioFixFuel` is enough for every `α` (more fuel never changes the matrix; checked on the sheet labels and some families)
- Library layout ([Googology/Trans/README.md](Googology/Trans/README.md))
  - `Trans/BMS/common/Cut.lean` still imports `Trans/BMS/ExBuchholz/Commute.lean`, so most of `BMS/common/` depends on extended Buchholz ψ: move the list lemmas (`Chain`, `Col`, `expandL`, `lastOf`, …) out of `ExBuchholz/Basic.lean` and `ExBuchholz/Commute.lean` into `BMS/common/`, so that `common/` imports nothing from `ExBuchholz/`
