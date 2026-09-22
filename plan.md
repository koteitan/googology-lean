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
| `Eval.lean` | done — `val`, `Lam`, `val_mem_CSet`, the two `ψ` comparison helpers |
| `Mono.lean` | done — the simultaneous induction, `val_lt_val`, `OTLt_wf` |
| `FS.lean` | done — `dom`, `fs`, `fs_lt`, `dom_eq_one_or_tw`, `step_lt`, `exb` |
| `Closure.lean` | done — Buchholz 3.4, 3.5, 3.6, the Bachmann property, and 3.3 from it: `bachmann`, `OTFS_thm`, `Trian_fs_thm` |
| `System.lean` | done — `exbOT` on the countable standard forms, `exbOT_wf`, `exbOT_terminates` |

**`ExBuchholz` is finished**: `OTLt_wf` says the order on its standard forms
is well founded with no hypothesis, and `exbOT_terminates` says the expansion
system on the countable ones ends, also with no hypothesis. What is not proved
is that `val` is onto the ordinals below `Λ`; the injective half is
`val_inj_of_OT`.

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
`ε_n`,
`RankVal.lean` says the rank of the system is that same ordinal and computes
the first two-row ranks, and `Append.lean` says expansion never reaches back
across a block, which makes the rank additive over blocks.

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

What is left of that is the Lean problem still open.

* **`val` is onto above `ε_ω`.** The source states that `val` restricted to
  `OT` is an order **isomorphism** onto `C_0(Λ)`. The monotone and injective
  half is here — `val_lt_val` and `val_inj_of_OT` — and surjectivity is proved
  below every `ε_n`: `Trans.BMS.exists_OT_of_lt_epsN`, by induction on `n`,
  with `exists_OT_of_lt_eps0` (Cantor normal form) as its base and the leading
  term `ψ_0(Ω·(n+1) + B)` as its step, `OT_cons_OmegaTerm` being the
  standard-form condition there. The arithmetic it rests on is
  `Ord.psi_OmegaMul_add` — `ψ_0(Ω·(n+1) + a) = ε_n·ω^a` up to `ε_{n+1}` — and
  `Ord.psi_OmegaMul`, that `ψ_0(Ω·(n+1))` **is** `ε_n`; the recursion
  decreases by `Ord.log_lt_self_of_lt_epsN_succ`, since between `ε_n` and
  `ε_{n+1}` the only fixed point of `ω ^ ·` would be `ε_{n+1}` itself.
  `Trans.BMS.existsUnique_OT_lt_teN` packages it as a bijection onto the
  ordinals below `ψ_0(Ω·(n+1))` at every `n`. `ε₀` and `ε₁` are the cases
  `n = 0` and `n = 1`, and `teN 0` and `teN 1` are `te0` and `te1` on the
  nose. `Trans.BMS.existsUnique_OT_lt_teW` takes it to the limit: `val` is a
  bijection onto the ordinals below `ε_ω`, which the term
  `teW = ψ_0(ψ_1(1))` names.

  The arithmetic above `ε₁` no longer has to be climbed a level at a time.
  `Notation/ExBuchholz/Eps.lean` proves `ψ_0(Ω·(n+1)) = ε_n` at every finite
  `n` at once — `Ord.psi_OmegaMul`, with `Ord.psi_OmegaMul_add` for
  `ψ_0(Ω·(n+1) + a) = ε_n·ω^a` below `ε_{n+1}` — by one strong induction on
  `n` rather than by repeating the `ε₀`, `ε₁` proofs. What carries it is
  `Ord.decomp`: a member of `C_0(Ω·(n+1))` below that bound is `Ω·k + c` with
  `k ≤ n` and `c < ε_n`, because a sum adds the `Ω·k` parts and `ε_n` swallows
  the rest, a collapse `ψ_0(Ω·k + c)` is bounded by `ε_{k-1}·ω^c < ε_n`, and a
  collapse with a nonzero subscript is already past `Ω·(n+1)` unless it is
  `ψ_1(0) = Ω` itself. The two values `Opow.lean` proves by hand are the cases
  `n = 0` and `n = 1` of it.

  The finite ladder is not the end of it either. `Notation/ExBuchholz/Ladder.lean`
  replaces it by the ε function: `Ord.eps γ` is `Ordinal.deriv (ω ^ ·) γ`, and
  `Ord.psi_Omega_mul_eps` says `ψ_0(Ω·(1+γ)) = ε_γ` at **every** `γ` below
  `ζ₀`, the first fixed point of `ε`, with `Ord.psi_Omega_mul_add_eps` for
  `ψ_0(Ω·(1+γ) + β) = ε_γ·ω^β` below `ε_{γ+1}`. The upper bound
  `Ord.psi_Omega_mul_le` holds at every `γ` with no condition at all.

  What carries the transfinite step, where the finite ladder needed a
  decomposition of the closure, is ordinal division by `Ω`.
  `Ord.mod_Omega_lt_eps` is the whole induction: every member of
  `C_0(Ω·(1+γ))` has `x % Ω < ε_γ`. The collapse clause reads its argument as
  `Ω·δ + β` by dividing, so the recursion at `δ` and the bound on `β` are both
  in hand, and a collapse with a nonzero subscript is additively principal and
  at least `Ω`, so its remainder is `0` — nothing has to be known about which
  ordinals `ψ_1` reaches. The other direction needs `Ω·(1+γ)` to be inside the
  closure, which `Ord.Omega_mul_mem_CSet` supplies from Cantor normal form and
  `Ord.psi_one_eq`: `Ω·ω^e` is `ψ_1(e)`.

  `ζ₀` is where it stops, and for a reason rather than for want of a proof:
  building `Ω·(1+ζ₀)` inside the closure needs `ζ₀`, which is exactly the
  value being collapsed to. `Ord.eps_Omega_one` — `ε_Ω = Ω` — says `ζ₀` is
  countable, so the condition is the only one. Past `ζ₀`, `ψ_0(Ω^2)` is `ζ₀`
  itself and the arguments need `ψ_1` inside them. What would settle that is a
  normal form theorem, and its first step is in: `Ord.principal_mem_CSet` says an additively principal member of
  `C_v(a)` is below `Ω_v` or a collapse `ψ_u(e)` with `u` and `e` in the
  closure. The second step is in too:
  `Ord.exists_principal_split` peels a leading principal off any member, with
  a smaller member behind it. What is left is the recursion that turns each
  `ψ_u(e)` into a term, which is the hard part. `e` may be larger than the
  ordinal being named, so the recursion cannot be on the ordinal alone; and
  the argument is not determined by the value either. `Ord.psi_eps0` and
  `Ord.psi_Omega_one` say `ψ_0` takes `ε₀` at `ε₀` and at `Ω` alike, and it
  is `Ω` that the standard form uses, because `Ω` lies in its own closure and
  `ε₀` does not. So the recursion has to choose the argument by that
  condition, not by taking the least one. Higher up the normal form is not
  Cantor's: it needs `ψ` at every subscript, so the induction that builds a
  term has to know which arguments each `ψ_v` reaches, which is `C_v` again.

The other two are not Lean problems.

* **A reading for two rows and up.** It needs a stated definition of the map
  from matrices to ordinals. The sources checked give worked values, not a
  rule, and a rule guessed to fit them is not worth committing. The rank
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
* **The Y sequence.** Its official definition is a program and its
  termination is open; see item 4.

## Conventions

* every claim is a Lean theorem with no `sorry` and no added axiom;
* `#guard` lines are computations on small cases, not theorems, and are kept
  visibly separate;
* `Core` never imports mathlib; a notation system imports it only when it
  evaluates into the ordinals.
