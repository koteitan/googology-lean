[English](README.md) | [Japanese](README-ja.md)

# googology-lean

A Lean 4 library for googology: expansion systems, ordinal notation systems,
and the translations between them.

The question about a googological system — BMS, DBMS, the Y sequence — is
whether every expansion chain terminates. This library answers it once, for
all of them, and each system supplies only what is its own.

## What it proves

Names are written relative to `Googology`.

### The systems

| | |
|---|---|
| **Bashicu matrices terminate**, for any number of rows | `Notation.BMS.bms_terminates` |
| **expansion ends from any array at all**, standard or not | `Notation.BMS.terminates_any` |
| so the rule on every array is a system, well founded and with a rank | `Notation.BMS.bmsAll`, `Notation.BMS.bmsAll_wf`, `Notation.BMS.bmsAllEval` |
| and the same on the entries, where the step runs | `Trans.BMS.bmsAllL`, `Trans.BMS.bmsAllL_wf`, `Trans.BMS.bmsAllLEval` |
| the primitive, pair and trio sequences terminate | `Notation.BMS.primitive_terminates`, `Notation.BMS.pair_terminates`, `Notation.BMS.trio_terminates` |
| BMS carries an ordinal measure | `Notation.BMS.bmsEval` |
| **every Bashicu matrix expansion, written on the entries, is `BM4.expand`** — so it runs, at any number of rows | `Trans.BMS.entriesR_expand` |
| the one-row, two-row and general rules are one rule | `Trans.BMS.expandRL_one`, `Trans.BMS.expandRL_two` |
| and a row of zeros underneath changes nothing, for one row inside two | `Trans.BMS.expand2L_withZero` |
| **the primitive sequence system sits inside the pair sequence system** | `Trans.BMS.primHomPair`, `Trans.BMS.withZero_std` |
| so does `bmsL 0` inside `bmsL 1`, the first step of the hierarchy | `Trans.BMS.bmsL_zero_sim_one` |
| **and a row of zeros underneath changes nothing at every number of rows** | `Trans.BMS.expandRL_zeroRow` |
| so `r + 1` rows sit inside `r + 2`, standard matrices and all matrices | `Trans.BMS.bmsL_homSucc`, `Trans.BMS.bmsAllL_homSucc` |
| and iterating that, `r ≤ s` puts `r + 1` rows inside `s + 1` | `Trans.BMS.bmsL_simLe`, `Trans.BMS.bmsAllL_simLe` |
| **and the ordinal a matrix names does not change when the zero row is added** | `Trans.BMS.rank_zeroRow`, `StepHom.rank_map` |
| the systems on the entries, with their generators | `Trans.BMS.prim`, `Trans.BMS.pairL`, `Trans.BMS.bmsL` |
| the general system at one and two rows is the primitive and pair sequence system | `Trans.BMS.bmsEquivPrim`, `Trans.BMS.pairEquivBms` |
| from a generator, any expansion sequence ends | `Notation.BMS.bmsStd_terminates`, `Notation.DBMS.dbmsStd_terminates`, `Trans.BMS.bmsLStd_terminates` |
| **well-foundedness and termination are the same condition** | `Rewrite.wf_iff_terminates` |
| so every system here is well founded and expansion has a rank | `Trans.BMS.bmsL_wf`, `Trans.BMS.pairL_wf`, `Trans.BMS.prim_wf`, `Trans.BMS.bmsLRankEval` |
| DBMS is the same rule with other generators, and terminates too | `Notation.DBMS.dbms_terminates`, `Trans.DBMS.dbmsL_terminates` |

### Extended Buchholz's ψ

| | |
|---|---|
| **the standard forms are well ordered** | `Notation.ExBuchholz.Term.OTLt_wf` |
| distinct standard forms name distinct ordinals | `Notation.ExBuchholz.Term.val_inj_of_OT` |
| the notation system is correct: the term order matches the ordinal order | `Notation.ExBuchholz.Term.val_lt_val` |
| the fundamental sequence descends | `Notation.ExBuchholz.Term.fs_lt` |
| **extended Buchholz terms terminate** | `Notation.ExBuchholz.Term.exbOT_terminates` |
| the fundamental sequence keeps a term standard — Buchholz's Lemma 3.3 | `Notation.ExBuchholz.Term.OTFS_thm` |
| **`ψ_0(a) = ω^a` below `ε₀`**, and `ψ_0(a) ≤ ω^a` always | `Notation.ExBuchholz.Ord.psi_zero_eq_opow`, `Notation.ExBuchholz.Ord.psi_zero_le_opow` |
| **`ψ_0(Ω) = ε₀`** | `Notation.ExBuchholz.Ord.psi_Omega_one` |

### One row: which ordinal a matrix names

| | |
|---|---|
| **expansion is the fundamental sequence** | `Trans.BMS.read_expandL` |
| **which ordinal a one-row Bashicu matrix names** | `Trans.BMS.bmsOrdEval` |
| it is below `ψ_0(Ω)` — the ceiling of the primitive sequence system | `Trans.BMS.read_lt_e0`, `Trans.BMS.bmsOrdEval_lt_e0` |
| and every standard form below `ψ_0(Ω)` is named by one | `Trans.BMS.exists_read`, `Trans.BMS.lt_e0_iff_allNil` |
| **and every ordinal below `ε₀` is named by one** — `ψ_0(Ω)` is `ε₀` | `Trans.BMS.exists_matrix_of_lt_eps0`, `Trans.BMS.val_te0` |
| so one row names those ordinals and no others | `Trans.BMS.val_read_lt_eps0` |
| `val` is onto the ordinals below `ε₀` | `Trans.BMS.exists_OT_of_lt_eps0` |
| **so the ordinal measure is a bijection onto `ε₀`** | `Trans.BMS.exists_bms_of_lt_eps0`, `Trans.BMS.bmsOrdEval_inj` |
| **the rank of the system is that same ordinal** — the two measures are one | `Trans.BMS.rank_prim_eq_val`, `Trans.BMS.rank_bms_eq_val` |
| the one-row generators name the towers of `ω`: `(0)` is `1`, `(0)(1)` is `ω` | `Trans.BMS.val_twr_succ`, `Trans.BMS.rank_primGen` |
| and small matrices can be read off: `(0)(1)(1)` is `ω²` and `(0)(1)(2)` is `ω^ω`, which settles two duplicated table entries | `Trans.BMS.val_read_one_one`, `Trans.BMS.val_read_one_two` |
| **the rank is the least ordinal measure** — any evaluation bounds it | `Eval.rank_le` |
| one row of DBMS names the same ordinals, and its rank agrees too | `Trans.DBMS.exists_dbms_of_lt_eps0`, `Trans.DBMS.rank_dbms_eq_val` |
| below `ψ_0(Ω)` a term is the least upper bound of its fundamental sequence | `Trans.BMS.fs_lub` |
| **the standard one-row matrices are exactly the matrices whose term is standard** | `Trans.BMS.std_entries_iff`, `Trans.BMS.exists_bms_of_lt_e0` |
| **the primitive sequence system and the standard forms below `ψ_0(Ω)` are equivalent** | `Trans.BMS.primEquivE0` |
| a one-row matrix is determined by the ordinal it names, and is the least upper bound of its own expansions | `Trans.BMS.bmsOrdEval_inj`, `Trans.BMS.expandL_lub` |
| one row terminates, by translation rather than by labels | `Trans.BMS.bms_one_terminates`, `Trans.BMS.prim_terminates` |
| the same for one-row DBMS, whose termination is not otherwise proved here | `Trans.DBMS.dbms_one_terminates`, `Trans.DBMS.dbmsOrdEval` |

### Two rows and up: what the rank reaches

No reading of a two-row matrix is available, so the rank of the expansion
relation is the only ordinal these carry. It can still be computed where the
expansions are understood.

| | |
|---|---|
| **the two-row generator `(0,0)(1,1)` has rank `ε₀`** — two rows start where one row ends | `Trans.BMS.rank_pairGen` |
| and at every number of rows the generator is the limit of the previous row's generators | `Trans.BMS.rank_gen_eq_iSup`, `Trans.BMS.rank_gen_lt` |
| `(0,0)` has rank `1`, so a zero column at the end adds one: `(0,0)(1,1)(0,0)` has rank `ε₀ + 1` | `Trans.BMS.rank_zeroCol`, `Trans.BMS.rank_append_zeroCol`, `Trans.BMS.rank_succAll` |
| **expansion never reaches back across a block** — a column whose row-`0` entry is `0` | `Trans.BMS.expandRL_append` |
| **so the rank is additive over blocks**, and `n` copies of a block have `n` times its rank | `Trans.BMS.rank_appendState`, `Trans.BMS.rank_repNState` |
| **with `m₀ = 0` the expansion is a fixed part and a block repeated**, so the rank is multiplied by `ω` | `Trans.BMS.expandRL_of_m0_zero`, `Trans.BMS.rank_mul_omega0` |
| so `(0,0)(1,0)` has rank `ω`, `(0,0)(1,1)(1,0)` has `ε₀·ω`, and `(0,0)(1,1)(0,0)(1,0)` has `ε₀ + ω` | `Trans.BMS.rank_omegaCol`, `Trans.BMS.rank_omegaAll`, `Trans.BMS.rank_sumAll` |

What it does not reach: `(0,0)(1,1)(2,1)`, where `m₀` is `1` so the copies
are incremented and differ; `(0,0)(1,1)(2,0)`, which does repeat, but repeats
`(1,1)`, and a part that does not start a block carries no rank of its own;
and the later generators.

No `sorry`, and no axiom beyond `propext`, `Classical.choice` and `Quot.sound`.
In `Googology.Core` the only declarations that use any axiom are the six that
conclude `Terminates`: `Rewrite.terminates_of_wf`,
`Rewrite.terminates_of_measure`, `Eval.terminates`, `Sim.terminates`,
`Sim.terminates_transfer` and `Equiv.terminates_iff`. They ask for a state
that halts, given only that no chain descends forever, and that step is
classical. Everything else in `Core` — the relation, well-foundedness, the
measures, and all four morphisms — depends on no axiom at all.

## Using it

Add it to your `lakefile.toml`:

```toml
[[require]]
name = "googology"
git = "https://github.com/koteitan/googology-lean"
```

Then, for instance:

```lean
import Googology

open Googology Notation.BMS

-- Bashicu matrices with five rows terminate.
example : (bms 5).Terminates := bms_terminates 5
```

## The idea

An expansion system packages the state type itself as a field, so systems with
different state types share one proposition:

```lean
structure Rewrite where
  State  : Type
  step   : State → Nat → State
  halted : State → Prop
```

It is a `structure` and not a `class` on purpose: one state type carries
several expansion rules — BMS has BM4, 3.3, 2, 1.1 — and a class keyed on the
state type could hold only one of them.

### Proved once, for every system

| name | statement |
|---|---|
| `Rewrite.terminates_of_wf` | well-foundedness implies termination |
| `Rewrite.wf_of_measure` | a measure into any well-founded order implies well-foundedness |
| `Rewrite.terminates_of_measure` | a measure implies termination |
| `Rewrite.Std.of_terminates` | termination on all states implies it on standard forms |
| `OrdHom.wf` | a strictly monotone map transfers well-foundedness |
| `OrdHom.injective` | trichotomy plus irreflexivity gives injectivity |
| `Sim.wf`, `Sim.terminates` | a simulation transfers well-foundedness and termination |
| `Sim.terminates_transfer` | termination transfers backwards along a simulation |
| `StepHom.toSim` | commuting with expansion yields a simulation |
| `Equiv.wf_iff`, `Equiv.terminates_iff` | mutually inverse translations make both equivalent |
| `Eval.terminates` | an evaluation into a well-founded order gives termination |
| `Eval.compOrd` | an evaluation composed with an order-preserving map is an evaluation |
| `Eval.ofSim` | a simulation pulls an evaluation back to the source |
| `Rewrite.rankEval` | a well-founded system carries an ordinal measure of its own |

The last three are the spine: a translation plus a target evaluation gives
termination of the source, in one line.

```lean
example (trans : Sim Src Tgt) (o : Eval Tgt ltO) (hO : WellFounded ltO) :
    Src.Terminates :=
  (Eval.ofSim trans o).terminates hO
```

## Adding a system

Give the three fields of `Rewrite`, and then, to prove termination, a measure:
a map into any type carrying a well-founded relation — `Nat`, an ordinal, a
term system of your own — that strictly decreases on every step. Everything
else is a theorem you inherit.

If your system already has a termination proof elsewhere, joining takes a few
lines; `Notation/BMS` is the worked example.

## What is in here

```
Googology/
  Core/            expansion systems, standard forms, translations
  Rank.lean        every well-founded system carries an ordinal measure
  Notation/        the systems themselves
    BMS/             Bashicu matrices, any number of rows
    ExBuchholz/      extended Buchholz's ψ
  Trans/           translations between two systems
```

Each directory has its own README.

## Build

```sh
lake build
```

Lean 4 v4.30.0. Two dependencies: mathlib, and
[koteitan/bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) for
the BMS termination proof. `Googology.Core` imports neither, so the
termination machinery can be read and used without mathlib.

## License

MIT. See [LICENSE](LICENSE).

---

## For contributors

* [spec.md](spec.md) — how the library is laid out and how it is written,
  including the rules that govern these documents
* [plan.md](plan.md) — the whole argument and where the work has got to

Current state: `Core/` is complete. `Notation/ExBuchholz` is finished, as a
notation system and as an expansion system: its termination is proved with
nothing assumed. `Notation/BMS` terminates for every number of rows. `Trans/`
settles one row completely — as terms, as ordinals, and as the rank of the
system, which agree — and reaches a few two-row ordinals without a two-row
reading; `plan.md` says what is still missing.
