[English](README.md) | [Japanese](README-ja.md)

# googology-lean

A Lean 4 library for googology: expansion systems, ordinal notation systems,
and the translations between them.

The question about a googological system — BMS, DBMS, the Y sequence — is
whether every expansion chain terminates. This library answers it once, for
all of them, and each system supplies only what is its own.

## What it proves

| | |
|---|---|
| **Bashicu matrices terminate**, for any number of rows | `Notation.BMS.bms_terminates` |
| the primitive, pair and trio sequences terminate | `primitive_terminates`, `pair_terminates`, `trio_terminates` |
| BMS carries an ordinal measure | `Notation.BMS.bmsEval` |
| **the standard forms of extended Buchholz's ψ are well ordered** | `ExBuchholz.Term.OTLt_wf` |
| distinct standard forms name distinct ordinals | `ExBuchholz.Term.val_inj_of_OT` |
| the notation system is correct: the term order matches the ordinal order | `ExBuchholz.Term.val_lt_val` |
| the fundamental sequence descends | `ExBuchholz.Term.fs_lt` |
| **extended Buchholz terms terminate** | `ExBuchholz.Term.exbOT_terminates` |
| the fundamental sequence keeps a term standard — Buchholz's Lemma 3.3 | `ExBuchholz.Term.OTFS_thm` |
| **a one-row Bashicu matrix names an ordinal, and expansion is its fundamental sequence** | `Trans.BMS.read_expandL` |
| the primitive sequence system terminates, by translation | `Trans.BMS.prim_terminates` |
| **which ordinal a one-row Bashicu matrix names** | `Trans.BMS.bmsOrdEval` |
| that ordinal is below `ψ_0(Ω)` — the ceiling of the primitive sequence system | `Trans.BMS.read_lt_e0`, `Trans.BMS.bmsOrdEval_lt_e0` |
| and every standard form below `ψ_0(Ω)` is named by one | `Trans.BMS.exists_read`, `Trans.BMS.lt_e0_iff_allNil` |
| the fundamental sequence converges below `ψ_0(Ω)` | `Trans.BMS.exists_le_fs` |
| **the standard one-row matrices are exactly the matrices whose term is standard** | `Trans.BMS.std_entries_iff`, `Trans.BMS.exists_bms_of_lt_e0` |
| one-row Bashicu matrices terminate, by translation rather than by labels | `Trans.BMS.bms_one_terminates` |
| the same for one-row DBMS, whose termination is not otherwise proved here | `Trans.DBMS.dbms_one_terminates`, `Trans.DBMS.dbmsOrdEval` |

No `sorry`, and no axiom beyond `propext`, `Classical.choice` and `Quot.sound`.
`Googology.Core` uses none of the three.

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
has its first entry, the one-row reading of a Bashicu matrix as an extended
Buchholz term; `plan.md` says what is still missing there.
