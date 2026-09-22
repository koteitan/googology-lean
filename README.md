[English](README.md) | [Japanese](README-ja.md)

# googology-lean

A Lean 4 library for googology: expansion systems, ordinal notation systems,
and the translations between them.

The library proves the shared theorems **once**, so that an individual system
only has to supply what is specific to it — usually a single measure.

## Where to start

| | |
|---|---|
| [plan.md](plan.md) | the whole argument and where the work has got to |

## Directory layout

```
Googology/
  Core/            system-independent core; no dependency beyond core Lean
    Rewrite.lean     expansion systems, Rel, WF, Terminates
    Std.lean         standard forms and generators
    Morphism.lean    OrdHom, Sim, StepHom, Equiv, Eval
  Rank.lean        every well-founded system carries an ordinal measure
  Notation/        notation systems; these never import one another
    BMS/             Bashicu matrices, any number of rows
    ExBuchholz/      extended Buchholz's psi
    DBMS/  Y/  ...   not yet
  Trans/           concrete translations; the only layer importing two systems
    BMS/
      DBMS.lean
      Y.lean
      OTB.lean
test/              scaffolding demonstration on invented rules, not on any real system
```

### Layering rules

1. `Core/` depends on nothing but core Lean, so a mathlib-free project can use it.
2. `Notation/X/` never imports `Notation/Y/`. A system knows only itself.
3. `Trans/` is the only place that imports two systems at once.
4. An unordered pair `{X, Y}` gets **one** file, placed under the
   alphabetically earlier name, holding both directions and the `Equiv` if
   there is one. [Trans/README.md](Googology/Trans/README.md) indexes them so
   the file is findable from either side.

Rule 2 is what keeps the import graph a DAG. If a translation lived under
`Notation/BMS/Trans/DBMS.lean`, then importing BMS would drag in DBMS, and
eventually every system.

Systems defined by the googology community and systems from the proof-theory
literature are the same kind of object — a type of terms, an order, fundamental
sequences — so they share one directory. mathlib is imported per system, by the
ones that evaluate into the ordinals.

## The core

An expansion system packages the state type itself as a field, so systems with
different state types inhabit one type and share one proposition.

```lean
structure Rewrite where
  State  : Type
  step   : State → Nat → State
  halted : State → Prop
```

This is a `structure` and not a `class` on purpose: one state type carries
several expansion rules (BMS has BM4, 3.3, 2, 1.1), and a class keyed on the
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
| `Rewrite.rankEval` | a well-founded system carries an ordinal measure of its own (needs mathlib) |

The last two are the spine. Together they turn a translation plus a target
evaluation into termination of the source, in one line:

```lean
example (trans : Sim Src Tgt) (o : Eval Tgt ltO) (hO : WellFounded ltO) :
    Src.Terminates :=
  (Eval.ofSim trans o).terminates hO
```

### What a new system has to supply

The three fields of `Rewrite`, and then, to prove termination, a measure — a
map into any type carrying a well-founded relation (`Nat`, an ordinal, a term
system of your own) that strictly decreases on every step.

## Build

```sh
lake build
```

Lean 4 v4.30.0. Two dependencies: mathlib, and
[koteitan/bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) for
the BMS termination proof.

`Googology.Core` imports nothing outside core Lean, so the whole termination
machinery can be read and used without mathlib. mathlib enters only where a
notation system evaluates into the ordinals — at present
`Googology.Notation.ExBuchholz.Ord`.

## Status

`Core/` is complete. `Notation/ExBuchholz` is finished as a notation system:
`OTLt_wf` needs no hypothesis. `Notation/BMS` terminates for every number of
rows. `Trans/` is empty. Nothing carries a `sorry` or an added axiom.

## License

MIT. See [LICENSE](LICENSE).
