[English](README.md) | [Japanese](README-ja.md)

# googology-lean

A Lean 4 library for googology: expansion systems, ordinal notation systems,
and the translations between them.

The question about a googological system — BMS, DBMS, the Y sequence — is
whether every expansion chain terminates. This library answers it once, for
all of them, and each system supplies only what is its own.

## What it proves

Every notation gets the same goals. They are defined exactly in section 6 of [spec.md](spec.md).

| notation | expansion defined | well-foundedness | well-foundedness (non-standard) |
|---|:-:|:-:|:-:|
| BMS | ✅ | ✅ | ✅ |
| DBMS | ✅ | ✅ | ✅ |
| Y sequence | ✅ |  |  |
| extended Buchholz's ψ | ✅ | ✅ |  |

- expansion defined: the expansion is a Lean function that runs.
- well-foundedness: the expansion relation on the standard forms has no infinite descending chain. It is equivalent to termination — every expansion sequence ends — and that is proved too.
- well-foundedness (non-standard): the same holds on all states, standard or not.
- The well-foundedness of the Y sequence is proved outside this library and only cited.

### Translations into the ordinals

A map sending each state to the ordinal it names.

| notation | defined | injective | surjective | decreases on expansion | equals the rank | order-preserving |
|---|:-:|:-:|:-:|:-:|:-:|:-:|
| primitive sequences | ✅ | ✅ | ✅ | ✅ | ✅ |  |
| one-row DBMS | ✅ |  | ✅ | ✅ | ✅ |  |
| extended Buchholz's ψ | ✅ | ✅ | ✅ | ✅ |  | ✅ |
| BMS with 2 rows or more |  |  |  |  |  |  |
| DBMS with 2 rows or more |  |  |  |  |  |  |
| Y sequence |  |  |  |  |  |  |

- defined: the map is defined in Lean. For primitive sequences and one-row DBMS it reads the state as an extended Buchholz term and takes its value; for extended Buchholz's ψ it is the value of the term.
- injective: distinct standard forms go to distinct ordinals.
- surjective: the image is known exactly — the ordinals below `ε₀` for primitive sequences and one-row DBMS, all of `C_0(Λ)` for extended Buchholz's ψ.
- decreases on expansion: one expansion step makes the value strictly smaller.
- equals the rank: the value is the rank of the expansion (how far expansion can descend). Only one map can do this.
- order-preserving: the order on the states matches the order on the ordinals.

### Translations between notations

| translation | defined | preserves expansion | commutes with expansion | injective | surjective | preserves the rank |
|---|:-:|:-:|:-:|:-:|:-:|:-:|
| primitive sequences → extended Buchholz's ψ | ✅ | ✅ | ✅ | ✅ | ✅ |  |
| one-row DBMS → primitive sequences | ✅ | ✅ | ✅ |  |  |  |
| primitive sequences → pair sequences | ✅ | ✅ | ✅ |  |  |  |
| BMS, `r` rows → BMS, `r+1` rows | ✅ | ✅ | ✅ |  |  | ✅ |
| DBMS, `r` rows → BMS, all arrays with `r` rows | ✅ | ✅ |  |  |  |  |
| `ψ_0(Ω_α)` of extended Buchholz's ψ → trio sequences | ✅ |  |  |  |  |  |

- defined: the map is defined in Lean. Primitive sequences go to the standard forms below `ψ_0(Ω)`. Primitive sequences → pair sequences and BMS `r` rows → `r+1` rows put a row of zeros underneath. The map into trio sequences is defined for `α < ε₀`. The last row transcribes the map of [koteitan/trio](https://github.com/koteitan/trio); it is defined and checked against the correspondence table, nothing more.
- preserves expansion: one expansion step goes to one expansion step in the target.
- commutes with expansion: bracket numbers included, expanding and then translating gives the same as translating and then expanding.
- injective, surjective: onto the standard forms of the target. Primitive sequences → extended Buchholz's ψ is both, so the two systems are one system written two ways.
- preserves the rank: the rank is the same before and after the translation.
- The full list of theorems, including the intermediate lemmas, is in [results.md](results.md).


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
    DBMS/            BMS with other generators
    Y/               the Y sequence
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

## Sources

Material by others that this library uses, and where. Repositories of
koteitan's are linked where they are used and are not listed here.

| source | what is taken from it | where |
|---|---|---|
| [mathlib](https://github.com/leanprover-community/mathlib4) (Apache-2.0) | ordinals, cardinals and the rest of the library it is built on | a dependency, imported outside `Core` |
| BashicuHyudora, [BASIC言語による巨大数のまとめ](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:BashicuHyudora/BASIC%E8%A8%80%E8%AA%9E%E3%81%AB%E3%82%88%E3%82%8B%E5%B7%A8%E5%A4%A7%E6%95%B0%E3%81%AE%E3%81%BE%E3%81%A8%E3%82%81) | the Bashicu matrix system and its version BM4 | `Notation/BMS/`; the rule is implemented in the dependency koteitan/bms-elem-pattern |
| Maksudov's extended Buchholz ψ, as stated on the [Googology Wiki](https://googology.miraheze.org/wiki/Extended_Buchholz%27s_function) | the definition of `ψ_v(a)` and `C_v(a)` | `Notation/ExBuchholz/Ord.lean` |
| p進大好きbot, [拡張Buchholz OCFに伴う順序数表記](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/%E6%8B%A1%E5%BC%B5Buchholz_OCF%E3%81%AB%E4%BC%B4%E3%81%86%E9%A0%86%E5%BA%8F%E6%95%B0%E8%A1%A8%E8%A8%98) | the terms, their order, `G`, `OT`, the evaluation, `dom` and `[ ]`, and the statement that `val` is an isomorphism onto `C_0(Λ)` | `Notation/ExBuchholz/` |
| W. Buchholz, A new system of proof-theoretic ordinal functions, Annals of Pure and Applied Logic 32 (1986) 195–207 | Lemmas 3.2–3.6, on which the fundamental sequences rest | `Notation/ExBuchholz/FS.lean`, `Closure.lean` |
| Yukito's Y sequence, and its official program [`script.js`](https://github.com/Naruyoko/YNySequence/blob/2de13970b9ac818c935577b8284c41dec01f0039/script.js) of Naruyoko/YNySequence (revision `2de1397`) | the definition, transcribed statement by statement; the expected values of the checks | `Notation/Y/Yukito.lean`, `test/YCheck.lean` |
| [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean) (Apache-2.0) | cited only, for the termination of 1-Y; nothing is copied or adapted | `Notation/Y/README.md` |
| the wiki articles [ペア数列数](https://googology.fandom.com/ja/wiki/%E3%83%9A%E3%82%A2%E6%95%B0%E5%88%97%E6%95%B0) and [Y数列](https://googology.fandom.com/ja/wiki/Y%E6%95%B0%E5%88%97) | background and correspondence tables | `plan.md` |

The transcription in `Notation/Y/Yukito.lean` is a translation of `script.js`
into Lean. `Naruyoko/YNySequence` has no license file.

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
