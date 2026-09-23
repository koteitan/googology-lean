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
| Y sequence | ✅ | ✅ | ✅ |
| extended Buchholz's ψ | ✅ | ✅ |  |

- expansion defined: the expansion is a Lean function that runs.
- well-foundedness: the expansion relation on the standard forms has no infinite descending chain. It is equivalent to termination — every expansion sequence ends — and that is proved too.
- well-foundedness (non-standard): the same holds on all states, standard or not.
- For the Y sequence, "all states" means every legal sequence: its entries are positive and, if it is not empty, its first entry is `1`. The proof is ported from [koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por) and [koteitan/1y-expand-equiv](https://github.com/koteitan/1y-expand-equiv); see [Notation/Y](Googology/Notation/Y/README.md).

### Translations into the ordinals

A map sending each state to the ordinal it names.

| notation | defined | injective | surjective | decreases on expansion | equals the rank | order-preserving |
|---|:-:|:-:|:-:|:-:|:-:|:-:|
| BMS with at most 2 rows | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| BMS with 3 rows or more |  |  |  |  |  |  |
| one-row DBMS | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| DBMS with 2 rows | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| DBMS with 3 rows or more |  |  |  |  |  |  |
| Y sequence |  |  |  |  |  |  |
| ω-Y |  |  |  |  |  |  |
| extended Buchholz's ψ | ✅ | ✅ | ✅(*1) | ✅ | ✅ | ✅ |

- defined: the map is defined in Lean. For primitive sequences and one-row DBMS it reads the state as an extended Buchholz term and takes its value. For pair sequences it sends the state to a Buchholz term by the `Trans` of [koteitan/pss-proof](https://github.com/koteitan/pss-proof), maps that to an extended Buchholz term, and takes `1 + val` (0 for the empty sequence). For two-row DBMS, a standard form splits into blocks that start with `(0,0)`; the rest of each block is read as a pair sequence `M_i`, and the value is `ω^o(M_0) + ω^o(M_1) + ...`, where `o` is the ordinal of a pair sequence. For extended Buchholz's ψ it is the value of the term.
- injective: distinct standard forms go to distinct ordinals. For BMS and DBMS a standard form is its matrix, so two states are compared as matrices, by their entries.
- surjective: the image is known exactly — the ordinals below `ε₀` for primitive sequences and one-row DBMS, the ordinals below `ψ_0(Ω_ω)` for pair sequences and two-row DBMS, the ordinals below `ψ_0(Λ)` for extended Buchholz's ψ (*1).
- (*1) The states of extended Buchholz's ψ are the standard terms below `Ω`, so the image is not all of `C_0(Λ)` but its part below `Ω`, that is, the ordinals below `ψ_0(Λ)`.
- decreases on expansion: one expansion step makes the value strictly smaller.
- equals the rank: the value is the rank of the expansion (how far expansion can descend). Only one map can do this.
- order-preserving: the order on the states matches the order on the ordinals.

### Translations between notations

| from \\ to | primitive sequences | pair sequences | trio sequences | BMS, `r` rows | BMS, `r+1` rows | one-row DBMS | DBMS, `r` rows | DBMS, `r+1` rows | extended Buchholz's ψ |
|---|:-:|:-:|:-:|:-:|:-:|:-:|:-:|:-:|:-:|
| primitive sequences | — | ✅✅✅✅❌✅ |  |  |  |  |  |  | ✅✅✅✅✅✅ |
| pair sequences |  | — |  |  |  |  |  |  | ✅❌❌✅✅✅(*2) |
| trio sequences |  |  | — |  |  |  |  |  |  |
| BMS, `r` rows |  |  |  | — | ✅✅✅✅❌✅(*4) |  |  |  |  |
| BMS, `r+1` rows |  |  |  |  | — |  |  |  |  |
| one-row DBMS | ✅✅✅✅✅✅ |  |  |  |  | — |  |  |  |
| DBMS, `r` rows |  |  |  | ✅✅✅✅❌✅ |  |  | — | ✅✅✅✅❌✅(*3) |  |
| DBMS, `r+1` rows |  |  |  |  |  |  |  | — |  |
| extended Buchholz's ψ |  |  | ✅❌❌✅❌❌ |  |  |  |  |  | — |

- Rows are the source, columns the target. An empty cell is a pair with no translation defined yet.
- The six marks of a cell are, from left to right: defined, preserves expansion, commutes with expansion, injective, surjective, preserves the rank. ✅ is proved, ❌ is not yet.
- BMS `r` rows → BMS `r+1` rows is one map for every `r`. The target of DBMS `r` rows → BMS `r` rows is all arrays, not only standard forms. Extended Buchholz's ψ → trio sequences is a map on the terms of the form `ψ_0(Ω_α)` only.
- defined: the map is defined in Lean. Primitive sequences go to the standard forms below `ψ_0(Ω)`, pair sequences to those below `ψ_0(Ω_ω)`. Primitive sequences → pair sequences, BMS `r` rows → `r+1` rows and DBMS `r` rows → `r+1` rows put a row of zeros underneath. The map into trio sequences is defined for `α < ε₀`. Extended Buchholz's ψ → trio sequences transcribes the map of [koteitan/trio](https://github.com/koteitan/trio). For `α < ε₀` it is proved that the image is a standard form of three-row BMS (`trioMatrix_std`) and that the map preserves and reflects the order (`omegaIndexMatrix_lt_iff`). Rules 1–10 for `ε₀ ≤ α < Λ` are transcribed (`TrioRules.lean`) and checked against the published table. For terms whose subscripts are `0` or `1` (all below `ψ_0(Ω_2)`) and whose depth is at most 200, rules 1–10 give standard forms and preserve and reflect the order (`TrioTreeRules.lean`).
- (*2) Pair sequences → extended Buchholz's ψ does not preserve expansion and does not commute with it (refuted). The generator `(0,0)(1,1)` expands with `[0]` to `(0,0)`; they go to `ψ_0(Ω_1)` and `1`, and no term of the fundamental sequence of `ψ_0(Ω_1)` is `1` (`Trans/PSS/Expansion.lean`). But one step goes to one or more steps on the ψ side, and "reached in one or more steps" is preserved and reflected by the map (`pairToExb_transGen_iff`, `Trans/PSS/Steps.lean`). Example: `(0,0)(1,1)[0]` goes to `ψ_0(Ω_1) →[0] ω →[1] 1`. The number of ψ steps has no bound: `(0,0)...(p,p)(p+1,p)[0]` takes exactly `p+1` steps (`pairToExb_steps_unbounded`, `pairToExb_min_steps`).
- (*3) DBMS `r` rows → DBMS `r+1` rows is not surjective (refuted): every image has a bottom row of zeros, but the generator `(0,0)(1,0)(2,1)` does not (`dbmsToSucc_not_surjective`).
- (*4) BMS `r` rows → BMS `r+1` rows is not surjective (refuted): every image has a bottom row of zeros, but the generator `(0,0)(1,1)` does not (`bmsToSucc_not_surjective`).
- preserves expansion: one expansion step goes to one expansion step in the target.
- commutes with expansion: bracket numbers included, expanding and then translating gives the same as translating and then expanding.
- injective, surjective: onto the standard forms of the target. Primitive sequences → extended Buchholz's ψ is both, so the two systems are one system written two ways. One-row DBMS → primitive sequences is both too: the standard one-row DBMS matrices are the primitive sequences.
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
    Y/               the Y sequence, and the ported proof of its termination
  Trans/           translations between two systems
```

Each directory has its own README.

## Build

```sh
lake build
```

Lean 4 v4.30.0. Three dependencies: mathlib,
[koteitan/bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) for
the BMS termination proof, and
[koteitan/pss-proof](https://github.com/koteitan/pss-proof) for the
translation `Trans` of pair sequences. `Googology.Core` imports none of them, so the
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
| [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean) (Apache-2.0), revision `6533b29` | the combinatorial layer of the proof that 1-Y is well founded, adapted in koteitan/1y-wo-por and ported here to Lean 4.30.0 | `Notation/Y/WellOrder/ZeroY/`, `Notation/Y/WellOrder/OneY/` |
| p進大好きbot, [ペア数列の停止性](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/%E3%83%9A%E3%82%A2%E6%95%B0%E5%88%97%E3%81%AE%E5%81%9C%E6%AD%A2%E6%80%A7); Naruyoko, [ペア数列システムの停止性証明に用いられた変換写像の全単射性](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:Naruyoko/%E3%83%9A%E3%82%A2%E6%95%B0%E5%88%97%E3%82%B7%E3%82%B9%E3%83%86%E3%83%A0%E3%81%AE%E5%81%9C%E6%AD%A2%E6%80%A7%E8%A8%BC%E6%98%8E%E3%81%AB%E7%94%A8%E3%81%84%E3%82%89%E3%82%8C%E3%81%9F%E5%A4%89%E6%8F%9B%E5%86%99%E5%83%8F%E3%81%AE%E5%85%A8%E5%8D%98%E5%B0%84%E6%80%A7) | the translation `Trans` of pair sequences into Buchholz terms and its bijectivity, as formalized in the dependency koteitan/pss-proof | `Googology/Trans/PSS/` |
| the wiki articles [ペア数列数](https://googology.fandom.com/ja/wiki/%E3%83%9A%E3%82%A2%E6%95%B0%E5%88%97%E6%95%B0) and [Y数列](https://googology.fandom.com/ja/wiki/Y%E6%95%B0%E5%88%97) | background and correspondence tables | `memo.md` |

The transcription in `Notation/Y/Yukito.lean` is a translation of `script.js`
into Lean. `Naruyoko/YNySequence` has no license file.

## License

MIT. See [LICENSE](LICENSE).

The files under `Googology/Notation/Y/WellOrder/ZeroY/`, `Googology/Notation/Y/WellOrder/OneY/`
and `Googology/Notation/Y/WellOrder/Por/` are the exception: they come from
[koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por) and are licensed under the
Apache License 2.0. See [LICENSE-APACHE](LICENSE-APACHE) and [NOTICE](NOTICE).

---

## For contributors

* [spec.md](spec.md) — how the library is laid out and how it is written,
  including the rules that govern these documents
* [plan.md](plan.md) — the tree of what is left to do
* [memo.md](memo.md) — the whole argument and where the work has got to

Current state: `Core/` is complete. `Notation/ExBuchholz` is finished, as a
notation system and as an expansion system: its termination is proved with
nothing assumed. `Notation/BMS` terminates for every number of rows.
`Notation/Y` terminates, on the standard forms and on every legal sequence. `Trans/`
settles one row and two rows (pair sequences): for every matrix the value of
the translation equals the rank of the expansion, and the systems reach `ε₀`
and `ψ_0(Ω_ω)`. There is no reading from three rows on; `plan.md` lists what is
still missing.
