[← Back](README.md) | [English](spec.md) | [Japanese](spec-ja.md)

# Specification

What this library is, how it is laid out, and the rules it is written by.
`README.md` is the entry for someone using the library; this file is for
someone changing it.

## 1. Scope

The library is about **expansion systems**: a type of states, a step indexed
by a natural number, and a set of halting states. The question it answers is
whether every chain of steps reaches a halting state.

Two kinds of object live here and they are not separated, because they are the
same kind of thing:

* systems defined by the googology community — BMS, DBMS, the Y sequence;
* notation systems from the proof-theory literature — extended Buchholz's ψ,
  Rathjen's `T(M)`.

Both are a type of terms with an order and, usually, fundamental sequences.
They differ only in role: one is what we set out to prove terminates, the
other is what we measure it against.

## 2. Layout

```
Googology/
  Core/            expansion systems, standard forms, translations
  Rank.lean        a well-founded system carries an ordinal measure
  Notation/<Name>/ one directory per system
  Trans/<A>/<B>.lean  translations, one file per unordered pair
test/              finite checks, not theorems
```

### Layering rules

1. `Core/` imports nothing outside core Lean, so a mathlib-free project can
   use it.
2. `Notation/X/` never imports `Notation/Y/`. A system knows only itself and
   `Core`.
3. `Trans/` is the only place that imports two systems at once.
4. An unordered pair `{X, Y}` gets **one** file, under the alphabetically
   earlier name, holding both directions and the `Equiv` if there is one.
   `Trans/README.md` indexes them.
5. mathlib is imported per system, by the ones that evaluate into the
   ordinals — never by `Core`.

Rule 2 is what keeps the import graph a DAG. A translation under
`Notation/BMS/` would drag every system BMS translates to into anyone who
imports BMS.

## 3. What a system supplies

The three fields of `Rewrite`, and, for termination, one measure into a type
carrying a well-founded relation. Everything else is inherited. A system that
already has a termination proof elsewhere joins by supplying the fields and a
`Subrelation.wf`; `Notation/BMS` is the worked example.

## 4. Evidence

* A claim in `Googology/` is a Lean theorem with no `sorry` and no axiom
  beyond `propext`, `Classical.choice` and `Quot.sound`.
* `#guard` lines are computations on finitely many cases. They are evidence,
  not proof, and they are kept visibly apart — in `test/` when they are a
  survey, and beside a definition when they are a sanity check on it.
* A definition transcribed from a source says so and names the source. If it
  has not been checked against the source clause by clause, it says that too.

## 5. Naming

* Lean modules and the directories holding them are UpperCamelCase, acronyms
  kept uppercase: `BMS`, `ExBuchholz`. Directories that are not Lean modules
  are lowercase: `test`.
* "Extended X" is `ExX`, not `EX` — `EBuchholz` would read as an initial.
* The `lean_lib` name and its root file must match exactly.

## Constitutions

These govern the documents, not the code.

### C1. The README is for the reader, not the author

`README.md` addresses someone who wants to use the library. It leads with what
the library gives them, how to add it to a project, and what it proves. It
does not open with the plan, the status, or what is left to do.

Notes for whoever is working on the library — the plan, the current state, the
open questions, the reasoning behind a design — go at the **bottom**, under a
quiet heading, or in `spec.md` and `plan.md`. A reader should be able to stop
before that line and have missed nothing they needed.

### C2. Every directory has a README, in both languages

`README.md` in English and `README-ja.md` in Japanese, with the language
switcher and a back link on the first line. The two say the same thing.

### C3. The Japanese is polite

The Japanese documents are written in the です・ます register. No imperatives
at the reader: not 見よ but ご覧ください, not 〜すること but 〜してください.

### C4. Say what is not proved

A table of results says which rows are theorems and which are not. Something
checked only by computation is marked as such, with the size of the check.
Nothing is described as done that is not.

### C5. Commit messages

`vA.B.C/short summary`, then a blank line, then one bullet per change. The
bullets are MECE: no overlap, no restating one change two ways. The patch
version is bumped in `lakefile.toml` in the same commit.

### C6. No paths from outside the repository

A document published here refers to other work by its public URL, never by a
path on the machine it was written on.
