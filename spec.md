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

## 6. The goals every notation is measured against

A notation is a `Rewrite`: a set of states $`S`$, one step
$`\mathrm{step} : S \times \mathbb{N} \to S`$ that expands a state at a bracket,
and a set of halted states $`H \subseteq S`$. One expansion step is the relation

```math
b \prec a \iff a \notin H \land \exists k \in \mathbb{N},\ b = \mathrm{step}(a, k).
```

The standard states $`\mathrm{Std} \subseteq S`$ are those reachable from the
generators $`g_0, g_1, \dots`$ by finitely many steps: the least set with
$`g_n \in \mathrm{Std}`$ and $`a \in \mathrm{Std} \Rightarrow \mathrm{step}(a, k) \in \mathrm{Std}`$.

### Well-foundedness

The relation $`\prec`$ on the standard states has no infinite descending chain:

```math
\neg \exists (a_i)_{i \in \mathbb{N}} \subseteq \mathrm{Std},\ \forall i,\ a_{i+1} \prec a_i .
```

It is equivalent to **termination**: from every standard state, every choice
of brackets reaches a halted state,

```math
\forall a_0 \in \mathrm{Std},\ \forall f : \mathbb{N} \to \mathbb{N},\
\exists n,\ a_n \in H \quad\text{where } a_{i+1} = \mathrm{step}(a_i, f(i)) .
```

`Rewrite.wf_iff_terminates` proves the two equivalent, so a notation proves
either one.

### Well-foundedness (non-standard)

The same with $`\mathrm{Std}`$ replaced by all of $`S`$ — for BMS and DBMS,
every array, standard or not:

```math
\neg \exists (a_i)_{i \in \mathbb{N}} \subseteq S,\ \forall i,\ a_{i+1} \prec a_i .
```

It implies well-foundedness, since $`\mathrm{Std} \subseteq S`$. It is a
separate goal because it says that termination does not depend on where the
expansion starts. It only makes sense where the expansion is defined on
non-standard states.

### Expansion defined

This column is not a proposition. It is ticked when $`\mathrm{step}`$ is a Lean
function that runs, and it comes with what ties it to its source: for BMS and
DBMS, the theorem $`\mathrm{step} = \mathtt{BM4.expand}`$ on the entries; for the
Y sequence, the comparison with the official program on finitely many cases.

### Translations into the ordinals

A translation into the ordinals is a map $`o : \mathrm{Std} \to \mathrm{Ord}`$.
Each column is ticked when the proposition under its name is proved.

**defined**: $`o`$ is defined. For the matrix notations it is
$`o = \mathrm{val} \circ t`$ for a map $`t`$ into the terms of an ordinal
notation.

**injective**:

```math
\forall a, b \in \mathrm{Std},\ o(a) = o(b) \Rightarrow a = b .
```

**surjective**: for an explicitly given set of ordinals $`X`$,

```math
\{\, o(a) \mid a \in \mathrm{Std} \,\} = X .
```

The row says which $`X`$: $`\{\alpha \mid \alpha \lt \varepsilon_0\}`$ for
primitive sequences and one-row DBMS, $`C_0(\Lambda)`$ for extended
Buchholz's ψ.

**decreases on expansion**:

```math
\forall a, b \in \mathrm{Std},\ b \prec a \Rightarrow o(b) < o(a) .
```

**equals the rank**: with the rank defined by
$`\mathrm{rank}(a) = \sup_{b \prec a} (\mathrm{rank}(b) + 1)`$,

```math
\forall a \in \mathrm{Std},\ o(a) = \mathrm{rank}(a) .
```

At most one map satisfies it, since the rank depends on nothing but
$`\prec`$.

**order-preserving**: for the order $`\lt_S`$ the notation puts on its
states,

```math
\forall a, b \in \mathrm{Std},\ a <_S b \iff o(a) < o(b) .
```

### Translations between notations

A translation from a notation $`R`$ to a notation $`Q`$ is a map
$`F : S_R \to S_Q`$ between their states. Each column is ticked when the
proposition under its name is proved.

**defined**: $`F`$ is defined.

**preserves expansion**:

```math
\forall a, b \in S_R,\ b \prec_R a \Rightarrow F(b) \prec_Q F(a) .
```

**commutes with expansion**: for some renumbering of brackets
$`\rho : \mathbb{N} \to \mathbb{N}`$,

```math
\forall a \in S_R,\ \forall k \in \mathbb{N},\
F(\mathrm{step}_R(a, k)) = \mathrm{step}_Q(F(a), \rho(k)),
\qquad F(a) \in H_Q \Rightarrow a \in H_R .
```

It implies the previous column.

**injective**:

```math
\forall a, b \in S_R,\ F(a) = F(b) \Rightarrow a = b .
```

**surjective**:

```math
\forall c \in S_Q,\ \exists a \in S_R,\ F(a) = c .
```

**preserves the rank**:

```math
\forall a \in S_R,\ \mathrm{rank}_Q(F(a)) = \mathrm{rank}_R(a) .
```

## Constitutions

These govern the documents, not the code.

### C1. The README is for the reader, not the author

`README.md` addresses someone who wants to use the library. It leads with what
the library gives them, how to add it to a project, and what it proves. It
does not open with the plan, the status, or what is left to do.

Notes for whoever is working on the library — the plan, the current state, the
open questions, the reasoning behind a design — go at the **bottom**, under a
quiet heading, or in `spec.md`, `plan.md` and `memo.md`. A reader should be able to stop
before that line and have missed nothing they needed.

### C2. Every directory has a README, in both languages

`README.md` in English and `README-ja.md` in Japanese, with the language
switcher and a back link on the first line. The two say the same thing.

### C3. The Japanese is plain, and never orders the reader about

The Japanese documents are written in the plain 常体 register, tables
included: 〜する or a noun, never 〜します.

That is not licence to command. Not 見よ, not 〜すること, but 〜を参照 or
〜にある — stated as fact. Terse and overbearing are different things.

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

### C7. The plan is a tree of what is left

`plan.md` holds only the tree of what is still to be done. Everything else —
the reasoning, the history, what has been finished, why a route was chosen —
goes to `memo.md`. A finished item is removed from the plan, not ticked.
