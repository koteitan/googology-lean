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
  Core/            expansion systems, standard forms, translations, goal records
  Rank.lean        a well-founded system carries an ordinal measure
  Notation/<Name>/ one directory per system
  Trans/<A>/<B>.lean  translations, one file per unordered pair
  Goals/Basic.lean goal records for translations (section 7)
  Goals.lean       the goal records of this library and the audit
test/              finite checks, not theorems; GoalsAudit.lean prints the audit
scripts/           check_readme.py compares the README tables with the audit
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
6. `Goals.lean` may import any module. Only the root `Googology.lean` and
   `test/` import it.

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

## 7. Goal records and the README check

Section 6 fixes one proposition per column of the README tables. This
section says how the library records, as Lean values, which of those
propositions are proved, and how a script checks that the tables of
`README.md` and `README-ja.md` say the same.

The README is not generated. Its tables are written by hand, like the rest of
the file. The script only reads it and reports differences.

### 7.1 Files

| file | holds | imports |
|---|---|---|
| `Googology/Core/Goals.lean` | `Rewrite.Std.WF`, `Status`, `Goal`, `Runs`, `Incl`, `NotationGoals`, `NonStdGoals`, `AuditLine` | `Googology.Core.Std`, `Googology.Core.Morphism` only |
| `Googology/Rank.lean` (additions) | `Rewrite.Std.wf_of_terminates`, `Rewrite.Std.wf_iff_terminates`, `Rewrite.rank`, `Rewrite.Std.rank`, `Rewrite.Std.rank_eq` | as now |
| `Googology/Goals/Basic.lean` | `OrdGoals`, `TransGoals` | `Googology.Core.Goals`, `Googology.Rank` |
| `Googology/Goals.lean` | the concrete records and the list `Googology.Goals.audit` | `Googology.Goals.Basic`, the notations and translations it needs |
| `test/GoalsAudit.lean` | prints the audit | `Googology.Goals`, `Lean` |
| `scripts/check_readme.py` | the check | Python 3 standard library only |

`Googology/Core.lean` imports `Googology.Core.Goals`. `Googology.lean` imports
`Googology.Goals`. `"GoalsAudit"` is added to the `globs` of the `Test`
library in `lakefile.toml`. So `lake build` builds the records and runs the
audit. A record that does not compile, or an audit that cannot be evaluated,
fails the build.

`Googology/Goals.lean` is the only module besides the root that imports
notations and translations together for this purpose. No module under
`Core/`, `Notation/` or `Trans/` imports it.

### 7.2 Well-foundedness on the standard forms

In `Googology/Core/Goals.lean`:

```lean
/-- One step, restricted to the standard forms, is well founded. -/
def Rewrite.Std.WF {R : Rewrite} (S : R.Std) : Prop :=
  WellFounded (fun b a : {s // S.Standard s} => R.Rel b.1 a.1)

theorem Rewrite.Std.wf_of_wf {R : Rewrite} (S : R.Std) : R.WF → S.WF
theorem Rewrite.Std.terminates_of_wf {R : Rewrite} (S : R.Std) : S.WF → S.Terminates
```

In `Googology/Rank.lean`, because the converse builds a descending chain from
a state that is not accessible, and that uses mathlib's
`not_acc_iff_exists_descending_chain`:

```lean
theorem Rewrite.Std.wf_of_terminates {R : Rewrite} (S : R.Std) : S.Terminates → S.WF
theorem Rewrite.Std.wf_iff_terminates {R : Rewrite} (S : R.Std) : S.WF ↔ S.Terminates
```

`S.WF` is the well-foundedness of section 6: no infinite descending chain
inside $`\mathrm{Std}`$. `S.Terminates` (already in `Core/Std.lean`) is its
termination. The chain in `S.Terminates` starts at a standard state; the
later states are standard by `step_std`.

Also in `Googology/Rank.lean`, the ranks that the columns "equals the rank"
and "preserves the rank" use:

```lean
/-- The rank of one step, on all states. It is `(Rewrite.rankEval h).val`. -/
noncomputable def Rewrite.rank {R : Rewrite} (h : R.WF) : R.State → Ordinal.{0}

/-- The rank of one step restricted to the standard forms. -/
noncomputable def Rewrite.Std.rank {R : Rewrite} (S : R.Std) (h : S.WF) :
    (a : R.State) → S.Standard a → Ordinal.{0}

/-- On a standard state the two ranks agree. -/
theorem Rewrite.Std.rank_eq {R : Rewrite} (S : R.Std) (h : R.WF)
    (a : R.State) (ha : S.Standard a) :
    S.rank (S.wf_of_wf h) a ha = Rewrite.rank h a
```

`Rewrite.Std.rank_eq` holds because every step of a standard state is
standard. It lets the existing theorems, stated with
`IsWellFounded.rank R.Rel`, fill the rank columns.

### 7.3 Proved, refuted, not yet proved

```lean
inductive Status where
  | proved | refuted | todo

/-- `"proved"`, `"refuted"`, `"open"`. -/
def Status.token : Status → String

/-- Where a record stands on one proposition. -/
inductive Goal (P : Prop) : Type where
  | proved (h : P)
  | refuted (h : ¬ P)
  | todo

def Goal.status {P : Prop} : Goal P → Status
```

"Not yet proved" is `Goal.todo`. The audit prints it as `open` (`open` is a
Lean keyword, so the constructor is `todo`). A proof of the negation is
`Goal.refuted`. The README does not tell refuted from open: both are an empty
cell in the first two tables and ❌ in the third.

A record never contains `sorry` (section 4). The audit prints the axioms the
records use, and the script rejects any axiom outside `propext`,
`Classical.choice` and `Quot.sound` (7.7).

### 7.4 The records

Every record type takes the objects that its propositions talk about as
**parameters of the type**, not as fields: the systems, the standard forms,
the maps, and so on. Its fields are only labels, `Goal` values and data that
must run. This has two effects.

* The proposition behind each column is fixed by the record type. It is
  visible in the type of the record's declaration.
* A record is computable even when its systems are not. `bms` and `dbms` are
  `noncomputable`. A value of type `NotationGoals bms bmsStd` whose fields are
  strings and `Goal` values compiles, since the systems appear only in its
  type. This was checked on Lean v4.30.0.

A record may cover a family. `Idx` is the index type: `Nat` for "every
number of rows", `Unit` for one system. Every proposition is stated for every
`i : Idx`.

Records are `def`, never `noncomputable def`.

#### Notations: `NotationGoals`, `NonStdGoals` (in `Core/Goals.lean`)

```lean
/-- The expansion runs: `run` computes one step on codes, and `halt` decides
halting on codes. -/
structure Runs (R : Rewrite) where
  Code : Type
  enc : R.State → Code
  run : Code → Nat → Code
  halt : Code → Bool
  enc_step : ∀ s k, enc (R.step s k) = run (enc s) k
  halt_iff : ∀ s, halt (enc s) = true ↔ R.halted s
  /-- What ties `run` to the source, e.g. the theorem `step = BM4.expand` on
  the entries, or the number of cases checked against the official program. -/
  source : String

/-- `R` is `Q` on part of its states: the same rule on more states. -/
structure Incl (R Q : Rewrite) where
  map : R.State → Q.State
  map_inj : ∀ a b, map a = map b → a = b
  map_step : ∀ s k, map (R.step s k) = Q.step (map s) k
  map_halted : ∀ s, Q.halted (map s) ↔ R.halted s

structure NotationGoals {Idx : Type} (sys : Idx → Rewrite)
    (std : (i : Idx) → (sys i).Std) where
  labelEn : String
  labelJa : String
  expansion : Option ((i : Idx) → Runs (sys i))
  wf : Goal (∀ i, (std i).WF)

structure NonStdGoals {Idx : Type} (sys all : Idx → Rewrite) where
  labelEn : String
  labelJa : String
  incl : ∀ i, Nonempty (Incl (sys i) (all i))
  wf : Goal (∀ i, (all i).WF)
```

Columns of the first table:

| column id | README column (en / ja) | from |
|---|---|---|
| `expansion` | expansion defined / 展開の定義 | `NotationGoals.expansion`: `some` is proved, `none` is open |
| `wf` | well-foundedness / 整礎性 | `NotationGoals.wf` |
| `wf-nonstd` | well-foundedness (non-standard) / 整礎性(非標準) | `NonStdGoals.wf` |

"Expansion defined" is not a proposition (section 6). `Runs` is data, and
the record holds it, so `enc`, `run` and `halt` must compile. That is what
"a Lean function that runs" means here. `enc` must compile too: a
noncomputable `enc` could hold the whole future of a state, and then any
system would pass. With `halt_iff`, a trivial code such as `Unit` fails.
`Runs` does not ask `enc` to be injective. For BMS the code is the list of
entries, and two arrays with the same entries can differ outside the matrix.

"Well-foundedness (non-standard)" is a separate record, because the system
on all states is a different `Rewrite`. For BMS, `sys r` is `bms r`, whose
states are the standard arrays, and `all r` is `bmsAll r`, whose states are
all arrays. `incl` says that `sys` is `all` on part of the states; it is a
`Prop`, so its map need not compute. A notation where the column does not
apply has no `NonStdGoals` record; its cell is then empty.

#### Translations into the ordinals: `OrdGoals` (in `Goals/Basic.lean`)

```lean
structure OrdGoals {Idx : Type} (sys : Idx → Rewrite)
    (std : (i : Idx) → (sys i).Std)
    (o : (i : Idx) → (sys i).State → Ordinal.{0})
    (X : Idx → Set Ordinal.{0})
    (lt : (i : Idx) → (sys i).State → (sys i).State → Prop) where
  labelEn : String
  labelJa : String
  injective : Goal (∀ i a b, (std i).Standard a → (std i).Standard b →
      o i a = o i b → a = b)
  surjective : Goal (∀ i, {α | ∃ a, (std i).Standard a ∧ o i a = α} = X i)
  decreasing : Goal (∀ i a b, (std i).Standard a → (std i).Standard b →
      (sys i).Rel b a → o i b < o i a)
  rank : Goal (∀ i, ∃ h : (std i).WF,
      ∀ a (ha : (std i).Standard a), o i a = (std i).rank h a ha)
  order : Goal (∀ i a b, (std i).Standard a → (std i).Standard b →
      (lt i a b ↔ o i a < o i b))
```

Columns of the second table:

| column id | README column (en / ja) | from |
|---|---|---|
| `defined` | defined / 定義 | always proved: the record gives `o` |
| `injective` | injective / 単射性 | `injective` |
| `surjective` | surjective / 全射性 | `surjective` |
| `decreasing` | decreases on expansion / 展開で値が下がる | `decreasing` |
| `rank` | equals the rank / 階数と一致 | `rank` |
| `order` | order-preserving / 順序を保つ | `order` |

#### Translations between notations: `TransGoals` (in `Goals/Basic.lean`)

```lean
structure TransGoals {Idx : Type} (R Q : Idx → Rewrite)
    (dom : (i : Idx) → (R i).State → Prop)
    (F : (i : Idx) → (R i).State → (Q i).State) where
  sourceEn : String
  sourceJa : String
  targetEn : String
  targetJa : String
  preserves : Goal (∀ i a b, dom i a → dom i b →
      (R i).Rel b a → (Q i).Rel (F i b) (F i a))
  commutes : Goal (∃ ρ : Idx → Nat → Nat, ∀ i,
      (∀ a k, dom i a → dom i ((R i).step a k) ∧
        F i ((R i).step a k) = (Q i).step (F i a) (ρ i k)) ∧
      (∀ a, dom i a → (Q i).halted (F i a) → (R i).halted a))
  injective : Goal (∀ i a b, dom i a → dom i b → F i a = F i b → a = b)
  surjective : Goal (∀ i c, ∃ a, dom i a ∧ F i a = c)
  rank : Goal (∀ i, ∃ (hR : (R i).WF) (hQ : (Q i).WF),
      ∀ a, dom i a → Rewrite.rank hQ (F i a) = Rewrite.rank hR a)
```

`dom` is the set of states the map is about. With `dom i := fun _ => True`
the fields are the propositions of section 6 word for word. A map defined on
part of the states only, such as extended Buchholz's ψ → trio sequences on
the terms $`\psi_0(\Omega_\alpha)`$, uses a smaller `dom`, and the README
says so under the table. The target is whatever `Q` is: the standard forms,
or all states, as for DBMS `r` rows → BMS `r` rows.

The six marks of a cell of the third table, in this order:

| column id | README meaning (en / ja) | from |
|---|---|---|
| `defined` | defined / 定義 | always proved: the record gives `F` |
| `preserves` | preserves expansion / 展開を保つ | `preserves` |
| `commutes` | commutes with expansion / 展開と可換 | `commutes` |
| `injective` | injective / 単射性 | `injective` |
| `surjective` | surjective / 全射性 | `surjective` |
| `rank` | preserves the rank / 階数を保つ | `rank` |

#### What Lean does not check

The parameters of a record are part of each statement, and Lean cannot tell
whether they are the intended ones. A reviewer checks them. The audit prints
each record's Lean name so that it can be found.

* `std i` is the standard forms of section 6, or the README says what it is.
* `all i` in `NonStdGoals` is the largest set of states the rule is defined on.
* `X` and `lt` in `OrdGoals` are defined without `o`. (With `X i := Set.range`
  of `o`, or `lt a b := o a < o b`, the column would be proved for nothing.)
* `dom` is all states unless the README notes otherwise.
* `Runs.source` is true.

### 7.5 Rows and cells

A record names its README row by its labels. A label is the text of the
README cell exactly as it stands in the Markdown source, with spaces at both
ends removed. Backticks are part of the label: ``BMS, `r` rows``. A label
contains no `|`, no tab and no line break. `labelEn`, `sourceEn` and
`targetEn` are labels in `README.md`; `labelJa`, `sourceJa` and `targetJa`
are labels in `README-ja.md`.

In the third table, `source` is the row and `target` is the column. Its
column headers are the same labels as its rows, in the same order.

Several records may name the same row, or the same cell of the third table.
For example, "BMS with at most 2 rows" is one record for one row and one for
two rows. The mark for a row (or cell) and a column is:

* ✅ if at least one record names it and every one of them has status
  `proved`;
* otherwise, in the first two tables, empty;
* otherwise, in the third table, ❌ when at least one record names the cell.

A cell of the third table that no record names is empty. The diagonal cells
of the third table are `—`. A README row that no record names has every cell
empty, apart from the diagonal.

### 7.6 The concrete records

`Googology/Goals.lean` defines one `def` per record, in the namespace
`Googology.Goals`, and the list

```lean
def Googology.Goals.audit : List AuditLine
```

that concatenates the lines of every record. With the current README, the
first table comes from these records:

| row (en / ja) | `NotationGoals` | `NonStdGoals` |
|---|---|---|
| BMS / BMS | `bms`, `bmsStd`, `Idx := Nat`; `wf` from `bms_wf`; `Runs` on `entriesR` with `expandRL` (`entriesR_expand`). If that needs `0 < r`, the family is `r ↦ bms (r + 1)` | `all := bmsAll`, `Incl` by `Subtype.val`, `bmsAll_wf` |
| DBMS / DBMS | `dbms`, `dbmsStd`; `dbms_wf`; `Runs` as for BMS | `all := bmsAll`, `bmsAll_wf` |
| Y sequence / Y 数列 | `ySys`, `yStd`, `Idx := Unit`; `ySys_wf`; `Runs` with `Code := List Nat`, `run := expand`, `halt := List.isEmpty`, `source` naming `test/YCheck.lean` and its 213 expansions | `all := yLegal`, `Incl` from `stdSim`, `yLegal_wf` |
| extended Buchholz's ψ / 拡張ブーフホルツ ψ | `exbOT` with a new `exbOT.Std`; `exbOT_wf`; `Runs` with `run X n := fs X (idx X n)` on terms | none |

The records of the second and third tables reproduce the current marks.
`results.md` names the theorems. One-row DBMS "injective" is
`Goal.refuted`, from `dbmsOrdEval_not_injective`.

### 7.7 The audit output

`Googology/Core/Goals.lean` defines the line and how it is printed:

```lean
structure AuditLine where
  table : String      -- "notation", "ordinal" or "between"
  record : String     -- the full Lean name of the record
  rowEn : String
  rowJa : String
  targetEn : String   -- "" unless table = "between"
  targetJa : String   -- "" unless table = "between"
  column : String     -- a column id of 7.4
  status : Status

def AuditLine.render : AuditLine → String
def AuditLine.printAll : List AuditLine → IO Unit
```

Each record type has a function `lines (g) (name : String) : List AuditLine`
that gives one line per column of the record: `NotationGoals` two
(`expansion`, `wf`), `NonStdGoals` one (`wf-nonstd`), `OrdGoals` and
`TransGoals` six each. `name` is the record's Lean name, written with a
name literal so that a wrong name does not compile:

```lean
bmsNotation.lines (toString ``Googology.Goals.bmsNotation)
```

These functions must be `@[macro_inline]`. A plain or `@[inline]` function
that takes the record also takes its system as an implicit argument, and the
compiler then refuses it when the system is `noncomputable`
(`failed to compile definition ... depends on 'Notation.BMS.bms'`). With
`@[macro_inline]` the call is expanded first and the system is dropped. This
was checked on Lean v4.30.0.

`test/GoalsAudit.lean` does two things:

1. `#eval Googology.AuditLine.printAll Googology.Goals.audit`
2. a command that prints the axioms of `Googology.Goals.audit`, obtained with
   `Lean.collectAxioms`.

Its standard output is text in UTF-8, one line per record and column:

```
GOALS-BEGIN	1
GOAL	<table>	<record>	<rowEn>	<rowJa>	<targetEn>	<targetJa>	<column>	<status>
…
GOALS-END	<number of GOAL lines>
GOALS-AXIOMS	<axiom>,<axiom>,…
```

* Fields are separated by one tab. There are exactly 9 fields in a `GOAL`
  line. `targetEn` and `targetJa` are empty unless `<table>` is `between`.
* `<status>` is `proved`, `refuted` or `open`.
* `1` after `GOALS-BEGIN` is the version of this format.
* `GOALS-AXIOMS` lists the full names of the axioms, sorted, separated by
  commas, with no spaces. It may be empty.
* The order of the `GOAL` lines carries no meaning.
* Any other line (messages of Lean, of `lake`, of a runner) may appear
  before, between or after these lines. A reader ignores it.

The audit is produced by running `test/GoalsAudit.lean`:

```sh
lake env lean test/GoalsAudit.lean > audit.txt
```

or by any runner that passes the output of `#eval` through, for example
`leanman check -C . test/GoalsAudit.lean > audit.txt`.

### 7.8 The check script

```sh
python3 scripts/check_readme.py --audit audit.txt [--root DIR]
```

* `--audit FILE` (required): a file holding the audit output. `-` reads
  standard input. The script does not run Lean.
* `--root DIR`: the directory holding `README.md` and `README-ja.md`. The
  default is the parent of the directory the script is in.

It reads three files and writes none. It never changes `README.md` or
`README-ja.md`, and it has no option to do so.

#### Reading the audit

The script reads the lines whose first field is `GOALS-BEGIN`, `GOAL`,
`GOALS-END` or `GOALS-AXIOMS`, and ignores every other line. The audit is
valid when all of these hold:

* `GOALS-BEGIN` appears once, with version `1`. `GOALS-END` and
  `GOALS-AXIOMS` appear once each. The number after `GOALS-END` equals the
  number of `GOAL` lines.
* Every `GOAL` line has 9 fields. `<table>` is `notation`, `ordinal` or
  `between`. `<column>` is a column id of that table (7.4). `<status>` is
  `proved`, `refuted` or `open`. Row labels are not empty. Target labels are
  non-empty exactly when `<table>` is `between`.
* In each table, the English label decides the Japanese label and the other
  way round: no English label goes with two Japanese labels, and no Japanese
  label with two English labels. In the table `between`, source labels and
  target labels are checked as one set.
* No `between` line has `targetEn` equal to `rowEn`.
* Every axiom in `GOALS-AXIOMS` is `propext`, `Classical.choice` or
  `Quot.sound`.

#### Reading the README

Each file is read as UTF-8. Lines inside fenced code blocks (between lines
starting with ```` ``` ````) are skipped.

A table is a header line starting with `|`, a delimiter line whose cells all
match `:?-+:?`, and the following lines that start with `|`. It ends at the
first line that does not start with `|`. To split a line into cells, remove
the first `|` and, if present, the last `|`, split on `|`, and remove spaces
at both ends of each cell. Every row has as many cells as the header.

The three tables are found by their header rows, not by headings, so the
headings may change. In the source text:

| table | `README.md` header | `README-ja.md` header |
|---|---|---|
| `notation` | `notation`, `expansion defined`, `well-foundedness`, `well-foundedness (non-standard)` | `表記`, `展開の定義`, `整礎性`, `整礎性(非標準)` |
| `ordinal` | `notation`, `defined`, `injective`, `surjective`, `decreases on expansion`, `equals the rank`, `order-preserving` | `表記`, `定義`, `単射性`, `全射性`, `展開で値が下がる`, `階数と一致`, `順序を保つ` |
| `between` | first cell `from \\ to` (two backslashes, as in the source) | first cell `翻訳元＼翻訳先` (U+FF3C) |

The `notation` and `ordinal` tables are found by the whole header row. The
`between` table is found by its first header cell; its other header cells
are the target labels. Each of the three tables appears exactly once in each
file. The first cell of each row is its label, and no label appears twice in
one table.

A cell is compared after removing spaces and U+FE0F (the emoji variation
selector). The allowed forms are:

* tables `notation` and `ordinal`: empty or `✅` (U+2705);
* table `between`: empty, `—` (U+2014), or exactly six characters each `✅`
  or `❌` (U+274C).

#### Mismatches (exit 1)

For each file, with the labels of its language:

1. A cell is not in an allowed form.
2. A cell differs from the mark of 7.5.
3. A row that the audit names is not in the table. In the table `between`,
   this includes a target label that is not a column header.
4. In the table `between`, the column headers are not the row labels in the
   same order, or a diagonal cell is not `—`.

Between the two files:

5. A table has a different number of rows in `README.md` and in
   `README-ja.md`.
6. The `n`-th rows of a table in the two files are one row. If the audit
   names either of them, the audit's English–Japanese pair must be exactly
   these two labels.

Each mismatch is printed on standard output as one line:

```
README-ja.md:42: ordinal: row "1 行の DBMS": column injective: expected "", found "✅"
```

that is, file, line number, table, row label, column id (and, in the table
`between`, the target label), the expected text and the text found. All
mismatches are printed, not only the first.

#### Exit codes

| code | meaning |
|---|---|
| `0` | the audit is valid and both files agree with it |
| `1` | at least one mismatch |
| `2` | the files cannot be compared: a file cannot be read, the audit is not valid, a table is missing or appears twice, a row has the wrong number of cells, or a label appears twice. The reason goes to standard error. |

`0` says that every mark in the tables is what the records say. It says
nothing about the parameters listed in "What Lean does not check".

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

### C8. The README tables agree with the audit

The three tables of `README.md` and `README-ja.md` are written by hand. They
show what the goal records say (section 7). `scripts/check_readme.py`
compares them with the audit and exits with `0` at every commit. A change to
a record and the matching change to the tables go in the same commit. The
tables are never generated, and the script never rewrites them.
