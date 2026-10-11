[← Back](README.md) | [English](spec.md) | [Japanese](spec-ja.md)

# Specification

This file is for someone changing the library. `README.md` is the entry for
someone using it.

## How it fits together

The library keeps one promise: **every ✅ in the README tables is a Lean
theorem.** Three layers keep it.

1. **Common main theorems** (chapter 1). Every notation is measured against the
   same propositions. They are written as the **types** of the fields of Lean
   structures (`NotationGoals`, `OrdGoals`, `TransGoals`). For example,
   injectivity of a translation into the ordinals is exactly the type of the
   field `injective` of `OrdGoals`.
2. **Records.** Each notation or translation has one value of such a structure
   (`Googology/Goals.lean`). A field holding a proof is proved; a proof of the
   wrong type does not build. Proofs of the common shapes come straight from
   shared structures (`Eval`, `Eval.Cofinal`, `StepHom` and so on, 1.3).
3. **The check script** (chapter 2). The audit `test/GoalsAudit.lean` prints,
   for every field of every record, whether it is proved, refuted or open, and
   the axioms the records use. `scripts/check_readme.py` compares that with the
   tables of `README.md` and `README-ja.md`.

```sh
lake env lean test/GoalsAudit.lean > audit.txt
python3 scripts/check_readme.py --audit audit.txt
```

Exit code `0` says that every ✅ in the tables has a Lean proof with no `sorry`
and no axiom beyond the standard three (`propext`, `Classical.choice`,
`Quot.sound`).

Chapter 3 onwards gives the detailed rules for writing records, the layout,
and how to write Lean here.

## 1. Common main theorems

A notation is a `Rewrite`: a set of states $`S`$, one step
$`\mathrm{step} : S \times \mathbb{N} \to S`$ that expands a state at a bracket,
and a set of halted states $`H \subseteq S`$. One expansion step is the relation

```math
b \prec a \iff a \notin H \land \exists k \in \mathbb{N},\ b = \mathrm{step}(a, k).
```

The standard states $`\mathrm{Std} \subseteq S`$ are those reachable from the
generators $`g_0, g_1, \dots`$ by finitely many steps: the least set with
$`g_n \in \mathrm{Std}`$ and $`a \in \mathrm{Std} \Rightarrow \mathrm{step}(a, k) \in \mathrm{Std}`$.
In Lean, `Rewrite.Std` holds the generators and the fact that a step keeps a
state standard.

For BMS and DBMS a standard form is its matrix. Two states with the same
entries are the same standard form: for example, the generator $`g_0 = (0)`$
and $`(0)(1)[0] = (0)`$ are one standard form. So for these notations the
states are the lists of entries, and the columns "injective" of the two
translation tables are about matrices. The systems on the entries are `prim`
and `pairL` (BMS with 1 and 2 rows), `bmsL r` (BMS with `r + 1` rows) and
`dbmsL1` (one-row DBMS). The array systems `bms r` and `dbms r` have the arrays
`Arr r` as states, and an array also holds values outside its matrix. On the
arrays injectivity fails for that reason only (`dbmsOrdEval_not_injective`,
`dbmsHom_not_injective`); this is a fact about the representation, not about
the standard forms.

### Records and the status of a proof

Each main theorem is one field of a record structure. The field has type
`Goal P`, where `P` is the proposition of that main theorem
(`Googology/Core/Goals.lean`).

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

In `proved h`, `h` proves `P`; in `refuted h`, `h` proves its negation. "Not
yet proved" is `todo`. The audit prints it as `open` (`open` is a Lean keyword,
so the constructor is `todo`). The README does not tell refuted from open: both
are an empty cell in the first two tables and ❌ in the third.

A record structure takes the objects its propositions talk about (the systems,
the standard forms, the maps, and so on) as **parameters of the type**, not as
fields. So the proposition behind each field is fixed by the record type and
is visible in the type of the record's declaration. A record may cover a
family. `Idx` is the index type: `Nat` for "every number of rows", `Unit` for
one system. Every proposition is stated for every `i : Idx`. The detailed rules
for writing records are in chapter 3.

Below, each main theorem is given with its proposition, the field of the
record, and its README column id. The column id is the name the audit output
and `check_readme.py` use.

### 1.1 Main theorems of a notation

The columns of the first README table. The records are `NotationGoals` and
`NonStdGoals` (`Googology/Core/Goals.lean`).

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

| column id | README column (en / ja) | field |
|---|---|---|
| `expansion` | expansion defined / 展開の定義 | `NotationGoals.expansion`: `some` is proved, `none` is open |
| `wf` | well-foundedness / 整礎性 | `NotationGoals.wf` |
| `wf-nonstd` | well-foundedness (non-standard) / 整礎性(非標準) | `NonStdGoals.wf` |

#### 1.1.1 Termination

From every standard state, every choice of brackets reaches a halted state:

```math
\forall a_0 \in \mathrm{Std},\ \forall f : \mathbb{N} \to \mathbb{N},\
\exists n,\ a_n \in H \quad\text{where } a_{i+1} = \mathrm{step}(a_i, f(i)) .
```

This is the question the library asks. The record holds it in the equivalent
form of well-foundedness (1.1.2); `Rewrite.Std.wf_iff_terminates` proves the
two equivalent (3.3).

#### 1.1.2 Well-foundedness

The relation $`\prec`$ on the standard states has no infinite descending chain:

```math
\neg \exists (a_i)_{i \in \mathbb{N}} \subseteq \mathrm{Std},\ \forall i,\ a_{i+1} \prec a_i .
```

The field is `NotationGoals.wf : Goal (∀ i, (std i).WF)`; the column id is
`wf`. `Rewrite.Std.WF` says that one step restricted to the standard forms is
well founded (3.3). It follows from well-foundedness on all states,
`Rewrite.WF`, by `Rewrite.Std.wf_of_wf`.

#### 1.1.3 Well-foundedness (non-standard)

The same with $`\mathrm{Std}`$ replaced by all of $`S`$ — for BMS and DBMS,
every array, standard or not:

```math
\neg \exists (a_i)_{i \in \mathbb{N}} \subseteq S,\ \forall i,\ a_{i+1} \prec a_i .
```

It implies well-foundedness, since $`\mathrm{Std} \subseteq S`$. It is a
separate goal because it says that termination does not depend on where the
expansion starts. It only makes sense where the expansion is defined on
non-standard states.

The field is `NonStdGoals.wf`; the column id is `wf-nonstd`. It is a separate
record because the system on all states is a different `Rewrite`. For BMS,
`sys r` is `bms r`, whose states are the standard arrays, and `all r` is
`bmsAll r`, whose states are all arrays. `incl` says that `sys` is `all` on
part of the states; it is a `Prop`, so its map need not compute. A notation
where the column does not apply has no `NonStdGoals` record; its cell is then
empty.

#### 1.1.4 Expansion defined

This column is not a proposition. It is ticked when $`\mathrm{step}`$ is a Lean
function that runs, and it comes with what ties it to its source: for BMS and
DBMS, the theorem $`\mathrm{step} = \mathtt{BM4.expand}`$ on the entries; for the
Y sequence, the comparison with the official program on finitely many cases.

The field is `NotationGoals.expansion`; the column id is `expansion`. `Runs`
is data, and the record holds it, so `enc`, `run` and `halt` must compile.
That is what "a Lean function that runs" means here. `enc` must compile too: a
noncomputable `enc` could hold the whole future of a state, and then any
system would pass. With `halt_iff`, a trivial code such as `Unit` fails.
`Runs` does not ask `enc` to be injective. For BMS the code is the list of
entries, and two arrays with the same entries can differ outside the matrix.

### 1.2 Main theorems of a translation

#### 1.2.1 Translations into the ordinals

The columns of the second README table. A translation into the ordinals is a
map $`o : \mathrm{Std} \to \mathrm{Ord}`$. The record is `OrdGoals`
(`Googology/Goals/Basic.lean`).

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
  cofinal : Goal (∀ i a, (std i).Standard a → ∀ β < o i a,
      ∃ b, (std i).Standard b ∧ (sys i).Rel b a ∧ β ≤ o i b)
  rank : Goal (∀ i, ∃ h : (std i).WF,
      ∀ a (ha : (std i).Standard a), o i a = (std i).rank h a ha)
  order : Goal (∀ i a b, (std i).Standard a → (std i).Standard b →
      (lt i a b ↔ o i a < o i b))
```

**defined** (column id `defined`): $`o`$ is defined. For the matrix notations
it is $`o = \mathrm{val} \circ t`$ for a map $`t`$ into the terms of an ordinal
notation. The record gives `o` as a parameter, so this is always proved.

**injective** (`injective`):

```math
\forall a, b \in \mathrm{Std},\ o(a) = o(b) \Rightarrow a = b .
```

**surjective** (`surjective`): for an explicitly given set of ordinals $`X`$,

```math
\{\, o(a) \mid a \in \mathrm{Std} \,\} = X .
```

The row says which $`X`$: $`\{\alpha \mid \alpha \lt \varepsilon_0\}`$ for
primitive sequences and one-row DBMS, $`C_0(\Lambda)`$ for extended
Buchholz's ψ.

**decreases on expansion** (`decreasing`):

```math
\forall a, b \in \mathrm{Std},\ b \prec a \Rightarrow o(b) < o(a) .
```

**cofinal** (`cofinal`): one expansion step reaches every ordinal below the
value.

```math
\forall a \in \mathrm{Std},\ \forall \beta < o(a),\ \exists b \in \mathrm{Std},\ b \prec a \land \beta \le o(b) .
```

With "decreases on expansion" it gives "equals the rank", and conversely a map
that equals the rank is cofinal (1.3).

**equals the rank** (`rank`): with the rank defined by
$`\mathrm{rank}(a) = \sup_{b \prec a} (\mathrm{rank}(b) + 1)`$,

```math
\forall a \in \mathrm{Std},\ o(a) = \mathrm{rank}(a) .
```

At most one map satisfies it, since the rank depends on nothing but
$`\prec`$.

**order-preserving** (`order`): for the order $`\lt_S`$ the notation puts on
its states,

```math
\forall a, b \in \mathrm{Std},\ a <_S b \iff o(a) < o(b) .
```

In README order the columns are `defined`, `injective`, `surjective`,
`decreasing`, `cofinal`, `rank`, `order`.

#### 1.2.2 Translations between notations

The cells of the third README table. A translation from a notation $`R`$ to a
notation $`Q`$ is a map $`F : S_R \to S_Q`$ between their states. The record is
`TransGoals` (`Googology/Goals/Basic.lean`).

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
the fields are the propositions below word for word. A map defined on part of
the states only, such as extended Buchholz's ψ → trio sequences on the terms
$`\psi_0(\Omega_\alpha)`$, uses a smaller `dom`, and the README says so under
the table. The target is whatever `Q` is: the standard forms, or all states,
as for DBMS `r` rows → BMS `r` rows.

**defined** (`defined`): $`F`$ is defined. The record gives `F`, so this is
always proved.

**preserves expansion** (`preserves`):

```math
\forall a, b \in S_R,\ b \prec_R a \Rightarrow F(b) \prec_Q F(a) .
```

**commutes with expansion** (`commutes`): for some renumbering of brackets
$`\rho : \mathbb{N} \to \mathbb{N}`$,

```math
\forall a \in S_R,\ \forall k \in \mathbb{N},\
F(\mathrm{step}_R(a, k)) = \mathrm{step}_Q(F(a), \rho(k)),
\qquad F(a) \in H_Q \Rightarrow a \in H_R .
```

It implies the previous column.

**injective** (`injective`):

```math
\forall a, b \in S_R,\ F(a) = F(b) \Rightarrow a = b .
```

**surjective** (`surjective`):

```math
\forall c \in S_Q,\ \exists a \in S_R,\ F(a) = c .
```

**preserves the rank** (`rank`):

```math
\forall a \in S_R,\ \mathrm{rank}_Q(F(a)) = \mathrm{rank}_R(a) .
```

The six marks of a cell are, in this order, `defined`, `preserves`,
`commutes`, `injective`, `surjective`, `rank`.

### 1.3 Proofs from shared parts

Some fields follow from shared structures that do not depend on the details of
a notation. A notation builds one value of such a structure and gets the proof
of the field.

| part | what it holds | fields it gives |
|---|---|---|
| `Rewrite.WF` (`Core/Rewrite.lean`) | one step is well founded | 1.1.2 well-foundedness (through `Rewrite.Std.wf_of_wf`) |
| `Eval R lt` (`Core/Morphism.lean`) | a value `val` and the descent `val_lt` | 1.2.1 defined and decreases on expansion; well-foundedness too, by `Eval.wf` |
| `Eval.Cofinal e` (`Googology/Cofinal.lean`) | one step reaches every ordinal below the value | 1.2.1 cofinal (`Eval.Cofinal.std`); equals the rank too, by `Eval.Cofinal.rank_eq` |
| `StepHom R Q` (`Core/Morphism.lean`) | a map sending one step to one step, with a renumbering of brackets | 1.2.2 preserves and commutes with expansion; preserves the rank too, by `StepHom.rank_map`, when the renumbering is onto and halting agrees |
| `Equiv R Q` (`Core/Morphism.lean`) | a `StepHom` both ways | 1.2.2 injective and surjective |

`Eval.Cofinal` and the rank are tied by two theorems:

```lean
/-- A cofinal evaluation is the rank. -/
theorem Eval.Cofinal.rank_eq {R : Rewrite} [IsWellFounded R.State R.Rel]
    {e : Eval R (· < · : Ordinal.{0} → Ordinal.{0} → Prop)} (hc : e.Cofinal) :
    ∀ a, IsWellFounded.rank R.Rel a = e.val a

/-- An evaluation that is the rank is cofinal. -/
theorem Eval.cofinal_of_rank_eq {R : Rewrite} [IsWellFounded R.State R.Rel]
    (e : Eval R (· < · : Ordinal.{0} → Ordinal.{0} → Prop))
    (he : ∀ a, IsWellFounded.rank R.Rel a = e.val a) : e.Cofinal
```

Primitive and pair sequences prove cofinality first (`primEval_cofinal`,
`pairOrdEval_cofinal`) and get "equals the rank" by `Eval.Cofinal.rank_eq`.

A field that is not in one of these shapes (injective, surjective and
order-preserving for translations into the ordinals, and so on) is filled with
the notation's own theorem, adapted to the field's type inside the record.

## 2. The check script

### 2.1 How to run it

Get the audit from `test/GoalsAudit.lean` and pass it to
`scripts/check_readme.py`:

```sh
lake env lean test/GoalsAudit.lean > audit.txt
python3 scripts/check_readme.py --audit audit.txt [--root DIR]
```

Any runner that passes the output of `#eval` through gives the audit, for
example `leanman check -C . test/GoalsAudit.lean > audit.txt`.

* `--audit FILE` (required): a file holding the audit output. `-` reads
  standard input. The script does not run Lean.
* `--root DIR`: the directory holding `README.md` and `README-ja.md`. The
  default is the parent of the directory the script is in.

It reads three files and writes none. It never changes `README.md` or
`README-ja.md`, and it has no option to do so. The README is not generated:
its tables are written by hand, like the rest of the file.

### 2.2 The audit output

`test/GoalsAudit.lean` does two things:

1. `#eval Googology.AuditLine.printAll Googology.Goals.audit`
2. a command that prints the axioms of `Googology.Goals.audit`, obtained with
   `Lean.collectAxioms`.

`Googology.Goals.audit` is the list of the lines of every record (3.5). A line
is the `AuditLine` of `Googology/Core/Goals.lean`:

```lean
structure AuditLine where
  table : String      -- "notation", "ordinal" or "between"
  record : String     -- the full Lean name of the record
  rowEn : String
  rowJa : String
  targetEn : String   -- "" unless table = "between"
  targetJa : String   -- "" unless table = "between"
  column : String     -- a column id of chapter 1
  status : Status

def AuditLine.render : AuditLine → String
def AuditLine.printAll : List AuditLine → IO Unit
```

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

### 2.3 Reading the audit

The script reads the lines whose first field is `GOALS-BEGIN`, `GOAL`,
`GOALS-END` or `GOALS-AXIOMS`, and ignores every other line. The audit is
valid when all of these hold:

* `GOALS-BEGIN` appears once, with version `1`. `GOALS-END` and
  `GOALS-AXIOMS` appear once each. The number after `GOALS-END` equals the
  number of `GOAL` lines.
* Every `GOAL` line has 9 fields. `<table>` is `notation`, `ordinal` or
  `between`. `<column>` is a column id of that table (chapter 1). `<status>`
  is `proved`, `refuted` or `open`. Row labels are not empty. Target labels
  are non-empty exactly when `<table>` is `between`.
* In each table, the English label decides the Japanese label and the other
  way round: no English label goes with two Japanese labels, and no Japanese
  label with two English labels. In the table `between`, source labels and
  target labels are checked as one set.
* No `between` line has `targetEn` equal to `rowEn`.
* Every axiom in `GOALS-AXIOMS` is `propext`, `Classical.choice` or
  `Quot.sound`.

### 2.4 Reading the README

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
| `ordinal` | `notation`, `defined`, `injective`, `surjective`, `decreases on expansion`, `cofinal`, `equals the rank`, `order-preserving` | `表記`, `定義`, `単射性`, `全射性`, `展開で値が下がる`, `共終性`, `階数と一致`, `順序を保つ` |
| `between` | first cell `from \\ to` (two backslashes, as in the source) | first cell `翻訳元＼翻訳先` (U+FF3C) |

The `notation` and `ordinal` tables are found by the whole header row. The
`between` table is found by its first header cell; its other header cells
are the target labels. Each of the three tables appears exactly once in each
file. The first cell of each row is its label, and no label appears twice in
one table.

A cell is compared after removing spaces, U+FE0F (the emoji variation
selector) and footnote markers `(*n)` with `n` a number, such as `✅(*1)`. The
footnote itself is written under the table. The allowed forms are:

* tables `notation` and `ordinal`: empty or `✅` (U+2705);
* table `between`: empty, `—` (U+2014), or exactly six characters each `✅`
  or `❌` (U+274C).

### 2.5 Rows, cells and marks

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

### 2.6 Mismatches (exit 1)

For each file, with the labels of its language:

1. A cell is not in an allowed form.
2. A cell differs from the mark of 2.5.
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
README-ja.md:35: ordinal: row "1 行の DBMS": column injective: expected "✅", found ""
```

that is, file, line number, table, row label, column id (and, in the table
`between`, the target label), the expected text and the text found. All
mismatches are printed, not only the first.

### 2.7 Exit codes

| code | meaning |
|---|---|
| `0` | the audit is valid and both files agree with it |
| `1` | at least one mismatch |
| `2` | the files cannot be compared: a file cannot be read, the audit is not valid, a table is missing or appears twice, a row has the wrong number of cells, or a label appears twice. The reason goes to standard error. |

### 2.8 What neither Lean nor the script checks

Exit code `0` says that every mark in the tables is what the records say. The
parameters of a record are part of each statement, and neither Lean nor the
script can tell whether they are the intended ones. A reviewer checks them.
The audit prints each record's Lean name so that it can be found.

* `std i` is the standard forms of chapter 1, or the README says what it is.
* `all i` in `NonStdGoals` is the largest set of states the rule is defined on.
* `X` and `lt` in `OrdGoals` are defined without `o`. (With `X i := Set.range`
  of `o`, or `lt a b := o a < o b`, the column would be proved for nothing.)
* `dom` is all states unless the README notes otherwise.
* `Runs.source` is true.

## 3. Writing records

### 3.1 Files

| file | holds | imports |
|---|---|---|
| `Googology/Core/Goals.lean` | `Rewrite.Std.WF`, `Status`, `Goal`, `Runs`, `Incl`, `NotationGoals`, `NonStdGoals`, `AuditLine` | `Googology.Core.Std`, `Googology.Core.Morphism` only |
| `Googology/Rank.lean` | `Rewrite.Std.wf_of_terminates`, `Rewrite.Std.wf_iff_terminates`, `Rewrite.rank`, `Rewrite.Std.rank`, `Rewrite.Std.rank_eq` | `Googology.Core` and mathlib |
| `Googology/Cofinal.lean` | `Eval.Cofinal`, `Eval.Cofinal.rank_eq`, `Eval.cofinal_of_rank_eq`, `Eval.Cofinal.std` | `Googology.Rank` only |
| `Googology/Goals/Basic.lean` | `OrdGoals`, `TransGoals` | `Googology.Core.Goals`, `Googology.Rank` |
| `Googology/Goals.lean` | the concrete records and the list `Googology.Goals.audit` | `Googology.Goals.Basic`, the notations and translations it needs |
| `test/GoalsAudit.lean` | prints the audit | `Googology.Goals`, `Lean` |
| `scripts/check_readme.py` | the check | Python 3 standard library only |

`Googology/Core.lean` imports `Googology.Core.Goals`. `Googology.lean` imports
`Googology.Goals`. `"GoalsAudit"` is in the `globs` of the `Test` library in
`lakefile.toml`. So `lake build` builds the records and runs the audit. A
record that does not compile, or an audit that cannot be evaluated, fails the
build.

`Googology/Goals.lean` is the only module besides the root that imports
notations and translations together for this purpose. No module under
`Core/`, `Notation/` or `Trans/` imports it.

### 3.2 Rules for record types

* A record type takes the objects its propositions talk about as
  **parameters of the type**, not as fields. Its fields are only labels,
  `Goal` values and data that must run.
* So a record is computable even when its systems are not. `bms` and `dbms`
  are `noncomputable`. A value of type `NotationGoals bms bmsStd` whose fields
  are strings and `Goal` values compiles, since the systems appear only in its
  type. This was checked on Lean v4.30.0.
* Records are `def`, never `noncomputable def`.
* A record never contains `sorry` (5.3). The audit prints the axioms the
  records use, and the script rejects any axiom outside `propext`,
  `Classical.choice` and `Quot.sound` (2.3).

### 3.3 Well-foundedness and rank on the standard forms

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

`S.WF` is the well-foundedness of 1.1.2, and `S.Terminates` (in
`Core/Std.lean`) the termination of 1.1.1. The chain in `S.Terminates` starts
at a standard state; the later states are standard by `step_std`.

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

### 3.4 The functions that print audit lines

Each record type has a function `lines (g) (name : String) : List AuditLine`
that gives one line per column of the record: `NotationGoals` two
(`expansion`, `wf`), `NonStdGoals` one (`wf-nonstd`), `OrdGoals` seven,
`TransGoals` six. `name` is the record's Lean name, written with a name
literal so that a wrong name does not compile:

```lean
bmsNotation.lines (toString ``Googology.Goals.bmsNotation)
```

These functions must be `@[macro_inline]`. A plain or `@[inline]` function
that takes the record also takes its system as an implicit argument, and the
compiler then refuses it when the system is `noncomputable`
(`failed to compile definition ... depends on 'Notation.BMS.bms'`). With
`@[macro_inline]` the call is expanded first and the system is dropped. This
was checked on Lean v4.30.0.

To add a main-theorem column: add a field to the record structure, add a line
to this function, add the column id and the header to `check_readme.py`, and
add the column to the README tables.

### 3.5 The concrete records

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
| ω-Y (official) / ω-Y（公式） | `omegaYSys`, `omegaYStd`, `Idx := Unit`; `omegaYSys_wf`; `Runs` with `Code := List Nat`, `run := expand`, `halt := List.isEmpty`, `source` naming `test/OmegaYCheck.lean` and its 474 expansions | `all := omegaYAll` (every list; an error of the rule steps to `()`), `Incl` from `stdSim`, `omegaYAll_wf` |
| extended Buchholz's ψ / 拡張ブーフホルツ ψ | `exbOT` with `exbOTStd`; `exbOT_wf`; `Runs` with `run X n := fs X (idx X n)` on terms | none |

The records of the second and third tables reproduce the current marks.
`results.md` names the theorems. The records of one-row DBMS use `dbmsL1`,
the system on the entries (chapter 1), so "injective" is proved there:
`dbmsL1OrdEval_injective` and `dbmsL1Prim_injective`.

## 4. Layout

```
Googology/
  Core/            expansion systems, standard forms, translations, goal records
  Rank.lean        a well-founded system carries an ordinal measure
  Cofinal.lean     cofinality in a common form (Eval.Cofinal); a cofinal evaluation is the rank
  Notation/<Name>/ one directory per system
  Trans/<A>/<B>/       the translation A → B, one directory per direction
  Trans/<A>/common/    facts about A alone that two or more translations use
  Goals/Basic.lean goal records for translations (1.2)
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
4. The translation `A → B` gets **one** directory `Trans/<A>/<B>/`: the cell
   "A → B" of the README tables, whose goals are proved there. `B → A` goes to
   `Trans/<B>/<A>/`, and a translation inside one family to `Trans/<A>/<A>/`.
   What both directions need goes with the direction that defines it first. A
   file about `A` alone goes to `Trans/<A>/common/` if two or more translations
   use it, and otherwise into the one directory that uses it. Each directory
   has a README; `Trans/README.md` links them.
5. mathlib is imported per system, by the ones that evaluate into the
   ordinals — never by `Core`.
6. `Goals.lean` may import any module. Only the root `Googology.lean` and
   `test/` import it.

Rule 2 is what keeps the import graph a DAG. A translation under
`Notation/BMS/` would drag every system BMS translates to into anyone who
imports BMS.

## 5. Writing a system

### 5.1 Scope

The library is about **expansion systems**: a type of states, a step indexed
by a natural number, and a set of halting states. The question it answers is
whether every chain of steps reaches a halting state (1.1.1).

Two kinds of object live here and they are not separated, because they are the
same kind of thing:

* systems defined by the googology community — BMS, DBMS, the Y sequence;
* notation systems from the proof-theory literature — extended Buchholz's ψ,
  Rathjen's `T(M)`.

Both are a type of terms with an order and, usually, fundamental sequences.
They differ only in role: one is what we set out to prove terminates, the
other is what we measure it against.

### 5.2 What a system supplies

The three fields of `Rewrite`, and, for termination, one measure into a type
carrying a well-founded relation. Everything else is inherited. A system that
already has a termination proof elsewhere joins by supplying the fields and a
`Subrelation.wf`; `Notation/BMS` is the worked example. A measure into the
ordinals is supplied as a value of `Eval` (1.3).

### 5.3 Evidence

* A claim in `Googology/` is a Lean theorem with no `sorry` and no axiom
  beyond `propext`, `Classical.choice` and `Quot.sound`.
* `#guard` lines are computations on finitely many cases. They are evidence,
  not proof, and they are kept visibly apart — in `test/` when they are a
  survey, and beside a definition when they are a sanity check on it.
* A definition transcribed from a source says so and names the source. If it
  has not been checked against the source clause by clause, it says that too.

### 5.4 Naming

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
show what the goal records say (chapter 1). `scripts/check_readme.py`
(chapter 2) compares them with the audit and exits with `0` at every commit. A
change to a record and the matching change to the tables go in the same
commit. The tables are never generated, and the script never rewrites them.
