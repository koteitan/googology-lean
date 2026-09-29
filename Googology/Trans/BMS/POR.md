[← the 2-row version](../PSS/POR.md) | [English](POR.md) | [Japanese](POR-ja.md)

# A map $`\Phi_3`$ from trio sequences to additive patterns ($`R_2^+`$) (in progress)

**Status: a partial rule and a record of experiments.** Nothing here is proved or
formalized.

This is a record of an attempt to extend the 2-row map $`\Phi`$ ([PSS/POR.md](../PSS/POR.md)) to a map
$`\Phi_3`$ from 3-row matrices (trio sequences) to Carlson's additive patterns of order 2,
$`R_2^+ = (\mathrm{Ord}; 0, +; \le, \le_1, \le_2)`$.

## 1. Summary

- **Where it works.** From $`(0,0,0)(1,1,1) = \psi_0(\Omega_\omega)`$ up to, but not
  including, $`(0,0,0)(1,1,1)(2,1,0)`$. In $`\psi`$ terms this is
  $`\psi_0(\Omega_\omega \cdot k + \cdots)`$ and $`\psi_0(\Omega_\omega \cdot \omega + \cdots)`$.
  In this range $`\Phi_3`$ agrees with the sheet, and no order violation was found.
- **Beyond.** Adding a second collapse raised the agreement with the sheet. But on
  $`[(0,0,0)(1,1,1)(2,1,0),\ (0,0,0)(1,1,1)(2,1,1))`$ order violations appeared. Their
  causes fall into five kinds (§5).
- **The two-level version** (§6). The case rules were replaced by a recursion with two
  collapses. Agreement with the sheet rose from 444 to 458 rows, and the bad pairs in the
  new range dropped from 19 to 11. Three rules that are not local remain.
- **Rules read from Carlson's definitions** (§7). Two of the three rules became local
  rules with a reason from the definition of $`\le_2`$, and the collapse of nested
  $`\omega`$ columns was fixed. Agreement rose to 468 rows, and both order tests now show 0
  violations.
- **One reflection rule** (§8). Carlson's downward 2-reflection (Def 9.4) gives one rule
  that replaces the third rule and explains more sheet rows. Agreement rose to 503 rows,
  still with 0 violations.
- **Wilken's $`R_2`$ and the undecided pairs** (§9). Wilken's analysis of $`R_2`$ does not
  describe $`R_2^+`$, so it cannot decide the pairs. The oracle with a longer budget
  certified 23 of the 310 undecided pairs and found no violation. Row 844: $`\Phi_{3i}`$ is
  right and the fix table should change. Rows 907 and 1009 are still open.
- **The rows above 915** (§10). $`\Phi_{3k}`$ fills three gaps of $`\Phi_{3i}`$: $`z = 1`$ children of
  $`D`$ on its own level, index columns of level $`\omega + j`$, and the counting of the
  $`\le_2`$-levels. Agreement rose from 504 to 787 rows. The order test shows 0 violations below
  $`(0,0,0)(1,1,1)(2,2,1)`$ and 4 above it, all in root runs and nested frames that the rule
  does not yet describe.
- **Root runs and nested frames** (§11). $`\Phi_{3l}`$ decides where the $`\le_2`$-levels of a limit
  summand go when the root has several summands: its level is at its successor, and its own
  levels come back as its pattern relative to $`x`$, built on the top successor. It also puts the
  witness of a prefix into the last $`\le_2`$-interval. Agreement rose from 787 to 834 rows, and
  both new order tests show 0 violations.
- **The level columns above row 1300** (§12). $`\Phi_{3m}`$ applies the rule "a marker collapses to the
  target of the $`\omega`$ column that owns it" to the children of the level columns, and gives the
  same-level and $`D`$-level $`\omega`$ columns inside them their own levels. Agreement rose from 834 to
  939 rows, and three order tests (up to $`(0,0,0)(1,1,1)(2,2,1)(3,2,1)`$) show 0 violations. Rows 1147,
  1150 and 1151 are certified sheet errors.

## 2. The shape of the rule

As in the 2-row $`\Phi`$, the row-0 parent forest is read as the additive structure. A term
is $`(y, z, \text{children})`$. $`\Phi_3(M)`$ is the closure of $`\{0, 1, M\}`$ under the
following operations.

- root segments, prefix sums, anchor, and the $`\le_1`$-reach $`\mathrm{lh}`$;
- $`\le_2`$-successors and $`\le_2`$-witness nodes.

$`x \le_1 y`$ reads $`x \le y \le \mathrm{lh}(x)`$. The $`\le_2`$ pairs are listed and then
closed. On matrices whose row 2 is all 0, $`\Phi_3`$ equals the 2-row $`\Phi`$.

The main rules added to the 2-row version are these.

- **The last root children are a run of $`z = 1`$ columns.** The 2-row fold $`\oplus`$ is
  applied with a copy one level up. Inside the copy:
  - $`z = 1`$ columns go up one level;
  - $`(y = 1, z = 0)`$ columns collapse to $`N`$;
  - $`y = 0`$ columns stay.
- **$`\le_2`$ pairs.** When the last child $`W`$ has $`z = 1`$ columns below it, followed
  only by leaves, a run of $`\le_2`$-successors appears. Example: sheet row 541 $`\lt_2`$ row
  551.
- **The second collapse.** The subtree of an index column (a $`(y = 1, z = 0)`$ column with
  children) is read relative to the $`\le_2`$-point $`c`$ by the 2-row $`\Phi`$, and the
  resulting nodes are placed inside the $`\le_2`$-interval. The collapse is:

```math
\Omega_\omega \mapsto c,\qquad \Omega_{\omega + \nu} \mapsto \Omega_\nu
```

- **Level bookkeeping.** A $`z = 1`$ child on the same level doubles the $`\le_2`$-reach.
  This part is only partly done.

The implementation is `por/phi3.py`. Flags select the version.

| flags | version |
|---|---|
| `z,dbl` | the first version; it fits the working range (sheet rows 522–754) |
| `z,dbl,idx,lvl,lev` (default) | with the second collapse and part of the level bookkeeping |

## 3. How it was checked

- **The sheet.** The 3-row rows of the spreadsheet "Sheetified Patterns of Resemblance"
  (author unknown). The sheet's patterns are themselves $`\Phi`$-style closures, so the
  structures were compared directly.
  - iso: $`\Phi_3(M)`$ has the same structure as the sheet pattern.
  - sub: the sheet pattern is the restriction of $`\Phi_3(M)`$ to some of its nodes,
    including the point. The oracle then checks
    $`\iota(\Phi_3(M)) \le \iota(\text{sheet})`$. The embedding gives the other direction,
    so the two are equal.
- **The oracle.** A search for certificates built from the rules of Carlson, "Patterns of
  resemblance of order 2" (APAL 158, 2009). It is not complete: some pairs stay undecided.

## 4. Numbers

**Agreement with the sheet** (iso / sub / sup / no)

| sheet rows | first version | current version |
|---|---|---|
| 522–754 | 34 / 187 / 0 / 8 | 34 / 187 / 0 / 8 |
| 755–914 | 27 / 45 / 3 / 83 | 44 / 86 / 1 / 27 |
| 915–1156 | 0 / 0 / 0 / 238 | 25 / 43 / 1 / 169 |
| 1157–1299 | 12 / 9 / 14 / 106 | 12 / 13 / 4 / 112 |
| 1300–1449 | 0 / 0 / 16 / 126 | 0 / 0 / 22 / 120 |
| 1450–1642 | 0 / 0 / 25 / 166 | 0 / 0 / 50 / 141 |

The oracle confirmed the sub rows as equal: 176 of 187 in rows 522–754, and 115 of the
128 new sub rows in 755–1156. The rest timed out.

**Order tests**

| range | matrices | adjacent pairs | "<" certified | violations | same pattern | undecided |
|---|---|---|---|---|---|---|
| $`[(0,0,0)(1,1,1),\ (0,0,0)(1,1,1)(2,1,0))`$ | 1085 | 1084 | 818 | 0 | 0 | 236 |
| $`[(0,0,0)(1,1,1)(2,1,0),\ (0,0,0)(1,1,1)(2,1,1))`$ | 305 | 292 | 141 | 8 | 11 | 133 |

The smallest violation in the new range is the pair below. The left matrix is
lexicographically smaller, but its $`\Phi_3`$ value is at least that of the right one.

```math
\begin{aligned}
&(0,0,0)(1,1,1)(2,1,0)(1,1,1)(1,1,0)(2,2,1)(3,1,0)(4,2,1) \cr
&(0,0,0)(1,1,1)(2,1,0)(1,1,1)(1,1,0)(2,2,1)(3,2,0)
\end{aligned}
```

## 5. Remaining causes

1. **A $`(y = 1, z = 0)`$ column with children inside a copied $`z = 1`$ column** (sheet
   rows 787–809). It is treated only as a leaf multiplier, and its subtree is dropped. Most
   of the same-pattern pairs come from this.
2. **A $`z = 1`$ column under an index column** (rows 904–914). This needs a point that
   starts a further $`\le_2`$ pair inside a $`\le_2`$-interval.
3. **A last $`D`$ that is an index leaf, followed by more children of $`W`$** (rows 826–844
   and 884).
4. **Extra $`\le_1`$-nesting-base nodes** that the sheet places next to a second
   $`\le_2`$-point (rows 764, 819 and 854).
5. **Level bookkeeping above row 915.**

## 6. A two-level collapse ($`\Phi_{3g}`$)

The 2-row $`\mathrm{Coll}`$ has one collapse target ($`\Omega_1 \mapsto N`$). In 3 rows there
are two targets. The case rules were replaced by a recursion with two collapses
(`por/phi3g.py`).

**Levels of columns.** Inside a subtree being collapsed, each column is one of the
following.

- **finite level $`y`$**: $`z = 0`$, and either there is no $`z = 1`$ ancestor, or $`y`$ is
  below that ancestor's $`y`$. Columns below a finite column are finite too.
- **level $`\omega`$**: $`z = 1`$.
- **index level $`\omega + j`$**: $`z = 0`$, below a $`z = 1`$ ancestor $`a`$, with
  $`y = a.y + j`$. The case $`j = 0`$ is called a **marker**.

**$`C1_N`$: the collapse at the $`\Omega_1`$-level** ($`\Omega_1 \mapsto N`$,
$`\Omega_{1+\nu} \mapsto \Omega_\nu`$)

- $`y = 0`$: unchanged.
- A finite column with $`y = 1`$ becomes a $`y = 0`$ root column whose children are $`N`$'s
  children followed by $`C1_N`$ of its own children.
- A finite column with $`y \ge 2`$ goes to $`y - 1`$.
- Index columns are fixed points. They move together with their $`\omega`$ ancestor.
- An $`\omega`$ column with $`y = 2`$ stays at $`y = 2`$ and is wrapped in one level-1
  column (this corresponds to $`\psi_1(\Omega_\omega \cdots)`$).
- An $`\omega`$ column with $`y \ge 3`$ goes to $`y - 1`$.

**$`C2_x`$: the collapse at the $`\Omega_\omega`$-level** ($`\Omega_\omega \mapsto x`$,
$`\Omega_{\omega+j} \mapsto \Omega_j`$). It is applied to the children of a copied $`\omega`$
column $`D`$; $`x`$ is a point that starts a $`\le_2`$ pair.

- $`y = 0`$: unchanged.
- A marker becomes a $`y = 0`$ root column whose children are $`x`$'s children followed by
  $`C2_x`$ of its own children.
- An index column $`\omega + j`$ with $`j \ge 1`$ goes to finite level $`j`$.
- A finite column below $`D`$ becomes a root column whose children are $`x`$'s children
  followed by $`C1_x`$ of its own children.

**Reaches.** $`\mathrm{lh}`$ is the 2-row fold $`\oplus`$ with these two collapses. In the
second case of $`\oplus`$, the result is $`\mathrm{lh}(Y) + Y`$ when $`Y`$ starts a $`\le_2`$
pair, and $`\mathrm{lh}(Y)`$ otherwise. The $`\le_2`$-reach $`\mathrm{lh}_2`$ is built by a fold
of the same shape.

**Three rules that are not local.** The pure version decides everything from the
$`(y, z)`$ of a column and its ancestors. It fits only 69 of the sheet rows 755–914. The
sheet needs three decisions that look at siblings or at the whole last summand.

1. A leaf marker on the rightmost path of the last $`\omega`$ summand is treated as a finite
   column (an $`\Omega_1`$-multiplier). The same local shape $`(3,2,0)`$ plays different roles
   in rows 759 and 851.
2. A unit summand right after a limit summand (one whose rightmost leaf is a marker) is its
   successor and forms one $`\le_2`$-level with it.
3. A doubled level also brings in its $`\le_1`$-nesting base as a node.

**Agreement with the sheet** (rows that are iso or sub)

| sheet rows | $`\Phi_{3g}`$ | case-rule version | first version |
|---|---|---|---|
| 522–754 | 221 | 221 | 221 |
| 755–914 | **144** | 130 | 72 |
| 915–1156 | 68 | 68 | 0 |
| 1157–1299 | 25 | 25 | 21 |
| 1300–1642 | 0 | 0 | 0 |
| total | **458** | 444 | 314 |

The oracle confirmed 139 of the 156 sub rows in 755–1299 as equal; the rest timed out. On
matrices whose row 2 is 0, $`\Phi_{3g}`$ equals the 2-row $`\Phi`$. On rows 522–754 every row
has the same verdict as before.

**Order tests**

| range | "<" certified | violations | same pattern | undecided |
|---|---|---|---|---|
| $`[(0,0,0)(1,1,1),\ (0,0,0)(1,1,1)(2,1,0))`$ (1085 matrices) | 818 | 0 | 0 | 236 |
| $`[(0,0,0)(1,1,1)(2,1,0),\ (0,0,0)(1,1,1)(2,1,1))`$ (305 matrices) | 145 | 10 | 1 | 137 |

The bad pairs dropped from 19 to 11. The 11 that remain fall into two families.

- **Same pattern (1 pair):** sheet rows 827 and 829. A low child of $`W`$ contains an
  $`\omega`$ column.
- **Violations (10 pairs):** in each, an index column contains an $`\omega`$ column, with
  finite or index columns below it. The smallest is this pair:

```math
\begin{aligned}
&(0,0,0)(1,1,1)(2,1,0)(3,2,1)(4,1,0)(5,2,1)(6,1,0)(7,2,1) \cr
&(0,0,0)(1,1,1)(2,1,0)(3,2,1)(4,2,0)
\end{aligned}
```

**Status of causes 1–5**

1. Gone: rows 787–809 now fit.
2. Partly gone: rows 909–914 now fit. Rows 904–908 and the 10 violations remain.
3. Mostly gone: rows 827, 828 and 831–833 remain.
4. Still open: rows 764, 819 and 854.
5. Unchanged. Above row 915 the problem is mostly missing nodes (the sup rows).

## 7. Rules read from Carlson's definitions ($`\Phi_{3h}`$)

The three rules of §6 were compared with the definitions of $`\le_1`$ and $`\le_2`$ in Carlson
(2009) and with the facts on $`R_2`$ listed in §1 of Wilken, "Pure Σ₂-elementarity beyond the
core" (APAL 172, 2021, [doi:10.1016/j.apal.2021.103001](https://doi.org/10.1016/j.apal.2021.103001)).
Two of the three became local rules. The new version is `por/phi3h.py`.

Notation: $`N = \psi_0(\alpha)`$ is the point being collapsed, and $`W`$ is the last summand of
$`\alpha`$.

**Rule 1 (the last column).**
- **Local form.** A leaf marker $`m`$ is an $`\Omega_1`$-multiplier if and only if $`m`$ is the
  last column of the argument of the current collapse target, and $`m`$ is a marker of the
  outermost $`\omega`$ column of that argument.
- **Reason.** As in the 1-row recursion
  $`\mathrm{lh}(\alpha) = \alpha + \mathrm{lh}(\rho_1) + \cdots + \mathrm{lh}(\rho_m)`$, the reach of $`N`$
  depends only on $`W`$.
  - An $`\Omega_1`$ followed by more terms inside an $`\omega`$ summand is a coefficient at
    level $`\omega + 0`$. $`C1`$ fixes it, because $`1 + \nu = \nu`$ for $`\nu \ge \omega`$.
  - The final $`\Omega_1`$ of the whole argument is a finite term of $`W`$. $`C1`$ maps it to
    $`N`$.
- **Checked.** With the rule off, $`\Phi(755)`$ and $`\Phi(810)`$ are certified to be at or
  above the next sheet rows (756 and 811).

**Rule 2 (a unit after a limit).**
- **Local form.** Write the copied $`\omega`$ summands as
  $`\Omega_\omega \beta_1 + \cdots + \Omega_\omega \beta_k`$. A $`\le_2`$-level is a successor summand
  of this multiplier. A unit summand right after a limit summand is that limit's successor.
- **Reason.** If $`a \lt_2 b`$, then $`a`$ is the proper supremum of an infinite $`\lt_1`$-chain
  (Wilken 2021, §1; Carlson 2009, Lemma 5.5). A limit summand
  $`\Omega_\omega \lambda`$ has no such chain, because the $`\Omega_1`$-collapse cuts it. So its
  level appears at $`\lambda + 1`$.
- **Checked.** With the rule off, $`\Phi(845)`$ and $`\Phi(863)`$ are certified to be at or
  above the next sheet rows (846 and 864).

**Rule 3 (the nesting base of a doubled level).**
- **Local form.** A witness $`w`$ with $`\mathrm{lh}_1(w) \gt \mathrm{lh}_2(w)`$ brings in its
  $`C1`$-nesting predecessor $`e`$, with $`e \le_1 \mathrm{lh}_1(w)`$.
- **Reason (not proved).** The isominimal realization is the pointwise least one among the
  closed coverings (Carlson 2009, Thm 14.10). Without $`e`$, the pair
  $`(w, \mathrm{lh}_2(w))`$ is not forced to lie inside the reach of the nesting.
- **Not checked.** With the rule off, the oracle decided neither row 929 nor row 944.

**Nested collapses (the 10 violations of §6).** The oracle showed that the error was in the
larger matrix: $`\Phi_{3g}(905) \le \text{sheet}(904)`$. In row 905 the last column
$`(4,2,0)`$ is a marker of the inner $`\omega`$ column $`(3,2,1)`$, which sits under the index
column $`(2,1,0)`$. $`\Phi_{3g}`$ collapsed it to the outer point; the sheet collapses it to the
witness of the inner level. The fix:

- (a) A $`z = 0`$ column is an index column of the **nearest** $`\omega`$ ancestor whose level
  is at most its own $`y`$. Otherwise it is finite. So each column carries a stack of
  $`\omega`$ ancestors.
- (b) A marker collapses to the target of the $`\omega`$ column that owns it. Rule 1 applies
  only to markers of the outermost $`\omega`$ column.
- (c) Under $`C2_x`$, the last leaf marker of a wrapped $`\omega`$ column is read relative to
  $`D`$ ($`\Omega_{\omega+1} \mapsto \Omega_1`$). It becomes a finite column of level 1, and then
  collapses to the witness.
- (d) The same reading on the last low child of $`W`$ (row 827). This removed the pair with
  the same pattern.

**Agreement with the sheet** (rows that are iso or sub)

| sheet rows | $`\Phi_{3h}`$ | $`\Phi_{3g}`$ | case-rule version | first version |
|---|---|---|---|---|
| 522–754 | 221 | 221 | 221 | 221 |
| 755–914 | **149** | 144 | 130 | 72 |
| 915–1156 | **73** | 68 | 68 | 0 |
| 1157–1299 | 25 | 25 | 25 | 21 |
| 1300–1642 | 0 | 0 | 0 | 0 |
| total | **468** | 458 | 444 | 314 |

Rows gained over $`\Phi_{3g}`$: 827, 904, 905, 906, 908, 925, 988, 989, 992, 993. No row
was lost. Of the 6 new sub rows, 4 were certified equal; 906 and 925 timed out.

**Order tests**

| range | "<" certified | violations | same pattern | undecided |
|---|---|---|---|---|
| $`[(0,0,0)(1,1,1),\ (0,0,0)(1,1,1)(2,1,0))`$ (1085 matrices) | 818 | 0 | 0 | 236 |
| $`[(0,0,0)(1,1,1)(2,1,0),\ (0,0,0)(1,1,1)(2,1,1))`$ (305 matrices) | 145 | **0** | **0** | 148 |

On the 1085 matrices $`\Phi_{3h}`$ equals $`\Phi_{3g}`$. Pairs with a pattern of more than 30
nodes were skipped (30 and 11 pairs).

**Status of causes 1–5**

1. and 2. Gone (the stack of $`\omega`$ ancestors, and "collapse to the owner's target").
3. Row 827 fits now. Rows 828 and 831–833 remain.
4. Still open: rows 764, 819 and 854.
5. Unchanged: the rows above 915, the $`(2,2,1)`$ family, and the sup rows.

## 8. One reflection rule and finite columns ($`\Phi_{3i}`$)

$`\Phi_{3i}`$ (`por/phi3i.py`) adds two rules to $`\Phi_{3h}`$. Agreement rose to 503 rows, and
both order tests still show 0 violations.

**Rule `d94`: the copy from downward 2-reflection.** Carlson 2009, Def 9.4 (downward
2-reflection), applied to $`X = \{x\}`$ and a $`\le_2`$-successor $`g`$ of $`x`$, gives a copy
$`\tilde{x} \lt x`$ such that, for $`y \ge x`$,
$`\tilde{x} \le_1 y \iff (x \le_1 g \text{ and } x \le_1 y)`$.
- **The rule.** For every $`\le_2`$-able node $`x`$ with $`\mathrm{lh}_1(x) \gt \mathrm{lh}_2(x)`$, add
  $`\tilde{x}`$: the least $`\le_1`$-nesting base that is not a dead end. Skip this when an
  earlier node already has $`\le_1`$-reach $`\mathrm{lh}_1(x)`$.
- **It replaces rule 3 of §7.** At a doubled level $`\mathrm{lh}_1(x) = g + g`$, so
  $`\tilde{x} \le_1 g + g`$. This is the sheet's extra node $`e`$. With `d94` on, the separate
  rule 3 changes no row.
- **It also explains cause 4** (rows 764, 819, 854). The sheet's extra node there is the
  same copy. These rows now fit exactly.
- **Checked.** A generating rule is valid (Carlson 2009, Thm 14.11), so the copy does not
  change the ordinal. The oracle confirmed this: with and without the node, the patterns
  have the same $`\iota`$ on rows 929, 764, 819, 854 and 833 (certificates of at most one
  step).

**Rule `infin`: $`\omega`$ columns below a finite column.**
- **The rule.** Below a finite column (a $`y = 1`$, $`z = 0`$ column of $`W`$, i.e. an
  $`\Omega_1`$-term), an $`\omega`$ column owns no index columns. Its markers are finite
  coefficients, and $`C1`$ lowers them by one level ($`\Omega_{k+1} \mapsto \Omega_k`$).
- **Exception.** A limit summand followed directly by a unit summand keeps its marker as an
  index (rule 2 of §7). Row 858 needs this.
- **Reason.** The level $`\omega + j`$ exists only relative to an $`\omega`$ column that is an
  $`\omega`$-level of the argument. Inside $`\psi_1(\cdots)`$ the column's $`y`$ is just a
  finite level.
- **Result.** Rows 828, 831 and 832 (cause 3) now fit.

**Agreement with the sheet** (rows that are iso or sub)

| sheet rows | $`\Phi_{3i}`$ | $`\Phi_{3h}`$ | $`\Phi_{3g}`$ |
|---|---|---|---|
| 522–754 | 221 | 221 | 221 |
| 755–914 | **155** | 149 | 144 |
| 915–1156 | **102** | 73 | 68 |
| 1157–1299 | 25 | 25 | 25 |
| 1300–1642 | 0 | 0 | 0 |
| total | **503** | 468 | 458 |

36 rows were gained and one (1009) was lost. Of the 34 new sub rows, 31 were certified
equal; 945, 962 and 977 timed out.

**Rows in 755–914 that still do not fit**
- 833: not the same shape, but certified to have the same ordinal as the sheet.
- 844: a row whose point the fix table corrects. Certified:
  $`\text{sheet}(843) \lt \text{fix} \lt \Phi_{3i}(844) \lt \text{sheet}(845)`$. So both are in the
  right place, but they differ, and the fix may be incomplete.
- 907 (and 1009): $`\text{sheet} \le \Phi_{3i}`$ is certified; the other direction was not found.

**Order tests**

| range | "<" certified | violations | same pattern | undecided | skipped (>30 nodes) |
|---|---|---|---|---|---|
| $`[(0,0,0)(1,1,1),\ (0,0,0)(1,1,1)(2,1,0))`$ (1085 matrices) | 874 | 0 | 0 | 178 | 32 |
| $`[(0,0,0)(1,1,1)(2,1,0),\ (0,0,0)(1,1,1)(2,1,1))`$ (305 matrices) | 157 | 0 | 0 | 132 | 15 |

- A longer oracle budget certified 74 more pairs.
- For $`A = P + a + \cdots`$ and $`B = P + b + \cdots`$ in Cantor normal form, $`A \lt B`$ iff
  $`a \lt b`$. When both $`a`$ and $`b`$ have $`z = 0`$, the $`R_1^+`$ oracle decides the pair,
  because $`R_2^+`$ and $`R_1^+`$ agree below the least $`\le_2`$-pair. This decided 3 more
  pairs.
- Almost all of the 310 undecided pairs are steps to a limit: the smaller matrix is a long
  member of the fundamental sequence of the larger one. For example
  $`(0,0,0)(1,1,1)(2,1,0)(3,2,0)(4,3,0)(5,4,0) \lt (0,0,0)(1,1,1)(2,1,0)(3,2,1)`$.
  Deciding them needs a proof that $`\iota \circ \Phi_3`$ is monotone inside a term.

## 9. Wilken's $`R_2`$ and the undecided pairs

`por/tr3.py` translates a trio matrix $`M`$ into Wilken's notation for the pure structure
$`R_2 = (\mathrm{Ord}; \le, \le_1, \le_2)`$ (Wilken, "Pure Σ₂-elementarity beyond the core",
APAL 172, 2021, [doi:10.1016/j.apal.2021.103001](https://doi.org/10.1016/j.apal.2021.103001)). Write $`\mathcal{T}_3(M)`$ for the value.
- $`\upsilon_0 = 0`$, $`\upsilon_{i+1} = (\upsilon_i)^\infty`$, and sups at limits (Wilken's Def 1.5).
  An ordinal in $`[\upsilon_i, \upsilon_{i+1})`$ is a $`\vartheta`$-term relative to
  $`\tau = \upsilon_i`$ (Def 1.3), and such terms are compared by Lemma 2.26.
- The reading is $`\upsilon_{1+\xi} = \psi_0(\Omega_\omega + \psi_1(\Omega_\omega) \cdot \xi)`$.
  A fixed point $`h = \upsilon_h`$ has no finite index. $`\mathcal{T}_3`$ names it by its
  matrix, and two such names are compared by the matrix order.
- On both test sets $`\mathcal{T}_3`$ is strictly increasing along the lex order.
- **$`R_2`$ is not $`R_2^+`$.** Wilken's $`\le_1`$ and $`\le_2`$ are those of the pure
  structure. $`\Phi_3`$ aims at $`R_2^+`$, which has $`+`$ in its language. The two differ:
  Wilken's Thm 1.8 gives $`\upsilon_2 \lt_2 \upsilon_\omega`$, but the sheet (row 534) and
  $`\Phi_{3i}`$ have no $`\le_2`$-successor of $`\upsilon_2`$. So Wilken's $`R_2`$ cannot serve
  as the oracle for $`\Phi_3`$. What does fit is to read $`\upsilon_\iota`$ in $`R_2^+`$ as
  $`\varepsilon_0 \cdot \iota`$ in $`R_2`$, the correspondence that Wilken §3 gives between
  $`R_1`$ and $`R_1^+`$. On the $`\upsilon`$-points with a finite index, 11758 relations agree
  and none disagrees.

**The 310 pairs under $`\mathcal{T}_3`$.** Each pair is $`A \lt_{\mathrm{lex}} B`$, and both
are single root terms with a $`z = 1`$ column.

| how $`\mathcal{T}_3(A) \lt \mathcal{T}_3(B)`$ is decided | pairs |
|---|---|
| same $`\upsilon`$-segment, $`\vartheta`$-terms compared by Lemma 2.26 | 43 |
| different $`\upsilon`$-indices | 2 |
| same segment, but $`\tau`$ is a fixed point named by its matrix | 13 |
| only by fixed-point names, i.e. by the matrix order | 252 |

- All 310 have $`\mathcal{T}_3(A) \lt \mathcal{T}_3(B)`$. The 58 pairs of the first three rows
  are decided by Wilken's comparison. The 252 others lie above the least fixed point of
  $`\upsilon`$, where $`\mathcal{T}_3`$ adds nothing to the matrix order.
- This compares the ordinals $`o(A) \lt o(B)`$ of the matrices. It says
  $`\iota(\Phi_{3i}(A)) \lt \iota(\Phi_{3i}(B))`$ only if $`\iota \circ \Phi_{3i} = o`$, which is
  the claim under test. So $`\mathcal{T}_3`$ decides none of the pairs by itself.

**The oracle with a longer budget.** Each pair got about 27 seconds. The methods, in order:
- the covering with the nodes that $`\Phi_{3i}(A)`$ and $`\Phi_{3i}(B)`$ share (the same matrix,
  so the same $`\mathcal{T}_3`$ value) fixed to themselves, after at most one step;
- limit macros: repeated upward 2-reflections (Carlson 2009, Def 10.1);
- best-first search and depth-first search over the generating rules.

Every certificate is replayed with explicit arithmetic.

- **Result.** 23 of the 310 pairs are now certified "<": 20 by the limit macros, 2 by the
  best-first search, and 1 by the covering with shared nodes fixed. Every certificate has 1
  to 3 steps.
- By the classes of the table above: 13 of the 56 same-segment pairs, 1 of the 2 pairs with
  different $`\upsilon`$-indices, and 9 of the 252 pairs above the least fixed point.
- **Violations.** None found. A reverse search (8 seconds per pair) found no certificate
  of $`\iota(\Phi_{3i}(B)) \le \iota(\Phi_{3i}(A))`$ for any of the 287 remaining pairs.
- 287 pairs remain: 158 in the first range and 129 in the second. The smallest is
  $`(0,0,0)(1,1,1)(2,0,0)(3,1,0)(4,2,0)(5,3,0) \lt (0,0,0)(1,1,1)(2,0,0)(3,1,1)`$.

**Order tests with the new certificates**

| range | "<" certified | violations | same pattern | undecided | skipped (>30 nodes) |
|---|---|---|---|---|---|
| $`[(0,0,0)(1,1,1),\ (0,0,0)(1,1,1)(2,1,0))`$ (1085 matrices) | 894 | 0 | 0 | 158 | 32 |
| $`[(0,0,0)(1,1,1)(2,1,0),\ (0,0,0)(1,1,1)(2,1,1))`$ (305 matrices) | 160 | 0 | 0 | 129 | 15 |

**Rows 844, 907 and 1009.** Each open row is a member of the fundamental sequence of the
next sheet row: $`844 = 845[3]`$, $`907 = 909[1]`$ and $`1009 = 1010[1]`$ (BM4 expansions).
All three lie above the least fixed point of $`\upsilon`$, so $`\mathcal{T}_3`$ names every
node by its matrix and cannot tell the patterns apart. The arguments below use the sheet's
own fundamental sequences and the oracle.

- **844: $`\Phi_{3i}`$ is right, and the fix table should change.**

  | matrix | sheet | $`\Phi_{3i}`$ |
  |---|---|---|
  | $`845[1]`$ (row 810) | `(b (b' ([c d] d+b')))` | contains it |
  | $`845[2]`$ (row 843) | `(b (b' (b'' ([c d] d+b''))))` | contains it |
  | $`845[3]`$ (row 844) | `(b (b' (b'' (b''' ([c d] d+b'')))))` | `(b (b' (b'' (b''' ([c d] d+b''')))))` |
  | $`845[4]`$ | none | `(b … (b'''' ([c d] d+b'''')))` |
  | $`845`$ | `(b ([c d] d+c))` | contains it |

  In $`845[n]`$ the summand after $`d`$ is the top of the $`\le_1`$-chain, and in the limit
  it becomes $`c`$, the sup of the chain. The sheet's row 844 keeps $`d + b''`$ from row 843,
  and the fix table records that it has the same ordinal as row 843. The fix table then
  moves the point to $`b'''`$.
  - Certified: $`\text{fix} \lt \text{corrected}`$, where "corrected" is
    `0 a (b (b' (b'' (b''' ([c d] d+b''')))))` with point $`b`$.
  - Certified: $`\iota(\text{corrected}) = \iota(\Phi_{3i}(844))`$. The corrected pattern is
    a restriction of $`\Phi_{3i}(844)`$, and the oracle gives the other direction.
  - With the corrected fix, row 844 fits, and the agreement becomes 504 rows.
- **907: still open.** Certified: $`\text{sheet}(905) \lt \text{sheet}(907) \lt \Phi_{3i}(907)`$.
  - $`\Phi_{3i}(907)`$ has an extra block `(e₁ (e₁' ([f₁ g₁] g₁+e₁')))` before the sheet's
    `(e (e' ([f g] g+e')))`, and $`\mathrm{lh}(b) = d + e`$ uses the larger $`e`$. The root
    term of $`e_1`$ ends in one column $`U = (1,1,0)(2,2,1)(3,2,0)`$, and the root term of
    $`e`$ ends in two. The two copies of $`U`$ are the $`C2`$ images of two different
    children of the copied $`\omega`$ column, and the images coincide.
  - In $`909[2]`$ (row 908) the second image is larger and absorbs the first, and
    $`\Phi_{3i}`$ equals the sheet.
  - **A rule tried and rejected** (`c2one` in `por/phi3j.py`): an index column whose $`C2`$
    image equals the image of the $`\omega`$ column just before it adds nothing. Then rows
    907 and 947 fit (505 rows) and nothing else changes. But the oracle certifies a
    violation: $`\iota(\Phi_{3j}(907)) \le \iota(\Phi_{3i}(M'))`$ for the lex-smaller
    $`M' = (0,0,0)(1,1,1)(2,1,0)(3,2,1)(4,2,0)(3,2,0)(4,3,1)(5,2,0)(6,3,1)`$.
  - A direct covering (no generating step) also shows $`\iota(\text{sheet}(907)) \le \iota(\Phi_{3i}(906))`$. So the
    sheet and $`\Phi_{3i}`$ cannot both be right on 906 and 907. Either the sheet's 907 is too
    small, or the extra block, which $`\Phi_{3i}`$ also adds to 906, is too big. Deciding this
    needs $`\iota(\Phi_{3i}(906)) \le \iota(\text{sheet}(906))`$, which was not found in 50
    seconds.
- **1009: probably $`\Phi_{3i}`$, not certified.**
  - The `d94` copies do not change the ordinal here. Certified both ways:
    $`\iota(\Phi_{3i}(1009)) = \iota(\Phi_{3i}(1009)\text{ without d94})`$.
  - The sheet's pattern is a restriction of $`\Phi_{3i}(1009)`$ without `d94`. So
    $`\iota(\text{sheet}) \le \iota(\Phi_{3i})`$; the other direction was not found in 50 seconds.
  - The difference is the last summand $`e`$ of $`\mathrm{lh}(b) = d + d + e`$. The appended
    columns $`(2,1,0)(3,2,1)(4,2,1)(4,2,1)(4,2,0)(3,2,1)(4,2,1)`$ have two $`\omega`$ columns,
    like the two $`\omega`$ summands of row 1008. $`\Phi_{3i}`$ reads both, so $`e`$ carries
    a copy of the whole pattern of 1008. The sheet's $`e`$ matches only the first
    $`\omega`$ column.
  - Certified: $`\Phi_{3i}(1008) \lt \Phi_{3i}(1009)`$ and
    $`\text{sheet}(1009) \lt \text{sheet}(1010)`$.

## 10. The rows above 915 ($`\Phi_{3k}`$)

$`\Phi_{3k}`$ (`por/phi3k.py`) adds nine flags to $`\Phi_{3j}`$. Agreement with the sheet rose
from 504 to 787 rows, and no row was lost. On the matrices below $`(0,0,0)(1,1,1)(2,1,1)`$,
$`\Phi_{3k}`$ gives the same pattern as $`\Phi_{3i}`$: all 1085 + 305 matrices of the earlier
test sets were checked. So the earlier order tests still hold.

**How the rules were found.** All rows from 915 on lie above the least fixed point of
$`\upsilon`$. There $`\mathcal{T}_3`$ names every node by its matrix (§9), and Wilken's $`R_2`$
is not $`R_2^+`$ anyway. So Wilken 2021 gives no ordinal comparisons here. Instead, the rules
follow the structure that $`\Phi_{3i}`$ already has. All of them act in the
$`\le_1`$-reach of a $`\le_2`$-able node

```math
x = \mathrm{root}(P,\ U+q), \qquad d_m = \mathrm{root}(P,\ U+q,\ U^m)\quad (m = 1, \dots, q),
```

where $`d_1 \lt \cdots \lt d_q`$ are the $`\le_2`$-successors of $`x`$ and $`D`$ is the last
$`\omega`$ column of $`U`$. $`\Phi_{3i}`$ had a rule for each kind of child of $`D`$ except
three. The new rules fill these gaps with the same two tools as before: the $`C2`$ read
($`\Omega_\omega \mapsto x`$, $`\Omega_{\omega+j} \mapsto \Omega_j`$) and the 2-row fold.
Each rule was checked on whole families of sheet rows. Each family is one column type with
all its variants.

**Rule `kimg`: a $`z = 1`$ child $`K`$ of $`D`$ on $`D`$'s own level.** From
$`(0,0,0)(1,1,1)(2,1,1)`$ on, $`D`$ has such children. $`\Phi_{3i}`$ read $`K`$ as one more copy
of $`d`$ and dropped the children of $`K`$. So rows 915, 1020, 1040, 1041 and 1061 all got the
pattern of row 915.
- **The rule.** $`K`$ gives the summand $`\mathrm{root}(d_1.\text{kids} + \mathrm{KI}(K.\text{kids}))`$,
  where KI maps
  - a $`z = 1`$ column on $`D`$'s level by the same rule (nested);
  - a marker leaf that is the last column and a direct child of $`K`$ to the anchor of $`x`$
    (the $`\Omega_1`$-multiplier of the point, as `lastcol` does for $`D`$);
  - every other column by $`C2`$.
- A bare $`K`$ gives $`d_1`$ itself, so the old doubling $`d + d`$ is the special case.

| row | matrix after $`(0,0,0)(1,1,1)`$ | sheet |
|---|---|---|
| 915 | $`(2,1,1)`$ | `(b ([c d] d+d))` |
| 1020 | $`(2,1,1)(3,0,0)`$ | `(b ([c d] e))` |
| 1040 | $`(2,1,1)(3,0,0)(4,0,0)`$ | `(b ([c d] (e e+a)))` |
| 1041 | $`(2,1,1)(3,1,0)`$ | `(b ([c d] (e e+b)))` |
| 1053 | $`(2,1,1)(3,1,0)(4,0,0)`$ | `(b ([c d] (e e+c+a)))` |
| 1061 | $`(2,1,1)(3,1,1)`$ | `(b ([c d] (e e+d)))` |
| 1094 | $`(2,1,1)(3,1,1)(4,1,1)(5,1,1)`$ | `(b ([c d] (e e+d) (f f+e)))` |

  The part after $`[c\ d]`$ is the 2-row pattern of $`K`$'s subtree built on $`d`$. For
  example $`e = \mathrm{root}(d.\text{kids} + 1)`$ in row 1020, and in row 1094 the nested
  $`z = 1`$ columns give the chain $`e \le_1 e + d`$, $`f \le_1 f + e`$. Of the rows 1020–1097
  whose matrix has one root child, all fit except 1059 and 1060 (nested frames, see the end
  of this section).

**Rule `idx1`: an index column of $`D`$ of level $`\omega + j`$ with $`j \ge 1`$** (from
$`(0,0,0)(1,1,1)(2,2,0)`$ on). Its $`C2`$ image is a bare $`\Omega_j`$ with no base, and
$`\Phi_{3i}`$ used it as a summand. So rows 1098–1156 lost their whole $`\le_2`$ pair (the sheet
had nodes that $`\Phi_{3i}`$ lacked).
- **The rule.** The image is the summand $`\mathrm{root}(d_q.\text{kids} + \text{image})`$. Consecutive
  index columns accumulate, as in the prefix fold of the 2-row map.
- **Rule `ubase`.** These summands are nodes. The sheet has them as the base $`e`$ of a
  relative $`\psi_0(\Omega_\omega)`$ pattern, for example row 1144
  `(b ([c d] (e ([f g] g+g))))`.

| row | matrix after $`(0,0,0)(1,1,1)`$ | sheet |
|---|---|---|
| 1098 | $`(2,2,0)`$ | `(b ([c d] (e e+e)))` |
| 1107 | $`(2,2,0)(2,2,0)`$ | `(b ([c d] (e e+e) (f f+f)))` |
| 1110 | $`(2,2,0)(3,1,1)`$ | `(b ([c d] (e e+e+d)))` |
| 1117 | $`(2,2,0)(3,3,1)`$ | `(b ([c d] [e f]))` |
| 1144 | $`(2,2,0)(3,3,1)(4,3,1)`$ | `(b ([c d] (e ([f g] g+g))))` |

**Rules `zsib`, `kbase`, `k2cut`, `k2chain`: the levels.** A $`z = 1`$ child of $`D`$ one
level up (an $`\Omega_{\omega+1}`$ factor, from $`(0,0,0)(1,1,1)(2,2,1)`$ on) adds a
$`\le_2`$-level. $`\Phi_{3i}`$ counted such children only along the chain of last children, so
$`(2,2,1)(2,0,0)`$ lost its second successor.
- **`zsib`.** Count these children also when they are not the last children of $`D`$. Equal
  siblings add one level each: `[[[c d] e] f]` for $`(2,2,1)(2,2,1)`$ (row 1286).
- **`kbase`.** A $`K`$ whose first children are such columns ($`j`$ of them) is built on
  $`d_{1+j}`$ instead of $`d_1`$: $`(2,2,1)(2,1,1)(3,2,1)`$ gives $`e + e`$ (row 1266), while
  $`(2,2,1)(2,1,1)`$ gives $`e + d`$ (row 1244).
- **`k2cut`.** Let $`K_1, K_2, \dots`$ be the chain of first up-children ($`K_1`$ of $`D`$,
  $`K_{i+1}`$ of $`K_i`$). $`d_m`$ belongs to $`K_m`$.
  - A column with $`z = 0`$ children ends the chain without a further top level. After such
    a column, every later up-child of $`D`$ adds its own chain.
  - If $`K_m`$ has children, then $`d_m`$ is not a $`\le_1`$-dead end. $`\mathrm{lh}_1(d_m)`$ is
    the fold of the $`C2`$ read of $`K_m`$'s children relative to $`d_m`$. A same-level
    $`z = 1`$ child of $`K_m`$ reaches $`d_{m+1}`$.
  - $`\mathrm{lh}_1(x)`$ starts from $`\mathrm{lh}_1(d_q)`$.
- **`k2chain`.** If $`K_m`$ has only chain children, then $`d_m \le_1 d_q`$.
- These rules give the crossing intervals of the sheet, such as `[c (d] d+a)`: here
  $`c \lt_2 d`$ and $`d \le_1 d + 1`$, while $`\mathrm{lh}_1(c) = d + 1`$ as well.

| row | matrix after $`(0,0,0)(1,1,1)`$ | sheet |
|---|---|---|
| 1157 | $`(2,2,1)`$ | `(b [[c d] e])` |
| 1203 | $`(2,2,1)(2,0,0)`$ | `(b ([[c d] e] e+a))` |
| 1300 | $`(2,2,1)(3,0,0)`$ | `(b ([c (d] d+a)))` |
| 1320 | $`(2,2,1)(3,0,0)(2,2,1)(3,0,0)`$ | `(b ([[c (d] d+a) (e] e+a)))` |
| 1431 | $`(2,2,1)(3,2,1)`$ | `(b [[c (d] e)])` |
| 1573 | $`(2,2,1)(3,3,1)`$ | `(b ([[[c (d] e] f)]))` |
| 1617 | $`(2,2,1)(3,3,1)(4,3,1)`$ | `(b ([[[c (d] (e] f)])))` |

**Rules `kin` and `klim`.**
- **`kin`.** A $`z = 1`$ column on $`D`$'s level nested deeper in $`D`$'s children, for example
  inside an index column, is read by `kimg`. Before, it was moved rigidly. Row 1149
  `(e ([f g] (h h+d)))`. Without this rule, 18 adjacent pairs of the new test sets have the
  same pattern.
- **`klim`.** A marker at the end of a same-level $`K`$ makes $`D`$ a limit summand, in the
  sense of the rule `mult` of §7. With it, a following unit summand joins $`D`$'s level. Rows
  1042, 1043, 1050 and 1052.

**Rules tried and rejected.**
- `kframe`: in a nested frame, read $`K`$ from $`x`$ instead of $`d_1`$ (suggested by rows 1147
  and 1150). It loses 98 rows.
- `kidx`: read a marker of $`D`$ with children by KI instead of $`C2`$. It loses 40 rows.

**Each flag is needed.** Rows that fit when one flag is switched off (all flags: 786, not
counting the rows the fix table drops):

| without | kimg | idx1 | zsib | kbase | ubase | kin | klim | k2cut | k2chain |
|---|---|---|---|---|---|---|---|---|---|
| rows | 643 | 700 | 725 | 758 | 745 | 778 | 776 | 701 | 763 |

**Agreement with the sheet** (iso / sub / sup / no)

| sheet rows | $`\Phi_{3i}`$ | $`\Phi_{3k}`$ | rows that fit |
|---|---|---|---|
| 522–754 | 34 / 187 / 0 / 8 | 34 / 187 / 0 / 8 | 221 → 221 |
| 755–914 | 39 / 117 / 0 / 2 | 39 / 117 / 0 / 2 | 156 → 156 |
| 915–1156 | 28 / 74 / 42 / 94 | 125 / 103 / 2 / 8 | 102 → 228 |
| 1157–1299 | 12 / 13 / 15 / 101 | 58 / 39 / 3 / 41 | 25 → 97 |
| 1300–1449 | 0 / 0 / 35 / 107 | 34 / 12 / 15 / 81 | 0 → 46 |
| 1450–1642 | 0 / 0 / 69 / 122 | 37 / 2 / 49 / 103 | 0 → 39 |
| total | 113 / 391 / 161 / 434 | 327 / 460 / 69 / 243 | 504 → 787 |

The oracle checked the 69 sub rows whose pattern is new (7 seconds per row, then 25 seconds for the
rest). It certified 48 of them as equal to the sheet. 21 timed out: 1043, 1054, 1187–1191,
1193–1197, 1221, 1223, 1437, 1441, 1442, 1447, 1448, 1450 and 1451.

**Order tests on two new sets.** The matrices were generated as before: BM4 expansions with
copy count at most 3 and at most 9 columns, started from the sheet's matrices in the range.
All of them are standard.

| range | matrices | adjacent pairs | "<" certified | violations | same pattern | undecided | skipped (>30 nodes) |
|---|---|---|---|---|---|---|---|
| $`[(0,0,0)(1,1,1)(2,1,1),\ (0,0,0)(1,1,1)(2,2,1))`$ | 785 | 784 | 470 | 0 | 0 | 306 | 8 |
| $`[(0,0,0)(1,1,1)(2,2,1),\ (0,0,0)(1,1,1)(2,2,1)(3,0,0))`$ | 290 | 289 | 214 | 4 | 0 | 66 | 5 |

- Each pair got 7 seconds for "<" and, if that failed, 7 seconds (the last 19: 25 seconds) for
  the reverse $`\iota(\Phi_{3k}(B)) \le \iota(\Phi_{3k}(A))`$. Every certificate is replayed.
- **Below $`(0,0,0)(1,1,1)(2,2,1)`$: no violation.** The undecided pairs are again mostly steps
  to a limit. The smallest is
  $`(0,0,0)(1,1,1)(2,1,1)(2,0,0)(1,1,1)(2,1,1)(2,0,0) \lt (0,0,0)(1,1,1)(2,1,1)(2,0,0)(2,0,0)`$.
- **Above $`(0,0,0)(1,1,1)(2,2,1)`$: 4 certified violations.** The smallest is

```math
\begin{aligned}
A &= (0,0,0)(1,1,1)(2,2,1)(2,1,0)(1,1,0)(2,2,1)(3,3,1)(3,2,0) \quad\text{(row 1211)}\cr
B &= (0,0,0)(1,1,1)(2,2,1)(2,1,0)(1,1,1) \quad\text{(row 1213)}
\end{aligned}
```

  with $`A \lt_{\mathrm{lex}} B`$ but $`\iota(\Phi_{3k}(B)) \le \iota(\Phi_{3k}(A))`$. In all four the
  larger matrix is a sheet row that $`\Phi_{3k}`$ does not fit (1213, 1231, 1242, 1283), and the
  smaller one is a row that it fits (1211, 1228, 1240, 1282). For three of them the oracle
  certifies $`\iota(\Phi_{3k}(A)) \lt \iota(\text{sheet}(B))`$; the fourth (1228/1231) timed out.
  So the sheet orders these pairs correctly, and $`\Phi_{3k}(B)`$ is too small. Rows 1213, 1231
  and 1242 are root runs whose first summand is a limit summand with two $`\le_2`$-levels:
  `mult` merges it with the following unit summand, and its levels are lost. The sheet keeps them as a
  nested block, for example `(e ([[f g] h] h+c))` in row 1213. Row 1283 is a nested frame
  (see below). A quick fix, not merging such a summand, makes the closure explode, so it was not
  kept.

**What is left above 915.**
- **Root runs with several summands** (rows 1177, 1186–1202, 1204–1249 with a second root
  child $`(1,1,1)`$). With two $`\le_2`$-levels per summand, the sheet puts the nested pattern
  of the first summand between $`d_1`$ and $`d_2`$. $`\Phi_{3k}`$ puts it below $`d_1`$, where
  the witnesses of §6 go.
- **Nested frames** (rows 1059, 1060, 1147, 1150, 1151). Inside the pattern of an index column, a
  same-level $`K`$ reads from the frame's $`c`$ in the sheet, but from its $`d`$ in
  $`\Phi_{3k}`$. The global version of this rule (`kframe`) is wrong.
- **Markers of $`K_m`$ followed by $`y = 0`$ columns** (rows 1332–1340): the sheet's
  `[c (d] d+c)` needs a variant of `lastcol`.
- **After $`K_1`$ with a same-level child** (rows 1463–1550): siblings and further children
  change the levels in a way that `k2cut` does not yet describe.
- **An index image that is itself $`\le_2`$-able** (rows 1122, 1123): the sheet also has the
  nesting base below it, which `ubase` does not add.
- Row 907 (§9) and row 947 are unchanged; row 1009 still does not fit.

## 11. Root runs with several summands and nested frames ($`\Phi_{3l}`$)

$`\Phi_{3l}`$ (`por/phi3l.py`) adds four flags to $`\Phi_{3k}`$. Agreement with the sheet rose from
787 to 834 rows, and no row was lost. The 4 violations of §10 are gone: both new test sets now
show 0 violations. On the 1085 + 305 matrices of the earlier test sets, $`\Phi_{3l}`$ gives the same
patterns as $`\Phi_{3k}`$, so those order tests still hold.

**Setting.** As in §10, $`x = \mathrm{root}(P,\ U+q)`$ is a $`\le_2`$-able node with successors
$`d_m = \mathrm{root}(P,\ U+q,\ U^m)`$. When the root has several $`z = 1`$ children (a root run),
$`U`$ has several $`\omega`$ columns $`D_1, \dots, D_k`$, one for each copied summand. Write the
copied summands as $`\Omega_\omega \lambda_1 + \cdots + \Omega_\omega \lambda_k`$. A summand is a
**limit summand** when $`\lambda_i`$ ends in a marker, that is $`\lambda_i = \lambda_i' + \Omega_\omega`$.
Rule `mult` of §7 puts the $`\le_2`$-level of a limit summand at its successor (the reason: if
$`a \lt_2 b`$, then $`a`$ is the proper supremum of an infinite $`\lt_1`$-chain, and a limit summand has no
such chain at $`\lambda_i`$). From $`(0,0,0)(1,1,1)(2,2,1)`$ on, $`\lambda_i`$ can carry its own
$`\le_2`$-levels (an $`\Omega_{\omega+1}`$ factor). The four rules say where those levels go.

**Rule `lsucc`: a limit summand with more levels than its successor.** Row 1213 is
$`\Omega_\omega \lambda_1 + \Omega_\omega`$ with $`\lambda_1 = \Omega_{\omega+1} + \Omega_\omega`$: `mult` merges the two
summands into one level, and $`\Phi_{3k}`$ read the children of $`D_1`$ one by one. It dropped the
$`\Omega_{\omega+1}`$ factor, so the two levels of $`\lambda_1`$ were lost.
- **The rule.** Under the $`C2`$ read ($`\Omega_\omega \mapsto x`$), the final $`\Omega_\omega`$ of
  $`\lambda_i`$ becomes $`x`$. This is rule 1 of §7 (`lastcol`: the final $`\Omega_1`$ of the whole
  argument becomes $`N`$) one level up. So $`\mathrm{lh}_1(x)`$ gets the summand
  $`e = \mathrm{root}(d_q.\text{kids} + (1, 0, D_i[\text{marker} \mapsto x]))`$. It is the
  $`\le_1`$-nesting base of the pattern of $`\Omega_\omega \lambda_i`$ relative to $`x`$, built on the
  top successor $`d_q`$, and it is a node (like the `ubase` summands).
- Only when $`\lambda_i'`$ has an $`\Omega_{\omega+1}`$ factor. Otherwise $`\lambda_i[x]`$ has no levels,
  and the pattern shrinks to the plain summand $`x`$ of the old read. Applied to every limit
  summand, the rule loses 137 rows below $`(0,0,0)(1,1,1)(2,2,1)`$, for example row 845
  `(b ([c d] d+c))`.

| row | matrix after $`(0,0,0)(1,1,1)`$ | sheet |
|---|---|---|
| 1209 | $`(2,2,1)(2,1,0)`$ | `(b ([[c d] e] e+b))` |
| 1213 | $`(2,2,1)(2,1,0)(1,1,1)`$ | `(b ([c d] (e ([[f g] h] h+c))))` |
| 1234 | $`(2,2,1)(2,1,0)(2,1,0)(1,1,1)`$ | `(b ([c d] (e ([[f g] h] h+f+c))))` |
| 1214 | $`(2,2,1)(2,1,0)(1,1,1)(2,1,1)`$ | `(b ([c ([e f] (g ([[h i] j] j+e))) d] d+d))` |

  In row 1213, `(e ([[f g] h] h+c))` is the pattern of row 1209 rebuilt on $`d`$, with the final
  $`\Omega_\omega`$ read as $`c = x`$ instead of $`b = N`$. In row 1234 the first marker is not final,
  and it gives $`+f`$ as in $`\Phi_{3k}`$. In row 1214 the same block sits inside the witness of the
  limit summand.

**Rule `lcov`: a summand that only adds levels.** Call a summand levels-only when all its children
are $`z = 1`$ columns one level up, recursively ($`\Omega_\omega \Omega_{\omega+1}^k`$-like).
- A levels-only summand after a limit summand is its successor, exactly as a unit summand is in
  `mult`: it adds levels and nothing else. If the limit's own levels are covered by the levels of
  $`x`$, nothing is lost, and its children are read by $`C2`$ as before: the marker gives $`+x`$.
- A limit prefix whose levels are covered is witnessed at its levels-only successor (the prefix
  followed by a chain with the same number of levels), as a U-form, that is a $`\le_1`$-nesting base,
  right above $`x`$.

| row | matrix after $`(0,0,0)(1,1,1)`$ | sheet |
|---|---|---|
| 1245 | $`(2,2,1)(2,1,1)(2,1,0)(1,1,1)(2,2,1)`$ | `(b ([[c d] e] e+d+c))` |
| 1249 | $`(2,2,1)(2,1,1)(2,1,0)(1,1,1)(2,2,1)(2,1,1)`$ | `(b ([[c (f ([[g h] i] i+h+g)) d] e] e+d))` |
| 1242 | $`(2,2,1)(2,1,0)(3,2,1)(4,3,1)(4,2,0)(3,2,1)(4,3,1)`$ | `(b ([[c (f ([[g h] i] i+g)) d] e] e+f))` |
| 1283 | $`(2,2,1)(2,2,0)(3,3,1)(4,4,1)(4,3,0)(3,3,1)(4,4,1)`$ | `(b ([[c d] e] (f ([[g h] i] i+g))))` |

  Rows 1242 and 1283 are the same case inside a frame: the frame's U-form is a limit column followed
  by a levels-only column, and its marker gives $`+g`$, the frame's own $`x`$.

**Rule `wlast`: the witness of a prefix goes into the last interval.** In §6 the witness of a
proper prefix of $`D_1, \dots, D_k`$ was placed in $`(x, d_1)`$. The sheet places it in
$`(d_{q-1}, d_q)`$ (with $`d_0 = x`$).
- **Reason.** $`x \le_2 d_q`$. By Carlson 2009 Def 5.3 (part 2), every pattern that occurs cofinally
  below $`x`$ occurs cofinally below $`d_q`$, so it also occurs above $`d_{q-1}`$. The prefix's
  $`\le_2`$-pattern occurs cofinally below $`x`$. The copy in the last interval is the one that
  $`x \le_2 d_q`$ requires. For $`q = 1`$ nothing changes.

| row | matrix after $`(0,0,0)(1,1,1)`$ | sheet |
|---|---|---|
| 1180 | $`(2,2,1)(1,1,1)`$ | `(b [c [[e f] g] d])` |
| 1198 | $`(2,2,1)(1,1,1)(2,2,1)`$ | `(b [[c d] [[f g] h] e])` |
| 1201 | $`(2,2,1)(1,1,1)(2,2,1)(1,1,1)(2,2,1)`$ | `(b [[c d] [[f g] [[i j] k] h] e])` |
| 1204 | $`(2,2,1)(2,0,0)(1,1,1)(2,2,1)`$ | `(b [[c' d'] ([[c d] e] e+a) e'])` |

**Rule `kiwrap`: one U-form in a frame.** The read KI of `kimg` read the children of a marker one
by one by $`C2`$. So two consecutive $`\omega`$ columns became two separate level-1 columns
$`\psi_1(\Omega_\omega a) + \psi_1(\Omega_\omega b)`$ instead of one $`\psi_1(\Omega_\omega a + \Omega_\omega b)`$. $`C2`$
already merges them (§6). With the same merge in KI, the frame of row 1059
`(f ([g h] (i i+g)))` has a limit column followed by a unit column, and `mult` gives it the right
level. Rows 1059, 1060 and 1066 now fit.

**A rule tried and rejected: `kfr`.** In an index frame (the image of an index column of level
$`\omega + 1`$), read a bare same-level $`K`$ that is nested in a $`K`$, or that comes after a summand
other than some $`d_m`$, as the frame's $`x`$ instead of $`d_1`$. Then rows 1147, 1150 and 1151 fit.
But the oracle certifies a violation: $`\iota(\Phi_{3l+\mathtt{kfr}}(1150)) \le \iota(\Phi_{3l}(A))`$ for

```math
A = (0,0,0)(1,1,1)(2,2,0)(3,3,1)(4,3,1)(5,3,0)(6,4,1)(7,4,1) \lt_{\mathrm{lex}} (0,0,0)(1,1,1)(2,2,0)(3,3,1)(4,3,1)(5,3,1)
```

The rule maps the bare $`K`$ below the image of the lex-smaller marker with children in $`A`$, so the
read is not monotone. With `kfr`, $`\Phi_{3l}(1150)`$ is isomorphic to the sheet's row 1150, so the
sheet's rows 1147, 1150 and 1151 are probably too small, like row 844 (§9).

**Each flag is needed.** Rows that fit when one flag is switched off (all flags: 833, not counting
the rows the fix table drops):

| without | wlast | lsucc | lcov | kiwrap |
|---|---|---|---|---|
| rows | 814 | 824 | 817 | 830 |

**Agreement with the sheet** (iso / sub / sup / no)

| sheet rows | $`\Phi_{3k}`$ | $`\Phi_{3l}`$ | rows that fit |
|---|---|---|---|
| 522–754 | 34 / 187 / 0 / 8 | 34 / 187 / 0 / 8 | 221 → 221 |
| 755–914 | 39 / 117 / 0 / 2 | 39 / 117 / 0 / 2 | 156 → 156 |
| 915–1156 | 125 / 103 / 2 / 8 | 127 / 104 / 2 / 5 | 228 → 231 |
| 1157–1299 | 58 / 39 / 3 / 41 | 62 / 69 / 3 / 7 | 97 → 131 |
| 1300–1449 | 34 / 12 / 15 / 81 | 34 / 15 / 15 / 78 | 46 → 49 |
| 1450–1642 | 37 / 2 / 49 / 103 | 37 / 9 / 49 / 96 | 39 → 46 |
| total | 327 / 460 / 69 / 243 | 333 / 501 / 69 / 196 | 787 → 834 |

The oracle checked the 52 sub rows whose pattern is new (7 seconds per row, then 25 seconds for the
rest). It certified 33 of them as equal to the sheet. 19 timed out: 1199–1202, 1218–1224,
1226–1228, 1230, 1235, 1236, 1246 and 1453.

**Order tests.** The same two sets as in §10, with the certificates of §10 reused where the pattern
pair is unchanged. New pairs got 7 seconds for "<" and 7 seconds for the reverse.

| range | matrices | adjacent pairs | "<" certified | violations | same pattern | undecided | skipped (>30 nodes) |
|---|---|---|---|---|---|---|---|
| $`[(0,0,0)(1,1,1)(2,1,1),\ (0,0,0)(1,1,1)(2,2,1))`$ | 785 | 784 | 471 | 0 | 0 | 305 | 8 |
| $`[(0,0,0)(1,1,1)(2,2,1),\ (0,0,0)(1,1,1)(2,2,1)(3,0,0))`$ | 290 | 289 | 220 | 0 | 0 | 64 | 5 |

- **The 4 violations of §10 are gone.** The pairs 1211/1213, 1240/1242 and 1282/1283 are now
  certified "<". The pair 1228/1231 is undecided (40 seconds each way). For row 1231 the oracle
  certifies $`\iota(\Phi_{3l}(1231)) = \iota(\text{sheet}(1231))`$ in both directions.
- **Below $`(0,0,0)(1,1,1)(2,2,1)`$** the rules change 14 patterns (`kiwrap`); still no violation.
- The smallest undecided pair above $`(0,0,0)(1,1,1)(2,2,1)`$ is again a step to a limit:
  $`(0,0,0)(1,1,1)(2,2,1)(2,0,0)(1,1,1)(2,2,1)(2,0,0) \lt (0,0,0)(1,1,1)(2,2,1)(2,0,0)(2,0,0)`$.

**What is left above 915.**
- **Root runs.** Rows 1177, 1192, 1217, 1268 do not fit yet. Rows 1231, 1237 and 1238 (and the sup rows 1232,
  1233) do not have the same shape: the sheet adds a node $`c`$ with one level and a node $`e`$ below
  the two-level node. But the oracle certifies the same ordinal: $`\iota(\text{sheet}) \le \iota(\Phi_{3l})`$
  for all five, and the reverse for 1231, 1237 and 1238 (for 1232 and 1233 it holds because
  $`\Phi_{3l}`$ is a restriction of the sheet). So the extra nodes are implied.
- **Nested frames.** Rows 1059, 1060 and 1283 fit now. Rows 1147, 1150 and 1151 do not; see `kfr`.
- The other open families of §10 are unchanged: markers of $`K_m`$ followed by $`y = 0`$ columns
  (rows 1332–1340), the levels after a $`K_1`$ with a same-level child (rows 1463–1550), index images
  that are themselves $`\le_2`$-able (rows 1122, 1123), and rows 907, 947, 1009.

## 12. The level columns above row 1300 ($`\Phi_{3m}`$)

$`\Phi_{3m}`$ (`por/phi3m.py`) adds fourteen flags to $`\Phi_{3l}`$. Agreement with the sheet rose from 834
to 939 rows; one row (1480) was lost. On the 1085 + 305 matrices of the earlier test sets, $`\Phi_{3m}`$
gives the same patterns as $`\Phi_{3l}`$.

**Setting.** As in §10, $`K_1, K_2, \dots`$ are the level columns of $`D`$ (the chain of up-children),
$`d_m`$ belongs to $`K_m`$, and $`\mathrm{lh}_1(d_m)`$ is the $`C2`$ read of the children of $`K_m`$
relative to $`d_m`$. From $`(0,0,0)(1,1,1)(2,2,1)(3,0,0)`$ on, $`K_1`$ has children of every kind. Most
new rules apply one principle of §7 (rule (b)): **a marker collapses to the target of the $`\omega`$
column that owns it.**

**Rule `kown`: markers below $`K_m`$.** $`\Phi_{3l}`$ read every marker below $`K_m`$ as $`d_m`$. But a
marker is owned by the nearest $`\omega`$ column whose level is at most its own. A marker of $`D`$
inside $`K_1`$ is an $`\Omega_\omega`$ of $`D`$'s multiplier, and $`C2`$ maps it to $`x`$; a marker of
$`K_j`$ ($`j \lt m`$) maps to $`d_j`$.

| row | matrix after $`(0,0,0)(1,1,1)`$ | sheet |
|---|---|---|
| 1300 | $`(2,2,1)(3,0,0)`$ | `(b ([c (d] d+a)))` |
| 1397 | $`(2,2,1)(3,2,0)`$ | `(b ([c (d] d+d)))` |
| 1332 | $`(2,2,1)(3,1,0)(2,0,0)`$ | `(b ([c (d] d+c)))` |
| 1373 | $`(2,2,1)(3,1,0)(3,0,0)`$ | `(b ([c (d] d+c+a)))` |
| 1338 | $`(2,2,1)(3,1,0)(2,1,0)`$ | `(b ([c (d] d+c) d+c+b))` |

- **`kownk`.** A marker of $`D`$ with children is the frame $`\mathrm{root}(x.\text{kids} + C2(\text{children}))`$,
  a node between $`x`$ and $`d_1`$ (rows 1378–1384, e.g. `(b ([c (e e+c) (d] d+e)))`).
- **`ksucc`.** In row 1332 the multiplier of $`D`$ is $`\Omega_{\omega+1} \cdot \Omega_\omega + 1`$: the
  level column ends in a marker of $`D`$, so it is a limit, and the unit after it is its successor
  (`mult` inside $`D`$). It adds nothing; a second unit adds $`+a`$ (row 1337). It fits one row and
  makes 11 sub rows exact (iso).

**Rule `lsup`: a limit summand whose pattern has content.** The block of `lsucc` (§11) now also
applies when the limit summand's own $`\le_2`$-pattern has content (a level column with children that
are not chain columns), whatever its successor is, and then the witness at its successor is not
added. Row 1327, $`(2,2,1)(3,1,0)(1,1,1)`$: `(b ([c' d'] ([c (d] d+c'))))`, the pattern of row 1332
rebuilt on $`d'`$ with the marker read as $`c'`$. Rows 1307–1330, 1364, 1457–1459.

**Rules `kcut2`, `kmax`, `ksl`, `kbcut`, `kdl`, `kdeep`, `lastkd`: the levels next to $`K_1`$.**
- **`kcut2`.** A level column with a same-level $`\omega`$ child is not a cut: the top level stays.
  Row 1520, $`(2,2,1)(3,2,1)(3,0,0)`$: `(b ([[c (d] e] e+a)))`.
- **`kmax`.** $`\mathrm{lh}_1(x)`$ starts from the farthest $`\mathrm{lh}_1(d_m)`$, not from
  $`\mathrm{lh}_1(d_q)`$: a lower level can reach beyond the top one. Row 1537 `(b ([[c (d] e] e+e) e+e+a))`.
- **`ksl`.** A same-level $`\omega`$ child $`K_s`$ of $`D`$ next to a level column with content has its
  own levels, the lowest ones (one if $`K_s`$ has no up-children, else those of $`K_s`$ read as a
  $`D`$); the level columns move up. Row 1313 `([[c c'] (d] d+a) d+c')`, row 1314
  `([[[c c'] c''] (d] d+a) d+c'')`.
- **`kbcut`.** Except when the first up-child of $`K_s`$ equals $`K_1`$ (with content): then $`K_s`$
  shares $`K_1`$'s level, reads $`d_1`$, and that up-child is consumed. Row 1315,
  $`(2,2,1)(3,0,0)(2,1,1)(3,2,1)(4,0,0)`$: `(b ([c (d] d+a) d+d))`. Rows 1315, 1351, 1402, 1440,
  1467–1470, 1539.
- **`kdl`.** An $`\omega`$ column at $`D`$'s level inside a level column ($`\Omega_\omega`$ inside an
  $`\Omega_{\omega+1}`$ factor) brings its own level columns as the lowest levels, ends the chain, and
  is read as the `kimg` summand built on them; if its first up-child equals $`K_1`$, it shares
  $`K_1`$'s level instead, as in `kbcut`. Rows
  1385–1396, 1405, 1406, e.g. 1391 $`(2,2,1)(3,1,1)(4,2,1)`$: `(b ([[[c d'] d''] (d] d+d'')))`.
  Without it, the new order test has 19 adjacent pairs with the same pattern.
- **`kdeep`.** Such a column deeper inside, below a marker frame, is an $`\Omega_\omega`$ of $`D`$ and
  collapses to $`x`$: the `kimg` summand built on $`x`$. It changes no fit row, but without it the new
  order test has 3 violations, e.g.
  $`(0,0,0)(1,1,1)(2,2,1)(3,2,0)(4,1,1)(5,2,1)(6,2,0) \lt_{\mathrm{lex}} (0,0,0)(1,1,1)(2,2,1)(3,2,0)(4,2,0)`$ (row 1422).
- **`lastkd`.** `lastcol` (§7, rule 1) also for a final marker owned by $`D`$ and by such columns:
  it is the $`\Omega_1`$-multiplier $`N`$. Rows 1345, 1366.

**Rule `lcov2`: a covered limit summand.** A limit summand with content whose marker is its last
child, followed by a summand that repeats its $`\lambda'`$ (up to a unit that `ksucc` absorbs), is
covered, as in `lcov`: merged with it, no block, and the marker gives $`+x`$. Row 1311
$`(2,2,1)(3,0,0)(2,1,0)(1,1,1)(2,2,1)(3,0,0)`$: `(b ([c (d] d+a) d+c))`; rows 1339, 1399, 1438, 1461,
1538. Without it, `lsup` gives three violations in the new order test.

**Rules `ibase`, `lwpos`.**
- **`ibase`.** An index image that is itself $`\le_2`$-able comes with its $`\le_1`$-nesting base, as
  every $`\le_2`$-able node reached by the nesting limit does. Rows 1122, 1123, 1192.
- **`lwpos`.** The witness of a covered limit prefix (`lcov`) sits just below the highest successor
  that its content reads: a same-level child with $`j`$ leading up-children reads $`d_{1+j}`$ (`kbase`).
  Row 1268.

**Each flag is needed.** Rows that fit when one flag is switched off (all flags: 938, not counting the
rows the fix table drops):

| without | kown | ksucc | kownk | lsup | kcut2 | kmax | ksl | ibase | lwpos | kdl | lcov2 | kbcut | kdeep | lastkd |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| rows | 891 | 937 | 931 | 926 | 923 | 935 | 926 | 935 | 937 | 924 | 932 | 920 | 938 | 936 |

`kdeep` changes no count but removes 3 order violations.

**Agreement with the sheet** (iso / sub / sup / no)

| sheet rows | $`\Phi_{3l}`$ | $`\Phi_{3m}`$ | rows that fit |
|---|---|---|---|
| 522–754 | 34 / 187 / 0 / 8 | 34 / 187 / 0 / 8 | 221 → 221 |
| 755–914 | 39 / 117 / 0 / 2 | 39 / 117 / 0 / 2 | 156 → 156 |
| 915–1156 | 127 / 104 / 2 / 5 | 129 / 104 / 0 / 5 | 231 → 233 |
| 1157–1299 | 62 / 69 / 3 / 7 | 62 / 71 / 3 / 5 | 131 → 133 |
| 1300–1449 | 34 / 15 / 15 / 78 | 91 / 29 / 0 / 22 | 49 → 120 |
| 1450–1642 | 37 / 9 / 49 / 96 | 60 / 16 / 44 / 71 | 46 → 76 |
| total | 333 / 501 / 69 / 196 | 415 / 524 / 47 / 113 | 834 → 939 |

The oracle checked the 24 sub rows whose pattern is new (7 seconds per row, then 25 seconds for the
rest). It certified 19 of them as equal to the sheet. 5 timed out: 1192, 1308, 1438, 1439 and 1440.

**Three sheet errors: rows 1147, 1150 and 1151.** §11 rejected `kfr`, the rule that fits these rows.
The oracle now certifies (directly, by a covering) that each sheet pattern is at most the value of a
member of the row's own fundamental sequence:

```math
\iota(\text{sheet}(T)) \le \iota(\Phi_{3l}(T[1])),\qquad T[1] \lt_{\mathrm{lex}} T \quad (T = 1147,\ 1150,\ 1151)
```

For $`T = 1150`$ also $`\iota(\Phi_{3l}(T[1])) \lt \iota(\Phi_{3l}(T))`$ is certified. In the frame of the
index column $`(2,2,0)`$, the sheet reads a bare same-level $`\omega`$ column as the frame's point $`f`$;
it should be $`g`$ (the frame's $`d_1`$), as at the top level (rows 1035, 1061, 1094). The corrected
patterns equal $`\Phi_{3l}`$ (iso), and both neighbours are certified:

| row | sheet | corrected | certified |
|---|---|---|---|
| 1147 | `(e ([f g] h h+f))` | `(e ([f g] h h+g))` | 1146 < fix < 1148 |
| 1150 | `(e ([f g] (h h+f)))` | `(e ([f g] (h h+g)))` | 1149 < fix < 1151 |
| 1151 | `(e ([f g] (h h+f) (i i+h)))` | `(e ([f g] (h h+g) (i i+h)))` | fix(1150) < fix < 1152 |

(the parts shown are inside `0 a (b ([c d] …))`). These entries go into the fix table.

**Order tests.** The sets of §10 and a new set just above: BM4 expansions (copy count at most 3, at most
9 columns) of the sheet's matrices in $`[(0,0,0)(1,1,1)(2,2,1)(3,0,0),\ (0,0,0)(1,1,1)(2,2,1)(3,2,1))`$; all
262 are standard. Certificates of §10 and §11 are reused where the pattern pair is unchanged.

| range | matrices | adjacent pairs | "<" certified | violations | same pattern | undecided | skipped (>30 nodes) |
|---|---|---|---|---|---|---|---|
| $`[(0,0,0)(1,1,1)(2,1,1),\ (0,0,0)(1,1,1)(2,2,1))`$ | 785 | 784 | 470 | 0 | 0 | 306 | 8 |
| $`[(0,0,0)(1,1,1)(2,2,1),\ (0,0,0)(1,1,1)(2,2,1)(3,0,0))`$ | 290 | 289 | 221 | 0 | 0 | 63 | 5 |
| $`[(0,0,0)(1,1,1)(2,2,1)(3,0,0),\ (0,0,0)(1,1,1)(2,2,1)(3,2,1))`$ | 262 | 261 | 209 | 0 | 0 | 52 | 0 |

- The 1085 + 305 matrices have the same patterns as before, so their tests still show 0 violations.
- On the new set, earlier versions of the rules had violations and same-pattern pairs. `kdl`, `lcov2`,
  `kbcut`, `kdeep` and `lastkd` remove them. 4 of these violations were already in $`\Phi_{3l}`$; `kbcut`
  and `kdeep` remove them too.
- **The pair 1228/1231 of §11 is a step to a limit.** Rows 1229 and 1230 are the members $`1231[1]`$ and
  $`1231[2]`$ of the fundamental sequence of row 1231. The oracle certifies
  $`\Phi_{3l}(1228) \lt \Phi_{3l}(1229) \lt \Phi_{3l}(1230)`$ (45 seconds each), but no finite chain of
  such steps reaches row 1231.
- The smallest undecided pair of the new set is again a step to a limit:
  $`(0,0,0)(1,1,1)(2,2,1)(3,0,0)(1,1,1)(2,2,1)(3,0,0) \lt (0,0,0)(1,1,1)(2,2,1)(3,0,0)(2,0,0)`$.

**What is left above 915.** 113 rows do not fit and 47 are sup rows (the sheet has more nodes).
- Root runs over $`(2,2,1)(3,1,0)`$ with a second summand (rows 1331, 1334–1336, 1340, 1346–1353,
  1356, 1357, 1367, 1368; rows 1336 and 1348–1350 are in the fix table), rows 1400, 1401, 1409 (1400
  and 1401 are in the fix table) and 1434–1436.
- Rows 1460–1553: a same-level child of $`D`$ whose own up-children read higher levels. Row 1480 was
  lost by `kbcut`. Rows 1564–1642 above $`(2,2,1)(3,3,1)`$ were not studied.
- Rows 1147, 1150, 1151 (sheet errors, above), 1177 and 1217 (in the fix table), 1231, 1237, 1238
  (same ordinal as the sheet, §11), 907, 947, 1009.

## 13. Next

- The 287 undecided pairs (§9): prove that $`\iota \circ \Phi_3`$ is monotone inside a term.
  A longer oracle budget helps little: 23 of 310 in about 27 seconds each.
- Row 907: decide whether $`\iota(\Phi_{3i}(906)) = \iota(\text{sheet}(906))`$. Row 1009: the
  other direction $`\iota(\Phi_{3i}) \le \iota(\text{sheet})`$. Row 844: change the fix table's
  entry to the corrected pattern of §9.
- An analysis of $`R_2^+`$ itself, for example by proving the correspondence
  $`\upsilon_\iota \leftrightarrow \varepsilon_0 \cdot \iota`$ between $`R_2^+`$ and $`R_2`$. Wilken's
  $`R_2`$ describes the pure structure only.
- The rows above 915 (§10–§12): root runs over $`(2,2,1)(3,1,0)`$ with a second summand, a same-level
  child of $`D`$ whose up-children read higher levels (rows 1460–1553, and row 1480 lost by `kbcut`),
  and the rows above $`(0,0,0)(1,1,1)(2,2,1)(3,3,1)`$. The undecided pairs of the order tests (421 in
  §12) are, like those of §9, mostly steps to a limit.

## 14. Programs

- `por/tss.py`: 3-row matrices and terms, and the lexicographic order.
- `por/tr3.py`: the translation $`\mathcal{T}_3`$ into Wilken's notation for $`R_2`$ (§9). `python3 por/tr3.py "(0,0,0)(1,1,1)(1,1,0)(2,2,1)"` prints `u[1 + 1]`, i.e. $`\upsilon_2`$.
- `por/phi3m.py`: the version $`\Phi_{3m}`$ of §12, the current one. `python3 por/phi3m.py "(0,0,0)(1,1,1)(2,2,1)(3,1,0)(2,0,0)"`
  prints each node's matrix, its $`\le_1`$-reach and its $`\le_2`$-successors. `--flags=` selects the flags.
- `por/phi3l.py`: the version $`\Phi_{3l}`$ of §11. `python3 por/phi3l.py "(0,0,0)(1,1,1)(2,2,1)(2,1,0)(1,1,1)"`
  prints each node's matrix, its $`\le_1`$-reach and its $`\le_2`$-successors. `--flags=` selects the flags; the rejected flag `kfr` is off.
- `por/phi3k.py`: the version $`\Phi_{3k}`$ of §10. `python3 por/phi3k.py "(0,0,0)(1,1,1)(2,2,1)(3,0,0)"`
  prints each node's matrix, its $`\le_1`$-reach and its $`\le_2`$-successors. `--flags=` selects the flags.
- `por/phi3j.py`: $`\Phi_{3i}`$ plus the rejected flag `c2one` of §9, which is off by default. `--flags=lastcol,mult,fin,c2rel,lastlo,infin,d94,nobase,c2one` turns it on.
- `por/phi3i.py`: the version $`\Phi_{3i}`$ of §8. `python3 por/phi3i.py "(0,0,0)(1,1,1)(2,1,0)(3,2,1)(4,2,0)"` prints the same table as `phi3g.py`.
- `por/phi3h.py`: the version $`\Phi_{3h}`$ of §7. `python3 por/phi3h.py "(0,0,0)(1,1,1)(2,1,0)(3,2,1)(4,2,0)"` prints the same table as `phi3g.py`.
- `por/phi3g.py`: the two-level version $`\Phi_{3g}`$ (§6). `python3 por/phi3g.py "(0,0,0)(1,1,1)(2,1,0)"` prints each node's matrix, its $`\le_1`$-reach and its $`\le_2`$-successors.
- `por/phi3.py`: the case-rule version $`\Phi_3`$. `python3 por/phi3.py "(0,0,0)(1,1,1)(1,1,0)(2,2,1)"` prints the
  pattern and the matrix of each node; `--flags=z,dbl` selects the first version.

Patterns are written as in the 2-row version, with `(x … z)` for $`\le_1`$ and `[x … z]`
for $`\le_2`$. The oracle is not included in this repository.
