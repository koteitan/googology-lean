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

## 7. Next

- The collapse when an $`\omega`$ column is nested inside an index column (the 10
  violations).
- Explaining the three non-local rules from Carlson's rules for $`R_2^+`$.
- The rows above 915: level bookkeeping, and the $`(2,2,1)`$ family.

## 8. Programs

- `por/tss.py`: 3-row matrices and terms, and the lexicographic order.
- `por/phi3g.py`: the two-level version $`\Phi_{3g}`$ (§6). `python3 por/phi3g.py "(0,0,0)(1,1,1)(2,1,0)"` prints each node's matrix, its $`\le_1`$-reach and its $`\le_2`$-successors.
- `por/phi3.py`: the case-rule version $`\Phi_3`$. `python3 por/phi3.py "(0,0,0)(1,1,1)(1,1,0)(2,2,1)"` prints the
  pattern and the matrix of each node; `--flags=z,dbl` selects the first version.

Patterns are written as in the 2-row version, with `(x … z)` for $`\le_1`$ and `[x … z]`
for $`\le_2`$. The oracle is not included in this repository.
