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

## 6. Next

The 2-row $`\mathrm{Coll}`$ has one collapse target ($`\Omega_1 \mapsto N`$). Three rows need
two targets: $`N`$ at the $`\Omega_1`$-level, and the $`\le_2`$-point $`c`$ at the
$`\Omega_\omega`$-level.

The plan is to stop adding cases one by one. First fix a general recursive $`\mathrm{Coll}`$
that carries the pair of targets as an environment. Then check whether the nested cases
of causes 1 and 2 come out of that recursion.

## 7. Programs

- `por/tss.py`: 3-row matrices and terms, and the lexicographic order.
- `por/phi3.py`: $`\Phi_3`$. `python3 por/phi3.py "(0,0,0)(1,1,1)(1,1,0)(2,2,1)"` prints the
  pattern and the matrix of each node; `--flags=z,dbl` selects the first version.

Patterns are written as in the 2-row version, with `(x … z)` for $`\le_1`$ and `[x … z]`
for $`\le_2`$. The oracle is not included in this repository.
