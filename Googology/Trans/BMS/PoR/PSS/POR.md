[← Back](README.md) | [English](POR.md) | [Japanese](POR-ja.md)

# A map $`\Phi`$ from pair sequences to additive patterns ($`R_1^+`$)

**Status: proved on paper (§8, [proof/](proof/README.md)) and formalized in Lean with no `sorry` (`Main.lean`: `mainTheorem_mat`), from facts cited from the literature as checked axioms; with numerical evidence.**

This page defines a map from a standard pair sequence $`M`$ to an additive pattern of
resemblance of order 1, $`\Phi(M)`$, in the sense of Carlson. $`\Phi(M)`$ is built by
rearranging the trees of the matrix; no $`\psi`$ term is written.

**Theorem (proved on paper, §8).** For standard pair sequences $`M, M'`$:

```math
M \lt_{\mathrm{lex}} M' \iff \iota(\Phi(M)) \lt \iota(\Phi(M'))
```

Here $`\iota(P)`$ is the value of the point of the pattern $`P`$ in its isominimal
realization.

It follows from a stronger form, also proved on paper:

```math
\iota(\Phi(M)) = 1 + \mathrm{val}(\mathrm{pairTerm}(M))
```

Here `pairTerm` is the map of `Rank.lean` from pair sequences to Buchholz's $`\psi`$-terms.
The $`1 +`$ is needed because `pairTerm` sends $`(0,0)`$ to 0, while
$`\iota(\Phi((0,0))) = 1`$; for infinite values $`1 + \alpha = \alpha`$. `pairTerm` is an order
isomorphism onto the terms below $`\psi_0(\Omega_\omega)`$, so this form gives the theorem,
and also that the points of $`\Phi`$ take every nonzero value in the core.

## 1. Background

- The order type of the pair sequences is $`\psi_0(\Omega_\omega)`$ (`Rank.lean` of this
  library).
- The core of Carlson's structure $`R_1^+ = (\mathrm{Ord}; 0, +; \le, \le_1)`$, the union of
  the isominimal realizations of its finite patterns, is also
  $`\psi_0(\Omega_\omega) = \lvert \Pi^1_1\text{-}\mathrm{CA}_0 \rvert`$ (Wilken,
  "Σ₁-Elementarity and Skolem Hull Operators", APAL 145, 2007).
- So an order isomorphism from pair sequences to $`R_1^+`$-patterns is expected. The
  question is whether it can be read off the matrix directly.
- $`\Phi`$ is a candidate of that kind, with one caveat. The operation $`\mathrm{Coll}`$
  it uses (§3.4) is Buchholz's collapse written on matrices. So $`\Phi`$ avoids the
  notation of $`\psi`$, but not its mechanism.

## 2. Reading a matrix as trees

- A matrix is a sequence of columns $`(x_i, y_i)`$.
- The **row-0 parent** of column $`i`$ is the largest $`j \lt i`$ with $`x_j \lt x_i`$. A
  column without a parent is a **root**.
- The **term** of column $`i`$ is $`T(i) = (y_i, (T(c_1), \ldots, T(c_k)))`$. Here
  $`c_1 \lt \cdots \lt c_k`$ are the columns whose parent is $`i`$ (its children).
- A matrix corresponds one-to-one to the sequence of its root terms
  $`(T(r_1), \ldots, T(r_m))`$; each $`x`$ is the depth in the tree.
- The order is the lexicographic order of the column sequences.
- The **sum** is Cantor-normal-form addition. $`(a_1, \ldots, a_m) + (b_1, \ldots, b_n)`$
  drops the trailing terms of $`a`$ that are smaller than $`b_1`$, then appends $`b`$.
- $`1 = (0, ())`$ is the matrix $`(0,0)`$.

**Example.** $`(0,0)(1,0)(2,0)(1,0)`$ is one tree. Its root has two children, $`(1,0)`$
(whose child is $`(2,0)`$) and $`(1,0)`$. Read a childless column as $`1 = \omega^0`$ and a
column with children as $`\omega^{(\text{sum of the children})}`$; the result is
$`\omega^{\omega + 1}`$. A matrix whose $`y`$ are all 0 is read like a primitive sequence.

## 3. Definition

Below, $`N = (0, (C_1, \ldots, C_k))`$ is a root term and $`A = (C_1, \ldots, C_k)`$.

### 3.1 Epsilon terms and the anchor

- $`N`$ is **epsilon** if $`k \ge 1`$ and the last child $`C_k`$ has $`y \ge 1`$.
- $`\mathrm{anchor}(N) = (0, (C_1, \ldots, C_{k-1}))`$ for $`k \ge 2`$: the last child is
  dropped.

### 3.2 The exponent $`\log`$ and $`\lambda`$

For a root term $`u = (0, B)`$ that is not epsilon, let $`B^{\mathrm{hi}}`$ be its
children with $`y \ge 1`$ and $`B^{\mathrm{lo}}`$ its children with $`y = 0`$, each in the
original order.

```math
\log(u) = (0, B^{\mathrm{hi}}) + B^{\mathrm{lo}}_1 + \cdots + B^{\mathrm{lo}}_r
```

If $`B^{\mathrm{hi}}`$ is empty, the first term is left out. When $`N`$ is not epsilon
($`k \ge 1`$), read the last child $`C_k`$ as a root term $`u`$ and put:

```math
\lambda(N) = \begin{cases} (u) & (u \text{ epsilon}) \cr \log(u) & (\text{otherwise}) \end{cases}
```

### 3.3 The reach $`\mathrm{lh}`$ (the largest point reached by $`\le_1`$)

- $`N = 1`$: $`\mathrm{lh}(N) = (N)`$.
- $`N`$ not epsilon: $`\mathrm{lh}(N) = (N) + \lambda(N)`$.
- $`N`$ epsilon: let $`W = C_k`$. Let $`D_1, \ldots, D_p`$ be the children of $`W`$ with
  $`y \ge 2`$ and $`E_1, \ldots, E_q`$ those with $`y \le 1`$, each in the original order.
  Build $`S`$ as follows and put $`\mathrm{lh}(N) = S`$.

```math
\begin{aligned}
S &:= (N, N) \cr
S &:= S \oplus \bigl(0,\ A + \mathrm{Coll}_A(D_1) + \cdots + \mathrm{Coll}_A(D_i)\bigr) && (i = 1, \ldots, p) \cr
S &:= S \oplus \mathrm{Coll}_A(E_j) && (j = 1, \ldots, q)
\end{aligned}
```

The fold $`\oplus`$ is defined by the formula below, where $`S_1`$ is the first term of
$`S`$.

```math
S \oplus Y = \begin{cases} S + (Y) & (Y \le S_1) \cr \mathrm{lh}(Y) & (Y \gt S_1) \end{cases}
```

$`\oplus`$ is the transitivity of $`\le_1`$. If the new point lies inside the reach so
far, the reach continues after it by addition. Otherwise the reach moves to the reach of
that point.

### 3.4 The collapse $`\mathrm{Coll}_A`$

For a term $`s = (y, (B_1, \ldots, B_m))`$, put the following, where
$`\mathrm{Coll}_A(B) = \mathrm{Coll}_A(B_1) + \cdots + \mathrm{Coll}_A(B_m)`$.

```math
\mathrm{Coll}_A(s) = \begin{cases}
s & (y = 0) \cr
(0,\ A + \mathrm{Coll}_A(B)) & (y = 1) \cr
(y - 1,\ \mathrm{Coll}_A(B)) & (y \ge 2)
\end{cases}
```

- A column with $`y = 1`$ becomes $`N`$ itself, with $`\mathrm{Coll}_A(B)`$ appended as
  children. For example, at $`N = (0,0)(1,1)(2,2)`$ the column $`(1,1)(2,2)`$ becomes
  $`(0,0)(1,1)(2,2)(1,1)`$.
- A column with $`y \ge 2`$ has its $`y`$ lowered by 1.
- This is Buchholz's collapse $`\Omega_1 \mapsto N`$, $`\Omega_{k+1} \mapsto \Omega_k`$.

### 3.5 The pattern $`\Phi(M)`$

Let $`M`$ be a standard matrix with root terms $`T_1, \ldots, T_m`$, and put
$`\hat{M} = (T_1, \ldots, T_m)`$. A matrix with several roots is the sum of its root terms.

- The set of nodes $`V`$ is the least set that contains $`\{(),\ (1),\ \hat{M}\}`$ and is
  closed under the following operations.
  - Prefix sums: $`(a_1, \ldots, a_m) \in V`$ gives $`(a_1, \ldots, a_j) \in V`$.
  - Root segments: $`(a_1, \ldots, a_m) \in V`$ gives $`(a_i) \in V`$.
  - For a node $`(N) \in V`$ with one term: $`(\mathrm{anchor}(N)) \in V`$ and
    $`\mathrm{lh}(N) \in V`$.
- Nodes are ordered lexicographically. Addition is the relation
  $`\{(x, y, z) \in V^3 : x + y = z\}`$, with the sum of §2.
- $`\le_1`$ is defined by the formula below.

```math
x \le_1 z \iff x = z \lor (x \text{ has one term} \land x \le z \le \mathrm{lh}(x))
```

- The point is $`\hat{M}`$.

## 4. Examples

Patterns are written as in poral's examples. The nodes are listed left to right in
increasing order. `0` is 0, `a` is 1, `n0, n1, …` are nodes with one term, `x+y` is a sum,
`(x … z)` means $`x \le_1 z`$ ($`z`$ being the end of $`x`$'s reach), and `*` marks the
point. The examples were computed with `por/phi.py`.

| matrix $`M`$ | $`\Phi(M)`$ | nodes |
|---|---|---|
| $`(0,0)(1,0)(2,0)(1,0)`$ | `0 a (n0 n0+a) *n1` | n0 = $`(0,0)(1,0)(2,0)`$, n1 = $`M`$ |
| $`(0,0)(1,1)`$ | `0 a (*n0 n0+n0)` | n0 = $`M = \varepsilon_0`$ |
| $`(0,0)(1,1)(1,0)`$ | `0 a (n0 n0+n0) *n1` | n0 = $`(0,0)(1,1)`$, n1 = $`M`$ |
| $`(0,0)(1,1)(1,0)(2,0)`$ | `0 a (n0 n0+n0) (*n1 n1+a)` | n1 = $`M`$, reach n1 + 1 |
| $`(0,0)(1,1)(1,1)`$ | `0 a (n0 n0+n0) (*n1 n1+n1)` | n0 = $`(0,0)(1,1)`$, n1 = $`M`$ |
| $`(0,0)(1,1)(2,1)(3,0)`$ | `0 a (*n0 n1)` | n1 = $`(0,0)(1,1)(2,1)(3,0)(1,0)`$ |
| $`(0,0)(1,1)(2,2)`$ | `0 a (*n0 (n1 n1+n1))` | n1 = $`(0,0)(1,1)(2,2)(1,1)`$ |
| $`(0,0)(1,1)(2,2)(3,3)(2,2)`$ | `0 a (*n0 (n1 (n2 n2+n2)) n2+n2+n2)` | n1 = $`M(1,1)(2,2)`$, n2 = $`M(1,1)(2,2)(1,1)`$ |

- $`(0,0)(1,1)(1,0)(2,0)`$ is $`\omega^{\varepsilon_0 + \omega}`$. The "+1" in its reach
  n1 + 1 is the exponent 1 of the last term $`\omega = \omega^1`$ of the exponent. This is
  Carlson's rule below $`\varepsilon_0`$: the reach extends by the exponent of the last
  term of the exponent.
- At $`(0,0)(1,1)(2,2)`$ (the Bachmann–Howard ordinal), $`\mathrm{Coll}`$ maps the column
  $`(1,1)(2,2)`$ to $`(0,0)(1,1)(2,2)(1,1)`$.
- A column with $`y = k`$ becomes a node nested $`k - 1`$ levels deep in $`\le_1`$.

## 5. Numerical evidence

The oracle is Samuel Alexander's calculator for $`R_1^+`$,
[poral](https://github.com/semitrivial/poral). poral has no license, so it is not
included in this repository.

**Agreement with a hand-made table.** The spreadsheet "Sheetified Patterns of
Resemblance" (author unknown) matches pair sequences with $`R_1^+`$-patterns by hand. On
469 of its 2-row rows, $`\Phi(M)`$ gives the same ordinal in 451 rows (compared with poral).

- The 18 misses are all errors of the sheet. In 14 rows the sheet's pattern equals $`\Phi`$
  of another matrix. The other 4 rows repeat the ordinal of the previous row.
- The sheet's point must be read as the last indecomposable node that no smaller node
  reaches by $`\le_1`$. With this reading the rows agree.

**Agreement of the orders.** Standard matrices were generated by expansions and prefixes,
and the lexicographic order was compared with poral's order.

| matrices | adjacent pairs | random pairs | violations |
|---|---|---|---|
| from $`(0,0)\ldots(3,3)`$, at most 8 columns | 3,013 | 1,008,223 | 0 |
| from $`(0,0)\ldots(4,4)`$, at most 9 columns | 5,291 | 823,565 | 0 |
| from $`(0,0)\ldots(5,5)`$, at most 9 columns | 5,328 | 823,337 | 0 |
| from $`(0,0)\ldots(4,4)`$, at most 11 columns | 95,515 | 3,880,540 | 0 |
| around sheet rows 460–467, at most 13 columns | 35,626 | 936,327 | 0 |
| total | 144,773 | 7,471,992 | 0 |

- **Surjectivity.** The numerical tests found no gap in the image of $`\Phi`$. That the image
  is the whole core except 0 is now proved on paper (§8).

## 6. Rejected variants

- **$`\mathrm{Coll}`$ without the fold.** It preserves the order below $`\psi(\Omega_3)`$
  and breaks at depth 3. The smallest counterexample is:

```math
\Phi\bigl((0,0)(1,1)(2,2)(3,3)(2,1)(3,2)(4,3)\bigr) \gt \Phi\bigl((0,0)(1,1)(2,2)(3,3)(2,2)\bigr)
```

- **Skipping past the reach.** It preserves the order but leaves a provable gap.
- **The fold $`\oplus`$** (kept). It preserves the order, and no gap was found.

## 7. Programs

- `por/pss.py`: matrices and terms, lexicographic order, Cantor-normal-form addition, and
  the expansion of pair sequences.
- `por/phi.py`: $`\Phi`$. `python3 por/phi.py "(0,0)(1,1)(2,2)"` prints the pattern and the
  matrix of each node.
- `por/tr.py`: the translation $`\mathcal{T}`$ to Wilken's $`\vartheta`$-terms used in the proof
  (§8). `python3 por/tr.py "(0,0)(1,1)(2,2)"` prints `t0(t1(W2))`.

| definition | function |
|---|---|
| epsilon | `is_eps` |
| $`\log`$, $`\lambda`$ | `log0`, `lam` |
| $`\mathrm{Coll}_A`$ | `L`, `Lsum` |
| $`\oplus`$ | `oplus` |
| $`\mathrm{lh}`$ | `lh` |
| anchor | `anchor` |
| $`\Phi(M)`$ | `closure`, `build_pattern` |

## 8. The proof (on paper)

The stronger form $`\iota(\Phi(M)) = 1 + \mathrm{val}(\mathrm{pairTerm}(M))`$ is proved on paper.
The full proof is in [proof/README.md](proof/README.md). It gives both halves of the theorem:
$`\Phi`$ preserves the order, and the points of $`\Phi`$ take every nonzero value of the core.
Each of its three parts was checked by an independent referee; no false statement was found,
and the gaps and minor points they found were repaired. It is formalized in Lean with no `sorry` (see [proof/README.md](proof/README.md), Status); the facts cited from the literature are axioms there, each checked against the papers. The one
outside assumption is that the Lean `Ord.psi` is Buchholz's $`\psi`$; it is used only to name the
image as the core.

The proof has three parts.
1. **Pair sequences** ([proof/COMB.md](proof/COMB.md)). A matrix is standard if and only if it
   satisfies local conditions on its row-0 tree (Theorem SC; the last condition is the
   pair-sequence form of Buchholz's $`G_\nu(a) \lt a`$). From it: $`\mathrm{anchor}`$, $`\log`$ and
   $`\mathrm{lh}`$ give standard matrices, $`\mathrm{lh}`$ terminates, and
   $`o(N) = \omega^{o(\log N)}`$ for non-epsilon $`N`$.
2. **A translation to Wilken's $`\vartheta`$** ([proof/TR.md](proof/TR.md)). An explicit map
   $`\mathcal{T}`$ from matrices to $`\vartheta`$-terms, defined on the trees without going through
   $`\psi`$, with $`\mathrm{val} \circ \mathcal{T} = o`$. No translation between Buchholz's $`\psi`$ and
   $`\vartheta`$ was known before (Weiermann and Wilken leave it open).
3. **The main chain** ([proof/PROOF.md](proof/PROOF.md)). The fold $`\oplus`$ is Wilken's
   computation of the $`\le_1`$-reach, so $`o(\mathrm{lh}(N))`$ is the largest $`\le_1`$-reach of
   $`o(N)`$. The node set $`V`$ is finite and its values are closed under Wilken's bar operator,
   so by Carlson and Wilken's normal forms the isominimal realization of $`\Phi(M)`$ puts the
   point at $`o(M)`$.

**Notes on the definition.** The sum in $`\log`$ must be the sum of §2, which drops smaller
terms. For example, for $`M = (0,0)(1,1)(1,1)(1,0)(2,1)(2,1)(2,0)(3,0)`$ the term
$`\varepsilon_1`$ is dropped. The anchor is not Wilken's bar operator in general: for
$`\varepsilon_{\varepsilon_0} = (0,0)(1,1)(2,0)(3,1)`$ there is no anchor, and the bar value is 1.

## 9. Next

- The extension to 3 rows (trio sequences and $`R_2^+`$); the record is [../BMS/POR.md](../Trio/POR.md).
  The current rule $`\Phi_{3i}`$ shows no order violation below $`(0,0,0)(1,1,1)(2,1,1)`$.
