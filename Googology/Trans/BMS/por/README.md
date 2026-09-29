[← Back](../POR.md) | [English](README.md) | [Japanese](README-ja.md)

# Converting trio sequences to patterns of resemblance

Programs that convert a trio sequence (a 3-row Bashicu matrix) into a pattern of resemblance of
order 2 (Carlson, "Patterns of resemblance of order 2", APAL 158, 2009). The background is in
[../POR.md](../POR.md).

## Usage

### Trio sequence → pattern of resemblance

```
python3 phi3def2.py "(0,0,0)(1,1,1)(1,1,0)(2,2,1)"
```

Output:

```
0 a (n0 (*n1 ([n2 n3])))
```

- The elements of the pattern, from left to right in increasing order: `0`, `a` (= 1), `n0`, `n1`, …; a sum is written `n1+n0`.
- `*` marks the element that stands for the input.
- `(x … z)` means $`x \le_1 z`$, and `[x … z]` means $`x \le_2 z`$.

### Pattern of resemblance → trio sequence

There is no program for this direction yet.

## Algorithm

The algorithm is in two parts, because GitHub renders only a limited amount of math per page:
A.1–A.8 below, and A.9–A.21 in [ALGORITHM-2.md](ALGORITHM-2.md). The labels of A.9–A.21 are
referred to from here by their section numbers.

The algorithm is written as nested lists of branches. Each function is introduced by a sentence that
gives its inputs and its output. Its branches follow in the order of the code, each with a label such
as (C2-5-1). The label starts with the name of the function, so the labels of one function form one
list. "Otherwise" always means "none of the earlier branches at this depth applies".

### A.1 Conventions

- A **term** is $`s = (y, z, B)`$. Here $`y = y(s)`$ is the row-1 entry of the column (its **level**),
  $`z = z(s)`$ is its row-2 entry, and $`B = \mathrm{ch}(s) = (B_1, \ldots, B_k)`$ are its children in order.
  The row-0 entry is the depth in the tree and is not stored.
- $`1 = (0, 0, ())`$ is the matrix $`(0,0,0)`$. A child equal to $`1`$ is a **unit**.
- A **sum** is a finite sequence of terms $`(t_1, \ldots, t_n)`$; $`()`$ is $`0`$. For a sequence
  $`B`$, $`\mathrm{root}(B) = (0, 0, B)`$.
- $`(A, B)`$ is the concatenation of the sequences $`A`$ and $`B`$, and $`U^m`$ is the sequence of
  $`m`$ copies of $`U`$. So $`\mathrm{root}(A, U^m)`$ is the root term whose children are $`A`$
  followed by $`m`$ copies of $`U`$. $`A + B`$ is always the sum of A.2, never concatenation.
- A column is a place in the tree. Words such as "the first up-kid", "the last child", "is an entry of
  the list" refer to places; $`=`$ compares terms. Two equal columns at different places are different
  columns.
- Lists are indexed from 1. $`\bot`$ is an entry of a list that stands for "no column", and
  $`\mathrm{none}`$ is the absent value.
- For a column $`K`$:
  - an **up-kid** of $`K`$ is a child $`c`$ with $`z(c) = 1`$ and $`y(c) = y(K) + 1`$;
    $`\mathrm{up}(K)`$ is the list of them, in order;
  - $`\mathrm{Rest}(K)`$ is the list of the other children of $`K`$, in order;
  - a **same-level child** of $`K`$ is a child $`c`$ with $`z(c) = 1`$ and $`y(c) = y(K)`$.

### A.2 The trees, the order and the sum (`tss.py`)

**Parsing.** $`\mathrm{parse}`$ reads a string and gives a list of columns. Each piece of the form
"(" … ")" without inner parentheses is one column; everything else is ignored.
- (parse-1) If the inside of the parentheses is blank, the column is $`(0)`$.
- (parse-2) Otherwise the column is the list of the comma-separated integers inside.

Each column is then padded with zeros to length 3. Entries after the third are kept by
$`\mathrm{parse}`$ and not used later.

**The tree.** $`\mathrm{tree}(M)`$ takes a list of columns $`M_1, \ldots, M_n`$, with
$`M_i = (x_i, y_i, z_i)`$, and gives a sum.
- The **parent** of $`M_i`$ is $`M_j`$ for the largest $`j \lt i`$ with $`x_j \lt x_i`$.
  - (tree-1) If such a $`j`$ exists, $`M_i`$ is a child of $`M_j`$ (children in increasing order of $`i`$).
  - (tree-2) Otherwise $`M_i`$ is a **root**.
- The term of $`M_i`$ is $`T(i) = (y_i, z_i, (T(c_1), \ldots, T(c_k)))`$, where
  $`c_1 \lt \cdots \lt c_k`$ are its children.
- $`\mathrm{tree}(M) = (T(r_1), \ldots, T(r_m))`$ for the roots $`r_1 \lt \cdots \lt r_m`$. This is the
  sum $`\hat{M}`$ of the matrix.

**The order.** $`\mathrm{cols}(s, e)`$ is the list of columns of the term $`s`$ placed at depth $`e`$:

```math
\mathrm{cols}(s, e) = \bigl((e, y(s), z(s)),\ \mathrm{cols}(B_1, e+1),\ \ldots,\ \mathrm{cols}(B_k, e+1)\bigr)
```

For a sum, $`\mathrm{mat}(t_1, \ldots, t_n)`$ is the concatenation of
$`\mathrm{cols}(t_1, 0), \ldots, \mathrm{cols}(t_n, 0)`$. It is the matrix of the sum.
- Lists of triples are compared lexicographically. The first position where they differ decides,
  and the triples there are compared lexicographically. If one list is a proper prefix of the other,
  it is the smaller.
- Terms: $`s \lt t`$ iff $`\mathrm{cols}(s, 0) \lt \mathrm{cols}(t, 0)`$. Sums: by $`\mathrm{mat}`$.

**The sum.** $`A + B`$ for sequences of terms $`A`$ and $`B`$:
- (add-1) If $`B = ()`$, then $`A + B = A`$.
- (add-2) Otherwise, while $`A \ne ()`$ and the last term of $`A`$ is smaller than $`B_1`$, remove the
  last term of $`A`$. Then $`A + B`$ is $`(A, B)`$.

$`\Sigma(t_1, \ldots, t_n) = (\cdots((() + (t_1)) + (t_2)) \cdots) + (t_n)`$ is the sum of a list,
added from the left. $`\Sigma() = ()`$.

**Output.** $`\mathrm{show}`$ writes a sum as its matrix $`\mathrm{mat}`$, one "(x,y,z)" per column.

### A.3 Basic functions (D1)

**Epsilon terms.** $`\mathrm{eps}(t)`$ is true iff $`y(t) = 0`$, $`\mathrm{ch}(t) \ne ()`$ and the
last child of $`t`$ has $`y \ge 1`$.

**The 2-row log.** For a root term $`t`$, let $`H`$ be its children with $`y \ge 1`$ and
$`O_1, \ldots, O_r`$ its children with $`y = 0`$, each in order.
- (log-1) If $`H \ne ()`$, then $`\log(t) = \Sigma(\mathrm{root}(H), O_1, \ldots, O_r)`$.
- (log-2) Otherwise $`\log(t) = \Sigma(O_1, \ldots, O_r)`$.

**The 2-row reach increment.** For a root term $`t`$ with last child $`B_k`$, let
$`u = \mathrm{root}(\mathrm{ch}(B_k))`$.
- (lam-1) If $`\mathrm{eps}(u)`$, then $`\lambda(t) = (u)`$.
- (lam-2) Otherwise $`\lambda(t) = \log(u)`$.

**The owner lookup.** $`\mathrm{own}(\sigma, y)`$ takes a stack $`\sigma`$ of entries and a level
$`y`$. An entry is $`(y_e, h_e)`$ or $`(y_e, h_e, \mathrm{ok}_e)`$: the level of an $`\omega`$ column,
the shift of its image, and (in C1) a flag. Let $`a`$ be the topmost entry with $`y_a \le y`$.
- (own-1) If $`a`$ exists, has a third component, and $`\mathrm{ok}_a`$ is false, then the result is
  $`\mathrm{none}`$.
- (own-2) If $`a`$ exists otherwise, the result is $`a`$.
- (own-3) If no entry has $`y_a \le y`$, the result is $`\mathrm{none}`$.

**Other small functions.**
- $`\mathrm{split}(W) = (\mathrm{hi}, \mathrm{lo})`$: $`\mathrm{hi}`$ is the list of the children of
  $`W`$ with $`y \ge 2`$ or $`z = 1`$, and $`\mathrm{lo}`$ the list of the others, each in order.
- $`\Omega\mathrm{pre}(\mathrm{hi})`$ is the longest prefix of $`\mathrm{hi}`$ whose columns all have
  $`z = 1`$.
- $`W + k = (y(W), z(W), (\mathrm{ch}(W), 1^k))`$: $`k`$ units appended to the children.
- $`\mathrm{anchor}(t)`$:
  - (anchor-1) If $`y(t) = 0`$ and $`t`$ has $`k \ge 2`$ children, then
    $`\mathrm{anchor}(t) = \mathrm{root}(B_1, \ldots, B_{k-1})`$.
  - (anchor-2) Otherwise $`\mathrm{anchor}(t) = \mathrm{none}`$.

### A.4 The collapse C1 (D2)

$`\mathrm{C1}_N`$ is Buchholz's collapse $`\Omega_1 \mapsto N`$, read with a stack of owners.

$`\mathrm{C1}_N(s;\ \sigma, \mathrm{last}, \mathrm{mn})`$ takes a root term $`N`$, a column $`s = (y, z, B)`$,
a stack $`\sigma`$ of entries $`(y_e, h_e, \mathrm{ok}_e)`$ or the mark $`\mathrm{fin}`$, and two flags.
It gives a term, or a **wrapped** column $`[\![c]\!]`$ (a column that will be put inside a level-1 column).
- (C1-1) If $`y = 0`$, then the result is $`s`$.
- (C1-2) Otherwise let $`\varphi`$ be true iff $`\sigma = \mathrm{fin}`$; if $`\varphi`$, replace $`\sigma`$ by the empty stack. Then:
  - (C1-2-1) If $`z = 1`$ and $`\sigma \ne ()`$: let $`h`$ be the shift of the top entry of $`\sigma`$, and $`\mathrm{ok}`$ its flag ($`\mathrm{ok} = \mathrm{true}`$ if it has no flag). The result is $`(y - h,\ 1,\ \mathrm{C1s}_N(B;\ (\sigma, (y, h, \mathrm{ok})), \mathrm{last}))`$.
  - (C1-2-2) If $`z = 1`$ and $`\sigma = ()`$: let $`\mathrm{ok} = \lnot\varphi \lor \mathrm{mn}`$.
    - (C1-2-2-1) If $`y = 2`$, the result is the wrapped column $`[\![(2,\ 1,\ \mathrm{C1s}_N(B;\ ((2, 0, \mathrm{ok})), \mathrm{last}))]\!]`$.
    - (C1-2-2-2) Otherwise the result is $`(y - 1,\ 1,\ \mathrm{C1s}_N(B;\ ((y, 1, \mathrm{ok})), \mathrm{last}))`$.
  - (C1-2-3) If $`z \ne 1`$: let $`a = \mathrm{own}(\sigma, y)`$.
    - (C1-2-3-1) If $`a \ne \mathrm{none}`$, and not ($`\mathrm{last}`$, $`B = ()`$, $`y = y_a`$ and $`a`$ is the bottom entry of $`\sigma`$ itself, not an equal entry), the result is $`(y - h_a,\ 0,\ \mathrm{C1s}_N(B;\ \sigma, \mathrm{last}))`$. The exception is the $`\Omega_1`$-multiplier: a final bare marker on the level of the outermost $`\omega`$ column.
    - (C1-2-3-2) Otherwise let $`K = \mathrm{C1s}_N(B;\ \mathrm{fin}, \mathrm{last})`$. If $`y = 1`$, the result is $`\mathrm{root}(\mathrm{ch}(N) + K)`$.
    - (C1-2-3-3) Otherwise the result is $`(y - 1,\ 0,\ K)`$.

$`\mathrm{C1s}_N(B;\ \sigma, \mathrm{last}, l)`$ is C1 on a list $`B = (B_1, \ldots, B_k)`$; $`l`$ is the position that gets the flag $`\mathrm{last}`$ ($`l = k`$ when it is not given). For $`i = 1, \ldots, k`$ let $`\mathrm{mn}_i`$ be true iff $`z(B_i) = 1`$, $`i \lt k`$, $`z(B_{i+1}) = 1`$ and $`\mathrm{ch}(B_{i+1}) = ()`$, and let $`r_i = \mathrm{C1}_N(B_i;\ \sigma, \mathrm{last} \land i = l, \mathrm{mn}_i)`$. Build a list $`O`$, for $`i = 1, \ldots, k`$:
- (C1s-1) If $`r_i`$ is wrapped:
  - (C1s-1-1) if the last entry of $`O`$ is a group of wrapped columns, add the column of $`r_i`$ at the end of that group;
  - (C1s-1-2) otherwise add a new group that holds the column of $`r_i`$.
- (C1s-2) Otherwise add $`r_i`$ to $`O`$.

The result is $`\Sigma`$ of $`O`$, where a group $`(c_1, \ldots, c_p)`$ counts as the term $`(1, 0, (c_1, \ldots, c_p))`$. (The stack $`\sigma`$ is the same for every $`B_i`$; with $`\sigma = \mathrm{fin}`$ each $`B_i`$ sees $`\mathrm{fin}`$.)

$`\mathrm{c1fixed}(G;\ N, \mathrm{last})`$ is true iff $`G \ne ()`$ and $`\mathrm{C1s}_N(G;\ (), \mathrm{last}) = ((1, 0, G))`$.

### A.5 The read context

The collapse C2 and the read of a same-level $`\omega`$ column (A.6, A.7) take a **read context** $`\rho = (\rho_C, \rho_D, \rho_1)`$. Each part is $`\mathrm{none}`$ or:
- $`\rho_C = (c, \ell_C, \Delta_C)`$: the $`\omega`$ column being read belongs to the node $`c`$, on level $`\ell_C`$, with the level list $`\Delta_C`$ (A.7);
- $`\rho_D = (x', \ell')`$: a level column of the $`\le_2`$-able node $`x'`$ is being read, and $`\ell'`$ is the level of its column $`D`$ (A.13);
- $`\rho_1 = (d, \kappa)`$: the read belongs to the successor $`d`$, and $`\kappa`$ is the next level column (or $`\mathrm{none}`$).

The context is passed down unchanged unless a branch says otherwise. **Every computation of $`\mathrm{lh}`$ (A.17) starts with the empty context $`\rho_\varnothing = (\mathrm{none}, \mathrm{none}, \mathrm{none})`$**, also when it is called inside another computation.

### A.6 The collapse C2 (D3)

$`\mathrm{C2}_x`$ is $`\Omega_\omega \mapsto x`$, $`\Omega_{\omega+j} \mapsto \Omega_j`$. Every marker collapses to the target of the $`\omega`$ column that owns it.

$`\mathrm{C2}_x(s;\ \ell, \sigma, \mathrm{last};\ \rho)`$ takes a root term $`x`$ (the target), a column $`s = (y, z, B)`$, the level $`\ell`$ of the $`\omega`$ column $`D`$ being collapsed, a stack $`\sigma`$ of entries $`(y_e, h_e)`$, a flag and a context. It gives a term.
- (C2-1) If $`y = 0`$, the result is $`s`$.
- (C2-2) If $`z = 1`$, $`\rho_D = (x', \ell')`$, $`y = \ell'`$ and $`y \lt \ell`$ (a $`D`$-level $`\omega`$ column deep inside a level column): let $`\rho'`$ be $`\rho`$ with $`\rho_D`$ replaced by $`\mathrm{none}`$.
  - (C2-2-1) If $`x'`$ is $`\le_2`$-able (A.13) with $`U'`$, $`q'`$ and last $`\omega`$ column $`D'`$, and $`\mathrm{kdl}(D', L(D')) = s`$ (A.11): the result is $`\mathrm{Kimg}(s;\ x', \ell', (\delta'_1, \ldots, \delta'_{q'}), \mathrm{none}, \mathrm{last}, \mathrm{none}, \mathrm{true};\ \rho')`$, where $`\delta'_i = (\mathrm{ch}(x'), U'^i)`$.
  - (C2-2-2) Otherwise the result is $`\mathrm{Kimg}(s;\ x', \ell', \mathrm{ch}(x'), \mathrm{none}, \mathrm{last};\ \rho')`$, with the single base $`\mathrm{ch}(x')`$.
- (C2-3) If $`z = 1`$, $`\rho_C = (c, \ell_C, \Delta_C)`$, $`y = \ell_C`$ and $`y = \ell`$: the result is $`\mathrm{Kimg}(s;\ c, \ell_C, \Delta_C, \mathrm{none}, \mathrm{last};\ \rho)`$.
- (C2-4) If $`z = 1`$ otherwise:
  - (C2-4-1) If $`\sigma \ne ()`$, let $`h`$ be the shift of its top entry. The result is $`(y - h,\ 1,\ \mathrm{C2s}_x(B;\ \ell, (\sigma, (y, h)), \mathrm{last};\ \rho))`$.
  - (C2-4-2) If $`\sigma = ()`$ and $`y - \ell \le 1`$, the result is $`(1,\ 0,\ ((2,\ 1,\ \mathrm{C2s}_x(B;\ \ell, ((y, y - 2)), \mathrm{last};\ \rho))))`$.
  - (C2-4-3) Otherwise the result is $`(y - \ell,\ 1,\ \mathrm{C2s}_x(B;\ \ell, ((y, \ell)), \mathrm{last};\ \rho))`$.
- (C2-5) If $`z \ne 1`$: let $`a = \mathrm{own}(\sigma, y)`$.
  - (C2-5-1) If $`a \ne \mathrm{none}`$, and not ($`\mathrm{last}`$, $`B = ()`$, $`y = y_a`$ and $`y_a - h_a = 2`$), the result is $`(y - h_a,\ 0,\ \mathrm{C2s}_x(B;\ \ell, \sigma, \mathrm{last};\ \rho))`$.
  - (C2-5-2) If $`a \ne \mathrm{none}`$ (the exception holds: a final bare marker whose owner is two levels up is read relative to $`D`$): let $`j = y - \ell`$ and $`K = \mathrm{C2s}_x(B;\ \ell, \sigma, \mathrm{last};\ \rho)`$.
    - (C2-5-2-1) If $`j \le 0`$, the result is $`\mathrm{root}(\mathrm{ch}(x) + K)`$.
    - (C2-5-2-2) Otherwise the result is $`(j,\ 0,\ K)`$.
  - (C2-5-3) If $`a = \mathrm{none}`$ and $`y \lt \ell`$, the result is $`\mathrm{root}(\mathrm{ch}(x) + \mathrm{C1s}_x(B;\ (), \mathrm{false}))`$.
  - (C2-5-4) Otherwise let $`K = \mathrm{C2s}_x(B;\ \ell, (), \mathrm{last};\ \rho)`$.
    - (C2-5-4-1) If $`y = \ell`$, the result is $`\mathrm{root}(\mathrm{ch}(x) + K)`$.
    - (C2-5-4-2) Otherwise the result is $`(y - \ell,\ 0,\ K)`$.

$`\mathrm{C2s}_x(B;\ \ell, \sigma, \mathrm{last};\ \rho)`$ is C2 on a list $`B = (B_1, \ldots, B_k)`$. Let $`r_i = \mathrm{C2}_x(B_i;\ \ell, \sigma, \mathrm{last} \land i = k;\ \rho)`$. Build a list $`O`$, for $`i = 1, \ldots, k`$:
- (C2s-1) If $`z(B_i) = 1`$, $`\sigma = ()`$, $`r_i = (1, 0, R)`$, $`O \ne ()`$, the last entry $`o`$ of $`O`$ has $`y(o) = 1`$, $`z(o) = 0`$, $`\mathrm{ch}(o) \ne ()`$ and a last child with $`z = 1`$, and $`z(B_n) = 1`$ for $`n = |O|`$ (the input column whose position is the current length of $`O`$): replace $`o`$ by $`(1, 0, (\mathrm{ch}(o), R))`$. (Consecutive wrapped $`\omega`$ columns merge into one $`U`$-form.)
- (C2s-2) Otherwise add $`r_i`$ to $`O`$.

The result is $`\Sigma(O)`$.

### A.7 The read of a same-level $`\omega`$ column (D3)

A **level list** $`\Delta`$ is either a list $`(\Delta_1, \ldots, \Delta_n)`$ of children lists (the levels $`\delta_m = \mathrm{ch}(d_m)`$ of A.13), or a **single base** $`b`$ (one children list).

$`\mathrm{KI}(B;\ x, \ell, \Delta, t_0, \mathrm{last};\ \rho)`$ reads the children $`B = (B_1, \ldots, B_k)`$ of a same-level $`\omega`$ column. $`x`$ is a root term, $`\ell`$ a level, $`t_0`$ a term or $`\mathrm{none}`$. It gives a sum. Keep a list $`O`$ and a pending run $`R`$, both empty at the start. To **flush** with a flag $`f`$: if $`R \ne ()`$, add the terms of $`\mathrm{C2s}_x(R;\ \ell, (), f;\ \rho)`$ to $`O`$ and empty $`R`$. For $`i = 1, \ldots, k`$, with $`g = B_i`$ and $`\mathrm{lg} = \mathrm{last} \land i = k`$:
- (KI-1) If $`y(g) \ne 0`$, not ($`z(g) = 1`$ and $`y(g) = \ell`$), and not ($`z(g) = 0`$ and $`y(g) \ge \ell`$): add $`g`$ to $`R`$.
  - (KI-1-1) If $`i = k`$, flush with $`\mathrm{lg}`$.
- Otherwise flush with $`\mathrm{false}`$, and then:
  - (KI-2) If $`y(g) = 0`$, add $`g`$ to $`O`$.
  - (KI-3) If $`z(g) = 1`$ and $`y(g) = \ell`$, add $`\mathrm{Kimg}(g;\ x, \ell, \Delta, t_0, \mathrm{lg};\ \rho)`$.
  - (KI-4) If $`z(g) = 0`$, $`y(g) = \ell`$, $`\mathrm{ch}(g) = ()`$, $`\mathrm{lg}`$ and $`t_0 \ne \mathrm{none}`$, add $`t_0`$ (the final bare marker is the $`\Omega_1`$-multiplier one level up).
  - (KI-5) If $`z(g) = 0`$ and $`y(g) = \ell`$, add $`\mathrm{root}(\mathrm{ch}(x) + \mathrm{KI}(\mathrm{ch}(g);\ x, \ell, \Delta, \mathrm{none}, \mathrm{lg};\ \rho))`$.
  - (KI-6) If $`z(g) = 0`$ and $`y(g) \gt \ell`$, add $`(y(g) - \ell,\ 0,\ \mathrm{KI}(\mathrm{ch}(g);\ x, \ell, \Delta, \mathrm{none}, \mathrm{lg};\ \rho))`$.
  - (KI-7) Otherwise add $`\mathrm{C2}_x(g;\ \ell, (), \mathrm{lg};\ \rho)`$. This case does not occur: (KI-1) to (KI-6) cover every column.

The result is $`\Sigma(O)`$.

$`\mathrm{Kimg}(K;\ x, \ell, \Delta, t_0, \mathrm{last}, c, j_0;\ \rho)`$ is the summand of a same-level $`\omega`$ column $`K`$ with $`y(K) = \ell`$. $`c`$ is a cap ($`\mathrm{none}`$ or an integer; $`\mathrm{none}`$ when not given) and $`j_0`$ a flag ($`\mathrm{false}`$ when not given). It gives a root term.
- (Kimg-1) If $`\Delta = (\Delta_1, \ldots, \Delta_n)`$ is a list: let $`B = \mathrm{ch}(K)`$, $`j = \min(\mathrm{lev}(K) - 1,\ n - 1)`$ (A.11), and $`V = \mathrm{up}(K)`$. Let $`\kappa`$ (the level column that $`K`$ may share) be:
  - (Kimg-1-1) if $`\rho_1 = (d, \kappa')`$ and $`d = x`$: $`\kappa = \kappa'`$;
  - (Kimg-1-2) otherwise, if $`x \ne \mathrm{none}`$ and $`x`$ is $`\le_2`$-able: $`\kappa = K_1(x)`$ (below);
  - (Kimg-1-3) otherwise $`\kappa = \mathrm{none}`$.

  Then:
  - (Kimg-1-4) If $`V \ne ()`$, $`\kappa \ne \mathrm{none}`$, $`V_1 = \kappa`$ and $`\mathrm{Rest}(V_1) \ne ()`$ (`kbcut`: $`K`$ shares the level of $`K_1`$): remove the child $`V_1`$ from $`B`$ and let $`j = \min(|V| - 1,\ n - 1)`$.
    - (Kimg-1-4-1) If $`c \ne \mathrm{none}`$, let $`j = \max(0, \min(j, c))`$ (`kb2`).

    Then remove the children $`V_2, \ldots, V_{1+j}`$ from $`B`$.
  - (Kimg-1-5) Otherwise, if $`j \ne 0`$ or $`V \ne ()`$, remove all up-kids of $`K`$ from $`B`$.
  - (Kimg-1-6) If $`j_0`$ (**the rule `kdl0`**): let $`\Lambda = L(K)`$ (A.11), let $`j`$ be the largest $`i - 1`$ with $`\Lambda_i \ne \bot`$ and $`\Lambda_i = \Lambda_1`$ as terms (or $`0`$ if there is none), $`j = \min(j, n - 1)`$, and let $`B`$ be $`\mathrm{ch}(K)`$ without its up-kids. Reason: a $`D`$-level $`\omega`$ column read after an elder sibling (or nested in a same-level child) is read on the lowest level of its last chain, not above its top.

  The result is $`\mathrm{root}(\Delta_{1+j} + \mathrm{KI}(B;\ x, \ell, \Delta, t_0', \mathrm{last};\ \rho))`$, where $`t_0' = t_0`$ if $`\mathrm{last}`$ and $`t_0' = \mathrm{none}`$ otherwise.
- (Kimg-2) Otherwise ($`\Delta = b`$ is a single base) the result is $`\mathrm{root}(b + \mathrm{KI}(\mathrm{ch}(K);\ x, \ell, b, t_0', \mathrm{last};\ \rho))`$, with $`t_0'`$ as above.

$`K_1(x)`$ for a $`\le_2`$-able $`x`$ is the first up-kid of its column $`D`$ (A.13), or $`\mathrm{none}`$ if $`D`$ has no up-kid.

$`\mathrm{shares}(g, K_1)`$ is true iff $`\mathrm{up}(g) \ne ()`$ and the first up-kid of $`g`$ equals $`K_1`$.

### A.8 The copy of a root $`\omega`$ run (D4)

$`\mathrm{Up}(a;\ N, \mathrm{last})`$ lifts a root $`\omega`$ column $`a`$ by one level. $`N`$ is a root term. It uses $`r(s, Y, \mathrm{lst})`$, where $`s = (y, z, B)`$ is a column, $`Y`$ a list of levels (of the $`\omega`$ columns above $`s`$) and $`\mathrm{lst}`$ a flag:
- (Up-1) If $`y = 0`$, then $`r = s`$.
- (Up-2) If $`\mathrm{lst}`$, $`B = ()`$, $`z = 0`$ and $`N \ne \mathrm{none}`$: let $`Y'`$ be the entries $`o`$ of $`Y`$ with $`o \le y`$, in order. If $`Y' \ne ()`$, ($`|Y'| = 1`$, or every entry of $`Y'`$ is $`y`$ and $`\max Y \gt y`$), the last entry of $`Y'`$ is $`y`$, and $`Y_1 = y`$, then $`r = N`$ (the final marker is the $`\Omega_1`$-multiplier $`N`$). If this condition fails, go on with (Up-3).
- (Up-3) Otherwise let $`Y'' = (Y, y)`$ if $`z = 1`$ and $`Y'' = Y`$ if not. Then $`r = (y + 1,\ z,\ (r(B_1, Y'', \mathrm{lst} \land 1 = k), \ldots, r(B_k, Y'', \mathrm{lst} \land k = k)))`$, where the flag goes to the last child only.

$`\mathrm{Up}(a;\ N, \mathrm{last}) = (2,\ 1,\ (r(B_i, (y(a)), \mathrm{last} \land i = k))_{i = 1, \ldots, k})`$ for $`\mathrm{ch}(a) = (B_1, \ldots, B_k)`$.

The algorithm continues in [ALGORITHM-2.md](ALGORITHM-2.md) (A.9–A.21).
