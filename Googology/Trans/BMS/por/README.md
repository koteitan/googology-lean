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

The program computes the pattern $`\Phi_3(M)`$ of the input matrix $`M`$: a finite set of sums (its elements), the relations $`\le_1`$ and $`\le_2`$ on it, and the element that stands for $`M`$. Steps 1–6 are the main procedure; the operations that they call follow in the order of their first call (A.1–A.8 below, A.9–A.18 in [ALGORITHM-2.md](ALGORITHM-2.md)), and the notation and the way the branches are written are in the appendix [Notation](ALGORITHM-2.md#notation).

<a id="step-1"></a>
### Step 1. Read the input and build the tree

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

So the input $`M`$ becomes the sum $`\hat{M}`$ of its root terms. Here a **term** $`s = (y, z, B)`$ is a column with its subtree: $`y = y(s)`$ is its row-1 entry, $`z = z(s)`$ its row-2 entry, and $`B = \mathrm{ch}(s)`$ the list of its children. A **sum** is a finite sequence of terms. The rest of the notation is in [Notation](ALGORITHM-2.md#notation).

<a id="step-2"></a>
### Step 2. Start the node set

The nodes are sums. Start with $`V = \{(), (1), \hat{M}\}`$, where $`() = 0`$ and $`1 = (0, 0, ())`$ is the term of the matrix $`(0,0,0)`$.

<a id="step-3"></a>
### Step 3. Close the node set

Repeat until no new node is added. For each node $`v = (t_1, \ldots, t_n) \in V`$, add to $`V`$:

1. every prefix $`(t_1, \ldots, t_j)`$ and every summand $`(t_i)`$;
2. if $`v = (t)`$ has one term, also:
   1. $`(\mathrm{anchor}(t))`$, if it is not $`\mathrm{none}`$ ([A.1](#a1));
   2. the sum $`\mathrm{lh}(t)`$, the $`\le_1`$-reach of $`t`$ ([A.2](#a2));
   3. $`(e)`$ for every $`e \in \mathrm{Img}(t)`$ (below);
   4. $`(d)`$ for every $`d \in \mathrm{succ}(t)`$, the $`\le_2`$-successors of $`t`$ ([A.3](#a3));
   5. $`(w)`$ for every $`w \in \mathrm{wit}(t)`$, the witnesses of $`t`$ ([A.4](#a4)).

**Recorded terms.** Some branches **record** a term $`e`$ **under** a key $`k`$ (a root term). $`\mathrm{Img}(k)`$ is the set of the terms recorded under $`k`$ during the computations of $`\mathrm{lh}(u)`$ for the one-term nodes $`(u) \in V`$, with every computation nested in them. The key matters: a term recorded under $`k`$ is added only through the node $`(k)`$.

The result is the least set of sums that contains the starting set and is closed under these additions. (The program adds the nodes by a work list; the order does not change the result.) For a set $`X`$ of sums, $`\mathrm{cl}(X)`$ is the result of this step started from $`\{(), (1)\} \cup X`$.
- (cl-1) If $`V`$ gets more than 300 nodes, the program stops with the error "too many nodes".

<a id="step-4"></a>
### Step 4. Add the Def 9.4 copies

This step adds the Def 9.4 copies (Carlson 2009, Def 9.4). $`\mathrm{copy}(x)`$ for a $`\le_2`$-able $`x`$ (A.3) is the first $`e = \mathrm{root}(P, U^m)`$, $`m = 1, \ldots, 7`$, with $`\mathrm{dead}(e)`$ false (A.3); it is $`\mathrm{none}`$ if there is none.

Repeat at most 4 times: let $`J`$ be the one-term nodes of $`V`$ in increasing order (A.5), and $`X = \emptyset`$. For each $`(x) \in J`$ that is $`\le_2`$-able, in order:
- (copy-1) if $`\mathrm{lh}(x) = (d_q)`$, skip it;
- (copy-2) if some $`(u) \in J`$ with $`u \lt x`$ has $`\mathrm{lh}(u) = \mathrm{lh}(x)`$, skip it;
- (copy-3) otherwise, if $`e = \mathrm{copy}(x) \ne \mathrm{none}`$ and $`(e) \notin V`$, add $`(e)`$ to $`X`$.

Then:
- (copy-4) if $`X = \emptyset`$, stop repeating;
- (copy-5) otherwise let $`V = \mathrm{cl}(V \cup X)`$.

<a id="step-5"></a>
### Step 5. Sort the nodes and compute the relations

For the node set $`V`$ after Step 4:
- The nodes are $`V`$, sorted by $`\mathrm{mat}`$ (A.5): $`v_0 = () \lt v_1 = (1) \lt \cdots`$.
- The **reach** of $`v_i`$: if $`v_i = (t)`$ has one term, it is the largest $`r \ge i`$ with $`\mathrm{mat}(v_r) \le \mathrm{mat}(\mathrm{lh}(t))`$; otherwise, or if there is no such $`r`$, it is $`i`$. So $`v_i \le_1 v_j`$ iff $`i = j`$, or $`v_i`$ has one term and $`i \le j \le \mathrm{reach}(i)`$.
- The **$`\le_2`$ pairs** are $`(i, j)`$ with $`v_i = (t)`$ and $`v_j = (d)`$ for $`d \in \mathrm{succ}(t)`$.
- The **point** is the index of $`\hat{M}`$.
- Addition is the relation $`v_i + v_j = v_k`$ of A.5, as in the 2-row version; the program does not print it.

<a id="step-6"></a>
### Step 6. Print the pattern

One line: the elements $`v_0 \lt v_1 \lt \cdots`$ from left to right, written `0` for $`v_0 = 0`$, `a` for the term $`(0,0,0)`$, `n0`, `n1`, … for the other one-term elements in increasing order, and `x+y+…` for a sum of such names; `*` before the point; `(` before $`v_i`$ and `)` after its reach $`v_{r}`$ when $`r \gt i`$; `[` before $`v_i`$ and `]` after $`v_j`$ for each $`\le_2`$ pair $`(i, j)`$. At one element, the brackets of the longer span open first, and the bracket opened last closes first. With `--table`, one line per element instead: `*` if $`i`$ is the point, $`i`$, $`\mathrm{show}(v_i)`$, `reach` and the reach of $`v_i`$, and `<=2` with the $`j`$ of its $`\le_2`$ pairs.

<a id="a1"></a>
### A.1 The anchor (D1)

$`\mathrm{anchor}(t)`$ takes a term $`t`$ with children $`B_1, \ldots, B_k`$ and gives a root term or $`\mathrm{none}`$; it is called from Step 3.
- (anchor-1) If $`y(t) = 0`$ and $`t`$ has $`k \ge 2`$ children, then
  $`\mathrm{anchor}(t) = \mathrm{root}(B_1, \ldots, B_{k-1})`$.
- (anchor-2) Otherwise $`\mathrm{anchor}(t) = \mathrm{none}`$.

<a id="a2"></a>
### A.2 The reach $`\mathrm{lh}`$ (D9)

$`\mathrm{lh}(t)`$ takes a root term $`t`$ and gives its $`\le_1`$-reach, a sum; it is called from Steps 3, 4 and 5, from the fold $`\oplus`$ (A.13), from $`\mathrm{lh}_1`$ (A.9) and from itself. It starts with the empty read context $`\rho_\varnothing`$ ([Notation](ALGORITHM-2.md#read-context)).
- (lh-1) If $`t = 1`$ or $`y(t) \ne 0`$, then $`\mathrm{lh}(t) = (t)`$.
- (lh-2) If $`t`$ is not epsilon, then $`\mathrm{lh}(t) = (t) + \lambda(t)`$.
- (lh-3) If $`\mathrm{d1}(t) = (x, K, m, q)`$ ($`t = d_m`$ and $`K = K_m`$ has children):
  - (lh-3-1) If $`\mathrm{Rest}(K) = ()`$ and not ($`m \lt q`$ and $`\mathrm{chtop}(K)`$) (only chain children): let $`H = \mathrm{sub}(K)`$. Match $`H`$ in $`\Lambda`$ from position $`m`$: let $`p = m`$ and $`s = 0`$; for $`i = m, \ldots, |\Lambda|`$:
    - (lh-3-1-1) if $`\Lambda_i \ne \bot`$, $`s \lt |H|`$ and $`\Lambda_i = H_{s+1}`$: let $`s = s + 1`$ and $`p = i`$;
      - (lh-3-1-1-1) if then $`s = |H|`$, stop the loop.

    Then:
    - (lh-3-1-2) if some $`i`$ with $`p \lt i \le |\Lambda|`$ has $`\Lambda_i = \bot`$, then for the first such $`i`$, $`\mathrm{lh}(t) = (d_i)`$;
    - (lh-3-1-3) otherwise $`\mathrm{lh}(t) = (d_q)`$.
  - (lh-3-2) If $`m \lt q`$ and $`\mathrm{chtop}(K)`$: compute $`\mathrm{lh}(x)`$. If that computation recorded $`\mathrm{pre}(x)`$ (LG-3), then $`\mathrm{lh}(t) = \mathrm{pre}(x)`$; otherwise $`\mathrm{lh}(t) = \mathrm{lh}(x)`$. (The children of $`K`$ are read at the top, in LG-2.)
  - (lh-3-3) Otherwise let $`n' = d_{m+1}`$ if $`m \lt q`$, and $`n' = t`$ if $`m = q`$. Let $`R = \mathrm{LK}(x, K, m)`$ and $`\rho = ((t, y(K), (\mathrm{ch}(n'))),\ (x, y(D)),\ \mathrm{none})`$. Let $`S = \mathrm{F}((t);\ t, (y(K), z(K), R), y(K), \mathrm{ch}(n'), (\mathrm{ch}(n')), \mathrm{none}, \mathrm{true};\ \rho)`$.
    - (lh-3-3-1) **The named case `kcross`.** If $`m + 1 = q`$, $`K`$ has a same-level child, and $`\mathrm{blk}(U)`$: for each child $`c`$ of $`D`$ with $`y(c) = 0`$, in order, let $`S = S \oplus \mathrm{root}(\mathrm{ch}(c))`$. Reason: the crossing interval just below the top reaches as far as $`x`$ does at the top.

    Then $`\mathrm{lh}(t) = S`$.
- (lh-4) If $`\mathrm{dead}(t)`$, then $`\mathrm{lh}(t) = (t)`$.
- Let $`A = \mathrm{ch}(t)`$ and $`W`$ its last entry.
- (lh-5) If $`z(W) = 1`$ (a root $`\omega`$ run): let $`a_1, \ldots, a_k`$ be the longest run of entries with $`z = 1`$ at the end of $`A`$. Let $`S = (t, t)`$, and for $`i = 1, \ldots, k`$ let $`S = S \oplus \mathrm{root}(A, (1, 0, (\mathrm{Up}(a_1;\ t, 1 = k), \ldots, \mathrm{Up}(a_i;\ t, i = k))))`$. Then $`\mathrm{lh}(t) = S`$.
- (lh-6) If $`t`$ is $`\le_2`$-able, then $`\mathrm{lh}(t) = \mathrm{lh}_1(t)`$ (A.9).
- Let $`(\mathrm{hi}, \mathrm{lo}) = \mathrm{split}(W)`$, $`G = \Omega\mathrm{pre}(\mathrm{hi})`$ and $`U = (1, 0, G)`$.
- (lh-7) If $`G \ne ()`$, $`G = \mathrm{hi}`$ and $`\mathrm{c1fixed}(G;\ t, \mathrm{true})`$ (a nesting limit):
  - (lh-7-1) if $`\mathrm{lo} = ()`$: let $`A'`$ be $`A`$ without all the copies of $`U`$ at its end; then $`\mathrm{lh}(t) = \mathrm{lh}(\mathrm{root}(A', U + 1))`$;
  - (lh-7-2) if every entry of $`\mathrm{lo}`$ is $`1`$: let $`r = \mathrm{lev}(G_{|G|})`$ and $`S = \mathrm{lh}(\mathrm{root}(A, U + r))`$ (here $`A`$ still ends with $`W`$, so $`U + r`$ is added after $`W`$); then let $`S = S \oplus 1`$, repeated $`|\mathrm{lo}| - r`$ times (no times if $`|\mathrm{lo}| \le r`$). $`\mathrm{lh}(t) = S`$;
  - otherwise go on with (lh-8).
- (lh-8) The 2-row fold. Let $`S = (t, t)`$. For $`i = 1, \ldots, |\mathrm{hi}|`$ let $`Y = \mathrm{root}(A + \mathrm{C1s}_t(\mathrm{hi}_1, \ldots, \mathrm{hi}_i;\ (), G \ne (), \min(i, |G|)))`$ (the flag $`\mathrm{last}`$ is true iff $`G \ne ()`$, at the position $`\min(i, |G|)`$), and:
  - (lh-8-1) if $`\mathrm{ch}(Y) = (A, W)`$ (the image is $`W`$ again), let $`S = S \oplus \mathrm{root}(P', W + 1)`$, where $`P'`$ is $`A`$ without its last entry;
  - (lh-8-2) otherwise let $`S = S \oplus Y`$.

  Then for each $`g`$ in $`\mathrm{lo}`$, in order:
  - (lh-8-3) if $`y(g) \ge 1`$, let $`S = S \oplus \mathrm{C1}_t(g;\ (), \mathrm{lg}, \mathrm{false})`$, where $`\mathrm{lg}`$ is true iff $`g`$ is the last entry of $`\mathrm{lo}`$;
  - (lh-8-4) otherwise let $`S = S \oplus g`$.

  Then $`\mathrm{lh}(t) = S`$.

<a id="a3"></a>
### A.3 $`\le_2`$-able nodes and successors (D7)

$`\mathrm{le2}(t)`$ takes a root term $`t`$, decides whether it is **$`\le_2`$-able**, $`t = \mathrm{root}(P, U + q)`$, and if so gives $`A`$, $`W`$, $`U`$ and $`q`$; it is called from Step 4, from $`\mathrm{succ}`$, $`\mathrm{dead}`$ and $`\mathrm{d1}`$ below (which Steps 3–5, (lh-3) and (lh-4) call), from (lh-6), and from every branch that asks whether a term is $`\le_2`$-able.
- (le2-1) If $`y(t) \ne 0`$ or $`\mathrm{ch}(t) = ()`$, it is not.
- Let $`A = \mathrm{ch}(t)`$ and let $`W`$ be its last entry.
- (le2-2) If $`y(W) \ne 1`$ or $`z(W) \ne 0`$, it is not.
- Let $`(\mathrm{hi}, \mathrm{lo}) = \mathrm{split}(W)`$ and $`G = \Omega\mathrm{pre}(\mathrm{hi})`$.
- (le2-3) If $`G = ()`$, $`G \ne \mathrm{hi}`$, $`\mathrm{lo} = ()`$, or some entry of $`\mathrm{lo}`$ is not $`1`$, it is not.
- (le2-4) If $`\mathrm{c1fixed}(G;\ t, \mathrm{true})`$ is false, it is not.
- (le2-5) Let $`q = |\mathrm{lo}|`$. If $`q \gt \mathrm{lev}(G_n)`$ for the last entry $`G_n`$ of $`G`$, it is not.
- (le2-6) Otherwise $`t`$ is $`\le_2`$-able, with $`A`$, $`W`$, $`U = (1, 0, G)`$ and $`q`$.

For a $`\le_2`$-able $`x`$ we write: $`A = \mathrm{ch}(x)`$; $`P`$ is $`A`$ without its last entry $`W`$; $`G = (G_1, \ldots, G_n) = \mathrm{ch}(U)`$; $`D = G_n`$ (the **last $`\omega`$ column**); $`\Lambda = L(D)`$; $`d_m = \mathrm{root}(A, U^m)`$ and $`\delta_m = \mathrm{ch}(d_m) = (A, U^m)`$ for $`m = 0, \ldots, q`$ (so $`d_0 = x`$, $`\delta_0 = A`$). $`K_m = \Lambda_m`$ is the level column of $`d_m`$.

**Successors.** $`\mathrm{succ}(t) = (d_1, \ldots, d_q)`$ if $`t`$ is $`\le_2`$-able, and $`()`$ otherwise.

**Dead nodes.** $`\mathrm{dead}(t)`$ says that $`t`$ is some $`d_m`$. Let $`A = \mathrm{ch}(t)`$.
- (dead-1) If $`A = ()`$, it is false.
- Let $`U`$ be the last entry of $`A`$ and $`m`$ the number of copies of $`U`$ at the end of $`A`$.
- (dead-2) If $`m \ge |A|`$, it is false.
- (dead-3) Otherwise it is true iff $`\mathrm{root}(A_1, \ldots, A_{|A|-m})`$ is $`\le_2`$-able with this $`U`$ and with $`m \le q`$.

**The successor with a level column.** $`\mathrm{d1}(t)`$ gives $`(x, K, m, q)`$ when $`t = d_m`$ and its level column $`K`$ has children. Let $`A = \mathrm{ch}(t)`$.
- (d1-1) If $`|A| \lt 2`$, or the last entry of $`A`$ has $`y \ne 1`$ or $`z \ne 0`$, the result is $`\mathrm{none}`$.
- Let $`U`$ be the last entry and $`m`$ the number of copies of $`U`$ at the end of $`A`$.
- (d1-2) If $`m \ge |A|`$, the result is $`\mathrm{none}`$.
- (d1-3) Let $`x = \mathrm{root}(A_1, \ldots, A_{|A|-m})`$. If $`x`$ is not $`\le_2`$-able, or its $`U`$ is not this $`U`$, or $`m \gt q`$, the result is $`\mathrm{none}`$.
- (d1-4) If $`m \gt |\Lambda|`$ or $`\Lambda_m = \bot`$, the result is $`\mathrm{none}`$.
- (d1-5) Let $`K = \Lambda_m`$. If $`\mathrm{ch}(K) = ()`$, the result is $`\mathrm{none}`$.
- (d1-6) Otherwise the result is $`(x, K, m, q)`$.

<a id="a4"></a>
### A.4 Witnesses (D10)

$`\mathrm{wit}(t)`$ takes a root term $`t`$ and gives a list of witnesses of the prefixes of $`G`$; it is called from Step 3. If $`t`$ is not $`\le_2`$-able, it is empty. Otherwise (with $`A`$, $`U`$, $`q`$, $`G`$ of A.3) let $`(a_1, b_1), \ldots, (a_s, b_s) = \mathrm{grp}(G)`$. For each $`e \in (b_1, \ldots, b_{s-1})`$ (the end of every group but the last), let $`\Pi = (G_1, \ldots, G_e)`$:
- (wit-1) If $`\mathrm{lim}(G_e)`$ and $`\mathrm{cont}(G_e)`$: no witness (its block replaces it).
- (wit-2) **The named case `lwpos`.** If $`\mathrm{lim}(G_e)`$ and $`1 \lt \mathrm{lev}(G_e) \le q`$: let $`j`$ be the largest $`\min(\mathrm{lev}(c) - 1,\ q - 1)`$ over the same-level children $`c`$ of $`G_e`$ ($`j = 0`$ if there are none). The witness is $`\mathrm{root}(A, U^j, (1, 0, (\Pi, \mathrm{lchain}(y(G_e), \mathrm{lev}(G_e)))))`$. Reason: cofinality; the witness is just below the highest successor that its content reads.
- (wit-3) Otherwise: if $`\mathrm{lim}(G_e)`$, let $`\Pi = (\Pi, (2, 1, ()))`$ (if not, $`\Pi`$ is kept).

  In both cases let $`w = \mathrm{root}(A, U^{q-1}, (1, 0, \Pi) + 1)`$.
  - (wit-3-1) If $`w`$ is $`\le_2`$-able, $`w`$ is a witness (it lies in the last interval between $`d_{q-1}`$ and $`d_q`$).

<a id="a5"></a>
### A.5 The order and the sum (`tss.py`)

$`\mathrm{cols}`$ and $`\mathrm{mat}`$ turn a term and a sum into a list of columns, which gives the order used in Steps 4 and 5 and in the branches; $`A + B`$ and $`\Sigma`$ add sums and are called from most operations.

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

**Writing a sum.** $`\mathrm{show}`$ writes a sum as its matrix $`\mathrm{mat}`$, one "(x,y,z)" per column.

<a id="a6"></a>
### A.6 The 2-row reach (D1)

$`\lambda(t)`$ takes a root term $`t`$ that is not epsilon and gives the part of its reach after $`t`$, a sum, as in the 2-row version; it is called from (lh-2), which also uses $`\mathrm{eps}`$.

**Epsilon terms.** $`\mathrm{eps}(t)`$ is true iff $`y(t) = 0`$, $`\mathrm{ch}(t) \ne ()`$ and the
last child of $`t`$ has $`y \ge 1`$.

**The 2-row reach increment.** For a root term $`t`$ with last child $`B_k`$, let
$`u = \mathrm{root}(\mathrm{ch}(B_k))`$.
- (lam-1) If $`\mathrm{eps}(u)`$, then $`\lambda(t) = (u)`$.
- (lam-2) Otherwise $`\lambda(t) = \log(u)`$.

**The 2-row log.** For a root term $`t`$, let $`H`$ be its children with $`y \ge 1`$ and
$`O_1, \ldots, O_r`$ its children with $`y = 0`$, each in order.
- (log-1) If $`H \ne ()`$, then $`\log(t) = \Sigma(\mathrm{root}(H), O_1, \ldots, O_r)`$.
- (log-2) Otherwise $`\log(t) = \Sigma(O_1, \ldots, O_r)`$.

<a id="a7"></a>
### A.7 Chains and cut columns (D6)

$`\mathrm{sub}(K)`$ and $`\mathrm{sub}^\top(K)`$ take a column $`K`$ and give the list of $`K`$ followed by the level columns above it; they are called from (lh-3-1), $`L`$ (A.8), $`\mathrm{cont}`$ (A.12), F (A.11) and LG (A.9), and $`\mathrm{cut}`$ and $`\mathrm{chtop}`$ below are called from the same places. $`\mathrm{up}`$, $`\mathrm{Rest}`$ and same-level children are in [Notation](ALGORITHM-2.md#notation).

**Chains.** $`\mathrm{sub}(K)`$ and $`\mathrm{sub}^\top(K)`$ list a column followed by the level columns above it. They differ only in (sub-2-2); all the recursive calls below are $`\mathrm{sub}`$, also inside $`\mathrm{sub}^\top`$. Let $`V = \mathrm{up}(K)`$.
- (sub-1) If $`V = ()`$, the result is $`(K)`$.
- (sub-2) Otherwise let $`H = \mathrm{sub}(V_1)`$, and let $`\gamma`$ be true iff the last entry of $`H`$ is cut. Start with $`(K, H)`$. For each $`S`$ in $`V_2, V_3, \ldots`$:
  - (sub-2-1) if $`S = V_1`$ or $`\gamma`$, add $`\mathrm{sub}(S)`$.

  Then:
  - (sub-2-2) Only for $`\mathrm{sub}`$ (not $`\mathrm{sub}^\top`$), and only if $`\gamma`$ is false: let $`E`$ be the list of the $`S`$ in $`V_2, V_3, \ldots`$ with $`S \ne V_1`$. If $`E \ne ()`$ and not ($`|E| = 1`$ and $`\mathrm{ch}(E_1) = ()`$), then for each $`E_i`$:
    - (sub-2-2-1) if $`i = 1`$ and $`\mathrm{ch}(E_1) = ()`$, skip it;
    - (sub-2-2-2) otherwise add $`\mathrm{sub}(E_i)`$.

**Cut.** $`\mathrm{cut}(K)`$ is the list of children that end the chain of $`K`$.
- (cut-1) If $`K`$ has a same-level child, then $`\mathrm{cut}(K) = ()`$.
- (cut-2) If $`K`$ has a child $`c`$ with $`z(c) = 0`$ and $`y(c) \gt y(K)`$ (an index column), then $`\mathrm{cut}(K) = ()`$.
- (cut-3) Otherwise $`\mathrm{cut}(K)`$ is the list of the $`c \in \mathrm{Rest}(K)`$ with ($`z(c) = 0`$ and $`y(c) \le y(K)`$) or $`y(c) \lt y(K)`$.

$`K`$ is **cut** iff $`\mathrm{cut}(K) \ne ()`$.

**Chain-continuing columns.** $`\mathrm{chtop}(K)`$ says that $`K`$ continues its chain and has other children (or one bare extra up-kid). Let $`V = \mathrm{up}(K)`$.
- (chtop-1) If $`|V| \ge 2`$ and the last entry of $`\mathrm{sub}(V_1)`$ is not cut: let $`E`$ be the $`c`$ in $`V_2, V_3, \ldots`$ with $`c \ne V_1`$.
  - (chtop-1-1) If $`|E| = 1`$ and $`\mathrm{ch}(E_1) = ()`$, it is true. If not, go on with (chtop-2).
- (chtop-2) Otherwise it is true iff $`\mathrm{Rest}(K) \ne ()`$ and $`V \ne ()`$.

<a id="a8"></a>
### A.8 The level columns $`L(D)`$ (D6)

$`L(D)`$ takes an $`\omega`$ column $`D`$ and gives the list of its level columns, one entry for each $`\le_2`$-successor $`d_m`$ (A.3), with $`\bot`$ for a level without a column; it is called as $`\Lambda = L(D)`$ in A.3, and from $`\mathrm{lev}`$ below, (L-2), $`\mathrm{Kimg}`$ (A.17), $`\mathrm{cov}`$ (A.12) and (C2-2-1). Let $`V = \mathrm{up}(D)`$.
- (L-1) If $`V = ()`$, then $`L(D) = (\bot)`$.
- (L-2) Otherwise let $`F = \mathrm{sub}(V_1)`$ (the first chain), let $`C`$ be $`\mathrm{sub}^\top(D)`$ without its first entry $`D`$, and let $`Q`$ be the list of the same-level children of $`D`$. The **lowest levels** come first:
  - (L-2-1) If $`Q \ne ()`$, some entry $`c`$ of $`C`$ has $`\mathrm{Rest}(c) \ne ()`$, and not ($`Q_1`$ has an up-kid and its first up-kid equals $`V_1`$): if $`\mathrm{up}(Q_1) = ()`$, let $`C = (\bot, C)`$ (L-2-1-1); otherwise let $`C = (L(Q_1), C)`$ (L-2-1-2).
  - (L-2-2) Else, if some entry $`c`$ of $`C`$ has some $`g \in \mathrm{Rest}(c)`$ with $`z(g) = 1`$, $`y(g) = y(D)`$ and not $`\mathrm{shares}(g, V_1)`$: let $`K'`$ be the first such $`g`$ (in the order of $`c`$, then of $`g`$), and let $`C = (L(K'), C)`$.
  - (L-2-3) Else, if $`\mathrm{kdl}(D, C) \ne \mathrm{none}`$ (below), let $`C = (L(\mathrm{kdl}(D, C)), C)`$.

  Then let $`C = \mathrm{ins}(C)`$ (below). Then insert the **own top levels**: build a new list; for $`i = 1, \ldots, |C|`$ add $`C_i`$, and add $`\bot`$ after it if $`C_i \ne \bot`$, $`i \lt |C|`$, $`C_{i+1} \ne \bot`$ and one of these holds:
  - (L-2-4-1) $`C_{i+1} = C_i`$ and $`C_i`$ has a same-level child;
  - (L-2-4-2) $`C_{i+1} = V_1`$, $`\mathrm{ch}(V_1) \ne ()`$ and $`C_i`$ is not cut;
  - (L-2-4-3) some $`k \le i`$ has $`C_k = C_{i+1}`$, $`\mathrm{ch}(C_k) \ne ()`$, $`C_i`$ not cut, and $`i - k + 1 = |\mathrm{sub}(C_k)|`$.

  Let $`C`$ be the new list. Then **the top**:
  - (L-2-5) If the last entry of $`F`$ is cut, then $`L(D) = C`$.
  - (L-2-6) Otherwise let $`C = (C, \bot)`$. Let $`E`$ be the list of the $`S`$ in $`V_2, V_3, \ldots`$ that are not (as places) entries of $`C`$. If $`E \ne ()`$ and not ($`|E| = 1`$ and $`\mathrm{ch}(E_1) = ()`$), then for each $`E_i`$:
    - (L-2-6-1) if $`i = 1`$ and $`\mathrm{ch}(E_1) = ()`$, skip it;
    - (L-2-6-2) otherwise let $`H = \mathrm{sub}(E_i)`$ with last entry $`T`$, and let $`C = (C, H)`$; if $`T`$ has a same-level child, or a child $`g`$ with $`z(g) = 0`$ and $`y(g) \gt y(T)`$, let $`C = (C, \bot)`$.

    Then $`L(D) = C`$.

$`\mathrm{kdl}(D, C)`$ is the first $`D`$-level $`\omega`$ column nested in a same-level child of a level column. For each entry $`c \ne \bot`$ of $`C`$ in order, and each same-level child $`g`$ of $`c`$ in $`\mathrm{Rest}(c)`$ in order, search breadth first: start a queue with $`g`$; while it is not empty, take $`h`$ from its front, and for each child $`k`$ of $`h`$ in order:
- (kdl-1) if $`z(k) = 1`$ and $`y(k) = y(D)`$, the result is $`k`$;
- (kdl-2) if $`z(k) = 1`$ and $`y(k) = y(c)`$, put $`k`$ at the back of the queue.
- (kdl-3) If the search ends without a result, $`\mathrm{kdl}(D, C) = \mathrm{none}`$.

$`\mathrm{ins}(C)`$ inserts the levels of a column found inside a level column on the level of the previous level column. Start with an empty list $`O`$. For each entry $`c`$ of $`C`$ in order:
- (ins-1) if $`c \ne \bot`$ and $`O`$ has an entry $`\ne \bot`$: let $`p`$ be the last such entry, and let $`g`$ be the first $`h \in \mathrm{Rest}(c)`$ with $`z(h) = 1`$ and $`y(h) = y(p) \lt y(c)`$.
  - (ins-1-1) If $`g`$ exists and $`g \ne p`$, let $`O = (O, L(g))`$.

Then add $`c`$ to $`O`$. The result is $`O`$.

**The number of levels.** $`\mathrm{lev}(D) = 1`$ if $`\mathrm{up}(D) = ()`$ (lev-1), and $`\mathrm{lev}(D) = |L(D)|`$ otherwise (lev-2).

$`\mathrm{shares}(g, K_1)`$ is true iff $`\mathrm{up}(g) \ne ()`$ and the first up-kid of $`g`$ equals $`K_1`$.

The algorithm continues in [ALGORITHM-2.md](ALGORITHM-2.md) (A.9–A.18, the notation, the names in the code).
