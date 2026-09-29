[← Back](README.md) | [English](ALGORITHM-2.md) | [Japanese](ALGORITHM-2-ja.md)

# Converting trio sequences to patterns of resemblance: algorithm, part 2

This is the second part of the algorithm of `phi3def2.py`. The first part (usage, conventions, A.1–A.8)
is in [README.md](README.md).

### A.9 Summands of $`U`$: limits, covers, groups, blocks (D5)

Here $`G`$, $`G'`$ are $`\omega`$ columns (summands of a $`U`$-form, A.13).

**Limit summands.** $`\mathrm{lim}(G)`$ says that the rightmost leaf of $`G`$ is a marker of $`G`$. Let $`\pi_0 = G, \pi_1, \ldots, \pi_r`$ be the rightmost path ($`\pi_{i+1}`$ is the last child of $`\pi_i`$, and $`\pi_r`$ has no children), and $`f = \pi_r`$.
- (lim-1) If $`r = 0`$, $`z(f) \ne 0`$ or $`y(f) \lt 1`$, then $`\mathrm{lim}(G)`$ is false.
- (lim-2) Otherwise, for $`i = r - 1, r - 2, \ldots, 0`$: if $`z(\pi_i) = 1`$ and $`y(\pi_i) \le y(f)`$, then:
  - (lim-2-1) if $`i \ne 0`$ and $`y(\pi_i) = y(G) = y(f)`$, go on with the next $`i`$ (an $`\omega`$ child on $`G`$'s level is passed through);
  - (lim-2-2) otherwise $`\mathrm{lim}(G)`$ is true iff $`i = 0`$ and $`y(G) = y(f)`$.
- (lim-3) If the loop ends without a result, $`\mathrm{lim}(G)`$ is false.

**Levels only.** $`\mathrm{lvonly}(G)`$ is true iff every child $`c`$ of $`G`$ is an up-kid of $`G`$ with $`\mathrm{lvonly}(c)`$ (true if $`G`$ has no children).

**Strip.** $`\mathrm{strip}(G)`$ removes the rightmost leaf:
- (strip-1) If $`\mathrm{ch}(G) = ()`$, the result is $`\mathrm{none}`$.
- (strip-2) Otherwise let $`s'`$ be $`\mathrm{strip}`$ of the last child $`B_k`$. The result is $`(y(G), z(G), (B_1, \ldots, B_{k-1}))`$, with $`s'`$ added at the end if $`s' \ne \mathrm{none}`$.

**Ends in a marker.** $`\mathrm{em}(K, \ell)`$ is true iff the rightmost leaf $`f`$ of $`K`$ (reached through last children; $`f = K`$ if $`K`$ has no children) has $`z(f) = 0`$ and $`y(f) = \ell`$.

**Covers.** $`\mathrm{cov}(G, G')`$ says that the summand $`G'`$ after the limit summand $`G`$ repeats $`G`$ (or a prefix of its children with $`G`$'s levels covered).
- (cov-1) If $`\mathrm{cont}(G)`$ (below) and $`\mathrm{ch}(G) \ne ()`$: let $`C = \mathrm{ch}(G')`$.
  - (cov-1-1) If $`C \ne ()`$, its last entry is $`1`$, $`|C| \ge 2`$ and $`\mathrm{em}(C_{|C|-1}, y(G'))`$, remove the last entry of $`C`$.
  - (cov-1-2) If $`C \ne ()`$, $`|C| \lt |\mathrm{ch}(G)|`$, $`C`$ is a prefix of $`\mathrm{ch}(G)`$, and $`|L(G)| \le |L((y(G'), z(G'), C))|`$ (A.11), then $`\mathrm{cov}(G, G')`$ is true.

  If it is not true here, go on with (cov-2).
- (cov-2) If $`\mathrm{cont}(G)`$ is false, or $`\mathrm{ch}(G) = ()`$, or the last child of $`G`$ is not $`(y(G), 0, ())`$, then it is false.
- (cov-3) Let $`s = \mathrm{strip}(G)`$. If $`s = \mathrm{none}`$ or $`\mathrm{ch}(s) = ()`$, it is false.
- (cov-4) If $`G' = s`$, it is true.
- (cov-5) Otherwise it is true iff $`\mathrm{ch}(G') \ne ()`$, the last child of $`G'`$ is $`1`$, $`|\mathrm{ch}(G')| \ge 2`$, $`\mathrm{em}`$ holds for the child before it and $`y(G')`$, and $`G'`$ without its last child equals $`s`$.

**Groups.** $`\mathrm{grp}(G_1, \ldots, G_n)`$ is a list of pairs $`(i, j)`$. Start with $`i = 1`$. While $`i \le n`$: let $`j = i`$;
- (grp-1) if $`\mathrm{lim}(G_j)`$, $`j \lt n`$ and $`\mathrm{ch}(G_{j+1}) = ()`$, let $`j = j + 1`$;
- (grp-2) else if $`\mathrm{lim}(G_j)`$, $`j \lt n`$ and $`\mathrm{lvonly}(G_{j+1})`$, let $`j = j + 1`$;
- (grp-3) else if $`\mathrm{lim}(G_j)`$, $`j \lt n`$ and $`\mathrm{cov}(G_j, G_{j+1})`$, let $`j = j + 1`$;

then add $`(i, j)`$ to the list and let $`i = j + 1`$. The **last group** is the last pair $`(a, b)`$; $`b = n`$.

**Content.** $`\mathrm{cont}(G)`$ says that some level column of $`G`$ has children other than its chain.
- (cont-1) If $`\mathrm{up}(G) = ()`$, it is false.
- (cont-2) Otherwise it is true iff some entry $`C`$ of $`\mathrm{sub}^\top(G)`$ other than the first (A.10) has $`\mathrm{Rest}(C) \ne ()`$.

**The marker replaced.** $`\mathrm{limx}(G, x)`$ replaces the rightmost leaf of $`G`$ by the root term $`x`$:
- (limx-1) If $`\mathrm{ch}(G) = ()`$, the result is $`\mathrm{root}(\mathrm{ch}(x)) = x`$.
- (limx-2) Otherwise the result is $`(y(G), z(G), (B_1, \ldots, B_{k-1}, \mathrm{limx}(B_k, x)))`$.

**The levels-only chain.** $`\mathrm{lchain}(y, k) = (y, 1, (\mathrm{lchain}(y + 1, k - 1)))`$ if $`k \gt 1`$, and $`(y, 1, ())`$ if $`k \le 1`$.

**Blocks.** $`\mathrm{blk}(U)`$ says that an earlier limit summand has a block: for $`G = \mathrm{ch}(U)`$ with last group $`(a, b)`$, it is true iff some $`G_i`$ with $`i \lt a`$ has $`\mathrm{lim}(G_i)`$ and $`\mathrm{cont}(G_i)`$.

### A.10 Cut columns and chains (D6)

**Cut.** $`\mathrm{cut}(K)`$ is the list of children that end the chain of $`K`$.
- (cut-1) If $`K`$ has a same-level child, then $`\mathrm{cut}(K) = ()`$.
- (cut-2) If $`K`$ has a child $`c`$ with $`z(c) = 0`$ and $`y(c) \gt y(K)`$ (an index column), then $`\mathrm{cut}(K) = ()`$.
- (cut-3) Otherwise $`\mathrm{cut}(K)`$ is the list of the $`c \in \mathrm{Rest}(K)`$ with ($`z(c) = 0`$ and $`y(c) \le y(K)`$) or $`y(c) \lt y(K)`$.

$`K`$ is **cut** iff $`\mathrm{cut}(K) \ne ()`$.

**Chains.** $`\mathrm{sub}(K)`$ and $`\mathrm{sub}^\top(K)`$ list a column followed by the level columns above it. They differ only in (sub-2-2); all the recursive calls below are $`\mathrm{sub}`$, also inside $`\mathrm{sub}^\top`$. Let $`V = \mathrm{up}(K)`$.
- (sub-1) If $`V = ()`$, the result is $`(K)`$.
- (sub-2) Otherwise let $`H = \mathrm{sub}(V_1)`$, and let $`\gamma`$ be true iff the last entry of $`H`$ is cut. Start with $`(K, H)`$. For each $`S`$ in $`V_2, V_3, \ldots`$:
  - (sub-2-1) if $`S = V_1`$ or $`\gamma`$, add $`\mathrm{sub}(S)`$.

  Then:
  - (sub-2-2) Only for $`\mathrm{sub}`$ (not $`\mathrm{sub}^\top`$), and only if $`\gamma`$ is false: let $`E`$ be the list of the $`S`$ in $`V_2, V_3, \ldots`$ with $`S \ne V_1`$. If $`E \ne ()`$ and not ($`|E| = 1`$ and $`\mathrm{ch}(E_1) = ()`$), then for each $`E_i`$:
    - (sub-2-2-1) if $`i = 1`$ and $`\mathrm{ch}(E_1) = ()`$, skip it;
    - (sub-2-2-2) otherwise add $`\mathrm{sub}(E_i)`$.

### A.11 The level columns $`L(D)`$ (D6)

$`L(D)`$ is the list of the level columns of an $`\omega`$ column $`D`$: one entry for each $`\le_2`$-successor $`d_m`$ (A.13), with $`\bot`$ for a level without a column. Let $`V = \mathrm{up}(D)`$.
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

**Chain-continuing columns.** $`\mathrm{chtop}(K)`$ says that $`K`$ continues its chain and has other children (or one bare extra up-kid). Let $`V = \mathrm{up}(K)`$.
- (chtop-1) If $`|V| \ge 2`$ and the last entry of $`\mathrm{sub}(V_1)`$ is not cut: let $`E`$ be the $`c`$ in $`V_2, V_3, \ldots`$ with $`c \ne V_1`$.
  - (chtop-1-1) If $`|E| = 1`$ and $`\mathrm{ch}(E_1) = ()`$, it is true. If not, go on with (chtop-2).
- (chtop-2) Otherwise it is true iff $`\mathrm{Rest}(K) \ne ()`$ and $`V \ne ()`$.

### A.12 Recorded terms

Some branches **record** a term $`e`$ **under** a key $`k`$ (a root term). $`\mathrm{Img}(k)`$ is the set of the terms recorded under $`k`$. They become nodes when $`k`$ is a node (A.20). The key matters: a term recorded under $`k`$ is added only through the node $`(k)`$.

### A.13 $`\le_2`$-able nodes and successors (D7)

$`\mathrm{le2}(t)`$ decides whether the root term $`t`$ is **$`\le_2`$-able**, $`t = \mathrm{root}(P, U + q)`$.
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

### A.14 The read of a level column's children (D8)

$`\mathrm{LK}(x, K, m)`$ reads the children of the level column $`K = K_m`$ of a $`\le_2`$-able $`x`$ (with its $`U`$, $`q`$, $`D`$, $`\Lambda`$). It gives a list of columns. All reads in LK use the empty context $`\rho_\varnothing`$.

Let $`R = \mathrm{Rest}(K)`$. The **owner map** $`w`$: $`w(y(D)) = 0`$; then for $`i = 1, \ldots, m - 1`$, if $`\Lambda_i \ne \bot`$ and $`y(\Lambda_i) \lt y(K)`$, set $`w(y(\Lambda_i)) = i`$ (a later $`i`$ replaces an earlier one). Replace each $`c \in R`$ by $`\mathrm{OL}(c)`$, and then by $`\mathrm{OD}(c)`$ (below). Then for each $`c`$ in $`R`$, in order:
- (LK-1) If $`z(c) = 1`$ and $`y(c) = y(D)`$: let $`j_0`$ be true iff $`c`$ is not the first child of $`K`$ (it has an elder sibling). Let $`e = \mathrm{Kimg}(c;\ x, y(D), (\delta_1, \ldots, \delta_q), \mathrm{none}, \mathrm{false}, m - 2, j_0;\ \rho_\varnothing)`$. Record $`e`$ under $`x`$, and replace $`c`$ by $`(0, 0, \mathrm{ch}(e))`$.
- (LK-2) Otherwise keep $`c`$.

Then for each $`c`$ in $`R`$, in order:
- (LK-3) If $`z(c) = 1`$, $`m \ge 2`$ and $`y(c) \lt y(K)`$: let $`p`$ be the largest $`i \le m - 1`$ with $`\Lambda_i \ne \bot`$ and $`y(\Lambda_i) = y(c)`$.
  - (LK-3-1) If $`p`$ exists, let $`\Delta' = (\delta_{p+1}, \ldots, \delta_{m-1})`$.
    - (LK-3-1-1) If $`\Delta' \ne ()`$, let $`e = \mathrm{Kimg}(c;\ x, y(c), \Delta', \mathrm{none}, \mathrm{false};\ \rho_\varnothing)`$, record $`e`$ under $`x`$, and replace $`c`$ by $`(0, 0, \mathrm{ch}(e))`$.

The result is $`R`$.

$`\mathrm{OL}(c)`$ reads a marker owned by $`D`$ or by an earlier level column:
- (OL-1) If $`z(c) = 0`$, $`y(c) \ge 1`$ and $`j = w(y(c))`$ is defined:
  - (OL-1-1) if $`\mathrm{ch}(c) = ()`$, the result is $`(0, 0, \delta_j)`$;
  - (OL-1-2) otherwise let $`e = \mathrm{root}(\delta_j + \mathrm{C2s}_{d_j}(\mathrm{ch}(c);\ y(c), (), \mathrm{true};\ \rho_\varnothing))`$ (the frame on $`d_j`$), record $`e`$ under $`x`$; the result is $`(0, 0, \mathrm{ch}(e))`$.
- (OL-2) Otherwise the result is $`c`$.

$`\mathrm{OD}(c)`$ does the same for bare markers nested in a same-level child of $`K`$:
- (OD-1) If not ($`z(c) = 1`$ and $`y(c) = y(K)`$), the result is $`c`$.
- (OD-2) Otherwise the result is $`\mathrm{rec}(c)`$, where $`\mathrm{rec}(t)`$ is $`t`$ with each child $`g`$ replaced as follows:
  - (OD-2-1) if $`z(g) = 0`$, $`\mathrm{ch}(g) = ()`$, $`w(y(g))`$ is defined and $`y(g) \lt y(K)`$: by $`(0, 0, \delta_{w(y(g))})`$;
  - (OD-2-2) else if $`z(g) = 1`$ and $`y(g) = y(K)`$: by $`\mathrm{rec}(g)`$;
  - (OD-2-3) else $`g`$ is kept.

### A.15 The fold of a column's children (D8)

$`\mathrm{F}(S;\ x, G, \ell, b, \Delta, t_0, \mathrm{lastG};\ \rho)`$ folds the reads of the children of a column $`G`$ into the sum $`S`$. $`x`$ is the root term that the read belongs to, $`\ell`$ a level, $`b`$ the frame base (a children list), $`\Delta = (\Delta_1, \ldots, \Delta_n)`$ a level list, $`t_0`$ a term or $`\mathrm{none}`$. It keeps a list $`I`$ of index images, empty at the start. Let $`V`$ be the children of $`G`$ with $`z = 1`$ and $`y = \ell + 1`$, and $`H = \mathrm{sub}(V_1)`$ if $`V \ne ()`$ ($`H = ()`$ otherwise). If $`H \ne ()`$ and the last entry of $`H`$ is not cut, let $`E`$ be the $`c`$ in $`V_2, V_3, \ldots`$ that are not (as places) entries of $`H`$ and have $`c \ne V_1`$; otherwise $`E = ()`$. Let $`\beta`$ be true iff $`|E| = 1`$ and $`\mathrm{ch}(E_1) = ()`$ (**one bare extra up-kid**). For each child $`c`$ of $`G`$ in order, with $`\mathrm{lst}`$ = ($`\mathrm{lastG}`$ and $`c`$ is the last child):
- (F-1) If $`\beta`$, $`c`$ is $`E_1`$, $`n \ge 1`$ and $`\mathrm{ch}(x) \ne \Delta_1`$ (the doubling): if $`\mathrm{ch}(c) = ()`$, let $`S = S \oplus \mathrm{root}(\Delta_n)`$; otherwise let $`S = S \oplus \mathrm{root}(\Delta_n + \mathrm{KI}(\mathrm{ch}(c);\ x, \ell, \Delta, \mathrm{none}, \mathrm{lst};\ \rho))`$ (this second case does not occur, since $`\beta`$ makes $`c`$ childless). Go to the next child.
- (F-2) If $`c = 1`$, $`c`$ is not the first child, and the child $`c'`$ before it has $`z(c') = 1`$, $`y(c') = \ell + 1`$ and $`\mathrm{em}(c', \ell)`$: skip $`c`$ (a unit after a limit level column is absorbed).
- (F-3) If $`z(c) = 1`$:
  - (F-3-1) if $`y(c) = \ell`$, let $`S = S \oplus \mathrm{Kimg}(c;\ x, \ell, \Delta, t_0, \mathrm{lst};\ \rho)`$;
  - (F-3-2) otherwise do nothing (it is a level).
- (F-4) If $`y(c) \gt \ell`$ (an index column): add the first term of $`\mathrm{KI}((c);\ x, \ell, \Delta, \mathrm{none}, \mathrm{lst};\ \rho)`$ to $`I`$. Let $`e = \mathrm{root}(b + \Sigma(I))`$ (the frame), record $`e`$ under $`x`$.
  - (F-4-1) If $`e`$ is $`\le_2`$-able, let $`W'`$ be its last child, and record under $`x`$ also $`\mathrm{root}(\mathrm{ch}(e) \text{ without } W',\ W'')`$, where $`W''`$ is $`W'`$ without its unit children (the nesting base).

  Then let $`S = S \oplus e`$.
- (F-5) Otherwise:
  - (F-5-1) if $`y(c) \ge 1`$, let $`S = S \oplus \mathrm{C2}_x(c;\ \ell, (), \mathrm{lst};\ \rho)`$;
  - (F-5-2) otherwise let $`S = S \oplus \mathrm{root}(\mathrm{ch}(c))`$.

The result is $`S`$.

### A.16 The fold $`\oplus`$ (D9)

$`S \oplus Y`$ takes a nonempty sum $`S`$ with first term $`S_1`$ and a term $`Y`$:
- (fold-1) If $`Y \le S_1`$, the result is $`S + (Y)`$.
- (fold-2) If $`Y \gt S_1`$ and $`Y`$ is $`\le_2`$-able, the result is $`\mathrm{lh}(Y) + (Y)`$.
- (fold-3) Otherwise the result is $`\mathrm{lh}(Y)`$.

$`S \succ S'`$ compares two sums term by term: at the first position where the terms differ, the larger term wins; if one sum is a prefix of the other, the longer one is larger.

### A.17 The reach $`\mathrm{lh}`$ (D9)

$`\mathrm{lh}(t)`$ is the $`\le_1`$-reach of a root term $`t`$, a sum. It starts with the empty context.
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
- (lh-6) If $`t`$ is $`\le_2`$-able, then $`\mathrm{lh}(t) = \mathrm{lh}_1(t)`$ (A.18).
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

### A.18 The reach of a $`\le_2`$-able node (D9)

$`\mathrm{lh}_1(x)`$ for a $`\le_2`$-able $`x`$ (with $`A`$, $`P`$, $`W`$, $`U`$, $`q`$, $`G`$, $`D`$, $`\Lambda`$, $`d_m`$, $`\delta_m`$ of A.13). Let $`r = \mathrm{lev}(D)`$ and $`S = (d_q)`$.
- (lh1-1) If $`q \lt r`$ (a nesting), then $`\mathrm{lh}_1(x) = \mathrm{lh}(\mathrm{root}(P, W + 1))`$.
- Let $`(a, b)`$ be the last group of $`G`$, and let the frame base be $`b_0 = \delta_q`$.
- (lh1-2) If $`q \ge 2`$, $`n = 1`$, $`|\Lambda| \ge q`$, $`\Lambda_q = \bot`$, $`\Lambda_{q-1} \ne \bot`$, $`\Lambda_{q-1}`$ has a same-level child, and every up-kid of $`D`$ is (as a place) an entry of $`\Lambda`$: let $`b_0 = \delta_{q-1}`$ (level $`q`$ is an own top level).
- (lh1-3) If $`\mathrm{d1}(d_q) \ne \mathrm{none}`$, let $`S = \mathrm{lh}(d_q)`$.
- For $`m = 1, \ldots, q - 1`$ (the largest reach of a $`d_m`$ with its own read):
  - (lh1-4) if $`\mathrm{d1}(d_m) = (x, K, m, q)`$, $`m \lt q`$ and $`\mathrm{chtop}(K)`$, skip this $`m`$;
  - (lh1-5) if $`\mathrm{d1}(d_m) \ne \mathrm{none}`$ otherwise, let $`L = \mathrm{lh}(d_m)`$;
    - (lh1-5-1) if $`L \succ S`$, let $`S = L`$.
- Let $`\Delta = (\delta_1, \ldots, \delta_q)`$, and $`t_0 = \mathrm{root}(P)`$ if $`|A| \ge 2`$, $`t_0 = \mathrm{none}`$ otherwise. Then $`\mathrm{lh}_1(x) = \mathrm{LG}(S)`$:

$`\mathrm{LG}(S)`$ folds into $`S`$ the reads of the last group, the top reads and the blocks:
- (LG-1) For $`i = a, \ldots, b`$, with $`\ell = y(G_i)`$:
  - (LG-1-1) if $`i \lt b`$, $`\mathrm{lim}(G_i)`$, ($`\mathrm{lev}(G_i) \gt \mathrm{lev}(G_b)`$ or $`\mathrm{cont}(G_i)`$), and not $`\mathrm{cov}(G_i, G_b)`$: let $`e = \mathrm{root}(\delta_q + ((1, 0, (\mathrm{limx}(G_i, x)))))`$ (the block of $`G_i`$), record $`e`$ under $`x`$, and let $`S = S \oplus e`$;
  - (LG-1-2) otherwise let $`S = \mathrm{F}(S;\ x, G_i, \ell, b_0, \Delta, t_0, i = n;\ ((x, \ell, \Delta), \mathrm{none}, \mathrm{none}))`$.
- (LG-2) For $`m = 1, \ldots, |\Lambda|`$ (the top reads):
  - (LG-2-1) if $`\Lambda_m = \bot`$, or $`m \ge q`$, or not $`\mathrm{chtop}(\Lambda_m)`$, skip this $`m`$;
  - (LG-2-2) otherwise let $`K = \Lambda_m`$, $`R = \mathrm{LK}(x, K, m)`$, $`\Delta' = (\delta_{m+1}, \ldots, \delta_q)`$, $`\kappa = \Lambda_{m+1}`$ if $`m \lt |\Lambda|`$ and $`\Lambda_{m+1} \ne \bot`$ ($`\kappa = \mathrm{none}`$ otherwise), and let $`S = \mathrm{F}(S;\ d_m, (y(K), z(K), R), y(K), \delta_q, \Delta', \mathrm{none}, \mathrm{true};\ \rho)`$ with $`\rho = ((d_m, y(K), \Delta'),\ (x, y(D)),\ (d_m, \kappa))`$.
- (LG-3) For each entry $`K \ne \bot`$ of $`\Lambda`$, with $`V = \mathrm{up}(K)`$:
  - (LG-3-1) if $`|V| \ge 2`$ and the last entry of $`\mathrm{sub}(V_1)`$ is not cut: let $`E`$ be the $`c`$ in $`V_2, V_3, \ldots`$ with $`c \ne V_1`$;
    - (LG-3-1-1) if $`|E| = 1`$ and $`\mathrm{ch}(E_1) = ()`$, let $`S = S \oplus d_q`$ (the doubling).

  Record $`\mathrm{pre}(x) = S`$ (used by lh-3-2).
- (LG-4) **The named case `lnest`.** If $`a \ge 3`$, $`\mathrm{lim}(G_{a-1})`$ and $`\mathrm{cont}(G_{a-1})`$: let $`e = \mathrm{root}(\delta_q + ((1, 0, (G_1, \ldots, G_{a-2}, \mathrm{limx}(G_{a-1}, x)))))`$, record $`e`$ under $`x`$, and let $`S = S \oplus e`$. Reason: the earlier summands are one $`U`$-form, and their levels are those of the last of them.
- (LG-5) Otherwise, for $`i = 1, \ldots, a - 1`$:
  - (LG-5-1) if $`\mathrm{lim}(G_i)`$ and $`\mathrm{cont}(G_i)`$, let $`e = \mathrm{root}(\delta_q + ((1, 0, (\mathrm{limx}(G_i, x)))))`$, record $`e`$ under $`x`$, and let $`S = S \oplus e`$.

The result is $`S`$.

### A.19 Witnesses (D10)

$`\mathrm{wit}(t)`$ is a list of witnesses of the prefixes of $`G`$. If $`t`$ is not $`\le_2`$-able, it is empty. Otherwise (with $`A`$, $`U`$, $`q`$, $`G`$ of A.13) let $`(a_1, b_1), \ldots, (a_s, b_s) = \mathrm{grp}(G)`$. For each $`e \in (b_1, \ldots, b_{s-1})`$ (the end of every group but the last), let $`\Pi = (G_1, \ldots, G_e)`$:
- (wit-1) If $`\mathrm{lim}(G_e)`$ and $`\mathrm{cont}(G_e)`$: no witness (its block replaces it).
- (wit-2) **The named case `lwpos`.** If $`\mathrm{lim}(G_e)`$ and $`1 \lt \mathrm{lev}(G_e) \le q`$: let $`j`$ be the largest $`\min(\mathrm{lev}(c) - 1,\ q - 1)`$ over the same-level children $`c`$ of $`G_e`$ ($`j = 0`$ if there are none). The witness is $`\mathrm{root}(A, U^j, (1, 0, (\Pi, \mathrm{lchain}(y(G_e), \mathrm{lev}(G_e)))))`$. Reason: cofinality; the witness is just below the highest successor that its content reads.
- (wit-3) Otherwise: if $`\mathrm{lim}(G_e)`$, let $`\Pi = (\Pi, (2, 1, ()))`$ (if not, $`\Pi`$ is kept).

  In both cases let $`w = \mathrm{root}(A, U^{q-1}, (1, 0, \Pi) + 1)`$.
  - (wit-3-1) If $`w`$ is $`\le_2`$-able, $`w`$ is a witness (it lies in the last interval between $`d_{q-1}`$ and $`d_q`$).

### A.20 The pattern (D11)

**The closure.** $`\mathrm{cl}(X)`$ is the least set $`V`$ of sums with $`(), (1) \in V`$ and $`X \subseteq V`$, closed under these operations:
- $`(t_1, \ldots, t_n) \in V`$ gives every prefix $`(t_1, \ldots, t_j)`$ and every $`(t_i)`$;
- $`(t) \in V`$ gives $`(\mathrm{anchor}(t))`$ (if it is not $`\mathrm{none}`$), $`\mathrm{lh}(t)`$, $`(e)`$ for every $`e \in \mathrm{Img}(t)`$, $`(d)`$ for every $`d \in \mathrm{succ}(t)`$, and $`(w)`$ for every $`w \in \mathrm{wit}(t)`$.

$`\mathrm{Img}(t)`$ holds the terms recorded under $`t`$ during the computations of $`\mathrm{lh}(u)`$ for the one-term nodes $`(u) \in V`$, with every computation nested in them. (The program adds these nodes by a work list; it is a least fixed point, and the order does not change it.)
- (cl-1) If $`V`$ gets more than 300 nodes, the program stops with the error "too many nodes".

**The Def 9.4 copies** (Carlson 2009, Def 9.4). $`\mathrm{copy}(x)`$ for a $`\le_2`$-able $`x`$ is the first $`e = \mathrm{root}(P, U^m)`$, $`m = 1, \ldots, 7`$, with $`\mathrm{dead}(e)`$ false; it is $`\mathrm{none}`$ if there is none.

**The pattern** $`\Phi_3(M)`$. Let $`\hat{M} = \mathrm{tree}(M)`$ and $`V = \mathrm{cl}(\{\hat{M}\})`$. Repeat at most 4 times: let $`J`$ be the one-term nodes of $`V`$ in increasing order, and $`X = \emptyset`$. For each $`(x) \in J`$ that is $`\le_2`$-able, in order:
- (copy-1) if $`\mathrm{lh}(x) = (d_q)`$, skip it;
- (copy-2) if some $`(u) \in J`$ with $`u \lt x`$ has $`\mathrm{lh}(u) = \mathrm{lh}(x)`$, skip it;
- (copy-3) otherwise, if $`e = \mathrm{copy}(x) \ne \mathrm{none}`$ and $`(e) \notin V`$, add $`(e)`$ to $`X`$.

Then:
- (copy-4) if $`X = \emptyset`$, stop repeating;
- (copy-5) otherwise let $`V = \mathrm{cl}(V \cup X)`$.

Then:
- The nodes are $`V`$, sorted by $`\mathrm{mat}`$: $`v_0 = () \lt v_1 = (1) \lt \cdots`$.
- The **reach** of $`v_i`$: if $`v_i = (t)`$ has one term, it is the largest $`r \ge i`$ with $`\mathrm{mat}(v_r) \le \mathrm{mat}(\mathrm{lh}(t))`$; otherwise, or if there is no such $`r`$, it is $`i`$. So $`v_i \le_1 v_j`$ iff $`i = j`$, or $`v_i`$ has one term and $`i \le j \le \mathrm{reach}(i)`$.
- The **$`\le_2`$ pairs** are $`(i, j)`$ with $`v_i = (t)`$ and $`v_j = (d)`$ for $`d \in \mathrm{succ}(t)`$.
- The **point** is the index of $`\hat{M}`$.
- Addition is the relation $`v_i + v_j = v_k`$ of A.2, as in the 2-row version; the program does not print it.

**Output.** One line: the elements $`v_0 \lt v_1 \lt \cdots`$ from left to right, written `0` for $`v_0 = 0`$, `a` for the term $`(0,0,0)`$, `n0`, `n1`, … for the other one-term elements in increasing order, and `x+y+…` for a sum of such names; `*` before the point; `(` before $`v_i`$ and `)` after its reach $`v_{r}`$ when $`r \gt i`$; `[` before $`v_i`$ and `]` after $`v_j`$ for each $`\le_2`$ pair $`(i, j)`$. At one element, the brackets of the longer span open first, and the bracket opened last closes first. With `--table`, one line per element instead: `*` if $`i`$ is the point, $`i`$, $`\mathrm{show}(v_i)`$, `reach` and the reach of $`v_i`$, and `<=2` with the $`j`$ of its $`\le_2`$ pairs.

### A.21 Names in the code

| text | `phi3def2.py` | text | `phi3def2.py` |
|---|---|---|---|
| $`\mathrm{eps}`$, $`\log`$, $`\lambda`$ | `is_eps`, `log0`, `lam` | $`\mathrm{own}`$ | `_nearest` |
| $`\mathrm{split}`$, $`\Omega\mathrm{pre}`$, $`W + k`$ | `split`, `omega_prefix`, `plus` | $`\mathrm{C1}`$, $`\mathrm{C1s}`$, $`\mathrm{c1fixed}`$ | `C1`, `C1s`, `c1fixed` |
| $`\mathrm{C2}`$, $`\mathrm{C2s}`$ | `C2`, `C2s` | $`\rho_C`$, $`\rho_D`$, $`\rho_1`$ | `KCTX`, `KDX`, `K1REF` |
| $`\mathrm{KI}`$, $`\mathrm{Kimg}`$ | `KI`, `Kimg` | $`K_1(x)`$, $`\mathrm{shares}`$ | `k1_of`, `shares_k1` |
| $`\mathrm{Up}`$ | `Up` | $`\mathrm{lim}`$, $`\mathrm{lvonly}`$, $`\mathrm{strip}`$ | `is_limit`, `levels_only`, `strip_marker` |
| $`\mathrm{cov}`$, $`\mathrm{grp}`$, $`\mathrm{cont}`$ | `covers`, `groups`, `has_content` | $`\mathrm{limx}`$, $`\mathrm{lchain}`$, $`\mathrm{blk}`$ | `limx`, `lchain`, `has_block` |
| $`\mathrm{Rest}`$, $`\mathrm{cut}`$ | `k2kids(K, 'all')`, `k2kids(K, 'cut')` | $`\mathrm{sub}`$, $`\mathrm{sub}^\top`$ | `subcols(K)`, `subcols(K, top=True)` |
| $`L`$, $`\mathrm{kdl}`$, $`\mathrm{ins}`$ | `level_cols`, `kdl_nested`, `kdl2_insert` | $`\mathrm{lev}`$, $`\mathrm{lev} - 1`$, $`\mathrm{chtop}`$ | `zsib` (= `zdepth`), `zlead`, `chtop_col` |
| $`\mathrm{le2}`$, $`\mathrm{succ}`$, $`\mathrm{dead}`$, $`\mathrm{d1}`$ | `le2_info`, `le2_succ`, `is_dead`, `d1_info` | $`\mathrm{Img}`$, $`\mathrm{pre}`$ | `IDXIMG`, `PREBLOCK` |
| $`\mathrm{LK}`$, $`\mathrm{OL}`$, $`\mathrm{OD}`$, $`\mathrm{em}`$ | `level_kids`, `ownleaf`, `owndeep`, `ends_in_marker` | $`\mathrm{F}`$ | `_lh1_kids` |
| $`\oplus`$, $`\succ`$ | `oplus`, `scmp` | $`\mathrm{lh}`$, $`\mathrm{lh}_1`$, $`\mathrm{LG}`$ | `lh`, `lh1_le2`, `_lh1_groups` |
| $`\mathrm{wit}`$, $`\mathrm{cl}`$, $`\mathrm{copy}`$ | `le2_wit`, `closure`, `d94_copy` | $`\Phi_3`$, output | `build`, `pattern`, `show` |
| $`\mathrm{parse}`$, $`\mathrm{tree}`$ | `tss.parse`, `tss.from_mat` | $`\mathrm{cols}`$, $`\mathrm{mat}`$, $`+`$, $`\Sigma`$ | `tss.cols_term`, `tss.mat`, `tss.add`, `tss.addall` |

**Notes on the code.** The read context is kept in global stacks (`KCTX`, `KDX`, `K1REF`) that a nested call of `lh` does not clear. On all 3290 test matrices, clearing them at every call of `lh` gives the same patterns, so the text states the cleared form (A.5). The parameter `top` of `C2` and `C2s` has no effect.
