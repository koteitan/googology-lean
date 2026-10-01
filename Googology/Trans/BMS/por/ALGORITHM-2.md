[← Back](README.md) | [English](ALGORITHM-2.md) | [Japanese](ALGORITHM-2-ja.md)

# Converting trio sequences to patterns of resemblance: algorithm, part 2

This is the second part of the algorithm of `phi3def2.py`. The main procedure (Steps 1–6) and the operations A.1–A.8 are in [README.md](README.md#step-1).

<a id="a9"></a>
### A.9 The reach of a $`\le_2`$-able node (D9)

$`\mathrm{lh}_1(x)`$ takes a $`\le_2`$-able root term $`x`$ (with $`A`$, $`P`$, $`W`$, $`U`$, $`q`$, $`G`$, $`D`$, $`\Lambda`$, $`d_m`$, $`\delta_m`$ of A.3) and gives its $`\le_1`$-reach, a sum; it is called from (lh-6), and the value $`\mathrm{pre}(x)`$ that it records in (LG-3) is used by (lh-3-2). Let $`r = \mathrm{lev}(D)`$ and $`S = (d_q)`$.
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

<a id="a10"></a>
### A.10 The read of a level column's children (D8)

$`\mathrm{LK}(x, K, m)`$ takes a $`\le_2`$-able $`x`$ (with its $`U`$, $`q`$, $`D`$, $`\Lambda`$), its level column $`K = K_m`$ and $`m`$, reads the children of $`K`$ and gives a list of columns; it is called from (lh-3-3) and (LG-2-2). All reads in LK use the empty context $`\rho_\varnothing`$.

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

<a id="a11"></a>
### A.11 The fold of a column's children (D8)

$`\mathrm{F}(S;\ x, G, \ell, b, \Delta, t_0, \mathrm{lastG};\ \rho)`$ takes a sum $`S`$ and a column $`G`$, folds the reads of the children of $`G`$ into $`S`$, and gives the new sum; it is called from (lh-3-3), (LG-1-2) and (LG-2-2). $`x`$ is the root term that the read belongs to, $`\ell`$ a level, $`b`$ the frame base (a children list), $`\Delta = (\Delta_1, \ldots, \Delta_n)`$ a level list, $`t_0`$ a term or $`\mathrm{none}`$. It keeps a list $`I`$ of index images, empty at the start. Let $`V`$ be the children of $`G`$ with $`z = 1`$ and $`y = \ell + 1`$, and $`H = \mathrm{sub}(V_1)`$ if $`V \ne ()`$ ($`H = ()`$ otherwise). If $`H \ne ()`$ and the last entry of $`H`$ is not cut, let $`E`$ be the $`c`$ in $`V_2, V_3, \ldots`$ that are not (as places) entries of $`H`$ and have $`c \ne V_1`$; otherwise $`E = ()`$. Let $`\beta`$ be true iff $`|E| = 1`$ and $`\mathrm{ch}(E_1) = ()`$ (**one bare extra up-kid**). For each child $`c`$ of $`G`$ in order, with $`\mathrm{lst}`$ = ($`\mathrm{lastG}`$ and $`c`$ is the last child):
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

<a id="a12"></a>
### A.12 Summands of $`U`$: limits, covers, groups, blocks (D5)

These functions take $`\omega`$ columns $`G`$, $`G'`$ (summands of a $`U`$-form, A.3) and give truth values, lists and columns; $`\mathrm{blk}`$ is called from (lh-3-3-1), $`\mathrm{grp}`$ from $`\mathrm{blk}`$ and $`\mathrm{wit}`$ (A.4), and the others from $`\mathrm{grp}`$, $`\mathrm{wit}`$, LG (A.9) and (F-2).

**Blocks.** $`\mathrm{blk}(U)`$ says that an earlier limit summand has a block: for $`G = \mathrm{ch}(U)`$ with last group $`(a, b)`$, it is true iff some $`G_i`$ with $`i \lt a`$ has $`\mathrm{lim}(G_i)`$ and $`\mathrm{cont}(G_i)`$.

**Groups.** $`\mathrm{grp}(G_1, \ldots, G_n)`$ is a list of pairs $`(i, j)`$. Start with $`i = 1`$. While $`i \le n`$: let $`j = i`$;
- (grp-1) if $`\mathrm{lim}(G_j)`$, $`j \lt n`$ and $`\mathrm{ch}(G_{j+1}) = ()`$, let $`j = j + 1`$;
- (grp-2) else if $`\mathrm{lim}(G_j)`$, $`j \lt n`$ and $`\mathrm{lvonly}(G_{j+1})`$, let $`j = j + 1`$;
- (grp-3) else if $`\mathrm{lim}(G_j)`$, $`j \lt n`$ and $`\mathrm{cov}(G_j, G_{j+1})`$, let $`j = j + 1`$;

then add $`(i, j)`$ to the list and let $`i = j + 1`$. The **last group** is the last pair $`(a, b)`$; $`b = n`$.

**Limit summands.** $`\mathrm{lim}(G)`$ says that the rightmost leaf of $`G`$ is a marker of $`G`$. Let $`\pi_0 = G, \pi_1, \ldots, \pi_r`$ be the rightmost path ($`\pi_{i+1}`$ is the last child of $`\pi_i`$, and $`\pi_r`$ has no children), and $`f = \pi_r`$.
- (lim-1) If $`r = 0`$, $`z(f) \ne 0`$ or $`y(f) \lt 1`$, then $`\mathrm{lim}(G)`$ is false.
- (lim-2) Otherwise, for $`i = r - 1, r - 2, \ldots, 0`$: if $`z(\pi_i) = 1`$ and $`y(\pi_i) \le y(f)`$, then:
  - (lim-2-1) if $`i \ne 0`$ and $`y(\pi_i) = y(G) = y(f)`$, go on with the next $`i`$ (an $`\omega`$ child on $`G`$'s level is passed through);
  - (lim-2-2) otherwise $`\mathrm{lim}(G)`$ is true iff $`i = 0`$ and $`y(G) = y(f)`$.
- (lim-3) If the loop ends without a result, $`\mathrm{lim}(G)`$ is false.

**Levels only.** $`\mathrm{lvonly}(G)`$ is true iff every child $`c`$ of $`G`$ is an up-kid of $`G`$ with $`\mathrm{lvonly}(c)`$ (true if $`G`$ has no children).

**Covers.** $`\mathrm{cov}(G, G')`$ says that the summand $`G'`$ after the limit summand $`G`$ repeats $`G`$ (or a prefix of its children with $`G`$'s levels covered).
- (cov-1) If $`\mathrm{cont}(G)`$ (below) and $`\mathrm{ch}(G) \ne ()`$: let $`C = \mathrm{ch}(G')`$.
  - (cov-1-1) If $`C \ne ()`$, its last entry is $`1`$, $`|C| \ge 2`$ and $`\mathrm{em}(C_{|C|-1}, y(G'))`$, remove the last entry of $`C`$.
  - (cov-1-2) If $`C \ne ()`$, $`|C| \lt |\mathrm{ch}(G)|`$, $`C`$ is a prefix of $`\mathrm{ch}(G)`$, and $`|L(G)| \le |L((y(G'), z(G'), C))|`$ (A.8), then $`\mathrm{cov}(G, G')`$ is true.

  If it is not true here, go on with (cov-2).
- (cov-2) If $`\mathrm{cont}(G)`$ is false, or $`\mathrm{ch}(G) = ()`$, or the last child of $`G`$ is not $`(y(G), 0, ())`$, then it is false.
- (cov-3) Let $`s = \mathrm{strip}(G)`$. If $`s = \mathrm{none}`$ or $`\mathrm{ch}(s) = ()`$, it is false.
- (cov-4) If $`G' = s`$, it is true.
- (cov-5) Otherwise it is true iff $`\mathrm{ch}(G') \ne ()`$, the last child of $`G'`$ is $`1`$, $`|\mathrm{ch}(G')| \ge 2`$, $`\mathrm{em}`$ holds for the child before it and $`y(G')`$, and $`G'`$ without its last child equals $`s`$.

**Strip.** $`\mathrm{strip}(G)`$ removes the rightmost leaf:
- (strip-1) If $`\mathrm{ch}(G) = ()`$, the result is $`\mathrm{none}`$.
- (strip-2) Otherwise let $`s'`$ be $`\mathrm{strip}`$ of the last child $`B_k`$. The result is $`(y(G), z(G), (B_1, \ldots, B_{k-1}))`$, with $`s'`$ added at the end if $`s' \ne \mathrm{none}`$.

**Ends in a marker.** $`\mathrm{em}(K, \ell)`$ is true iff the rightmost leaf $`f`$ of $`K`$ (reached through last children; $`f = K`$ if $`K`$ has no children) has $`z(f) = 0`$ and $`y(f) = \ell`$.

**Content.** $`\mathrm{cont}(G)`$ says that some level column of $`G`$ has children other than its chain.
- (cont-1) If $`\mathrm{up}(G) = ()`$, it is false.
- (cont-2) Otherwise it is true iff some entry $`C`$ of $`\mathrm{sub}^\top(G)`$ other than the first (A.7) has $`\mathrm{Rest}(C) \ne ()`$.

**The marker replaced.** $`\mathrm{limx}(G, x)`$ replaces the rightmost leaf of $`G`$ by the root term $`x`$:
- (limx-1) If $`\mathrm{ch}(G) = ()`$, the result is $`\mathrm{root}(\mathrm{ch}(x)) = x`$.
- (limx-2) Otherwise the result is $`(y(G), z(G), (B_1, \ldots, B_{k-1}, \mathrm{limx}(B_k, x)))`$.

**The levels-only chain.** $`\mathrm{lchain}(y, k) = (y, 1, (\mathrm{lchain}(y + 1, k - 1)))`$ if $`k \gt 1`$, and $`(y, 1, ())`$ if $`k \le 1`$.

<a id="a13"></a>
### A.13 The fold $`\oplus`$ (D9)

$`S \oplus Y`$ takes a nonempty sum $`S`$ with first term $`S_1`$ and a term $`Y`$ and gives a sum; it is called from $`\mathrm{lh}`$ (A.2), $`\mathrm{lh}_1`$ and LG (A.9) and F (A.11).
- (fold-1) If $`Y \le S_1`$, the result is $`S + (Y)`$.
- (fold-2) If $`Y \gt S_1`$ and $`Y`$ is $`\le_2`$-able, the result is $`\mathrm{lh}(Y) + (Y)`$.
- (fold-3) Otherwise the result is $`\mathrm{lh}(Y)`$.

$`S \succ S'`$ compares two sums term by term: at the first position where the terms differ, the larger term wins; if one sum is a prefix of the other, the longer one is larger.

<a id="a14"></a>
### A.14 The copy of a root $`\omega`$ run (D4)

$`\mathrm{Up}(a;\ N, \mathrm{last})`$ takes a root $`\omega`$ column $`a`$, a root term $`N`$ and a flag, and gives $`a`$ lifted by one level; it is called from (lh-5). It uses $`r(s, Y, \mathrm{lst})`$, where $`s = (y, z, B)`$ is a column, $`Y`$ a list of levels (of the $`\omega`$ columns above $`s`$) and $`\mathrm{lst}`$ a flag:
- (Up-1) If $`y = 0`$, then $`r = s`$.
- (Up-2) If $`\mathrm{lst}`$, $`B = ()`$, $`z = 0`$ and $`N \ne \mathrm{none}`$: let $`Y'`$ be the entries $`o`$ of $`Y`$ with $`o \le y`$, in order. If $`Y' \ne ()`$, ($`|Y'| = 1`$, or every entry of $`Y'`$ is $`y`$ and $`\max Y \gt y`$), the last entry of $`Y'`$ is $`y`$, and $`Y_1 = y`$, then $`r = N`$ (the final marker is the $`\Omega_1`$-multiplier $`N`$). If this condition fails, go on with (Up-3).
- (Up-3) Otherwise let $`Y'' = (Y, y)`$ if $`z = 1`$ and $`Y'' = Y`$ if not. Then $`r = (y + 1,\ z,\ (r(B_1, Y'', \mathrm{lst} \land 1 = k), \ldots, r(B_k, Y'', \mathrm{lst} \land k = k)))`$, where the flag goes to the last child only.

$`\mathrm{Up}(a;\ N, \mathrm{last}) = (2,\ 1,\ (r(B_i, (y(a)), \mathrm{last} \land i = k))_{i = 1, \ldots, k})`$ for $`\mathrm{ch}(a) = (B_1, \ldots, B_k)`$.

<a id="a15"></a>
### A.15 Splitting a column (D1)

These three functions take a column or a list of columns and give lists of columns or a column; they are called from (le2-3), (lh-7) and (lh-8).
- $`\mathrm{split}(W) = (\mathrm{hi}, \mathrm{lo})`$: $`\mathrm{hi}`$ is the list of the children of
  $`W`$ with $`y \ge 2`$ or $`z = 1`$, and $`\mathrm{lo}`$ the list of the others, each in order.
- $`\Omega\mathrm{pre}(\mathrm{hi})`$ is the longest prefix of $`\mathrm{hi}`$ whose columns all have
  $`z = 1`$.
- $`W + k = (y(W), z(W), (\mathrm{ch}(W), 1^k))`$: $`k`$ units appended to the children.

<a id="a16"></a>
### A.16 The collapse C1 (D2)

$`\mathrm{C1}_N`$ collapses a column over the root term $`N`$ and gives a term or a wrapped column, $`\mathrm{C1s}_N`$ does this on a list and gives a sum, and $`\mathrm{c1fixed}`$ tests a list; they are called from (le2-4), (lh-7), (lh-8), (lh-8-3) and (C2-5-3).

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

**The owner lookup.** $`\mathrm{own}(\sigma, y)`$ takes a stack $`\sigma`$ of entries and a level
$`y`$. An entry is $`(y_e, h_e)`$ or $`(y_e, h_e, \mathrm{ok}_e)`$: the level of an $`\omega`$ column,
the shift of its image, and (in C1) a flag. Let $`a`$ be the topmost entry with $`y_a \le y`$.
- (own-1) If $`a`$ exists, has a third component, and $`\mathrm{ok}_a`$ is false, then the result is
  $`\mathrm{none}`$.
- (own-2) If $`a`$ exists otherwise, the result is $`a`$.
- (own-3) If no entry has $`y_a \le y`$, the result is $`\mathrm{none}`$.

<a id="a17"></a>
### A.17 The read of a same-level $`\omega`$ column (D3)

$`\mathrm{Kimg}`$ takes a same-level $`\omega`$ column $`K`$ and gives its summand, a root term, and $`\mathrm{KI}`$ takes the children of such a column and gives their read, a sum; they call each other and are called from LK (A.10), F (A.11), (C2-2) and (C2-3) (A.18). The level lists $`\Delta`$ and the read context $`\rho`$ are in [Notation](#level-list).

$`\mathrm{Kimg}(K;\ x, \ell, \Delta, t_0, \mathrm{last}, c, j_0;\ \rho)`$ is the summand of a same-level $`\omega`$ column $`K`$ with $`y(K) = \ell`$. $`c`$ is a cap ($`\mathrm{none}`$ or an integer; $`\mathrm{none}`$ when not given) and $`j_0`$ a flag ($`\mathrm{false}`$ when not given). It gives a root term.
- (Kimg-1) If $`\Delta = (\Delta_1, \ldots, \Delta_n)`$ is a list: let $`B = \mathrm{ch}(K)`$, $`j = \min(\mathrm{lev}(K) - 1,\ n - 1)`$ (A.8), and $`V = \mathrm{up}(K)`$. Let $`\kappa`$ (the level column that $`K`$ may share) be:
  - (Kimg-1-1) if $`\rho_1 = (d, \kappa')`$ and $`d = x`$: $`\kappa = \kappa'`$;
  - (Kimg-1-2) otherwise, if $`x \ne \mathrm{none}`$ and $`x`$ is $`\le_2`$-able: $`\kappa = K_1(x)`$ (below);
  - (Kimg-1-3) otherwise $`\kappa = \mathrm{none}`$.

  Then:
  - (Kimg-1-4) If $`V \ne ()`$, $`\kappa \ne \mathrm{none}`$, $`V_1 = \kappa`$ and $`\mathrm{Rest}(V_1) \ne ()`$ (`kbcut`: $`K`$ shares the level of $`K_1`$): remove the child $`V_1`$ from $`B`$ and let $`j = \min(|V| - 1,\ n - 1)`$.
    - (Kimg-1-4-1) If $`c \ne \mathrm{none}`$, let $`j = \max(0, \min(j, c))`$ (`kb2`).

    Then remove the children $`V_2, \ldots, V_{1+j}`$ from $`B`$.
  - (Kimg-1-5) Otherwise, if $`j \ne 0`$ or $`V \ne ()`$, remove all up-kids of $`K`$ from $`B`$.
  - (Kimg-1-6) If $`j_0`$ (**the rule `kdl0`**): let $`\Lambda = L(K)`$ (A.8), let $`j`$ be the largest $`i - 1`$ with $`\Lambda_i \ne \bot`$ and $`\Lambda_i = \Lambda_1`$ as terms (or $`0`$ if there is none), $`j = \min(j, n - 1)`$, and let $`B`$ be $`\mathrm{ch}(K)`$ without its up-kids. Reason: a $`D`$-level $`\omega`$ column read after an elder sibling (or nested in a same-level child) is read on the lowest level of its last chain, not above its top.

  The result is $`\mathrm{root}(\Delta_{1+j} + \mathrm{KI}(B;\ x, \ell, \Delta, t_0', \mathrm{last};\ \rho))`$, where $`t_0' = t_0`$ if $`\mathrm{last}`$ and $`t_0' = \mathrm{none}`$ otherwise.
- (Kimg-2) Otherwise ($`\Delta = b`$ is a single base) the result is $`\mathrm{root}(b + \mathrm{KI}(\mathrm{ch}(K);\ x, \ell, b, t_0', \mathrm{last};\ \rho))`$, with $`t_0'`$ as above.

$`\mathrm{KI}(B;\ x, \ell, \Delta, t_0, \mathrm{last};\ \rho)`$ reads the children $`B = (B_1, \ldots, B_k)`$ of a same-level $`\omega`$ column. $`x`$ is a root term, $`\ell`$ a level, $`t_0`$ a term or $`\mathrm{none}`$. It gives a sum. Keep a list $`O`$ and a pending run $`R`$, both empty at the start. To **flush** with a flag $`f`$: if $`R \ne ()`$, add the terms of $`\mathrm{C2s}_x(R;\ \ell, (), f;\ \rho)`$ to $`O`$ and empty $`R`$. For $`i = 1, \ldots, k`$, with $`g = B_i`$ and $`\mathrm{lg} = \mathrm{last} \land i = k`$:
- (KI-1) If $`y(g) \ne 0`$, not ($`z(g) = 1`$ and $`y(g) = \ell`$), and not ($`z(g) = 0`$ and $`y(g) \ge \ell`$): add $`g`$ to $`R`$.
  - (KI-1-1) If $`i = k`$, flush with $`\mathrm{lg}`$.
- Otherwise flush with $`\mathrm{false}`$, and then:
  - (KI-2) If $`y(g) = 0`$, add $`g`$ to $`O`$.
  - (KI-3) If $`z(g) = 1`$ and $`y(g) = \ell`$, add $`\mathrm{Kimg}(g;\ x, \ell, \Delta, t_0, \mathrm{lg};\ \rho)`$.
  - (KI-4) If $`z(g) = 0`$, $`y(g) = \ell`$, $`\mathrm{ch}(g) = ()`$, $`\mathrm{lg}`$ and $`t_0 \ne \mathrm{none}`$, add $`t_0`$ (the final bare marker is the $`\Omega_1`$-multiplier one level up).
  - (KI-5) If $`z(g) = 0`$ and $`y(g) = \ell`$, add $`\mathrm{root}(\mathrm{ch}(x) + \mathrm{KI}(\mathrm{ch}(g);\ x, \ell, \Delta, \mathrm{none}, \mathrm{true};\ \rho))`$ (**the rule `lastt`**, as in (C2-5-4-1): the children of $`g`$ are read with the flag $`\mathrm{true}`$, not $`\mathrm{lg}`$).
  - (KI-6) If $`z(g) = 0`$ and $`y(g) \gt \ell`$, add $`(y(g) - \ell,\ 0,\ \mathrm{KI}(\mathrm{ch}(g);\ x, \ell, \Delta, \mathrm{none}, \mathrm{lg};\ \rho))`$.
  - (KI-7) Otherwise add $`\mathrm{C2}_x(g;\ \ell, (), \mathrm{lg};\ \rho)`$. This case does not occur: (KI-1) to (KI-6) cover every column.

The result is $`\Sigma(O)`$.

$`K_1(x)`$ for a $`\le_2`$-able $`x`$ is the first up-kid of its column $`D`$ (A.3), or $`\mathrm{none}`$ if $`D`$ has no up-kid.

<a id="a18"></a>
### A.18 The collapse C2 (D3)

$`\mathrm{C2}_x`$ collapses a column read inside an $`\omega`$ column to the target $`x`$ and gives a term, and $`\mathrm{C2s}_x`$ does this on a list and gives a sum; they are called from (OL-1-2), (F-5-1) and KI (A.17).

$`\mathrm{C2}_x`$ is $`\Omega_\omega \mapsto x`$, $`\Omega_{\omega+j} \mapsto \Omega_j`$. Every marker collapses to the target of the $`\omega`$ column that owns it.

$`\mathrm{C2}_x(s;\ \ell, \sigma, \mathrm{last};\ \rho)`$ takes a root term $`x`$ (the target), a column $`s = (y, z, B)`$, the level $`\ell`$ of the $`\omega`$ column $`D`$ being collapsed, a stack $`\sigma`$ of entries $`(y_e, h_e)`$, a flag and a context. It gives a term.
- (C2-1) If $`y = 0`$, the result is $`s`$.
- (C2-2) If $`z = 1`$, $`\rho_D = (x', \ell')`$, $`y = \ell'`$ and $`y \lt \ell`$ (a $`D`$-level $`\omega`$ column deep inside a level column): let $`\rho'`$ be $`\rho`$ with $`\rho_D`$ replaced by $`\mathrm{none}`$.
  - (C2-2-1) If $`x'`$ is $`\le_2`$-able (A.3) with $`U'`$, $`q'`$ and last $`\omega`$ column $`D'`$, and $`\mathrm{kdl}(D', L(D')) = s`$ (A.8): the result is $`\mathrm{Kimg}(s;\ x', \ell', (\delta'_1, \ldots, \delta'_{q'}), \mathrm{none}, \mathrm{last}, \mathrm{none}, \mathrm{true};\ \rho')`$, where $`\delta'_i = (\mathrm{ch}(x'), U'^i)`$.
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
  - (C2-5-4) Otherwise:
    - (C2-5-4-1) If $`y = \ell`$ (**the rule `lastt`**), the result is $`\mathrm{root}(\mathrm{ch}(x) + \mathrm{C2s}_x(B;\ \ell, (), \mathrm{true};\ \rho))`$. Reason: the new root term is built from $`B`$ alone, so $`B`$ is read with $`\mathrm{last}`$ decided inside that term, as the same subtree is read at the root; the summands that follow it are folded by their own rules.
    - (C2-5-4-2) Otherwise the result is $`(y - \ell,\ 0,\ \mathrm{C2s}_x(B;\ \ell, (), \mathrm{last};\ \rho))`$.

$`\mathrm{C2s}_x(B;\ \ell, \sigma, \mathrm{last};\ \rho)`$ is C2 on a list $`B = (B_1, \ldots, B_k)`$. Let $`r_i = \mathrm{C2}_x(B_i;\ \ell, \sigma, \mathrm{last} \land i = k;\ \rho)`$. Build a list $`O`$, for $`i = 1, \ldots, k`$:
- (C2s-1) If $`z(B_i) = 1`$, $`\sigma = ()`$, $`r_i = (1, 0, R)`$, $`O \ne ()`$, the last entry $`o`$ of $`O`$ has $`y(o) = 1`$, $`z(o) = 0`$, $`\mathrm{ch}(o) \ne ()`$ and a last child with $`z = 1`$, and $`z(B_n) = 1`$ for $`n = |O|`$ (the input column whose position is the current length of $`O`$): replace $`o`$ by $`(1, 0, (\mathrm{ch}(o), R))`$. (Consecutive wrapped $`\omega`$ columns merge into one $`U`$-form.)
- (C2s-2) Otherwise add $`r_i`$ to $`O`$.

The result is $`\Sigma(O)`$.

<a id="notation"></a>
### Appendix: notation

**Terms, sums and places.**

- A **term** is $`s = (y, z, B)`$. Here $`y = y(s)`$ is the row-1 entry of the column (its **level**),
  $`z = z(s)`$ is its row-2 entry, and $`B = \mathrm{ch}(s) = (B_1, \ldots, B_k)`$ are its children in order.
  The row-0 entry is the depth in the tree and is not stored.
- $`1 = (0, 0, ())`$ is the matrix $`(0,0,0)`$. A child equal to $`1`$ is a **unit**.
- A **sum** is a finite sequence of terms $`(t_1, \ldots, t_n)`$; $`()`$ is $`0`$. For a sequence
  $`B`$, $`\mathrm{root}(B) = (0, 0, B)`$.
- $`(A, B)`$ is the concatenation of the sequences $`A`$ and $`B`$, and $`U^m`$ is the sequence of
  $`m`$ copies of $`U`$. So $`\mathrm{root}(A, U^m)`$ is the root term whose children are $`A`$
  followed by $`m`$ copies of $`U`$. $`A + B`$ is always the sum of A.5, never concatenation.
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

<a id="read-context"></a>
**The read context.** The collapse C2 and the read of a same-level $`\omega`$ column (A.18, A.17) take a **read context** $`\rho = (\rho_C, \rho_D, \rho_1)`$. Each part is $`\mathrm{none}`$ or:
- $`\rho_C = (c, \ell_C, \Delta_C)`$: the $`\omega`$ column being read belongs to the node $`c`$, on level $`\ell_C`$, with the level list $`\Delta_C`$ (below);
- $`\rho_D = (x', \ell')`$: a level column of the $`\le_2`$-able node $`x'`$ is being read, and $`\ell'`$ is the level of its column $`D`$ (A.3);
- $`\rho_1 = (d, \kappa)`$: the read belongs to the successor $`d`$, and $`\kappa`$ is the next level column (or $`\mathrm{none}`$).

The context is passed down unchanged unless a branch says otherwise. **Every computation of $`\mathrm{lh}`$ (A.2) starts with the empty context $`\rho_\varnothing = (\mathrm{none}, \mathrm{none}, \mathrm{none})`$**, also when it is called inside another computation.

<a id="level-list"></a>
**Level lists.** A **level list** $`\Delta`$ is either a list $`(\Delta_1, \ldots, \Delta_n)`$ of children lists (the levels $`\delta_m = \mathrm{ch}(d_m)`$ of A.3), or a **single base** $`b`$ (one children list).

**How the branches are written.** The operations are written as nested lists of branches. Each section starts with a sentence that gives the inputs, the output and the places that call the operation. The branches follow in the order of the code, each with a label such as (C2-5-1). The label starts with the name of the function, so the labels of one function form one list. "Otherwise" always means "none of the earlier branches at this depth applies".

<a id="names"></a>
### Appendix: names in the code

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

**Notes on the code.** The read context is kept in global stacks (`KCTX`, `KDX`, `K1REF`) that a nested call of `lh` does not clear. On all 3290 test matrices, clearing them at every call of `lh` gives the same patterns, so the text states the cleared form ([notation](#read-context)). The parameter `top` of `C2` and `C2s` has no effect.
