[← Back](README.md)

# Pair-sequence combinatorics for $`\Phi`$: S1, R, 2.4, T

Companion to [PROOF](PROOF.md). The notation ($`R`$, $`o`$, $`\mathcal{L}`$, anchor, $`\mathrm{lh}`$,
$`\mathrm{Coll}_A`$, $`\oplus`$) is as there and in [POR.md](../POR.md) §2–§3. Labels:

- **PROVED**: full argument here (it may use CITED items, named).
- **CITED**: a Lean theorem (file / name) or a paper.
- **OPEN**: not proved; the missing piece is named.

## 0. Status

| item | status |
|---|---|
| Lemma 1 (tree invariants I0–I3) | PROVED |
| Lemma 2 ($`P`$ = root segments) | PROVED |
| Lemma 3 (locality of expansion) | PROVED |
| Lemma 4 (Sh: subtree of a $`y = 0`$ column is standard) | PROVED |
| **S1 (a), (b), (c)** | **PROVED** |
| Lemma 5 (ordinal facts: CNF, additivity, $`o(M) = \sup o(M[n])`$) | PROVED from CITED Lean facts + S1 |
| Lemma 6 ($`\mathcal{L}N`$ is standard) | PROVED |
| **Lemma R** | **PROVED** (induction along fundamental sequences) |
| **Lemma 2.4**: $`\mathrm{anchor}(N)`$ standard | PROVED |
| **Lemma 2.4**: $`\mathrm{lh}(N)`$ standard, $`N = 1`$ or non-epsilon | PROVED |
| **Lemma 2.4**: $`\mathrm{lh}(N)`$ standard, $`N`$ epsilon | **PROVED** (Lemma C + T) |
| **T** (termination of $`\mathrm{lh}`$) | **PROVED** (depth of nested calls $`\lt`$ height of the last child) |
| Lemma 7 (Sib: sibling terms are non-increasing) | PROVED |
| Lemma 8 (G\*: a descending node is below its level ancestor) | PROVED |
| Lemma 9 ($`y`$-descent) | PROVED |
| **Theorem SC** (standard $`\iff`$ R0 + I0 + (A) + Sib + G\*) | **PROVED** (§8b) |
| Lemma 10 (Coll is strictly monotone) | PROVED |
| **Lemma C** ($`\mathrm{Coll}_A(s\vert_i)`$ is standard, for <em>every</em> $`y = 1`$ column $`s`$ of <em>any</em> $`N \in R`$ and every truncation $`i`$) | **PROVED** (§8c) |
| **Mono\*** ($`\mathcal{T}_k`$ strictly increasing at every level on valid terms; see [TR](TR.md) §2) | **PROVED** in [TR](TR.md) |
| **Lemma TR** ($`\mathrm{val} \circ \mathcal{T} = o`$; see [TR](TR.md)) | **PROVED** in [TR](TR-2.md) §4b (Theorem Cof by propagation along the path, from Mono\*, SC and cited $`T^1`$ facts; no LOC needed) |

All items of this file, and Lemma TR, are PROVED. Corrections to [PROOF](PROOF.md) are in §9.

---

## 1. Facts used

### 1.1 Expansion ([pss-proof](https://github.com/koteitan/pss-proof) `oper`)

For $`M`$ with last index $`j_1 \ge 1`$:

- $`M_{j_1} = (0,0)`$, or no parent in row $`i_1`$: $`M[n] = \mathrm{Pred}\,M`$.
- Otherwise put $`i_1 = 1`$ if $`y_{j_1} \gt 0`$, else 0. $`j_0`$ = parent of $`j_1`$ in row $`i_1`$:
  - row 0: the largest $`j \lt j_1`$ with $`x_j \lt x_{j_1}`$;
  - row 1: the nearest proper row-0 ancestor with $`y \lt y_{j_1}`$.
- $`d_0 = x_{j_1} - x_{j_0}`$ if $`i_1 = 1`$, else 0. ($`d_1 = 0`$ always for pairs.)
- $`M[n] = M{\restriction}j_0 \mathbin{+\!\!+} B_0 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B_{n-1}`$, where
  $`B_k = ((x_j + k \cdot d_0, y_j))_{j_0 \le j \lt j_1}`$.

All columns strictly between $`j_0`$ and $`j_1`$ are row-0 descendants of $`j_0`$. So shifting the
whole block by $`k \cdot d_0`$ is the usual "ascending" rule.

### 1.2 Cited Lean facts

From [pss-proof](https://github.com/koteitan/pss-proof):

- **F1** `ctps_iff_leExpPS`: CTPS $`M \iff \exists v,\ M \mathrel{\le_p[\,]} \mathrm{diag}(0,v)`$. So every CTPS
  arises from some $`\mathrm{diag}(0,v) = (0,0)(1,1)\cdots(v,v)`$ by finitely many steps
  $`M \mapsto M[n]`$, $`n \ge 1`$.
- **F2** `ctps_oper`: CTPS $`M`$, $`n \ge 1 \Rightarrow`$ CTPS $`M[n]`$.
- **F3** prefixes: `take_leExpPS_of_lt` with `stps_expand` and `leExpPS_head`.
  A nonempty prefix of a CTPS is CTPS.
- **F4** `ltExpPS_ltPS_of_lng`: $`\mathrm{Lng}\,M \ge 2 \Rightarrow M[n] \lt_p M`$.
- **F5** `oper_prefix`: $`M[m]`$ is a prefix of $`M[n]`$ for $`1 \le m \le n`$.
- **F6** `lePS_iff_leExpPS`, `trans_injOn`, `trans_surjOn`, `trans_bijOn`,
  `trans_order_iso`, `trans_mapsTo`, `OT_Trans_of_CTPS`, `Trans_zero_singleton'`.

Also from [pss-proof](https://github.com/koteitan/pss-proof):

- **F7** `P_last_multi`, `P_fseq_2`; `P_nonmulti_eq`; `Pcut_props`.
- **F8** `STPS_RTPS`.
- **F9** `Trans_P_equivariance`:
  RTPS $`M \land \neg\,\mathrm{zeroT}(P\,M)_0 \Rightarrow \mathrm{Trans}\,M = \mathrm{SigmaB}(\mathrm{map}\ \mathrm{transPComponent}\ (P\,M))`$.
  Here $`\mathrm{transPComponent}\,J = D_0 0`$ if zeroT $`J`$, else $`\mathrm{Trans}\,J`$, and SigmaB
  concatenates the principal lists.
- **F10** `Trans_monoT_principal`: RTPS, monoT, $`\mathrm{Trans} \ne 0 \Rightarrow \mathrm{Trans}\,M = \mathrm{trm}[p]`$.
- **F11** `Trans_Mark_multi_equations`: for RTPS multiT $`M`$,
  $`\mathrm{Trans}\,M = \mathrm{Trans}(M{\restriction}\mathrm{Pcut}) + \begin{cases} D_0 0 & \text{if } M.\mathrm{drop}\,\mathrm{Pcut} = [(0,0)] \cr \mathrm{Trans}(M.\mathrm{drop}\,\mathrm{Pcut}) & \text{otherwise.} \end{cases}`$
- **F12** `OT` = `isOT_BT`: a sum $`\mathrm{trm}[p_1,\ldots,p_m]`$ is in OT iff each $`p_i`$ is OT and
  $`p_1 \ge \cdots \ge p_m`$ (`descP`) ([B86] §2.2).

From [Rank.lean](../Rank.lean) and [Expand.lean](../Expand.lean) of this library:

- **F13** `rank_pairL_eq`, `typein_pairLt`, `exists_le_oper`, `isWellOrder_ctpsLt`
  ([Rank.lean](../Rank.lean)), and `pairL_step_eq_oper` ([Expand.lean](../Expand.lean): a `pairL`
  step on a state of length $`\ge 2`$ is `oper l (k+1)`).
  $`o = \mathrm{pairOrdL}`$ is the rank of the system whose steps are $`M \mapsto M[n]`$, $`n \ge 1`$.
  Hence $`o(M) = \sup_{n \ge 1} (o(M[n]) + 1)`$ for $`\mathrm{Lng}\,M \ge 2`$, $`o((0,0)) = 1`$,
  $`o(()) = 0`$, and $`o(M) = \mathrm{otp}\{\text{nodes} \lt_p M\}`$.

---

## 2. Tree invariants

**Lemma 1 (PROVED).** Every CTPS $`M`$ satisfies:

- (I0) $`x_{j+1} \le x_j + 1`$;
- (I1) $`y_j \le x_j`$;
- (I2) $`y_c \le y_{p(c)} + 1`$ for every non-root column $`c`$, where $`p`$ = row-0 parent;
- (I3) if $`c \lt c'`$ are siblings (same row-0 parent), then $`y_c \ge y_{c'}`$.

<em>Proof.</em> Induction along F1. Base $`\mathrm{diag}(0,v)`$: a chain with $`y = x`$, so all four hold. Step
$`M \mapsto M[n]`$:

- Pred keeps all four, since the parents of the kept columns do not change.
- Case $`i_1 = 1`$, $`d_0 \gt 0`$ (the argument for $`B_0`$ is the same with $`k = 0`$).
  - (I0) Inside each $`B_k`$ the differences are those of $`M`$. At the junction $`B_k \to B_{k+1}`$ we
    need $`x_{j_0} + d_0 \le x_{j_1-1} + 1`$, that is $`x_{j_1} \le x_{j_1-1} + 1`$. This is (I0) for $`M`$.
  - (I1) Copies keep $`y`$ and do not decrease $`x`$.
  - Parents in the new matrix: for $`j \in (j_0, j_1)`$ the parent of $`\mathrm{copy}_k(j)`$ is
    $`\mathrm{copy}_k(p(j))`$. The parent of $`\mathrm{copy}_k(j_0)`$, $`k \ge 1`$, is
    $`\mathrm{copy}_{k-1}(p(j_1))`$: we need the last column of $`B_{k-1}`$ with $`x_j \lt x_{j_1}`$,
    which is $`p(j_1) \ge j_0`$.
  - (I2) at $`\mathrm{copy}_k(j_0)`$: if $`p(j_1) = j_0`$ it is trivial. Otherwise $`p(j_1)`$ is an
    ancestor of $`j_1`$ strictly after $`j_0`$, so $`y_{p(j_1)} \ge y_{j_1} \gt y_{j_0}`$ ($`j_0`$ is the
    nearest ancestor with $`y \lt y_{j_1}`$).
  - (I3) The children of $`\mathrm{copy}_{k-1}(p(j_1))`$ are those of $`p(j_1)`$ in $`M`$ with $`j_1`$
    replaced by $`\mathrm{copy}_k(j_0)`$. Also $`y_{j_0} \lt y_{j_1} \le`$ (earlier siblings) by (I3) in
    $`M`$. The other children lists lose only a last element ($`j_1`$).
- Case $`i_1 = 0`$, $`d_0 = 0`$, $`j_0 = p(j_1)`$.
  - (I0) At the junction, $`x_{j_0} \le x_{j_1-1}`$.
  - The copies of $`j_0`$ get the parent $`p(j_0)`$, because every column of $`B_k`$ has
    $`x \ge x_{j_0}`$. The children of $`p(j_0)`$ in $`M`$ end with $`j_0`$, since everything after
    $`j_0`$ descends from $`j_0`$. So the new list is $`(\ldots, j_0, j_0, \ldots, j_0)`$, with equal
    $`y`$, and (I2) and (I3) hold. ∎

**Corollaries (PROVED).** For CTPS $`M`$:

- (T0) The parent of a non-root $`c`$ has $`x = x_c - 1`$. So $`x`$ is the depth, and the reading of
  [POR.md](../POR.md) §2 is exact.
- (T1) Roots are exactly the columns with $`x = 0`$, and each of them is $`(0,0)`$.
- (T2) A one-root $`N = (0, (C_1,\ldots,C_k))`$ has all $`y(C_i) \le 1`$, non-increasing. So the
  children are an H-block ($`y = 1`$) followed by a Lo-block ($`y = 0`$), and
  $`(0, H) = (0, B^{\mathrm{hi}})`$ is a **prefix** of $`N`$.
- (T3) $`N`$ is epsilon $`\iff`$ all children of the root have $`y = 1`$. So $`\mathrm{anchor}(N)`$ is
  epsilon or 1.
- (T4) For epsilon $`N`$ and $`W = C_k`$: $`y(W) = 1`$. The children of $`W`$ have $`y \le 2`$ and are
  non-increasing, so $`D_1,\ldots,D_p`$ ($`y = 2`$) come first, then the $`E`$'s ($`y = 1`$, then
  $`y = 0`$). Hence the fold input $`Y_i = (0, A + \mathrm{Coll}_A(D_1..D_i))`$ equals
  $`\mathrm{Coll}_A(W\vert_i)`$, where $`W\vert_i = (1, (D_1,\ldots,D_i))`$ is a prefix of $`W`$'s block.

Evidence: all four invariants and (T2)–(T4) hold on all 44,653 CTPS with $`\le 8`$ columns
(a numerical check).

## 3. Components, locality, subtrees

**Lemma 2 (PROVED).** For CTPS $`M`$ with root segments $`t_1 \cdots t_m`$,
$`P\,M = [t_1, \ldots, t_m]`$ (literal segments; no shift is needed).

<em>Proof.</em> Induction on $`m`$.

- $`m = 1`$: $`M`$ is zeroT ($`M = (0,0)`$) or monoT (column 0 is an ancestor of the last column),
  so $`P\,M = [M]`$ (`P_nonmulti_eq`).
- $`m \ge 2`$: $`M`$ is multiT. The row-0 ancestors of the last column form the chain starting at
  the root $`r_m`$ of $`t_m`$, and $`r_m \gt 0`$. So $`\mathrm{Pcut}\,M = r_m`$.
- Then `P_last_multi` gives $`P\,M = P(t_1 \cdots t_{m-1}) \mathbin{+\!\!+} [t_m]`$. ∎

**Lemma 3 (locality; PROVED).** Let $`M`$ be a matrix, $`j_1`$ its last column, and $`c`$ an
ancestor-or-self of $`j_1`$ with $`c \le j_0`$ (the bad root). Let $`Q = \mathrm{sh}(M[c..j_1])`$, where
$`\mathrm{sh}(x, y) = (x - x_c, y)`$. Then

```math
M[n] = M{\restriction}c \mathbin{+\!\!+} \mathrm{sh}^{-1}(Q[n]).
```

This holds in particular when $`y_c = 0`$ and $`c \lt j_1`$. (If $`i_1 = 1`$, $`c`$ itself has
$`y \lt y_{j_1}`$; if $`i_1 = 0`$, $`j_0 = p(j_1) \ge c`$.)

<em>Proof.</em> $`j_0`$, $`j_1`$, $`d_0`$ and all parents of columns in $`[c, j_1]`$ are computed inside
$`[c, j_1]`$, and they do not change under a uniform $`x`$-shift. ∎

**Lemma 4 (Sh; PROVED).** Let $`M`$ be CTPS and $`c`$ a column with $`y_c = 0`$. Then
$`\mathrm{sh}(\mathrm{subtree}(c))`$ is CTPS; in particular it is in $`R`$. (The subtree is the
contiguous block of $`c`$ and its row-0 descendants.)

<em>Proof.</em> Induction along F1. The base is trivial: the only $`y = 0`$ column of $`\mathrm{diag}(0,v)`$
is the root. Step $`M \mapsto M[n]`$.

- **Pred case** ($`M[n] = \mathrm{Pred}\,M`$). If the removed last column lies in $`\mathrm{subtree}(c)`$
  and is not $`c`$ itself, the new $`\mathrm{sh}(\mathrm{subtree}(c))`$ is a nonempty prefix of the old
  one, so it is CTPS by F3. Otherwise $`\mathrm{subtree}(c)`$ does not change.

For the other cases:

- **$`c \in G = M{\restriction}j_0`$, not an ancestor of $`j_1`$.** Its subtree lies in $`G`$ and ends at
  the same place. If $`j_0`$ were inside it, then $`c`$ would be an ancestor of $`j_1`$.
- **$`c \in G`$, an ancestor of $`j_1`$.** The new subtree is $`[c, \mathrm{end}]`$, and by Lemma 3 it
  equals $`\mathrm{sh}^{-1}(Q_c[n])`$ with $`Q_c = \mathrm{sh}(\mathrm{subtree}_M(c))`$. This is CTPS by
  the IH and F2.
- **$`c = \mathrm{copy}_k(j)`$, $`j`$ not an ancestor of $`j_1`$.** The subtree is the copy of
  $`\mathrm{subtree}_M(j)`$, shifted uniformly. It ends inside $`B_k`$. If $`e_j = j_1 - 1`$, the next
  column is $`\mathrm{copy}_{k+1}(j_0)`$, and $`x_{j_0} + d_0 = x_{j_1} \le x_j`$ ($`j_1`$ is not a
  descendant of $`j`$), so the subtree stops there.
- **$`c = \mathrm{copy}_k(j)`$, $`j`$ an ancestor of $`j_1`$.** Then $`j = j_0`$:
  - if $`i_1 = 1`$, an ancestor $`j \gt j_0`$ with $`y_j = 0 \lt y_{j_1}`$ would contradict "nearest";
  - if $`i_1 = 0`$, $`j_0 = p(j_1)`$ is the last proper ancestor.
- In the last case:
  - $`i_1 = 1`$: the new subtree is $`B_k \cdots B_{n-1} = \mathrm{sh}^{-1}(Q_{j_0}[n-k])`$.
  - $`i_1 = 0`$: the new subtree is
    $`B_k = \mathrm{sh}^{-1}(\mathrm{Pred}\,Q_{j_0}) = \mathrm{sh}^{-1}(Q_{j_0}[1])`$.
  - Both are CTPS by the IH and F2. ∎

Evidence: 55,679 subtrees (a numerical check).

---

## 4. S1

**S1.** For a nonempty matrix $`M`$ with $`M_0 = (0,0)`$, with root segments $`t_1 \cdots t_m`$:

```math
M \in \mathrm{CTPS} \iff \text{every } t_i \in R \text{ and } t_1 \ge_p t_2 \ge_p \cdots \ge_p t_m.
```

**On the shift caveat of [PROOF](PROOF.md) §2.** For CTPS every root is $`(0,0)`$ (T1), so the root
segments already start at $`(0,0)`$ and no shift is needed. For $`M_0 = (0,0)`$ the right-hand
side forces the same: $`t_i \in R`$ starts with $`(0,0)`$.

**(a) $`\Rightarrow`$ $`t_i \in R`$ (PROVED).**

- <em>Route 1:</em> each root is a $`y = 0`$ column, so Lemma 4 applies.
- <em>Route 2 (CITED):</em> [pss-proof](https://github.com/koteitan/pss-proof) `SkTPS_P_component` with
  Lemma 2, plus T1 for the head $`(0,0)`$.

**(b) $`\Rightarrow`$ non-increasing (PROVED).** Induction along F1. $`\mathrm{diag}(0,v)`$ has one root.
Step:

- If the last column is $`(0,0)`$, $`M[n] = \mathrm{Pred}\,M`$ drops $`t_m`$.
- Otherwise $`j_0, j_1 \in t_m`$, and by Lemma 3 ($`c = r_m`$),
  $`M[n] = t_1 \cdots t_{m-1} \mathbin{+\!\!+} t_m[n]`$.
- $`t_m[n]`$ has either one root, or (when $`j_0 = r_m`$ and $`i_1 = 0`$) the $`n`$ equal roots
  $`\mathrm{Pred}\,t_m`$. (If $`j_0 = r_m`$ and $`i_1 = 1`$, the copies sit at $`x \ge d_0 \ge 1`$. If
  $`j_0 \gt r_m`$, all new columns lie below $`r_m`$.)
- Its first root $`s_1`$ is a prefix of $`t_m[n]`$, so $`s_1 \le_p t_m[n] \lt_p t_m \le_p t_{m-1}`$ (F4).

**(c) $`\Leftarrow`$ (PROVED).** Let $`t_1 \ge \cdots \ge t_m`$ be in $`R`$ and $`M = t_1 \cdots t_m`$.

- If $`t_1 = (0,0)`$, then all $`t_i = (0,0)`$, since $`(0,0)`$ is $`\le_p`$ every CTPS. And
  $`(0,0)^m = ((0,0)(1,1)[2])[m]`$ is CTPS.
- Otherwise:
  1. **The terms.** Let $`p_i`$ be the principal term with $`\mathrm{trm}[p_i] = \mathrm{transPComponent}(t_i)`$:
     - if $`t_i = (0,0)`$, $`p_i = D_0 0`$;
     - otherwise $`\mathrm{Trans}\,t_i = \mathrm{trm}[p_i]`$ by F10, F8. Here
       $`\mathrm{Trans}\,t_i \ne 0 = \mathrm{Trans}(0,0)`$ and
       $`\mathrm{Trans}\,t_i \ne D_0 0 = \mathrm{Trans}((0,0)(0,0))`$ (F11), both by `trans_injOn`.
  2. **In TransRange.**
     - $`p_i \ge p_{i+1}`$: by `trans_order_iso` when both $`t`$'s differ from $`(0,0)`$. If
       $`t_{i+1} = (0,0)`$, use (B-a) below. The case $`t_i = (0,0) \ne t_{i+1}`$ cannot occur.
     - So $`s := \mathrm{trm}[p_1,\ldots,p_m] \in \mathrm{OT}`$ (F12).
     - $`s \lt D_0 D_\omega 0`$, because $`p_1 \lt D_0 D_\omega 0`$ (`trans_mapsTo`) and (B-b) below.
     - Three standard facts about Buchholz terms are used here (by the definitions of
       `lessBT`/`leBT`, following [B86] §2.1):
       - (B-a) every principal term $`D_u a`$ satisfies $`\mathrm{trm}[D_0 0] \le \mathrm{trm}[D_u a]`$.
         Either $`u \gt 0`$, or $`u = 0`$ and $`a \ge 0`$;
       - (B-b) `lessBT` compares lists lexicographically, so $`p_1 \lt D_0 D_\omega 0`$ gives
         $`\mathrm{trm}[p_1,\ldots,p_m] \lt \mathrm{trm}[D_0 D_\omega 0]`$;
       - (B-c) $`\mathrm{trm}[D_0 0]`$ is `Dprin 0 BZero`.
     - Hence $`s \in \mathrm{TransRange}`$.
  3. **A standard preimage.** `trans_surjOn` gives a CTPS $`M'`$ with $`\mathrm{Trans}\,M' = s`$. By (a)
     and (b), $`M' = t'_1 \cdots t'_{m'}`$ with the $`t'_j`$ non-increasing in $`R`$.
     - If $`t'_1 = (0,0)`$, then $`M' = (0,0)^{m'}`$, and by F11 $`\mathrm{Trans}\,M' = \mathrm{trm}[D_0 0,\ldots]`$
       (or 0). But $`p_1 \ne D_0 0`$, a contradiction.
     - So F9 applies to $`M'`$ (with F8 and Lemma 2): $`\mathrm{Trans}\,M' = \mathrm{trm}[p'_1,\ldots,p'_{m'}]`$.
  4. **$`M' = M`$.** Equal lists give $`m' = m`$ and $`p'_i = p_i`$. If $`p_i = D_0 0`$, then
     $`t_i = t'_i = (0,0)`$. Otherwise $`\mathrm{Trans}\,t'_i = \mathrm{Trans}\,t_i`$, so $`t'_i = t_i`$
     (`trans_injOn`). Hence $`M = M' \in \mathrm{CTPS}`$. ∎

<em>Alternative proof of (c).</em> Theorem SC (§8b) gives (c) independently. Each root segment
$`t_i`$ satisfies SC by Part 1. Sib on the roots is the hypothesis, and the other SC
conditions are internal to the root segments. So $`M`$ satisfies SC, and $`M \in \mathrm{CTPS}`$ by
Part 2. The proof of SC does not use S1(c).

Evidence: S1(a, b) on all 44,653 CTPS with $`\le 8`$ columns (a numerical check).

---

## 5. Ordinal facts

**Lemma 5 (PROVED from S1, F13).**

- (a) Nodes ordered by $`\lt_p`$ are the non-increasing finite sequences over $`(R, \lt_p)`$, ordered
  lexicographically with a proper prefix smaller. This is Lemma 2.1 of [PROOF](PROOF.md) with S1.
  So $`o(t_1 \cdots t_m) = \omega^{\rho(t_1)} + \cdots + \omega^{\rho(t_m)}`$, with
  $`\rho(t) = \mathrm{otp}\{s \in R : s \lt_p t\}`$, by the CNF theorem and `typein_pairLt`. In particular:
  - $`o(\mathrm{add}(X, Y)) = o(X) + o(Y)`$;
  - $`o(t^n) = o(t) \cdot n`$;
  - $`o(t) \in P`$ (additive principal) for $`t \in R`$.
- (b) If $`\mathrm{Lng}\,X \ge 2`$ and the last column of $`X`$ is not $`(0,0)`$, then $`X[n]`$ strictly
  increases in $`n`$ (F5, and $`B \ne \emptyset`$) and $`o(X) = \sup_n o(X[n])`$ is a limit (F13).

## 6. $`\mathcal{L}N`$ is a node

**Lemma 6 (PROVED).** For $`N \in R`$, $`\mathcal{L}N`$ is standard (or empty).

<em>Proof.</em>

- $`N = 1`$: $`\mathcal{L}N = ()`$.
- $`N`$ epsilon: $`\mathcal{L}N = (N)`$.
- Otherwise $`\mathcal{L}N = \mathrm{addall}((0,H), \mathrm{Lo}_1, \ldots, \mathrm{Lo}_r)`$:
  - $`(0,H)`$ is a prefix of $`N`$ (T2), hence in $`R`$ (F3); it is left out if $`H = \emptyset`$;
  - each $`\mathrm{Lo}_i = \mathrm{sh}(C)`$ for a $`y = 0`$ child $`C`$, hence in $`R`$ (Lemma 4);
  - addall of $`R`$-terms is non-increasing, hence standard by S1(c). ∎

Evidence: all 33,734 roots with $`\le 8`$ columns (a numerical check).

---

## 7. Lemma R

**Lemma R (PROVED).** For all $`N \in R`$: $`o(N) = \omega^{o(\mathcal{L}N)}`$. In particular:

- $`o(N) \in E`$ (epsilon numbers) for epsilon $`N`$;
- by Prop 4.1 of [PROOF](PROOF.md) (with Lemma 6), $`\mathcal{L} : R \to \text{nodes}`$ is an order
  isomorphism.

<em>Proof.</em> Induction on $`N`$ along $`\lt_p`$ (a well-order, `isWellOrder_ctpsLt`).

- **$`N = (0,0)`$.** $`o(N) = 1 = \omega^0`$, and $`o(()) = 0`$.
- Otherwise let $`N = (0, (C_1..C_k))`$ with last column $`\ell`$, $`x_\ell \ge 1`$. By F13,
  $`o(N) = \sup_n (o(N[n]) + 1)`$, and $`N[n] \lt_p N`$ (F4).

**Case A: $`N`$ non-epsilon and $`C_k = (1,0)`$ is a leaf.**

- $`i_1 = 0`$ and $`j_0`$ = the root, so $`N[n] = (\mathrm{Pred}\,N)^n`$.
- $`\mathrm{Pred}\,N \in R`$ (F3). By the IH, $`o(\mathrm{Pred}\,N) = \omega^\beta`$ with
  $`\beta = o(\mathcal{L}\,\mathrm{Pred}\,N)`$.
- $`\mathcal{L}N = \mathrm{add}(\mathcal{L}(\mathrm{Pred}\,N), (1))`$. Check: if $`\mathrm{Pred}\,N`$ is
  epsilon, $`\mathcal{L}(\mathrm{Pred}\,N) = ((0,H))`$; if it is non-epsilon, it is the same addall
  without the last 1; if $`\mathrm{Pred}\,N = 1`$, it is $`()`$.
- Lemma 5(a) gives $`o(N[n]) = \omega^\beta \cdot n`$ and $`o(\mathcal{L}N) = \beta + 1`$.
- So $`o(N) = \sup_n (\omega^\beta \cdot n + 1) = \omega^{\beta+1}`$.

**Case B: $`N`$ non-epsilon and $`C_k = \mathrm{Lo}_r`$ is not a leaf.**

- Put $`Q = \mathrm{sh}(C_k) \in R`$ (Lemma 4).
- Lemma 3 with $`c`$ = the start of $`C_k`$ gives
  $`N[n] = (0, H, \mathrm{Lo}_1..\mathrm{Lo}_{r-1}, R_1..R_s)`$, where $`R_1 \cdots R_s`$ are the roots
  of $`Q[n]`$. They have $`y = 0`$, so $`N[n] \in R`$ is non-epsilon.
- With $`P := \mathrm{addall}((0,H), \mathrm{Lo}_1..\mathrm{Lo}_{r-1})`$ we get
  $`\mathcal{L}N = \mathrm{add}(P, (Q)) =: X = P' \mathbin{+\!\!+} (Q)`$, where $`P'`$ is the part of $`P`$
  that is $`\ge Q`$.
- $`\mathcal{L}(N[n]) = \mathrm{add}(P, Q[n]) = P'' \mathbin{+\!\!+} Q[n]`$, where $`P''`$ is the part of
  $`P`$ that is $`\ge R_1`$.
- $`X[n] = P' \mathbin{+\!\!+} Q[n]`$ (F7 `P_fseq_2`).
- Since $`R_1 \le_p Q[n] \lt_p Q`$, $`P'`$ is a prefix of $`P''`$. Comparing root sequences gives the
  sandwich

```math
X[n] \le_p \mathcal{L}(N[n]) \lt_p X.
```

- By the IH, $`o(N[n]) = \omega^{o(\mathcal{L}\,N[n])}`$. By Lemma 5(b), $`\sup_n o(X[n]) = o(X)`$ is a
  limit that is not attained. By continuity of $`\xi \mapsto \omega^\xi`$, $`o(N) = \omega^{o(X)}`$.

**Case C1: $`N`$ epsilon and $`C_k = (1,1)`$ is a leaf.**

- $`i_1 = 1`$, $`j_0`$ = the root, $`d_0 = 1`$, and $`B = a := \mathrm{anchor}(N)`$, or $`a = (0,0)`$ if
  $`k = 1`$.
- $`N[n] = T_n`$, where $`T_1 = a`$ and $`T_{m+1} = (0, (C_1..C_{k-1}, T_m))`$.
- By T3, $`(0, H(T_{m+1})) = a`$. So $`\mathcal{L}T_{m+1} = \mathrm{add}((a), (T_m))`$, or $`(T_m)`$ if
  $`k = 1`$.
- By the IH:
  - $`\alpha := o(a) = \omega^\alpha`$ ($`a`$ is epsilon), or $`\alpha := 0`$ if $`k = 1`$;
  - $`t_{m+1} := o(T_{m+1}) = \omega^{\alpha + t_m}`$.
- The $`t_m`$ strictly increase (F5), so $`\tau := \sup t_m = \omega^{\alpha+\tau} = \omega^\tau`$, since
  $`\alpha \lt \tau \in P`$.
- So $`o(N) = \tau \in E`$, that is $`o(N) = \omega^{o(N)} = \omega^{o(\mathcal{L}N)}`$.

**Case C2: $`N`$ epsilon and $`C_k`$ is not a leaf.**

- Then $`N[n] \in R`$ is epsilon, because its root's last child still starts with $`C_k`$'s first
  column $`(1,1)`$. Check each case:
  - $`i_1 = 0`$: $`j_0 \in C_k`$. If $`j_0 = \mathrm{start}(C_k)`$, the copies are new root children
    with $`y = 1`$.
  - $`i_1 = 1`$, $`j_0 \ge \mathrm{start}(C_k)`$: the copies attach inside $`C_k`$.
  - $`i_1 = 1`$, $`j_0`$ = the root (possible only if $`y_\ell = 1`$): $`d_0 = x_\ell \ge 2`$, and the
    copies attach below $`p(\ell) \in C_k`$.
- By the IH, the $`o(N[n])`$ are epsilon numbers, and they strictly increase (F5). So
  $`o(N) = \sup o(N[n]) \in E`$. ∎

Evidence (numerical checks on all roots with $`\le 8`$ columns, $`n = 1..3`$):

- the case shapes: A 16,086, B 8,751, C1 11,766 (+15,688 shape checks), C2 64,596;
- the sandwich of Case B;
- $`\mathcal{L}`$ strictly increasing on the 33,734 sorted roots;
- 0 failures.

---

## 8. Lemma 2.4 and T

**2.4(i) anchor (PROVED).** $`\mathrm{anchor}(N)`$ is a prefix of $`N`$, since $`C_k`$'s block is the
suffix. So it is in $`R`$ by F3.

**2.4(ii) lh, $`N = 1`$ or non-epsilon (PROVED).**

- $`\mathrm{lh}(N) = \mathrm{add}((N), \lambda(N))`$, with $`\lambda(N) = \mathcal{L}(\mathrm{sh}\,C_k)`$.
- $`\mathrm{sh}\,C_k \in R`$ by Lemma 4, and $`\mathcal{L}(\mathrm{sh}\,C_k)`$ is a node by Lemma 6.
- add gives a non-increasing $`R`$-sequence, which is standard by S1(c). (By R,
  $`o(\lambda(N)_1) \lt o(N)`$, so nothing is absorbed: $`\mathrm{lh}(N) = (N) \mathbin{+\!\!+} \lambda(N)`$.)

**2.4(iii) lh, $`N`$ epsilon (PROVED from Lemma C and T).**

- $`(N, N)`$ is standard (S1(c)).
- A non-jump step is $`\mathrm{add}(S, (Y))`$ with $`Y \le S_1`$. This is standard if $`Y \in R`$ (S1(c)).
- A jump is $`\mathrm{lh}(Y)`$. By induction on the finite call tree (T below), it is standard if the
  inputs of that call are in $`R`$.
- So 2.4 follows from: **every fold input is in $`R`$**. The inputs are:
  - $`\mathrm{Coll}_A(E)`$ with $`y(E) = 0`$: this is $`\mathrm{sh}(E) \in R`$ by Lemma 4;
  - $`\mathrm{Coll}_A(W\vert_i)`$ (T4) and $`\mathrm{Coll}_A(E)`$ with $`y(E) = 1`$: both are covered by
    Lemma C (§8c), with $`s = W`$ truncated to $`i`$ children, or $`s = E`$.

**T (PROVED).** For every term $`N`$, standard or not, the recursion $`\mathrm{lh}(N)`$ terminates. The
nesting depth of lh-calls is at most the number of nodes on a longest root-to-leaf path
of the tree $`W_N`$, where $`W_N`$ is the last child of $`N`$.

<em>Proof.</em>

- **Facts about Coll.** Let $`\Phi = \mathrm{Coll}_{A_m} \circ \cdots \circ \mathrm{Coll}_{A_1}`$, a
  composite with $`m \ge 0`$.
  - (i) If $`y(\Phi(c)) \ge 1`$, then each Coll was applied to a term with $`y \ge 2`$. The children
    of $`\Phi(c)`$ form a subsequence of $`(\Phi(c'))_{c' \text{ child of } c}`$, because addall keeps a
    subsequence.
  - (ii) If $`y(\Phi(c)) = 0`$, then either:
    - $`\Phi(c) = c`$ ($`y(c) = 0`$), or
    - $`\Phi(c)`$ is a <em>blob</em> $`(0, A_j + \mathrm{Coll}_{A_j}(\text{children of } \Phi_{\lt j}(c)))`$,
      with $`j = y(c)`$. Its last child is $`\mathrm{Coll}_{A_j}(\Phi_{\lt j}(c''))`$ for the last child
      $`c''`$ of $`c`$. If $`c`$ has no children, the blob is $`(0, A_j)`$.
- **Invariant.** Every call $`\mathrm{lh}(Z)`$ with $`Z`$ epsilon in the call tree of $`\mathrm{lh}(N)`$
  carries a pair $`(\Phi_Z, d_Z)`$ such that:
  - $`d_Z`$ is a subterm of $`W_N`$;
  - $`W_Z = \Phi_Z(d_Z)`$;
  - each $`A_j`$ in $`\Phi_Z`$ is the child tuple of an ancestor call's argument $`Z_j`$.

  Start: $`(\mathrm{id}, W_N)`$.
- **Monotonicity.** Along the fold, $`S_1`$ never decreases and $`S_1 \ge Z`$:
  - a non-jump keeps $`S_1`$;
  - a jump sets $`S := \mathrm{lh}(Y)`$, whose first term is $`\ge Y \gt S_1`$.

  So the arguments strictly increase along nested calls, and every ancestor argument $`Z_j`$
  is $`\le S_1`$. **Hence a blob $`(0, A_j) = Z_j`$ is never a jump.**
- **Jumps inside $`\mathrm{lh}(Z)`$** ($`C`$ = child of $`W_Z = \Phi_Z(c')`$, $`c'`$ a child of $`d_Z`$):
  - $`Y_i`$: $`W_Y = \mathrm{Coll}_{A_Z}(D_i) = \mathrm{Coll}_{A_Z}(\Phi_Z(c'))`$, so $`d_Y = c'`$.
  - $`\mathrm{Coll}(E)`$, $`y(E) = 1`$:
    $`W_Y = \mathrm{Coll}_{A_Z}(\text{last child of } E) = \mathrm{Coll}_{A_Z}(\Phi_Z(c''))`$ by (i),
    with $`c''`$ a child of $`c'`$. (If $`E`$ has no children, then $`Y = Z`$, which is no jump.)
  - $`E`$ with $`y = 0`$, $`E = c'`$: $`W_Y`$ = the last child of $`c'`$, with $`\Phi_Y = \mathrm{id}`$.
  - $`E`$ a blob from level $`j`$: $`W_Y = \mathrm{Coll}_{A_j}(\Phi_{\lt j}(c''))`$ by (ii), with $`c''`$
    the last child of $`c'`$. (The empty blob is no jump, by monotonicity.)
  - In every case $`d_Y`$ is a **proper** subterm of $`d_Z`$.
- Non-epsilon and trivial calls do not recurse.
- So along any chain of nested calls, the $`d_Z`$ form a strictly descending chain of subterms
  of $`W_N`$. Its length is at most the number of nodes on a root-to-leaf path of $`W_N`$. Each
  call makes at most $`\lvert \mathrm{children}(W_Z) \rvert`$ direct calls, and Coll and add are
  structural. So the call tree is finite (König). ∎

Evidence (a numerical check): on all 25,454 epsilon roots with $`\le 8`$ columns, the depth
is $`\lt \mathrm{height}(W)`$ (the maximum depth seen is 6), and the instrumented lh equals `lh`
of [phi.py](../por/phi.py).

**Remark.** The "obvious measure" of [PROOF](PROOF.md) A6 fails because it measures $`W_Z`$. The
blobs re-insert all of $`A_j`$, so $`W_Z`$ can be larger than $`W_N`$. The measure must follow the
<em>provenance</em> $`d_Z`$ in the original tree. No recursion ever enters the $`A_j`$-part of a blob,
because that would be the empty-blob case, which monotonicity excludes.

---

## 8b. A criterion for standardness

**Notation.**

- A matrix $`M`$ is read as a forest by row-0 parents. $`T(u)`$ is the term (block) of column $`u`$.
- Terms are compared as blocks normalized to $`x = 0`$, lexicographically, with a proper
  prefix smaller (Lemma 2.1 of [PROOF](PROOF.md)).
- A non-root node $`u`$ is **descending** if $`y_u \le y_{p(u)}`$.
- For a descending $`u`$, $`v(u)`$ is the nearest proper ancestor with $`y \le y_u`$. By (A) below, the
  $`y`$-value falls by at most 1 per step upward, so $`y_{v(u)} = y_u`$.

**Theorem SC (PROVED).** A matrix $`M`$ is CTPS iff all of the following hold:

- **(R0)** $`M_0 = (0,0)`$, and every root has $`y = 0`$.
- **(I0)** $`x_{j+1} \le x_j + 1`$.
- **(A)** $`y_c \le y_{p(c)} + 1`$ for every non-root $`c`$.
- **(Sib)** Siblings (the roots count as siblings) have non-increasing terms.
- **(G\*)** $`T(u) \lt_p T(v(u))`$ for every descending node $`u`$.

Remarks:

- (I3) of Lemma 1 is the root-$`y`$ part of Sib.
- (G\*) is the pair-sequence form of Buchholz's condition $`G_\nu(a) \lt a`$.
- SC gives S1 and Lemma 4 again: the conditions for a subtree of a $`y = 0`$ column, or
  for a root segment, involve only that subtree.

**Evidence.**

- An exhaustive check: SC selects exactly the 44,653 standard matrices among all candidates
  with $`\le 8`$ columns. There are no false positives and no false negatives.
- A random check at length 9–12: 65,699 SC matrices were all standard, and 76,286
  one-column non-SC extensions were all non-standard.
- Weaker candidates fail. The candidate that uses only I0–I3 and Sib accepts $`(0,0)(1,0)(2,1)`$,
  which is non-standard since $`\omega^{\varepsilon_0} = \varepsilon_0`$. Three intermediate
  candidates were also tried.

### Part 1: CTPS $`\Rightarrow`$ SC

R0, I0 and (A) are Lemma 1.

**Lemma 7 (Sib; PROVED).** Induction along F1. Base $`\mathrm{diag}(0,v)`$: each node has one child.
Step $`M \mapsto M[n]`$:

1. **Children lists that lose their last child $`\ell`$, or whose last child is an ancestor of $`\ell`$.**
   The new term of an ancestor $`a`$ of $`\ell`$ agrees with $`T(a)`$ up to $`\ell`$'s relative position.
   There $`T(a)`$ has $`\ell`$, and $`T'(a)`$ has the first column of $`B_1`$, which is smaller:
   $`(x_\ell, y_{j_0})`$ with $`y_{j_0} \lt y_\ell`$ when $`i_1 = 1`$, or $`(x_{j_0}, y_{j_0})`$ with
   $`x_{j_0} \lt x_\ell`$ when $`i_1 = 0`$. It may also end there. So $`T'(a) \lt T(a) \le`$ (previous
   sibling).
2. **$`i_1 = 1`$.** The children of $`\mathrm{copy}_{k-1}(p(\ell))`$ are the old children of $`p(\ell)`$
   before $`\ell`$, then $`\mathrm{copy}_k(j_0)`$. Its root $`y`$ is $`y_{j_0} \lt y_\ell \le`$ (previous
   sibling) by (I3) in $`M`$.
3. **$`i_1 = 0`$.** The children of $`p(j_0)`$ end with $`j_0`$, whose term is now $`T(j_0)`$ without
   $`\ell`$, followed by $`n - 1`$ equal copies of it.

**3′. $`i_1 = 1`$, copies of ancestors.** Let $`a \in [j_0, \ell)`$ be an ancestor of $`\ell`$ other than
$`p(\ell)`$, let $`a'`$ be its child on the path, and take $`1 \le k \le n-1`$. The children list of
$`\mathrm{copy}_k(a)`$ consists of copies of $`a`$'s children, ending with $`\mathrm{copy}_k(a')`$.

- Its term $`T'(\mathrm{copy}_k(a'))`$ is, after normalization, $`T_{M[n-k]}(a')`$.
- Item 1 applied to $`M[n-k]`$: this term agrees with $`T(a')`$ before $`\ell`$'s relative position,
  and there it is smaller or ends. So $`T'(\mathrm{copy}_k(a')) \lt T(a') \le`$ the previous sibling.
- For $`a = p(\ell)`$, item 2 applies instead.

4. **Copies of non-ancestors** are unchanged.
5. **Pred** shortens only last children.
6. **Roots:** S1(b). ∎

**Lemma 8 (G\*; PROVED).** Induction along F1. Base: $`\mathrm{diag}(0,v)`$ has no descending node.

- **Useful facts.**
  - An ancestor $`a`$ of $`\ell`$ gets the term $`M[n][a..\mathrm{end}]`$. The one exception is $`j_0`$
    when $`i_1 = 0`$, which gets $`T(j_0)`$ without $`\ell`$.
  - $`T'(a)`$ agrees with $`T(a)`$ before $`\ell`$'s relative position and is smaller there.
  - A non-ancestor $`u`$ of $`\ell`$ keeps its term. This is the argument of Lemma 4, case 3.
    - If the block of $`u`$ ends before $`\ell - 1`$, nothing changes.
    - If it ends at $`\ell - 1`$, the column now at position $`\ell`$ is $`\mathrm{copy}_1(j_0)`$. Its $`x`$
      is $`x_\ell \le x_u`$ when $`i_1 = 1`$ ($`\ell`$ is not a descendant of $`u`$), or
      $`x_{j_0} \lt x_u`$ when $`i_1 = 0`$. So the block still ends there.
  - For $`w \in [j_0, \ell)`$, $`T'(\mathrm{copy}_k(w))`$ is, after normalization, the term of $`w`$ in
    $`M[n-k]`$.
- **(1) $`u`$ an original column ($`u \lt \ell`$).** Its ancestors, and hence $`v(u)`$, are the same as
  in $`M`$. By IH, $`T(u) \lt T(v)`$.
  - If $`u`$ is not an ancestor of $`\ell`$, its block ends before $`\ell`$. The comparison is decided at
    a relative position $`\lt \ell - v`$, where $`T'(v) = T(v)`$.
  - If $`u`$ and $`v`$ are both ancestors of $`\ell`$: if the comparison is decided before $`\ell`$, it is
    unchanged. If it is decided at $`\ell`$ or by the prefix relation, the column that
    replaces $`\ell`$ in $`T'(u)`$ is smaller than $`\ell`$.
  - If $`u = j_0`$ with $`i_1 = 0`$: $`T'(j_0)`$ is $`T(j_0)`$ with the last column removed, which is a
    prefix of $`T'(v)`$ or smaller.
- **(2) $`u = \mathrm{copy}_k(j)`$, $`k \ge 1`$.**
  - If $`v(j) \in [j_0, j)`$, then $`v(u) = \mathrm{copy}_k(v(j))`$. Both terms are, after
    normalization, terms in $`M[n-k]`$, so case (1) for $`M[n-k]`$ applies.
  - If $`v(j) \lt j_0`$, the ancestors inside the copies all have $`y \gt y_j`$, so
    $`v(u) = v(j) \in G`$. Then
    $`T'(\mathrm{copy}_k(j)) = T_{M[n-k]}(j) \lt T_{M[n-k]}(v(j)) \le T_{M[n]}(v(j))`$. The first
    step is case (1) for $`M[n-k]`$. The second holds because $`M[n-k]`$ is a prefix of $`M[n]`$
    (`oper_prefix`) and $`v(j)`$'s block reaches the end.
  - If $`j = j_0`$ and $`i_1 = 1`$: $`v(u) = \mathrm{copy}_{k-1}(j_0)`$, and $`T'(u)`$ is the $`j_0`$-suffix
    of $`M[n-k]`$, which is a proper prefix of that of $`M[n-k+1]`$.
  - If $`j = j_0`$ and $`i_1 = 0`$: $`v(u) = v(j_0)`$, and $`T'(u) = T(j_0)`$ without $`\ell`$. This is
    handled as in (1).
- **Pred:** removing the last column keeps every comparison. A decision at the last
  column turns into a proper prefix. ∎

### Part 2: SC $`\Rightarrow`$ CTPS

**Lemma 9 ($`y`$-descent; PROVED).** Suppose $`P \mathbin{+\!\!+} (x_q+1, y)`$ is CTPS, where the new
column $`c`$ has parent $`q`$ and $`1 \le y \le y_q + 1`$. Then $`P \mathbin{+\!\!+} (x_q+1, y-1)`$ is CTPS.

<em>Proof.</em>

- By (A), walking up from $`q`$ the $`y`$-value falls by at most 1 per step. So the row-1
  parent $`j_0`$ of $`c`$ has $`y_{j_0} = y - 1`$.
- $`(P \mathbin{+\!\!+} c)[2] = P \mathbin{+\!\!+} \mathrm{copy}_1([j_0, c))`$, whose first new column is
  $`(x_{j_0} + d_0, y_{j_0}) = (x_q+1, y-1)`$.
- Take the prefix and use F3. ∎

**SC is prefix-closed.** Removing the last column preserves (A), Sib (only last
children shrink) and G\* (the Pred argument of Lemma 8 uses only the tree structure).

**Proof of SC $`\Rightarrow`$ CTPS.** Suppose $`M`$ satisfies SC but is not CTPS.

1. **Reduce to one column.** Replace $`M`$ by $`Q \mathbin{+\!\!+} c`$, where $`Q`$ is its longest CTPS
   prefix. By prefix-closure it still satisfies SC and is still not CTPS.
2. **The least CTPS matrix above $`M`$.** First, $`M \lt_p \mathrm{diag}(0, \lvert M \rvert)`$.
   - $`x_j \le j`$ by I0 and $`M_0 = (0,0)`$.
   - $`y_j \le x_j`$ by induction on depth: R0 gives $`y = 0`$ at the roots, and (A) with T0
     ($`x`$ = depth) gives $`y_c \le y_{p(c)} + 1 \le x_{p(c)} + 1 = x_c`$.
   - So at the first $`j`$ with $`M_j \ne (j,j)`$, $`M_j \lt_p (j,j)`$. If there is no such $`j`$, then
     $`M = \mathrm{diag}(0, \lvert M \rvert - 1)`$, which is CTPS and excluded.

   So $`X :=`$ the least CTPS with $`X \gt_p M`$ exists (`isWellOrder_ctpsLt`).
   - If $`X`$'s last column is $`(0,0)`$, then $`\mathrm{Pred}\,X \lt M \lt \mathrm{Pred}\,X \mathbin{+\!\!+} (0,0)`$,
     which is impossible. So $`X`$ is a limit.
   - Every $`X[n]`$ is CTPS and $`\lt X`$, hence $`\lt M`$ by minimality.
3. **The limit word $`\omega`$.** Let $`\omega = G B_0 B_1 B_2 \cdots = \lim X[n]`$.
   - $`M`$ is not a prefix of $`\omega`$, since it would then be a prefix of some $`X[n]`$ (F3).
   - Let $`p`$ be the first position with $`M[p] \ne \omega[p]`$. Then $`M[p] \gt \omega[p]`$.
   - $`p \ge j_1`$, otherwise $`M \gt X`$.
   - If $`p \lt \lvert Q \rvert`$, then $`Q \gt X[n]`$ for all large $`n`$, while $`Q \lt X`$. This
     contradicts `exists_le_oper` together with `oper_prefix`.
   - So $`p = \lvert Q \rvert`$: $`Q`$ is a prefix of $`\omega`$, and $`c \gt w := \omega[\lvert Q \rvert]`$.
4. **$`\lvert Q \rvert = j_1`$.** Then $`c \lt \ell`$, because $`M \lt X`$ and $`M \ne X`$. So $`w \lt c \lt \ell`$.
   - $`i_1 = 0`$: $`c = (x_{j_0}, y')`$ with $`y' \gt y_{j_0}`$. This is a later sibling of $`j_0`$ with a
     larger root $`y`$, which violates Sib (or R0 if $`j_0`$ is a root).
   - $`i_1 = 1`$: $`c = (x_\ell, y')`$ with $`y_{j_0} \lt y' \lt y_\ell`$. Then $`M`$ is CTPS by Lemma 9
     applied to $`X`$, repeatedly.
5. **$`\lvert Q \rvert \gt j_1`$.** Then $`Q = G B_0 \cdots B_{k-1} (B_k{\restriction}t)`$ with $`k \ge 1`$.
   Let $`r_k = \mathrm{copy}_k(j_0)`$.
   - $`i_1 = 0`$ (the copies are siblings). The term of the current copy agrees with the
     previous copy $`\beta = T(j_0)`$ without $`\ell`$ up to position $`t`$, and then has $`c \gt w`$. So
     it exceeds $`\beta`$, which violates Sib. If $`t = 0`$, $`c`$ either extends $`r_{k-1}`$ beyond
     $`\beta`$ (again Sib) or is a new sibling with larger $`y`$ (Sib).
   - $`i_1 = 1`$ (the copies are nested, and $`v(r_k) = r_{k-1}`$). $`T(r_k)`$ and $`T(r_{k-1})`$ agree
     up to position $`t`$ and then compare $`c`$ against $`w`$, so $`T(r_k) \gt T(r_{k-1})`$, which
     violates G\*. If $`t = 0`$, the same comparison between $`r_{k-1}`$ and $`r_{k-2}`$ at relative
     position $`\lvert B \rvert`$, namely $`(\ge d_0, \cdot)`$ against $`(d_0, y_{j_0})`$, violates G\*.
6. Every case gives a contradiction. ∎

---

## 8c. Lemma C

**Lemma C (PROVED).** Let $`N = (0, A) \in R`$ (epsilon or not). Let $`s`$ be any $`y = 1`$ column of
$`N`$, and $`0 \le i \le \lvert \mathrm{ch}(s) \rvert`$. Then

```math
Y := (0, A \oplus \mathrm{Coll}_A(\mathrm{ch}(s)[{:}i])) \in R,
```

where $`A \oplus \pi := \mathrm{addall}(A \mathbin{+\!\!+} \pi)`$. In particular the fold inputs
$`\mathrm{Coll}_A(W\vert_i)`$ and $`\mathrm{Coll}_A(E)`$ ($`y(E) = 1`$) are standard.

**The region.** The region is the subtree of $`s`$ restricted to its first $`i`$ children, cut
at $`y = 0`$ nodes. In the region every node except the cut $`y = 0`$ nodes has $`y \ge 1`$. Coll
acts as follows:

- it lowers $`y \ge 2`$ nodes by 1;
- it turns a $`y = 1`$ node $`b`$ into the **blob** $`(0, A \oplus \mathrm{Coll}(\mathrm{ch}\,b))`$;
- it keeps a $`y = 0`$ node with its whole original subtree (a **constant**).

**Two facts from SC($`N`$) (Theorem SC, Part 1).**

- (K1) Every constant $`u`$ satisfies $`T(u) \lt N`$. Follow G\* along the chain of $`y = 0`$
  ancestors up to the root.
- (K2) Every blob is $`\ge N`$, and $`T(Y) \ge N`$. Indeed $`A \oplus \pi \ge A`$ for every $`\pi`$.
  - Either nothing of $`A`$ is dropped, and $`A \oplus \pi`$ extends $`A`$.
  - Or only the first $`r \lt \lvert A \rvert`$ elements of $`A`$ survive. Then the entry of $`A \oplus \pi`$
    at position $`r`$ is $`\max \pi`$, and $`\max \pi \gt A[r]`$, since $`A[r]`$ was dropped by some
    element of $`\pi`$.
  - (The earlier justification "the first dropped element is $`\lt \pi_1`$" is correct only for
    non-increasing $`\pi`$. That is the case inside Lemma C, where $`\pi = \mathrm{Coll}\,\sigma`$, but
    the general claim needs the argument above.)

**Lemma 10 (Coll is strictly monotone; PROVED).** For region terms $`a \lt_p b`$ we have
$`\mathrm{Coll}(a) \lt_p \mathrm{Coll}(b)`$. For non-increasing region sequences
$`\sigma \lt_{\mathrm{lex}} \tau`$ we have
$`A \oplus \mathrm{Coll}\,\sigma \lt_{\mathrm{lex}} A \oplus \mathrm{Coll}\,\tau`$.

<em>Proof.</em> Induction on height.

- **Different $`y`$:** the images sit on different levels, which are ordered:
  constants ($`y = 0`$, $`\lt N`$ by K1) $`\lt`$ blobs ($`y = 0`$, $`\ge N`$ by K2) $`\lt`$ lowered nodes
  ($`y \ge 1`$, in the order of $`y`$).
- **Same $`y`$:**
  - $`y = 0`$: Coll is the identity;
  - $`y \ge 2`$: compare $`\mathrm{Coll}(\mathrm{ch}\,a)`$ with $`\mathrm{Coll}(\mathrm{ch}\,b)`$;
  - $`y = 1`$: compare $`A \oplus \mathrm{Coll}(\mathrm{ch}\,a)`$ with $`A \oplus \mathrm{Coll}(\mathrm{ch}\,b)`$.
- **Sequences.** $`\mathrm{Coll}\,\sigma`$ is non-increasing (elementwise monotone, $`\sigma`$
  non-increasing by Sib), so
  $`A \oplus \mathrm{Coll}\,\sigma = A{\restriction}r(\mathrm{Coll}\,\sigma_1) \mathbin{+\!\!+} \mathrm{Coll}\,\sigma`$,
  where $`r(x) = \#\{A\text{-elements} \ge x\}`$.
  - If $`\sigma`$ is a proper prefix of $`\tau`$, the result is a proper prefix (or, for
    $`\sigma = \emptyset`$, K2 gives strictness).
  - If $`\sigma`$ and $`\tau`$ first differ at $`p \ge 1`$, $`r`$ is the same, and the results differ at
    $`r + p`$.
  - If $`p = 0`$: when $`r(\mathrm{Coll}\,\sigma_1) = r(\mathrm{Coll}\,\tau_1)`$, compare
    $`\mathrm{Coll}\,\sigma_1 \lt \mathrm{Coll}\,\tau_1`$. Otherwise $`r_\sigma \gt r_\tau`$, and
    $`A[r_\tau] \lt \mathrm{Coll}\,\tau_1`$. ∎

**Proof that $`Y`$ satisfies SC.**

- **R0, I0.** Clear.
- **(A).** Children of the root or of a blob: $`A`$ ($`y \le 1`$, by (A) in $`N`$) and Coll images
  ($`y \le 1`$, since children of $`y = 1`$ nodes have $`y \le 2`$). A lowered node $`\mathrm{Coll}(b)`$
  has children with $`y \le y_b = (y_b - 1) + 1`$. Original parts are unchanged.
- **Sib.** The children of the root or a blob are $`A \oplus \mathrm{Coll}\,\sigma`$, which addall
  makes non-increasing. The children of a lowered node are $`\mathrm{Coll}(\mathrm{ch}\,b)`$,
  non-increasing by Lemma 10. Original parts are unchanged.
- **G\*.**
  - **Nodes inside a copy of an $`A`$-element** (under the root or a blob $`\beta`$): if $`v_N(u)`$
    lies in the copy, nothing changed. If $`v_N(u)`$ = $`N`$'s root, then $`v(u) = \beta`$ and
    $`T(u) \lt N \le T(\beta)`$ by G\* for $`N`$ and K2.
  - **Lowered $`u = \mathrm{Coll}(b)`$, descending.** $`v(u) = \mathrm{Coll}(v_N(b))`$, because between
    $`b`$ and $`s`$ all nodes have $`y \ge 1`$, and $`v_N(b)`$ has $`y = y_b \ge 2`$. Lemma 10 applied to
    $`T(b) \lt T(v_N(b))`$ gives the claim.
  - **Blob $`u = \mathrm{Coll}(b)`$, with $`y_b = 1`$ and $`b \ne s`$.** $`v(u)`$ is the blob of the
    nearest $`y = 1`$ proper ancestor $`b'`$, or the root of $`Y`$ if $`b' = s`$. G\* for $`N`$ at $`b`$
    gives $`\mathrm{ch}(b) \lt_{\mathrm{lex}} \mathrm{ch}(b')`$. For $`b' = s`$ we even have
    $`\mathrm{ch}(b) \lt_{\mathrm{lex}} \mathrm{ch}(s)[{:}i]`$: otherwise $`\mathrm{ch}(b)`$ would begin
    with $`B_1..B_i`$, so $`T(b)`$ would properly contain $`T(B_j)`$ for the $`B_j`$ above it, which is
    impossible by size. Lemma 10 finishes.
  - **Constants $`u`$.** $`v(u)`$ is the enclosing blob or the root, and $`T(u) \lt N \le T(v(u))`$ by
    K1 and K2.
  - **Nodes inside a constant** have their $`v`$ inside it. ∎

Hence $`Y \in \mathrm{CTPS}`$ by Theorem SC. $`Y`$ is one-root, so $`Y \in R`$. ∎

**Consequence.** Lemma 2.4 is now fully PROVED.

- anchor is standard (§8, (i)).
- $`\mathrm{lh}(N)`$ is standard for non-epsilon $`N`$ (§8, (ii)).
- For epsilon $`N`$, $`\mathrm{lh}(N)`$ is standard: every fold input is in $`R`$, by Lemma 4 for
  $`y(E) = 0`$ and by Lemma C otherwise, and the induction runs over the finite call tree (T).

Evidence: 138,585 Coll-terms, all standard. Lemma 10 was checked on 270,147 region
child-sequences, with no internal absorption and no order violation.

---

## 9. Corrections to PROOF.md

The items below refer to sections and lemmas of [PROOF](PROOF.md).

1. **S1(a) shift caveat.** It is vacuous for CTPS: roots are $`(0,0)`$ (T1), and $`P`$ gives
   the root segments literally (Lemma 2).
2. **Lemma 4.2, step 2: "$`C_k \in R`$ by S1(a)" is the wrong citation.** $`C_k`$ is a <em>child</em>,
   not a root segment. $`\mathrm{sh}(C_k) \in R`$ is Lemma 4 (Sh), which uses $`y(C_k) = 0`$. The same
   applies to $`\lambda(N)`$ in lh and to the Lo-terms of log.
3. **§4.5 "By standardness $`y(W) = 1`$".** This is T3/T4 (Lemma 1). Moreover <em>all</em> root
   children of an epsilon $`N`$ have $`y = 1`$, and the $`D`$'s ($`y = 2`$) precede the $`E`$'s. So the
   fold inputs are $`\mathrm{Coll}_A(W\vert_i)`$ and $`\mathrm{Coll}_A(E_j)`$.
4. **Lemma 6.4, step 2** ("$`\log N = \mathcal{L}(a) + C_k`$"). It is correct because of T2: H precedes
   Lo, so $`(0, H)`$ is a prefix and $`\mathrm{anchor}(N)`$ is $`(0,H)`$ or has $`\log(\mathrm{anchor})`$
   as its first part.
5. **Prop 4.1 needs Lemma 6** ($`\mathcal{L}N`$ is a node) before $`\mathcal{L}`$ can be called a map
   $`R \to \text{nodes}`$. Lemma R as proved here gives Prop 4.1's hypothesis directly.
6. **Lemma 2.4 and T.** Lemma 2.4 for epsilon $`N`$ is an induction on the lh call tree, so
   it uses T. T is proved without standardness (§8).
7. **Lemma 2.4 is no longer OPEN.** Theorem SC and Lemma C (§8b, §8c) prove it.
8. **A new tool: Theorem SC.** It turns standardness into a local tree condition
   (R0, I0, (A), Sib, G\*). Any future claim of the form "this constructed matrix is
   standard" can be checked against SC instead of searching for an expansion path.

## 10. For a Lean formalization

- **Direct from existing Lean** ([pss-proof](https://github.com/koteitan/pss-proof) +
  [Rank.lean](../Rank.lean)):
  - Lemma 2 (`P_last_multi`, `Pcut_props`, `P_nonmulti_eq`);
  - S1(c) (`Trans_P_equivariance`, `Trans_monoT_principal`, `STPS_RTPS`, `trans_bijOn`,
    `trans_order_iso`, `Trans_Mark_multi_equations`, `isOT_BT`/`descP`);
  - S1(a) (`SkTPS_P_component` + T1).
- **New, elementary; induction over `ctps_iff_leExpPS` with an explicit description of
  `oper`:** Lemma 1 (I0–I3), Lemma 3 (locality), Lemma 4 (Sh), S1(b). The main work is a
  "parents in `oper M n`" lemma: $`\mathrm{copy}_k(j) \mapsto \mathrm{copy}_k(p(j))`$,
  $`\mathrm{copy}_k(j_0) \mapsto \mathrm{copy}_{k-1}(p(j_1))`$ or $`p(j_0)`$. The lemmas of
  [pss-proof](https://github.com/koteitan/pss-proof) on P-fundamental sequences and on the segment
  invariance of fundamental sequences contain much of this.
- **Terms.** A tree view of matrices (term $`\leftrightarrow`$ matrix bijection, shift sh, prefix =
  anchor) with lemmas relating `ltPS` to the term order (Lemma 2.1 of [PROOF](PROOF.md)).
- **Ordinals.**
  - The CNF order-type fact (Lemma 5a): Mathlib has `Ordinal.CNF`; one needs the
    lex/non-increasing-sequence version.
  - $`\mathrm{rank} = \sup(\mathrm{rank}(M[n]) + 1)`$ from `rank_pairL_eq` and `IsWellFounded.rank_eq`.
  - Continuity of $`\xi \mapsto \omega^\xi`$, and "a sup of an increasing sequence of epsilon numbers
    is epsilon".
- **Lemma R:** well-founded induction on `CtpsLt` with the four cases of §7.
- **T:** define lh with fuel = the number of nodes on a longest root-to-leaf path of $`W_N`$, and
  prove, via the provenance invariant, that the fuel suffices (or define lh on the pair (term,
  provenance)).
- **Theorem SC.**
  - Part 1 (CTPS $`\Rightarrow`$ SC) is the same kind of induction as Lemma 1: Sib and G\* need the
    "terms in `oper M n`" facts of §8b (an ancestor's term is the tail of $`M[n]`$; a copy's
    term equals the corresponding term in $`M[n-k]`$).
  - Part 2 (SC $`\Rightarrow`$ CTPS) needs `isWellOrder_ctpsLt` (least CTPS above $`M`$), `oper_prefix`,
    `exists_le_oper`, F3 (prefix closure), and Lemma 9. The limit word $`\omega`$ can be avoided
    by working with $`X[n]`$ for a large enough $`n`$.
- **Lemma C:** Coll on terms, Lemma 10 by induction on height, then the SC check of §8c.
  The "size" step (a term is not a proper subterm of itself) is structural.
- **Nothing in this file is OPEN any more.**

## 11. Numerical checks

The numerical checks were made with scripts that are not published; only
[phi.py](../por/phi.py), [pss.py](../por/pss.py) and [tr.py](../por/tr.py) are in this repository.
The checks were:

- a standardness test: greedy descent from $`\mathrm{diag}(0,d)`$ using F6 (`lePS_iff_leExpPS`) and
  `exists_le_oper`, and enumeration of CTPS with at most $`L`$ columns. It agrees with yaBMS `-s`
  on 1,500 random candidates;
- S1(a, b), T2, Sh; the invariants I2, I3 (and the stronger sibling $`y`$-order);
- Lemma C, generalized;
- Lemma 6, monotonicity of $`\mathcal{L}`$, the case shapes and the sandwich of R;
- the depth bound of T;
- greedy expansion paths (exploration for Lemma C);
- earlier, weaker or intermediate candidate criteria (exploration);
- Theorem SC: the criterion equals CTPS on all matrices with $`\le 8`$ columns (44,653);
- Theorem SC on random matrices of length 9–12 (65,699 accepted + 76,286 rejected, all
  agreeing with the standardness test);
- Lemma 10: 270,147 region child-sequences; Coll never absorbs internally and is monotone on
  siblings (0 failures);
- Mono\*: 62,943 valid terms of levels 0–7 ($`\le 8`$ columns), $`\mathcal{T}_k`$ strictly increasing,
  0 failures;
- [W24] fundamental sequences on $`T^1`$. Cofinality $`\mathcal{T}(M)[n] \le \mathcal{T}(M[k])`$ holds on
  5,970 limit matrices ($`\le 7`$ columns), 0 failures;
- appending a $`y = 0`$ leaf child to the last column is not always standard (it can break Sib).

---

## References

- [B86] W. Buchholz, "A new system of proof-theoretic ordinal functions", Annals of Pure and
  Applied Logic 32 (1986) 195–207. doi:10.1016/0168-0072(86)90052-7.
- [W24] G. Wilken, "Fundamental sequences based on localization", arXiv:2410.15953 (v4).
- [PROOF](PROOF.md) and [TR](TR.md): the companion documents.
- [pss-proof](https://github.com/koteitan/pss-proof): the Lean facts F1–F12 of §1.2.
- This library: [Rank.lean](../Rank.lean) and [Expand.lean](../Expand.lean) (F13).

---

## Review history

An independent referee reviewed §1–§8c of this document: Lemma 1, T0–T4, Lemmas 2–4,
S1 (a), (b), (c), Lemmas 5 and 6, Lemma R, Lemma 2.4, T, Theorem SC with Lemmas 7–9,
Lemma 10 and Lemma C. Mono\* and Lemma TR, listed in the §0 table, are proved in
[TR](TR.md) and were reviewed there. The referee read the cited Lean statements; no Lean
was run. The referee's scale: FATAL (a claim is false), BLOCKING (a needed step is missing
or wrong), MINOR (the claim follows, but a step is terse, mis-cited or omitted).

**Result.** No FATAL or BLOCKING finding. Every lemma in scope follows from the argument
given and the cited facts. There were eight MINOR items; none of them changes a statement.
All eight were repaired in the text:

- **M1 (citation, F13).** `pairL_step_eq_oper` is in [Expand.lean](../Expand.lean), not in
  [Rank.lean](../Rank.lean). §1.2 now says so.
- **M2 (step omitted, Lemma 4).** The Pred case had no argument. It is now written out.
- **M3 (case left implicit, Lemma 7).** For $`i_1 = 1`$ the children lists of the copies of
  ancestors of $`\ell`$ were not covered. Item 3′ covers them.
- **M4 (step omitted, Lemma 8).** "A non-ancestor keeps its term" needed the argument of
  Lemma 4, case 3. It is now given.
- **M5 (unstated fact, Theorem SC Part 2, step 2).** $`M \lt_p \mathrm{diag}(0, \lvert M \rvert)`$
  needs $`y_j \le x_j`$, which is not a condition of SC. It is now proved from R0, (A) and
  T0.
- **M6 (wrong justification, true claim, K2).** "The first dropped element is
  $`\lt \pi_1`$" is false for a general $`\pi`$. K2 now has a proof for every $`\pi`$; the
  old sentence is correct only for non-increasing $`\pi`$, which is the case inside Lemma C.
- **M7 (uncited facts, S1(c)).** Three facts about Buchholz terms were used without
  citation. They are now stated as (B-a), (B-b), (B-c). An alternative proof of S1(c)
  from Theorem SC was added.
- **M8 (wording, T).** "The nesting depth is $`\lt \mathrm{height}(W_N)`$" depends on the
  convention for height. T now bounds the depth by the number of nodes on a longest
  root-to-leaf path of $`W_N`$. Finiteness, which is all that Lemma 2.4 needs, was not
  affected.

**The referee's counterexample search** found no failure:

- Theorem SC against standardness, exhaustively: all one-column extensions of all
  standard matrices of length 8 (412,718 matrices of 9 columns) and of length 9
  (2,889,191 matrices of 10 columns). 0 disagreements.
- Random walks of 12–16 columns that test every extension at each step: 291,386 and
  640,457 tests. 0 failures.
- Prefixes (11–16 columns) of random expansion chains from $`\mathrm{diag}(0,4)`$ and
  $`\mathrm{diag}(0,6)`$, with all their extensions: 809 bases, 83,810 tests. 0 failures.
- Lemma C: 15,841 matrices $`Y`$ (up to 28 columns) from one-root $`N`$ with 10–14
  columns, and 207 values of $`\mathrm{lh}`$. 0 failures.
