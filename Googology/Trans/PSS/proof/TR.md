[← Back](README.md)

# Lemma TR: $`\mathrm{val} \circ \mathcal T = o`$

**Part 1: §0–§4** | [Part 2: §4b–§7, References, Review history](TR-2.md)

This document is split into two files, because GitHub renders only a limited amount of math on one page.

$`\mathcal T`$ is the translation of [PROOF](PROOF-2.md) §12.1 (code [tr.py](../por/tr.py)).
$`o`$ is the ordinal of a node: $`o(M) = \mathrm{pairOrdL}(M) = 1 + \mathrm{val}(\mathrm{pairTerm}\ M)`$.
COMB is [COMB](COMB.md) (S1, Lemma R, Theorem SC, Lemma 10, …).
## 0. Status

| item | status |
|---|---|
| **Mono\*** (Theorem M: $`\mathcal T_k`$ is strictly increasing, at every level $`k`$, on the level-$`k`$ term trees of standard matrices and of Coll images; hence $`\mathcal T`$ is strictly increasing on nodes) | **PROVED** (§2) |
| Lemma M5 ($`\mathcal T_0(N) = \omega^{\mathcal T(\mathcal LN)}`$ for non-epsilon $`N`$) | PROVED |
| Theorem TR-red (TR $`\iff`$ $`\mathrm{Clos}(N)`$ for every epsilon root $`N`$ of shape C2) | **PROVED** (§3) |
| TR for a node, given TR below it, when its last root is non-epsilon, of shape C1, or of shape C2 with $`W`$'s last child at $`y = 0`$ | PROVED |
| **$`\mathrm{Clos}(N)`$**, shape C2, $`W`$'s last child has $`y = 0`$ (sub-cases S0 and S1a: any expansion inside that child) | PROVED (§4) |
| Lemma W, P-lo, P-hi, bases $`(\mathrm{B}\ell)`$ / $`(\mathrm{B}j_0)`$ / (Bdup) ([§4b](TR-2.md)) | PROVED (see Review history) |
| **Theorem Cof** ($`\sup_n \mathcal T(M[n]) = \mathcal T(M)`$ for every limit $`M`$; this includes S1b and S2) | **PROVED** ([§4b](TR-2.md)) |
| **$`\mathrm{Clos}(N)`$**, all shapes | **PROVED** (corollary of Cof and TR) |
| **Lemma TR** ($`\mathrm{val} \circ \mathcal T = o`$) | **PROVED** ([§4b](TR-2.md)), from Mono\*, Cof and the cited facts of §1 |
| S2(a) as a literal identity $`\mathcal T(M[n]) = \mathcal T(M)[n]`$ | false in general ([§4b.5](TR-2.md)), and not needed |
| LOC (support terms) | not needed; proved independently in [PROOF](PROOF-3.md) §14 |
| Adjustment of $`\mathcal T`$ needed? | **No.** The Mono proof goes through for the definition as given. Standardness is essential ([§6](TR-2.md)). |

## 1. Facts used

**$`T^1`$ side (CITED).** [W07a] = Wilken, APAL 145 (2007); [W24] = Wilken, arXiv:2410.15953v4;
[WW11] = Weiermann–Wilken, MLQ 57 (2011).

- **(L)** Levels.
  - $`\vartheta_m`$-values lie in $`P \cap [\Omega_m, \Omega_{m+1})`$, and $`\vartheta_m`$ is 1-1 on $`T \cap \Omega_{m+2}`$ ([W07a] Lemma 3.30).
  - Terms are ANF sums of $`\vartheta`$-terms, so equal values mean equal terms.
- **(C)** Comparison ([W07a] Lemma 3.30 = [W24] Prop 2.3):
  - $`\beta^{\star_m} \lt \vartheta_m(\beta)`$;
  - $`\vartheta_m(\alpha) \lt \vartheta_m(\gamma) \iff (\alpha \lt \gamma \land \alpha^{\star_m} \lt \vartheta_m(\gamma)) \lor \vartheta_m(\alpha) \le \gamma^{\star_m}`$.
  - Here $`\xi^{\star_m}`$ is the largest $`\vartheta_m`$-subterm of $`\xi`$ that does not lie inside a $`\vartheta_j`$ with $`j \lt m`$
    (0 if there is none).
- **(Min)** Minimality ([W24] Prop 2.2): $`\vartheta_j(\alpha) = \min\{\theta \in \mathbb{P},\ \theta \ge \Omega_j : \alpha^{\star_j} \lt \theta \land \forall \beta \in T^{\Omega_j} \cap \alpha\ (\beta^{\star_j} \lt \theta \to \vartheta_j(\beta) \lt \theta)\}`$.
  Here $`\mathbb{P}`$ is the class of additively principal ordinals. Without this restriction the
  statement is false already at $`\alpha = 1`$: it would give $`\vartheta_0(1) = 2`$ instead of $`\omega`$.
  (Found while formalizing in Lean.)
  - $`T^{\Omega_j}`$ allows arbitrary parameters below $`\Omega_j`$. For $`j = 0`$ it is $`T^1`$ itself.
  - For $`j \ge 1`$ it is **not** $`T^1`$, because $`T^1 \cap [\Omega_j, \Omega_{j+1})`$ is not an initial segment. An
    example is $`\Omega_1 + \psi_0(\Omega_\omega)`$. For that reason (Min) is used only at level 0, and in the C1
    sub-case of $`(\mathrm{B}j_0)`$ (where $`\beta`$ with parameters is checked explicitly). The general base
    $`(\mathrm{B}j_0)`$ avoids it ([§4b.3](TR-2.md), fix B1).
- **(E)** $`\vartheta_j(\Delta + \eta)`$ is an epsilon number above $`\Omega_j`$ iff $`\Delta \gt 0`$. [W24] Lemma 2.4 covers all
  levels $`j`$; [W07a] Lemma 4.3 covers level 0 only.
- **(Inc)** $`\sigma \mapsto \vartheta_j(\Delta + \sigma)`$ ($`\sigma \lt \Omega_{j+1}`$) is strictly increasing. [W24] §2.1 covers all
  levels $`j`$; [W07a] p. 142 covers level 0 only.
- **(Seg)** $`T^1 \cap \Omega_1`$ is an ordinal ([W24] Thm 2.1; [W07a] Theorem 3.23: $`T_m \cap \Omega_{m+1} = \theta_m`$). This is used only at
  the root, in [§4b.4](TR-2.md).
- **(Exp)** The terms `omega_exp(Z, m)` and `log_omega(p)` of [tr.py](../por/tr.py) have the values $`\omega^{\mathrm{val}\,Z}`$
  and the $`u`$ with $`\omega^u = \mathrm{val}\ p`$ ([W07a] Lemma 4.2, [WW11] Lemma 2.12(b), Lemma 3.1). This holds
  at every level, including the $`\Omega_m + n`$ and $`\varepsilon + n`$ cases.
  - The docstring of [tr.py](../por/tr.py) states that the code handles all levels.

**Pair-sequence side.**

- [COMB](COMB.md) S1, Lemma 1 (tree invariants), Lemma 4 (Sh), Lemma 5 (CNF, additivity,
  $`o(M) = \sup_n (o(M[n]) + 1)`$), Lemma R (with its cases A, B, C1, C2), Theorem SC (R0, I0,
  (A), Sib, G\*).
- **Canon ⇐ G\*.** If $`v`$ has $`y = k`$ and $`c`$ is its first child with $`y = k`$, then
  $`T(c) \lt (k, H_v \mathbin{+\!\!+} [(k+1, ())])`$, where $`H_v`$ are $`v`$'s children with $`y = k+1`$.
  - Proof: G\* gives $`T(c) \lt T(v)`$. If $`T(c) \ge (k, H_v, \mathrm{leaf}_{k+1})`$, then $`\mathrm{ch}(c)`$ begins with
    $`H_v`$ followed by some $`w \ge \mathrm{leaf}_{k+1}`$. So $`y(w) = k+1 \gt k = y(c)`$, and $`w \gt c`$. But
    $`T(c) \lt T(v)`$ forces $`w \le c`$. Contradiction.
- Lean: `exists_le_oper` ($`N \lt M`$ standard $`\Rightarrow`$ $`N \le M[n]`$ for some $`n`$) and
  `isWellOrder_ctpsLt` in [Rank.lean](../Rank.lean); `oper_prefix` and `ctps_oper` in
  [pss-proof](https://github.com/koteitan/pss-proof).

**Valid terms.** A term $`s = (y, \text{children})`$ is <em>valid</em> if it is the block of some column of
some CTPS matrix.

- By F3 (prefixes of CTPS are CTPS), valid terms are closed under subterms and under
  child-prefixes: $`(y, (c_1..c_j))`$ for a valid $`(y, (c_1..c_m))`$.
- They satisfy (A), Sib, G\* and Canon for all nodes inside them whose reference node
  $`v(u)`$ lies inside them.
- $`y(s) = k`$ is the <em>level</em> of $`s`$, and $`\mathcal T_k(s)`$ is its image.

## 2. Mono\* (Theorem M)

**Mono\* (= Theorem M, PROVED).** For valid terms $`s, s'`$ of the same level $`k`$:
$`s \lt_t s' \Rightarrow \mathrm{val}\ \mathcal T_k(s) \lt \mathrm{val}\ \mathcal T_k(s')`$. Across levels the order is automatic, by (L). Hence $`\mathcal T`$
is strictly increasing on nodes: roots are non-increasing (S1), their images are then
non-increasing (so ANF with no absorption), and nodes are ordered lexicographically on
root sequences ([PROOF](PROOF.md) Lemma 2.1; [COMB](COMB.md) Lemma 5(a)).

**Lean.** Theorem M is `mono` (and `mono_node` on nodes) in [TR/Mono.lean](../TR/Mono.lean), with no `sorry`, for every term with the tree condition `TGood []`; M2 is `chain` ([TR/Chain.lean](../TR/Chain.lean)), M4 is `bound` ([TR/Bound.lean](../TR/Bound.lean)), and the cited facts of §1 are the axioms of [TR/Cited.lean](../TR/Cited.lean).

**Coll images are covered.** Every term tree that occurs inside a Coll image
$`Y = (0, A \oplus \mathrm{Coll}_A(\mathrm{ch}(s)[:i]))`$ is valid, because $`Y`$ is standard ([COMB](COMB.md) Lemma C). So Mono\*
applies to them with no extra argument. This is the form used in [PROOF](PROOF-3.md) §13 (NS, CI,
$`\mathrm{Bar}_T`$, S-eps).

**Numerical check.** All valid terms of every level that occur in the
44,653 standard matrices with $`\le 8`$ columns were sorted, and $`\mathcal T_k`$ was checked to be strictly increasing:
62,943 terms (33,734 at level 0, 18,929 at level 1, 7,618 at level 2, 2,143 at level 3,
and 519 at levels 4–7). There were 0 failures.

<em>Notation.</em>

- **Non-epsilon $`s`$** (last child $`y \le k`$): $`s = (k, \mathrm{hi} \mathbin{+\!\!+} \mathrm{lo})`$, where hi are the children with
  $`y = k+1`$ (they come first by Sib) and lo are the rest.
  - $`\mathcal T_k(s) = \omega^Z`$ at level $`k`$, with $`Z = h \oplus \lang \mathcal T(c) \rang_{c \in \mathrm{lo}}`$.
  - $`h = \mathcal T_k((k,\mathrm{hi}))`$ if $`\mathrm{hi} \ne \emptyset`$; $`h = \Omega_k`$ if $`\mathrm{hi} = \emptyset`$ and $`k \ge 1`$; $`h`$ is empty if $`\mathrm{hi} = \emptyset`$ and
    $`k = 0`$.
  - $`\oplus`$ is ANF addition (addall).
- **Epsilon $`s`$** (all children $`y = k+1`$, by [COMB](COMB.md) T3): $`s = (k, H_1..H_r)`$.
  - $`X_i := \log \mathcal T_{k+1}(H_i) = D_i + \rho_i`$, where $`D_i`$ is the part of level $`\ge k+1`$ and $`\rho_i`$ is
    the rest.
  - $`\Delta := D_r`$; the final run is $`j+1..r`$ ($`D_i = \Delta`$); $`c := \Sigma_{\mathrm{run}}\, \omega^{\rho_i}`$.
  - $`\eta := [e_p +] (-1 + c)`$, where $`e_p = \mathcal T_k((k, H_1..H_j))`$ is added iff $`j \gt 0`$ and
    $`e_p \gt \Delta^{\star_k}`$.
  - $`\mathcal T_k(s) = \vartheta_k(\Delta + \eta)`$.

<em>The induction.</em> The proof is by induction on $`\mathrm{size}(s) + \mathrm{size}(s')`$ (number of columns). The
IH covers all pairs of valid terms with smaller total size, at all levels. It uses the
following lemmas, whose proofs use only the IH.

**M1 (Seq).** Let a head $`h`$ be fixed (empty or one level-$`k`$ principal term). If $`\sigma \lt_{\mathrm{lex}} \tau`$ are
non-increasing sequences of valid terms of smaller total size, then
$`h \oplus \mathcal T\sigma \lt_{\mathrm{lex}} h \oplus \mathcal T\tau`$.

<em>Proof.</em> By the IH the images are strictly monotone elementwise, and $`\mathcal T\sigma`$ and $`\mathcal T\tau`$ are
non-increasing. The rest is the argument of [COMB](COMB.md) Lemma 10:

- prefix case: a proper prefix;
- first difference at $`p \ge 1`$: the same number $`r`$ of kept head terms, and a difference at
  $`r + p`$;
- $`p = 0`$: either $`r`$ is equal and the first appended terms decide, or fewer head terms are
  kept on the $`\tau`$ side, and $`h[r_\tau] \lt \mathcal T\tau_1`$. ∎

**M2 (Chain).** Let $`q`$ be an epsilon valid term (or a leaf) and $`q \mathbin{+\!\!+} H`$ valid. Then
$`\mathcal T_k(q) \lt \mathcal T_k(q \mathbin{+\!\!+} H)`$.

<em>Proof.</em>

- **Leaf $`q`$:** $`\vartheta_k(0)`$ is the least level-$`k`$ value.
- **Monotone logs:** by Sib, $`H \le H_{\mathrm{last}}`$. By the IH at level $`k+1`$ and monotonicity of $`\log`$,
  $`X(H) \le X(H_{\mathrm{last}})`$, so $`D(H) \le D_{\mathrm{last}}`$.
- **$`D(H) = D_{\mathrm{last}}`$:** the run and $`e_p`$ stay the same, and $`c' = c + \omega^{\rho_H}`$ (ANF extension,
  since $`\rho_H \le \rho_{\mathrm{last}}`$).
  - So $`\eta`$ is an ANF-prefix of $`\eta'`$, and the $`\vartheta_k`$-subterms of $`\Delta+\eta`$ are among those of $`\Delta+\eta'`$.
  - Hence $`(\Delta+\eta)^\star \le (\Delta+\eta')^\star \lt \vartheta_k(\Delta+\eta')`$ by (C), while $`\Delta+\eta \lt \Delta+\eta'`$.
  - By (C), first disjunct, the value increases.
- **$`D(H) \lt D_{\mathrm{last}}`$:** a new run starts. Its prefix is $`q`$, so $`e_p' = \mathcal T_k(q)`$.
  - If $`\mathcal T_k(q) \gt \Delta'^\star`$, then $`\eta' = \mathrm{add}(\mathcal T_k(q), -1 + \omega^{\rho_H})`$. Either $`\mathcal T_k(q)`$ survives in $`\eta'`$, or
    it is absorbed by the leading term $`\lambda`$ of $`-1 + \omega^{\rho_H}`$.
    - In the absorbed case $`\lambda \gt \mathcal T_k(q) \ge \Omega_k`$ and $`\lambda \lt \Omega_{k+1}`$, so $`\lambda`$ is a level-$`k`$ term. It
      lies at the top level of $`\eta'`$, hence it is $`\star_k`$-visible.
    - Absorption does happen: 6 of 8,562 insertions with $`\le 8`$ columns, e.g.
      $`s = (0,[(1,[(2)]),(1,[(0,[(1,[(2)]),(0)])])])`$ (found by the referee).
    - Either way $`(\mathrm{arg}')^\star \ge \mathcal T_k(q)`$.
  - Otherwise $`\mathcal T_k(q) \le \Delta'^\star \le (\mathrm{arg}')^\star`$.
  - In both cases $`\mathcal T_k(q \mathbin{+\!\!+} H) = \vartheta_k(\mathrm{arg}') \gt (\mathrm{arg}')^\star \ge \mathcal T_k(q)`$ by (C). ∎

**M4 (Bound).** Let $`s`$ be valid, epsilon, of level $`k`$, with argument $`\Delta + \eta`$. Let $`E`$ be an
**epsilon number** (value in the epsilon class; the hypothesis is essential, see below) with
$`\mathcal T_k(u) \lt E`$ for every <em>witness</em> $`u`$ of $`s`$. Then $`(\Delta + \eta)^{\star_k} \lt E`$.

The witnesses of $`s`$ are:

- the $`y = k`$ nodes $`u`$ inside $`s`$ reached from $`s`$ through nodes with $`y \ge k+1`$ (these are
  descending with $`v(u) = s`$, so $`u \lt_t s`$ by G\*);
- the proper child-prefixes $`(k, H_1..H_j)`$, $`j \lt r`$, of $`s`$ ($`\lt_t s`$).

All witnesses are valid, $`\lt_t s`$, and smaller than $`s`$.

<em>Proof.</em> Say that a node $`t`$ of $`s`$ is <em>reached</em> if the path from $`s`$ to $`t`$ ($`s`$ excluded) has only
nodes with $`y \ge k+1`$. By <em>visible</em> we mean a $`\vartheta_k`$-subterm not inside a $`\vartheta_i`$ with $`i \lt k`$.

**Invariant (I).** Let $`t`$ be valid of level $`j \ge k+1`$, where $`t`$ is either a reached inner node of $`s`$, or a
child-prefix of such a node. Then every visible $`\vartheta_k`$-subterm of $`\mathcal T_j(t)`$ is $`\lt E`$.

<em>Proof of (I),</em> by induction on the size of $`t`$.

- **Leaf:** $`\vartheta_j(0)`$ has no $`\vartheta_k`$-subterm.
- **$`t`$ non-epsilon at level $`j`$:** $`\mathcal T_j(t) = \mathrm{omega\_exp}(Z)`$ with $`Z = h \oplus \lang \mathcal T(c) \rang_{c \in \mathrm{lo}}`$.
  - `omega_exp` only removes a leading $`\Omega_j`$ or a final 1 (in the $`\varepsilon + n`$ case). So its
    visible $`\vartheta_k`$-subterms are among those of the summands of $`Z`$. For $`k = 0`$, a removed or added
    $`1 = \vartheta_0(0)`$ is $`\lt E`$ anyway.
  - The head $`h = \mathcal T_j((j, \mathrm{hi}))`$: $`(j, \mathrm{hi})`$ is a child-prefix of $`t`$, of smaller size. Use the IH.
    If $`\mathrm{hi} = \emptyset`$, $`h = \Omega_j`$ has none.
  - A lo child $`c`$ with $`y(c) \ge k+1`$: a reached node of smaller size. Use the IH.
  - A lo child $`c`$ with $`y(c) = k`$: $`c`$ is a witness of $`s`$. So $`\mathcal T_k(c) \lt E`$, and every visible
    subterm of $`\mathcal T_k(c)`$ is $`\lt \mathcal T_k(c)`$ by (C).
  - A lo child $`c`$ with $`y(c) \lt k`$: every $`\vartheta_k`$-subterm of $`\mathcal T(c)`$ lies inside a $`\vartheta_{y(c)}`$, so it
    is invisible.
- **$`t`$ epsilon at level $`j`$:** $`\mathcal T_j(t) = \vartheta_j(\Delta' + \eta')`$.
  - $`\Delta' + \rho_i`$ are parts of $`X_i = \log \mathcal T_{j+1}(H_i)`$. $`\log`$ only adds or removes a final 1 or a
    leading $`\Omega_{j+1}`$. Each $`H_i`$ is a reached node of level $`j+1`$, so the IH applies.
  - $`e_p' = \mathcal T_j(\text{child-prefix of } t)`$: IH.
  - A run term $`\omega^{\rho_i}`$, at the level of $`\rho_i`$:
    - if that level is $`\gt k`$, its visible $`\vartheta_k`$-subterms are those of $`\rho_i`$ (IH, as above);
    - if that level is $`\lt k`$, they are invisible;
    - if that level is $`= k`$, then $`\omega^{\rho_i}`$ is itself a $`\vartheta_k`$-term. Every summand of $`\rho_i`$ is
      $`\lt E`$: a visible level-$`k`$ summand by the IH, a lower one because it is $`\lt \Omega_k \lt E`$. So
      $`\rho_i \lt E`$, since $`E`$ is additive principal. Then $`\omega^{\rho_i} \lt E`$, **because $`E`$ is an epsilon
      number**. Its inner visible subterms are those of $`\rho_i`$.

**$`s`$ itself** (level $`k`$, epsilon) is handled the same way.

- $`\Delta`$ comes from $`X_r`$, with $`H_r`$ a reached node of level $`k+1`$: (I).
- $`e_p = \mathcal T_k(\text{proper child-prefix})`$ is a witness image, and its subterms are smaller by (C).
- Run terms $`\omega^{\rho_i}`$ are handled as in the epsilon case of (I). Their level-$`k`$ summands are
  images of $`y = k`$ children of $`H_i`$, which are witnesses.
- So every visible $`\vartheta_k`$-subterm of $`\Delta + \eta`$ is $`\lt E`$. ∎

**Why $`E`$ must be an epsilon.** In 9,153 of 29,352 epsilon valid terms ($`\le 8`$ columns;
found by the referee), $`(\Delta+\eta)^{\star_k}`$ is an $`\omega^{\rho}`$-term that is <em>larger than every witness
image</em>. So "$`E \gt`$ all witness images" alone does not suffice.

**Where M4 is used.** In each use, $`E`$ is a $`\vartheta_k`$-epsilon value:
- in (V), $`E = \mathcal T_k(q')`$;
- in Lemma W, $`E = \mathcal T_k(a\lang n\rang)`$ with $`a\lang n\rang`$ epsilon;
- in §3, $`E = \theta`$ is a sup of epsilons. Only additive principality and $`\omega`$-closure are used,
  and a sup of epsilons has both.

**Main case analysis.** Let $`s \lt_t s'`$ be valid of level $`k`$.

- **(I) $`s`$ a leaf.** $`\mathcal T_k(s) = \vartheta_k(0)`$ is minimal at level $`k`$ (1 when $`k = 0`$), and $`s'`$ is not a
  leaf.
- **(II) Both non-epsilon.** Compare the children lists $`\mathrm{hi} \mathbin{+\!\!+} \mathrm{lo}`$ and $`\mathrm{hi}' \mathbin{+\!\!+} \mathrm{lo}'`$.
  - (i) $`\mathrm{hi} = \mathrm{hi}'`$, $`\mathrm{lo} \lt_{\mathrm{lex}} \mathrm{lo}'`$: $`Z \lt Z'`$ by M1.
  - (ii) Otherwise $`(k,\mathrm{hi}) \lt_t (k,\mathrm{hi}')`$: the hi-part differs first, or hi is a proper prefix
    of hi′. (hi′ a proper prefix of hi would give $`s \gt s'`$.)
    - Then $`h \lt \mathcal T_k((k,\mathrm{hi}'))`$ by the IH ($`\mathrm{lo} \ne \emptyset`$, so the size drops); $`\Omega_k \lt`$ it if $`\mathrm{hi} = \emptyset`$.
    - Canon gives $`\mathrm{lo}_1 \lt_t (k, \mathrm{hi}, \mathrm{leaf}_{k+1}) \le_t (k, \mathrm{hi}')`$, because every proper extension
      of hi by a $`y = k+1`$ child is $`\ge`$ the leaf. So $`\mathcal T(\mathrm{lo}_1) \lt \mathcal T_k((k,\mathrm{hi}'))`$ by the IH
      (terms of lower level are trivially smaller).
    - So every summand of $`Z`$ is $`\lt \mathcal T_k((k,\mathrm{hi}')) \le Z'`$.
  - In both sub-cases $`\omega^Z \lt \omega^{Z'}`$ by (Exp).
- **(III) $`s`$ epsilon, $`s'`$ non-epsilon.**
  - Comparing children, $`s \le_t (k,\mathrm{hi}')`$, since $`H_i = \mathrm{hi}'_i`$ and a later $`H`$ ($`y = k+1`$) against
    $`\mathrm{lo}'_1`$ ($`y \le k`$) would give $`s \gt s'`$.
  - If $`s \lt_t (k,\mathrm{hi}')`$: $`\mathcal T_k(s) \lt \mathcal T_k((k,\mathrm{hi}')) \le Z' \le \omega^{Z'}`$.
  - If $`s = (k,\mathrm{hi}')`$: $`\mathrm{lo}' \ne \emptyset`$ makes $`Z' \gt \mathcal T_k(s)`$, and $`\omega^{Z'} \ge Z'`$.
- **(IV) $`s`$ non-epsilon, $`s'`$ epsilon.** Every summand of $`Z`$ is $`\lt \mathcal T_k(s')`$:
  - $`h`$: $`(k,\mathrm{hi}) \lt_t s \lt_t s'`$, by the IH;
  - $`\Omega_k`$;
  - lo images of lower level;
  - lo children with $`y = k`$: they are descending with $`v = s`$, so $`c \lt_t s \lt_t s'`$ (G\*), and the
    IH applies.

  So $`Z \lt \mathcal T_k(s')`$, and $`\mathcal T_k(s') \in E`$ by (E). Hence $`\omega^Z \lt \mathcal T_k(s')`$.
- **(V) Both epsilon.**
  - If the **children list** of $`s`$ is a proper prefix of that of $`s'`$ ($`H_i = H'_i`$ for $`i \le r`$):
    iterate M2.
  - Otherwise let $`p`$ be the first index with $`H_p \ne H'_p`$. Then $`H_p \lt_t H'_p`$. This includes the
    case where $`H_p`$ is a proper <em>block</em> prefix of $`H'_p`$, i.e. $`s`$ is a block prefix of $`s'`$ whose
    last child is extended. M2 does not cover that case; the argument below does. Put
    $`q = (k, H_1..H_{p-1})`$ and
    $`q' = q \mathbin{+\!\!+} H'_p`$. Then $`q'`$ is a child-prefix of $`s'`$, so $`\mathcal T_k(q') \le \mathcal T_k(s')`$ by M2. It
    remains to show $`\mathcal T_k(s) \lt \mathcal T_k(q')`$.
  - By the IH at level $`k+1`$ and Sib, $`X_i \le X_p \lt X'_p`$ for $`i \ge p`$. So $`D_r \le D_p \le D'_p =: \Delta'`$.
    - **$`D_r \lt \Delta'`$:** then $`\Delta_s + \eta_s \lt \Delta' + \eta'`$.
    - **$`D_r = \Delta'`$:** then $`D_i = \Delta'`$ for all $`i \ge p`$, and $`\rho_p \lt \rho'_p`$. Both runs start at the
      same index, with the same $`e_p`$ and the same insertion test (same $`\Delta`$).
      - $`\eta_s = [e_p+](-1 + C + \omega^{\rho_p} + \cdots + \omega^{\rho_r})`$, and
        $`\eta' = [e_p+](-1 + C + \omega^{\rho'_p})`$.
      - Since $`\rho_r \le \cdots \le \rho_p \lt \rho'_p`$, the tail sum is $`\lt \omega^{\rho'_p}`$. So $`\eta_s \lt \eta'`$.
  - **The $`\star`$-condition.** $`\mathcal T_k(q')`$ is an epsilon value (E). Every witness $`u`$ of $`s`$ satisfies
    $`u \lt_t s \lt_t q'`$, with smaller size, so $`\mathcal T_k(u) \lt \mathcal T_k(q')`$ by the IH. M4 gives
    $`(\Delta_s + \eta_s)^\star \lt \mathcal T_k(q')`$.
  - By (C), first disjunct, $`\mathcal T_k(s) \lt \mathcal T_k(q')`$. ∎

**Remark (why SC matters).** Case (II)(ii) uses Canon, and (IV), (V) and M4 use G\*. For
non-standard matrices Mono fails:

- $`(0,0)(1,0)(2,1)`$ gets $`\omega^{\varepsilon_0} = \varepsilon_0 = \mathcal T((0,0)(1,1))`$, a collision.
- $`(0,0)(1,1)(2,0)(3,1)(4,1)`$ gets $`\vartheta(\Omega + \zeta_0)`$ with $`\zeta_0`$ a sup-point. This is fact NS of
  [PROOF](PROOF-2.md) §12.5.

So Mono is a statement about standard matrices only. SC is exactly the hypothesis it
needs.

**Lemma M5 (PROVED).** For non-epsilon $`N \in R`$, $`\mathcal T_0(N) = \mathrm{omega\_exp}(\mathcal T(\mathcal LN), 0)`$, so
$`\mathrm{val}\ \mathcal T_0(N) = \omega^{\mathrm{val}\ \mathcal T(\mathcal LN)}`$.

<em>Proof.</em> $`Z = \mathcal T((0,\mathrm{hi})) \oplus \lang \mathcal T(\mathrm{lo}_i) \rang`$, while $`\mathcal LN = \mathrm{addall}((0,\mathrm{hi}), \mathrm{lo}_1, \ldots)`$. The absorptions
agree because $`\mathcal T_0`$ is strictly monotone (Theorem M). Then use (Exp). ∎

## 3. Reduction of TR

<em>Superseded by [§4b](TR-2.md). Kept as a cross-check; [§4b](TR-2.md) does not depend on it.</em>

**Definition (Clos).** Let $`N \in R`$ be epsilon with $`\mathcal T(N) = \vartheta_0(\Delta + \eta)`$, and put
$`\theta := \sup_n \mathrm{val}\ \mathcal T(N[n])`$. Then

```math
\mathrm{Clos}(N):\quad \forall \beta \in T^1 \cap (\Delta + \eta):\ \ \beta^\star \lt \theta \ \Rightarrow\ \exists n\ \ \vartheta_0(\beta) \lt \mathcal T(N[n]).
```

**Theorem TR-red (PROVED).** TR holds iff $`\mathrm{Clos}(N)`$ holds for every epsilon $`N \in R`$ whose last
child $`C_k`$ is not a leaf (shape C2 of [COMB](COMB.md) Lemma R).

<em>Proof of ⇐.</em> Induction on nodes along $`\lt_p`$. The IH is $`\mathrm{val}\ \mathcal T(v) = o(v)`$ for all $`v \lt_p M`$.

- **$`(0,0)`$:** $`\vartheta_0(0) = 1 = o`$.
- **Several roots:** $`\mathcal T`$ of a sum is the ANF sum, since images do not increase (Theorem M).
  Additivity of $`o`$ ([COMB](COMB.md) Lemma 5(a)) finishes.
- **$`N \in R`$ non-epsilon:**
  - $`\mathcal LN \lt_p (N)`$, so $`\mathrm{val}\ \mathcal T(\mathcal LN) = o(\mathcal LN)`$ by the IH.
  - Then $`\mathrm{val}\ \mathcal T(N) = \omega^{o(\mathcal LN)}`$ by M5, and $`\omega^{o(\mathcal LN)} = o(N)`$ by Lemma R.
- **$`N`$ epsilon, shape C1** ($`C_k = (1,1)`$):
  - $`\theta :=`$ the least epsilon $`\gt o(a)`$, where $`a = \mathrm{anchor}(N)`$; if $`k = 1`$, put $`a := ()`$ with
    $`o(a) := 0`$, so that $`\theta = \varepsilon_0`$. This equals $`o(N)`$ by
    [COMB](COMB.md) Lemma R, case C1. By the IH, $`o(a) = \mathrm{val}\ \mathcal T(a)`$.
  - **The run.** The leaf has $`X = \Omega`$, so $`D = \Omega`$ and $`\rho = 0`$.
    - If $`C_{k-1}`$ is in the final run, then $`\eta = \eta_a + 1`$, where $`\mathcal T(a) = \vartheta(\Omega + \eta_a)`$.
    - Otherwise $`\eta = e_p = \mathcal T(a)`$: $`e_p \gt \Omega^\star = 0`$, and the prefix $`a`$ has $`\Delta_a \gt \Omega`$.
    - If $`k = 1`$, $`\eta = 0`$.
  - **Upper bound, by (Min).**
    - $`(\Omega+\eta)^\star = \eta^\star \le \mathcal T(a) \lt \theta`$.
    - Let $`\beta \lt \Omega + \eta`$ with $`\beta^\star \lt \theta`$.
      - If $`\beta \lt \Omega`$: $`\beta \lt \theta`$, since its leading summand is visible. So $`\vartheta(\beta) \le \omega^{\beta+1} \lt \theta`$.
      - If $`\beta = \Omega + \sigma`$ with $`\sigma \le \eta_a`$: $`\vartheta(\beta) \le \mathcal T(a) \lt \theta`$ by (Inc).
      - If $`\beta = \Omega + \sigma`$ with $`\sigma \lt \mathcal T(a)`$ (the case $`\eta = e_p`$): $`\Omega + \sigma \lt \Delta_a + \eta_a`$, and
        $`\sigma^\star \le \sigma \lt \mathcal T(a)`$. So $`\vartheta(\beta) \lt \mathcal T(a)`$ by (C).
    - Hence $`\mathrm{val}\ \mathcal T(N) \le \theta`$.
  - **Lower bound.** $`\mathcal T(N)`$ is an epsilon (E) and $`\gt \mathcal T(a)`$ by Theorem M. So it is $`\ge \theta`$.
- **$`N`$ epsilon, shape C2:**
  - The $`N[n]`$ are epsilon, $`\lt_p N`$, and increasing, so
    $`o(N) = \sup o(N[n]) = \sup \mathrm{val}\ \mathcal T(N[n]) = \theta`$, by [COMB](COMB.md) Lemma R and the IH.
  - Theorem M gives $`\mathrm{val}\ \mathcal T(N) \ge \theta`$.
  - **Upper bound, by (Min).**
    - $`(\Delta+\eta)^\star \lt \theta`$, by M4 with witnesses $`u \lt_p N`$. These are standard by Sh and F3. By
      `exists_le_oper`, $`u \le N[n]`$ for some $`n`$, so $`\mathcal T(u) \le \mathcal T(N[n]) \lt \theta`$ (Theorem M). $`\theta`$ is a
      sup of epsilons, hence $`\omega`$-closed.
    - The second condition of (Min) is exactly $`\mathrm{Clos}(N)`$.

<em>Proof of ⇒.</em> Given TR and Theorem M, $`\mathrm{val}\ \mathcal T(N) = \theta`$. By (Min) the condition of Clos holds
with $`\theta`$, and "$`\vartheta_0(\beta) \lt \theta`$" means "$`\vartheta_0(\beta) \lt \mathcal T(N[n])`$ for some $`n`$". ∎

**Why Clos is the whole content.** Mono gives $`\mathrm{val} \circ \mathcal T \ge o`$ pointwise, since a strictly
increasing map on a well-order dominates the rank. Clos is exactly "no ordinal of $`T^1`$ falls
into a gap $`\sup_n \mathcal T(N[n]) \le p \lt \mathcal T(N)`$", that is, downward closure of the image ([PROOF](PROOF.md)
§12.3(a)). The least-gap argument shows that the least non-image ordinal below an image
must be an epsilon $`p = \vartheta_0(\Gamma+\rho)`$ of shape C2:

- a sum is covered by S1(c);
- a non-epsilon principal $`\omega^Z`$ is covered by Lemma R's surjectivity ($`\mathcal L^{-1}`$) and M5;
- shapes A, B and C1 are excluded as above.

## 4. Clos in shape C2: what is proved

<em>Superseded by [§4b](TR-2.md). Kept as a cross-check; [§4b](TR-2.md) does not depend on it.</em>

Write $`N = (0, C_1..C_{k-1}, W)`$, where $`W = C_k`$ is not a leaf and $`y(W) = 1`$. The last column
$`\ell`$ lies inside $`W`$, at depth $`\ge 2`$.

**Sub-case S0 (PROVED): $`\ell = (2,0)`$ is a $`y = 0`$ leaf child of $`W`$.** Then $`i_1 = 0`$, $`j_0 = W`$, and
$`N[n] = (0, C_1..C_{k-1}, W^-, \ldots, W^-)`$ with $`n`$ copies of $`W^- := W`$ without $`\ell`$.

- **The logs.** By (Exp), $`X(W) = X(W^-) + 1`$, whether $`W^-`$ is non-epsilon, epsilon at level 1,
  or a leaf. The last lo image is $`\mathcal T_0(\ell) = 1`$, which absorbs nothing. So $`D(W^-) = \Delta`$ and
  $`\rho_W = \rho^- + 1`$.
- **The runs.** The final run of $`N[n]`$ is the run of $`N`$ with $`W`$ replaced by $`n`$ copies of $`W^-`$.
  $`j`$, $`e_p`$ and the insertion test are unchanged, and
  $`\eta_n = [e_p+](-1 + c' + \omega^{\rho^-}\cdot n)`$, while $`\eta = [e_p+](-1 + c' + \omega^{\rho^-+1})`$.
- **The limit.** Since $`\omega^{\rho^-+1} = \sup_n \omega^{\rho^-}\cdot n`$, every $`\sigma \lt \eta`$ lies below some $`\eta_n`$.
- **Checking Clos.** Let $`\beta = \Gamma + \sigma \lt \Delta + \eta`$.
  - If $`\Gamma \lt \Delta`$, then $`\beta \lt \Delta \le \Delta + \eta_1`$.
  - If $`\Gamma = \Delta`$, then $`\sigma \lt \eta_n`$ for some $`n`$.
  - In both cases $`\beta \lt \Delta + \eta_n`$. Also $`\beta^\star \lt \theta`$ gives $`\beta^\star \lt \mathcal T(N[n'])`$ for large $`n'`$. So
    $`\vartheta(\beta) \lt \mathcal T(N[n])`$ by (C), for $`n`$ large. ∎

**Sub-case S1a (PROVED): $`W`$'s last child $`E`$ has $`y(E) = 0`$ and is not a leaf,** with $`\ell`$
anywhere inside $`E`$.

- **Locality.** $`E`$ has $`y = 0`$ and lies on $`\ell`$'s ancestor path. So the bad root is inside $`E`$'s
  subtree:
  - if $`y_\ell \ge 1`$, $`E`$ itself is an ancestor with smaller $`y`$;
  - if $`y_\ell = 0`$, $`j_0 = p(\ell) \ge E`$.
- By [COMB](COMB.md) Lemma 3 ($`c = E`$) and Lemma 4, $`Q := \mathrm{sh}(E) \in R`$, and
  $`N[n] = (0, C_1..C_{k-1}, W\lang n\rang)`$, where $`W\lang n\rang = (1, \mathrm{ch}(W)^- \mathbin{+\!\!+} \mathrm{roots}(Q[n]))`$ and the roots of
  $`Q[n]`$ ($`y = 0`$) become the last children of $`W`$.
- **The logs.** In $`Z(W) = h \oplus (y{=}1 \text{ lo images}) \oplus (y{=}0 \text{ images})`$, level-0 summands never
  absorb level-1 summands. By (L) and ANF uniqueness, $`\log_\omega`$ returns $`Z`$ syntactically. So
  $`D(W\lang n\rang) = D(W) = \Delta`$, and
  $`\rho_n = \rho^- + \mathrm{val}\ \mathcal T(Q[n])`$ while $`\rho_W = \rho^- + \mathrm{val}\ \mathcal T(Q)`$ (as values; the syntactic ANF matches,
  by Mono\*).
- **TR below $`N`$.** G\* for $`E`$ ($`v(E) = N`$'s root) gives $`Q \lt_p N`$. So TR holds for $`Q`$ and for
  every $`Q[n]`$ (IH).
- **The limit.** $`Q`$ is a limit node, so $`\mathrm{val}\ \mathcal T(Q) = o(Q) = \sup o(Q[n])`$ ([COMB](COMB.md) Lemma 5(b)). So
  $`\sup_n \rho_n = \rho_W`$, with $`\rho_n \lt \rho_W`$, and $`\rho_W`$ is a limit.
- **The runs.** $`\rho_n \lt \rho_W \le \rho`$ of the previous run member. So the final run, $`j`$, $`e_p`$ and the
  insertion test are those of $`N`$, and as values
  $`\eta_n = e + (-1 + c' + \omega^{\rho_n}) \to \eta = e + (-1 + c' + \omega^{\rho_W})`$, by continuity of $`\omega^{\cdot}`$
  and of ordinal addition in the right argument.
- **Checking Clos.** It follows exactly as in S0: $`\beta = \Gamma + \sigma \lt \Delta + \eta`$ gives $`\beta \lt \Delta + \eta_n`$
  for some $`n`$, and then (C) applies. ∎

Together, S0 and S1a cover every C2 configuration in which $`W`$'s last child has $`y = 0`$.

**All remaining sub-cases: see [§4b](TR-2.md).** [§4b](TR-2.md) proves cofinality directly for <em>every</em> limit
matrix, by one uniform propagation argument. S1b and S2 are special cases. The proof
needs neither a $`\mathcal T`$-level substitution identity nor the support-term fact LOC.

---

**Part 1: §0–§4** | [Part 2: §4b–§7, References, Review history](TR-2.md)
