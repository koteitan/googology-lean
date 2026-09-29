[← Back](README.md)

# Lemma TR: $`\mathrm{val} \circ \mathcal T = o`$ (part 2 of 2)

[Part 1: §0–§4](TR.md) | **Part 2: §4b–§7, References, Review history**

## 4b. Cofinality (Cof): PROVED

**Theorem Cof.** For every standard matrix $`M`$ whose last column is not $`(0,0)`$, with
$`\mathrm{Lng}\ M \ge 2`$:

```math
\sup_n \mathrm{val}\ \mathcal T(M[n]) = \mathrm{val}\ \mathcal T(M).
```

**Theorem TR (PROVED).** $`\mathrm{val}\ \mathcal T(M) = o(M)`$ for every node $`M`$.

<em>Proof of TR from Cof.</em> Induction along $`\lt_p`$.

- **$`(0,0)`$:** $`1 = 1`$.
- **Successor** $`M = M'(0,0)`$: $`\mathcal T(M) = \mathcal T(M') + 1`$, and $`o(M) = o(M') + 1`$ ([COMB](COMB.md) Lemma 5).
- **Limit $`M`$:** $`\mathrm{val}\ \mathcal T(M) = \sup \mathrm{val}\ \mathcal T(M[n])`$ (Cof) $`= \sup o(M[n])`$ (IH, since $`M[n] \lt_p M`$)
  $`= o(M)`$ ([COMB](COMB.md) Lemma 5(b)). ∎

In particular $`\mathrm{Clos}(N)`$ holds for every $`N`$ (Theorem TR-red, ⇒), and so do S1b and S2.

### 4b.0 Setting (pair-sequence facts only)

Fix a limit $`M`$.

- $`\ell`$ is the last column; $`j_0, i_1, d_0`$ are as in `oper`.
- The <em>path</em> is the set of ancestors of $`\ell`$ ($`\ell`$ included). $`t`$ is the last root segment, and
  $`r`$ its root.
- For a path node $`a \ne \ell`$, $`a\lang n\rang`$ is the term (block) of $`a`$ in $`M[n]`$. We use $`n \ge 2`$ throughout.

**Case $`i_1 = 1`$.** Put $`m := y_{j_0} = y_\ell - 1`$ (step-down, [COMB](COMB.md) Lemma 9). Every path node
strictly between $`j_0`$ and $`\ell`$ has $`y \ge m+1`$.

- **(S)** For path nodes $`a`$ from $`j_0`$ down to $`p(\ell)`$: $`T(a\lang n\rang) = T(a)[\ell \mapsto T(j_0\lang n-1\rang)]`$.
  - The copy $`B_1 \ldots B_{n-1}`$, attached at $`\mathrm{copy}_0(p(\ell))`$, is the block of $`j_0`$ in $`M[n-1]`$,
    shifted.
  - So $`j_0\lang n\rang = j_0[\ell \mapsto j_0\lang n-1\rang]`$, and $`j_0\lang 1\rang = j_0`$ without $`\ell`$.
- **(A)** For proper ancestors $`a`$ of $`j_0`$: $`T(a\lang n\rang) = T(a)[j_0\text{-block} \mapsto T(j_0\lang n\rang)]`$, by
  locality ([COMB](COMB.md) Lemma 3).

**Case $`i_1 = 0`$.** $`j_0 = p(\ell)`$, and $`\ell`$ is a $`y = 0`$ leaf.

- If $`j_0 \ne r`$: $`p(j_0)\lang n\rang = p(j_0)`$ with its last child $`j_0`$ replaced by $`n`$ sibling copies of
  $`j_0^- := j_0`$ without $`\ell`$.
- If $`j_0 = r`$: $`M[n] = (\text{earlier roots}) \mathbin{+\!\!+} (\mathrm{Pred}\ t)^n`$.
- Higher path nodes change by locality, as in (A).

**Positions.** For every path node $`a \ne \ell`$, except $`a = j_0`$ in case $`i_1 = 0`$ (there $`j_0\lang n\rang = j_0^-`$
has length exactly $`q_a`$; this node is never used, since propagation starts at $`p(j_0)`$):

- $`T(a\lang n\rang)`$ agrees with $`T(a)`$ at every position before $`q_a`$, the position of $`\ell`$ in $`T(a)`$;
- $`T(a\lang n\rang)`$ is longer than $`q_a`$ (for $`n \ge 2`$);
- the column of $`T(a\lang n\rang)`$ at position $`q_a`$ is smaller than $`\ell`$: it is $`(x_\ell, y_{j_0})`$ if
  $`i_1 = 1`$, and $`(x_{j_0}, y_{j_0})`$ if $`i_1 = 0`$.

So $`a\lang n\rang \lt_t a`$, and $`a\lang n\rang`$ is increasing in $`n`$ (`oper_prefix`).

### 4b.1 Two lemmas

**Lemma W (witnesses stay below; PROVED).** Let $`a`$ be a path node, $`a \ne \ell`$, of level $`k`$,
and $`n \ge 2`$. Then every witness $`u`$ of $`a`$ (M4: an inner $`y = k`$ node reached through $`y \ge k+1`$,
or a proper child-prefix $`(k, H_1..H_j)`$) satisfies $`u \lt_t a\lang n\rang`$. Hence
$`\mathcal T_k(u) \lt \mathcal T_k(a\lang n\rang)`$ by Mono\*.

If $`a\lang n\rang`$ is epsilon, M4 gives $`(\text{arg of } \mathcal T_k(a))^{\star_k} \lt \mathcal T_k(a\lang n\rang)`$.

<em>Proof.</em>

- **Child-prefixes** stay proper prefixes of $`a\lang n\rang`$, because only the last child changes.
- **An inner witness $`u`$** starts at offset $`\ge 1`$ in $`T(a)`$. Its block ends at or before $`q_a`$:
  if $`\ell`$ is in its block, $`\ell`$ is its last column. So $`\mathrm{len}\ T(u) \le q_a`$.
- The comparison $`T(u) \lt_t T(a)`$ (G\*) is decided at a position $`\lt \mathrm{len}\ T(u) \le q_a`$, or $`T(u)`$
  is a proper prefix of $`T(a)`$. $`T(a\lang n\rang)`$ agrees with $`T(a)`$ below $`q_a`$ and is longer than
  $`q_a`$, so the same comparison gives $`T(u) \lt_t T(a\lang n\rang)`$. ∎

**Bounds.** Let $`B`$ be either True, or $`B_m(\gamma) :\iff \gamma^{\star_m} \lt \theta_m`$. Here
$`\theta_m := \sup_n \mathrm{val}\ \mathcal T_m(j_0\lang n\rang)`$, in case $`i_1 = 1`$.

- The terms to which $`B`$ is passed below are the following. Each lies outside every $`\vartheta_j`$
  with $`j \lt m`$, so each $`\star_m`$-subterm of it is a $`\star_m`$-subterm of $`\gamma`$, and it inherits $`B`$:
  - the argument $`\beta`$ of the leading term $`g = \vartheta_k(\beta)`$ of $`\gamma`$ ($`k \gt m`$);
  - $`\beta^{\star_k}`$ for $`k \gt m`$ (P-hi, IH);
  - $`\xi = \log g`$ and the syntactic tail $`\xi' = -K(v) + \xi`$ (P-lo);
  - $`D_c`$, a top-level summand of $`\beta`$; the syntactic tail $`\sigma'' = -\Pi + \sigma`$ of $`\sigma`$; and
    $`\zeta := \log(\text{leading term of } \sigma'')`$, hence $`D_c + \zeta`$ (P-hi);
  - $`\omega^\xi`$ versus $`\xi`$ (the X-form). $`\omega^{\cdot}`$/$`\log`$ only add or remove a leading $`\Omega_{k+1}`$ or a final 1.

**$`\mathrm{LC}_B(a)`$** (cofinality of a path node):

```math
\forall \gamma \in T^1:\ \ \gamma \lt \mathcal T(a) \land B(\gamma)\ \Rightarrow\ \exists n \ge 2:\ \ \gamma \lt \mathcal T(a\lang n\rang).
```

LC is a statement about $`T^1`$-terms only. It says nothing about ordinals outside $`T^1`$. Only at
the root (level 0) is it turned into an ordinal equality, by (Seg).

For $`c`$ of level $`k+1`$, the **X-form** of $`\mathrm{LC}_B(c)`$ is: for all $`\xi \lt X(c)`$ with $`B(\xi)`$, there is $`n`$
with $`\xi \lt X(c\lang n\rang)`$. Here $`X = \log \mathcal T_{k+1}`$.

- It follows from $`\mathrm{LC}_B(c)`$: if $`\xi \lt \Omega_{k+1}`$, it is trivial, since $`X(c\lang n\rang) \ge \Omega_{k+1}`$.
- Otherwise apply $`\mathrm{LC}_B(c)`$ to $`\omega^\xi`$ at level $`k+1`$, which has the same $`\star_m`$ ($`\omega^{\cdot}`$ and $`\log`$ only
  add or remove a leading $`\Omega_{k+1}`$ or a final 1), and use (Exp).

### 4b.2 Propagation

**Lemma P-lo (PROVED).** Let $`a`$ be non-epsilon at level $`k`$, with its last child $`c`$ on the
path. Suppose $`a\lang n\rang = a`$ with $`c`$ replaced by $`c\lang n\rang`$, where $`c\lang n\rang`$ is one child of level $`\le k`$,
and $`v_n := \mathcal T(c\lang n\rang) \lt v := \mathcal T(c)`$. Then $`\mathrm{LC}_B(c) \Rightarrow \mathrm{LC}_B(a)`$. This includes $`c = \ell`$, with
$`v = \Omega_{m+1}`$ and $`v_n = \mathcal T_m(j_0\lang n-1\rang)`$.

<em>Proof.</em>

- $`\mathcal T(a) = \omega^Z`$ with $`Z = Z^- \oplus v`$, and $`\mathcal T(a\lang n\rang) = \omega^{Z_n}`$ with $`Z_n = Z^- \oplus v_n`$. Write
  $`K(w)`$ for the part of $`Z^-`$ that is $`\ge w`$. Then $`Z = K(v) + v`$, and
  $`Z_n \ge K(v) + v_n`$, since $`v_n \lt v`$ makes $`K(v_n)`$ an extension of $`K(v)`$.
- Let $`\gamma \lt \omega^Z`$ with $`B(\gamma)`$. If $`\gamma \lt \Omega_k`$, we are done.
- Otherwise let $`g`$ be the leading term of $`\gamma`$ and $`\xi := \log g \lt Z`$. Then $`B(\xi)`$ holds, and
  $`\gamma \lt \omega^{\xi+1}`$.
  - If $`\xi \lt K(v)`$: then $`\xi + 1 \le Z_n`$.
  - Otherwise $`\xi = K(v) + \xi'`$ with $`\xi' \lt v`$ and $`B(\xi')`$. By $`\mathrm{LC}_B(c)`$, $`\xi' \lt v_n`$. Since $`v_n`$ is
    principal, $`\xi + 1 \le K(v) + v_n \le Z_n`$.
- Either way $`\gamma \lt \omega^{Z_n}`$. ∎

**Lemma P-hi (PROVED).** Let $`a`$ be epsilon at level $`k`$, $`a = (k, H_1..H_{r-1}, c)`$, with $`c`$ on
the path, $`c \ne \ell`$, and $`a\lang n\rang = (k, H_1..H_{r-1}, c\lang n\rang)`$. Suppose $`\mathrm{LC}_B(c)`$ holds in X-form, and
$`B`$ is True or $`B_m`$ with $`m \lt k`$. Then $`\mathrm{LC}_B(a)`$.

<em>Proof.</em> Induction on the size of $`\gamma`$. $`\mathcal T_k(a\lang n\rang)`$ is a level-$`k`$ epsilon value, since the last
child keeps $`y = k+1`$. So it suffices to treat the leading term $`g = \vartheta_k(\beta)`$ of $`\gamma`$; the case
$`\gamma \lt \Omega_k`$ is trivial.

By (C), $`g \lt \vartheta_k(\Delta+\eta)`$ gives two cases.

- **(ii) $`g \le (\Delta+\eta)^{\star_k}`$.** By Lemma W (with M4), $`g \lt \mathcal T_k(a\lang n\rang)`$.
- **(i) $`\beta \lt \Delta+\eta`$ and $`\beta^{\star_k} \lt \mathcal T_k(a)`$.**
  - By the IH ($`\beta^{\star_k}`$ is smaller than $`\gamma`$ and satisfies $`B`$),
    $`\beta^{\star_k} \lt \mathcal T_k(a\lang n_1\rang)`$.
  - It remains to find $`n \ge n_1`$ with $`\beta \lt \Delta_n + \eta_n`$; then (C) gives $`g \lt \mathcal T_k(a\lang n\rang)`$.
  - Write $`\beta = \Gamma + \sigma`$, where $`\Gamma`$ is the part of level $`\ge k+1`$.
  - **$`\Gamma \lt \Delta = D_c`$.** Then $`\xi := \beta \lt X(c)`$. The X-form gives $`\xi \lt X(c\lang n\rang) = D'_n + \rho'_n`$.
    Also $`\Delta_n = D'_n`$ and $`\eta_n \ge -1 + \omega^{\rho'_n} \ge \rho'_n`$. So $`\beta \lt \Delta_n + \eta_n`$.
  - **$`\Gamma = \Delta`$, and $`D(c\lang n\rang) = D_c`$ for all $`n`$.**
    - The run, the prefix $`e_p`$ and the insertion test are the same for $`a\lang n\rang`$. This is
      because $`D(c\lang n\rang) = D_c`$ and the other children are unchanged.
    - $`\rho(c\lang n\rang) \lt \rho_c`$, since $`X(c\lang n\rang) \lt X(c)`$ (Mono\*) with the same $`D`$-part. So $`\rho_c \gt 0`$,
      and the $`\omega`$-terms stay non-increasing: $`\rho(c\lang n\rang) \lt \rho_c \le \rho(H_{r-1})`$.
    - Put $`\Pi := [e_p +] (-1 + C)`$, where $`C`$ is the run sum without $`c`$, with the convention
      $`-1 + 0 := 0`$ when $`C = \emptyset`$. As values,
      $`\eta = \Pi + \omega^{\rho_c}`$ and $`\eta_n \ge \Pi + (-1 + \omega^{\rho(c\lang n\rang)})`$. When $`C = \emptyset`$, this uses $`\rho_c \gt 0`$.
    - If $`\sigma \lt \Pi`$, then $`\sigma \lt \eta_n`$.
    - Otherwise let $`\sigma'' := -\Pi + \sigma \lt \omega^{\rho_c}`$. It is a syntactic tail of the ANF of $`\sigma`$, so
      $`B(\sigma'')`$ holds.
      - If $`\sigma'' = 0`$, put $`\zeta := 0`$. Otherwise let $`\zeta := \log(\text{leading term of } \sigma'')`$, so
        $`\sigma'' \lt \omega^{\zeta+1}`$ and $`\zeta \lt \rho_c`$.
      - $`B(D_c + \zeta)`$ holds: $`D_c`$ is a top-level summand of $`\beta`$, and $`\zeta`$ comes from $`\sigma''`$.
      - $`D_c + \zeta \lt D_c + \rho_c = X(c)`$. The X-form gives $`n`$ with 
        $`D_c + \zeta \lt X(c\lang n\rang) = D_c + \rho(c\lang n\rang)`$, so $`\zeta \lt \rho(c\lang n\rang)`$.
      - Hence $`\omega^{\zeta+1} \le \omega^{\rho(c\lang n\rang)}`$. Also $`\rho(c\lang n\rang) \ge 1`$, so $`-1 + \omega^{\rho(c\lang n\rang)} = \omega^{\rho(c\lang n\rang)}`$.
        So $`\sigma = \Pi + \sigma'' \lt \Pi + \omega^{\rho(c\lang n\rang)} \le \eta_n`$.
  - **$`\Gamma = \Delta`$, and $`D(c\lang n\rang) \lt D_c`$.**
    - Then $`c`$'s path child has $`y \ge k+1`$. (A path child of level $`\le k`$ changes only summands
      of level $`\le k`$, which never absorb the higher ones.)
    - So $`c`$ has no children of level $`\le k`$ (Sib), and $`\rho_c = 0`$.
    - Hence $`\eta \in \{\eta'+1, e_p, 0\}`$, where $`\vartheta_k(\Delta+\eta') = \mathcal T_k(\mathrm{anchor}_a)`$, and
      $`e_p = \mathcal T_k(\mathrm{anchor}_a)`$ with $`e_p \gt \Delta^\star`$. Here $`\mathrm{anchor}_a = (k, H_1..H_{r-1})`$.
    - If $`\sigma \le \eta'`$: $`g \le \mathcal T_k(\mathrm{anchor}_a)`$, by (Inc).
    - If $`\sigma \lt e_p`$: $`g \lt e_p`$, by (C). The argument $`\Delta + \sigma`$ is below that of the anchor, whose
      last run has a larger $`D`$, and $`(\Delta+\sigma)^\star \lt e_p`$.
    - Finally $`\mathcal T_k(\mathrm{anchor}_a) \lt \mathcal T_k(a\lang n\rang)`$ by Mono\*, since the anchor is a proper prefix of
      $`a\lang n\rang`$. ∎

(This last step is where [W24]'s support terms, and the LOC lemmas of [PROOF](PROOF-3.md) §14, would
enter. Here they are replaced by "$`\mathrm{anchor}_a`$ is a proper prefix of $`a\lang n\rang`$" together with
Mono\*.)

### 4b.3 Bases

**$`(\mathrm{B}\ell)`$ $`i_1 = 1`$: $`\mathrm{LC}_{B_m}(\ell)`$.**

- $`\mathcal T(\ell) = \Omega_{m+1}`$, and $`\ell\lang n\rang`$ is the inserted copy with value $`x_{n-1} := \mathcal T_m(j_0\lang n-1\rang)`$.
- If $`\gamma \lt \Omega_{m+1}`$ and $`\gamma^{\star_m} \lt \theta_m`$, then $`\gamma \lt \theta_m`$: its level-$`m`$ summands are visible, and
  its lower summands are $`\lt \Omega_m`$.
- $`\theta_m = \sup x_n`$, so $`\gamma \lt x_{n-1}`$ for some $`n`$. ∎

**$`(\mathrm{B}j_0)`$ $`i_1 = 1`$: $`\mathrm{LC}_\mathrm{True}(j_0)`$** (on $`T^1`$).

- **When $`p(\ell) = j_0`$** ($`\ell`$ is a hi leaf: $`j_0 = (m, H_1..H_{r-1}, (m+1, ()))`$, the C1 shape
  at level $`m`$).
  - By (S), $`j_0\lang 1\rang = \mathrm{anchor}`$ (or $`(m,())`$), and $`j_0\lang n+1\rang = (m, H_1..H_{r-1}, j_0\lang n\rang)`$, with the
    new child at $`y = m`$.
  - By (Exp), $`t_1 = \mathcal T(\mathrm{anchor}) =: e`$ (an epsilon, by S-eps; or $`\Omega_m`$), and
    $`t_{n+1} = \omega^{e + t_n}`$. So $`\theta_m`$ is the least level-$`m`$ epsilon $`\gt e`$.
  - (Min) at level $`m`$ for $`\alpha = \Omega_{m+1} + \eta`$, with $`\eta \in \{\eta'+1, e_p, 0\}`$. Here $`\beta`$ ranges over
    $`T^{\Omega_m} \cap \alpha`$, parameters included. The closure holds, exactly as for shape C1 in [§3](TR.md):
    - $`\beta \lt \Omega_{m+1}`$ with $`\beta^{\star_m} \lt \theta_m`$: then $`\beta \lt \theta_m`$, because parameters are $`\lt \Omega_m`$. So
      $`\vartheta_m(\beta) \le \omega^{\Omega_m+\beta+1} \lt \theta_m`$;
    - $`\beta = \Omega_{m+1} + \sigma`$ with $`\sigma \le \eta'`$: $`\vartheta_m(\beta) \le e`$, by (Inc).
      - (Inc) is cited for $`T^\tau`$, but it holds in $`T^{\Omega_m}`$ (parameters $`\lt \Omega_m`$) by (C). If
        $`\sigma \lt \sigma'`$, then $`(\Delta+\sigma)^{\star m} = \max(\Delta^{\star m}, \sigma^{\star m}) \lt \vartheta_m(\Delta+\sigma')`$, since $`\sigma^{\star m} \le \sigma \lt \sigma'`$
        and both $`\Delta^{\star m}`$ and $`\sigma'^{\star m}`$ are $`\lt \vartheta_m(\Delta+\sigma')`$. So the first disjunct of (C) gives
        $`\vartheta_m(\Delta+\sigma) \lt \vartheta_m(\Delta+\sigma')`$;
    - $`\beta = \Omega_{m+1} + \sigma`$ with $`\sigma \lt e_p`$: $`\vartheta_m(\beta) \lt e_p`$, by (C), since $`\sigma^{\star_m} \le \sigma`$.
  - So $`\mathcal T_m(j_0) \le \theta_m`$, and together with Mono\* ($`j_0\lang n\rang \lt_t j_0`$), $`\mathcal T_m(j_0) = \theta_m`$. This
    gives $`\mathrm{LC}_\mathrm{True}(j_0)`$.
- **Otherwise** (fix (b) of the referee's B1). Here the path child $`b`$ of $`j_0`$ is not a leaf,
  and $`y(b) = m+1`$. So every $`j_0\lang n\rang`$ is epsilon at level $`m`$.
  - $`\mathrm{LC}_\mathrm{True}(j_0)`$ is proved on $`T^1`$ directly, by induction on the size of $`\gamma`$. It is **not**
    proved as the ordinal equality $`\mathcal T_m(j_0) = \theta_m`$, which is not needed.
  - (The earlier text applied (Min) with $`\beta \in T^1`$. That was wrong for $`m \ge 1`$, as (Min) needs
    $`\beta \in T^{\Omega_m}`$; see [§1](TR.md).)

  <em>Proof.</em> Let $`\gamma \in T^1`$ with $`\gamma \lt \mathcal T_m(j_0)`$. If $`\gamma \lt \Omega_m`$, we are done. Otherwise let
  $`g = \vartheta_m(\beta)`$ be its leading term. Since $`\mathcal T_m(j_0\lang n\rang)`$ is additive principal, it suffices to
  show $`g \lt \mathcal T_m(j_0\lang n\rang)`$ for some $`n`$. By (C), with $`\alpha`$ the argument of $`\mathcal T_m(j_0)`$, there are two
  cases.

  - **(ii) $`g \le \alpha^{\star_m}`$.** By Lemma W with M4 ($`E = \mathcal T_m(j_0\lang n\rang)`$, an epsilon),
    $`\alpha^{\star_m} \lt \mathcal T_m(j_0\lang n\rang)`$. So $`g \lt \mathcal T_m(j_0\lang n\rang)`$.
  - **(i) $`\beta \lt \alpha`$ and $`\beta^{\star_m} \lt \mathcal T_m(j_0)`$.**
    - $`\beta^{\star_m} \in T^1`$ is a proper subterm of $`\gamma`$. By the IH, $`\beta^{\star_m} \lt \mathcal T_m(j_0\lang n_1\rang) \le \theta_m`$.
      So $`B_m(\beta)`$ holds.
    - Run the case analysis (i) of P-hi with $`a := j_0`$, $`c := b`$, $`B := B_m`$, using $`\mathrm{LC}_{B_m}(b)`$
      in X-form. This gives, for all large $`n`$, either $`\beta \lt \Delta_n + \eta_n`$, or directly
      $`g \lt \mathcal T_m(j_0\lang n\rang)`$ (the anchor sub-cases).
    - In the first alternative, (C) with $`\beta^{\star_m} \lt \mathcal T_m(j_0\lang n\rang)`$ ($`n \ge n_1`$) gives
      $`g \lt \mathcal T_m(j_0\lang n\rang)`$.
  - **Where $`\mathrm{LC}_{B_m}(b)`$ comes from.** It is proved on $`T^1`$ from $`(\mathrm{B}\ell)`$ by propagating up the
    region (S) with P-lo and P-hi. Every level in (S) is $`\ge m+1 \gt m`$, so P-hi applies
    with $`B = B_m`$. P-lo, P-hi and $`(\mathrm{B}\ell)`$ are all stated and proved for $`\gamma \in T^1`$, and they do
    not use (Min).
  - This completes the proof. ∎

**(Bdup) $`i_1 = 0`$, $`j_0 \ne r`$: $`\mathrm{LC}_\mathrm{True}(p(j_0))`$.**

- By (Exp), $`\mathcal T(j_0) = \mathcal T(j_0^-)\cdot\omega = \sup_n \mathcal T(j_0^-)\cdot n`$. This holds whether $`j_0^-`$ is non-epsilon,
  epsilon, or a leaf: the extra lo leaf contributes a final $`+1`$ to the exponent.
- **$`p(j_0)`$ non-epsilon:** $`Z_n = Z^- \oplus \mathcal T(j_0^-)\cdot n`$. Run the proof of P-lo with $`v = \mathcal T(j_0)`$ and
  $`v_n = \mathcal T(j_0^-)\cdot n`$.
  - $`v_n`$ is not principal. Instead: $`\xi' \lt v`$ gives $`\xi' \lt \mathcal T(j_0^-)\cdot n`$ for some $`n`$, hence
    $`\xi' + 1 \le \mathcal T(j_0^-)\cdot(n+1)`$.
  - $`K(\mathcal T(j_0^-)) \supseteq K(\mathcal T(j_0))`$, because $`\mathcal T(j_0^-) \lt \mathcal T(j_0)`$.
  - So $`\xi + 1 \le K(v) + \mathcal T(j_0^-)\cdot(n+1) \le Z_{n+1}`$.
- **$`p(j_0)`$ epsilon:** $`D(j_0^-) = D(j_0)`$, and $`\rho(j_0) = \rho(j_0^-) + 1`$. The run gains $`n`$ copies. As
  values, $`\eta_n \ge \Pi + (-1 + \omega^{\rho^-}\cdot n)`$, with $`\Pi`$ as in P-hi (and the convention
  $`-1 + 0 := 0`$). $`\eta = \Pi + \omega^{\rho^-+1}`$.
  - When $`C = \emptyset`$ and $`\rho^- = 0`$, the finite case gives $`\eta_n = \Pi + (n-1)`$. This is harmless,
    because only cofinality is used: $`\sup_n (-1 + \omega^{\rho^-}\cdot n) = \omega^{\rho^-+1}`$. The proof of P-hi
    goes through, with case (i) using the same $`\Delta`$.
  - $`\sigma \lt \eta`$ gives $`\sigma \lt \Pi + (-1 + \omega^{\rho^-}\cdot n) \le \eta_n`$ for some $`n`$.
  - The $`\star`$-condition is handled by the size IH, as in P-hi. ∎

### 4b.4 Proof of Theorem Cof

- **Start from a base:**
  - $`i_1 = 1`$: start from $`(\mathrm{B}j_0)`$, which is $`\mathrm{LC}_\mathrm{True}(j_0)`$;
  - $`i_1 = 0`$, $`j_0 \ne r`$: start from (Bdup);
  - $`i_1 = 0`$, $`j_0 = r`$: $`\mathcal T(t) = \mathcal T(\mathrm{Pred}\ t)\cdot\omega`$ (as in Bdup), and $`M[n]`$ ends with $`(\mathrm{Pred}\ t)^n`$.
- **Propagate** $`\mathrm{LC}_\mathrm{True}`$ upward to $`r`$ by P-lo and P-hi. Each step changes only the last
  child, by (A) and locality.
- At level 0, $`\mathrm{LC}_\mathrm{True}(r)`$ says: every $`T^1`$-term below $`\mathcal T(t)`$ lies below some $`\mathcal T(t\lang n\rang)`$. By (Seg),
  $`T^1 \cap \Omega_1`$ is an ordinal, so this is the ordinal equality $`\sup_n \mathcal T(t\lang n\rang) = \mathcal T(t)`$.
- Then $`\mathcal T(M[n]) = \mathcal T(\text{earlier roots}) \oplus \mathcal T(t\lang n\rang)`$, and ordinal addition is continuous in its
  right argument. ∎

**What is used.**

- CITED: (C), (Inc), (E), (Exp), (L), (Seg). (Min) is used only in the C1 sub-case of
  $`(\mathrm{B}j_0)`$, with the correct domain $`T^{\Omega_m}`$.
- PROVED here: Mono\*, M4, Lemma W, S-eps ([PROOF](PROOF-3.md) §13.0, from Mono\* and G\*).
- COMB ([COMB](COMB.md)): SC (Sib, G\*), Lemma 3 (locality), Lemma 9 (step-down), and the explicit form of
  `oper`, including (S).
- Lean: `oper_prefix`.
- **Not used:** [W24] Lemma 3.10, the $`\mathcal T`$-level substitution identity, LOC. LOC is proved
  independently in [PROOF](PROOF-3.md) §14.

### 4b.5 Evidence

An implementation of [W24] Def 3.1, 3.3 and 3.5 ($`\chi`$, $`d`$, support terms, fundamental
sequences) for $`T^1`$ on the terms of [tr.py](../por/tr.py) was used to check, for every limit standard matrix
with $`\le 7`$ columns (5,970 matrices):

- $`\mathcal T(M)[n] \lt \mathcal T(M)`$, increasing ($`n = 0..3`$);
- **$`\mathcal T(M)[n] \le \mathcal T(M[k])`$ for some $`k \le 8`$**, i.e. cofinality against Wilken's sequences.

There were 0 failures, and $`d(\mathcal T(M)) = 0`$ throughout.

- Exact equality $`\mathcal T(M)[n] = \mathcal T(M[n+s])`$ with a fixed shift $`s \in \{1, 2\}`$ holds in 4,372 of
  the 5,970 cases.
- In the others the sequences interleave. For example, for $`\varepsilon_1 = (0,0)(1,1)(1,1)`$,
  Wilken's sequence is $`\vartheta(\vartheta(\Omega)), \vartheta(\vartheta(\vartheta(\Omega))), \ldots`$ while $`\mathcal T(M[n]) = \vartheta(\vartheta(\Omega)+\vartheta(\Omega)), \ldots`$.
- So a literal substitution identity $`\mathcal T(M[n]) = \mathcal T(M)[n]`$ (the original S2(a)) is **false
  in general**. This is one reason the proof above works with cofinality instead.

## 5. Earlier evidence

- [PROOF](PROOF-2.md) §12.2 "Value": $`\mathrm{val}\ \mathcal T(N) = \iota(\Phi(N))`$ on 210,065 roots ([poral](https://github.com/semitrivial/poral)), consistent with TR.

## 6. Does $`\mathcal T`$ need adjusting?

- **No.** Theorem M is proved for $`\mathcal T`$ exactly as in [PROOF](PROOF-2.md) §12.1, including the $`e_p \gt \Delta^\star`$
  refinement.
- The proof shows why the refinement is harmless for monotonicity: M2 needs only that
  $`e_p`$ is dominated by a visible level-$`k`$ term of the argument. That term is $`e_p`$ itself, or
  the term $`\lambda`$ that absorbs it, or it comes from $`e_p \le \Delta^\star`$.
- The only side condition is standardness (valid terms). Section 2 shows it is
  necessary: the non-standard $`(0,0)(1,0)(2,1)`$ collides with $`\varepsilon_0`$.

## 7. For Lean

- **Theorem M:** structural induction on pairs of terms by total size, with the five
  cases of [§2](TR.md).
- Needs from $`T^1`$, as axioms or from a $`T^1`$ library:
  - the comparison (C), levels (L), (Exp) and (E);
  - an ANF library;
  - the COMB facts SC (G\*, Sib, Canon) and Lemma 10 style sequence monotonicity.
- **TR-red:** induction along `isWellOrder_ctpsLt`, with (Min) and (Inc) as cited axioms,
  and COMB Lemma R (cases A, B, C1, C2) and Lemma 5.
- **Cof:** induction on the size of $`\gamma`$ inside P-hi and in the general case of $`(\mathrm{B}j_0)`$. The
  path/region bookkeeping (S), (A) and the Positions fact are statements about `oper`.
  - Axioms needed: (C), (Inc), (Seg).
  - (Min) is needed only for the C1 sub-case of $`(\mathrm{B}j_0)`$, with domain $`T^{\Omega_m}`$. That sub-case
    could also be redone by the size induction of the general case.
- **TR:** induction along `isWellOrder_ctpsLt` with Cof and COMB Lemma 5.

---

## References

- [W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", Annals of Pure and Applied
  Logic 145 (2007) 130–161. doi:10.1016/j.apal.2006.07.003.
- [W24] G. Wilken, "Fundamental sequences based on localization", arXiv:2410.15953 (v4).
- [WW11] A. Weiermann, G. Wilken, "Ordinal arithmetic with simultaneously defined
  theta-functions", Mathematical Logic Quarterly 57 (2011) 116–132.
  doi:10.1002/malq.200910125.
- [COMB](COMB.md) and [PROOF](PROOF.md): the companion documents.
- [pss-proof](https://github.com/koteitan/pss-proof) and [Rank.lean](../Rank.lean): the Lean
  facts on standard pair sequences.

---

## Review history

An independent referee reviewed [§1](TR.md)–§4b of this document in two rounds: Theorem M (Mono\*,
with M1, M2, M4, Canon and the cases I–V), TR-red ([§3](TR.md)), Theorem Cof (§4b: the statements
$`\mathrm{LC}_B`$, Lemma W, P-lo, P-hi, and the bases), and the proof of TR from Cof. The
referee tried to refute each step and ran numerical attacks; they found 0
counterexamples. The referee's scale: FATAL (a claim is false), BLOCKING (a needed step
has no proof), MINOR (wording, bookkeeping, or a sketch that closes by a routine argument).

**First review.** No FATAL issue. One BLOCKING gap with a short repair, and nine MINOR
items.

- **B1 (BLOCKING).** The base $`(\mathrm{B}j_0)`$ at level $`m \ge 1`$ applied (Min) with the wrong
  quantifier domain. [W24] Prop 2.2 needs closure for all $`\beta \in T^{\Omega_m}`$, that is,
  with parameters below $`\Omega_m`$. The argument covered only $`\beta \in T^1`$, and
  $`T^1 \cap [\Omega_m, \Omega_{m+1})`$ is not an initial segment. So the step
  "$`\mathcal{T}_m(j_0) \le \theta_m`$" was unproved.
  Fixed by the referee's option (b):
  - The general case of $`(\mathrm{B}j_0)`$ is now an induction on the size of $`\gamma \in T^1`$,
    using (C), Lemma W with M4, and case (i) of P-hi with $`\mathrm{LC}_{B_m}(b)`$.
  - (Min) is no longer used there. Its quotation in [§1](TR.md) is corrected: $`\beta \in T^{\Omega_j}`$.
  - (Min) remains only in the C1 sub-case of $`(\mathrm{B}j_0)`$, where the closure is checked for
    $`\beta`$ with parameters, and at level 0 ([§3](TR.md)), where $`T^{\Omega_0} = T^1`$.
  - The final step at the root uses (Seg).
- **m1.** M4 is written out, with the invariant (I) over reached inner nodes and their
  child-prefixes (heads $`h`$, prefixes $`e_p'`$). The hypothesis "$`E`$ is an epsilon" is
  explicit, and its necessity is noted (9,153 cases).
- **m2.** The wording of M2 is fixed: an absorbed $`e_p`$ is dominated by a visible level-$`k`$
  term $`\lambda`$.
- **m3.** In (V), "prefix" now means the prefix of the children list; a block prefix is
  covered by the first-difference branch.
- **m4.** Positions excludes $`a = j_0`$ when $`i_1 = 0`$.
- **m5.** The second sub-case of P-hi is rewritten: the letter $`\Pi`$ replaces $`E`$; the
  reason the run is unchanged is corrected; $`\rho_c \gt 0`$ is stated;
  $`\zeta := \log(\text{leading term of } \sigma'')`$, and $`B(D_c + \zeta)`$ is justified.
- **m6.** The list of places where $`B`$ is passed on is completed (§4b.1).
- **m7.** (Bdup) uses $`n+1`$, and $`K(\mathcal{T}(j_0^-)) \supseteq K(\mathcal{T}(j_0))`$.
- **m8.** Citations: "COMB Lemma 2.1" became [PROOF](PROOF.md) Lemma 2.1 / [COMB](COMB.md)
  Lemma 5(a); (E) and (Inc) are cited through [W24] Lemma 2.4 and [§2.1](TR.md) for all levels; in
  [§3](TR.md), case C1 with $`k = 1`$: $`a := ()`$, $`o(a) := 0`$, $`\theta = \varepsilon_0`$.
- **m9.** [§3](TR.md) and [§4](TR.md) are marked as superseded by §4b.
- The stale docstring of [tr.py](../por/tr.py) was noted; the published copy states that the
  code handles all levels.

**Second review.** B1 is closed, and no new gap appears. No FATAL or BLOCKING finding.
Three MINOR items, all fixed:

- **r1.** (Seg) now cites [W07a] Theorem 3.23 (instead of Cor 3.24).
- **r2.** The C1 sub-case of $`(\mathrm{B}j_0)`$ gets the one-line derivation of (Inc) in
  $`T^{\Omega_m}`$ from (C).
- **r3.** The convention $`-1 + 0 := 0`$ for $`\Pi`$ when $`C = \emptyset`$. (Bdup) now states
  $`\eta_n \ge \Pi + (-1 + \omega^{\rho^-} \cdot n)`$, noting the off-by-one in the finite
  case; only cofinality is used.

The referee's verdict: TR ($`\mathrm{val} \circ \mathcal{T} = o`$) is proved. It follows from
Mono\* and Cof, the cited $`T^1`$ facts, and the pair-sequence lemmas of [COMB](COMB.md).
Theorem SC Part 2 is not used.

---

[Part 1: §0–§4](TR.md) | **Part 2: §4b–§7, References, Review history**
