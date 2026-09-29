[← Back](README.md)

# $`\Phi`$: standard pair sequences → $`R_1^+`$-patterns (proof, part 3 of 4)

[Part 1: §0–§10](PROOF.md) | [Part 2: §11–§12](PROOF-2.md) | **Part 3: §13–§14** | [Part 4: §15–§16, References, Review history](PROOF-4.md)

## 13. The four syntactic lemmas

New tools used in this section:

- **[COMB](COMB.md) Theorem SC** (§8b). A matrix is standard iff:
  - (R0) $`M_0 = (0,0)`$ and roots have $`y = 0`$;
  - (I0) $`x_{j+1} \le x_j + 1`$;
  - (A) $`y_c \le y_{p(c)} + 1`$;
  - (Sib) siblings have non-increasing terms;
  - (G\*) for every <em>descending</em> node $`u`$ ($`y_u \le y_{p(u)}`$): $`T(u) \lt_p T(v(u))`$, where $`v(u)`$ is
    the nearest proper ancestor with $`y \le y_u`$.
- **[COMB](COMB.md) Lemma C** (§8c; now PROVED): every blob $`\mathrm{Coll}_A(s|_i)`$ is standard.
- **Assumption Mono\*** (the level-$`k`$ form of TR's first half; now PROVED in [TR](TR.md) §2 as Theorem M):
  for every $`k`$, $`\mathcal{T}_k`$ is strictly increasing, with respect to $`\lt_p`$ on blocks, on the level-$`k`$
  terms that occur in standard matrices. The case $`k = 0`$ is TR's (Mono).
  - Every "PROVED" below that uses Mono\* is marked so.
- Sub-claims were also checked numerically.

### 13.0 Two basic lemmas

**Lemma S-eps (PROVED from G\* and Mono\*).** For a term $`s`$ of a standard matrix with
$`y(s) = k`$: $`s`$ is epsilon at level $`k`$ (its last child has $`y = k+1`$) $`\iff`$ $`\mathcal{T}_k(s)`$ is an epsilon
number of level $`k`$. (Checked on 200,945 terms.)

<em>Proof.</em>

- ($`\Rightarrow`$) By construction $`\mathcal{T}_k(s) = \vartheta_k(\Delta+\eta)`$ with $`\Delta \gt 0`$ ([W07a] Lemma 4.3).
- ($`\Leftarrow`$) Let $`s`$ be non-epsilon. Then $`\mathcal{T}_k(s) = \omega^Z`$ at level $`k`$, and it is an epsilon number iff
  $`Z`$ is a single level-$`k`$ epsilon $`\varepsilon`$ ($`\omega^\varepsilon = \varepsilon`$).
  - The last summand of $`Z`$ is $`\mathcal{T}(c)`$ for the last child $`c`$, and CNF addition never removes
    the last summand. So $`Z`$ single forces $`Z = \mathcal{T}_k(c)`$ with $`y(c) = k`$.
  - That $`c`$ is descending, with $`v(c) = s`$. So G\* gives $`T(c) \lt_p T(s)`$.
  - Mono\* then gives $`\mathcal{T}_k(c) \lt \mathcal{T}_k(s) = \omega^{\mathcal{T}_k(c)} = \mathcal{T}_k(c)`$, a contradiction. ∎

**Lemma $`\iota`$-exp (PROVED from [W07a] Lemma 4.2 (relativized: $`T^\alpha`$ has $`\Omega_0 = \alpha`$), Def 7.1,
Lemma 7.2(b)).** Let $`x \in T^\tau_\alpha`$ with $`x \ge \Omega_m`$, $`m \ge 1`$. Then, as values in $`T^\alpha`$,
$`\iota(\omega^x) = \omega^{\iota x}`$ and $`\iota(\log_\omega p) = \log_\omega(\iota p)`$. Here $`\omega^\cdot`$ is taken at level $`m`$ in $`T^\tau`$ and at
level $`m-1`$ in $`T^\alpha`$; for $`m = 1`$ this is the relativized level 0, with $`\Omega_0 := \alpha`$.

<em>Proof.</em> $`\omega^x = \vartheta_m(\mathrm{arg}(x))`$ with $`\mathrm{arg}`$ by the rule of [WW11] Lemma 2.12(b):
$`\mathrm{arg} = x - \Omega_m`$, or $`\varepsilon+n-1`$ when $`x = \varepsilon+n`$ with $`\varepsilon \in E_{\gt\Omega_m}`$. $`\iota`$ maps $`\vartheta_m \mapsto \vartheta_{m-1}`$
($`\vartheta_1 \mapsto \vartheta^\alpha`$). It maps $`\Omega_m \mapsto \Omega_{m-1}`$ ($`\Omega_1 \mapsto \alpha`$). It maps the level-$`m`$ epsilon numbers ($`\Delta' \gt 0`$)
onto the level-$`(m-1)`$ epsilon numbers of $`T^\alpha`$, and it fixes finite parts. So the case
distinction and the argument are carried over exactly. The value identity follows from
Lemma 4.2 in $`T^\tau`$ and in $`T^\alpha`$. ∎

In particular, all the "$`\varepsilon+n`$ / $`-1`$ / $`\Omega_0`$" adjustments of $`\mathcal{T}`$ commute with $`\iota`$, and the value of
$`t \circ \iota`$ is the value of $`\iota`$ ([W07a] Lemma 6.3: $`t`$ is value-preserving on $`T^\alpha_{\alpha^+}`$).

### 13.1 NS

**NS (PROVED from G\*, Sib, [COMB](COMB.md) Lemma 4, Mono\*).** Let $`N`$ be a standard epsilon root with
$`\mathcal{T}(N) = \vartheta_0(\Delta+\eta)`$. If $`\eta`$ is a sup-point ([W07a] Lemma 4.4: $`\eta = \vartheta_0(\Gamma+\rho)`$ with $`\Gamma \gt \Delta`$ and
$`\eta \gt \Delta^\star`$), then $`\rho_W = 0`$.

<em>Proof.</em>

1. **Which $`\eta`$ are sup-points.** $`\eta = [e_p +] (-1 + c)`$. A sup-point is a single principal
   term.
   - If $`e_p`$ is added and survives, then $`\eta`$ single forces $`-1 + c = 0`$, so $`c = 1`$ and
     $`\rho_W = 0`$.
   - Otherwise $`\eta = -1 + c = c`$ is a single term $`\omega^{\rho_W}`$. The last summand of $`c`$ is
     $`\omega^{\rho_W}`$; it is never removed, and the members of the run have non-increasing $`\rho`$ (Sib,
     Mono\*), so no absorption happens and the run is $`\{W\}`$.
   - Then $`\omega^{\rho_W}`$ is an epsilon, so $`\rho_W = \varepsilon`$ is an epsilon with $`\Gamma_\varepsilon \gt \Delta`$ and $`\varepsilon \gt \Delta^\star`$.
     Moreover, either there is no prefix, or $`\varepsilon \gt e_p`$.
2. **$`\varepsilon`$ comes from a unique child.** $`\rho_W`$ is the CNF sum of $`\mathcal{T}_0(E)`$ over the $`y = 0`$ children $`E`$
   of $`W`$. These are non-increasing (Sib, Mono\*), so no absorption happens. So $`W`$ has
   exactly one $`y = 0`$ child $`E`$, and $`\mathcal{T}_0(\mathrm{sh}\, E) = \varepsilon`$. Also $`\mathrm{sh}\, E \in R`$ ([COMB](COMB.md) Lemma 4), and it is
   epsilon (S-eps). Write $`\mathrm{sh}\, E = (0, B_1 \ldots B_b)`$ and $`N = (0, H_1 \ldots H_r)`$.
3. **G\* forces $`\mathrm{sh}\, E`$ below $`N`$.** $`E`$ is descending ($`y_E = 0 \le 1`$), with $`v(E) =`$ the root of $`N`$.
   So G\* gives $`\mathrm{sh}\, E \lt_p N`$, i.e. $`(B) \lt_{\mathrm{lex}} (H)`$ as sequences of blocks. Let $`H_{j+1} \ldots H_r`$ be
   $`N`$'s last run ($`D`$-part $`\Delta`$), and let $`i`$ be the first index where $`B`$ and $`H`$ differ.
   - **$`i \le j`$**, or $`B`$ is a proper prefix of $`(H_1 \ldots H_j)`$. Then $`(0,B) \lt_p (0,H_1 \ldots H_j)`$, which is
     an iterated anchor, hence standard. By Mono\*, $`\varepsilon \lt e_p`$. Then $`e_p`$ is not absorbed,
     and $`\eta = e_p + \varepsilon`$ is not a single term: no sup-point.
   - **$`B = (H_1 \ldots H_j)`$.** Then $`\varepsilon = e_p`$, and $`\eta = e_p + e_p`$ is not a single term.
   - **$`i \gt j`$.** Then $`B_i \lt_p H_i`$ with $`D(H_i) = \Delta`$. Mono\* at level 1 gives
     $`\mathcal{T}_1(B_i) \le \mathcal{T}_1(H_i)`$, and $`D`$-parts are monotone, so $`D(B_i) \le \Delta`$. Along $`B`$ the $`D`$-parts do
     not increase (Sib, Mono\*). So $`\varepsilon`$'s last-run $`D`$-part satisfies $`\Gamma = D(B_b) \le D(B_i) \le \Delta`$,
     against $`\Gamma \gt \Delta`$.
   - **$`B`$ is a proper prefix $`(H_1 \ldots H_b)`$ of $`(H_1 \ldots H_r)`$ with $`j \lt b \lt r`$** (M8).
     - $`\mathrm{sh}\, E = (0, H_1 \ldots H_b)`$ is an iterated anchor of $`N`$. Its last member $`H_b`$ lies in $`N`$'s
       last run, so $`D(H_b) = \Delta`$.
     - The last-run $`D`$-part of $`\varepsilon = \mathcal{T}(\mathrm{sh}\, E)`$ is therefore $`\Gamma = D(H_b) = \Delta`$, against $`\Gamma \gt \Delta`$.
     - ($`B = (H_1 \ldots H_r)`$ itself is impossible, since $`\mathrm{sh}\, E \lt_p N`$ is strict.)
   - **The case $`j = 0`$** ($`N`$ has no prefix before its last run).
     - The first two bullets are vacuous. $`B \ne ()`$, because $`\mathrm{sh}\, E`$ is epsilon and so has a
       child.
     - What remains is $`i \gt 0 = j`$, or $`B`$ a proper prefix of length $`b \gt 0 = j`$. These are
       the third and fourth bullets.
4. In every case we reach a contradiction. ∎

### 13.2 CI

**CI (PROVED from S-eps, $`\iota`$-exp, Mono\*, SC, [COMB](COMB.md) Lemma C, [W07a] Lemma 4.5, Cor 7.3,
Lemma 6.3, Lemma 7.2, and the sub-lemmas ND and LT below).** Value form: for a region
term $`s`$ ($`y(s) = m \ge 1`$, reached from $`W`$ through $`y \ge 1`$ ancestors, or a truncation of such a
term), $`\mathrm{val}\, \mathcal{T}_{m-1}(\mathrm{Coll}_A s) = \mathrm{val}\, \iota(\mathcal{T}_m s)`$.

<em>Proof.</em> Induction on (height, number of children) of $`s`$.

**Preliminary (B3).** Every level-0 subterm of $`\mathcal{T}_m(s)`$ is $`\lt \alpha`$, so $`\iota`$ is defined.

- These subterms come from constants, i.e. $`y = 0`$ nodes $`u`$ of the region. By G\* along the
  $`y = 0`$ chain up to the root, $`T(u) \lt_p N`$ ([COMB](COMB.md) K1). By Mono\*, $`\mathcal{T}(u) \lt \alpha`$.
- Their $`\vartheta_0`$-subterms are smaller still ([W07a] Lemma 3.30: $`\xi^\star \lt \vartheta(\xi)`$).

**Case $`m \ge 2`$.**

- Coll lowers $`s`$ and its region children by one level, blobs its $`y = 1`$ children, and keeps
  its $`y = 0`$ children.
- $`s`$ is epsilon at level $`m`$ $`\iff`$ $`\mathrm{Coll}(s)`$ is epsilon at level $`m-1`$: its last child's $`y`$ goes from
  $`m+1`$ to $`m`$, or from $`\le m`$ to $`\le m-1`$.
- Every clause in the definition of $`\mathcal{T}_m`$ is uniform in the level:
  - $`\Omega_m \mapsto \Omega_{m-1}`$;
  - $`\omega^\cdot`$ and $`\log`$ commute with $`\iota`$ ($`\iota`$-exp);
  - $`\iota`$ is additive on sums $`\gt \Omega_1`$;
  - the $`D`$-part/$`\rho`$ split at level $`m+1`$ goes to the split at level $`m`$;
  - runs are preserved because $`\iota`$ is injective;
  - $`\Delta^{\star_m} \mapsto \Delta^{\star_{m-1}}`$ ([W07a] Lemma 7.2(a)), and order is preserved (7.2(b)), so the test
    "$`e_p \gt \Delta^\star`$" is preserved.
- Each ingredient is by induction:
  - for the children of $`s`$;
  - for the truncation $`(m, \mathrm{hi})`$ or the prefix $`(m, H_1 \ldots H_j)`$, which are truncations of $`s`$;
  - constants are fixed.
- So the two constructions agree. The lowered children lists are Coll applied elementwise
  (no $`\oplus`$), and they do not increase ([COMB](COMB.md) Lemma 10).

**Domain condition for $`t`$ at $`m = 1`$ (M5).**

<em>Claim.</em> For every region term $`s`$ with $`y(s) = 1`$, including truncations: $`\iota(\mathcal{T}_1 s) \lt \alpha^+`$.
So $`\iota(\mathcal{T}_1 s) \in T^\alpha_{\alpha^+}`$, which is where $`t^\alpha_\tau`$ is the identity and value-correct
([W07a] Def 6.1, Lemma 6.3). For a principal level-0 term $`\xi`$, $`\xi^\star = \xi`$.

<em>Proof.</em>

1. **$`s \le_p W`$ as blocks.**
   - For $`s = W`$ this is trivial.
   - For another region node with $`y = 1`$: $`s`$ is descending, and the G\* chain of Claim Q
     (§14.1) gives $`T(s) \lt_p T(W)`$.
   - A truncation $`s|_i`$ is a prefix of $`s`$'s block, so $`s|_i \le_p s`$.
2. **Mono\* at level 1** gives $`\mathcal{T}_1(s) \le \mathcal{T}_1(W)`$. $`\iota`$ is order preserving ([W07a] Cor 7.3), so
   $`\iota(\mathcal{T}_1 s) \le \iota(\mathcal{T}_1 W)`$.
3. **$`W`$ epsilon at level 1.** Then $`X_W = \mathcal{T}_1(W)`$, so $`D(W) = \mathcal{T}_1(W)`$ and $`\rho_W = 0`$. $`W`$ is in the
   last run, so $`\Delta = \mathcal{T}_1(W)`$, and $`\iota(\mathcal{T}_1 W) = \iota(\Delta) \lt \alpha^+`$ by [W07a] Cor 7.3.
4. **$`W`$ not epsilon at level 1.**
   - $`\mathcal{T}_1(W) = \omega^{Z_W}`$ with $`Z_W = X_W = \Delta + \rho_W`$.
   - By $`\iota`$-exp, $`\iota(\mathcal{T}_1 W) = \omega^{\iota(\Delta) + \rho_W}`$. Here $`\rho_W \lt \alpha`$ is fixed by $`\iota`$ (preliminary B3).
   - $`\iota(\Delta) \lt \alpha^+`$ (Cor 7.3) and $`\rho_W \lt \alpha \lt \alpha^+`$.
   - $`\alpha^+ = \vartheta(\Delta+\eta+1)`$ is an epsilon number ($`\Delta \gt 0`$, [W07a] Lemma 4.3). So
     $`\iota(\Delta) + \rho_W \lt \alpha^+`$ and $`\omega^{\iota(\Delta)+\rho_W} \lt \alpha^+`$. ∎

The same bound covers the arguments: their $`\vartheta^\alpha`$-subterms are below the principal term
([W07a] Lemma 3.30). So both $`m = 1`$ cases below may translate by $`t`$.

**Case $`m = 1`$, $`s`$ non-epsilon at level 1.**

- $`\mathcal{T}_1(s) = \omega^Z`$ with $`Z = [\mathcal{T}_1((1,\mathrm{hi}\, s)) \text{ or } \Omega] + \sum_{c:\, y \le 1} \mathcal{T}(c)`$.
- $`\mathrm{Coll}(s) = (0, A \oplus \pi)`$. Its last child is a blob or a constant ($`y = 0`$), so it is
  non-epsilon, and $`\mathcal{T}_0(\mathrm{Coll}\, s) = \omega^{\mathcal{T}(\mathcal{L}\, \mathrm{Coll}\, s)}`$ (Lemma R).
- $`\mathrm{hi}(\mathrm{Coll}\, s) = A \mathbin{+\!\!+} \mathrm{Coll}(\mathrm{hi}\, s)`$:
  - if $`\mathrm{hi}\, s \ne \emptyset`$, by **ND**;
  - if $`\mathrm{hi}\, s = \emptyset`$, then $`\pi_1`$ has $`y = 0`$, so it is smaller than every element of $`A`$, and
    nothing of $`A`$ is dropped.
- So $`\mathcal{L}(\mathrm{Coll}\, s) = (0, A \mathbin{+\!\!+} \mathrm{Coll}(\mathrm{hi}\, s)) +`$ (the blobs and constants).
  - Its first term is $`\mathrm{Coll}((1, \mathrm{hi}\, s))`$, with value $`\iota\mathcal{T}_1((1, \mathrm{hi}\, s))`$ by induction; or it is
    $`N`$, with value $`\alpha = \iota(\Omega)`$.
- Hence $`\mathcal{T}(\mathcal{L}\, \mathrm{Coll}\, s) = \iota Z`$ as values, and $`\mathcal{T}_0(\mathrm{Coll}\, s) = \omega^{\iota Z} = \iota(\omega^Z)`$ ($`\iota`$-exp).

**Case $`m = 1`$, $`s`$ epsilon at level 1** (children $`D_1 \ldots D_n`$, all $`y = 2`$).

- $`\mathrm{Coll}(s) = (0, A \mathbin{+\!\!+} \mathrm{Coll}(D_1 \ldots D_n))`$ by ND. Every $`\mathrm{Coll}(D_i)`$ has $`y = 1`$, so this is an
  epsilon root.
- Its monomials:
  - for $`\mathrm{Coll}(D_i)`$: $`\log \mathcal{T}_1(\mathrm{Coll}\, D_i) = \iota \log \mathcal{T}_2(D_i)`$, by induction and $`\iota`$-exp;
  - so $`D'_i = \iota(D_i^{(2)})`$ and $`\rho'_i = \iota(\rho_i^{(2)})`$;
  - runs are preserved.
- **S-run.** The last run contains no element of $`A`$. (Checked on 28,467 cases.)
  - By **LT**, $`\mathrm{Coll}(s) \lt_p N^+ := (0, A \mathbin{+\!\!+} [W'])`$, where $`W'`$ is $`W`$ without its $`y = 0`$ children.
  - $`N^+`$ is standard by SC: it is $`A`$ followed by a prefix of $`W`$'s block.
  - $`\mathcal{T}(N^+) = \vartheta(\Delta + \eta + 1) = \alpha^+`$: the run gets one more summand $`\omega^0`$. This is **Lemma N⁺
    ([§15.2](PROOF-4.md), M10), proved from the definition of $`\mathcal{T}`$**, and checked on 75,328 cases.
  - Also $`\mathrm{Coll}(s) \gt_p N`$ ([COMB](COMB.md) K2). By Mono\*, $`\alpha \lt \mathcal{T}(\mathrm{Coll}\, s) \lt \alpha^+`$.
  - By [W07a] Lemma 4.5, the level $`\Delta_Y`$ of $`\mathcal{T}(\mathrm{Coll}\, s)`$ is $`\lt \Delta`$.
  - But every $`H \in A`$ has $`D(H) \ge \Delta`$ (Sib, Mono\*, $`D`$-parts monotone). So no element of $`A`$ can
    be in the last run.
- **The prefix rule matches [W07a] Def 6.2.**
  - If the run is all of $`\mathrm{Coll}(D_1 \ldots D_n)`$, the prefix of the blob is $`A`$, so $`e_p = \alpha`$. It is
    added iff $`\alpha \gt \Delta^\star_Y`$, iff $`\Gamma := \iota(\Delta_s)`$ contains no $`\vartheta^\alpha`$-subterm. That is Def 6.2's split
    between "$`\Gamma^\star \lt \alpha`$" ($`t`$ gives $`\vartheta(\Gamma^t + \alpha + \rho^t)`$) and "$`\Gamma^\star \ge \alpha`$" ($`t`$ gives $`\vartheta(\Gamma^t + \rho^t)`$).
  - If the run starts later, the prefix is $`A \mathbin{+\!\!+} \mathrm{Coll}(D_1 \ldots D_j)`$. By induction on the
    truncation, its value is $`\iota\mathcal{T}_1((1, D_1 \ldots D_j)) = \iota(e_p^s)`$. The test "$`e_p \gt \Delta^\star`$" carries
    over by 7.2(a, b).
  - The coefficient is $`c' = \iota(c_s)`$.
- So $`\mathcal{T}_0(\mathrm{Coll}\, s) = \vartheta_0(\iota(\Delta_s) + \iota(\eta_s))`$ as values, which is $`\iota(\mathcal{T}_1 s)`$. ∎

**Sub-lemmas used by CI (PROVED in §14.1).**

- **ND.** $`A \oplus \mathrm{Coll}(\mathrm{ch}\, s)`$ drops no element of $`A`$, i.e. $`W \ge \mathrm{Coll}(\text{first child of } s)`$. Checked
  on 200,120 cases.
- **LT.** $`\mathrm{Coll}(s) \lt_p N^+`$. Given ND, this says $`\mathrm{Coll}(\text{first child of } s) \lt_p W'`$. Checked on
  200,120 cases.

Both are lex statements about region terms under Coll, of the same kind as [COMB](COMB.md)
Lemma 10 (Coll is strictly monotone).

- When the first child $`c`$ of $`s`$ has $`y \le 1`$, both are immediate: $`\mathrm{Coll}(c)`$ has $`y = 0`$ and
  $`W`$, $`W'`$ have $`y = 1`$.
- The remaining case is $`y(c) = 2`$, where $`\mathrm{Coll}(c) = (1, \mathrm{Coll}(\mathrm{ch}\, c))`$ must be compared with
  the children of $`W`$. This needs an induction like [COMB](COMB.md)'s proof of Lemma 10.

### 13.3 $`\mathrm{Bar}_T`$

**$`\mathrm{Bar}_T`$.** For a standard epsilon $`N`$ with $`k`$ children: $`\mathrm{bar}(\mathcal{T}N) = \mathcal{T}(\mathrm{anchor}\, N)`$ if $`k \ge 2`$, and
$`\mathrm{bar}(\mathcal{T}N) = 1`$ if $`k = 1`$. (Checked on 30,562 cases.)

**(a) $`W`$ shares its run with $`H_{k-1}`$: PROVED (Mono\*, Sib; [CW12] Def 5.1).**

- $`c = c_a + \omega^{\rho_W}`$ without absorption ($`\rho`$ does not increase within a run). So $`\eta' = \eta_a`$
  and $`\eta_0 = \omega^{\rho_W}`$.
- $`\eta' = \eta_a`$ is the $`\eta`$ of the anchor $`a`$, which is a standard epsilon root.
- **If $`\eta'`$ is a sup-point** (corrected, M9):
  - NS (§13.1), applied to $`a`$ (whose last child is $`H_{k-1}`$), gives $`\rho_{k-1} = 0`$.
    - Without NS this step fails: $`c_a = \omega^{\rho_{k-1}}`$ could itself be a sup-point.
  - $`\rho`$ does not increase within a run, so $`\rho_W = 0`$.
  - $`W`$ shares its run with $`H_{k-1}`$, so $`c`$ has at least two summands. Its last summand is
    $`\omega^0`$, and the last term of $`\eta = [e_p +](-1 + c)`$ is 1. So $`\eta_0 = 1`$.
- Either way Def 5.1's first case applies: $`\mathrm{bar} = \vartheta(\Delta + \eta') = \mathcal{T}(\mathrm{anchor})`$.

**(b) $`W`$ alone in its run, part 1: PROVED (Mono\*, SC).** $`\alpha \in (e_p, e_p^+)`$, where
$`e_p = \mathcal{T}(\mathrm{anchor})`$.

- Let $`H' :=`$ $`H_{k-1}`$ without its $`y = 0`$ children, and $`a^+ := (0, H_1 \ldots H_{k-1}, H')`$. This is
  standard by SC, and $`\mathcal{T}(a^+) = e_p^+`$ by Lemma N⁺ ([§15.2](PROOF-4.md), M10) applied to the anchor.
  Here $`W`$ alone in its run means $`e_p = \mathcal{T}(\mathrm{anchor})`$.
- $`D(H_{k-1}) \gt D(W)`$. $`D`$-parts are $`\Omega`$-multiples, so $`X_{H'} = D(H_{k-1}) \ge D(W) + \Omega \gt X_W`$.
- Hence $`\mathcal{T}_1(W) \lt \mathcal{T}_1(H')`$. Mono\* makes lex and value orders agree, so $`W \lt_p H'`$, $`N \lt_p a^+`$,
  and $`\alpha \lt e_p^+`$. Also $`\alpha \gt e_p`$, since $`N \gt_p \mathrm{anchor}`$.

**(b) part 2: reduced to LOC′ (PROVED in §14.2).**

- By [W07a] Lemma 6.5, the $`\tau`$-localization of $`\alpha`$ is the $`\tau`$-localization of $`e_p`$ followed by
  the $`e_p`$-localization of $`\alpha`$.
- By Lemma 4.9 and Lemma 6.4(b), $`\alpha_{n-1} = e_p`$ iff no $`\vartheta_0`$-subterm $`\nu`$ of $`\alpha`$ with
  $`e_p \lt \nu \lt \alpha`$ has an argument larger than $`\Delta + \eta`$.
- **LOC′:** every $`\vartheta_0`$-subterm $`\nu`$ of $`\eta`$ with $`\nu \gt e_p`$ has argument $`\lt \Delta + \eta`$. Such $`\nu`$ come from
  the $`y = 0`$ children of $`W`$. This is an NS-type statement; the argument of §13.1 handles
  $`\nu = \rho_W`$ itself, and deeper subterms still need it. The conclusion $`\alpha_{n-1} = e_p`$ is
  checked on 11,535 cases.
- The case $`e_p \le \Delta^\star`$ (e.g. $`\psi_0(\Omega^\Omega + \Omega^{\Gamma_0}) = \vartheta(\vartheta_1(\Gamma_0))`$) is covered by the same Lemma
  6.5 argument, with $`e_p`$ a subterm of $`\Delta`$.

**(c) $`k = 1`$: reduced to LOC″ (PROVED in §14.2).**

- With no prefix, $`\eta = -1 + \omega^{\rho_W}`$. Def 5.1 gives $`\vartheta(\Delta + \eta')`$ or $`\alpha_{n-1}`$. The value 1 can
  only arise as $`\alpha_{n-1}`$, so $`\mathrm{bar} = 1`$ iff the $`\tau`$-localization of $`\alpha`$ is exactly $`(1, \alpha)`$.
- **LOC″:** no $`\vartheta_0`$-subterm of $`\Delta + \eta`$ has an argument larger than $`\Delta + \eta`$.
- The numerical result $`\mathrm{bar}(\mathcal{T}N) = 1`$ for all 27,950 single-child epsilon roots implies
  LOC″ on those cases.
- LOC′ and LOC″ are the same kind of statement: they bound the arguments of the
  $`\vartheta_0`$-subterms that come from region terms and from $`y = 0`$ children of $`W`$.

So $`\mathrm{Bar}_T`$: (a) and part 1 of (b) are PROVED here. LOC′ (the rest of (b)) and LOC″
(case (c)) are PROVED in §14.2. So $`\mathrm{Bar}_T`$ is PROVED.

### 13.4 $`\mathrm{E2}_T`$

**$`\mathrm{E2}_T`$ (reduced here; PROVED in §14.3, with M6 of [§15.2](PROOF-4.md); checked on 110,778 jumps).** Let $`Y`$ be a jump input and $`\beta := \mathcal{T}(Y)`$.
By CI, Lemma 6.5 and [W07a] Lemma 7.2(a), the intermediate elements $`\beta_i`$ of the
$`\alpha`$-localization of $`\beta`$ are the values $`\mathcal{T}(\mathrm{Coll}\, s')`$ of <em>sub-blobs</em>: blobs of region terms $`s'`$
strictly inside the collapsed term $`s`$, including truncations. $`\mathrm{E2}_T`$ says that no sub-blob
has $`\lambda \ge \beta`$.

- **Given TR, the semantic content is PROVED.**
  - Let $`\xi`$ be the $`\kappa`$-index reached before $`Y`$, and $`K(\xi) = \mathrm{lh}(\kappa^\alpha_\xi)`$.
  - A sub-blob $`\beta_i \le K(\xi)`$ lies in some component $`[\kappa_{\xi'}, \mathrm{lh}\, \kappa_{\xi'}]`$ with $`\xi' \le \xi`$. If
    $`\beta_i \le_1 \beta`$, then $`\kappa_{\xi'} \le_1 \beta_i \le_1 \beta`$, so $`\beta \le \mathrm{lh}(\kappa_{\xi'}) \le K(\xi) \lt \beta`$. Contradiction.
- (The covering argument above is corrected in §14.3 and M6(b).)
- **What was left at that stage** (closed by PL, §14.3): sub-blobs in the interval
  $`(K(\xi), \beta)`$.
  - Example: $`Y_2 = \mathrm{Coll}(W|_2)`$ has the sub-blob $`\mathrm{Coll}(W|_1) = Y_1`$. Since $`Y_2`$ is a jump,
    $`Y_1 \le K(\xi)`$.
  - A general argument needs every sub-blob of a jump input to lie below $`K(\xi)`$. That means
    comparing sub-blobs with earlier fold inputs lexicographically, as in [COMB](COMB.md)'s
    Lemma C proof.

### 13.5 Intermediate status (superseded; see [§0](PROOF.md) and [§16](PROOF-4.md))

| item | status |
|---|---|
| S1, R, Lemma 6, T, Theorem SC, Lemma C, Lemma 2.4 | PROVED ([COMB](COMB.md)) |
| S-eps, NS, $`\iota`$-exp | PROVED (NS, S-eps from Mono\*) |
| CI | PROVED from Mono\* + sub-lemmas **ND, LT** (OPEN, 200k checks each) |
| $`\mathrm{E1}_T`$ | PROVED from CI ([§12.5](PROOF-2.md); NS is now proved) |
| $`\mathrm{Bar}_T`$ | (a) and (b) part 1 PROVED; **LOC′** (11.5k checks) and **LOC″** (27.9k checks) OPEN |
| $`\mathrm{E2}_T`$ | semantic core PROVED given TR; the sub-blob placement is **OPEN** (110k checks) |
| TR, including Mono\* | OPEN at that stage; now PROVED in [TR](TR.md) |

The Main Theorem follows from TR (with Mono\*) + ND + LT + LOC′ + LOC″ + (the $`\mathrm{E2}_T`$ placement),
together with everything PROVED or CITED above.

---

## 14. The remaining combinatorial pieces

Conventions:

- $`N`$ is a standard epsilon root, $`N = (0, A)`$, $`A = (H_1 \ldots H_r)`$, $`W = H_r`$, $`\alpha = \mathcal{T}(N) = \vartheta_0(\Delta+\eta)`$.
- $`H_{j+1 \ldots r}`$ is the last run. $`e_p = \mathcal{T}((0,H_1 \ldots H_j))`$, or 1 if $`j = 0`$.
- The **region** is the set of nodes reached from $`W`$ (or from any run member) through
  ancestors with $`y \ge 1`$.
- A **constant** is a $`y = 0`$ node whose parent is in the region.
- Blocks are compared by $`\lt_p`$, normalized to $`x = 0`$.
- "Mono\*" is the assumption of §13 (now [TR](TR.md) Theorem M).
- Checks: numerical checks of P′, Q, LV and PL on the generated test sets with maximal $`y = 2, 3`$.

### 14.1 ND and LT (PROVED; syntactic + [COMB](COMB.md) Theorem SC)

**Claim P′ (PROVED; purely syntactic).** Let $`x`$ be a region node, a child of $`p`$, with
$`y(x) = y(p) + 1 =: m + 1 \ge 2`$. Then $`\mathrm{Coll}(x) \lt_p (m, [x])`$, the block with root $`y = m`$ and
single child $`x`$. (Checked on 73,161 cases.)

<em>Proof.</em> Induction on the height of $`x`$. $`\mathrm{Coll}(x) = (m, \mathrm{Coll}(\mathrm{ch}\, x))`$. Compare the child
sequences $`\mathrm{Coll}(\mathrm{ch}\, x)`$ and $`[x]`$.

- **$`\mathrm{ch}\, x = \emptyset`$:** $`(m)`$ is a proper prefix of $`(m, [x])`$.
- **Otherwise,** let $`x_1`$ be the first child; $`y(x_1) \le m + 2`$ by (A).
  - $`y(x_1) \le 1`$: $`\mathrm{Coll}(x_1)`$ has $`y = 0`$ (blob or constant), which is below $`x`$'s head $`y = m+1`$.
  - $`2 \le y(x_1) \le m+1`$: $`\mathrm{Coll}(x_1)`$ has $`y \le m \lt m+1`$.
  - $`y(x_1) = m+2`$: by induction $`\mathrm{Coll}(x_1) \lt_p (m+1, [x_1]) \le_p x`$, since $`(m+1, [x_1])`$ is a
    prefix of $`x`$'s block.
- In every case the first elements satisfy $`\mathrm{Coll}(x_1) \lt_p x`$. A strict difference in the
  first child block decides the whole block comparison (as in Lemma 2.1: when a block is
  a proper prefix, the next column is a sibling head at depth 1, which is shallower than
  the deeper columns of the other block). ∎

**Claim Q (PROVED from G\*).** Let $`s`$ be a region node with $`y(s) = 1`$ whose first child $`c`$
has $`y = 2`$. Then $`c \le_p w_1`$, the first child of $`W`$, and $`y(w_1) = 2`$. (Checked on 58,094 cases.)

<em>Proof.</em>

- If $`s = W`$, then $`c = w_1`$.
- Otherwise $`s`$ is descending (its parent is a region node with $`y \ge 1`$), and $`v(s)`$ is the
  nearest $`y = 1`$ ancestor on the path to $`W`$.
- G\* gives $`T(s) \lt_p T(v(s))`$; iterating up the chain, $`T(s) \lt_p T(W)`$. So $`\mathrm{ch}(s) \le_{\mathrm{lex}} \mathrm{ch}(W)`$,
  and in particular the first children satisfy $`c \le_p w_1`$.
- $`y(c) = 2`$ and $`c \le_p w_1`$ force $`y(w_1) \ge 2`$, hence $`= 2`$ by (A). ∎

**ND and LT (PROVED).** Let $`\pi = \mathrm{Coll}(\mathrm{ch}(s)[:i])`$, $`i \ge 1`$, and $`W' = (1, \text{the } y \ge 1 \text{ children of } W)`$, which is a prefix of $`W`$'s block.

- **$`y(c) \le 1`$:** $`\pi_1 = \mathrm{Coll}(c)`$ has $`y = 0 \lt 1`$. So $`\pi_1 \lt_p W' \le_p W`$.
- **$`y(c) = 2`$:** $`\pi_1 = \mathrm{Coll}(c) \lt_p (1, [c]) \le_p (1, [w_1]) \le_p W' \le_p W`$, by P′ and Q. Here $`w_1`$ is
  the first child of $`W'`$.
- **ND:** $`A \oplus \pi`$ drops the trailing elements of $`A`$ below $`\pi_1`$. Since $`\pi_1 \lt W`$, the last element
  of $`A`$, nothing is dropped.
- **LT:** $`\mathrm{Coll}(s|_i) = (0, A \mathbin{+\!\!+} \pi) \lt_p (0, A \mathbin{+\!\!+} [W']) = N^+`$, because $`\pi_1 \lt_p W'`$. (For $`i = 0`$ it
  is $`N`$ itself.) ∎

**Consequence.** CI is **PROVED** (from Mono\*, SC, [COMB](COMB.md) Lemma C and the [W07a] lemmas
of §13.2).

### 14.2 LOC′ and LOC″, hence $`\mathrm{Bar}_T`$ (PROVED from Mono\*, SC, [COMB](COMB.md) Lemma 4)

**Lemma CL (PROVED; structural induction on the clauses of $`\mathcal{T}`$).** Every $`\vartheta_0`$-subterm of
$`\mathcal{T}(N)`$ other than $`\mathcal{T}(N)`$ and 1 is one of:

- a $`\vartheta_0`$-subterm of $`e_p`$ (from the $`\eta`$-clause);
- a $`\vartheta_0`$-subterm of $`\mathcal{T}(\mathrm{sh}\, u)`$ for a constant $`u`$ in the region of a last-run member;
- a non-epsilon term $`\omega^\rho`$ ($`\omega^{\cdot}`$ at level 0 of a level-0 coefficient $`\rho`$).

Reason: the clauses of $`\mathcal{T}_k`$ only combine the values or logs of children. Level-0 terms
enter only as values of constants, or through $`\omega^{\cdot}`$ of level-0 coefficients. $`\log`$ and $`\omega^{\cdot}`$ at
levels $`\ge 1`$, the $`D`$/$`\rho`$ split, "$`-1+`$" and $`\Omega_k`$ add no new $`\vartheta_0`$-terms. The level-$`k`$ prefixes and
hi-truncations consist of the same region nodes.

**Lemma EL (PROVED; [W07a] Lemma 3.30, and $`\xi \lt \vartheta(\Delta+\xi)`$ for $`\Delta \gt 0`$).** Let $`\mu`$ be a proper
$`\vartheta_0`$-subterm of $`\alpha`$ with $`\mathrm{level}(\mu) = \Delta`$, i.e. $`\mu = \vartheta_0(\Delta + \eta_\mu)`$. Then $`\eta_\mu \lt \eta`$, so
$`\mathrm{arg}(\mu) \lt \mathrm{arg}(\alpha)`$.

<em>Proof.</em>

- Terms denote ordinals uniquely, so $`\mu`$'s term contains the term $`\Delta`$.
- Hence $`\mu`$ is not a subterm of $`\Delta`$: otherwise $`\Delta`$ would be a proper subterm of itself. So $`\mu`$
  lies inside a summand $`p`$ of $`\eta`$.
- Then $`\mu \le p \le \eta`$ (proper $`\vartheta_0`$-subterms of $`p`$ are $`\lt p`$ by Lemma 3.30).
- Also $`\eta_\mu \lt \mu`$ (fixed-point freeness). So $`\eta_\mu \lt \eta`$. ∎

**Lemma FD (PROVED by induction on $`\lvert M \rvert`$; uses G\*, Sib, Mono\*, [COMB](COMB.md) Lemma 4 and the
standardness of anchors).** For every standard one-root $`M \lt_p N`$: every epsilon $`\vartheta_0`$-subterm
$`\nu`$ of $`\mathcal{T}(M)`$, including $`\mathcal{T}(M)`$ itself, satisfies $`\nu \le e_p`$ or $`\mathrm{level}(\nu) \le \Delta`$.

<em>Proof.</em> Write $`M = (0, B_1 \ldots B_b)`$, and let $`i`$ be the first index where $`B`$ and $`(H_1 \ldots H_r)`$
differ.

- **(1) $`i \le j`$, or $`B`$ is a prefix of $`(H_1 \ldots H_j)`$.** Then $`M \le_p (0, H_1 \ldots H_j)`$, which is
  standard, so $`\mathcal{T}(M) \le e_p`$ by Mono\*. All its subterms are smaller.
- **(2) Otherwise** $`B_t = H_t`$ for $`t \lt i`$ with $`i - 1 \ge j`$, and either $`B_i \lt_p H_i`$, or
  $`B = (H_1 \ldots H_{i-1})`$ with $`i - 1 \gt j`$.
  - $`\mathcal{T}(M)`$, if epsilon, has level $`D(B_b) \le D(B_i) \le D(H_i) = \Delta`$, or level $`D(H_{i-1}) = \Delta`$.
    This uses Sib + Mono\*: $`D`$-parts are monotone and do not increase along siblings.
  - By CL applied to $`M`$, its other epsilon subterms lie in $`e_p(M)`$ or in $`\mathcal{T}(\mathrm{sh}\, u')`$ for
    constants $`u'`$ of $`M`$. If $`M`$ is non-epsilon, they lie in $`\mathcal{T}`$ of the root terms of $`\mathcal{L}M`$.
  - The matrices $`(0, B_1 \ldots B_{j_M})`$, $`\mathrm{sh}\, u'`$, $`(0, \mathrm{hi}\, M)`$ and $`\mathrm{sh}\, c`$ are all standard ([COMB](COMB.md)
    Lemma 4, anchors) and $`\lt_p M`$ (prefix, or G\*), hence $`\lt_p N`$ and smaller.
  - The induction hypothesis applies to them. ∎

**Lemma LV (PROVED).** Every epsilon $`\vartheta_0`$-subterm $`\nu \ne \alpha`$ of $`\alpha`$ satisfies $`\nu \le e_p`$ or
$`\mathrm{level}(\nu) \le \Delta`$. (Checked on 79,116 cases.)

- By CL, $`\nu`$ lies in $`e_p`$, or in $`\mathcal{T}(\mathrm{sh}\, u)`$ for a constant $`u`$ of a run member.
- In the latter case G\* gives $`\mathrm{sh}\, u \lt_p N`$, since $`v(u)`$ is the root. Then FD applies.

**LOC′ and LOC″ (PROVED).** Let $`\nu`$ be a $`\vartheta_0`$-subterm of $`\alpha`$ with $`e_p \lt \nu \lt \alpha`$ (in case (c),
$`e_p = 1`$). Then:

- if $`\nu`$ is non-epsilon, its argument is countable, hence $`\lt \Delta \le \mathrm{arg}(\alpha)`$;
- if $`\nu`$ is epsilon, LV gives $`\mathrm{level}(\nu) \le \Delta`$; level $`\lt \Delta`$ gives a smaller argument, and level
  $`= \Delta`$ gives a smaller argument by EL.

So $`\alpha`$ has the maximal argument among the $`\vartheta_0`$-subterms above $`e_p`$.

- **(b) $`W`$ alone.** $`\alpha \in (e_p, e_p^+)`$ (§13.3), and $`e_p \in P(\alpha)`$. [W07a] Lemma 6.5 with
  6.4(b), (c): the $`\tau`$-localization of $`\alpha`$ is that of $`e_p`$ followed by the $`e_p`$-localization of
  $`\alpha`$, whose next element is $`\alpha`$. So $`\alpha_{n-1} = e_p`$.
- **(c) $`k = 1`$.** The $`\tau`$-localization of $`\alpha`$ is $`(1, \alpha)`$.

**$`\mathrm{Bar}_T`$ (PROVED from Mono\*).**

- Case (a) is §13.3.
- In cases (b) and (c), Def 5.1 always falls into its second case:
  - $`\rho_W = 0`$ gives $`\eta \in \{e_p, 0\}`$;
  - $`\rho_W \gt 0`$ gives $`\eta = e_p + \omega^{\rho_W}`$ ($`\eta' = e_p`$ is a sup-point), or $`\eta = \omega^{\rho_W}`$ ($`\eta' = 0`$).
- Then $`\mathrm{bar} = \alpha_{n-1} = e_p = \mathcal{T}(\mathrm{anchor}\, N)`$, or 1 when $`k = 1`$. ∎

So **bar-closure of $`o[V_M]`$ holds given TR**: $`V`$ is closed under anchor, and non-epsilon
nodes are handled by [§11.3](PROOF-2.md). Isominimality then follows via Route A (Thm 11.1).

**Lean.** $`\mathrm{Bar}_T`$ is `barEps` in [Main/BarEps.lean](../Main/BarEps.lean), with no `sorry`, by a route that does not use CL, FD, LV or N⁺: the lemma KEY (`key_eps_root`), EL (`argV_lt_of_level_eq`) and [W07a] Lemma 6.4 (a) on $`T^1`$ (`mem_sub0_of_between`, proved from (C)) are in [Main/EpsRoots.lean](../Main/EpsRoots.lean).

### 14.3 $`\mathrm{E2}_T`$ placement (PROVED from Mono\*, LV, SC, [COMB](COMB.md) Lemma 10 and Lemma C)

**PL.** For a jump input $`Y`$ with $`\beta = \mathcal{T}(Y)`$: every intermediate element $`\beta_i`$ of the
$`\alpha`$-localization of $`\beta`$ satisfies $`\beta_i \le K`$, where $`K = \mathrm{val}\, S`$ is the reach before the jump.
(Checked on 3,420 elements.)

<em>Proof.</em>

- **(0) What an intermediate element is.** By [W07a] Lemma 6.5 and 6.4(b), $`\beta_i`$ is a
  $`\vartheta_0`$-subterm of $`\beta`$ above $`\alpha`$. By Lemma 4.9, the levels along a localization strictly
  decrease. So:
  - $`\mathrm{level}(\beta_i) \gt \mathrm{level}(\beta) \gt 0`$ if $`\beta`$ is epsilon;
  - $`\beta_i`$ is an epsilon number if $`\beta`$ is not (level 0).
- **(1) Earlier fold inputs are $`\le K`$.** The fold's $`S`$ covers each input: an input is either
  added or jumped to $`\mathrm{lh}(\text{input})`$. All $`D`$-inputs $`Y_1 \ldots Y_p`$ come before the $`E`$-inputs.
- **(2) $`\beta`$ epsilon.**
  - $`Y`$ is a standard epsilon root ([COMB](COMB.md) Lemma C), so LV applies to $`Y`$ itself. Every
    epsilon subterm of $`\mathcal{T}(Y)`$ with level $`\gt \Delta_Y`$ is $`\le e_p(Y)`$.
  - By S-run (§13.2), $`Y`$'s last run consists of Coll-images, so $`e_p(Y) = \mathcal{T}(\mathrm{Coll}(s|_{j'}))`$
    is a truncation blob of the collapsed term $`s`$.
  - **$`s = W|_i`$:** $`e_p(Y) = \mathcal{T}(Y_{j'})`$ with $`j' \lt i`$ (or $`\alpha`$). This is an earlier input.
  - **$`s = E_j`$ ($`y = 1`$) and $`Y`$ epsilon:** then every child of $`E_j`$ has $`y = 2`$.
    - If $`j \ge 2`$: $`E_j|_{j'} \le_p E_j \le_p E_{j-1}`$ (Sib). $`E_{j-1}`$ has $`y = 1`$, so $`\mathrm{Coll}(E_{j-1})`$ is an
      earlier input, and [COMB](COMB.md) Lemma 10 gives $`\mathrm{Coll}(E_j|_{j'}) \le_p \mathrm{Coll}(E_{j-1})`$.
    - If $`j = 1`$: G\* gives $`E_1 \lt_p W`$, so $`\mathrm{ch}(E_1) \lt_{\mathrm{lex}} (D_1 \ldots D_p, E_1, \ldots)`$. Since every child of $`E_1`$
      has $`y = 2 \gt y(E_1)`$, $`\mathrm{ch}(E_1)`$ cannot run past $`D_1 \ldots D_p`$. Hence
      $`\mathrm{ch}(E_1)[:j'] \le_{\mathrm{lex}} (D_1 \ldots D_p)`$, and $`\mathrm{Coll}(E_1|_{j'}) \le_p Y_p`$ (Lemma 10).
      ($`\mathrm{ch}(E_1) = (D_1 \ldots D_p)`$ would give $`Y = Y_p`$, which is no jump.)
  - With Mono\*, $`e_p(Y) \le K`$.
- **(3) $`\beta`$ non-epsilon** ($`s = E_j`$ with a child of $`y \le 1`$; the inputs $`\mathrm{Coll}(W|_i)`$ are always
  epsilon).
  - The intermediate elements are epsilon subterms of $`\mathcal{T}(\mathcal{L}Y)`$. By CL (applied to $`\mathcal{L}Y`$'s root
    terms) these lie in:
    - (a) $`\mathcal{T}((0, \mathrm{hi}\, Y)) = \mathcal{T}(\mathrm{Coll}(E_j|_{p_j}))`$, where $`p_j`$ = the number of $`y = 2`$ children of
      $`E_j`$;
    - (b) the values of lo-items: constants ($`\lt \alpha`$), and blobs $`\mathrm{Coll}(c)`$ for $`y = 1`$ children $`c`$
      of $`E_j`$.
  - For (a): the argument of (2) gives $`\mathrm{Coll}(E_j|_{p_j}) \le_p Y_p`$ or $`\le_p \mathrm{Coll}(E_{j-1})`$, hence
    $`\le K`$. Its subterms are smaller.
  - For (b): $`c`$ is a region $`y = 1`$ node, so $`\mathrm{ch}(c) \lt_{\mathrm{lex}} \mathrm{ch}(W)`$ by the G\* chain (Claim Q).
    Two cases:
    - $`\mathrm{Coll}(c)`$ epsilon (all children of $`c`$ have $`y = 2`$): as in (2), $`\mathrm{Coll}(c) \le_p Y_p`$.
    - $`\mathrm{Coll}(c)`$ non-epsilon: $`\mathrm{Coll}(c)`$ is not itself an intermediate element. Its epsilon
      subterms lie in $`\mathrm{Coll}(c|_{p_c}) \le_p Y_p`$ and in the lo-blobs of $`c`$. By induction on
      height they are $`\le K`$.
  - **If $`W`$ has no $`D`$-children,** G\* gives $`\mathrm{ch}(s) \lt_{\mathrm{lex}} \mathrm{ch}(W) = (E_1, \ldots)`$ for every region
    $`y = 1`$ node $`s`$. So every first child has $`y \le 1`$, and hence every child does. The region
    has no $`y = 2`$ nodes, and no blob is epsilon. So there is no intermediate element, and
    the localization goes directly from $`\alpha`$ to $`\beta`$. ∎

**Remark.** Sub-blobs of a jump input can lie above $`K`$: 6 instances were found, e.g. in
$`(0,0)(1,1)(2,2)(3,2)(2,2)(3,1)(4,2)(5,2)(4,2)`$. There $`X = \vartheta_0(\Omega+Y_1) \gt K`$, and $`X`$ is a
subterm of $`Y_2 = \vartheta_0(\Omega + X)`$. Such sub-blobs have level $`\le \Delta_Y`$, so they are not localization
elements (EL, Lemma 4.9). This is why PL is stated for localization elements only.

**E2 (PROVED given TR; corrected for referee item M6).** This is step $`(\mathrm{E2}_j)`$ of the
induction of Prop 4.3 (M7, [§4.5](PROOF.md)). So $`K = K(\xi) = o(S_{j-1})`$ with $`\xi = \xi_{j-1} \lt \lambda_\alpha`$.

- **$`\beta`$ lies in $`(\alpha, \alpha^+)`$ (M6(a)).**
  - $`o(Y_j) \le \xi_j \le \xi_n = \lambda_\alpha`$, by E1.
  - $`\lambda_\alpha = \lambda^1_\alpha`$ ([W07b] Thm 5.3), and $`\lambda^1_\alpha \lt \alpha^+`$ ([W07a] Cor 7.6).
  - So $`\beta = o(Y_j) \lt \alpha^+`$. Also $`\beta \gt \alpha`$ (the inputs are $`\gt_p N`$, [COMB](COMB.md) K2).
  - So [W07a] Lemma 6.5 applies to $`\beta`$.
- **The candidate predecessor.** Suppose some $`\beta' \in (\alpha, \beta)`$ had $`\beta' \lt_1 \beta`$.
  - By [W07b] Cor 5.9 (relativized to $`\alpha`$, with [W07a] Lemmas 6.5 and 7.7), the greatest
    such $`\beta'`$ is an intermediate element $`\gamma := \beta_i`$ of the $`\alpha`$-localization of $`\beta`$, with
    $`\lambda_\gamma \ge \beta`$.
  - By PL, $`\gamma \le K`$.
- **The component of $`\gamma`$ (M6(b), replacing the incorrect citation of [W07b] Lemma 3.4(a)).**
  1. Let $`\beta_0 := \min\{\delta \in (\alpha, \gamma] : \delta \le_1 \gamma\}`$. It exists, since $`\gamma`$ itself qualifies.
  2. $`\beta_0`$ is $`\alpha`$-$`\le_1`$-minimal. Suppose $`\delta \lt_1 \beta_0`$ with $`\delta \gt \alpha`$. Then $`\delta \le_1 \beta_0 \le_1 \gamma`$, so $`\delta \le_1 \gamma`$ by
     transitivity ([W07b] Lemma 2.1). This contradicts the minimality of $`\beta_0`$.
  3. So $`\beta_0 = \kappa^\alpha_{\xi'}`$ for some $`\xi' \ge 1`$ ([W07b] Def 3.2).
  4. By [W07b] Lemma 3.3(c) with $`\beta = 1`$: $`\kappa^\alpha_{\xi+1} = \mathrm{lh}(\kappa^\alpha_\xi) + 1 = K + 1`$. This uses
     $`\xi \lt \lambda_\alpha \le \theta_\alpha`$, and $`1 \lt \mathrm{lh}(\kappa_\xi)^L`$.
  5. $`\kappa^\alpha_{\xi'} = \beta_0 \le \gamma \le K \lt \kappa^\alpha_{\xi+1}`$, and $`\kappa^\alpha`$ is strictly increasing. So $`\xi' \le \xi`$.
  6. **$`K`$ is monotone in the index.** For $`\xi' \lt \xi`$, $`\mathrm{lh}(\kappa_{\xi'}) \lt \mathrm{lh}(\kappa_{\xi'}) + 1 = \kappa_{\xi'+1} \le \kappa_\xi \le \mathrm{lh}(\kappa_\xi)`$ (Lemma 3.3(c) again). So $`\mathrm{lh}(\kappa_{\xi'}) \le K`$ for all $`\xi' \le \xi`$.
- **Conclusion.**
  - $`\beta_0 \le_1 \gamma \le_1 \beta`$ gives $`\beta_0 \le_1 \beta`$. So $`\beta \le \mathrm{lh}(\beta_0) = \mathrm{lh}(\kappa_{\xi'}) \le K`$.
  - But a jump input satisfies $`\beta \gt \mathrm{lead}(K)`$. Since $`\beta \in P`$, this gives $`\beta \ge \mathrm{lead}(K) \cdot \omega \gt K`$.
  - Contradiction. ∎

**Lean.** E2 is stated in this value form as `E2` in [Main/E12.lean](../Main/E12.lean) and left as `sorry`: PL and [W07b] Cor 5.9 are not formalized.

### 14.4 Intermediate status (superseded; see [§0](PROOF.md) and [§16](PROOF-4.md))

| item | status |
|---|---|
| ND, LT (hence CI) | **PROVED** (P′, Q; SC; CI from Mono\*) |
| LOC′, LOC″ (hence $`\mathrm{Bar}_T`$, hence bar-closure given TR) | **PROVED** from Mono\* (CL, EL, FD, LV) |
| NS, S-eps, $`\iota`$-exp, $`\mathrm{E1}_T`$ | PROVED (§13) |
| E2 | **PROVED given TR** (PL proved; semantic core via [W07b] Cor 5.9, Lemmas 3.3, 3.4) |
| TR, including Mono\* | OPEN at this stage; now PROVED in [TR](TR.md) |
| [COMB](COMB.md): S1, R, Lemma 6, T, SC, Lemma C, Lemma 2.4 | PROVED |

**At this stage everything except TR (with Mono\*) was PROVED. [§15.1](PROOF-4.md) adds the finiteness of $`V_M`$ (B1); see [§16](PROOF-4.md).**

The Main Theorem follows from TR through this chain:

- L: E1 and E2 give the fold correctness (Prop 4.3), with T.
- Lemma 5.1 (embedding).
- Isominimality via Route A: bar-closure from $`\mathrm{Bar}_T`$ and [§11.3](PROOF-2.md), then [CW12] Thm 6.2 and
  Cor 6.3.
- Lemma 6.1.

---

[Part 1: §0–§10](PROOF.md) | [Part 2: §11–§12](PROOF-2.md) | **Part 3: §13–§14** | [Part 4: §15–§16, References, Review history](PROOF-4.md)
