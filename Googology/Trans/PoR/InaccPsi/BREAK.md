[← Back](README.md) | [English](BREAK.md) | [Japanese](BREAK-ja.md)

# $`R_2^+`$ where the skeleton ends: INC1 and NOBAD, the first non-skeletal point, nested pairs, chains from fans, and finite closures

This page continues [PINS.md](PINS.md). The status words are those of [README.md](README.md) §3: **proved** means that an
independent referee found the result proved with no fatal or blocking point. All results on this page are from
2026-10. They come from eight papers in two rounds of four, each paper refereed once. "1 review" means one referee.
"2 reviews" means that two independent papers proved the result and each paper was refereed once. A statement that its
referee found not proved, or false as written, is listed under **Not proved**, even when the rest of its paper is proved.
None of the eight papers uses Wilken, JSL 72 (2007), Carlson, AML 38 (1999), or Wilken, AML 45 (2006). No result on this
page is in Lean.

**Notation.** As on [REACHES.md](REACHES.md) and [PINS.md](PINS.md). $`\nu_P = \upsilon_{\Lambda^*+\omega^2}`$ is the end of Theorem SKEL. $`\mathrm{lh}_1(a)`$ is the
reach of $`a`$ in $`R_1^+`$. A gap is the interval between two consecutive $`\upsilon`$-points. A **standard pair** is a
$`\lt_2`$-pair $`(\upsilon_{\lambda+\omega j}, \upsilon_{\lambda+\omega j+1})`$ ($`\lambda = 0`$ or a restart index, $`j \ge 1`$); every other $`\lt_2`$-pair is a
**new pair**. A **fan** is a point with two $`\lt_2`$-successors. A **$`k`$-nest** is $`x_1 \lt \cdots \lt x_k \lt y_k \lt \cdots \lt y_1`$ with $`x_i \lt_2 y_i`$
($`k`$ nested pairs); its top is $`y_1`$. PS is the pattern of a 2-nest (a pair with a pair nested inside).
$`H(\eta) = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$, $`P_k = \psi_{\Omega_2}(\Omega_\omega\cdot k)`$, so $`P_1 = \theta`$ and $`P_2 = \theta' = \psi_{\Omega_2}(\Omega_\omega\cdot 2)`$.
$`\beta_0`$ is the first difference between $`R_2^S`$ and $`R_2^C`$ ([README.md](README.md) §3).

## 1. INC1 and NOBAD: proved

INC1-S is "$`a \le_1 b`$ in $`R_2^S`$ implies $`a \le_1 b`$ in $`R_1^+`$". INC1-nonups is the same for $`R_2^C`$. Both are trivial when $`a`$ is a
$`\upsilon`$-point, because in $`R_1^+`$ a $`\upsilon`$-point is $`\le_1`$ to everything above it. The first round reduced both to one
conjecture (NOBAD, and CC in $`R_2^C`$); the second round proved them.

- **The earlier remark "INC1-S is trivial in $`R_2^S`$" was wrong** (proved, 1 review). $`\le_1`$ of $`R_2^S`$ is $`\Sigma_1`$ in the language of
  $`R_2^S`$, not in that of $`R_1^+`$, so a copy need not keep the $`\le_1`$-facts of $`R_1^+`$.
- **Lemma LEFT-AT** (proved, 1 review). Lemma LEFT needs INC1 only at its own right end: if $`\alpha \lt_2 \beta`$ and INC1 holds for
  the pairs $`y \le_1 \alpha`$, then $`\alpha = \upsilon_\lambda`$ with $`\lambda`$ a limit. Also Lemma LEFT-SK (proved, 1 review).
- **Bad right ends.** A point $`b`$ that is not a $`\upsilon`$-point is a **bad right end** if there are $`v \lt x \lt b`$ with $`v \lt_2 b`$, $`x \lt_1 b`$,
  and $`x`$ not a $`\upsilon`$-point in the gap of $`b`$. Then $`v`$ is a fan ($`v \lt_2 x`$ and $`v \lt_2 b`$). NOBAD says that there is none.
- **Theorem INC1-LOC** (proved, 1 review; $`R_2^S`$). INC1-S holds for every pair whose right end is at most the least bad
  right end. Proof idea: take the least failing right end $`g_0`$; then $`g_0 = \mathrm{lh}_1(x) + 1`$ for some $`x`$. If no point below
  $`x`$ has a $`\lt_2`$-successor in $`(x, g_0)`$, a copy argument contradicts Wilken, APAL 145 (2007) 162–175, Claim 5.6. Otherwise
  there is a bad right end below $`g_0`$.
- **Theorem INC1-LOC-C** ($`R_2^C`$). The same for $`R_2^C`$: first proved given CC (1 review), now proved without it (1 review), by
  Theorem CC-F.
- **Theorem CC-F** (proved, 1 review). Let $`a \le_1 b`$ in $`R_1^+`$, and let $`X \subset a`$ and $`Y \subset [a, b)`$ be finite, with $`0 \in X`$ and
  $`X \cup Y`$ closed under Cantor normal form parts. Then there are cofinally many $`\tilde Y \subset a`$ above $`X`$ such that $`X \cup \tilde Y`$ is
  closed and some map from $`X \cup Y`$ onto $`X \cup \tilde Y`$ fixes $`X`$, keeps $`0`$, $`+`$ and $`\le`$ in both directions and keeps $`\le_1`$ forward.
  Proof idea: take any copy $`\varphi`$, send each Cantor normal form part $`z_i`$ of a point to the largest Cantor normal form part
  of $`\varphi(z_i)`$, and add the parts back up. INC1-LOC-C needs only this forward form. CC as an isomorphism ($`\le_1`$ in
  both directions) is still open, but nothing uses it.
- **Lemma FANCOF** (proved, 1 review; $`R_2^S`$ and $`R_2^C`$). If $`v \lt_2 x \lt b`$ and $`v \lt_2 b`$, then $`\lt_2`$-pairs are cofinal below $`v`$
  ($`\Sigma_1`$-reflection in $`R_2^S`$; Carlson 2009, L.5.5(1) in $`R_2^C`$).
- **Theorem INC1** (proved, 1 review; $`R_2^S`$ and $`R_2^C`$, no hypothesis). $`a \le_1 b`$ in $`R_2^+`$ implies $`a \le_1 b`$ in $`R_1^+`$.
  Proof: take the least failing right end $`g_0`$. INC1-LOC gives a bad right end $`b \lt g_0`$ with $`v \lt x \lt b`$, $`v \lt_2 x`$ and $`v \lt_2 b`$.
  By FANCOF and Lemma PI2-UP (§3), $`\lt_2`$-pairs $`(p, q)`$ are cofinal below $`b`$. Since $`p \lt g_0`$, LEFT-AT makes each $`p`$ a
  $`\upsilon`$-point. The $`\upsilon`$-points form a closed class, so $`b`$ is a $`\upsilon`$-point, which a bad right end is not. This is
  Theorem RE of §3, run at a stage where LEFT already holds below $`b`$.
- **Corollaries NOBAD and LEFT** (proved, 1 review; both structures). There is no bad right end. Every $`\lt_2`$-left end is
  $`\upsilon_\lambda`$ with $`\lambda`$ a limit. The lower bounds for the least bad right end proved in the first round are no longer needed.
- **RIGHT** (every $`\lt_2`$-right end is a $`\upsilon`$-point) is **not proved**. Proved (1 review each):
  - RE-U: Theorem RE of §3 holds with no hypothesis. If $`\lt_2`$-pairs are cofinal below $`\alpha`$ and $`\alpha \lt_2 \beta`$, then $`\beta = \upsilon_\mu`$
    with $`\mu`$ a restart index.
  - FAN-R: every $`\lt_2`$-successor of a fan is $`\upsilon_\mu`$ with $`\mu`$ a restart index.
  - RIGHT-LIM: if $`\beta`$ is the supremum of its $`\lt_1`$-predecessors, then $`\beta = \upsilon_\lambda`$ with $`\lambda`$ a limit.
  - REDUCTION: call a pair $`\alpha \lt_2 \beta`$ **isolated** if $`\lt_2`$-pairs are not cofinal below $`\alpha`$. RIGHT is equivalent to
    **Conjecture RIGHT-ISO**: in every isolated pair, $`\beta`$ is a $`\upsilon`$-point. In an isolated pair, $`\alpha`$ is the largest
    $`y \lt \beta`$ with $`y \le_1 \beta`$, and $`\beta`$ is the only $`\lt_2`$-successor of $`\alpha`$.
  - A proof of RIGHT-ISO needs facts of $`R_1^+`$ above $`\beta`$, and $`\alpha \le_2 \beta`$ gives none. A numeric search is not possible,
    because being a $`\upsilon`$-point is not visible in a pattern.

The results that used LEFT, INC1 or CC:

| result | first round | now (1 review) |
|---|---|---|
| INC1-S, INC1-nonups | given NOBAD (and CC) | proved |
| LEFT, LEFT-SK | below the least bad right end; everywhere given NOBAD (and CC) | proved |
| 3CH (i)–(iii) ([REACHES.md](REACHES.md) §4) | given NOBAD | proved |
| 3CH (iv), FIRST-BREAK ([REACHES.md](REACHES.md) §4) | proved | unchanged |
| C3′-FALSE ([REACHES.md](REACHES.md) §5) | given NOBAD | proved; the numeric C3′ is false given only that Lemma REL is an equality there |
| VEB, C3-VEB (a)–(c) ([PINS.md](PINS.md) §4) | given NOBAD | proved; for VEB a minor fix from its first review (one case) is still to be written in |
| $`\Lambda \ge \Lambda_{cert}`$ ([PINS.md](PINS.md) §4) | given INC1-nonups | proved (with the replayed certificates) |
| FRAG2-W, FRAG2-C ([REACHES.md](REACHES.md) §4) | given INC1 | the INC1 hypothesis is gone; the referee's range (below $`\nu`$) stays |
| RE, C3′′-FALSE, the bounds for $`c_0, c_1, c_2`$ (§3) | given LEFT | proved |
| NU-C′, $`\nu_C \le \mathrm{top}(PS^*) \lt`$ the point of $`\Phi_3`$(row 28) | given CC and the replayed certificates | given the replayed certificates |

## 2. The first non-skeletal point

$`\nu_S`$ is the first point where $`R_2^S`$ stops being skeletal ([REACHES.md](REACHES.md) §4). $`\nu_{new}`$ is the least right end of a new
pair, and $`\nu_{nest}`$ the least top $`y`$ of a realization of PS.

- **Premise corrected** (proved / cited, 1 review). $`\nu_P`$ is not a non-skeletal point: $`R_2^S`$ is skeletal on $`[0, \nu_P]`$
  (Theorem SKEL), so $`\nu_S \gt \nu_P`$. And the first break is not a fan (see CAP below).
- **Theorem SKEL⁺** (proved, 1 review; $`R_2^S`$; no FRAG). The description of Theorem SKEL holds on $`[0, \nu_{new})`$ with one change:
  a restart may have $`\lt_1`$-predecessors, and they are exactly the restarts below it whose reach covers it. The pairs are
  the standard pairs, block points have their block caps, and the reaches of restarts are closed. So $`R_2^S`$ is
  skeletal, and INC1-S and LEFT hold, on $`[0, \nu_{new})`$. The referee found two minor gaps (a choice of a bound, and one step
  that used SKEL at its own end point) and gave a fix for each.
- **Theorem FIRST-PAIR** (proved, 1 review; $`R_2^S`$; no FRAG). $`\nu_S = \nu_{new} = \nu_{nest}`$; call it $`\nu`$.
  - The break is a non-standard $`\lt_2`$-pair. A $`\upsilon`$-cap that cuts a reach does not occur at or below $`\nu`$.
  - Exactly one new pair has right end $`\le \nu`$: $`(a_0, \nu)`$, where $`a_0`$ is the least new left end. $`a_0 = \rho_\Lambda`$ with
    $`\omega^3 \mid \Lambda`$. Its $`\lt_1`$-predecessors are cofinal below it; they are restarts, they form a $`\lt_1`$-chain, and each has reach
    exactly $`\nu`$. $`m_0`$ is the least of them.
  - $`\nu = \rho_{\mu_0}`$ is a restart, with $`\omega^3 \mid \mu_0`$ and $`\mu_0 \ge \Lambda + \omega^3`$. It is a limit of standard pairs and of restarts.
  - The least realization of PS has least point $`a_0`$ and top $`\nu`$. This is Conjecture NS of [REACHES.md](REACHES.md) §4 for
    $`R_2^S`$, apart from the names.
- **Lemma CAP** (proved, 1 review; $`R_2^S`$ and $`R_2^C`$). Every $`\alpha \le \nu_{nest}`$ has $`\mathrm{lh}(\alpha) \le \nu_{nest}`$. Proof: "a pair with a
  pair nested inside exists" is a $`\Sigma_1`$ sentence with no parameters. Consequences in $`R_2^S`$:
  - $`\mathrm{lh}(a_0) = \nu`$, and $`a_0`$ has exactly one $`\lt_2`$-successor.
  - $`\mathrm{lh}(\nu) = \nu`$: $`\nu`$ is the first restart that does not reach its first block top.
  - No fan has its apex $`\le \nu`$. Every chain of length 3 has $`c_0 \gt \nu`$, and $`m_3 \gt \nu`$. The least $`\kappa`$ that is $`\le_1`$ to every
    larger ordinal is $`\gt \nu`$.
- **Two reviews.** "Every fan apex of $`R_2^S`$ is $`\ge \nu_P`$, and $`m_3 \gt \nu_P`$" has **2 reviews**: CAP gives it through $`\nu \gt \nu_P`$, and
  Theorem M-S of §3 proves it independently.
- **$`R_2^C`$, first round** (proved, 1 review). Let $`T_C`$ be the top of the least realization of PS in $`R_2^C`$. Then $`\nu_C \le T_C`$ without
  INC1 or CC, CAP holds, and $`[0, T_C] \subseteq \mathrm{Core}(R_2^C)`$. With the certificate "$`T_C`$ is below the point of $`\Phi_3`$(row 28)"
  (replayed), $`\nu_C`$ is below the point of $`\Phi_3`$ of row 28 of the table in [README.md](README.md) §6, without any hypothesis.
- **Theorem NU-CT** (proved, 1 review; no FRAG, INC1, CC or HC). $`\nu_C = T_C \le \nu_S`$, and exactly one of the following holds:
  - (A) $`\beta_0 \gt \nu_S`$. Then $`R_2^C`$ and $`R_2^S`$ agree on every relation with right end $`\le \nu_S`$, $`\nu_C = \nu_S`$, and SKEL⁺, FIRST-PAIR
    and CAP hold in $`R_2^C`$ as stated.
  - (B) A "ghost": $`\beta_0 = \nu_C = T_C \lt \nu_S`$. Then $`R_2^C`$ has exactly one extra new pair $`\rho_L \lt_2 \nu_C`$ that $`R_2^S`$ does not have.
    Lemma GHOST (proved, 1 review) gives its shape, which is the shape of FIRST-PAIR.

  In both cases the two structures agree on every relation with right end $`\lt \nu_C`$. Also proved: $`\nu_C = \nu_S`$ iff there is
  no ghost iff $`\beta_0 \gt \nu_S`$ iff $`T_C = \nu_S`$.
- **Corollaries** (proved, 1 review; $`R_2^C`$).
  - $`\beta_0 \ge \nu_C \gt \nu_P`$. Before: $`\beta_0 \ge \rho_{\Theta_A+\omega^2}`$.
  - $`[0, \nu_C] \subseteq \mathrm{Core}(R_2^C)`$, so the core of $`R_2^C`$ contains $`[0, \nu_P]`$. Before: $`[0, \rho_{\Theta_{d\omega}})`$, and $`[0, T_C]`$ with $`T_C`$ not
    compared with $`\nu_P`$.
  - SKEL⁺ (with HC and INC1-nonups) holds in $`R_2^C`$ on $`[0, \nu_C)`$.
  - No fan of $`R_2^C`$ has its apex $`\le \nu_C`$, every chain of length 3 has $`c_0 \gt \nu_C`$, and $`m_3 \gt \nu_C`$. Before, this came only
    from certificates.
- **$`\nu_C = \nu_S`$** is open. Excluding the ghost is one case of Conjecture CORE-2: the $`\Pi_2`$ upward-transfer clause of the
  finite-set test T2 for the ghost pair.
- **Certificates** ($`R_2^C`$; replayed by the author, 4 of them again by the referee). With $`Q`$ = (0,0,0)(1,1,1)(1,1,1) (row 27),
  $`K`$ = (1,1,0)(2,2,1)(2,2,1), $`M_a = QK(2,0,0)`$ and $`M_\nu = M_a(1,1,0)(2,2,1)(2,2,1)`$: the least point of PS lies between the
  points of $`\Phi_3(QK^3)`$ and $`\Phi_3(M_a(1,0,0))`$, and $`T_C`$ between those of $`\Phi_3(M_\nu[2])`$ and $`\Phi_3(M_\nu(1,0,0))`$. The least fan
  pattern PT has its point above that of $`\Phi_3(\mathrm{SRO})`$ and below $`m_3`$.
- **Theorem GEN-EXT** (proved, 1 review). Theorem GEN ([PINS.md](PINS.md) §3) holds word for word for $`\eta \lt \Omega_\omega\cdot\omega`$:
  $`H(\eta) = \upsilon_{1+\iota(\eta)}`$ for every such $`\eta`$ in $`D`$. **Lemma RI3**: $`\iota(\eta)`$ is a multiple of $`\omega^3`$ iff
  $`\mathrm{logend}(\eta) \ge 3`$. The referee's random test: 480 values of $`\eta`$, 0 mismatches.
- **Theorem PS-TERMS** (proved, 1 review). In $`R_2^S`$ the least realization of PS is
  $`\{0, 1, \upsilon_\Lambda, \upsilon_{\Lambda+\omega}, \upsilon_{\Lambda+\omega+1}, \upsilon_{\mu_0}\}`$: its pairs are $`(a_0, \nu)`$ and the first standard pair above $`a_0`$.
  In $`R_2^C`$ it has the same form, built on the unique $`\lt_2`$-predecessor of $`\nu_C`$. If $`a_0 = H(\eta_a)`$ with $`\eta_a \in D`$, then with
  $`A = \Omega_\omega + \theta\cdot\eta_a`$ the inner pair is $`\psi_{\Omega_1}(A + \omega^{\theta+1})`$, $`\psi_{\Omega_1}(A + \omega^{\theta+1} + \theta)`$.
- **Lemma CORE-ν** (proved, 1 review; $`R_2^S`$). $`m_0 = \min\{\alpha : \alpha \le_1 \nu\} = \min\{\alpha : \mathrm{lh}(\alpha) = \nu\}`$, and every finite configuration in
  $`[m_0, \nu)`$ over a finite set below $`m_0`$ has copies cofinally below $`m_0`$. So $`m_0`$ plays for $`\nu`$ the role that $`\upsilon_1`$ plays for
  $`R_1^+`$. The further claim that every least realization below $`\nu`$ lies below $`m_0`$ has a gap (closedness of the copies) and is
  not counted.
- **Conjecture NU-NAME** (normal forms and order checked in Python and Lean): $`m_0 = \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$,
  $`a_0 = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'+1})`$, $`\nu = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'+1} + \theta')`$. The first new pair would copy
  $`(\upsilon_\omega, \upsilon_{\omega+1})`$ one level up. Proved (1 review, in the referee's corrected form): NU-NAME is equivalent to two
  statements about indices, (N-χ) the $`\lt_1`$-predecessors of $`a_0`$ are exactly the $`\psi_{\Omega_1}(\Omega_\omega\cdot 2 + \theta'\cdot n)`$, $`n \lt \omega`$, and (N-ν)
  $`\nu = H(\eta_a + \theta')`$. Under NU-NAME the inner pair of PS is $`\psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'+1} + \omega^{\theta+1})`$ and the same
  plus $`\theta`$. What blocks a proof: there is no theory of reaches above $`\Theta_A`$, FRAG-E is open, and there is no sufficient test
  for a new $`\lt_2`$-pair in $`R_2^S`$. Proved bounds: $`\nu \gt a_0 \ge m_0 \ge \rho_{\Lambda^*}`$, and $`\nu \lt m_3`$.
- **Not proved** (blocking point, 1 review): "the InaccPsi side of the names is complete; no extension of the maps $`B`$ and $`E`$
  of GEN-EXT is needed". GEN-EXT names the $`\upsilon`$-points only below $`\sup H[D]`$, and no InaccPsi upper bound on $`a_0`$ or $`\nu`$ is
  proved (the only one is $`\nu \lt m_3`$, and $`m_3`$ has no name).
- **The first fan** (proved, 1 review). In $`R_2^S`$ its apex is a new left end above $`\nu`$, and both successors are above $`\nu`$. In
  $`R_2^C`$ it lies above $`\nu_C`$ (NU-CT) and above the point of $`\Phi_3(\mathrm{SRO})`$ (certificates). Where it lies against the levels of
  nested pairs is in §6. Its name is open.

## 3. Chains of length 3 from fans

$`C_l`$ are the classes of the ladder of [PINS.md](PINS.md) §4 ($`C_1`$ = fixed points of $`\iota \mapsto \upsilon_\iota`$), $`f`$ enumerates $`C_{\omega^\omega}`$, and
$`(C)'`$ is the class of limit points of $`C`$. The first round proved several results here given LEFT; LEFT is now proved
(§1), so they hold with no hypothesis (1 review).

- **Theorem CF** (proved, 1 review; $`R_2^S`$ with a citation repair by the referee, and $`R_2^C`$). A chain of length 3 with bottom $`a`$ and
  middle $`e`$ exists iff the $`\lt_2`$-successors of $`a`$ are cofinal in $`e`$ and $`e`$ has a $`\lt_2`$-successor. So a chain of length 3 is
  exactly a fan with infinitely many successors whose limit is itself a left end. **Corollary LEAST** ($`R_2^C`$): $`c_0`$ is the
  least bottom of a chain, $`c_1`$ the least left end among the successors of $`c_0`$, and $`c_2`$ the least successor of $`c_1`$.
- **Lemma PI2-UP and Lemma PC** (proved, 1 review). If $`y \le_2 e`$, every finite configuration that is cofinal below $`y`$ is cofinal
  below $`e`$. In every chain of length 3, pairs, fans and the configurations of every level $`l \lt \omega^\omega`$ of the ladder are
  cofinal below $`c_0`$, below each successor of $`c_0`$ and below $`c_1`$; the successors of $`c_0`$ are cofinal in $`c_2`$.
- **Theorem RE** (proved, 1 review; given LEFT in the first round, now unconditional). If pairs are cofinal below $`y`$ and $`y \lt_2 e`$,
  then $`e = \upsilon_\mu`$ with $`\mu`$ a restart index. If also the ladder configurations of every level $`l \lt \omega^\omega`$ are cofinal below $`y`$,
  then $`e \in C_{\omega^\omega}`$ (this second part needs the minor fix to VEB of §1).
- **Theorem C3′′-FALSE** (proved, 1 review; now unconditional). In every chain of length 3, the points $`c_0, c_1, c_2`$ and every
  successor of $`c_0`$ and of $`c_1`$ lie in $`C_{\omega^\omega}`$, and $`c_0, c_1, c_2`$ are limit points of $`C_{\omega^\omega}`$. So the conjectured shape
  C3′′, $`C^*_3 = \{\upsilon_\Lambda, \upsilon_{\Lambda+\omega}, \upsilon_{\Lambda+\omega+1}\}`$, is false, and the consequences of C3′′ listed under C3-VEB
  ([PINS.md](PINS.md) §4) are vacuous. Read literally the paper also says "every chain $`\upsilon_\mu \lt_2 \upsilon_{\mu+1}`$" is excluded; the referee
  restricts this to the links of a chain of length 3 (standard pairs do exist).
- **Names** (proved, 1 review; from NAME-V). $`C_g`$ is the class of fixed points of $`V_g`$ ($`g \ge 1`$). So
  $`\min C_l = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1\cdot l})`$ for $`1 \le l \le \omega^\omega`$, and the least limit point of $`C_{\omega^\omega}`$ is
  $`\Lambda_{struct} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\omega^{\Omega_1+\omega}+1})`$. Before, both were conjectures.
- **Theorem NO-CHAIN-AT-$`\Lambda_{struct}`$** (proved, 1 review; unconditional). $`\Lambda_{struct} \lt \Lambda_\varepsilon \lt \nu_P`$ and
  $`\Lambda_{struct} \lt \rho_{\Theta_A+\omega^2}`$. It is a restart with no $`\lt_1`$-predecessor, so it has no $`\lt_2`$-successor at all (SKEL in $`R_2^S`$,
  EQB-A in $`R_2^C`$). This is the first proof that $`\Lambda_{struct} \lt \nu_P`$; before, it came only from conjectured names.
- **Theorem M-S** (proved, 1 review; $`R_2^S`$; unconditional). Every fan apex is $`\ge \nu_P`$, and every $`m \lt c_0`$ with $`m \le_1 c_0`$ is
  $`\gt \nu_P`$. Before, only $`c_0 \ge \nu_P`$ was known.
- **Bounds** (proved, 1 review; now unconditional). Let $`B = \nu_P`$ in $`R_2^S`$ and $`B = \rho_{\Theta_A+\omega^2}`$ in $`R_2^C`$, and let $`f(a)`$ be the
  least element of $`(C_{\omega^\omega})'`$ above $`B`$. Then $`c_0 \ge f(a)`$, $`c_1 \ge f(a+\omega)`$, $`c_2 \ge f(a+\omega\cdot 2)`$. Their names are conjectures,
  all below $`\psi_{\Omega_1}(\Omega_\omega\cdot 2) \lt \theta_0`$, so these bounds alone do not need an inaccessible.
- **Correction to Theorem GEN** (proved, 1 review). GEN names the $`\upsilon`$-points only below $`\upsilon^* = \sup H[D] \le \psi_{\Omega_1}(\Omega_\omega + \Omega_2)`$. The
  $`\upsilon`$-points are cofinal in $`\omega_1`$, so "every $`\upsilon`$-point has a name" (written in earlier versions of these pages) was
  false. GEN-EXT (§2) extends the names to $`\eta \lt \Omega_\omega\cdot\omega`$. The referee's random test: 315 values, 0 violations.
- **Not delivered** (blocking point against the goal of the paper, not against a stated result). The paper gives no way to
  produce a chain of length 3. CF restates the problem ("$`e`$ is a left end"). Its other remark, that the new results need
  LEFT, no longer applies.

## 4. Finite closures and reaches beyond $`\Theta_A`$

$`C_\tau(z)`$ is the closure of $`\{0, \tau, z\}`$ under Cantor normal form parts and partial sums, $`\mathrm{lh}`$, and the bar operation
([PINS.md](PINS.md) §1).

- **Theorem CL-FIN** (proved, 1 review). $`C_\tau(z)`$ is finite for every base $`\tau \in \{1\} \cup E`$ and every $`z \in [\tau, \tau^\infty)`$, with a
  size bound that is elementary in the size of $`z`$. Proof idea: $`\mathrm{lh}`$ makes new terms only through "children", and a child has a
  smaller Wilken height than its parent (the computation of Wilken, APAL 145 (2007) 130–161, L.7.14). That $`z \mapsto C_\tau(z)`$ is
  elementary recursive is only an outline (not counted).
- **LHPAR\*.** The Cl\*-form of [PINS.md](PINS.md) is proved (1 review). The sharper form is **not proved as stated**: with Wilken's
  parameters (APAL 145 (2007) 130–161, Def 3.28) it fails, e.g. at $`\tau = \varepsilon_0`$ and $`a = \theta^\tau(\theta^\tau(\omega+1))`$. It holds when the
  parameters are read as their Cantor normal form parts. Nothing else uses the sharp form.
- **Theorem EXPL** (proved, 1 review). $`C_\tau(z)`$ is an explicit pin pattern in the strong sense (coverings may raise the parameters),
  it is $`\tau`$-isominimal, and it commutes with base changes. So the point of [PINS.md](PINS.md) §1 "that $`C_\tau(z)`$ is a $`\tau`$-isominimal pin
  pattern" is proved, and Theorem TOP-FLAT$`_1`$ ([PINS.md](PINS.md) §2) no longer needs CL-FIN and LHPAR\*.
- **Substitution maps** (proved, 1 review). Moving the base and the parameters by a map that is increasing, additive and
  commutes with $`\mathrm{logend}`$ gives an isomorphism that commutes with $`\mathrm{lh}`$ and bar (SUBST-ISO, SUBST-COMM); base change commutes
  with Wilken's translation (COMM-T). **FRAG-SUBST**: the map of Lemma FRAG equals the substitution map, so it does not
  depend on the auxiliary choices (the conjecture at the end of [RESTARTS.md](RESTARTS.md) §1 is now a theorem).
- **Lemma PIN-S** (proved, 1 review). Every point of every segment of a region below $`\delta_j`$ is pinned against copies at a
  restart. So the hypothesis H-RC of [PINS.md](PINS.md) §2 is proved.
- **$`r(\Theta_A)`$** (proved, 1 review). $`\mathrm{lh}(\rho_{\Theta_A}) = \delta + \varepsilon_{\sigma+\omega}`$ in $`R`$ (the upper bound uses no FRAG, the lower bound uses FRAG).
  So the possible exceptional pairs of EQB-A at $`\Theta_A`$ do not occur: HC holds at every $`\lambda \le \Theta_A`$, and the first difference
  $`\beta_0`$ is at least $`\rho_{\Theta_A+\omega^2}`$.
- **New landmarks** (proved, 1 review). $`\Theta_\delta`$ and $`\Theta_{d\omega}`$ are the least restart indices whose formal reach (a recursion
  that uses no FRAG) reaches $`\delta_\lambda\cdot 2`$ and $`\delta_\lambda\cdot\omega`$. The formal reach at $`\Theta_\delta`$ is $`\delta\cdot 2`$, and
  $`\Theta_A \lt \Theta_\delta \lt \Theta_{d\omega} \lt \Lambda^*`$.
- **Corollary CORE-C$`^{d\omega}`$** (proved, 1 review; no FRAG). $`[0, \rho_{\Theta_{d\omega}}) \subseteq \mathrm{Core}(R_2^C)`$. Before: $`[0, \rho_{\Theta_A+\omega^2})`$.
- **Not proved, false as written** (blocking point, off by one at $`y = \delta`$). Theorem TOP-REG ("a point that is not reflected
  bounds the reach"), REACH (a), the claim "reach = formal reach", and the bound $`r_C \le R`$ in Theorem EQB-dw. Counterexample:
  at $`\lambda = \omega^2`$ the formal reach is $`\delta`$, but $`\rho \le_1 \delta + 1`$. In general the formal reach is one less than the reach
  when the offset is finite. The referee's repair (count only $`y \gt \delta`$) is proved in the review, but not yet reviewed
  itself. The values at $`\Theta_A`$, $`\Theta_\delta`$, $`\Theta_{d\omega}`$ and CORE-C$`^{d\omega}`$ do not depend on it.


## 5. Nested pairs above $`\nu`$: the first block of every level

For $`k \ge 1`$ let $`T_k`$ be the least top of a $`k`$-nest, $`x_k`$ the least outer left end of a $`k`$-nest with top $`T_k`$,
$`U_k = \{u \in (0, T_k] : u \le_1 T_k\}`$ and $`s_k = \min U_k`$. So $`(s_1, x_1, T_1) = (\upsilon_1, \upsilon_\omega, \upsilon_{\omega+1})`$, and $`(s_2, x_2, T_2) = (m_0, a_0, \nu)`$
of §2 (in $`R_2^C`$, $`T_2 = \nu_C`$ by NU-CT). $`T_\omega = \sup_k T_k`$.

- **Theorem LIFT-0** (proved, 1 review; $`R_2^S`$ and $`R_2^C`$, every $`k`$, no hypothesis). The first block of level $`k`$ has the shape of the
  first block $`[\upsilon_1, \upsilon_{\omega+1}]`$ of level 1:
  - $`U_k`$ is $`\{x_k, T_k\}`$ together with the $`\lt_1`$-predecessors of $`x_k`$. It is closed, its members are additively principal, and each
    has reach exactly $`T_k`$.
  - $`[0, s_k)`$ is closed under $`\mathrm{lh}`$, and a point strictly between two consecutive members of $`U_k`$ has its reach below the
    upper one.
  - $`x_k \lt_2 T_k`$ is the only $`\lt_2`$-relation with an end in $`U_k`$.
  - Every gap of $`U_k`$ contains $`(k-1)`$-nests and no $`k`$-nest. A point below a member $`u`$ of $`U_k`$ is related to all of $`[u, T_k]`$ in
    the same way.
  - $`T_{k-1} \lt s_k`$ for $`k \ge 2`$.

  The referee found one minor gap (that $`T_k`$ itself is additively principal) and gave a fix.
- **Theorem NEST** (proved, **2 reviews**: two independent papers, both structures). $`T_1 \lt T_2 \lt T_3 \lt \cdots`$, every $`T_k \lt m_3`$, and
  $`T_\omega \le m_3`$. $`T_\omega`$ has no $`\lt_1`$-predecessor and lies in no $`\lt_2`$-pair. Also (1 review): in every chain of length 3, $`k`$-nests are
  cofinal below $`c_0`$, $`c_1`$ and $`c_2`$ for every $`k`$. In $`R_2^S`$ the bound $`T_k \lt m_3`$ is new.
- **Theorem O** (proved given GI, 1 review; both structures). Suppose a base change GI between the gaps of $`U_k`$ exists (the
  analogue at level $`k`$ of Wilken's maps; open, it needs a notation for level $`k`$). Then, counting $`s_k`$ as the 0-th member of $`U_k`$,
  $`x_k`$ is the $`\omega`$-th member and $`T_k`$ the $`(\omega+1)`$-th, as $`\upsilon_\omega`$ and $`\upsilon_{\omega+1}`$ at level 1. For $`k = 2`$ this is the shape part of
  NU-NAME. The paper's claim that this shape is equivalent to GI is not proved (only one direction is shown).
- **What a lift can be** (proved, 1 review; trivial). No order isomorphism maps $`[0, T_2)`$ onto $`[s_2, T_3)`$: the order types differ. The
  stronger claim that even the skeletons of two levels are not order-isomorphic is not proved. The paper therefore looks
  for a recursion one level up, as with Wilken's base changes, not for an image.
- **Not proved** (blocking point, 1 review): Proposition TAIL, "inside a gap of $`U_2`$ the reaches of the restarts follow the
  formal-reach recursion of §4, run inside the gap". It is an outline. The results it uses assume a restart index at most
  $`\Lambda^*`$, every restart in such a gap has a larger index, and the paper does not check the other places that use this
  assumption.
- **Conjecture LIFT-REC** (names): $`s_k = \psi_{\Omega_1}(\Omega_\omega\cdot k)`$, $`x_k = \psi_{\Omega_1}(\Omega_\omega\cdot k + \omega^{P_k+1})`$, $`T_k = \psi_{\Omega_1}(\Omega_\omega\cdot k + \omega^{P_k+1} + P_k)`$.
  For $`k = 1`$ these are proved (Theorem T); for $`k = 2`$ they are NU-NAME. The paper also states a structure for
  $`[s_k, T_{k+1})`$ (level $`k`$ built like SKEL⁺ over the level-$`k`$ points). The referee found that statement wrong (blocking point):
  it ends the points of each level at the start of the next level, but already the $`\upsilon`$-points go on past $`s_2`$ ($`m_0`$, $`a_0`$
  and $`\nu`$ are restarts). It has to be restated.
- **At $`\Omega_\omega\cdot\omega`$** (conjecture). The uniform pattern of the levels cannot go on there; either no new kind of $`\Sigma_1`$
  sentence appears until the first fan (Conjecture FF, §6) or new fan-free kinds appear from long reaches. The referee
  notes that the paper argues this less strongly than it states it.

## 6. The first fan and the first chain against the limit of the levels

A **cap** is an ordinal $`T`$ such that every $`\alpha \le T`$ has $`\mathrm{lh}(\alpha) \le T`$. A **closed fan** is a fan $`x \lt_2 y_1`$, $`x \lt_2 y_2`$ with
$`y_1 \le_1 y_2`$. $`x_F`$ is the least fan apex, and $`(f_0, f_1, f_2)`$ the least closed fan of $`R_2^C`$. A pattern is **fan-free** if no point
of it has two $`\lt_2`$-successors. $`\sigma_F`$ is the supremum of the least realizations of fan-free patterns in $`R_2^C`$; the same
for patterns with no chain of length 3 is $`m_3`$ (Theorem SHARP).

- **Lemma CAP-S1** (proved, 1 review). The least top of a realization of a finite configuration with no parameters is a cap
  (in $`R_2^C`$ also the top of the least realization of any pattern). Lemma CAP of §2 is the case of a 2-nest.
- **Theorem LIM-CAP** (proved, 1 review). A strictly increasing limit $`L`$ of caps has no $`\lt_1`$-predecessor and lies in no
  $`\lt_2`$-pair; no pair $`(a, b)`$ has $`a \lt L \le b`$. So a fan or a chain of length 3 never sits at a limit of levels, only strictly
  above one.
- **Theorem DOM_F** (proved, 1 review; $`R_2^C`$). Every fan-free pattern has its least realization below $`f_0`$. With LIM-CAP:

```math
T_\omega \le \sigma_F \lt f_0 \lt m_3 \lt c_0, \qquad x_F \le f_0 .
```

  In $`R_2^S`$ DOM_F is open, and so is whether an open fan (two successors not $`\le_1`$-related) lies below $`\sigma_F`$.
- **The first fan is not the first chain** (proved, 1 review). Fans and closed fans are cofinal below $`m_3`$, and closed fans with a
  $`k`$-nest inside are cofinal below $`c_0`$. A fan whose successors pile up at a left end occurs first at $`c_0`$ (CF). $`m_3`$ lies in no
  pair and $`m_3 \le_1 c_0`$: the chain is not at the limit $`m_3`$, the limit reaches its bottom. The claim that the first chain sits
  "just above" $`m_3`$ is not proved: fans and nested fans are cofinal below $`c_0`$.
- **Given H-LIFT** (proved, 1 review). H-LIFT is the hypothesis that the levels $`k \lt \omega`$ are fan-free and that $`T_k`$ has the name of
  LIFT-REC. Given it, $`x_F \gt T_\omega = \psi_{\Omega_1}(\Omega_\omega\cdot\omega)`$ (by Lemma CONT, which is in Lean). This is the reading of row 28,
  (0,0,0)(1,1,1)(2,0,0), and it needs no inaccessible.
- **Theorem CH-LOW-1** (proved given FF, 1 review; $`R_2^C`$). FF is the hypothesis that every $`\gamma \lt \theta_0`$ lies below the least
  realization of some fan-free pattern. Given FF, $`f_0`$, $`m_3`$, $`c_0`$, $`c_1`$, $`c_2`$ are all $`\gt \theta_0`$, so every InaccPsi name of them
  contains an inaccessible. FF is open; it would follow from the lower-bound program below $`\theta_0`$ ([README.md](README.md) §3)
  together with "the patterns $`\Phi_3(M)`$ for standard $`M`$ below SRO have no fan" (checked on every scanned matrix). In $`R_2^S`$ the same
  argument is circular.
- **Not proved** (blocking point, 1 review): "given FF, the first fan $`x_F`$ is $`\gt \theta_0`$, so it needs an inaccessible". FF bounds only
  $`\sigma_F`$, and DOM_F puts $`\sigma_F`$ only below the first closed fan $`f_0`$; $`x_F \lt \sigma_F`$ is not excluded. Also not proved as stated:
  "$`\theta_0`$ is excluded as a limit of caps, given FF".
- **Open**: no fan and no chain of length 3 is exhibited below $`\theta_1 = \psi_{\Omega_1}(\psi_{I_1}(0))`$ (the upper half for $`k = 1`$).

## 7. Checks

Each run was under 60 seconds; none is a proof. Certificates count only when replayed.

- INC1 (first round): the referee replayed 3 certificates (the point of $`\Phi_3(\mathrm{SRO})`$ below PT and below a variant, and the
  top of PS below the point of $`\Phi_3`$(row 28)).
- CC-F: the referee tested its arithmetic part on 11,668 random maps keeping $`+`$ below $`\omega^\omega`$ (9,160 of them changed by the
  construction): 0 failures.
- First non-skeletal point: program runs place the point of $`\Phi_3`$ at the predecessors $`QK^n`$, at $`M_a`$ and at $`M_\nu`$, and exactly at
  the inner pair of PS for $`M_u = M_a(1,1,0)(2,2,1)(2,0,0)`$ and $`M_v = M_u(1,1,0)(2,2,1)`$. 16, then 11 named terms are normal forms and
  increasing, in Python and in Lean (test files, not proofs); the referee's own script and Lean copy agree. GEN-EXT: 480
  random $`\eta`$, 0 mismatches, $`H`$ increasing on 38,229 pairs.
- Nested pairs ($`R_2^C`$, replayed by the author, 2 of them again by the referee). With $`Q_2`$ = (0,0,0)(1,1,1)(1,1,1)(1,1,1),
  $`K_2`$ = (1,1,0)(2,2,1)(2,2,1)(2,2,1), $`M_{2a} = Q_2K_2(2,0,0)`$ and $`M_{2\nu} = M_{2a}K_2`$: the least point of a 3-nest lies between the points
  of $`\Phi_3(Q_2K_2)`$ and $`\Phi_3(M_{2a}(1,0,0))`$, and $`T_3`$ is below the points of $`\Phi_3(M_{2\nu}(1,0,0))`$ and $`\Phi_3`$(row 28). Another run
  places $`T_3`$ above the point of $`\Phi_3(Q_2)`$ and $`T_4`$ below that of $`\Phi_3`$(row 28). On 250 standard matrices the position of the
  point against the first nests never goes down. 39 named terms are normal forms (36 of them checked increasing), and 32
  more are normal forms and increasing in Python and in Lean. Some certificate searches stopped at the time limit with no result; the referee's 4 searches for refuting
  certificates (one would refute DOM_F) found none in 40 seconds. These readings assume that the point of
  $`\Phi_3((0,0,0)(1,1,1)^k)`$ is $`\psi_{\Omega_1}(\Omega_\omega\cdot k)`$, which the table in [README.md](README.md) §6 marks as computed, not proved.
- Chains from fans: 27 named terms are normal forms and increasing, in Python and in Lean (test files); the referee's 315
  random values of $`H(\eta)`$: 0 violations of the GEN range or of monotonicity.
- Finite closures: the author's checker on 910 random terms (1,130 children, 3,414 values of LHPAR\*) and the referee's on
  300 terms (539 children, 1,445 values): 0 violations. These tests use only principal parameters, so they never test the
  counterexample to the sharp LHPAR\*; the referee confirmed that counterexample with ordinal values.

## 8. Open

- **RIGHT-ISO** (and so RIGHT). CC as an isomorphism (not needed).
- The name of $`\nu`$ (NU-NAME, now the two index statements (N-χ) and (N-ν)); $`\nu_C = \nu_S`$ (exclude the ghost); the structure above
  $`\nu`$: GI, TAIL, a restated LIFT-REC; the least fan and its name.
- A chain of length 3: a point of $`(C_{\omega^\omega})'`$ above $`B`$ whose successors accumulate at a left end. Being a left end is not a
  property of a finite configuration, so Carlson's generating rules cannot produce it (NO-GEN). FF, DOM_F in $`R_2^S`$, open fans
  below $`\sigma_F`$, and the upper half below $`\theta_1`$. Conjecture CH.
- The reaches for candidates in $`[\delta_j\cdot\omega, \delta_{j+1})`$; a review of the repaired TOP-REG and REACH; $`R_2^C`$ above $`\nu_C`$; the closed
  forms and names above $`\Lambda_\Gamma`$ ($`\Theta_P`$, $`\Theta_1`$, $`\Theta_A`$, $`\Theta_\delta`$, $`\Theta_{d\omega}`$, $`\Lambda^*`$, $`\nu_P`$); names above $`\upsilon^*`$ beyond GEN-EXT.
- That the assignments between ordinals and patterns are elementary recursive (outline only), and that UNIF is onto.
