[← Back](README.md) | [English](BREAK.md) | [Japanese](BREAK-ja.md)

# $`R_2^+`$ where the skeleton ends: INC1 and NOBAD, the first non-skeletal point, nested pairs, chains from fans, finite closures, and the levels above $`\nu`$

This page continues [PINS.md](PINS.md). The status words are those of [README.md](README.md) §3: **proved** means that an
independent referee found the result proved with no fatal or blocking point. All results on this page are from
2026-10. They come from sixteen papers in four rounds of four, each paper refereed once (the third round is §7, the fourth §8). "1 review" means one referee.
"2 reviews" means that two independent papers proved the result and each paper was refereed once. A statement that its
referee found not proved, or false as written, is listed under **Not proved**, even when the rest of its paper is proved.
None of the sixteen papers uses Wilken, JSL 72 (2007), Carlson, AML 38 (1999), or Wilken, AML 45 (2006). No result on this
page is in Lean. The fifth to seventh rounds (four papers each) are on the next page, [COVER.md](COVER.md), the eighth to tenth on [FANFREE.md](FANFREE.md), and the eleventh and twelfth on [VEBLEN.md](VEBLEN.md). The sixth round proves
SKEL⁺ and SKEL$`^\omega`$ in full, so several results of §1, §7.1 and §8 below that were proved only at outline level are now proved
([COVER.md](COVER.md) §5.1); the labels below say so.

**Notation.** As on [REACHES.md](REACHES.md) and [PINS.md](PINS.md). $`\nu_P = \upsilon_{\Lambda^*+\omega^2}`$ is the end of Theorem SKEL. $`\mathrm{lh}_1(a)`$ is the
reach of $`a`$ in $`R_1^+`$. A gap is the interval between two consecutive $`\upsilon`$-points. A **standard pair** is a
$`\lt_2`$-pair $`(\upsilon_{\lambda+\omega j}, \upsilon_{\lambda+\omega j+1})`$ ($`\lambda = 0`$ or a restart index, $`j \ge 1`$); every other $`\lt_2`$-pair is a
**new pair**. A **fan** is a point with two $`\lt_2`$-successors. A **$`k`$-nest** is $`x_1 \lt \cdots \lt x_k \lt y_k \lt \cdots \lt y_1`$ with $`x_i \lt_2 y_i`$
($`k`$ nested pairs); its top is $`y_1`$. PS is the pattern of a 2-nest (a pair with a pair nested inside).
$`H(\eta) = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$, $`P_k = \psi_{\Omega_2}(\Omega_\omega\cdot k)`$, so $`P_1 = \theta`$ and $`P_2 = \theta' = \psi_{\Omega_2}(\Omega_\omega\cdot 2)`$.
$`\beta_0`$ is the first difference between $`R_2^S`$ and $`R_2^C`$ ([THETA.md](THETA.md) §8.2).

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
- **RIGHT** (every $`\lt_2`$-right end is a $`\upsilon`$-point) was **not proved** in these rounds. **Now proved** in $`R_2^S`$, and in $`R_2^C`$ for right
  ends below $`\beta_0`$ (Theorem SKEL$`^\infty`$, [COVER.md](COVER.md) §5.1, 1 review). Proved here (1 review each):
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
- **Theorem SKEL⁺** (proved, 1 review at proof level, [COVER.md](COVER.md) §5.1; this first paper was accepted at outline level; $`R_2^S`$; no FRAG). The description of Theorem SKEL holds on $`[0, \nu_{new})`$ with one change:
  a restart may have $`\lt_1`$-predecessors, and they are exactly the restarts below it whose reach covers it. The pairs are
  the standard pairs, block points have their block caps, and the reaches of restarts are closed. So $`R_2^S`$ is
  skeletal, and INC1-S and LEFT hold, on $`[0, \nu_{new})`$. The referee found two minor gaps (a choice of a bound, and one step
  that used SKEL at its own end point) and gave a fix for each. The complete proof corrects one wording: "the reach of a restart is
  closed" in $`R_1^+`$ needs that reach to be below the top of its block.
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
  - $`\beta_0 \ge \nu_C \gt \nu_P`$. Before: $`\beta_0 \ge \rho_{\Theta_A+\omega^2}`$. (Now $`\nu_C \gt \upsilon^* = \psi_{\Omega_1}(\Omega_\omega + \Omega_2)`$, 1 review, and
    $`\nu_P \ge \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{\theta+2})`$, proved as a transfer, [THETA.md](THETA.md) §1; now $`\nu_P = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{\theta+2})`$ and
    $`\nu_C \ge \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{\theta+3}\cdot 2)`$, [THETA.md](THETA.md) §9.1; then $`\nu_C \ge X_4 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{G_2+1}\cdot 2)`$ with $`G_2 = \psi_{\Omega_2}(\Omega_\omega + \omega^{\theta_2+2})`$, [SHIFT.md](SHIFT.md) §1; then $`\nu_C \ge X_5`$ given FRAG, [SHIFT.md](SHIFT.md) §8.1; then $`\nu_C \ge X_8`$ given FRAG, §9.1 there; then $`\nu_C \ge X_9`$ given FRAG, [SHIFT2.md](SHIFT2.md) §1.1; then $`\nu_C \ge X_{11}`$ given FRAG, §2.1 there.)
  - $`[0, \nu_C] \subseteq \mathrm{Core}(R_2^C)`$, so the core of $`R_2^C`$ contains $`[0, \nu_P]`$. Before: $`[0, \rho_{\Theta_{d\omega}})`$, and $`[0, T_C]`$ with $`T_C`$ not
    compared with $`\nu_P`$.
  - SKEL⁺ (with HC and INC1-nonups) holds in $`R_2^C`$ on $`[0, \nu_C)`$. Now with no hypothesis ([COVER.md](COVER.md) §5.1).
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
  itself. (Now the amended definition of the formal reach, $`y`$ in $`(\delta, \rho_{\lambda+\omega^2})`$, is used in [THETA.md](THETA.md) §9.1, and its referee confirmed
  that it is consistent and that the bound "reach $`\le`$ formal reach" holds for it; then it was written out as an amendment and
  checked by a second referee, [SHIFT.md](SHIFT.md) §1.) The values at $`\Theta_A`$, $`\Theta_\delta`$, $`\Theta_{d\omega}`$ and CORE-C$`^{d\omega}`$ do not depend on it.


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
  NU-NAME. The paper's claim that this shape is equivalent to GI is not proved (only one direction is shown). Now (§7.2) the
  hypothesis can be weakened to a finite form $`GI^{fin}`$, and this finite form is equivalent to the shape. In $`R_2^C`$ the shape now holds for
  every $`k`$ with no hypothesis (Theorem O$`^C`$, §8.1, 1 review); in $`R_2^S`$ it is open for $`k \ge 2`$.
- **What a lift can be** (proved, 1 review; trivial). No order isomorphism maps $`[0, T_2)`$ onto $`[s_2, T_3)`$: the order types differ. The
  stronger claim that even the skeletons of two levels are not order-isomorphic is not proved. The paper therefore looks
  for a recursion one level up, as with Wilken's base changes, not for an image.
- **Not proved** (blocking point, 1 review): Proposition TAIL, "inside a gap of $`U_2`$ the reaches of the restarts follow the
  formal-reach recursion of §4, run inside the gap". It is an outline. The results it uses assume a restart index at most
  $`\Lambda^*`$, every restart in such a gap has a larger index, and the paper does not check the other places that use this
  assumption. Now (§7.1) every use is listed and replaced; the result was still an outline, and is now proved ([COVER.md](COVER.md) §5.1).
- **Conjecture LIFT-REC** (names): $`s_k = \psi_{\Omega_1}(\Omega_\omega\cdot k)`$, $`x_k = \psi_{\Omega_1}(\Omega_\omega\cdot k + \omega^{P_k+1})`$, $`T_k = \psi_{\Omega_1}(\Omega_\omega\cdot k + \omega^{P_k+1} + P_k)`$.
  For $`k = 1`$ these are proved (Theorem T); for $`k = 2`$ they are NU-NAME. The paper also states a structure for
  $`[s_k, T_{k+1})`$ (level $`k`$ built like SKEL⁺ over the level-$`k`$ points). The referee found that statement wrong (blocking point):
  it ends the points of each level at the start of the next level, but already the $`\upsilon`$-points go on past $`s_2`$ ($`m_0`$, $`a_0`$
  and $`\nu`$ are restarts). It has to be restated. Now restated, with this point fixed (§7.1).
- **At $`\Omega_\omega\cdot\omega`$** (conjecture). The uniform pattern of the levels cannot go on there; either no new kind of $`\Sigma_1`$
  sentence appears until the first fan (Conjecture FF-LIFT; now proved false, §7.4) or new fan-free kinds appear from long reaches. The referee
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
  (0,0,0)(1,1,1)(2,0,0), and it needs no inaccessible. Now $`x_F \gt T_\omega`$ holds with no hypothesis (§7.1 and §7.4, 2 reviews);
  H-LIFT is needed only for the name of $`T_\omega`$.
- **Theorem CH-LOW-1** (proved given FF, 1 review; $`R_2^C`$). FF is the hypothesis that every $`\gamma \lt \theta_0`$ lies below the least
  realization of some fan-free pattern. Given FF, $`f_0`$, $`m_3`$, $`c_0`$, $`c_1`$, $`c_2`$ are all $`\gt \theta_0`$, so every InaccPsi name of them
  contains an inaccessible. FF is open; it would follow from the lower-bound program below $`\theta_0`$ ([README.md](README.md) §3)
  together with "the patterns $`\Phi_3(M)`$ for standard $`M`$ below SRO have no fan" (checked on every scanned matrix). In $`R_2^S`$ the same
  argument is circular.
- **Not proved** (blocking point, 1 review): "given FF, the first fan $`x_F`$ is $`\gt \theta_0`$, so it needs an inaccessible". FF bounds only
  $`\sigma_F`$, and DOM_F puts $`\sigma_F`$ only below the first closed fan $`f_0`$; $`x_F \lt \sigma_F`$ is not excluded (now $`x_F \lt \sigma_F`$ is proved, [COVER.md](COVER.md) §5.3). Also not proved as stated:
  "$`\theta_0`$ is excluded as a limit of caps, given FF". Now $`x_F \gt \theta_0`$ is proved given a stronger hypothesis $`FF_N`$ (§7.4).
- **Open**: no fan and no chain of length 3 is exhibited below $`\theta_1 = \psi_{\Omega_1}(\psi_{I_1}(0))`$ (the upper half for $`k = 1`$).

## 7. The levels above $`\nu`$, the ghost, and the first fan

This section is the third round: four papers, each refereed once. It uses the notation of §5 and §6. The **depth** of a pair
$`(x, y)`$ is the largest $`k`$ such that $`(x, y)`$ is the outer pair of a $`k`$-nest. For $`\xi \lt T_\omega`$, $`T_k(\xi)`$ is the least top of a
$`k`$-nest above $`\xi`$. The **level-$`k`$ tops** $`\mathrm{Top}_k`$ are the points $`\beta^k_0 = T_k`$, $`\beta^k_{g+1} = T_k(\beta^k_g)`$, and the
**level-$`k`$ restarts** $`\mathrm{Res}_k`$ are the suprema $`\beta^k_l`$ at limits $`l`$. At level 1 these are the $`\delta`$-points and the restarts
of §4 (by SKEL$`^\omega`$ below); level 2 starts with $`(s_2, x_2, T_2) = (m_0, a_0, \nu)`$. A **long pair** is $`a \lt_2 b`$ with $`b \lt \mathrm{lh}(a)`$,
that is $`a \le_1 b+1`$. $`(x_L, y_L)`$ is the least long pair, and $`m_L = \min\{m : m \le_1 x_L\}`$.

### 7.1 The structure below $`T_\omega`$ (LIFT-REC restated)

- **Lemma DEEP** (proved, 1 review; $`R_2^S`$ and $`R_2^C`$). If $`x \lt_2 y`$ and $`\mathrm{lh}(x) \gt y`$, then $`(x, y)`$ is the outer pair of a
  $`k`$-nest for every $`k`$.
- **Corollary D** (proved, 1 review; both). Below $`T_\omega`$ every pair has finite depth, and the reach of its left end is its right end.
  Two pairs are nested or disjoint. Each left end has one right end, each right end has one left end, and no point is both. A
  point strictly inside a pair $`(x, y)`$ has its reach below $`y`$.
- **Every fan apex and every long left end lies above $`T_\omega`$** (proved, **2 reviews**: Corollary D here and LONG-NEST of §7.4,
  two independent papers). So $`x_F \gt T_\omega`$ with no hypothesis.
- **Theorem SH** (proved, 1 review; both; every level $`k`$). LIFT-0 (§5) holds for every block of every level, not only the first.
  For $`\xi \lt T_\omega`$: $`T_k(\xi)`$ exists; no point of $`(\xi, T_k(\xi)]`$ reaches beyond $`T_k(\xi)`$; $`T_k(\xi)`$ has exactly one
  $`\lt_2`$-predecessor $`x_k(\xi) \gt \xi`$; and the set $`U_k(\xi)`$ of the $`\lt_1`$-predecessors of $`x_k(\xi)`$ above $`\xi`$, together with
  $`x_k(\xi)`$ and $`T_k(\xi)`$, has the shape of $`U_k`$ in LIFT-0. The level-$`k`$ tops and restarts exhaust $`[0, T_\omega)`$. Only points of
  $`\mathrm{Res}_k`$ reach past a level-$`k`$ top above them. No pair of depth at most $`k`$ crosses a point of $`\mathrm{Top}_k \cup \mathrm{Res}_k`$. The
  level-$`(k+1)`$ tops, the left ends of pairs of depth $`k+1`$, and every $`U_{k+1}(\xi)`$ lie in $`\mathrm{Res}_k`$. The referee asked
  for two wording fixes (one descent step, and one missing line in the cofinality argument).
- **LIFT-REC, restated** (1 review). The lift is now a recursion, not an image. Level $`k`$ carries over level $`k-1`$ the structure that the
  $`\upsilon`$-points, the $`\delta`$-points and the restarts carry over $`R_1^+`$. Its skeleton $`Y_k`$ is $`\mathrm{Res}_k`$ together with all the
  chains $`U_k(\xi)`$. The shape clauses are proved in both structures (by DEEP and SH). They include
  $`Y_{k+1} \subseteq \mathrm{Res}_k \subseteq Y_k`$, which fixes the blocking point of §5: level $`k`$ goes on past $`s_{k+1}`$, and the
  conjectured names $`\xi \mapsto \psi_{\Omega_1}(\Omega_\omega\cdot k + P_k\cdot\xi)`$ go on past $`\xi = \Omega_\omega`$. Open: that every chain $`U_k(\xi)`$ has the shape
  of §5 Theorem O (index $`\omega`$ at its left end), the exact reaches, the gaps as base-changed copies of $`[1, s_k)`$, and the names. The
  "level-$`k`$ base change" in the paper is not defined, so that clause is a program, not a statement. That $`P_k`$ is an
  $`\varepsilon`$-number is checked only.
- **Theorem NU-CT$`_\omega`$** (proved, 1 review; $`R_2^C`$). Either $`\beta_0 \ge T_\omega`$ (of $`R_2^S`$): then $`R_2^C = R_2^S`$ on every relation with
  right end below $`T_\omega`$, and all of §7.1 holds in $`R_2^C`$. Or $`\beta_0 \lt T_\omega`$ and $`\beta_0`$ is a ghost stage: $`R_2^C`$ has an
  extra pair $`\rho_L \lt_2 \beta_0`$, where $`\rho_L`$, the largest $`\lt_1`$-predecessor of $`\beta_0`$, is a restart and the only
  $`\lt_2`$-predecessor of $`\beta_0`$ in $`R_2^C`$; $`\beta_0`$ is a restart and not a right end in $`R_2^S`$; the extra pair has depth at least 2.
- **Outline only in this round, now proved** ([COVER.md](COVER.md) §5.1, 1 review each). The referee found no error in the following, but each
  uses Theorem SKEL$`^\omega`$, which the paper gives as an outline and which was not refereed to proof level. The paper labels some
  of them "proved"; the referee relabels them (blocking point about labels only). SKEL$`^\omega`$ now has a refereed proof, with
  the corrected wording of SKEL⁺ (§2), so all of them are proved.
  - SKEL$`^\omega`$: SKEL⁺ (§2) holds on all of $`[0, T_\omega)`$ with the pairs of higher depth allowed. The pairs of depth 1 are exactly
    the standard pairs, and every other pair joins two restarts. So $`R_2^S`$ is skeletal there in the weaker form "every pair joins
    two $`\upsilon`$-points", FRAG2 holds in that form, and RIGHT (§1) holds for every pair with left end below $`T_\omega`$. Its clause on
    reaches has the same correction as SKEL⁺: the reach of a restart is closed in $`R_1^+`$ only when that reach is below the top of its
    block (always so below $`\Theta_P`$).
  - TAIL and TAIL-GAP: every use of the assumption $`\lambda \le \Lambda^*`$ is listed and replaced. So above any base $`w \lt T_\omega`$, in
    particular in every gap of every chain, the reaches of the restarts follow the formal-reach recursion of §4 run above $`w`$
    (the upper bound uses no FRAG; equality uses FRAG).
  - TOP: let $`k \ge 2`$, let $`L \in \mathrm{Res}_k`$ not be a right end, and let $`T_k(L)`$ be the first level-$`k`$ top above $`L`$. Then
    $`\mathrm{lh}(L) \le T_k(L) + c^k(L)`$, where $`c^k`$ is the formal offset of §4 run among the level-$`k`$ restarts. If $`L`$ has finite
    Cantor–Bendixson rank $`n`$ in $`\mathrm{Res}_k`$, this gives $`\mathrm{lh}(L) \le T_k(L) + n + 1`$. Lower bounds: $`L \le_1 \delta^L_1`$, and
    $`L \le_1 \rho_{L+\omega^2}`$ given FRAG.
  - In the level-2 structure theorem on $`[s_2, T_3)`$, the clauses on level 1 inside it and on the reaches. Its other clauses are
    proved (1 review): one pair per level-2 block, the blocks, caps and chains as in SH, and no fan, no chain of length 3 and no
    long left end on $`[0, T_\omega]`$.
- **$`T_\omega`$** (Theorem NU-OMEGA). Proved (1 review): $`T_\omega`$ is in no pair and has no $`\lt_1`$-predecessor (as in NEST);
  $`\mathrm{lh}(T_\omega) \le Y_{LL}`$, where $`Y_{LL}`$ is the least $`y'`$ with $`x \lt_2 y \lt y'`$ and $`x \le_1 y'`$ for some $`x, y`$; and $`Y_{LL}`$ lies
  above every level structure that starts just above $`T_\omega`$. Outline in this round, now proved ([COVER.md](COVER.md) §5.1): $`T_\omega`$ is a restart, a limit of $`\mathrm{Top}_k`$ for every
  $`k`$, and its block 0 is standard. **Not proved** (blocking point): "given FRAG, $`T_\omega \le_1 \rho_{T_\omega+\omega^2}`$". The proof needs
  the whole region of $`T_\omega`$ to be standard, and only block 0 is shown. (The whole region is now shown standard, [COVER.md](COVER.md) §5.1;
  the rest of this proof has not been reviewed again, so it stays not proved.) "Every level decomposition goes on above $`T_\omega`$" is
  argued only in part. **Conjecture**: $`\mathrm{lh}(T_\omega) = y^* + 1 = Y_{LL}`$, where $`(x^*, y^*)`$ is the least pair of infinite depth above
  $`T_\omega`$. Then the first block at level $`\omega`$ does not have the LIFT-0 shape.

### 7.2 Base changes between the gaps of a level (GI)

Write $`U_k = \{\upsilon^k_\zeta : \zeta \le o_k + 1\}`$ in increasing order, so $`s_k = \upsilon^k_0`$, $`x_k = \upsilon^k_{o_k}`$, $`T_k = \upsilon^k_{o_k+1}`$. By
LIFT-0, $`o_k`$ is a limit $`\ge \omega`$, and $`o_1 = \omega`$ (Theorem T). The gaps are $`G_\zeta = [\upsilon^k_\zeta, \upsilon^k_{\zeta+1})`$. A base change
at a limit $`\zeta \le o_k`$ copies $`G_\zeta`$ into an earlier gap $`G_\eta`$ and sends $`\upsilon^k_\zeta`$ to $`\upsilon^k_\eta`$. There are three forms:
the global $`GI_k(\zeta)`$ (an onto map; in $`R_2^C`$ both directions are coverings), the local $`GI^{loc}_k(\zeta)`$ (finite copies inside
one gap, with a back property inside that gap), and the finite $`GI^{fin}_k(\zeta)`$ (finite copies with Wilken's Property 2 of
2020, Prop 21.11, bounded by a number $`m`$).

- **Lemma GAPCAP** (proved, 1 review; both). For $`y`$ in a gap $`G_\zeta`$, $`\sup\{\mathrm{lh}(u) : \upsilon^k_\zeta \lt u \le y\} \lt \upsilon^k_{\zeta+1}`$.
- **Theorem HIER** (proved, 1 review; both). For every limit $`\zeta \le o_k`$:

```math
GI_k(\zeta) \Rightarrow GI^{loc}_k(\zeta) \Rightarrow GI^{fin}_k(\zeta) \Leftrightarrow \upsilon^k_\zeta <_2 \upsilon^k_{\zeta+1} \Leftrightarrow \zeta = o_k .
```

  The new step "$`\lt_2`$ gives $`GI^{fin}`$" (Lemma LOC, proved) uses GAPCAP and one $`\Sigma_2`$ sentence. So the last gap $`[x_k, T_k)`$ is
  always copied, base to base, into cofinally many earlier gaps, and every form of GI fails at every limit $`\zeta \lt o_k`$. Theorem O
  of §5 now needs only $`GI^{fin}_k(\omega)`$, and conversely $`o_k = \omega`$ gives $`GI^{fin}_k(\omega)`$. The referee's blocking point is about
  what this means: $`GI^{fin}_k(\omega)`$ is another name for $`\upsilon^k_\omega \lt_2 \upsilon^k_{\omega+1}`$, so "$`o_k = \omega`$ iff $`GI^{fin}_k(\omega)`$" restates
  the pair clause of LIFT-0. It is not progress on $`o_k = \omega`$.
- **Proposition SEG1** (proved given Lemma ST of FRAG, 1 review; $`k = 2`$; $`R_2^S`$, and $`R_2^C`$ below $`\nu_C`$). For
  $`\eta \lt \zeta \le o_2`$, Wilken's map $`\pi_{c,a}`$ with $`a = \upsilon^2_\zeta`$ and $`c = \upsilon^2_\eta`$ is an isomorphism from
  $`c \cup (T^a[c] \cap [a, a^\infty))`$ onto $`[0, c^\infty)`$, where $`a^\infty`$ is the least $`\upsilon`$-point above $`a`$. This is GI on the first
  $`R_1^+`$-segment of every gap.
- **Not proved.** Proposition LOW1 (the substitution map is an isomorphism on the low part of a gap): an outline built on TAIL-GAP,
  which was then an outline (TAIL-GAP is now proved, [COVER.md](COVER.md) §5.1); its statement and proof do not match (blocking point). Neither $`o_k = \omega`$ for $`k \ge 2`$ nor any
  form of $`GI_k(\omega)`$ was proved in this round (now $`o_k = \omega`$ and $`GI^{fin}_k(\omega)`$ are proved in $`R_2^C`$, §8.1; $`R_2^S`$ is open). What blocks: an onto level-$`k`$ hull (for $`k = 2`$ this is (N-χ) of §7.3), the reaches beyond the
  low part of a gap, and for $`k \ge 3`$ a test for new pairs.

### 7.3 The ghost and the name of $`\nu`$

Here $`\nu = \nu_S`$ and $`U_2 = \{\upsilon^2_\zeta\}`$ as in §7.2. $`\mathrm{Car}_S(\alpha, \beta, i)`$ is Carlson's covering condition for $`\le_i`$ (Carlson
2009, Def 5.3), evaluated inside $`R_2^S`$. A **long restart** is a restart whose reach passes its first pair and the next restart. A
**$`K`$-chain** is a $`\lt_1`$-chain of $`K`$ long restarts.

- **Theorem LOC** (proved, 1 review). $`\beta_0`$ is the least $`\beta`$ at which $`\mathrm{Car}_S(\cdot, \beta, i)`$ differs from $`R_2^S`$. So $`\nu_C = \nu_S`$ iff
  $`\mathrm{Car}_S(\alpha, \beta, i)`$ implies $`\alpha \le_i^S \beta`$ for all $`\alpha \lt \beta \le \nu_S`$ and $`i = 1, 2`$. The ghost question is a question
  about $`R_2^S`$ alone; Conjecture CORE-2 is not needed for it.
- **Lemma G1′** (proved, 1 review). If there is a ghost, then for every $`K`$ the $`K`$-chains are cofinal below $`\beta_0`$. This fixes a minor
  gap in Lemma GHOST (§2).
- **Theorem LOCATE** (proved, 1 review). A ghost pair $`\rho_L \lt_2 \beta_0`$ lies in exactly one of four places: (P1) $`\beta_0 \lt m_0`$;
  (P2) $`\rho_L`$ is inside a gap of $`U_2`$ and $`\beta_0`$ is below the next point of $`U_2`$; (P3a) $`\rho_L = \upsilon^2_\zeta`$ with $`\zeta`$ a limit, and
  $`\beta_0`$ is strictly inside the next gap; (P3b) $`(\rho_L, \beta_0) = (\upsilon^2_\zeta, \upsilon^2_{\zeta+1})`$ with $`\zeta`$ a limit below $`o_2`$, which forces
  $`o_2 \gt \omega`$.
- **Theorem GR** (proved as a reduction, 1 review). NOLIM and $`o_2 = \omega`$ together give $`\nu_C = \nu_S`$. NOLIM says that no point of
  $`(0, \nu)`$ outside $`U_2`$ has $`K`$-chains cofinal below it for every $`K`$; it is the level-2 form of "the supremum of an infinite
  $`\lt_1`$-chain of $`R_1^+`$ is a $`\upsilon`$-point". NOLIM holds on $`(0, \nu_P]`$ (proved); above $`\nu_P`$ it is open.
- **Proposition RICH** (proved, 1 review). Let $`b`$ be a restart in $`(a_0, \nu)`$ such that no point of $`(a_0, b)`$ is $`\le_1 b`$. Then
  $`\mathrm{Car}_S(a_0, b, 2)`$ holds iff every finite pattern of the gap $`(a_0, \nu)`$ occurs cofinally below $`b`$. Such a $`b`$ always gives a
  ghost. Given $`o_2 = \omega`$ and LL (an infinite $`\lt_1`$-chain of restarts below $`\nu`$ has its supremum in $`U_2`$), a ghost exists iff
  such a $`b`$ exists.
- **Lemma NAME-RED** (proved, 1 review). Let $`L(\xi) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \theta'\cdot\xi)`$. NU-NAME (§2) holds iff all three hold:
  (O) $`o_2 = \omega`$; (N-χ) $`\upsilon^2_n = L(n)`$ for every $`n \lt \omega`$; (N-ν) $`\nu = L(\omega+1)`$. The name of $`m_0`$ is (N-χ) at $`n = 0`$, and the
  name $`a_0 = L(\omega)`$ follows from (O) and (N-χ). The statement (O) is shared with the ghost question. The referee notes that a proof of
  (N-ν) still needs $`\Sigma_1`$ copies at restarts with long reaches (the kind of FRAG-E).
- **Open**: $`\nu_C = \nu_S`$, $`o_2 = \omega`$ (now proved in $`R_2^C`$, §8.1), NOLIM above $`\nu_P`$ (now reduced to one statement per gap, §8.4), (N-χ) and (N-ν). The referee notes that no proved fact contradicts NOLIM or
  LL, and that LL with $`o_2 = \omega`$ says that $`a_0`$ is the least point whose $`\lt_1`$-predecessors form a cofinal set of restarts.
  That is the remaining content of these questions.

### 7.4 The first fan and the first inaccessible

- **Lemma MATCH** (proved, 1 review; both). Below $`x_F`$, $`\lt_2`$ is a laminar matching: each left end has exactly one right end, a right
  end is never a left end, and two pairs are nested or disjoint.
- **Theorem FAN-CAP** (proved, 1 review; both). $`x_F`$ has exactly two $`\lt_2`$-successors $`y_1 \lt y_2`$, and $`y_2 = \mathrm{lh}(x_F)`$ is the
  least top of any fan. For the least closed fan, $`\mathrm{lh}(f_0)`$ is its largest right end, which is the least top of a closed fan.
- **Theorem OPEN-C** (proved, 1 review; $`R_2^C`$, from Carlson 2009, Thm 14.10). The least fan is the least realization of the
  open-fan pattern PT, and it is open ($`y_1 \le_1 y_2`$ fails). So $`x_F \lt f_0`$ strictly. In $`R_2^S`$ the same holds if $`\beta_0`$ is above the
  least top of a fan of $`R_2^C`$.
- **Lemma LONG** (proved, 1 review; both; a routine fix: add the point 1 to the parameters). Every fan apex is the left end of a long
  pair, and long pairs are cofinal below every fan apex. The least long pair has exactly one right end, and
  $`\mathrm{lh}(x_L) = y_L + 1`$. The referee adds a proof of $`\mathrm{lh}(m_L) = y_L + 1`$, which the paper had as a conjecture.
- **Theorem LONG-NEST** (proved, 1 review; both). Below every long left end, $`k`$-nests are cofinal for every $`k`$. So
  $`T_\omega \lt x_L \lt x_F`$ with no hypothesis (2 reviews together with Corollary D of §7.1).
- **Conjecture FF-LIFT of §5 is false** (proved, 1 review). The configuration LP of one long pair ($`x \lt_2 y`$, $`x \le_1 y+1`$) has no fan,
  and its least realization $`(x_L, y_L, y_L+1)`$ lies strictly between $`T_\omega`$ and $`x_F`$; $`\mathrm{lh}(T_\omega) \le y_L + 1 \lt x_F`$. So new
  fan-free kinds of $`\Sigma_1`$ sentences appear between $`T_\omega`$ and the first fan.
- **Theorem FAN-REFL** (proved, 1 review; both; the same routine fix). Let N be the least class of configurations that contains the
  empty one and is closed under three steps: N($`Q_1`$, $`Q_2`$) (a pair $`a \lt_2 b`$ with the point $`b+1`$, $`Q_1`$ inside $`(a, b)`$, $`Q_2`$ above
  $`b+1`$, and $`a \le_1`$ every point of $`Q_1`$, of $`Q_2`$ and $`b`$, $`b+1`$), putting one configuration above another, and taking
  sub-configurations. Every configuration of N occurs cofinally below every fan apex. So $`\sigma_N \lt x_F`$, where $`\sigma_N`$ is the
  supremum of the least tops of the configurations of N.
- **conv at level $`\omega`$** (proved, 1 review; $`R_2^C`$). Let $`Q_\omega`$ = (0,0,0)(1,1,1)(2,0,0) (row 28 of [README.md](README.md) §6),
  $`K_\omega`$ = (1,1,0)(2,2,1)(3,0,0), $`X_\omega = Q_\omega K_\omega(2,0,0)`$ and $`Y_\omega = X_\omega K_\omega`$. The points of $`\Phi_3(Q_\omega)`$, $`\Phi_3(X_\omega)`$ and
  $`\Phi_3(Y_\omega)`$ are exactly $`m_L`$, $`x_L`$ and $`y_L`$. The referee adds, by the same proof (not reviewed separately): the point of
  $`\Phi_3`$((0,0,0)(1,1,1)(2,2,1)) is exactly $`m_F = \min\{m : m \le_1 x_F\}`$, and $`\sigma_N \le m_F \lt x_F`$.
- **FF made precise** (1 review). FF of §6 ($`\sigma_F \ge \theta_0`$) stays open. The paper replaces it by $`FF_N`$: $`\sigma_N \ge \theta_0`$. Proved:
  L1p-HYP implies $`FF_N`$, and $`FF_N`$ implies both $`x_F \gt \theta_0`$ and FF. Here L1p-HYP says that every realization of the configuration
  L1p ($`x_1 \lt_2 y_1 \lt x_2 \lt_2 y_2`$ with $`x_1 \le_1 x_2`$, $`x_1 \le_1 y_2`$) has $`x_1 \ge \theta_0`$. Checked (one replayed certificate): POINT-SRO
  implies L1p-HYP, where POINT-SRO says that the point of $`\Phi_3(\mathrm{SRO})`$ is $`\ge \theta_0`$. "FF implies $`x_F \gt \theta_0`$" is still open. Now (1 review each, [FANFREE.md](FANFREE.md) §4): $`\sigma_N = m_F`$, so $`FF_N`$ is
  equivalent to $`m_F \ge \theta_0`$; and POINT-SRO implies L1p-HYP by a hand proof.
- **Theorem CH-LOW-1′** (proved given $`FF_N`$, 1 review; $`R_2^C`$). Given $`FF_N`$, the points $`x_F`$, $`f_0`$, $`m_3`$, $`c_0`$, $`c_1`$, $`c_2`$ are all
  $`\gt \theta_0`$, so their InaccPsi names contain an inaccessible. This answers the blocking point of §6 only under $`FF_N`$, which is
  stronger than FF.
- **Does the first fan need $`I_0`$?** Open. The answer is yes given $`FF_N`$, but this is immediate, since $`FF_N`$ already gives
  $`x_F \gt \theta_0`$. With the referee's addition above it is one statement about one matrix: if the point of
  $`\Phi_3`$((0,0,0)(1,1,1)(2,2,1)) is $`\ge \theta_0`$, then the first fan needs $`I_0`$ (the converse is open). Now this statement is equivalent to a lower bound for
  fan-free patterns whose right ends have no reach ([COVER.md](COVER.md) §5.3); the seventh round proves several uniform steps of it, not all
  ([COVER.md](COVER.md) §6.1).
- **Names** (conjecture; conv and Ytosk's reading agree on the three matrices). With $`P_\omega = \psi_{\Omega_2}(\Omega_\omega\cdot\omega)`$:
  $`m_L = T_\omega = \psi_{\Omega_1}(\Omega_\omega\cdot\omega)`$, $`x_L = \psi_{\Omega_1}(\Omega_\omega\cdot\omega + \omega^{P_\omega+1})`$, $`y_L = \psi_{\Omega_1}(\Omega_\omega\cdot\omega + \omega^{P_\omega+1} + P_\omega)`$.
  None of them needs an inaccessible. The same terms are the conjectured $`(x^*, y^*)`$ of §7.1. The least fan and $`f_0`$ have no
  supported name.

## 8. The fourth round: $`o_k = \omega`$ and NOLIM

This section is the fourth round: four papers, each refereed once. Three of them attack $`o_2 = \omega`$ (§7.2, §7.3) by three
routes, and the fourth attacks NOLIM above $`\nu_P`$ (§7.3). Notation as in §7.2: $`U_k = \{\upsilon^k_\zeta : \zeta \le o_k + 1\}`$,
$`x_k = \upsilon^k_{o_k}`$, $`T_k = \upsilon^k_{o_k+1}`$, and $`G_\zeta = [\upsilon^k_\zeta, \upsilon^k_{\zeta+1})`$. $`\mathrm{Pred}_1(b) = \{a \lt b : a \le_1 b\}`$.
**Result of the round:** $`o_k = \omega`$ is proved in $`R_2^C`$ for every $`k`$ (§8.1). In $`R_2^S`$, $`o_2 = \omega`$ and NOLIM above $`\nu_P`$ stay
open, and so does $`\nu_C = \nu_S`$.

### 8.1 $`o_k = \omega`$ in $`R_2^C`$ (the covering route)

- **Lemma MOVE** (proved, 1 review; $`R_2^C`$). Let $`Z`$ be a finite closed set, $`u \in Z`$ additively principal, $`X = Z \cap u`$, and
  $`\alpha`$ additively principal with $`\max X \lt \alpha \lt u`$. Let $`f^+`$ be the closed embedding of $`Z`$ that sends $`u`$ to $`\alpha`$ and
  fixes every other indecomposable of $`Z`$ (Carlson 2009, L.4.4–4.5). Then $`f^+ \le \mathrm{id}`$, and $`f^+`$ is a covering of $`Z`$ if
  (M1) $`\alpha \le_1 v^*`$ with $`v^* = \max\{v \in Z : u \le_1 v\}`$, and (M2) no $`v \in Z`$ has $`u \lt_2 v`$. No reach is used. (The paper
  also asks $`\alpha \le_1 u`$; the referee notes that this follows from (M1).)
- **Theorem CP** (proved, 1 review; $`R_2^C`$). Let $`u`$ be additively principal and in the core of $`R_2^C`$. If $`\mathrm{Pred}_1(u)`$ is cofinal
  in $`u`$, then $`u`$ is a $`\lt_2`$-left end. Proof: an isominimal set that contains $`u`$ is its own least realization (Carlson 2009,
  Def 2.6 and Thm 14.10(2)); MOVE gives a closed covering of it that moves $`u`$ down, against the minimality of Thm 14.10(2),
  which holds against all coverings, not only against isomorphic copies. The referee checked this citation word for word.
- **Theorem O$`^C`$** (proved, 1 review; $`R_2^C`$; every $`k \ge 1`$; no hypothesis). $`o_k = \omega`$. So
  $`x_k = \upsilon^k_\omega = \sup_n \upsilon^k_n`$, $`T_k = \upsilon^k_{\omega+1}`$ and $`\mathrm{Pred}_1(x_k) = \{\upsilon^k_n : n \lt \omega\}`$. Proof: if $`o_k \gt \omega`$,
  then $`s = \upsilon^k_\omega \lt x_k`$ lies in the core (the core contains $`[0, T_k]`$, because $`T_k`$ is the top of the least realization of a
  $`k`$-nest; Carlson 2009, Thm 14.14), and the points $`\upsilon^k_n`$ are cofinal in $`s`$ and $`\le_1 s`$. CP makes $`s`$ a left end, but by
  LIFT-0 (§5) the only left end in $`U_k`$ is $`x_k`$. No base change, hull or reach is used. For $`k = 1`$ this is a new proof of
  $`o_1 = \omega`$ in $`R_2^C`$ from Carlson 2009 alone.
- **Corollary LEAST** (proved, 1 review). In the least realization of a $`k`$-nest, $`x_k`$ is the supremum of the points made by $`n`$
  downward 2-reflections of the pattern (Carlson 2009, Def 9.4), and the $`n`$-th of them is $`\upsilon^k_{n-1}`$.
- **Consequences in $`R_2^C`$** (proved, 1 review). Theorem O of §5 and $`GI^{fin}_k(\omega)`$ of §7.2 hold for every $`k`$ with no hypothesis;
  $`U_k \cap x_k`$ has no limit point; the last gap $`[x_k, T_k)`$ is copied, base to base, into gaps $`G_n`$ with $`n \lt \omega`$. The shape part
  of NU-NAME holds in $`R_2^C`$: $`x_2 = \upsilon^2_\omega`$ and $`\nu_C = \upsilon^2_{\omega+1}`$. Every isominimal set that contains $`x_k`$ contains $`T_k`$.
- **Transfer to $`R_2^S`$** (proved, 1 review). (a) If the two structures agree on every relation with right end at most $`T_k`$ of
  $`R_2^S`$, then $`o_k = \omega`$ in $`R_2^S`$; in particular $`\nu_C = \nu_S`$ implies $`o_2 = \omega`$ in $`R_2^S`$ (before, only the converse direction,
  given NOLIM, was known: GR, §7.3). (b) If $`o_2 \gt \omega`$ in $`R_2^S`$, a ghost exists; in case (P2) of LOCATE its gap has a finite index.
  (c) Given NOLIM: $`\nu_C = \nu_S`$ iff $`o_2 = \omega`$ in $`R_2^S`$, and the only possible ghost is the pair $`(\upsilon^2_\omega, \upsilon^2_{\omega+1})`$ of $`R_2^S`$
  (case (P3b)). The paper marked (b) and (c) as resting on unreviewed results; the referee notes that LOC, LOCATE and GR are reviewed
  (§7.3), so they are proved.
- **Open in $`R_2^S`$**: $`o_k = \omega`$ for $`k \ge 2`$. The covering proof does not carry over, for two reasons: $`[0, \nu_S] \subseteq \mathrm{Core}(R_2^S)`$
  is not known, and an isominimal set of $`R_2^S`$ is minimal only against isomorphic copies, while the moved map of MOVE can add a
  $`\le_1`$-relation.

### 8.2 The $`\Sigma_2`$ route ($`R_2^S`$)

Here $`k = 2`$, $`\nu = \nu_S`$ and $`s = \upsilon^2_\omega`$.

- **Proved, but only restating the problem** (1 review; the referee: restatements of the pair clause of LIFT-0, LOC and HIER).
  $`U_2 \setminus \{\nu\}`$ is the set of $`\Sigma_1`$-closed ordinals of $`R|\nu`$, and $`x_2`$ is the only $`\Sigma_2`$-closed one, so
  $`o_2 = \omega \Leftrightarrow s \le_2 \nu \Leftrightarrow s \lt_2 \nu`$. For a finite $`X`$ and a $`\Pi_2`$ sentence with parameters $`X`$, the indices $`\zeta`$ with
  $`R|\upsilon^2_\zeta`$ satisfying it form an initial segment, closed at limits, that contains $`o_2 + 1`$ or ends at a successor index. So
  $`o_2 = \omega`$ iff every $`\Pi_2`$ sentence with parameters below $`s`$ that fails in $`R|\nu`$ fails already in some $`R|\upsilon^2_n`$, $`n \lt \omega`$; and iff
  no $`\Pi_1`$ formula with parameters below $`s`$ has its first realization in the gap $`G_\omega`$.
- **Lemma OFF** (proved, 1 review, from the substitution lemma of §4). Wilken's substitution, segment by segment, gives a map $`\Psi^n`$:
  a $`(\lt, +)`$-isomorphism from the hull of $`G_\omega`$ over the parameters below $`\upsilon^2_n`$ onto the gap $`G_n`$, below an offset
  bound. It keeps the kinds of points and the pairs.
- **Proposition MONO** (proved, 1 review). If for infinitely many $`n`$ the map $`\Psi^n`$ is an isomorphism below $`z`$ and $`\Psi^n\rho \le_1 \Psi^n z`$,
  then $`\rho \le_1 z`$. So where $`G_\omega`$ and almost all finite gaps first disagree, the cap in $`G_\omega`$ is the larger one.
- **Theorem HR** (proved as an implication, 1 review; parts (a), (c) used SKEL⁺, now proved, [COVER.md](COVER.md) §5.1). If two statements HULL$`(n)`$ (on the hull,
  the $`\le_1`$-test can be passed inside the hull) and LEN$`(n)`$ (the index lengths of $`G_n`$ and $`G_\omega`$ are equal) hold for infinitely
  many $`n`$, then $`s \lt_2 \upsilon^2_{\omega+1}`$, so $`o_2 = \omega`$.
- **Not proved** (blocking points). The route is likely empty: LEN$`(n)`$ forces the index length of $`G_\omega`$ to be below $`s`$ (that of $`G_n`$
  is at most $`\upsilon^2_{n+1} \lt s`$), but under the conjectured names (NU-NAME, GEN-EXT) $`G_\omega`$ has $`\upsilon`$-points at index offsets
  $`\ge s`$ (4 instances checked). So, if the names are right, LEN fails for every $`n`$. An onto map must also replace $`s`$ by $`\upsilon^2_n`$
  inside the offsets, as the map of §8.3 does. The claims that HULL and LEN follow from LIFT-REC are not proved; the "no-go"
  remark (an argument about $`U_2`$ alone cannot give $`o_2 = \omega`$) is a remark, not a proof.

### 8.3 The global substitution route ($`R_2^S`$)

- **Theorem GS** (proved, 1 review; transfer of the substitution lemma of §4, no FRAG). A **block map** $`\sigma'`$ is an order isomorphism
  from a set of restart indices of $`G_\zeta`$, containing its base index, onto all restart indices of $`G_\eta`$. Its substitution map $`T_\sigma`$
  is an isomorphism for $`0`$, $`\le`$, $`+`$ and the $`\le_1`$ of $`R_1^+`$ from $`c \cup D_\sigma`$ onto $`[0, \upsilon^2_{\eta+1})`$, where $`c = \upsilon^2_\eta`$; it is the
  identity below $`c`$, sends $`\upsilon^2_\zeta`$ to $`c`$, has closed domain and range, and commutes with Wilken's maps.
- **Theorem RED** (proved, 1 review; through SKEL⁺, now proved, [COVER.md](COVER.md) §5.1). $`T_\sigma`$ is an isomorphism of $`R_2^S`$ iff the reaches of the
  moved restarts correspond: for every moved restart $`\lambda`$ and $`z \in D_\sigma`$, $`z \le r(\lambda) \Leftrightarrow T_\sigma z \le r(\sigma'\lambda)`$ (RI). The
  same holds in $`R_2^C`$ below $`\nu_C`$ with coverings. So if such maps exist for every finite subset of $`G_\omega`$ and cofinally many $`n`$,
  then $`GI_2(\omega)`$ and $`o_2 = \omega`$ (proved; it was an outline before [COVER.md](COVER.md) §5.1).
- **Lemma INT** (proved, 1 review). A block map that shifts an initial segment moves only bases of small index offset; under the
  conjectured names $`G_\omega`$ has points beyond (checked).
- **Not proved** (blocking point). The shift map already fails (RI) at the restart with index offset $`c`$, so it is an isomorphism only
  if the restart indices of $`G_\eta`$ have order type at most $`c`$, which fails under the conjectured names for $`\eta = 0, 1, 2`$
  (checked). Any block map has to act on index offsets like the substitution, not by order type. Proposition RANK (RI at restarts
  of finite Cantor–Bendixson rank) is false as stated at the base index and correct above it (outline). What is left is one
  statement: the skipped restarts never change where the reach of a moved restart cuts the domain. It joins the two blockers
  of GI (§7.2: the onto hull and the reaches) into one. On the initial part of each segment of level 2 this statement is now settled
  at outline level (RM-P, [FANFREE.md](FANFREE.md) §3), and now proved below the first limit of critical indices of each segment (RM-D, [FANFREE.md](FANFREE.md) §7.3), and on a larger part (RM#,
  [FANFREE.md](FANFREE.md) §10.3); but the reduction always needs long restarts, where no closed form applies (NEED-C, same place). A direct
  $`\Sigma_2`$ argument matches every extension above the copy, the long restarts included, and leaves a local part with a fixed finite set below
  the copy (1 review, [VEBLEN.md](VEBLEN.md) §4). With that set, on the zone of the base change and given an open condition (HC), the local part holds,
  but the translations fail there, so that reduction does not work (1 review, [VEBLEN.md](VEBLEN.md) §11).

### 8.4 NOLIM above $`\nu_P`$

For $`g \in G = \{0\} \cup (U_2 \setminus \{\nu\})`$ let $`g^+`$ be the next member of $`U_2`$; the gap of $`g`$ is $`(g, g^+)`$. $`b`$ is a **LIM point** if for every
$`K`$ and every $`\gamma \lt b`$ there is a $`K`$-chain inside $`(\gamma, b)`$; NOLIM says that no point of $`(0, \nu) \setminus U_2`$ is a LIM point. $`C_K`$ is the
configuration $`\chi_1 \lt t_1 \lt d_1 \lt \cdots \lt \chi_K \lt t_K \lt d_K \lt \chi_{K+1}`$ with $`\chi_i \le_1 \chi_{K+1}`$ and $`t_i \lt_2 d_i`$; $`e_K(g)`$ is the least top of a
realization of $`C_K`$ above $`g`$, $`E(g) = \sup_K e_K(g)`$, and $`b^*(g)`$ is the least LIM point above $`g`$.

- **Lemma CH** (proved, 1 review; through SKEL⁺, now proved, [COVER.md](COVER.md) §5.1). Below $`\nu`$, $`K`$-chains and realizations of $`C_K`$ give each other.
- **Lemma TRANSFER** (proved, 1 review). For points up to $`\nu`$, LIM goes down along $`\le_1`$ and up along $`\le_2`$; a supremum of LIM points is
  a LIM point; every member of $`U_2`$ is a LIM point.
- **Lemma CAP$`_K`$** (proved, 1 review). No $`\alpha \in (g, e_K(g)]`$ has reach above $`e_K(g)`$. $`E(g)`$ is a restart whose index is a multiple of
  $`\omega^3`$, and $`\mathrm{Pred}_1(E(g)) = U_2 \cap (0, g]`$.
- **Theorem ITER** (proved, 1 review; the referee also checked its abstract step in a Lean test file, not part of this library).
  $`b^*(g)`$ is the value where the iteration $`b_0 = g`$, $`b_{n+1} = E(b_n)`$ stops at a LIM point, or the limit of the $`b_n`$. So

```math
\text{NOLIM} \Leftrightarrow \forall g \in G :\ b^*(g) = g^+ ,
```

  and $`E(g) = g^+`$ for every $`g`$ (NOLIM$`^*`$, a conjecture) is enough. (The explicit $`K`$ in the paper's remark is wrong; the
  corollary is not affected.)
- **GAP-LOW** (proved, 1 review; one bound at outline level). NOLIM holds in every gap up to the analogue of $`\nu_P`$ above $`g`$.
- **The ghost** (proved, 1 review). In cases (P1), (P2), (P3a) of LOCATE a ghost forces $`b^*(g) \lt g^+`$ in its gap. So $`b^*(g) = g^+`$ for all $`g`$,
  together with $`o_2 = \omega`$, excludes the ghost (GR in this form).
- **$`R_2^C`$** (proved, 1 review). All of the above holds in $`R_2^C`$.
- **Open**: NOLIM above $`\nu_P`$, in both structures (now proved in $`R_2^C`$, [COVER.md](COVER.md) §3 and §5.1). Below $`\nu`$ the proved results fix every relation except the reaches of the restarts
  inside the gaps, and NOLIM is a statement about those reaches only; they are unknown above the analogue of $`\Theta_A`$ in each gap.

### 8.5 Status after this round

- $`o_k = \omega`$: proved in $`R_2^C`$ for every $`k`$ (1 review, §8.1); open in $`R_2^S`$ for $`k \ge 2`$. The two $`R_2^S`$ routes (§8.2, §8.3) end at
  statements that are likely false as stated (LEN) or not proved (the reach statement of §8.3).
- Consequences in $`R_2^C`$ (1 review): Theorem O and $`GI^{fin}_k(\omega)`$ for every $`k`$; the shape part of NU-NAME.
- $`\nu_C = \nu_S`$: open. It implies $`o_2 = \omega`$ in $`R_2^S`$, and given NOLIM it is equivalent to it. NOLIM above $`\nu_P`$: open, reduced to
  $`b^*(g) = g^+`$ in every gap.
- The names (N-χ) and (N-ν) of §7.3: untouched.

## 9. Checks

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
- Levels (§7.1). The patterns of 3,667 standard matrices below row 28 satisfy every finite consequence of DEEP and SH (0
  violations), and the first restarts of levels 2 and 3 reach exactly "top + 1", the bound of TOP. Above row 28 (199 matrices)
  the only violations are long left ends reaching "partner + 1". The referee reran 16,396 standard patterns: no counterexample.
  But below row 28 the referee found 9 points that reach past two level-2 tops without a long left end, e.g. in
  Q(1,1,0)(2,2,1)(2,2,1)(2,2,0)(3,3,1)(3,3,1)(3,1,0)(4,2,1)(4,2,1)(4,2,0)(5,3,1)(5,3,1). Its pattern is a level-1 restart above $`\Lambda^*`$
  moved one level up, so it is not a counterexample to TOP, but the paper's "no such point below row 28" came from a small
  sample. The names are normal forms and increasing; "$`P_k`$ is an $`\varepsilon`$-number" was checked for $`k = 1, \dots, 4`$.
- Ghost and names (§7.3). $`L(\xi)`$ for $`\xi = 0, \dots, 6, \omega, \omega+1, \omega+2, \omega\cdot 2`$: normal forms and increasing, in Python (two independent
  scripts) and in Lean (a test file, not a proof).
- Base changes (§7.2). Under the conjectured names, $`x_2`$ is below the next $`\upsilon`$-point of level 1, which is below $`\nu`$ (the referee's run).
- First fan (§7.4; $`R_2^C`$; replayed, 5 of them again by the referee): $`\Phi_3(Q_\omega) \lt`$ LP $`\lt \Phi_3(Q_\omega(1,1,1))`$;
  LP $`\lt`$ LNL $`\lt \Phi_3(\mathrm{SRO}) \lt`$ L1p $`\lt`$ L2; L1p, L2 and LP below PT; PT below PTc. With FAN-REFL this gives
  $`x_F \gt`$ the point of L1p $`\gt`$ the point of $`\Phi_3(\mathrm{SRO})`$. No certificate in either direction between $`\Phi_3(X_\omega)`$ and LP, as the
  equal points predict. The referee's searches for certificates that would refute LONG-NEST or FAN-REFL found none, and the
  probes that should fail (PTc below PT, two names for one diagram) gave none. conv prints no fan for the scanned matrices below
  (0,0,0)(1,1,1)(2,2,1), and an open fan for that matrix. 16 names are normal forms and increasing (Python and a Lean test file).

- Fourth round (§8). MOVE: the referee ran its atom logic on random finite models of reflection over $`(\omega^E, +)`$ (3 seeds):
  3,467 cases met (M1) and (M2) with 0 failures; dropping (M2) gave 74 failures and dropping $`\alpha \le_1 v^*`$ gave 2,053, so both
  conditions are needed. §8.2: the 4 named points at offsets $`\ge s`$ are normal forms (the referee's script). §8.3: the program's
  structure of the gaps $`G_1`$, $`G_2`$, $`G_3`$ and the last gap agrees after renumbering on 2,916 standard suffixes (the referee: 2,915,
  0 differences); the program is uniform in the gaps by construction, so this is only a consistency check, and its small cases do
  not reach index offset $`c`$. §8.4: 4,885 program patterns (the referee's rerun: 3,378) show $`C_K`$ only for $`K \le 2`$; the program
  describes one point and what lies above it, so it cannot test NOLIM.

## 10. Open

- RIGHT in $`R_2^C`$ above $`\beta_0`$ (RIGHT-ISO and RIGHT are now proved in $`R_2^S`$, [COVER.md](COVER.md) §5.1). CC as an isomorphism (not needed).
- The name of $`\nu`$: now the three statements (O) $`o_2 = \omega`$ (proved in $`R_2^C`$, §8.1), (N-χ) and (N-ν) (§7.3). $`\nu_C = \nu_S`$ (exclude the ghost): it implies (O) in $`R_2^S`$ (§8.1), and it is reduced to
  NOLIM above $`\nu_P`$ and $`o_2 = \omega`$, both about $`R_2^S`$ (§7.3); NOLIM is now the statement $`b^*(g) = g^+`$ for every gap of $`U_2`$ (§8.4); it is proved in $`R_2^C`$, and $`\nu_C = \nu_S`$ is
  equivalent to NOLIM and $`o_2 = \omega`$ in $`R_2^S`$ ([COVER.md](COVER.md) §3).
- The structure above $`\nu`$: $`o_k = \omega`$ for $`k \ge 2`$ in $`R_2^S`$ (equivalently $`GI^{fin}_k(\omega)`$; proved in $`R_2^C`$, §8.1), the global base change $`GI_k(\omega)`$, the exact reaches of
  level-$`k`$ restarts, the gaps as base-changed copies, and the names (§7.1, §7.2); the reach of $`T_\omega`$. (SKEL$`^\omega`$, TAIL, TAIL-GAP and
  TOP are now proved, [COVER.md](COVER.md) §5.1.)
- The least fan: its name, the name of $`f_0`$, $`FF_N`$ (now the same as $`m_F \ge \theta_0`$, [FANFREE.md](FANFREE.md) §4), L1p-HYP, POINT-SRO, and whether the least fan of $`R_2^S`$ is open (§7.4). Its structure in
  $`R_2^C`$ is now fixed, with order type $`o_F = \omega^2`$ ([COVER.md](COVER.md) §2 and §5.2).
- A chain of length 3: a point of $`(C_{\omega^\omega})'`$ above $`B`$ whose successors accumulate at a left end. Being a left end is not a
  property of a finite configuration, so Carlson's generating rules cannot produce it (NO-GEN). FF, DOM_F in $`R_2^S`$, open fans
  below $`\sigma_F`$, and the upper half below $`\theta_1`$. Conjecture CH. In $`R_2^C`$ the bottoms of chains of length 3 are now exactly the points of the core
  with an infinite $`\le_1`$-chain of right ends (Theorem CP3, [COVER.md](COVER.md) §1); this characterizes the chain but does not locate it.
- The reaches for candidates in $`[\delta_j\cdot\omega, \delta_{j+1})`$; a review of the repaired TOP-REG and REACH; $`R_2^C`$ above $`\nu_C`$; the closed
  forms and names above $`\Lambda_\Gamma`$ ($`\Theta_1`$, $`\Theta_A`$, $`\Theta_\delta`$, $`\Theta_{d\omega}`$, $`\Lambda^*`$, $`\nu_P`$; the closed forms up to $`\Lambda'`$ and the name of $`\Theta_P`$ are
  now proved, [FANFREE.md](FANFREE.md) §10.4, the closed forms up to $`\Lambda_{\mathrm{fp}}`$ too, [VEBLEN.md](VEBLEN.md) §1, and up to $`\Lambda_{\mathrm{fp}2}`$, with $`\Theta_1`$ and $`\Theta_A`$ reduced to the open lemma PAR-SAME, §8; now PAR-SAME is proved and $`\Theta_1`$, $`\Theta_A`$ are named,
  and for $`\Theta_\delta`$, $`\Theta_{d\omega}`$, $`\Lambda^*`$, $`\nu_P`$ lower bounds are proved as a transfer, [THETA.md](THETA.md) §1; now these names are proved, [THETA.md](THETA.md) §9.1); names above $`\upsilon^*`$ beyond GEN-EXT.
- That the assignments between ordinals and patterns are elementary recursive (outline only), and that UNIF is onto.
