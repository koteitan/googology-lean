[← Back](README.md) | [English](BREAK.md) | [Japanese](BREAK-ja.md)

# $`R_2^+`$ where the skeleton ends: INC1, the first non-skeletal point, chains from fans, and finite closures

This page continues [PINS.md](PINS.md). The status words are those of [README.md](README.md) §3: **proved** means that an
independent referee found the result proved with no fatal or blocking point. All results on this page are from
2026-10. They come from four papers, each refereed once. "1 review" means one referee. "2 reviews" means that two
independent papers proved the result and each paper was refereed once. A statement that its referee found not proved,
or false as written, is listed under **Not proved**, even when the rest of its paper is proved. None of the four papers
uses Wilken, JSL 72 (2007), Carlson, AML 38 (1999), or Wilken, AML 45 (2006). No result on this page is in Lean.

**Notation.** As on [REACHES.md](REACHES.md) and [PINS.md](PINS.md). $`\nu_P = \upsilon_{\Lambda^*+\omega^2}`$ is the end of Theorem SKEL. $`\mathrm{lh}_1(a)`$ is the
reach of $`a`$ in $`R_1^+`$. A gap is the interval between two consecutive $`\upsilon`$-points. A **standard pair** is a
$`\lt_2`$-pair $`(\upsilon_{\lambda+\omega j}, \upsilon_{\lambda+\omega j+1})`$ ($`\lambda = 0`$ or a restart index, $`j \ge 1`$); every other $`\lt_2`$-pair is a
**new pair**. A **fan** is a point with two $`\lt_2`$-successors. PS is the pattern "$`x \lt_2 y`$ and $`u \lt_2 v`$ with $`x \lt u \lt v \lt y`$"
(a pair with a pair nested inside). $`\theta' = \psi_{\Omega_2}(\Omega_\omega\cdot 2)`$.

## 1. INC1: reduced to one hypothesis

INC1-S is "$`a \le_1 b`$ in $`R_2^S`$ implies $`a \le_1 b`$ in $`R_1^+`$". INC1-nonups is the same for $`R_2^C`$. Both are trivial when $`a`$ is a
$`\upsilon`$-point, because in $`R_1^+`$ a $`\upsilon`$-point is $`\le_1`$ to everything above it.

- **The earlier remark "INC1-S is trivial in $`R_2^S`$" was wrong** (proved, 1 review). $`\le_1`$ of $`R_2^S`$ is $`\Sigma_1`$ in the language of
  $`R_2^S`$, not in that of $`R_1^+`$, so a copy need not keep the $`\le_1`$-facts of $`R_1^+`$.
- **Lemma LEFT-AT** (proved, 1 review). Lemma LEFT needs INC1 only at its own right end: if $`\alpha \lt_2 \beta`$ and INC1 holds for
  the pairs $`y \le_1 \alpha`$, then $`\alpha = \upsilon_\lambda`$ with $`\lambda`$ a limit. Also Lemma LEFT-SK (proved, 1 review).
- **Bad right ends.** A point $`b`$ that is not a $`\upsilon`$-point is a **bad right end** if there are $`v \lt x \lt b`$ with $`v \lt_2 b`$, $`x \lt_1 b`$,
  and $`x`$ not a $`\upsilon`$-point in the gap of $`b`$. Then $`v`$ is a fan ($`v \lt_2 x`$ and $`v \lt_2 b`$). $`b^*_S`$, $`b^*_C`$ are the least bad
  right ends. **Conjecture NOBAD**: there is none. It follows from **Conjecture RIGHT**: every $`\lt_2`$-right end is a $`\upsilon`$-point.
  (The referee added "$`v \lt x`$" to the definition; the proof only produces such $`v`$.)
- **Theorem INC1-LOC** (proved, 1 review; $`R_2^S`$). INC1-S holds for every pair whose right end is $`\le b^*_S`$. So NOBAD
  implies INC1-S. Proof idea: take the least failing right end $`g_0`$; then $`g_0 = \mathrm{lh}_1(x) + 1`$ for some $`x`$. If no point below
  $`x`$ has a $`\lt_2`$-successor in $`(x, g_0)`$, a copy argument contradicts Wilken, APAL 145 (2007) 162–175, Claim 5.6. Otherwise
  there is a bad right end below $`g_0`$.
- **Theorem INC1-LOC-C** (proved given CC, 1 review). The same for $`R_2^C`$. **CC** (open): copies in $`R_1^+`$ over a fixed
  lower set can be chosen closed under the parts of Cantor normal forms. Carlson 2001 proves it only without a fixed
  lower set (L.5.3 and L.3.18 do not give it).
- **Lower bounds** (proved, 1 review). $`b^*_S \gt \nu_P`$ (Theorem SKEL: below $`\nu_P`$ every left end has one successor).
  $`b^*_C`$ is above the point of $`\Phi_3(\mathrm{SRO})`$ (from replayed certificates: every fan of $`R_2^C`$ lies above that point).
- So **Lemma LEFT** holds (1 review): in $`R_2^S`$ for every left end $`\le b^*_S`$, so on $`[0, \nu_P]`$; in $`R_2^C`$ for every left end
  $`\le b^*_C`$ given CC; everywhere given NOBAD (and CC in $`R_2^C`$).

The results that used LEFT. "Given NOBAD" means given NOBAD in $`R_2^S`$, and given NOBAD and CC in $`R_2^C`$.

| result | new status (1 review) |
|---|---|
| 3CH (i)–(iii) ([REACHES.md](REACHES.md) §4) | proved given NOBAD; unconditional when $`c_1 \le b^*`$ |
| 3CH (iv) | proved, unconditional (it does not use LEFT) |
| FIRST-BREAK ([REACHES.md](REACHES.md) §4, $`R_2^S`$) | proved, unconditional: every use of LEFT is below the first failure of SK1 or SK3, where SK1 gives INC1 |
| C3′-FALSE ([REACHES.md](REACHES.md) §5) | proved given NOBAD; unconditional when $`r_1(\tau) \le b^*`$ |
| VEB ([PINS.md](PINS.md) §4) | proved given NOBAD; unconditional for $`y \le b^*`$ |
| C3-VEB (a)–(c) ([PINS.md](PINS.md) §4) | proved given NOBAD; unconditional when $`c_1 \le b^*`$ |
| NU-C, $`\nu_C \le \mathrm{top}(PT^*) \lt m_3`$ | proved, unchanged (it never used LEFT) |
| NU-C′, $`\nu_C \le \mathrm{top}(PS^*) \lt`$ the point of $`\Phi_3`$(row 28) | proved given CC and the replayed certificates; §2 removes CC |

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
- **Two reviews.** "Every fan apex of $`R_2^S`$ is $`\ge \nu_P`$, and $`m_3 \gt \nu_P`$" now has **2 reviews**: CAP gives it through $`\nu \gt \nu_P`$, and
  Theorem M-S of §3 proves it independently.
- **$`R_2^C`$** (proved, 1 review). Let $`T_C`$ be the top of the least realization of PS in $`R_2^C`$. Then $`\nu_C \le T_C`$ without INC1 or
  CC, CAP holds, and $`[0, T_C] \subseteq \mathrm{Core}(R_2^C)`$. With the certificate "$`T_C`$ is below the point of $`\Phi_3`$(row 28)" (replayed),
  $`\nu_C`$ is below the point of $`\Phi_3`$ of row 28 of the table in [README.md](README.md) §6, now without any hypothesis.
  Whether $`\nu_C = T_C`$, and whether $`\nu_C = \nu_S`$, is open.
- **Certificates** ($`R_2^C`$; replayed by the author, 4 of them again by the referee). With $`Q`$ = (0,0,0)(1,1,1)(1,1,1) (row 27),
  $`K`$ = (1,1,0)(2,2,1)(2,2,1), $`M_a = QK(2,0,0)`$ and $`M_\nu = M_a(1,1,0)(2,2,1)(2,2,1)`$: the least point of PS lies between the
  points of $`\Phi_3(QK^3)`$ and $`\Phi_3(M_a(1,0,0))`$, and $`T_C`$ between those of $`\Phi_3(M_\nu[2])`$ and $`\Phi_3(M_\nu(1,0,0))`$. The least fan
  pattern PT has its point above that of $`\Phi_3(\mathrm{SRO})`$ and below $`m_3`$.
- **Theorem GEN-EXT** (proved, 1 review). Theorem GEN ([PINS.md](PINS.md) §3) holds word for word for $`\eta \lt \Omega_\omega\cdot\omega`$:
  $`\psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta) = \upsilon_{1+\iota(\eta)}`$ for every such $`\eta`$ in $`D`$. **Lemma RI3**: $`\iota(\eta)`$ is a multiple of $`\omega^3`$ iff
  $`\mathrm{logend}(\eta) \ge 3`$. The referee's random test: 480 values of $`\eta`$, 0 mismatches.
- **Conjecture NU-NAME** (normal forms and order checked in Python and Lean): $`m_0 = \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$,
  $`a_0 = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'+1})`$, $`\nu = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'+1} + \theta')`$. The first new pair would copy
  $`(\upsilon_\omega, \upsilon_{\omega+1})`$ one level up. The referee notes that the evidence from Ytosk's reading rests on one new choice
  in the dictionary between readings; two other choices give other terms.
- **The first fan** (proved, 1 review). In $`R_2^S`$ its apex is a new left end above $`\nu`$, and both successors are above $`\nu`$. In
  $`R_2^C`$ it lies above the point of $`\Phi_3(\mathrm{SRO})`$ (certificates). Its name is open.

## 3. Chains of length 3 from fans

$`C_l`$ are the classes of the ladder of [PINS.md](PINS.md) §4 ($`C_1`$ = fixed points of $`\iota \mapsto \upsilon_\iota`$), $`f`$ enumerates $`C_{\omega^\omega}`$, and
$`(C)'`$ is the class of limit points of $`C`$. "Given LEFT" means given INC1-S in $`R_2^S`$ and INC1-nonups in $`R_2^C`$; by §1 this
follows from NOBAD (and CC in $`R_2^C`$).

- **Theorem CF** (proved, 1 review; $`R_2^S`$ with a citation repair by the referee, and $`R_2^C`$). A chain of length 3 with bottom $`a`$ and
  middle $`e`$ exists iff the $`\lt_2`$-successors of $`a`$ are cofinal in $`e`$ and $`e`$ has a $`\lt_2`$-successor. So a chain of length 3 is
  exactly a fan with infinitely many successors whose limit is itself a left end. **Corollary LEAST** ($`R_2^C`$): $`c_0`$ is the
  least bottom of a chain, $`c_1`$ the least left end among the successors of $`c_0`$, and $`c_2`$ the least successor of $`c_1`$.
- **Lemma PI2-UP and Lemma PC** (proved, 1 review). If $`y \le_2 e`$, every finite configuration that is cofinal below $`y`$ is cofinal
  below $`e`$. In every chain of length 3, pairs, fans and the configurations of every level $`l \lt \omega^\omega`$ of the ladder are
  cofinal below $`c_0`$, below each successor of $`c_0`$ and below $`c_1`$; the successors of $`c_0`$ are cofinal in $`c_2`$.
- **Theorem RE** (proved given LEFT, 1 review). If pairs are cofinal below $`y`$ and $`y \lt_2 e`$, then $`e = \upsilon_\mu`$ with $`\mu`$ a restart index.
  If also the ladder configurations of every level $`l \lt \omega^\omega`$ are cofinal below $`y`$, then $`e \in C_{\omega^\omega}`$.
- **Theorem C3′′-FALSE** (proved given LEFT, 1 review). In every chain of length 3, the points $`c_0, c_1, c_2`$ and every successor of
  $`c_0`$ and of $`c_1`$ lie in $`C_{\omega^\omega}`$, and $`c_0, c_1, c_2`$ are limit points of $`C_{\omega^\omega}`$. So the conjectured shape
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
- **Bounds** (proved given LEFT, 1 review). Let $`B = \nu_P`$ in $`R_2^S`$ and $`B = \rho_{\Theta_A+\omega^2}`$ in $`R_2^C`$, and let $`f(a)`$ be the least element
  of $`(C_{\omega^\omega})'`$ above $`B`$. Then $`c_0 \ge f(a)`$, $`c_1 \ge f(a+\omega)`$, $`c_2 \ge f(a+\omega\cdot 2)`$. In $`R_2^S`$ the bound for $`c_0`$ was known; the
  bounds for $`c_1`$, $`c_2`$ and the $`R_2^C`$ form are new. Their names are conjectures, all below
  $`\psi_{\Omega_1}(\Omega_\omega\cdot 2) \lt \theta_0`$, so the structure theory alone does not yet need an inaccessible.
- **Correction to Theorem GEN** (proved, 1 review). GEN names the $`\upsilon`$-points only below $`\upsilon^* = \sup H[D] \le \psi_{\Omega_1}(\Omega_\omega + \Omega_2)`$. The
  $`\upsilon`$-points are cofinal in $`\omega_1`$, so "every $`\upsilon`$-point has a name" (written in earlier versions of these pages) was
  false. GEN-EXT (§2) extends the names to $`\eta \lt \Omega_\omega\cdot\omega`$. The referee's random test: 315 values, 0 violations.
- **Not delivered** (blocking point against the goal of the paper, not against a stated result). The paper gives no way to
  produce a chain of length 3. CF restates the problem ("$`e`$ is a left end"), and the new substantial results need LEFT.

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

## 5. Checks

Each run was under 60 seconds; none is a proof. Certificates count only when replayed.

- INC1: the referee replayed 3 certificates (the point of $`\Phi_3(\mathrm{SRO})`$ below PT and below a variant, and the top of PS below
  the point of $`\Phi_3`$(row 28)). A numeric search for bad right ends is not possible: being a $`\upsilon`$-point is not visible in a pattern of
  $`R_2^C`$.
- First non-skeletal point: program runs place the point of $`\Phi_3`$ at the predecessors $`QK^n`$, at $`M_a`$ and at $`M_\nu`$. 16 named terms are
  normal forms and increasing, in Python and in Lean (test files, not proofs); GEN-EXT: 480 random $`\eta`$, 0 mismatches, $`H`$
  increasing on 38,229 pairs.
- Chains from fans: 27 named terms are normal forms and increasing, in Python and in Lean (test files); the referee's 315
  random values of $`H(\eta)`$: 0 violations of the GEN range or of monotonicity.
- Finite closures: the author's checker on 910 random terms (1,130 children, 3,414 values of LHPAR\*) and the referee's on
  300 terms (539 children, 1,445 values): 0 violations. These tests use only principal parameters, so they never test the
  counterexample to the sharp LHPAR\*; the referee confirmed that counterexample with ordinal values.

## 6. Open

- **NOBAD** (and **RIGHT**), and **CC** for $`R_2^C`$. With them INC1-S and INC1-nonups, and so LEFT, hold everywhere.
- The name of $`\nu`$ (Conjecture NU-NAME); $`\nu_C = \nu_S`$; SKEL⁺ for $`R_2^C`$; the least fan and its name; the structure above $`\nu`$.
- A chain of length 3: a point of $`(C_{\omega^\omega})'`$ above $`B`$ whose successors accumulate at a left end. Being a left end is not a
  property of a finite configuration, so Carlson's generating rules cannot produce it (NO-GEN). Conjecture CH.
- The reaches for candidates in $`[\delta_j\cdot\omega, \delta_{j+1})`$; a review of the repaired TOP-REG and REACH; $`R_2^C`$ above $`\rho_{\Theta_{d\omega}}`$; the
  closed forms and names above $`\Lambda_\Gamma`$ ($`\Theta_P`$, $`\Theta_1`$, $`\Theta_A`$, $`\Theta_\delta`$, $`\Theta_{d\omega}`$, $`\Lambda^*`$, $`\nu_P`$); names above $`\upsilon^*`$ beyond GEN-EXT.
- That the assignments between ordinals and patterns are elementary recursive (outline only), and that UNIF is onto.
