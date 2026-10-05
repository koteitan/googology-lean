[← Back](README.md) | [English](THETA.md) | [Japanese](THETA-ja.md)

# $`R_2^+`$, the thirteenth and fourteenth rounds: PAR-SAME, the names up to $`\nu_P`$, the claim up to $`X_3`$, modules for the fixed points of $`\upsilon`$, (REP), (HC) and twisted copies

This page continues [VEBLEN.md](VEBLEN.md), and [SHIFT.md](SHIFT.md) and [SHIFT2.md](SHIFT2.md) continue it. The status words are those of [README.md](README.md) §3: **proved** means that an
independent referee found the result proved with no fatal or blocking point. §1–§7 are the thirteenth round (2026-10, four papers), and §9 is the fourteenth round (2026-10, four papers). §8 holds two
parts that were moved here from the README to keep it short: the summary of the rounds 1–12, and the results on $`R_2^S`$ against $`R_2^C`$.
A statement with a blocking point against it is listed under **Not proved**; a statement that its referee found to restate the target, or to be
a remark, is listed under **Not counted**. A certificate counts only when it was replayed. **Proved as a transfer** means: a refereed proof
repeated with one map, base or index range changed, where the paper names every place that needs an extra fact and the referee accepted
each of them (the same standard as L3 and H3 of [VEBLEN.md](VEBLEN.md) §1 and §8). The transfers of §1 are written out as full proofs in §9.1.

Every paper was refereed once, so a result here has 1 review unless a count is given. None of the papers uses Wilken, JSL 72 (2007), Carlson,
AML 38 (1999), Wilken, AML 45 (2006), or the equivalence that Carlson 2009, p. 97, announces. No Lean file was added: one paper (§1) checked a Lean
test file of named points with leanman (green, and green again in the referee's rerun); it only compares terms (`#eval`, no theorem). The papers
number the levels of nested pairs one lower; here they are renumbered (their $`U^1`$ and $`u_n`$ are $`U_2`$ and $`\upsilon^2_n`$ here).

## 1. PAR-SAME, $`\Theta_1`$ and $`\Theta_A`$, and the claim up to $`\upsilon^*`$

Notation of [VEBLEN.md](VEBLEN.md) §1 and §8: $`H(\eta) = \psi_{\Omega_1}(A_\eta)`$ with $`A_\eta = \Omega_\omega + \theta\cdot\eta`$, $`C_\eta`$ the InaccPsi hull of
$`(A_\eta, H(\eta))`$, $`D`$ the set of $`\eta \lt \Omega_2`$ with $`\eta \in C_\eta`$, and $`\upsilon^* = \sup H[D]`$ ([PINS.md](PINS.md) §3). $`T^\tau`$ is Wilken's system over the base
$`\tau`$ (Wilken 2007, APAL 145, 130–161), and $`\bar T^\tau`$ the simultaneous system of Weiermann–Wilken (MLQ 57, 2011). New: $`\theta_2 = \psi_{\Omega_3}(\Omega_\omega)`$,
$`Z = \psi_{\Omega_2}(\Omega_\omega + \Omega_2)`$, $`G(\zeta) = \psi_{\Omega_2}(\Omega_\omega + \theta_2\cdot\zeta)`$ (so $`G(0) = \theta`$), $`D'`$ the set of $`\eta \lt \Omega_\omega`$ with $`\eta \in C_\eta`$, and
$`\iota'(\eta)`$ the order type of $`D' \cap \eta`$. $`X_2 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{\theta+2})`$.

- **FID and Theorem PAR-SAME** (proved; the referee checked the places of the 2011 paper, Def 3.2, Cor 3.7(f), Def 3.9, Def 4.7, and of Wilken 2007, Def 3.28,
  Def 4.6, L.3.30, against the text). By Cor 3.7(f) of the 2011 paper the order isomorphism $`f^\tau`$ of its Def 3.9 is the identity, so $`T^\tau`$ and $`\bar T^\tau`$ are
  the same set and only the term of an ordinal changes. PAR-SAME: for every $`\alpha \in T^\tau`$, the parameters read off its term in Wilken's system
  (Wilken 2007, Def 3.28) equal those read off its term in the simultaneous system (2011, Def 4.7). This is the lemma that the twelfth round lacked
  ([VEBLEN.md](VEBLEN.md) §8). Proof: a simultaneous induction along Def 3.2 of the 2011 paper; the key step is that the first element of the localization of
  $`\Delta_1`$ is a subterm of $`\Delta_1`$ (Wilken 2007, Def 4.6). (The referee: one inequality in the induction needs the citation Wilken 2007, L.3.30.)
- **Corollaries** (proved). $`T^\tau[\sigma] = \bar T^\tau[\sigma]`$ for every $`\sigma`$; the two base changes $`\pi_{\sigma,\tau}`$ are the same map; **READOFF**: the parameters
  written in a $`\bar T^\tau`$ expression bound the parameters of its value (so if they are below an additively principal $`\sigma`$, so are those of the value).
  (The referee: READOFF does not list the trivial case where the value is $`\tau`$.)
- **Theorems THETA1 and THETA-A** (proved, 2 reviews: the twelfth-round referee checked every step except PAR-SAME, and the referee of this round checked
  that PAR-SAME with READOFF gives both directions that the blocking point of [VEBLEN.md](VEBLEN.md) §8 asked for).
  $`\Theta_1 = H(\theta) = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta\cdot 2})`$ with $`\mathrm{lh}(H(\theta)) = H(\theta+\omega+1) + H(\theta+1)`$, and $`\Theta_A = H(\varepsilon_{\theta+\omega}) = \psi_{\Omega_1}(\Omega_\omega + \varepsilon_{\theta+\omega})`$.
  So Wilken's claim holds in $`R_2^C`$ on $`[0, H(\varepsilon_{\theta+\omega} + \omega^2))`$, both halves. The five minor points of the twelfth-round review are applied: the
  parameters of $`E^{\Omega_1}`$ are among the countable maximal subterms; the map $`\Psi^\#`$ is read on its proper domain; NU-CT replaces an $`R_2^S`$ citation;
  NEST-CHAR is relabelled a restatement of NU-CT (not counted); the hull lemma below $`\psi_{\Omega_2}(\Omega_2\cdot 2)`$ is relabelled plausible.
- **TAU-BOUND, CONT₂ and UPS\*** (proved; checked against the facts of [InaccPsi](../../../Notation/InaccPsi/README.md) and the Lean lemma `psi_one_iSup`). For $`\eta \in D'`$
  and $`\tau \in C_\eta \cap \Omega_2`$: $`\tau \lt \psi_{\Omega_2}(A_\eta)`$, and $`\psi_{\Omega_2}(A_\eta) \le Z`$ for $`\eta \in D`$. $`\psi_{\Omega_2}`$ is continuous on increasing sequences (CONT₂, the
  $`\Omega_2`$ form of Lemma CONT). $`\sup D = Z \notin D`$, and

```math
\upsilon^* = \sup H[D] = \psi_{\Omega_1}(\Omega_\omega + \Omega_2) = H(\Omega_2).
```

- So below $`\upsilon^*`$ every restart $`\lambda`$ has its exponent $`\tau_\lambda \lt Z \lt G(1)`$. Before, only $`\upsilon^* \le \psi_{\Omega_1}(\Omega_\omega + \Omega_2)`$ was known.
- **GEN⁺** (proved as a transfer). Theorem GEN of [PINS.md](PINS.md) §3 holds on $`D'`$: $`H(\eta) = \upsilon_{1+\iota'(\eta)}`$ for every $`\eta \in D'`$. The one place in its proof that
  names $`\Omega_2`$ needs only $`\theta\cdot\eta \lt \Omega_\omega`$.
- **The shifted LOW-STEP maps** (on $`[\theta, Z)`$ proved, with all five comparison cases checked by the referee against L.4.3 and L.4.4 of the 2011 paper; at
  the other bases proved as a transfer, SLOW$`_\zeta`$, which the referee finds to be an index shift). A map $`E^{G(\zeta)}`$ from the InaccPsi normal forms
  with values in $`[G(\zeta), G(\zeta+1))`$ into $`\bar T^{G(\zeta)}`$: strictly increasing, every node in its domain, with the maximal subterms below $`G(\zeta)`$ as its
  parameters. **Lemma S** (proved as a transfer of SUBST-ISO): substitution at an uncountable base.
- **Theorem U\*** (proved, resting on Lemma S at the base $`\theta`$, which is now proved in full, §9.1; the referee: the induction must run on $`\lambda`$, as in R-CAP, and one bound $`\kappa`$ must be
  chosen additively principal). Every restart $`\lambda`$ with $`\rho_\lambda \lt \upsilon^*`$ has formal reach below $`\delta_\lambda + \upsilon_{\lambda+2}`$. So $`\Theta_\delta`$, $`\Theta_{d\omega}`$ and
  $`\Lambda^*`$ are all at or above $`\upsilon^*`$, outside the names of GEN.
- **Theorem F1: Wilken's claim on $`[0, \upsilon^*)`$ in $`R_2^C`$**, both halves (proved, resting on one transfer, Lemma S at the base $`\theta`$). Every ordinal below
  $`\upsilon^* = \psi_{\Omega_1}(\Omega_\omega + \Omega_2)`$ is in the core and is the value of an InaccPsi normal form with collapse arguments below $`I_\omega`$, and $`\nu_C \gt \upsilon^*`$.
  Before: $`[0, \rho_{\Lambda_{\mathrm{fp}2}+\omega^2})`$. The core half comes from CORE-C$`^{d\omega}`$ ([BREAK.md](BREAK.md) §4), because $`\rho_{\Theta_{d\omega}} \ge \upsilon^*`$; the names
  half is Lemmas L and IS. This also answers a question of [VEBLEN.md](VEBLEN.md) §1: $`\nu_C`$ is not below $`\upsilon^*`$.
- **R-CAP and Theorem F2** (proved as a transfer: GEN⁺, SLOW$`_\zeta`$, and Lemma S at the bases $`G(\zeta)`$). Every restart $`\lambda`$ with $`\eta_\lambda \lt \theta_2\cdot\omega^2`$
  is below $`\Lambda^*`$, so $`\Lambda^* \ge \iota'(\omega^{\theta_2+2})`$. With [BREAK.md](BREAK.md) §2: $`\nu_C \gt \nu_P \ge X_2`$, and Wilken's claim holds in $`R_2^C`$ on $`[0, X_2)`$, both halves.
- **The names** (lower bounds proved as a transfer; equality a conjecture; **now all four are proved**, §9.1). The name of $`\rho_{\Lambda^*}`$ comes out of this derivation and matches
  the earlier conjecture of [REACHES.md](REACHES.md) §3, which was made from matrices.

| point | conjectured InaccPsi name |
|---|---|
| $`\rho_{\Theta_\delta}`$ | $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+1} + \theta_2)`$ |
| $`\rho_{\Theta_{d\omega}}`$ | $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+1} + \theta_2 + \omega^{\omega^{G+1}})`$, $`G = \psi_{\Omega_2}(\Omega_\omega + \omega^{\theta_2+1} + \theta_2)`$ |
| $`\rho_{\Lambda^*}`$ | $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2})`$ |
| $`\nu_P`$ | $`X_2 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{\theta+2})`$ |

- **Not counted**: NEST-CHAR (a restatement of NU-CT, as said above). (The referee: a remark of the paper overstates where the closed form of the reaches
  is known; it is exact only for $`e_\lambda \le \psi_{\Omega_2}(\Omega_2\cdot 2) + 1`$ and at $`\Theta_A`$, with bounds only in between.)
- **Open** (the equality halves and $`\nu_P`$ are now proved, §9.1): the equality halves of the names (they need the shifted STEP at the bases $`G(\zeta)`$, codes for the realizers, and lower bounds for the reaches
  between $`\delta_j\cdot\omega`$ and the next block top); the exact value of $`\nu_P`$; an InaccPsi upper bound for $`\nu_C`$ (one positive $`\lt_2`$-relation whose left end is a
  restart). PAR-SAME and Lemma S could not be tested: there is no implementation of Wilken's $`T^\tau`$.

## 2. Native codes: modules for the fixed points of $`\upsilon`$

Notation of [VEBLEN.md](VEBLEN.md) §2 and §9, and the Veblen hierarchy over $`\upsilon`$ of [REACHES.md](REACHES.md) §1: $`V_1(\alpha) = \Xi_\alpha`$, and $`V_{\nu+1}`$ enumerates the fixed
points of $`V_\nu`$, so $`V_2(1) = \Phi_1`$. $`\Gamma^\upsilon_1`$ is the least $`\nu \ge 1`$ with $`V_\nu(1) = \nu`$; this is the point $`\Lambda_\Gamma = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1^2})`$, whose
name is proved in [PINS.md](PINS.md) §3 (the paper calls this name unproved).

- **LEV, NO-HIGH, NO-HIGH-K** (proved; checked line by line). Every fixed point $`\zeta \lt \Gamma^\upsilon_1`$ of $`\upsilon`$ is $`V_\nu(1+\beta)`$ with a largest level $`\nu`$, and
  $`\nu, \beta \lt \zeta`$. A fixed point above the needed points of $`\beta`$ and below $`\zeta`$ has level at most $`\nu`$, and at level $`\nu`$ it has a smaller $`\beta`$.
- **Lemma EXTRA** (proved; the referee: the steps at layer 0 are covered by the same argument, but one sentence is missing). Every step of the layered codes of
  [VEBLEN.md](VEBLEN.md) §9 also holds with an extra closed set $`F`$ below the point held fixed; the new chain then lies above $`\max F`$.
- **Theorem MODULE-RED** (proved as an implication). Suppose every fixed point of $`\upsilon`$ below a bound $`Z'`$ gets a module block with three properties: (MA) a
  fixed shape (one pair and one ordinary inner chain), (MB) the block is an L1p-free pattern, (MC) the block hosts the blocks of the smaller fixed points.
  Then the codes satisfy $`N(\gamma') \ll N(\gamma)`$ on $`[\omega, Z')`$, and $`\iota(\mathrm{CH}_2) \ge Z'`$. (The referee: the paper says that the whole native program is reduced to
  modules; this overclaims. It is reduced to modules of shape (MA), and the next kinds of module do not have this shape.)
- **Theorem LADDER** (proved). Slack blocks $`L_\nu(\beta)`$, one per level; the block $`J = L_2(0)`$, whose top is $`c + x + r`$, is the module of $`\Phi_1`$, and it is exactly what conv
  draws for (0,0,0)(1,1,1)(2,1,1)(3,1,0)(2,1,0) (checked). So $`\iota(\mathrm{CH}_2) \ge V_{\omega^2}(1)`$.
- **Theorem IDX-Γ** (proved). Inner-code modules: the block of $`V_\nu(1+\beta)`$ holds the chain of $`N(\omega+\nu)`$ inside its pair, below a top that grows with $`\beta`$.
  So $`N(\gamma') \ll N(\gamma)`$ for $`\omega \le \gamma' \lt \gamma \lt \Gamma^\upsilon_1`$, and $`\iota(\mathrm{CH}_2) \ge \Gamma^\upsilon_1 = \Lambda_\Gamma`$ natively (before: $`\Phi_1`$). This is still far below the known
  $`\iota(\mathrm{CH}_2) \gt \nu_C`$; the progress is on the native route toward $`\iota(\mathrm{CH}_2) \ge \theta_0`$ only.
- **Not counted** (the referee: a remark, not a theorem): "the fundamental sequences of G. Wilken, Fundamental sequences based on localization (APAL 2025,
  arXiv 2410.15953) stay inside one layer". The paper cites the wrong corollary for it (the right places are Def 2.29 with Thm 2.28), and as written it is
  false: Def 3.5 there takes the step across a layer base from a base system given as input.
- **The grammar that follows conv**: (G1) inner codes relative to $`x`$, an outline only; (G2) a collapsing hierarchy over $`\upsilon`$, open (conjecture: it reaches $`\Theta_1`$);
  (G3) everything beyond, up to $`\theta_0`$, open.
- **Not proved**: $`\iota(\mathrm{CH}_2) \ge \theta_0`$, as the paper says. The gap: modules for the fixed points of $`\upsilon`$ from $`\Gamma^\upsilon_1`$ (where $`\zeta`$ is in the range of $`V_\zeta`$) up to
  $`\theta_0`$. The next kinds of module do not fit (MA): a second inner chain above the pair, inner sums that contain $`x`$, and conv's next blocks $`c \le_1 c + y`$
  and $`c \le_1 c\cdot 2`$. So MODULE-RED itself must be widened first.

## 3. The shapes of $`\Phi_3`$: (REP) proved, and the staircases with $`t = 2`$

Notation of [VEBLEN.md](VEBLEN.md) §3 and §10. The theorems are about the text definition of $`\Phi_3`$ and the program `por/phi3def2.py`; everything is in $`R_2^C`$.

- **PRES-IN, PRES and Theorem REP** (proved; the referee checked each line against the program, and the list of dead code and of the five live identity
  tests). Two conditions on the pairs of $`A[0]`$ and $`A[1]`$: (J) a child's $`y`$ is at most its parent's $`y + 1`$; (N) no column with $`z = 1`$ has a child with $`z = 1`$ one
  level higher. They pass to every $`A[j]`$, and all 3,166 sample matrices satisfy them (decided by computation). Under them the level-column part of the
  program never runs, only five identity tests are evaluated, and each equals the test by position. So the run does not depend on how objects are
  stored or on the order of calls, the closure is order-independent, and the program equals the text definition: (REP) holds. So SYM, SYM-P, SYM-R
  and every symbolic result since [FANFREE.md](FANFREE.md) §10.1 hold without (REP); the 1,862 matrices of [VEBLEN.md](VEBLEN.md) §10 are now proved outright. (The referee:
  a side lemma, F1′, holds only for objects with $`y = 1`$, which is its only use; REP does not depend on it.) **Finding** (open, only above SRO): in one branch
  of the program a record can be missed by the closure; it is never reached below SRO.
- **L-STAIR and REL-OPQ** (proved; REL-OPQ needs one more sentence on why one case split does not depend on the whole term). The first copy step lowers the
  staircase by one level; a run of the unchanged program on terms with opaque markers that finishes gives the result for every admissible substitution.
- **Theorem STAIR-V** (proved, given finite base checks B0–B6, which pass for all 96 + 29 matrices; the referee reran them). For the class STAIR ($`t = 2`$, the
  chain start $`C`$ a child of the bad root, the chain tail the last child of the root): conv$`(A[n])`$ explicitly for every $`n \ge 4`$.
- **TRANSFER and STAIR-FS** (TRANSFER is proved after the referee's fix: every relative node at level $`n+1`$ has $`y \ge 6`$ and every node of the tail has $`y \le 3`$,
  so the final segment does not change). FS⁺ for every $`n`$ on 96 ROOT and 29 III matrices.
- **The tally** (the referee checked that $`1{,}987 = 1{,}862 + 125`$):

| class | matrices | proved for every $`n`$ | given LOW | given a condition checked for small $`n`$ | $`t = 2`$, given a shape checked for small $`n`$ | open |
|---|---|---|---|---|---|---|
| I | 581 | 381 | 2 | 0 | 0 | 198 |
| SUM | 603 | 488 | 0 | 7 | 0 | 108 |
| ROOT | 635 | 587 | 0 | 0 | 0 | 48 |
| III | 1,347 | 531 | 0 | 0 | 24 | 792 |
| all | 3,166 | 1,987 (before: 1,862 given (REP)) | 2 | 7 | 24 | 1,146 |

- **Open**: UNIF-FS below SRO. The 1,179 matrices that are not proved: $`t = 0`$, 462 (M1 258, M2 139, M3–M5 65, as in [VEBLEN.md](VEBLEN.md) §10); $`t = 2`$, 335 (24 of III
  where the head of the top chain moves, which needs an $`\iota`$ with two modes; 136 of III and 31 of ROOT where $`C`$ lies deeper than a child of the bad root
  or the derivation fails; 144 of I and SUM that need a lifting of the core); $`t = 1`$, 382. M1 was not attempted: it needs a theorem on nested blocks
  with run lengths in two places.

## 4. $`\nu_C = \nu_S`$: (HC) proved, and the twisted residue

Notation of [VEBLEN.md](VEBLEN.md) §11: $`u_m = \upsilon^2_m`$, $`x = x_2`$, $`\nu = \nu_C`$, $`P^*`$ isominimal with $`x, \nu \in P^*`$, $`\tilde x = u_m`$ the downward copy of $`x`$, $`g = u_m^\#`$.

- **U-CHAIN and Theorem HC** (proved; checked against Carlson 2009, Defs 2.3 and 2.6). If $`J`$ is isominimal and $`\nu \in J`$, then $`J \cup \{u_{n^*}, \ldots, u_N\}`$ is isominimal for
  every $`N \ge n^*`$, where $`u_{n^*}`$ is the first point of $`U_2`$ above $`\max(J \cap x)`$. These points change nothing in $`[x, x^\#)`$ but push the copy $`\tilde x = u_m`$
  above any finite set of hereditary parameters. So (HC) holds, and COPY-EQ, LOC#, ET-TF and GHOST-TR (in the referee's repaired form) of
  [VEBLEN.md](VEBLEN.md) §11 hold with no hypothesis.
- **RED-TF** (proved; it closes both holes of the blocking point of [VEBLEN.md](VEBLEN.md) §11). The low points (below $`g`$) go by $`T_m`$, applied to the suffixes of Cantor
  normal forms; the top parts need one copy $`\Psi_0`$ with images in $`(x^\#, \nu)`$. The only condition left is
  (CUT′): $`a \le_1 B + w`$ iff $`\Psi_0(a) \le_1 \Psi_0(B) + T_m(w)`$. Every other atom is forced.
- **ISO-EXT, LOW-ISO, UNTWIST and GHOST-TW** (proved; the referee: one step of UNTWIST assumes that the target set is closed, which follows from UP-EX by a
  short argument that is not written). Carlson's upward rule over an enlarged isominimal base keeps every low point fixed. It gives (CUT′) for all
  $`w \lt u_m`$, for all high tails, and the direction "⇐" for every $`w`$. So a ghost needs a **twisted triple**: a top point $`a`$ with $`\mathrm{lh}(a) = B + r`$ and
  $`u_m \le w \le r \lt u_m^\#`$, where the exact upward copy keeps the reach end at $`u_m`$ instead of moving it to $`x`$.
- **TW-0** (proved, given Theorem KV of [FANFREE.md](FANFREE.md) §10.3). For a restart whose index $`\iota`$ is not a fixed point of $`\upsilon`$, the twist can be put into the
  index: $`\iota' = \omega^{x^\# + l' + 1} + \omega^{l'}`$ with $`l' = T_m(\mathrm{logend}(\iota))`$. It lies below the $`\omega`$-th point of $`K`$ above $`x`$, which is below $`\nu`$, so Example TW of
  [VEBLEN.md](VEBLEN.md) §11 is realized below $`\nu`$. (The referee: this does not settle the remark that asked for such a point above $`\max(P^* \cap \nu)`$; nothing needs it.)
- **ZONE-RED and LH-LAMBDA** (proved as conditional lemmas; ZONE-RED uses one fact that is not among its listed properties, and it follows from them).
  All of the above works for every zone system with properties (Z1)–(Z5); Theorem KV gives the zone that ends at $`u^\#`$. The reaches stay below $`\lambda_u`$, the
  least limit of fixed points of $`k`$ above $`u`$.
- **Not proved**: (TWIST\*), a twisted copy of a whole top configuration. It is shown only when the top part is $`\{\rho_\iota, \delta_\iota\}`$ with $`\iota`$ not a fixed point of $`\upsilon`$; it
  is missing for restarts in $`\mathrm{Fix}_1 \setminus K`$, for points of $`K`$, for several blocks at once, for the points $`u_{m+j}`$, and for zone C. (R2) needs (PROF) on
  $`[u^\#, \lambda_u)`$ and zone C. Neither $`\nu_C = \nu_S`$ nor $`\nu_C \lt \nu_S`$ is proved, and no first difference was found. (The referee: the paper's "equivalent" in one
  place shows only that (TWIST\*) gives ET.)

## 5. Status after the thirteenth round

The fourteenth to eighteenth rounds changed this status; see §9.5, [SHIFT.md](SHIFT.md) §5, §8.5, §9.5 and [SHIFT2.md](SHIFT2.md) §1.5.


- Wilken's claim in $`R_2^C`$: both halves hold on $`[0, \upsilon^*)`$ with $`\upsilon^* = \psi_{\Omega_1}(\Omega_\omega + \Omega_2)`$ (resting on one transfer), and on $`[0, X_2)`$ with
  $`X_2 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{\theta+2})`$ (proved as a transfer); $`\Theta_1 = H(\theta)`$ and $`\Theta_A = H(\varepsilon_{\theta+\omega})`$ (2 reviews); $`\nu_C \gt \nu_P \ge X_2`$.
- The lower-bound program below $`\theta_0`$: the step below SRO is proved for every $`n`$ on 1,987 of the 3,166 sample matrices, with no condition on the program
  (§3); the native codes are ordered on $`[\omega, \Lambda_\Gamma)`$, so $`\iota(\mathrm{CH}_2) \ge \Lambda_\Gamma`$ natively, and the rest is reduced to modules of shape (MA) (§2).
- The first inaccessible: $`H_m`$ is open; it would follow from $`\iota(\mathrm{CH}_2) \ge \theta_0`$.
- Upper bounds: no InaccPsi bound is proved for any $`\iota(\mathrm{CH}_k)`$, $`m_F`$, $`x_F`$, $`C^*_3`$ or $`\nu_C`$.
- $`\nu_C = \nu_S`$: (HC) holds, the reduction is repaired, and everything except twisted triples is matched (§4); left: (TWIST\*), (PROF) and zone C.

## 6. Checks of the thirteenth round

Each run was under 60 seconds; none is a proof. Certificates count only when replayed.

- §1. $`E^\theta`$ on $`[\theta, Z)`$: 2,500 terms, 806,640 pairs, 0 order, domain or parameter failures; broken controls fail (18,222 and 367 mismatches). The general
  shifted map at the bases $`\theta`$, $`G(1)`$, $`G(\omega)`$: 502,264 pairs, 0 failures; broken controls fail. 12,883 pairs $`(\tau, \eta)`$ with $`\tau \in C_\eta`$, all below $`\psi_{\Omega_2}(A_\eta) \le Z`$.
  The 11 named points are normal forms and strictly increasing (Python, and the Lean test file, green). The referee: reruns with new seeds, 0 failures;
  an own generator: $`E^\theta`$ on 1,000 terms and 280,920 pairs, 0 failures; 400 random normal forms below $`Z`$ are all below $`\zeta_8`$, and 474 random countable
  normal forms below $`\upsilon^*`$ are all below $`H(\zeta_8)`$ ($`\zeta_0 = 0`$, $`\zeta_{n+1} = \psi_{\Omega_2}(A_{\zeta_n})`$), which supports $`\sup_n \zeta_n = Z`$; TAU-BOUND above $`\Omega_2`$: 3,262 pairs,
  0 failures. PAR-SAME and Lemma S were not tested (no implementation of $`T^\tau`$).
- §2. The 15 module patterns (14 new; SRO is not new) are patterns, RF, fan-free and L1p-free; 19 of 19 certificates in the predicted direction were found
  and replayed; 7 reverse searches found none. The referee: the rerun is identical; the six conv drawings of the paper match; 10 own reverse searches
  found nothing (each stopped at about 45 s), and 4 own forward pairs were found and replayed. This is weak evidence: the searches are shallow.
- §3. 0 violations of PRES in 15,830 builds; an instrumented run evaluates exactly the five identity tests; the step structure for $`n = 2, \ldots, 9`$ and the
  transferred solutions at levels 6 to 9. A bug in the author's own tool (wrong staircase constants for the numbering of III) and a missing hypothesis
  of L-STAIR (children that do not increase) were found and fixed, and all 125 were run again. The referee: 16,632 builds, 0 violations; B0–B6 rerun with
  the same results; mutation tests show that the checker rejects wrong values; the step for ROOT at $`n = 10, \ldots, 18`$ and for III at $`n = 10, \ldots, 13`$, 0 failures.
- §4. The paper ran nothing. The referee's toy model of the RED-TF map on Cantor normal forms: 14,400 pairs, 0 failures.

## 7. Open

The fourteenth to eighteenth rounds changed this list; the current list is [SHIFT2.md](SHIFT2.md) §1.7.


- The first inaccessible: $`H_m`$ (enough: $`\iota(\mathrm{CH}_2) \ge \theta_0`$, through modules for the fixed points of $`\upsilon`$ from $`\Lambda_\Gamma`$ up to $`\theta_0`$, with MODULE-RED widened
  beyond shape (MA), or the grammar (G1)–(G3)); UNIF-FS below SRO on the 1,179 open matrices of §3; $`\iota(A_n) \ge |\tau_n|`$.
- Upper bounds: any InaccPsi bound for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$, $`f_0`$, $`m_3`$, $`c_0`$, or for $`\nu_C`$ (one positive $`\lt_2`$-relation at a restart); STEP-CH; REL-SHARP; (HQ).
- Names past $`\upsilon^*`$: the equality halves of the table of §1 (the shifted STEP at the bases $`G(\zeta)`$, codes for the realizers, and lower bounds for the reaches
  between $`\delta_j\cdot\omega`$ and the next block top); the exact $`\nu_P`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$ (the hull lemma of [VEBLEN.md](VEBLEN.md) §1).
- $`\nu_C = \nu_S`$: (TWIST\*) in the missing cases of §4, (PROF), zone C; the reaches at limits of fixed points of $`k`$.
- The rest of [COVER.md](COVER.md) §9.

## 8. Moved from the README

### 8.1 The rounds 1–12 in brief

Below $`\upsilon_{\omega\cdot\omega}`$ the claim holds, in both $`R_2^C`$ and $`R_2^S`$: every ordinal
below $`\upsilon_{\omega\cdot\omega}`$ is in the core, and it is the countable value of an InaccPsi normal form whose
collapse arguments are below $`I_\omega`$ (Theorem LOW of [README.md](README.md) §3). Wilken's points have exact names:
$`\upsilon_{1+\eta} = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$ for $`\eta \lt \Gamma_0`$ (Theorem T, §4), and now for every
$`\eta`$ below the first fixed point $`\Xi_1`$ of $`\iota \mapsto \upsilon_\iota`$ (Theorem T+). Lemma FRAG is now proved. These results of
2026-10 (FRAG, FRAG2, the restart blocks, T+) are on the second page [RESTARTS.md](RESTARTS.md). The third page
[REACHES.md](REACHES.md) has the newest ones: the exact reach of every restart up to $`\Lambda_\varepsilon`$ (some results with
2 reviews), the names $`\Xi_\alpha = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1}\cdot\alpha)`$ (2 reviews), so that in $`R_2^C`$ the claim
holds up to $`\Phi_1`$, the structure of $`R_2^S`$ on the whole skeletal regime, where the skeleton ends, and the least chain
of length 3. The fourth page [PINS.md](PINS.md) has the results of the next round: relativized patterns of $`R_1^+`$
(Wilken's announced relativized core, rebuilt except "elementary recursive"), the exact reaches up to $`\Theta_A`$, the names
$`\upsilon_{1+\iota(\eta)} = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$ of all $`\upsilon`$-points (Theorem GEN), so that in $`R_2^C`$ the claim holds up
to $`\Lambda_\varepsilon`$, and the shape of the bottom of a chain of length 3. It also records a gap found in Lemma LEFT. The fifth
page [BREAK.md](BREAK.md) has the latest two rounds: INC1, NOBAD and Lemma LEFT proved with no hypothesis left, the first
non-skeletal point of $`R_2^S`$ found exactly, that of $`R_2^C`$ equal to it unless one extra pair exists, the first block of every
level of nested pairs, limits of these levels never in a pair, chains of length 3 as fans whose limit is a left end (so the
shape C3′′ is false), the finiteness of the closures $`C_\tau(z)`$, and the core of $`R_2^C`$ up to $`\nu_C \gt \nu_P`$. Its §7 has the third round:
every block of every level of nested pairs below their limit $`T_\omega`$ has the shape of the first block (Theorem SH), every fan apex
lies above $`T_\omega`$ (2 reviews), the least fan has exactly two successors and in $`R_2^C`$ is open, the question $`\nu_C = \nu_S`$ is a
question about $`R_2^S`$ alone, and the name of $`\nu`$ and the base changes between gaps are reduced to the index statement $`o_2 = \omega`$ and
two more. Its §8 has the fourth round: in $`R_2^C`$, every level of nested pairs has exactly $`\omega`$ points below its left end
($`o_k = \omega`$ for every $`k`$, Theorem O$`^C`$, 1 review, by Carlson's minimality against coverings), so the shape part of NU-NAME holds in
$`R_2^C`$; in $`R_2^S`$, $`o_2 = \omega`$, NOLIM above $`\nu_P`$ and $`\nu_C = \nu_S`$ stay open, $`\nu_C = \nu_S`$ now implies $`o_2 = \omega`$, and NOLIM is reduced
to one statement per gap. The sixth page [COVER.md](COVER.md) has the fifth round, all by the same minimality (1 review each): in
$`R_2^C`$, a point of the core is the bottom of a chain of length 3 iff it has an infinite $`\le_1`$-chain of right ends (Theorem CP3), the
least fan is described except its order type, and NOLIM holds; in $`R_2^S`$, $`\nu_C = \nu_S`$ is equivalent to NOLIM and
$`o_2 = \omega`$ there, and $`o_k = \omega`$ is reduced to an $`R_2^S`$ form of Carlson's minimality and one pinning statement. Its §5 has the sixth
round (1 review each): the level-0 description of $`R_2^S`$ holds at every countable ordinal (so SKEL⁺, SKEL$`^\omega`$ and RIGHT in $`R_2^S`$ are
proved, and the results that used them, NOLIM in $`R_2^C`$ among them, move from outline to proof level); the least fan of $`R_2^C`$ has
order type $`\omega^2`$; whether its least $`\le_1`$-predecessor $`m_F`$ is $`\ge \theta_0`$ (which makes the fan need an inaccessible) is exactly a lower
bound for fan-free patterns whose right ends have no reach; and the $`R_2^S`$ form of Carlson's minimality holds up to $`\beta_0`$. Its §6 has
the seventh round (1 review each): a calculus of comparisons between patterns proves the top step of $`\theta_0`$ (at SRO) and several
uniform families of steps, but not all, so whether the first fan needs an inaccessible stays open; $`m_F \gt \nu_C`$; an upper bound for
the least fan or the least chain needs only one $`\lt_2`$-pair with one more point, but no bound by an InaccPsi term is proved, and two
proposed reductions only restate the targets; $`\nu_C = \nu_S`$ is one $`\Sigma_2`$ statement inside the structure that $`R_2^S`$ and $`R_2^C`$ share,
and it follows from a condition on the segments of level 2 that is proved on the first block; the names of the least fan are
conjectured with the base $`I_0`$, on analogy only. The seventh page [FANFREE.md](FANFREE.md) has the eighth round (1 review each): all 26
undecided limit jumps of the lower-bound sample are proved; $`m_F`$ is the limit of the points of one explicit sequence of chains of
pairs, so the first fan needs an inaccessible iff one of these chains has its point at or above $`\theta_0`$ (and $`FF_N`$ is the same
hypothesis), and an upper bound for $`m_F`$ is a bound for that one sequence; a map without matrices is built on the index family
below $`\varepsilon_0`$, but the proof of its order has a gap; and the reaches of restarts correspond between the segments of level 2 on
the initial part of each segment, at outline level only. The same page has the ninth round (1 review each): the step of the
lower-bound program below SRO is proved for every $`n`$ on 459 of the 3,166 sample matrices (one earlier gap, IDX-ADD, included), and
the rest falls into four open classes; the native codes are ordered up to $`\varphi_\omega(0)`$, and every fan-free pattern without the
configuration L1p lies below the point of $`\mathrm{CH}_2`$, so a map of all terms below $`\theta_0`$ to such patterns would show that the first fan
needs an inaccessible; the reach of every restart below $`\nu_C`$ is known except at limits of "critical" indices, and the segment
condition SC is proved up to the first such limit, but $`\nu_C = \nu_S`$ stays open; no InaccPsi upper bound for the point of $`\mathrm{CH}_2`$ is
proved, and such a bound is exactly three relations at one point above $`\nu_C`$. The same page has the tenth round (1 review each): in
$`R_2^C`$ the claim now holds up to $`\rho_{\Lambda'+\omega^2}`$, with the reach of every restart there in closed form, and
$`\Theta_P`$ has its name; the step below SRO is proved for every $`n`$ on 874 of the 3,166 sample matrices; the native codes are ordered up to the
Bachmann–Howard ordinal; the reaches below $`\nu_C`$ are known up to offset $`\rho^\rho`$ (a Klammer hierarchy over $`\upsilon`$), and SC holds on a larger part of each
segment, but the reduction to SC always needs the long restarts, where no closed form of the reaches applies, so $`\nu_C = \nu_S`$ stays open. The eighth page [VEBLEN.md](VEBLEN.md) has the eleventh round (1 review each): in
$`R_2^C`$ the claim now holds up to $`\rho_{\Lambda_{\mathrm{fp}}+\omega^2}`$, because Wilken's hull levels are now matched with the Veblen
functions and with $`\Gamma`$; below $`\nu_C`$ the Klammer forms of the restarts are read off their InaccPsi names; $`\Theta_1 = H(\theta)`$ is reduced to one open hull lemma; the step below SRO
is proved for every $`n`$ on 1,442 of the 3,166 sample matrices; the native codes are ordered on all indices below $`\upsilon_1`$ and one level of references, so
$`\iota(\mathrm{CH}_2) \ge \upsilon_2\cdot\upsilon_1`$; for $`\nu_C = \nu_S`$, Carlson's 2-reflection gives exact copies and every extension above the copy is matched, but the claimed reduction
to two local statements has a blocking gap, so $`\nu_C = \nu_S`$ stays open. The same page has the twelfth round (1 review each): the claim now holds
up to $`\rho_{\Lambda_{\mathrm{fp}2}+\omega^2}`$, with the offsets up to the second fixed point of Γ; the names of $`\Theta_1`$ and $`\Theta_A`$ need only one short open lemma on
parameters, PAR-SAME (without it the proofs have a blocking gap); the step below SRO is proved for every $`n`$ on 1,862 of the 3,166 sample
matrices, given a checked property (REP) of the program; the native codes are ordered on all indices below $`\Phi_1`$, so $`\iota(\mathrm{CH}_2) \ge \Phi_1`$; for
$`\nu_C = \nu_S`$, the corrected reduction fails in the zone where the copy is known exactly, so it stays open. $`C^*_3`$ lies below $`\omega_1^{CK}`$ (Carlson 2009, Thm 15.2), but it still has
no upper bound by an InaccPsi term and no name. After the twelfth round both halves were open above $`\rho_{\Lambda_{\mathrm{fp}2}+\omega^2}`$
in $`R_2^C`$ (the core part was proved up to $`\nu_C`$), and above $`\upsilon_{\omega^3}`$ in $`R_2^S`$. The thirteenth round is §1–§7 of this page.

### 8.2 $`R_2^S`$ against $`R_2^C`$

All results of this part are from 2026-10. Let $`\beta_0`$ be the least stage $`\beta`$ at which some relation
$`\alpha \le_i \beta`$ differs between the two structures ($`\beta_0 = \infty`$ if they are equal). Let
$`\kappa_X = \min\{\kappa : \kappa \le_1^X \beta \text{ for all } \beta \ge \kappa\}`$.

- **Lemma STAGE.** If the structures agree on all pairs below $`\beta`$, then $`\alpha \le_1^S \beta \Rightarrow \alpha \le_1^C \beta`$;
  if also $`\le_1`$ to $`\beta`$ agrees, then $`\alpha \le_2^S \beta \Rightarrow \alpha \le_2^C \beta`$. Tools: the finite-set test
  (T1 of [README.md](README.md) §3), the leading-term map of Theorem EQ, an $`R_2^+`$ form of Wilken 2021, Lemma 1.7(2), and transfer of
  $`\Pi_2`$ sentences.
- **Corollary FIRST.** Every $`R_2^S`$ relation ($`\le_1`$ or $`\le_2`$) with right end at most $`\beta_0`$ holds in
  $`R_2^C`$ (the case "$`\le_2`$ with right end $`\beta_0`$" was added in a second paper, 2026-10, 1 review). At $`\beta_0`$ the difference is an extra relation of $`R_2^C`$. So
  $`R_2^S = R_2^C`$ if and only if the converse ($`C \Rightarrow S`$) holds at every stage of agreement. Also
  $`\beta_0 \ge \upsilon_{\omega^3}`$ (with FRAG, now proved; now $`\beta_0 \ge \Lambda_\varepsilon`$ and $`\beta_0 \ge \rho_{\Theta_P}`$,
  [REACHES.md](REACHES.md) §1–2; then $`\beta_0 \ge \rho_{\Theta_A}`$, [PINS.md](PINS.md) §2; then $`\beta_0 \ge \rho_{\Theta_A+\omega^2}`$, [BREAK.md](BREAK.md) §4; now $`\beta_0 \ge \nu_C \gt \nu_P`$, §2), and $`\beta_0`$ is countable or $`\infty`$.
- **Theorem LOC** (2026-10, 1 review; [BREAK.md](BREAK.md) §7.3). $`\beta_0`$ is the least stage at which Carlson's covering condition,
  evaluated inside $`R_2^S`$, differs from $`R_2^S`$. So whether $`\nu_C = \nu_S`$ (no "ghost") is a question about $`R_2^S`$ alone. Now
  $`\nu_C = \nu_S`$ implies $`o_2 = \omega`$ in $`R_2^S`$, and given NOLIM the two are equivalent ([BREAK.md](BREAK.md) §8.1, 1 review). Now $`\nu_C = \nu_S`$ iff NOLIM and $`o_2 = \omega`$ hold in $`R_2^S`$
  (GHOST-EQ), and NOLIM holds in $`R_2^C`$ (Theorem NOLIM$`^C`$) ([COVER.md](COVER.md) §3 and §5.1, 1 review). Now $`\nu_C = \nu_S`$ iff
  $`x_2 \lt_2^S \nu_C`$, one $`\Sigma_2`$ statement inside the common structure below $`\nu_C`$ (Theorem EQ, [COVER.md](COVER.md) §6.3, 1 review). The condition SC behind it holds on the initial part of each segment of level 2,
  at outline level only ([FANFREE.md](FANFREE.md) §3); now it is proved on the larger part below the first limit of critical indices ([FANFREE.md](FANFREE.md) §7.3), and on a still larger part
  ([FANFREE.md](FANFREE.md) §10.3). But the reduction to SC always needs SC at long restarts, where no closed form of the reaches applies (NEED-C, same place).
  Working with the $`\Sigma_2`$ statement directly (1 review, [VEBLEN.md](VEBLEN.md) §4): over isominimal sets Carlson's 2-reflection gives exact copies, and
  every extension above the copy, the long restarts included, is matched (TOP); what is left is a local base change and translations, with a
  fixed finite set below the copy (the paper's reduction to these two without that set has a blocking gap). With that set (1 review, [VEBLEN.md](VEBLEN.md) §11):
  given an open condition (HC), the downward copy is the copy by the base change of SC and the local part holds, but the translations then fail,
  so this reduction does not work there; left: (HC), the local part beyond that zone, and a "twisted" upward rule. In the thirteenth round (§4) (HC) is proved, the reduction is repaired (RED-TF), and what is left is a twisted copy of whole top
  configurations (TWIST\*), (PROF) and zone C.
- **Lemma UPG.** At a stage of agreement, $`\alpha \le_1^C \beta \Rightarrow \alpha \le_1^S \beta`$ when every $`\gamma \lt \alpha`$ lies in an
  isominimal subset of $`\alpha`$ in $`R_2^C`$ (true for $`\alpha = \kappa_C`$ and $`\alpha = \upsilon_{\omega\cdot\omega}`$).
- **KAPPA and CORE-EQ.** $`\kappa_C \le \beta_0 \Rightarrow \kappa_C \le \kappa_S`$, and $`\kappa_S \le \beta_0 \Rightarrow \kappa_S \le \kappa_C`$. So if
  $`\max(\kappa_S, \kappa_C) \le \beta_0`$ (call this AGR), then $`\mathrm{Core}(R_2^S) = \mathrm{Core}(R_2^C)`$. The claim for
  $`R_2^C`$ together with AGR gives the claim for $`R_2^S`$.
- **The converse $`C \Rightarrow S`$ at a stage of agreement** (2026-10, 1 review). Write $`G_C`$ for the set of $`\alpha`$ such
  that every $`\gamma \lt \alpha`$ lies in an isominimal subset of $`\alpha`$. For $`\le_1`$:
  $`\alpha \le_1^C \beta \Rightarrow \alpha \le_1^S \beta`$ holds when $`\beta \lt \kappa_C`$ (**CORE-1**, for every $`\alpha`$; proof by
  Carlson 2009, Def 9.1, Lemma 9.3 and Thm 14.11), when $`\beta`$ is a limit (LIM1), and when $`\beta = \alpha + 1`$
  (ONE-POINT). For $`\le_2`$: a successor stage has no $`\le_2`$ relation in either structure (SUCC2), and the
  converse holds when $`\beta`$ is a limit of its $`\le_1`$-predecessors (LIM2).
- **DICH** (2026-10, 1 review). If $`\beta_0 \lt \infty`$, exactly one case holds. (i) $`\beta_0 = \beta' + 1 \gt \kappa_C`$, and
  the difference is an extra $`\alpha \le_1^C \beta_0`$ with $`\alpha \lt \beta'`$, $`\alpha \notin G_C`$. (ii) $`\beta_0 = \omega^\lambda`$ with $`\lambda`$
  a limit, $`\le_1`$ to $`\beta_0`$ agrees, and the difference is an extra $`\alpha \le_2^C \beta_0`$; the
  $`\le_1`$-predecessors of $`\beta_0`$ have a largest one $`d \lt \beta_0`$, and $`\alpha \le_2 d`$. So below $`\kappa_C`$ the two
  structures can first differ only by a $`\le_2`$ relation of type (ii).
- **R-INC** (2026-10, 1 review). Write W(C) for the claim in $`R_2^C`$, Σ2-GAP for "no extra $`\le_2^C`$ relation of
  type (ii) at a stage $`\le \kappa_C`$" (the referee notes it is equivalent to $`\kappa_C \le \beta_0`$), and INC for
  "$`\le_i^S \subseteq \le_i^C`$ everywhere". Then W(C), Σ2-GAP and INC give AGR, and so
  $`\mathrm{Core}(R_2^S) = \mathrm{Core}(R_2^C) = \rho`$.
- **Stages of type (ii)** (2026-10, 1 review). Such a stage is a $`\beta = \omega^\lambda`$ ($`\lambda`$ a limit) where the
  structures agree on all pairs below $`\beta`$ and on $`\le_1`$ to $`\beta`$, and the $`\le_1`$-predecessors of $`\beta`$ are
  nonempty and bounded, with largest one $`d`$. Let $`D_2 = \{\gamma \lt \beta : \gamma \le_2^C \beta\}`$.
  - **MAX2.** If $`D_2 \ne \emptyset`$, it has a largest element $`a^* \le d`$, and the $`\le_2`$ converse at $`\beta`$ holds for all of
    $`D_2`$ iff $`a^* \le_2^S \beta`$. If $`\beta_0`$ is of type (ii), its extra relation can be taken to be $`(a^*, \beta_0)`$.
  - **RED-d.** $`a^* \le_2^S \beta`$ iff $`\Pi_2`$-UP($`\beta`$): every $`\Pi_2`$ sentence with parameters $`\lt a^*`$ that is true in
    $`R|d`$ is true in $`R|\beta`$. Only witnesses that meet $`[d, \beta)`$ need work. **LOW-Y**: the test T2 holds for every
    $`Y \subseteq [\alpha, d)`$.
  - **FIRST2.** The first $`\lt_2`$-pair $`(\upsilon_\omega, \upsilon_{\omega+1})`$ is a stage of type (ii) with $`a^* = d = \upsilon_\omega`$. The
    referee added (proved): $`a^* = d`$ at every stage of type (ii) below $`\upsilon_{\omega^2}`$, so RED-d reduces nothing at
    the stages where $`R_2`$ is known.
  - **UPCOPY.** Inside the core: let $`P`$ be isominimal with $`a \lt_2 b`$ in $`P`$, and $`Y^\circ = P \cap [a, b)`$. Every
    extension "at $`a`$" (Carlson 2009, Def 8.6) of the downward copy of $`Y^\circ`$ appears below $`b`$ over some upward copy
    of $`Y^\circ`$. That copy lies above all of $`P \cap b`$; it is not $`Y^\circ`$ itself.
  - **EQ-E.** These are equivalent: (E) $`\kappa_C \le \beta_0`$; Σ2-GAP; $`\Pi_2`$-UP($`\beta`$) at every stage $`\beta \lt \kappa_C`$
    of type (ii); **Conjecture CORE-2** (inside the core, at a stage of agreement, $`\le_2^C`$ gives
    $`\Sigma_2`$-elementarity; the order-2 analogue of Carlson 2001, Lemma 5.7(4); Carlson 2009, p. 97, says the
    equivalence "will be established elsewhere").
  - **R-OM.** (R) "$`\kappa_C \le_1^S \gamma`$ for all $`\gamma \ge \kappa_C`$" iff $`\kappa_C \le_1^S \Omega_1`$ (this uses
    $`\kappa_C \le \Omega_1`$, from HULL, [README.md](README.md) §3). Under (E) it holds for every $`\gamma \in [\kappa_C, \beta_0]`$.
  - **AGR iff (E) and (R).** W(C) is not needed for AGR, only for "$`= \rho`$".
  - Open: **PIN** (move the extension from the upward copy back onto $`Y^\circ`$) and **LOW** (extensions with a new
    point $`\le \max X`$, or whose least new point is not additive principal). Only "PIN and LOW give CORE-2" is shown.

## 9. The fourteenth round

Four papers (2026-10), each refereed once, so a result of this section has 1 review unless a count is given. **2 reviews** means that the
referee of §1 accepted the result as a transfer and the referee of this round checked the full proof. No paper uses the papers listed at the
top of this page. No Lean file was added: one paper (§9.1) checked a Lean test file of named points with leanman (green, and green in the
referee's rerun); it only compares terms with a test copy of the normal-form test, so it counts as a check. Levels are renumbered as in §4.

### 9.1 The transfers as full proofs, the names up to $`\nu_P`$, and the claim up to $`X_3`$

Notation of §1. For a restart $`\lambda`$: $`s_2 = \upsilon_{\lambda+2}`$, $`\tau_1 = \upsilon_{\lambda+\omega}`$, $`\delta = \delta_\lambda = \upsilon_{\lambda+\omega+1}`$, and $`R(\lambda)`$ is the formal reach of
[BREAK.md](BREAK.md) §4. $`\Theta_{s2}`$ and $`\Theta_{\tau 1}`$ are the least restart indices with $`R(\lambda) \ge \delta + s_2`$ and $`R(\lambda) \ge \delta + \tau_1`$ (like $`\Theta_\delta`$, $`\Theta_{d\omega}`$).
$`\mathrm{cmax}(x)`$ is the set of countable maximal subterms of the normal form of $`x`$, and $`\pi_g = \psi_{\Omega_2}(A_g)`$.

- **Definition of $`R`$, amended** (the referee: this must be written down, because every upper half below rests on it). $`R(\lambda)`$ is the least
  $`y`$ in $`(\delta, \rho_{\lambda+\omega^2})`$, not in $`[\delta, \rho_{\lambda+\omega^2})`$, with the property of [BREAK.md](BREAK.md) §4. Read literally, the old definition gives $`R(\lambda) = \delta`$ at
  every restart with $`\mathrm{logend}(\eta_\lambda) = 2`$, because the condition is empty there; then the chain of proofs below falls apart. The amended $`R`$ is
  the one the earlier proofs use, and the bound "reach $`\le R`$" holds for it. This is the off-by-one repair of [BREAK.md](BREAK.md) §4, now accepted.
- **Lemma S and COMP-S** (proved, 2 reviews). For any two $`\varepsilon`$-bases below $`\Omega_2`$, countable or not, and any strictly increasing additive
  parameter map that sends principal numbers to principal numbers, substitution is an isomorphism of Wilken's systems for $`\lt`$ and $`+`$, and it
  moves the parameters by the map; composites of substitutions are substitutions. The proof follows Wilken 2007 (APAL 145, 130–161), L.5.3. REN,
  SUBST-ISO and the uses at the bases $`\theta`$ and $`G(\zeta)`$ in §1 are special cases.
- **GEN⁺** (cited): the case $`\eta \lt \Omega_\omega`$ of GEN-EXT ([BREAK.md](BREAK.md) §2).
- **SLOW$`_\zeta`$** (proved, 2 reviews). Every lemma of LOW-STEP (ARG, PMAX, Q, Q1, D, M) restated at the levels of the base $`G(\zeta)`$ and proved.
  (The referee: one sentence of 5.4 (ii) is wrong for nodes inside a stop; those nodes lie below the stop, so the conclusion holds.)
- **PHI, U\* and R-CAP** (proved, 2 reviews), now by one induction on $`\lambda`$, with $`\kappa`$ an $`\varepsilon`$-number and VIS applied at $`A_\eta`$ (the points m4, m5, m7
  of the review of §1). No FRAG. Lower bounds: $`\Theta_{s2} \ge \iota'(\theta_2)`$, $`\Theta_{\tau 1} \ge \iota'(\theta_2\cdot\omega)`$, $`\Theta_\delta \ge \iota'(\theta_2\cdot(\omega+1))`$, $`\Theta_{d\omega} \ge \iota'(\eta_{d\omega})`$,
  $`\Lambda^* \ge \iota'(\theta_2\cdot\omega^2)`$.
- **SSTEP$`_\zeta`$** (proved). Theorem STEP one level up: the map $`B`$ at the base $`G(\zeta)`$, with $`X_0 = \Omega_\omega + \theta_2\cdot\zeta`$ and the level-0 code
  $`\psi_{\Omega_3}(\omega^{B(\alpha)})`$, is strictly increasing into $`G(\zeta+1)`$. So $`T^{G(\zeta)} \cap \Omega_2 \le G(\zeta+1)`$. The other inequality is open and unused: it needs
  every ordinal below the bound, and Lemma IS covers only countably many. **Erratum** to L3 of [VEBLEN.md](VEBLEN.md) §8: for the same reason only
  $`T^{\Omega_1} \cap \Omega_2 \le \theta`$ is proved there, not equality; nothing uses equality.
- **Lemma C, the realizer map, B-PAR, HULL-SEG, REAL, Lemma L$`_R`$, BRACKET** (proved). The offsets of a restart are read through Wilken's terms (Lemma C).
  A realizer map sends them to exponents of restarts, with control of the parameters (B-PAR; the referee: run its induction on the terms of the
  simultaneous system, since Lemma S is proved for Wilken's terms). HULL-SEG:

```math
C_g \cap \Omega_2 = \{\, x \lt \pi_g : \mathrm{cmax}(x) \subseteq H(g) \,\}.
```

  REAL: realizers exist cofinally (the referee: only for $`\nu \le \eta_0`$, which is all its uses need). Lemma L$`_R`$ (the paper's "Lemma L"; renamed
  here because Lemma L is a Lean lemma of [README.md](README.md) §3): every restart $`\mu`$ whose exponent is the image of an offset $`m`$ has
  $`R(\mu) \ge \delta_\mu + c_\mu(m)`$, without FRAG; the same for the reach, given FRAG. BRACKET: lower and upper bounds for $`R(\lambda) - \delta`$ from the two maps.
  (The referee: the base case of Lemma L$`_R`$ should cite a different earlier lemma; same conclusion. Corrected in the fifteenth round: $`\delta`$ is not reflected at a
  restart with logend 2, so the base case uses the step lemma for block targets with step 1, [SHIFT.md](SHIFT.md) §1.)
- **NAMES-EQ** (proved; the referee checked both halves of every row). With $`\eta_{d\omega} = \omega^{\theta_2+1} + \theta_2 + \omega^{\omega^{G+1}}`$ and
  $`G = \psi_{\Omega_2}(\Omega_\omega + \omega^{\theta_2+1} + \theta_2)`$:

| restart | index | $`\rho`$ | $`R`$ | FRAG |
|---|---|---|---|---|
| $`\Theta_{s2}`$ | $`\iota'(\theta_2)`$ | $`\psi_{\Omega_1}(\Omega_\omega + \theta_2)`$ | $`\delta + s_2`$ | not used |
| $`\Theta_{\tau 1}`$ | $`\iota'(\theta_2\cdot\omega)`$ | $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+1})`$ | $`\delta + \tau_1`$ | not used |
| $`\Theta_\delta`$ | $`\iota'(\theta_2\cdot(\omega+1))`$ | $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+1} + \theta_2)`$ | $`\delta\cdot 2`$ | not used |
| $`\Theta_{d\omega}`$ | $`\iota'(\eta_{d\omega})`$ | $`\psi_{\Omega_1}(\Omega_\omega + \eta_{d\omega})`$ | in $`[\delta\cdot\omega, \delta_2)`$ | not used |
| $`\Lambda^*`$ | $`\iota'(\theta_2\cdot\omega^2)`$ | $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2})`$ | | upper half |
| $`\Lambda^* + \omega^2`$ | | $`\nu_P = X_2 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{\theta+2})`$ | | upper half |

- So the names that §1 conjectured are proved (FRAG is proved, [BREAK.md](BREAK.md) §4). $`\Theta_{d\omega}`$ needs a mixed realizer (multiples of $`G`$ plus an image),
  because the plain map overshoots there. The value of $`R(\Theta_{d\omega})`$ is not determined.
- **Theorem X3** (proved, no FRAG). With $`\lambda_2 = \iota'(\theta_2\cdot\omega^2)`$:

```math
\nu_C \ge X_3 = \upsilon_{\lambda_2+\omega^3\cdot 2} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{\theta+3}\cdot 2).
```

  Proof: R-CAP, and in both cases of NU-CT ([BREAK.md](BREAK.md) §2) the left end of the pair at $`\nu_C`$ is a $`\rho_L`$ with $`\omega^3 \mid L \gt \lambda_2`$ and the right end has
  index $`\ge L + \omega^3`$ (FIRST-PAIR and Lemma GHOST, [BREAK.md](BREAK.md) §2). (The referee: case (A) uses $`R_2^S`$ facts through $`\nu_C = \nu_S`$; correct, the
  wording should say so.) So **Wilken's claim holds in $`R_2^C`$ on $`[0, X_3]`$, both halves** (no FRAG): the core half by $`[0, \nu_C] \subseteq \mathrm{Core}(R_2^C)`$, the
  names half by Lemmas L and IS. Also on $`[0, \nu_P] = [0, X_2]`$ (2 reviews: as a transfer in §1, in full here).
- **Open**: an InaccPsi upper bound for $`\nu_C`$. Realizers, the upward and downward copies, and the twisted copies TW-0 give only $`\le_1`$-facts or copies of a
  $`\lt_2`$-pair already known to exist. A named bound needs one new pair $`\rho_L \lt_2 b`$ with $`b`$ named: an isomorphism of a final segment $`[\rho_L, b)`$
  onto a segment above a $`\le_1`$-predecessor of $`\rho_L`$, as in Wilken 2020, Thm 21.13 (then Prop 21.11 gives the pair). The candidate pair is
  $`a_0 \lt_2 \nu`$ of Conjecture NU-NAME ([BREAK.md](BREAK.md) §2). (Now $`\nu_C \ge X_4`$, and no new pair is needed: two $`\le_1`$-statements at one named pair
  give the bound, [SHIFT.md](SHIFT.md) §1; then $`\nu_C \ge X_5`$ given FRAG, and the two statements are still open, §8.1 there; then $`\nu_C \ge X_8`$ given FRAG, and (P) needs reaches across an uncountable offset, §9.1 there; then $`\nu_C \ge X_9`$ given FRAG, [SHIFT2.md](SHIFT2.md) §1.1.) Also open: the value of $`R(\Theta_{d\omega})`$, and whether
  $`m_0 \ge \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ for the least $`\le_1`$-predecessor $`m_0`$ of the left end of the first new pair.

### 9.2 Native codes: modules up to $`\Lambda_T`$

Notation of §2. $`F(\alpha) = \upsilon_{1+\alpha}`$. For a normal map $`H`$: $`O_1(H)`$ enumerates the fixed points of $`H`$; $`O_{n+1}(H)`$ enumerates the $`z`$ with $`O_n^z(H)(0) = z`$;
$`S(H)`$ enumerates the common values of all $`O_n(H)`$; $`T(H)`$ enumerates the $`z`$ with $`S^z(H)(0) = z`$. So $`\Gamma^\upsilon_1 = O_2(F)(0)`$, and $`\Lambda_T = T^{\omega^2}(F)(0)`$.

- **MODULE-RED⁺** (proved, as an implication). MODULE-RED of §2 holds for every module block of shape (MA⁺): $`r \lt x \lt_2 y`$, $`r`$ and $`x`$ are $`\le_1`$ to the top $`R`$,
  and some $`c \in (y, R]`$ has $`c \le_1 c + A`$ with $`A \ge r`$ and $`c + A \le R`$. This allows several inner chains, nested pairs, sums containing $`x`$, and the blocks
  $`c \le_1 c + y`$ and $`c \le_1 c\cdot 2`$ of conv. EXIST-AMB gets the case asked for in the review of §2. (The referee: a remark that every other pair lies in $`(x, y)`$ needs
  "no element in $`(r, x)`$"; no proof uses it.)
- **CHAIN⁺** (proved). A block with $`c \le_1 c + A`$ hosts every nest of blocks that each carry one decoration $`u \le_1 u + D`$ ($`D`$ may contain $`u`$), as long as every
  $`D`$, read in the host, is below $`A`$. (The referee: CHAIN of [VEBLEN.md](VEBLEN.md) §9 is its base case, not a special case.)
- **DOM-T, NO-HIGH-T** (proved). Every fixed point of $`\upsilon`$ below $`\Lambda_T`$ has canonical data (a tier below $`\omega^2`$, a level, a greedy signature), and two
  fixed points compare by their data.
- **LEX-HOST, (MC) and Theorem IDX-T** (proved). Modules of scheme T: the finite positions are coded by a nest of blocks, the tier and the level by
  the decoration. So the native codes are ordered on $`[\omega, \Lambda_T)`$, and natively

```math
\iota(\mathrm{CH}_2) \ge \Lambda_T \gt T^\omega(F)(0) \gt T(F)(0) \gt S(F)(0) \gt \Gamma^\upsilon_1 = \Lambda_\Gamma.
```

  (The referee: the same bounds for the conv patterns of (0,0,0)(1,1,1)(2,1,1)(3,1,1) and (0,0,0)(1,1,1)(2,2,0) are proved for the module patterns; that
  these equal conv's output is checked.) Conjectured names, with $`H'(\Delta) = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Delta})`$: $`O_n(F)(0) = H'(\Omega_1^n)`$,
  $`S(F)(0) = H'(\Omega_1^\omega)`$, $`T(F)(0) = H'(\Omega_1^{\omega+1})`$, $`\Lambda_T = H'(\Omega_1^{\omega+1}\cdot\omega^2)`$. Still far below $`\Lambda_\varepsilon \lt \nu_C`$; the progress is on the native route only.
- **Not counted** (the referee: a remark about two proof methods): "no module of $`\Lambda_T`$ by CHAIN⁺ or LEX-HOST".
- **Open**: the module of $`\Lambda_T`$ itself: decorations with several slots (an outline, checked on paper for 2 slots), then CHAIN-REL (hosting inner parts
  that use the outer $`x`$, where GEN (a) cannot be used). (G2): a collapsing function $`\vartheta^\upsilon`$ over $`\upsilon`$ is defined, with its comparison lemma, dictionary and
  names as conjectures; DOM-T is an analogue of one direction of that lemma (the referee); expected reach $`\Theta_1`$. $`\iota(\mathrm{CH}_2) \ge \theta_0`$ stays open.

### 9.3 The shapes of $`\Phi_3`$: nested blocks, 2,330 of 3,166

Notation of §3.

- **OPQ-R** (proved, meta) and **LEMMA OPEN** (proved). Runs of the rewritten program on terms with opaque prefixes, open run counts and staircase
  segments give the result on every instance. (The referee: the code opens only the first run; every open term built for the matrices below has
  at most one run.)
- **Theorem NB** (proved; part (a) of LEMMA SLOT is false as written, and the referee's repair, checked on all 155 matrices, makes it and NB proved).
  For an M1 matrix whose run is among the children of the root: $`V(A[n]) = V_{base} \cup \beta(0) \cup \dots \cup \beta(n)`$, where each block $`\beta(j)`$ is a fixed list of
  nodes with family slots, each member again such a list (so the blocks double).
- **NB-DER** (proved). Each block type maps onto a long pair $`x \lt_2 y`$ in the top block of the matrix; GEN gives conv$`(A[n]) \ll`$ conv$`(A)`$. 155 matrices.
- **SUM-CORE-NB** (26), **IX-NB** (59; its lemma IX-PHI\* is written only as a sketch), **SUM-CORE-2** (30), **IX-STAIR** (73), and $`(0,0,0)(1,1,1)`$ as a staircase
  core (39 of the 73): proved.
- **Not proved**: the GEN induction of 2.6 (no check that the run count decreases). No counted matrix uses it. (Now replaced by GEN-IND, proved,
  [SHIFT.md](SHIFT.md) §3.)
- **The tally** (the referee reproduced it; $`2{,}330 = 1{,}987 + 343`$):

| class | matrices | proved for every $`n`$ | given a condition checked for small $`n`$ | $`t = 2`$, given a shape checked for small $`n`$ | open |
|---|---|---|---|---|---|
| I | 581 | 479 | 0 | 0 | 102 |
| SUM | 603 | 544 | 7 | 0 | 52 |
| ROOT | 635 | 587 | 0 | 0 | 48 |
| III | 1,347 | 720 | 0 | 24 | 603 |
| all | 3,166 | 2,330 | 7 | 24 | 805 |

- The 2 matrices "given LOW" of §3 are among the new ones. **Left** (836): M1 18 (5 whose reach recurses through every smaller run length, 6 with one
  of these as core, 1 whose template fails at the first block, 3 SUM, 3 with a template node below the core); M2 139, M3 28, M4 14, M5 23; $`t = 2`$:
  III 160, ROOT 31, I 15, SUM 26; $`t = 1`$: 382. The minor points m1–m6 of the review of §3 are applied as errata.

### 9.4 $`\nu_C = \nu_S`$: twisted copies

Notation of §4.

- **PUSH** (proved). $`u_{m+1} \le_1 x`$, so no point of $`U_2`$ needs a twisted copy: the case "the points $`u_{m+j}`$" of (TWIST\*) does not occur.
- **TOPSUM, REACH-RED, TW-CLASS** (proved; the citation of Wilken 2007, APAL 145, 162–175, Thm 2.2 matches the paper). (CUT′) follows from an exact
  transfer of reaches: $`\mathrm{lh}(\Psi_0(a)) = \Psi_0(L_{top}) + T_m(L_{low})`$. A twisted triple occurs only at a twisted point, and the twisted points are
  classified by their closed forms.
- **LADDER, DIAG, FIX-LADDER, LH-DELTA** (proved; one step inherits a repairable slip of Theorem KV, [FANFREE.md](FANFREE.md) §10.3). Every restart whose index is
  not in the diagonal class $`\mathrm{Fix}(f_\Delta)`$ has a closed reach below $`\delta\cdot 2`$. Long restarts, the points of $`U_2`$ and $`\nu`$ have indices in it.
- **NU-K** (proved). Long restarts are cofinal below $`\nu`$ (Carlson 2009, Def 5.3, clause 2).
- **FRESH**: not proved as written (at level 0 the new index can fail to be a restart index); the referee gives a one-line repair. **TW-MULTI** (proved
  with that repair and one more): twisted copies exist for any finite union of skeletons of small closed-form restarts, so for several blocks at
  once, for the restarts in $`\mathrm{Fix}_1 \setminus K`$, and for the points of $`K`$ outside $`\mathrm{Fix}(f_\Delta)`$. **TW-MIX** (proved, with runs built in increasing
  order): these copies combine with Carlson's copy on the anchors, under four conditions.
- **DICT, PROF-1** (proved). (PROF) holds for every symbol with at most one position $`\ge u`$.
- **Not proved**: (TWIST\*) in general. Left: twisted points with index in $`\mathrm{Fix}(f_\Delta)`$ (long restarts among them), top data, points of a run region
  that are not in a skeleton (twisted or not; the referee's example $`\omega^{\rho_a+1}`$ shows that the paper's list of the residue is not complete), and
  failures of the conditions SEP and ROOM. (PROF) with two or more positions $`\ge u`$, and the base change beyond $`u^\#`$, are open. Neither $`\nu_C = \nu_S`$ nor
  $`\nu_C \lt \nu_S`$ is proved.

### 9.5 Status after the fourteenth round

The fifteenth to eighteenth rounds changed this status; see [SHIFT.md](SHIFT.md) §5, §8.5, §9.5 and [SHIFT2.md](SHIFT2.md) §1.5.

- Wilken's claim in $`R_2^C`$: both halves hold on $`[0, X_3]`$ with $`X_3 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{\theta+3}\cdot 2)`$, no FRAG and no transfer left;
  the names of $`\Theta_\delta`$, $`\Theta_{d\omega}`$, $`\Lambda^*`$ and $`\nu_P = X_2`$ are proved; the core half holds on $`[0, \nu_C]`$ with $`\nu_C \ge X_3`$.
- The lower-bound program below $`\theta_0`$: the step below SRO is proved for every $`n`$ on 2,330 of the 3,166 sample matrices; $`\iota(\mathrm{CH}_2) \ge \Lambda_T`$ natively.
- Upper bounds: still none by an InaccPsi term for $`\iota(\mathrm{CH}_k)`$, $`m_F`$, $`x_F`$, $`C^*_3`$ or $`\nu_C`$.
- $`\nu_C = \nu_S`$: twisted copies exist for small closed-form skeletons; left: the residue at $`\mathrm{Fix}(f_\Delta)`$, SEP, ROOM and (PROF).

### 9.6 Checks of the fourteenth round

Each run was under 60 seconds; none is a proof. Certificates count only when replayed.

- §9.1. The shifted map $`B`$ at the bases $`G(0)`$, $`G(1)`$, $`G(\omega)`$, $`G(\omega+1)`$: 1,278,400 pairs, 0 failures; two broken controls fail. B-PAR as an equivalence: 9,000 pairs,
  0 disagreements. HULL-SEG: 33,800 pairs, 0 disagreements. The 9 named points are normal forms and increasing. The referee: $`E(B(t)) \ge t`$ on 2,995 terms
  at 4 bases (if it failed, BRACKET would contradict itself), 1,200 realizers built as in REAL, all valid, and the runs reproduced with 0 disagreements.
- §9.2. 23 module blocks (19 new) are patterns, RF, fan-free and L1p-free; 4 are equal to conv's output; certificates: 18 of 20 in the predicted
  direction and 5 of 7 for CHAIN⁺, all replayed; 0 of 6 in the reverse direction. The referee's reruns are identical, and 5 own reverse searches
  found nothing (each stopped at 45 s).
- §9.3. The node sets of the full builds at $`n = 6, 7`$ agree for all 155 NB matrices (node sets only), and the 132 index templates agree. The referee: ordered lists with lh and succ at $`j = 6, 7`$
  (155 of 155) and $`j = 8`$ (52 of 52); the templates at $`n = 8, 9`$; $`(0,0,0)(1,1,1)`$ passes the step for $`n = 2, \ldots, 20`$.
- §9.4. The readings of K(3,0,0), K(3,0,0)(3,0,0) and K(3,1,0) match LADDER and DIAG. The referee: 18 strings with the program, which also match 4 new predictions.

### 9.7 Open

The fifteenth to eighteenth rounds changed this list; the current list is [SHIFT2.md](SHIFT2.md) §1.7.

- Upper bounds: an InaccPsi bound for $`\nu_C`$ (one new pair $`\rho_L \lt_2 b`$ at a named $`b`$, §9.1), for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$, $`f_0`$, $`m_3`$, $`c_0`$.
- The first inaccessible: $`H_m`$, through $`\iota(\mathrm{CH}_2) \ge \theta_0`$ (modules from $`\Lambda_T`$ on: several slots, CHAIN-REL, or the collapsing function $`\vartheta^\upsilon`$);
  UNIF-FS below SRO on the 836 matrices of §9.3.
- $`\nu_C = \nu_S`$: (TWIST\*) at $`\mathrm{Fix}(f_\Delta)`$ and for points outside the skeletons, SEP and ROOM, (PROF) with two or more positions.
- Names: $`R(\Theta_{d\omega})`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$; names beyond $`X_3`$; the rest of [COVER.md](COVER.md) §9.
