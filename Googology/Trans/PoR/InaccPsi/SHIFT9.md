[← Back](README.md) | [English](SHIFT9.md) | [Japanese](SHIFT9-ja.md)

# $`R_2^+`$, the thirty-fifth to thirty-seventh rounds: the reaches of the skeleton up to $`L(\theta'_2\cdot(\omega+1)+G''(\omega+1)\cdot\omega)`$, the first gap of $`\mathrm{Core}(R_2^S)`$, and the stage route toward $`\theta_0`$

This page continues [SHIFT8.md](SHIFT8.md) (§2 there is the thirty-fourth round); §1 is the thirty-fifth round, §2 the thirty-sixth, §3 the thirty-seventh; the thirty-eighth to fortieth rounds are on [SHIFT10.md](SHIFT10.md), the forty-first on [SHIFT11.md](SHIFT11.md). The status words are those of [README.md](README.md) §3: **proved** means that
an independent referee found the result proved with no fatal or blocking point. A statement with a blocking point against it is listed under **Not proved**.
A certificate counts only when it was replayed. A result that the referee calls only a restatement of something known is not counted as progress.

**Later (the fortieth round, [SHIFT10.md](SHIFT10.md) §3.2):** the frontiers of this page ($`L(G_2)`$, $`L(\Omega_2+\Phi^{P'}\cdot\omega)`$, $`L(\theta'_2\cdot(\omega+1)+G''(\omega+1)\cdot\omega)`$, and $`Z^\Gamma`$ in $`R_2^S`$) rest on $`\nu_C = \nu_S = L(\omega+1)`$ and on the exact calculus in the gaps, which are not proved as written; so they are **not proved as written**. The code side (the tier maps), the results on (E) that use no reach, and the native codes stand. Given FRAG, the claim is proved in $`R_2^C`$ on $`[0, X_{21}]`$. **Later (the forty-first round, [SHIFT11.md](SHIFT11.md) §1.1):** $`\nu_C = \nu_S = L(\omega+1)`$ and the claim on $`[0, \nu_C]`$ are proved again, given FRAG; the exact calculus in the gaps above $`\nu_C`$ is not yet run again, so the results of this page above $`\nu_C`$ stay not proved as written.

## 1. The thirty-fifth round

Three papers (2026-10), each refereed once: a paper on the reaches of the restarts of the skeleton for every code below $`G_2`$ (§1.1), a paper on (E) and $`\beta_0`$ (§1.2), and a paper on
native codes (§1.3). A result in this section has 1 review unless a count is given. The claim on $`[0, L(\varepsilon_{\Phi_\Omega+1}+\omega^2)]`$ is proved in the first two papers independently, so the
step from $`L(\varepsilon_{\Phi_\Omega+1})`$ to $`L(\varepsilon_{\Phi_\Omega+1}+\omega^2)`$ has **2 reviews**. The minor points of the review of [SHIFT8.md](SHIFT8.md) §2.1 are applied by the first paper, and its referee
checked each repair (**2 reviews**); the second paper uses the results of [SHIFT8.md](SHIFT8.md) §2.2 in the forms corrected by that review; the third paper applies the minor points of the review of
§2.3 there (its referee gave no separate verdict on them). None of the papers uses Wilken, JSL 72 (2007), Carlson, AML 38 (1999), or Wilken, AML 45 (2006) (the referees checked this). Papers
cited: in §1.1 only through refereed stages, as in [SHIFT8.md](SHIFT8.md); in §1.2 Carlson's [C11], https://arxiv.org/abs/1104.1686 (the Categoricity Theorem (a)–(d), Claim 1, Cor 0.8, Cor 0.9; an
unrefereed preprint, its Claim 1 and the overlap step re-checked in the thirty-fourth round), and Carlson 2009 (Def 5.2, Def 5.3, Def 5.4, L.5.5, L.5.7, Thm 14.10). No paper is used in a
proved step of §1.3, which does not use FRAG. No Lean file was added: the ordinal inputs of §1.1 and §1.2 were checked with Lean files that only compare terms (`#eval`, no theorem; green,
identical to Python, and identical in the referees' reruns), and the abstract cores of two lemmas of §1.3 were checked with a Lean file (green, only the standard axioms, no `sorry`; the
referee rechecked it); these count as checks. Levels are numbered as in [SHIFT8.md](SHIFT8.md) (one higher than in the papers). "Given FRAG" is as there.

Notation (as in [SHIFT8.md](SHIFT8.md)): $`L(e) = H(\eta_e) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + P'\cdot e)`$, $`P' = \psi_{\Omega_2}(\Omega_\omega\cdot 2)`$, $`\Phi_\Omega = \psi_{\Omega_2}(\Omega_2)`$, the restarts $`L(\lambda'')`$ of the skeleton with
code $`c''(\lambda'')`$ and pairs $`(\tau''_j, \delta''_j)`$; $`G(\zeta) = \psi_{\Omega_2}(\Omega_\omega + \theta_2\cdot\zeta)`$ as in [SHIFT2.md](SHIFT2.md) §2.1, so $`G_2 = G(\omega^2) = \psi_{\Omega_2}(\Omega_\omega + \omega^{\theta_2+2})`$ with
$`\theta_2 = \psi_{\Omega_3}(\Omega_\omega)`$. For a restart $`b = L(\lambda'')`$, the **first region of its gap** is $`[b, H(\eta_{\lambda''}+\omega^2))`$, with the $`\upsilon`$-points $`H(\eta_{\lambda''}+1+\zeta)`$, $`\zeta \lt \omega^2`$; and for a code $`c`$,

```math
o_b(c) = \text{the order type of the codes } c' \lt c \text{ whose countable constants are all below } b.
```

### 1.1 The reaches of the skeleton for every code below $`G_2`$, and the claim up to $`L(G_2)`$, given FRAG

- **The repairs of the review of [SHIFT8.md](SHIFT8.md) §2.1** (m1–m7; **2 reviews**). The cofinal tower starts at $`t_0 = \Phi_\Omega+1`$ (m1). EXACT-G″ and TOP-REG″ are restricted to
  $`\lambda'' \lt \varepsilon_{\Phi_\Omega+1}`$ (m2), and are now proved again on the larger domain below. The uses at $`\lambda'' = \Omega_1\cdot\omega`$ are labelled as transfers (m3); wording, labels and the convention
  for normal forms (m4–m6). The point m7 of that review was itself wrong: since $`-1 + x = x`$ for infinite $`x`$, the old label "codes up to $`\Phi_\Omega+1`$" was exact (the referee of this round
  agrees). One label of a check of the repair is wrong (m2 below).
- **The domain of $`L`$ below $`P'`$** (ARG-BOUND, DOM″, DOWN″, COF″, TAIL″; proved). For every normal form $`e \lt P'`$: $`e`$ is in the domain of $`L`$ exactly when every countable constant of $`e`$
  is below $`L(e)`$ (before: for $`e \lt \varepsilon_{\Phi_\Omega+1}`$). ARG-BOUND: outside its countable subterms, every collapse in $`e`$ with an uncountable value has its argument below $`\Omega_\omega\cdot 2`$.
- **The reading tiers at every $`\upsilon`$-point** (READ$`^b`$; proved by transfer, no FRAG). The readings of the codes below $`\theta`$ at one $`\upsilon`$-point ([VEBLEN.md](VEBLEN.md) §1, §8, [SHIFT2.md](SHIFT2.md) §3.1,
  [SHIFT3.md](SHIFT3.md) §1.1, §2.1) use only that the base is a $`\upsilon`$-point, so they hold at every $`L(\lambda'')`$. One cited input, stated only at the first level, is never used (m6).
- **Theorem EXACT-O″, the Veblen closure above $`\Phi_\Omega`$ and every code below $`\theta`$** (RED-O″, EXACT-O″; proved by transfer, given FRAG). For every restart $`b = L(\lambda'')`$ of the skeleton with
  code $`c = c''(\lambda'') \lt \theta`$:

```math
r(L(\lambda'')) = \delta''_1(\lambda'') + o_b(c).
```

  This is the conjecture EXACT-O″ of [SHIFT8.md](SHIFT8.md) §2.1 below $`\theta`$: the reading EXACT-O$`^n`$ of [SHIFT3.md](SHIFT3.md) §2.1 one step up. Example: the code $`\Gamma_{\Phi_\Omega+1} = \psi_{\Omega_2}(\Omega_2+1)`$ gives
  $`\delta''_1 + \Gamma_{\Phi^b+1}`$, with $`\Phi^b`$ the least fixed point of $`\alpha \mapsto \Gamma_\alpha`$ above $`b`$. The referee: in the upper half, a reading that leaves the segment of $`b`$ needs the enlarged form
  of the upper-bound rule of the next item, which is what is used (m5).
- **Codes from $`\theta`$ to $`G_2`$** (the θ-reading, INDEX″$`_1`$, H-RC″$`_1`$, TOP-REG″$`^\theta`$, Theorem EXACT-O″$`^\theta`$, ATTAIN″$`^\theta`$; proved by transfer, given FRAG; the referee checked each case
  against the region pins of the earlier rounds). For codes in $`[\theta, G_2)`$, $`o_b`$ is the reading of [SHIFT3.md](SHIFT3.md) §2.1 with the $`\upsilon`$-points of the first region of the gap of $`b`$ in place of
  those above $`\nu`$; for example $`o_b(\theta) = H(\eta_{\lambda''}+1)`$, the next $`\upsilon`$-point above $`b`$, and $`o_b(G(\omega))`$, $`o_b(G(\omega+1))`$ are the two ends of the first pair of that region. So the target stays in $`[\delta''_1, \delta''_1\cdot 2)`$, and the obstacle
  of the window at the first level ([SHIFT4.md](SHIFT4.md) §1.1) does not arise. New pins on the first region of a base of the skeleton give the upper-bound rule TOP-REG″$`^\theta`$, and FRAG″ the lower
  bound: the formula above holds **for every code below $`G_2`$**. The least restart whose offset reaches a given code is also known (ATTAIN″$`^\theta`$).
- **Theorem C$`^\theta`$ and the new frontier** (proved by transfer, given FRAG). Below $`L(G_2)`$, $`R_2^S`$ is skeletal for the skeleton of the points $`L(e)`$: every new pair is a pair $`(\tau''_j, \delta''_j)`$ and
  contains no new pair, every restart has an exact reach, and there is no fan apex and no triple nest. So $`\beta_0 \gt L(G_2)`$, the least top of a triple nest in $`R_2^C`$ is above it, and **Wilken's
  claim holds in $`R_2^C`$ on $`[0, L(G_2)]`$**, both halves (the names half because the point is a normal form, Lemma L):

```math
L(G_2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+G_2}),\qquad G_2 = \psi_{\Omega_2}(\Omega_\omega + \omega^{\theta_2+2}).
```

  On the way, each with both halves: $`L(\psi_{\Omega_2}(\Omega_2+1))`$, $`L(\psi_{\Omega_2}(\Omega_2\cdot 2))`$, $`L(\psi_{\Omega_2}(\Omega_2^{\Omega_2}))`$ (the end of the Veblen closure), $`L(\psi_{\Omega_2}(\varepsilon_{\Omega_2+1}))`$, and $`L(\theta)`$. The first code not
  covered is $`G_2`$, at the point itself; its reading would be the first restart inside the gap.
- The referee's minor points (none changes a result). In one example the code of $`\lambda'' = G(\omega+1)\cdot\omega = \omega^{G(\omega+1)+1}`$ is $`G(\omega+1)+1`$, not $`G(\omega+1)\cdot\omega`$, so one landmark and two rows of
  the checks are mislabelled (m1). One check label of the repair of m1 names the wrong point; the claim holds (m2). In the description of the skeleton inside a gap, "$`n \ge 1`$ or $`j = 0`$"
  should read "$`n \ge 1`$" (still off at $`n = 1`$, §2.1), and PIN-R uses a bound on the reach of the left ends that should be stated there (m3). The author's own slip of procedure (a stray directory change that failed and
  changed nothing; m7).
- **Not proved.** PIN-R (the pin at the first restart inside the gap): proved up to m3, not used for the frontier; that the same argument works at every restart of the gap: outline (m4). The
  relative far pin through the whole gap: outline. EXACT-O″ for every short restart below $`\psi_{\Omega_1}(\Omega_\omega\cdot 3)`$ (readings that stay below $`\delta''_1\cdot\omega`$): conjecture; it needs that pin and the
  window rule one step up for targets from $`\delta''_1\cdot 2`$ on. The long restarts of the skeleton (conjecture: exactly from the code $`\psi_{\Omega_2}(\Omega_\omega\cdot 2 + \psi_{\Omega_3}(\Omega_\omega\cdot 2)\cdot\omega^2)`$ on), their
  landing calculus, the codes below $`P_3`$ and $`\nu_3`$: open; the order of the remaining steps is written in the paper. $`T_3 \le \nu_3`$ is not claimed.

### 1.2 (E), the first gap of $`\mathrm{Core}(R_2^S)`$, and $`\beta_0`$

Words as in [SHIFT8.md](SHIFT8.md) §2.2; $`f`$ is the isomorphism of the cores, $`\rho(\mu)`$ the least $`\le_1`$-predecessor of $`\mu`$, $`x_F^C`$ the least fan apex of $`R_2^C`$. Write $`\varepsilon = \varepsilon_{\Phi_\Omega+1}`$.

- **The region of $`L(\varepsilon)`$** (PI-EPS, BLOCK″$`_0`$, EXACT-G″$`_\varepsilon`$, C$`^\#`$, AGREE$`^\#`$; proved by transfer, given FRAG). The code $`\varepsilon`$ of $`L(\varepsilon)`$ is a limit code; its reading at $`b`$ is the
  single term $`\varepsilon_{\Phi^b+1}`$, and base change commutes with it (the $`\varphi`$-case of the Veblen reading). So

```math
r(L(\varepsilon)) = L(\varepsilon+\omega+1) + \varepsilon_{\Phi^{L(\varepsilon)}+1},
```

  the whole region of $`L(\varepsilon)`$ is skeletal, $`\beta_0 \gt L(\varepsilon+\omega^2)`$, the least top of a triple nest in $`R_2^C`$ is above it, and the claim holds in $`R_2^C`$ on $`[0, L(\varepsilon+\omega^2)]`$, where
  $`L(\varepsilon+\omega^2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+\varepsilon} + \omega^{P'+2})`$ (a second proof of this part of §1.1). One bound needs a cited fact that is not named (m6).
- **NO-GAP$`^\#`$** (proved, given FRAG). $`[0, L(\varepsilon+\omega^2)) \subseteq \mathrm{Core}(R_2^S)`$ and $`f`$ is the identity there, so **the claim holds in $`R_2^S`$ on $`[0, L(\varepsilon_{\Phi_\Omega+1}+\omega^2))`$**. The referee:
  $`[0, L(\varepsilon))`$ already followed from [SHIFT8.md](SHIFT8.md) §2.1, §2.2, so the gain is one region, not the step from $`L(\Omega_1\cdot\omega)`$ that the paper states (m7); and the lemma ROOT-CORE
  (proved, no FRAG: $`\rho(\beta_0)`$ is the largest $`p \le \beta_0`$ with no $`\le_1`$-predecessor) is not needed for it (m8).
- **The first gap** (GAP-AP, TWIN, MOVE-OBST, S-COVERED; proved, no FRAG). $`\sigma_S`$ is additively principal and lies in $`[\rho(\beta_0), \beta_0]`$. Its twin $`\gamma = f^{-1}(\sigma_S)`$ has, below $`\sigma_S`$, the same
  $`\le_1`$- and $`\le_2`$-predecessors that $`\sigma_S`$ has in $`R_2^C`$. In every isominimal set of $`R_2^S`$ that contains $`\gamma`$, $`\gamma`$ is a $`\lt_2`$-left end, or the least $`\le_1`$-predecessor of a later point above
  the points of the set below $`\gamma`$. A $`C`$-isominimal set all of whose relations hold in $`R_2^S`$ lies in $`\mathrm{Core}(R_2^S)`$, with $`f`$ the identity on it. The referee: one clause, "$`\sigma_S \le \alpha`$ iff
  $`f^{-1}(\alpha) \gt \alpha`$", is proved only from right to left, the other direction does not follow, and the clause is not used (m1); that $`\gamma`$ is additively principal must be stated (m5).
- **β0-CHAR** (proved; **not counted**: the referee calls it the corollary of the finite-set test CMP ([ROUND1.md](ROUND1.md) §1) together with Carlson 2009, Def 5.4, restated; only the name
  "Carlson-closed" is new, m4). $`\beta_0`$ is the least $`b`$ such that some $`\alpha \lt b`$ satisfies Carlson's clauses for $`\alpha \le_k b`$ (Def 5.3, read in $`R_2^S`$) but not $`\alpha \le_k b`$ in $`R_2^S`$.
- **CL2-ONLY and SHARP-RIG** (proved). At a cap of $`\alpha`$ inside a gap of $`R_2^S`$, Carlson's $`\le_2`$ reduces to clause 2 of Def 5.3; so below $`x_F^C`$ the condition RIG of [SHIFT8.md](SHIFT8.md) §2.2 is
  necessary as well as sufficient to exclude a first difference of type N.
- **NO-GO** (proved; the referee checked Carlson's clauses for it by hand). The structure $`R_2^C`$ below a bound, with one $`\le_2`$-relation removed, satisfies the hypotheses (a)–(d) of [C11]'s
  theorem, has arbitrarily long $`\le_2`$-chains, MIN and CC, and its core has a gap. So (E) does not follow from these hypotheses, MIN$`^S`$ and CC$`^S`$ alone; the results above on the first gap use only these and one
  lemma on moving points. The sentence "any proof must use that $`\Sigma`$-elementarity is closed under Carlson's clauses" is a tautology by β0-CHAR, so a remark (m3).
- **Where $`\beta_0`$ can be** (proved as a case split). A first difference below $`x_F^C`$ has one of two shapes: (N1) a cap of $`\alpha`$ inside a gap of $`R_2^S`$ where clause 2 holds, or (N2) $`\alpha`$ has no
  $`\lt_2`$-successor in $`R_2^S`$, and then $`\alpha \notin \mathrm{Core}(R_2^S)`$ and $`\sigma_S \le \alpha`$. Getting $`\beta_0 \ge x_F^C`$ from SHARP-RIG needs it at every bound below $`x_F^C`$ (m2).
- **Not proved.** (E): open. The referee names the exact gap: below the core of $`R_2^C`$, every relation that Carlson's clauses give in $`R_2^S`$ must hold there; below $`x_F^C`$ this is clause-2
  rigidity, the cases (N1) and (N2) excluded at every cap from $`L(\varepsilon+\omega^2)`$ on. $`\beta_0 \ge x_F^C`$: conjecture, now stated inside $`R_2^S`$; type F is not excluded. No counterexample can be searched for,
  since $`R_2^S`$ is not computable. Outline only: the frontier $`L(\varepsilon\cdot\omega)`$, then $`L(\varepsilon_{\Phi_\Omega+2})`$.

### 1.3 Native codes: general stage lemmas, tree units and pair-free objects

Notation as in [SHIFT8.md](SHIFT8.md) §2.3: $`\Omega' = \Omega_{\omega+1}`$. A stage $`T`$ is written by a term over labels (ordinals below $`\Omega_\omega`$); its multiple is $`\Omega_\omega\cdot T`$.

- **The ordinal side, general lemmas** (proved; the abstract cores of COVER and NAMES* checked in Lean). Three lemmas replace the lemmas of each stage of the rounds before. GOOD-CRIT: at
  every level above the largest level of the labels of $`T`$, $`T`$ is good exactly when every collapse reached in $`\Omega_\omega\cdot T`$ has its argument below $`\Omega_\omega\cdot T`$. COVER: for $`\beta \lt \Omega_{j+1}`$, at
  most $`\aleph_j`$ multiples $`\Omega_\omega\cdot T'`$, $`T' \lt T`$, cover the closure of $`\Omega_\omega\cdot T`$ below it. NAMES*: at every limit stage $`T`$,

```math
\psi_{\Omega_{j+1}}(\Omega_\omega\cdot T) = \sup\{\psi_{\Omega_{j+1}}(\Omega_\omega\cdot T') : T' \lt T,\ T' \text{ good at level } j\}.
```

  STEP is proved too. The referee: state one convention for "label-free" (m1); the decomposition term must be split into Cantor normal form summands (m2).
- **Not proved: STAGE$`^G`$** (blocking point B-1, probably repairable; repaired in §2.3). The general stage lemma, which joins these lemmas to the stage systems, uses a family that must be cofinal among all
  earlier stages. At the level of the labels of $`T`$ it is not: the referee gives a counterexample with an $`\varepsilon`$-number label of level 1. At higher levels it is not shown cofinal among the
  earlier stages that are not good there, which the earlier rounds got from explicit chains. Likely repair: a larger closure bound and a lemma BUMP (every earlier stage lies below an earlier
  stage whose multiple is in that closure). So PUSH$`^G`$, "the ordinal side is complete up to $`\theta_0`$" and the two bounds below are not proved.
- **Tree units and pair-free objects** (the hosting lemmas proved, the referee checked every hypothesis of R1 and every case of NEXT-HOST by hand; REGION and SHAPE proved by transfer). One unit
  for each hereditary position value and one code for each leaf value, both ordered by value; a fresh guest is copied by R1 at the next host unit above it. For the atoms above $`\Omega'`$ in the high
  parts (Veblen atoms over $`\Omega'`$ and collapses by $`\psi_{\Omega_{\omega+2}}`$): objects with several additive principal points and no pair (multiplicities 2 and 3); the next host position is an atom
  that can be copied (NEXT-HOST, by $`\varepsilon`$-closure); the $`\Omega'`$ unit gets a universal source without a pair above $`y`$. Every code keeps chain number 3. Minor: one copy must be placed above
  a given point (m3); one closure needs a point above the labels (m4).
- **Not proved: the bounds** (they rest on STAGE$`^G`$; now proved, §2.3). Natively, with $`\mathrm{CH}_4`$,

```math
\iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\varepsilon_{\Omega_{\omega+1}+1}) \quad\text{(Conjecture TREE)},\qquad \iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\Omega_{\omega+2}),
```

  and RED-TOWER with $`\mathrm{CH}_4`$ up to $`\psi_{\Omega_1}(\Omega_{\omega+2})`$. The proved native bound stays $`\iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\Omega'^2 + \psi'(\Omega'^2))`$ ([SHIFT8.md](SHIFT8.md) §2.3). Giving each object its own pair also works,
  with chain number 4, so $`\mathrm{CH}_5`$ (a remark).
- **Further** (not proved). Conjecture MULT$`^n`$: $`\iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\Omega_{\omega+n})`$ for every $`n`$, so RED-TOWER with $`\mathrm{CH}_4`$ up to $`\psi_{\Omega_1}(\Omega_{\omega\cdot 2})`$; a variant with stacked pairs and
  chain number $`n+3`$: outline; $`\Omega`$ units indexed by their argument codes: outline. Remark: past $`\Omega_{\omega\cdot 2+1}`$ the stage sets contain nested collapses of every depth (checked up to
  depth 4), so both schemes would need a top of unbounded depth. $`\theta_0`$ and "the first fan needs an inaccessible": open.

### 1.4 Status after the thirty-fifth round

Superseded by §2.4.

### 1.5 Checks of the thirty-fifth round

Each run was under 60 seconds; none is a proof.

- §1.1. The domain criterion on 900 normal-form indices with constants at the boundary, 0 mismatches; ARG-BOUND; the reading points at 7 bases; 71 targets; the chain of landmarks; three
  cofinal towers; Lean green, identical to Python. The referee: the domain criterion on 1,500 indices of an independent grammar, with nested $`\psi_{\Omega_2}`$, $`\psi_{\Omega_3}`$, $`\psi_{\Omega_4}`$ and iterated
  fixed-point controls, 0 mismatches and 0 failures of ARG-BOUND; $`\omega^{G_2} = G_2`$, so $`L(G_2)`$ is the right frontier; the order of the reading points at 7 bases; the author's runs and the Lean file
  rerun, identical.
- §1.2. Normal forms and the domain on 19 indices, 0 mismatches (3 controls correctly fail); 40 targets, all valid; the chain of landmarks increasing. The referee: the author's runs rerun,
  identical; the domain criterion on 359 indices at and past $`\varepsilon`$, 0 mismatches; 63 targets, all consistent; the chain of the region of $`L(\varepsilon)`$; a Lean file for it, green and identical to
  Python. $`R_2^S`$, $`R_2^C`$, reaches and the map $`f`$ cannot be computed.
- §1.3. Names on two seeds, 89 checks each, 0 failures (the referee's rerun identical); 14 patterns, chain numbers as expected; the Lean file green. Certificates (replayed): 5 of 5 forward toys
  found, 0 of 3 reverse. The referee: each toy tests one fresh object against one host object; the case of two objects of the same kind and every case with codes have no certificate (m5).

### 1.6 Open

Superseded by §2.6.

## 2. The thirty-sixth round

Three papers (2026-10), each refereed once: a paper on the reaches of the skeleton for every code below $`\Phi^{P'}`$ (§2.1), a paper on (E), $`\beta_0`$ and the reading through the gap
(§2.2), and a paper on native codes (§2.3). A result in this section has 1 review unless a count is given. The claim on $`[0, L(G(\Omega_1)\cdot\omega)]`$ is proved in the first two papers
independently, by two different readings of the gap of a restart, so the step from $`L(G_2)`$ to $`L(G(\Omega_1)\cdot\omega)`$ has **2 reviews**. The minor points of the reviews of §1.1 and §1.2 are applied
by the first two papers, and their referees checked each repair (**2 reviews**); the third paper applies those of §1.3 (its referee checked them). None of the papers uses Wilken, JSL 72 (2007),
Carlson, AML 38 (1999), or Wilken, AML 45 (2006) (the referees checked this). Papers cited: in §2.1 only through refereed stages; in §2.2 [C11] and Carlson 2009 (Def 5.3, Def 5.4, L.5.5,
L.5.7) as in §1.2; no paper in a proved step of §2.3, which does not use FRAG. No Lean file was added: the ordinal inputs of §2.1 and §2.2 were checked with Lean files that only compare
terms (`#eval`, no theorem; green, identical to Python, and identical in the referees' reruns), and the abstract cores of the lemmas of §2.3 with a Lean file (green, only the standard axioms,
no `sorry`; the referee rechecked it); these count as checks. Levels and "given FRAG" are as in §1.

Notation (as in §1): $`\Phi^X`$ is the least fixed point of $`\alpha \mapsto \Gamma_\alpha`$ above $`X`$, so $`\Phi^{P'} = \psi_{\Omega_2}(\Omega_\omega\cdot 2 + \Omega_2)`$; $`\hat G = G(\Omega_2)`$; for a restart $`b = L(\lambda'')`$ of the skeleton,
$`b_1 = L(\lambda''+1)`$ and $`u_\xi = H(\eta_{\lambda''}+\xi)`$, the points of the gap of $`b`$.

### 2.1 The reaches of the skeleton for every code below $`\Phi^{P'}`$, and the claim up to $`L(\Omega_2+\Phi^{P'}\cdot\omega)`$, given FRAG

- **The repairs of the review of §1.1** (m1–m7; **2 reviews**). The skeleton inside a gap is restated block by block; the reading "$`n \ge 1`$" of m3 there is still wrong at $`n = 1`$, since $`\delta_j`$
  itself reaches only $`\delta_j`$, and PIN-R is proved again in the corrected form (not used for the frontier). The step "the same argument for every restart of the gap" (m4) is now an
  outline, replaced by FAR-PIN″ below. The upper half of RED-O″ is TOP-REG″ with the fixed set enlarged by a pin pattern (TOP-REG″⁺, m5). The rest are labels.
- **The domain of $`L`$ below $`\Phi^{P'}`$, and $`L(\Omega_2)`$** (PSI2$`^{P'}`$, ARG-BOUND$`^\Phi`$, DOM″$`^\Phi`$, EMPTY″, FIX″$`_2`$, DOWN″, COF″, TAIL″; proved). $`\psi_{\Omega_2}(\Omega_\omega\cdot 2+1+\beta) = \Gamma_{P'+1+\beta}`$ for
  $`\beta \lt \Phi^{P'}`$ (the $`\Gamma`$ tier above $`P'`$). The domain criterion of §1.1 holds for every normal form $`e \lt \Phi^{P'}`$ and for $`e \in [\Omega_2, \Omega_2+\Phi^{P'}\cdot\omega)`$. No $`e \in [\Phi^{P'}, \Omega_2)`$ is in
  the domain, so $`L(\Omega_2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2+\Omega_2)`$ is the supremum of the points $`L(e)`$ below it, and its code is $`\Phi^{P'}`$; above $`\Omega_2`$ the codes below $`\Phi^{P'}`$ come again.
- **The reading at a base of the skeleton** (THETA$`^b`$, THETA$`^\Gamma`$; proved by transfer, no FRAG). The reading THETA$`^\omega`$ of [SHIFT6.md](SHIFT6.md) §3, run at $`b`$, gives $`o_b(c)`$ inside the gap
  $`[b, b_1)`$ for every code $`c \lt P'`$: $`o_b(G_2) = u_{\omega^2}`$ (the first restart inside the gap), $`o_b(\hat G) = u_{\Omega_1}`$ (its first index fixed point), and the supremum is $`b_1`$. For $`c \in [P', \Phi^{P'})`$,
  $`o_b(c)`$ is the reading at the $`\upsilon`$-point $`b_1`$ of the code $`c`$ with $`P'`$ replaced by $`\Omega_1`$. The referee: for $`\lambda'' \lt \Omega_2`$ the codes with constants below $`b`$ end below $`\Phi^{P'}`$,
  so the reading is onto an initial segment only, and one equality of the transport fails at some tails; the inequalities that are used hold (m2).
- **The relative far pin** (L-PIN, FAR-PIN″, PIN-S at $`b_1`$; proved by transfer, given FRAG). A copy at $`b`$ sends $`L(\lambda''+n)`$ to a point $`L(e) \ge L(\mu''+n)`$, where $`L(\mu'')`$ is the image
  of $`b`$ (L-PIN). For every finite set of points of $`[b, \tau''_1)`$ a finite pin pattern makes the copy send each of them at least to its transport (FAR-PIN″): the relative pin of
  [SHIFT7.md](SHIFT7.md) §1.1, applied at the relative bases $`L(\lambda''+n)`$. The referee: proved at the root gap, which is all that the frontier uses; over several gaps the pattern must hold every
  $`L(\lambda''+i)`$, $`1 \le i \le \max n`$, not only the bases of the gaps met (m1); the relative bound should be $`b_1`$ (m3); an image restart that is a point $`L(e)`$ needs the other clauses written (m4);
  PIN-S needs its form with moved parameters (m5).
- **Theorems EXACT-O″$`^\omega`$ and EXACT-O″$`^\Gamma`$** (TOP-REG″⁺, RED-O″⁺, ATTAIN″; proved by transfer, given FRAG). For every restart $`b = L(\lambda'')`$ whose code $`c`$ is at most $`\Phi^{P'}`$:

```math
r(L(\lambda'')) = \delta''_1(\lambda'') + o_b(c).
```

  So every code in $`[G_2, P')`$ is short: its reading stays in the gap of $`b`$. Examples: $`r(L(G_2)) = \delta''_1 + u_{\omega^2}`$ at $`b = L(G_2)`$, and $`r(L(\Omega_2)) = \delta''_1 + \Phi^{L(\Omega_2+1)}`$.
- **Theorem C$`^\Phi`$ and the new frontier** (proved by transfer, given FRAG). Below $`L(\Omega_2+\Phi^{P'}\cdot\omega)`$, $`R_2^S`$ is skeletal for the skeleton of the points $`L(e)`$, every restart has an exact reach, and
  there is no fan apex and no triple nest. So $`\beta_0`$ and the least top of a triple nest in $`R_2^C`$ are above it, and **Wilken's claim holds in $`R_2^C`$ on $`[0, L(\Omega_2+\Phi^{P'}\cdot\omega)]`$**, both halves:

```math
L(\Omega_2+\Phi^{P'}\cdot\omega) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \Omega_2 + \omega^{\Phi^{P'}+1}),\qquad \Phi^{P'} = \psi_{\Omega_2}(\Omega_\omega\cdot 2 + \Omega_2).
```

  On the way, each with both halves: $`L(\varepsilon_{G_2+1})`$, $`L(\hat G)`$, $`L(G(\Omega_3))`$, $`L(P') = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'\cdot 2})`$, $`L(\varepsilon_{P'+1})`$, $`L(\Gamma_{P'+1}) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \psi_{\Omega_2}(\Omega_\omega\cdot 2+1))`$ and $`L(\Omega_2)`$.
- Other minor points (none changes a result): ATTAIN″ compares offsets read at different bases and should be stated by codes (m6); the author's checks missed the new bases
  $`L(\Omega_2)`$, $`L(\Omega_2+\Phi^{P'}\cdot k)`$, which the referee checked (m7).
- **Not proved.** FAR-PIN″ over several gaps as written (m1; not used). FAR-PIN″ with parameters in earlier gaps: outline. Conjecture TAU: the segment tier $`[\Omega_1, \psi_{\Omega_2}(\Omega_3))`$ carries over
  above $`P'`$ (checked), which would move the frontier to $`L(\psi_{\Omega_3}(\Omega_3))`$. Conjecture READ″: the code $`\psi_{\Omega_2}(\Omega_\omega\cdot 2 + \psi_{\Omega_3}(\Omega_\omega\cdot 2)\cdot\zeta)`$ reads $`L(\lambda''+1+\zeta)`$; this supports the
  conjectured start of the long restarts in §1.1. Proved: if $`\lambda'' \le \theta_2`$, every code is at most $`\psi_{\Omega_2}(\Omega_\omega\cdot 2+\theta_2)`$, so long restarts need an uncountable $`\lambda''`$. Open: the window rule
  one step up, the long restarts and their landing calculus, the codes below $`P_3`$, and $`\nu_3`$. $`T_3 \le \nu_3`$ is not claimed. (Now proved: FAR-PIN″ over several gaps and with
  parameters in earlier gaps, TAU, and READ″ for $`\zeta \le \omega+1`$, §3.1.)

### 2.2 (E), the reading through the gap, and $`\beta_0`$

Words as in §1.2.

- **The repairs of the review of §1.2** (m1–m8; **2 reviews**). Only "$`f^{-1}(\alpha) \gt \alpha \Rightarrow \sigma_S \le \alpha`$" is kept, and the converse is false (a counterexample is given); SHARP-RIG is required at
  every bound below $`x_F^C`$; the sentence on closedness is a remark; citations and wording.
- **NO-GAP$`^\theta`$** (proved by transfer, given FRAG). $`[0, L(G_2)) \subseteq \mathrm{Core}(R_2^S)`$, with $`f`$ the identity there: the bound $`\beta_0 \gt L(G_2)`$ of §1.1 with a lemma of
  [SHIFT8.md](SHIFT8.md) §2.2 applied at the point $`L(G_2)`$.
- **The reading through the gap** (G-CONT, FIX-G, READ$`^{\mathrm{gap}}`$ by transfer; PIN-GAP, PIN-b, INDEX$`^{\mathrm{gap}}`$, H-RC$`^{\mathrm{gap}}`$ without FRAG, given the induction hypothesis; TOP-REG″$`^{\mathrm{gap}}`$ by
  transfer; all proved, every case of the pins checked by hand). $`G`$ is continuous on $`[0, \hat G]`$, and a code below $`G(\Omega_1)`$ whose countable constants lie below an $`\varepsilon`$-number $`z`$ is
  below $`G(z)`$ (G-CONT). $`o_b(G(\zeta)) = u_{1+\zeta}`$ for $`\zeta \lt b`$ and $`o_b(G(\Omega_1)) = u_b`$ (READ$`^{\mathrm{gap}}`$): the reading runs through the restarts $`u_{\omega^2\cdot k}`$, $`u_{\omega^3}`$, …, $`u_{\varepsilon_0}`$, … of
  the gap. A copy that sends $`b`$ to $`b' = L(\mu'')`$ sends each $`u_\xi`$ with a fixed countable $`\xi`$ at least to $`H(\eta_{\mu''}+\xi)`$, since no restart of the image between the image of the
  prefix and that point has the code of $`u_\xi`$ (PIN-GAP); the same for $`\xi = b`$ (PIN-b). $`L(G(\Omega_1))`$ is the least fixed point of $`\zeta \mapsto L(G(\zeta))`$ (FIX-G).
- **Theorems EXACT-O″$`^G`$ and EXACT-O″$`_{G(\Omega_1)}`$** (proved by transfer, given FRAG). Every restart with code $`c \lt G(\Omega_1)`$ has $`r = \delta''_1 + o_b(c)`$ (on $`[G_2, G(\Omega_1))`$ a second proof of
  §2.1), and the limit code $`G(\Omega_1)`$ gives $`r = \delta''_1 + u_b`$. So (Theorem C$`^{G1}`$) the claim holds in $`R_2^C`$ on $`[0, L(G(\Omega_1)\cdot\omega)]`$, $`\beta_0 \gt L(G(\Omega_1)\cdot\omega+\omega+1)`$, and
  **$`[0, L(G(\Omega_1)\cdot\omega)) \subseteq \mathrm{Core}(R_2^S)`$ with $`f`$ the identity there, so the claim holds in $`R_2^S`$ on $`[0, L(G(\Omega_1)\cdot\omega))`$**:

```math
L(G(\Omega_1)\cdot\omega) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+G(\Omega_1)+1}),\qquad G(\Omega_1) = \psi_{\Omega_2}(\Omega_\omega + \omega^{\theta_2+\Omega_1}).
```

  On the way: $`L(G_2+\omega^2)`$, $`L(G_2\cdot\omega)`$, $`L(G(\omega^3))`$, $`L(G(\varepsilon_0))`$, $`L(G(\Omega_1))`$. Codes in $`(G(\Omega_1), \hat G)`$: outline in this paper (§2.1 reads them in another way; the transport it needed is proved in §3.1). Minor: one
  bound needs $`\kappa_0`$ to be an $`\varepsilon`$-number, which can be chosen (m1); the reading for every countable $`\zeta`$ is a re-run of the earlier proof, not a citation of it (m6); the block facts must be
  cited in the form that holds at every countable stage (m7); one step needs "suppose $`b \le_1 y+1`$" (m8); one check label (m2).
- **Toward (E)** (proved; no FRAG except in the first). If (E) fails, then $`\sigma_S \ge L(G(\Omega_1)\cdot\omega)`$ and the extra left end is above $`L(G(\Omega_1)\cdot\omega+\omega+1)`$ (given FRAG). PERSIST:
  $`\Sigma_2`$ truths go up along $`\le_1`$, so in $`R_2^S`$ $`\le_2`$ respects $`\le_1`$; its use proves only that a refuting point lies in $`[\mathrm{lh}_S(\beta_0), \delta)`$, and the rest is a remark (m3). N2-SHAPE: a
  difference of shape (N2) looks like the counterexample of NO-GO (§1.2); one clause holds only for the sets that contain $`\gamma`$ with an $`S`$-successor (m4). FAN-BOTTOM: $`f(x_F^S) = x_F^C`$. F-SHAPE+: in
  a difference of type F the second branch of the fan of $`R_2^C`$ appears in $`R_2^S`$ only higher, at an $`S`$-successor $`f^{-1}(\beta_0) \gt \beta_0`$ (the paper says "the second"; m5).
- Remark NO-LIFT: reflecting the pair to copies below $`\alpha`$ gives copies that pass Carlson's tests only up to a fixed size; excluding (N1) this way needs the uniform finite-set test (one copy for
  all sizes at once), which is open. (Corrected in §3.2: $`\Sigma_2`$ reflection does not carry Carlson's clauses at all; the conclusion
  stands.)
- **Not proved.** (E): open. The referee's exact gap: clause-2 rigidity at every cap of a left end (N1′) and (N2′), for every $`b`$ from $`L(G(\Omega_1)\cdot\omega+\omega+1)`$ to $`\kappa_C`$; the first code that
  this paper does not read is $`G(\Omega_1)+1`$. $`\beta_0 \ge x_F^C`$: conjecture; it needs SHARP-RIG at every bound below $`x_F^C`$, so the codes above $`G(\Omega_1)`$, the long restarts and their landing calculus, the
  codes below $`P_3`$, $`\nu_3`$ and the long pairs below $`x_F`$. Type F is not excluded.

### 2.3 Native codes: the stage lemma repaired, and $`\Omega_{\omega+n}`$

Notation as in §1.3.

- **The repairs of the review of §1.3** (m1–m5; the referee checked them). "Label-free" now means generated, and the level of a stage counts every leaf below $`\Omega_\omega`$.
- **BUMP-CL** (proved, given the finiteness lemma of m1 below). For stages $`T' \lt T`$ and $`\beta`$ above every leaf of $`\Omega_\omega\cdot T`$, the closure $`\mathrm{Cl}(\Omega_\omega\cdot T, \beta)`$ has an element in
  $`[\Omega_\omega\cdot T', \Omega_\omega\cdot T)`$. The proof is an induction over the two readings with a stack of frames, one for each pair of collapses with the same index; the frames keep the bumped collapse
  strictly smaller. The referee checked every case and that the measure decreases. With it: the family of the stage lemma is cofinal among all earlier stages from the level of the labels on
  (at the referee's counterexample of §1.3 it contains the stages $`t_2+\lambda+n`$), the good stages are cofinal one level higher, and at successor stages the earlier stages have a largest one (SUCC).
- **STAGE$`^G`$, PUSH$`^G`$ and the ordinal side up to $`\theta_0`$** (proved by transfer). The blocking point B-1 of §1.3 is closed. So Conjecture TREE is now a theorem, and

```math
\iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\varepsilon_{\Omega_{\omega+1}+1}),\qquad \iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\Omega_{\omega+2})
```

  (proved by transfer).
- **MULT$`^n`$** (proved; REGION, SHAPE and IDX by transfer; the referee checked HIGH, NEXT-HOST, MERGED-LEX, DEPTH, SOURCE, SCOPE-SUP and UNIT-SUP case by case). For every $`n`$,
  $`\iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\Omega_{\omega+n})`$, so RED-TOWER with $`\mathrm{CH}_4`$ holds below $`\psi_{\Omega_1}(\Omega_{\omega\cdot 2})`$. The units have no pair: an inner scope inside every collapse object whose
  argument reaches its own $`\Omega`$, multiplicities ordered by level (Veblen 2, a collapse of level $`l`$ $`2l-1`$, $`\Omega_{\omega+l}`$ $`2l`$), and universal sources whose capacity is $`n`$ minus the depth of the
  scope. The depth is at most $`n-2`$, so one finite top hosts every unit, and every code keeps chain number 3.
- Minor points: that the reading of a value with uncountable leaves is a finite tree is used but not proved; the referee gives a short proof by the same frames (an infinite reading gives an
  infinite descending sequence) (m1); in SUCC the chain of inequalities is wrong, and the subterm cycle is the right argument (m2); citations (m3); one part of a fact is a remark (m4); the scope
  of the checks (m5, m6).
- **Further** (not proved). Past $`\Omega_{\omega\cdot 2}`$ the stage sets need unbounded levels and unbounded nesting (proved for the levels; checked up to depth 4 for the nesting), so this scheme
  stops there. Nested pairs cost one more link at every depth (codes of chain number 4, so $`\mathrm{CH}_5`$; checked on mock patterns); with units indexed by level: outline, and conjecture:
  RED-TOWER with $`\mathrm{CH}_5`$ up to $`\psi_{\Omega_1}(\Omega_{\Omega_1})`$. $`\theta_0`$ and "the first fan needs an inaccessible": open. (The nested-pair scheme is not
  proved and this conjecture is withdrawn, §3.3.)

### 2.4 Status after the thirty-sixth round

- Wilken's claim in $`R_2^C`$: both halves hold on $`[0, X_4]`$ without FRAG, and **on $`[0, L(\Omega_2+\Phi^{P'}\cdot\omega)]`$ given FRAG, with $`L(\Omega_2+\Phi^{P'}\cdot\omega) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \Omega_2 + \omega^{\Phi^{P'}+1})`$**
  ($`[0, X_{21}]`$ with 2 reviews; up to $`\nu_C = \nu_S = L(\omega+1)`$ with 1 review and an audit; from $`\nu_C`$ to $`L(\omega^2)`$ with 2 reviews; from $`L(\omega^2)`$ to $`L(\Omega_1\cdot\omega)`$ with 1 review; from
  $`L(\Omega_1\cdot\omega)`$ to $`Z^+`$ with 2 reviews; from $`Z^+`$ to $`L(\varepsilon_{\Phi_\Omega+1})`$ with 1 review; from there to $`L(\varepsilon_{\Phi_\Omega+1}+\omega^2)`$ with 2 reviews, §1.1, §1.2; from there to $`L(G_2)`$ with 1
  review, §1.1; from there to $`L(G(\Omega_1)\cdot\omega)`$ with 2 reviews, two proofs, §2.1, §2.2; from there to $`L(\Omega_2+\Phi^{P'}\cdot\omega)`$ with 1 review, §2.1).
- Wilken's claim in $`R_2^S`$: on $`[0, L(G(\Omega_1)\cdot\omega))`$ given FRAG (§2.2); without FRAG up to $`\upsilon_{\omega^3}`$.
- $`R_2^S`$ against $`R_2^C`$: the two agree on every relation with right end at most $`L(\Omega_2+\Phi^{P'}\cdot\omega)`$ (given FRAG); $`\beta_0 \ge \sigma_S`$, and $`\sigma_S`$ is additively principal, in $`[\rho(\beta_0), \beta_0]`$,
  and at least $`L(G(\Omega_1)\cdot\omega)`$ given FRAG; (E) is equivalent to "the two cores are equal", and does not follow from the hypotheses of [C11] with MIN and CC alone. $`\beta_0`$ is not located.
- Reaches (given FRAG): exact for every restart below $`L(\Omega_2+\Phi^{P'}\cdot\omega)`$.
- **LOW: false, given FRAG**; **LOW$`^\infty`$: true, given FRAG** (1 review each; no change). The steps PIN and LOW of Conjecture CORE-2: undecided (no change).
- The lower-bound program below $`\theta_0`$: native bounds $`\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\varepsilon_{\Omega_\omega+1})`$ (no change) and $`\iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\Omega_{\omega+n})`$ for every $`n`$ (§2.3), so RED-TOWER with
  $`\mathrm{CH}_4`$ below $`\psi_{\Omega_1}(\Omega_{\omega\cdot 2})`$ (1 review each). The step below SRO: no change (every $`n`$ on all 3,166 sample matrices; the general statement for all standard matrices below
  SRO is open).

### 2.5 Checks of the thirty-sixth round

Each run was under 60 seconds; none is a proof.

- §2.1. 33 runs, 0 mismatches: the domain, the order of the names, the transport maps (about 58,000 pairs) and the bounds on codes; Lean green, identical to Python. The referee: the domain
  criterion on 1,500 indices with nested $`\Gamma`$ atoms, 0 mismatches; 600 indices in $`[\Phi^{P'}, \Omega_2)`$, none in the domain; $`\beta \mapsto \psi_{\Omega_2}(\Omega_\omega\cdot 2+1+\beta)`$ keeps the order on 14,641 pairs; the cap
  bound at the new bases; the author's runs and the Lean file rerun, identical (one printed sample line differs only by the order of a set).
- §2.2. Six runs passed (the domain on 1,201 indices with 0 mismatches, the continuity of $`G`$, the gap points, 64 targets, the chain of landmarks, FIX-G); one test first stated the wrong property,
  and the corrected test passes; Lean green, identical to Python. The referee: the author's runs rerun, identical; G-CONT at its exact bound on 1,400 terms, offsets past $`b`$, FIX-G at the
  border and the arithmetic of PIN-GAP on 1,710 cases, no counterexample; the Lean file rerun, identical. $`R_2^S`$, $`R_2^C`$, reaches and $`f`$ cannot be computed.
- §2.3. The Lean file green (only the standard axioms, no `sorry`; the referee rechecked it); the frame algorithm on 2 seeds, 1,400 pairs, frames up to depth 4, 0 failures (a first version had a
  bug in the frame descent, and its fix also corrected one rule of the proof); names on 2 seeds, 0 failures; 26 patterns. The referee: the author's runs rerun, identical; the frame algorithm
  written again from the text, on 3 seeds, 7,143 pairs, 0 failures. Certificates (replayed): 4 of 4 forward toys found, 0 of 3 reverse. Frames of depth 2 or more occur only in one special
  family, the depth bound is reached only for $`n = 3`$, and the toys are single objects (m6).

### 2.6 Open

Superseded by §3.6.

## 3. The thirty-seventh round

Three papers (2026-10), each refereed once: a paper on the codes above $`\Phi^{P'}`$ through tier maps (§3.1), a paper on (E), the $`\Gamma`$ tier above $`P'`$ and the uniform test (§3.2), and a
paper on native codes (§3.3). A result in this section has 1 review unless a count is given. The step of the claim in $`R_2^C`$ from $`L(\Omega_2+\Phi^{P'}\cdot\omega)`$ to
$`L(\Omega_2\cdot(\omega+1)+\Phi^{P'}_{\omega+1}\cdot\omega+\omega^2)`$ is proved in the first two papers independently, by two different readings of the codes above $`\Phi^{P'}`$, so it has **2 reviews**. The minor
points of the reviews of §2.1, §2.2 and §2.3 are applied by the three papers, and their referees checked each repair (**2 reviews**). None of the papers uses Wilken, JSL 72 (2007), Carlson,
AML 38 (1999), or Wilken, AML 45 (2006) (the referees checked this). Papers cited: in §3.1 only through refereed stages; in §3.2 [C11] and Carlson 2009 as in §1.2, and Carlson–Wilken,
"Tracking chains of Σ₂-elementarity" [CW12b], https://www.sciencedirect.com/science/article/pii/S0168007211001199 (Prop 7.4, the criterion, and Thm 7.9 (b)), with the same criterion in
Wilken's "A glimpse of Σ₃-elementarity" (Prop 21.11); no paper in a proved step of §3.3, which does not use FRAG. No Lean file was added: the ordinal inputs of §3.1 and §3.2 were checked with
Lean files that only compare terms (`#eval`, no theorem; green, identical to Python, and identical in the referees' reruns), and the referee of §3.3 checked the four order cases of the lemma KEY
with a separate Lean file (green, only the standard axioms, no `sorry`); these count as checks. Levels and "given FRAG" are as in §1.

Notation (as in §2): $`\theta'_2 = \psi_{\Omega_3}(\Omega_\omega\cdot 2)`$ and $`G''(\zeta) = \psi_{\Omega_2}(\Omega_\omega\cdot 2 + \theta'_2\cdot\zeta)`$, so $`G''(0) = P'`$; $`\Phi^{P'}_\zeta = \psi_{\Omega_2}(\Omega_\omega\cdot 2 + \Omega_2\cdot\zeta)`$, the
$`\zeta`$-th fixed point of $`\alpha \mapsto \Gamma_\alpha`$ above $`P'`$ ($`\Phi^{P'}_0 = P'`$, $`\Phi^{P'}_1 = \Phi^{P'}`$); for a restart $`b = L(\lambda'')`$ of the skeleton, $`b_{1+n} = L(\lambda''+1+n)`$ for $`n \le \omega`$, so
$`b_{1+\omega} = \tau''_1`$.

### 3.1 The codes above $`\Phi^{P'}`$: tier maps, and the claim up to $`L(\theta'_2\cdot(\omega+1)+G''(\omega+1)\cdot\omega)`$, given FRAG

- **The repairs of the review of §2.1** (m1–m7; **2 reviews**). The pin pattern now holds every $`L(\lambda''+i)`$ (m1), and the relative bound is $`L(e+1)`$, resp. $`\delta''_1`$ (m3); both are built into
  FAR-PIN″ below. The truncation of the reading at $`\pi_{\eta_b}`$ is stated once and used throughout (m2); the image restarts that are points $`L(e)`$ are written out (m4); PIN-S is cited in its
  form with moved parameters (m5); ATTAIN″ is stated by codes (m6); the new bases are checked (m7).
- **The domain of $`L`$** (DOM″$`^K`$, TAIL″$`^K`$, COF″$`^{\mathrm{gen}}`$, T2-TARGET; proved). For every normal form $`e \lt \theta'_2\cdot(\omega+1) + G''(\omega+1)\cdot\omega`$: $`e`$ is in the domain of $`L`$ exactly
  when its countable constants are below $`L(e)`$ and every atom $`\psi_{\Omega_2}(\Omega_\omega\cdot 2+a')`$ of $`e`$ has $`a' \lt P'\cdot e`$. Every index fixed point in this range is a limit of the domain, and
  the targets that the lower bounds need exist for every code below the code. The referee: one sentence of the proof ("all arguments are at most $`\Omega_\omega\cdot 2`$") is false, with a
  counterexample, but both sides of the criterion agree there (m2).
- **FAR-PIN″ over several gaps and with parameters in earlier gaps** (proved by transfer, given FRAG). At every relative base the lower map is the transport restricted to the fixed set, which is
  the base of the relative pin of [SHIFT7.md](SHIFT7.md) §1.1. Then the base change at a gap either equals the transport or lies above its whole target gap, so no monotonicity in the lower map is
  needed. This proves the two forms of FAR-PIN″ that were not proved in §2.1. **TRANS-b** (proved): the FRAG″ transport of offsets that contain $`b`$ or points of its gap is already in the domain
  of the η-base change of TC⁺; this closes the outline of §2.2 for the codes in $`(G(\Omega_1), \hat G)`$.
- **The tier maps** (Lemmas VIS and TIER$`_n`$; proved, a syntactic statement about InaccPsi normal forms, through the comparison that Lean proves correct, `Term.cmp_eq_compare`). For $`n \le \omega+1`$
  let $`\mathrm{Tr}_n`$ send $`\Omega_1`$ to $`G''(n)`$, keep $`\Omega_k`$ ($`k \ge 2`$), $`+`$ and $`\varphi`$, send the constants through an order isomorphism onto codes below $`G''(n)`$, send $`\psi_{\Omega_k}(z)`$ to
  $`\psi_{\Omega_k}(\mathrm{Tr}_n(z))`$ for $`k \ge 3`$, and

```math
\psi_{\Omega_2}(h + t) \mapsto \psi_{\Omega_2}(\Omega_\omega\cdot 2 + \theta'_2\cdot n + 1 + \psi_{\Omega_3}(\mathrm{Tr}_n(h)) + \mathrm{Tr}_n(t)),
```

  where $`h`$ is the sum of the Cantor normal form summands $`\ge \Omega_3`$ of the argument and $`t \lt \Omega_3`$ the rest. Then $`\mathrm{Tr}_n`$ is an order isomorphism from the codes in $`[\Omega_1, P')`$ onto
  the codes in $`[G''(n), G''(n+1))`$, and it keeps normal forms. The referee checked every comparison clause and tested five tiers, $`n = 0, 1, 2, \omega, \omega+1`$ (the author tested two). Two
  cases settle the conjectures of §2.1 (**TAU** and **SEG$`^{P'}`$**, proved): $`\mathrm{Tr}_0`$ maps the codes in $`[\Omega_1, \psi_{\Omega_2}(\Omega_3))`$ onto those in
  $`[P', \psi_{\Omega_2}(\Omega_\omega\cdot 2+\psi_{\Omega_3}(\Omega_3)))`$, and the codes in $`[\Omega_1, \theta)`$ onto those in $`[P', \psi_{\Omega_2}(\Omega_\omega\cdot 2+\theta_2))`$.
- **READ″** (proved by transfer, no FRAG; Conjecture READ″ of §2.1 for $`\zeta \le \omega+1`$). At a restart $`b`$ of the skeleton, a code $`c \in [G''(n), G''(n+1))`$ reads as the code $`\mathrm{Tr}_n^{-1}(c)`$ read at the
  point $`b_{1+n}`$ (THETA$`^b`$ of §2.1 run there). So $`o_b(G''(n)) = L(\lambda''+1+n)`$, $`o_b(G''(\omega)) = \tau''_1`$, and the codes below $`G''(\omega+1)`$ read exactly the points below $`\delta''_1`$. The
  referee: the reading at every point $`L(e)`$ (TH-L) extends the cited result past its stated range; the extension is sound and is a transfer, not a citation (m4); one step needs every constant of
  the code to lie in the domain at the tails, which holds by DOM″$`^K`$ but is not written (m1); one value is a value of the map, not a supremum (m3).
- **Theorems EXACT-O″$`^R`$ and EXACT-O″$`_{G''(\omega+1)}`$** (TOP-REG″$`^{++}`$, RED-O″$`^R`$, ATTAIN″; proved by transfer, given FRAG). For every restart $`L(\lambda'')`$ of the skeleton whose code $`c`$ is at
  most $`G''(\omega+1)`$:

```math
r(L(\lambda'')) = \delta''_1(\lambda'') + o_b(c).
```

  Examples: $`r(L(\theta'_2\cdot k)) = \delta''_1 + L(\theta'_2\cdot k+k+1)`$, $`r(L(\theta_2)) = \delta''_1 + H(\eta_{\theta_2}+P'+1)`$, and at the limit code $`r(L(\theta'_2\cdot(\omega+1))) = \delta''_1\cdot 2`$. The referee: in
  TOP-REG″ the added points may now lie in $`[\tau''_1, \delta''_1)`$, so the reason given in §2.1 no longer applies; the conclusion holds by the block-top argument of an earlier lemma (m5).
- **Theorem C$`^R`$ and the new frontier** (proved by transfer, given FRAG). Below the frontier given below, $`R_2^S`$ is skeletal for the skeleton of the points $`L(e)`$, every restart has an exact reach, and there
  is no fan apex and no triple nest. So $`\beta_0`$ and the least top $`T_3^C`$ of a triple nest in $`R_2^C`$ are above it, and **Wilken's claim holds in $`R_2^C`$ on
  $`[0, L(\theta'_2\cdot(\omega+1)+G''(\omega+1)\cdot\omega)]`$**, both halves:

```math
L(\theta'_2\cdot(\omega+1)+G''(\omega+1)\cdot\omega) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+1} + \theta'_2 + \omega^{G''(\omega+1)+1}),\qquad G''(\omega+1) = \psi_{\Omega_2}(\Omega_\omega\cdot 2 + \theta'_2\cdot(\omega+1)).
```

  On the way, each with both halves: $`L(\psi_{\Omega_3}(\Omega_3)) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \psi_{\Omega_3}(\Omega_3))`$ (the target named in §2.1), $`L(\theta_2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \theta_2)`$,
  $`L(\theta'_2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \theta'_2)`$, $`L(\theta'_2\cdot\omega)`$ and $`L(\theta'_2\cdot(\omega+1))`$. The first code not covered is $`G''(\omega+1)+1`$, at the frontier itself. The Lean file checks
  only the chain of names (m6).
- **Not proved.** The codes from $`G''(\omega+1)`$ to $`G''(\omega+1)\cdot\omega`$: outline (the same proof at the base $`\delta''_1`$). Open: the window rule one step up (codes from $`G''(\omega+1)\cdot\omega`$ on),
  the blocks $`j \ge 1`$ of each region (an index lemma one step up is needed), the long restarts, which start at the code $`G''(\omega^2)`$ (it reads $`L(\lambda''+\omega^2)`$; the first long restart is
  $`L(\theta'_2\cdot\omega^2)`$, above the frontier), and their landing calculus, the codes below $`P_3`$, and $`\nu_3`$. Conjecture: an analogue of $`\mathrm{Tr}_n`$ one level up gives the reaches below $`\nu_3`$.

### 3.2 (E), the $`\Gamma`$ tier above $`P'`$, and the uniform test

Words as in §1.2 and §2.2.

- **The repairs of the review of §2.2** (m1–m8; **2 reviews**). $`\kappa_0`$ is taken to be an $`\varepsilon`$-number (one exists below $`b`$); the use of PERSIST is restated (a refuting point lies in
  $`[\mathrm{lh}_S(\beta_0), \delta)`$); the step of m8 now assumes $`b \le_1 y+1`$ first; the rest are labels and citations.
- **NO-GAP$`^\Phi`$** (proved by transfer, given FRAG). $`[0, L(\Omega_2+\Phi^{P'}\cdot\omega)) \subseteq \mathrm{Core}(R_2^S)`$ with $`f`$ the identity there, so the claim holds in $`R_2^S`$ on that segment. The
  reach of that point, whose code $`\Phi^{P'}+1`$ is a successor, is $`\delta''_1 + \Phi^{b_1} + 1`$ (the referee checked the $`+1`$ step by step), and $`\beta_0`$ is above the region of that point. One
  step cites a later section where only the monotonicity of $`\psi_{\Omega_2}`$ is needed (m6).
- **The $`\Gamma`$ tier above $`P'`$** (PSI2$`^{P'}_\zeta`$, ARG-BOUND$`^*`$, DOM″$`^*`$, EMPTY″$`_\zeta`$, FIX″$`_{2,\zeta}`$, THETA$`^{G*}`$; proved, the readings by transfer). For $`\zeta \le \omega`$ and $`\beta \lt \Phi^{P'}_{\zeta+1}`$:
  $`\psi_{\Omega_2}(\Omega_\omega\cdot 2 + \Omega_2\cdot\zeta + 1 + \beta) = \Gamma_{\Phi^{P'}_\zeta+1+\beta}`$. No index in $`[\Omega_2\cdot\zeta + \Phi^{P'}_{\zeta+1}, \Omega_2\cdot(\zeta+1))`$ is in the domain of $`L`$, and
  $`L(\Omega_2\cdot(\zeta+1)) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \Omega_2\cdot(\zeta+1))`$ has code $`\Phi^{P'}_{\zeta+1}`$. The map of §2.1 that replaces $`P'`$ by $`\Omega_1`$ in a code is an order isomorphism here too,
  and gives the reading at $`b_1`$. The referee: at $`\zeta = 0`$ the notation breaks ($`\Phi^{P'}_0 = P'`$ goes to $`\Omega_1`$, not to $`\psi_{\Omega_2}(0)`$); no proof is affected (m4).
- **Theorems EXACT-O″$`^{G*}`$ and C$`^*`$** (proved by transfer, given FRAG). $`r(L(\lambda'')) = \delta''_1 + o_b(c)`$ for every code $`c \le \Phi^{P'}_{\omega+1}`$. So the claim holds in $`R_2^C`$ on $`[0, Z^\Gamma]`$, $`\beta_0 \gt Z^\Gamma`$,
  $`T_3^C \gt Z^\Gamma`$, and **$`[0, Z^\Gamma) \subseteq \mathrm{Core}(R_2^S)`$, so the claim holds in $`R_2^S`$ on $`[0, Z^\Gamma)`$**, where

```math
Z^\Gamma = L(\Omega_2\cdot(\omega+1)+\Phi^{P'}_{\omega+1}\cdot\omega+\omega^2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \Omega_2\cdot(\omega+1) + \omega^{\Phi^{P'}_{\omega+1}+1} + \omega^{P'+2}),\qquad \Phi^{P'}_{\omega+1} = \psi_{\Omega_2}(\Omega_\omega\cdot 2+\Omega_2\cdot(\omega+1)).
```

  On the way: $`L(\Omega_2\cdot k) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \Omega_2\cdot k)`$, $`L(\Omega_2\cdot\omega)`$, $`L(\Omega_2\cdot(\omega+1))`$. This point $`Z^\Gamma`$ is below $`L(\theta'_2)`$ of §3.1, so in $`R_2^C`$ the step from
  $`L(\Omega_2+\Phi^{P'}\cdot\omega)`$ to $`Z^\Gamma`$ has two proofs. The Lean file does not cover $`Z^\Gamma`$; it is checked in Python only (m3; now covered, [SHIFT10.md](SHIFT10.md) §1.2).
- **The uniform test.** (a) The remark NO-LIFT of §2.2 is corrected (proved by a counterexample): $`\Sigma_2`$ reflection carries the quantifier-free diagram and the $`\Pi_1`$ type of the pair, not
  Carlson's clauses, because bounded formulas are not free in this $`\Sigma_n`$ hierarchy; in $`(\mathrm{Ord}; \lt)`$, $`\omega \le_1 \omega\cdot 2`$, but "some $`v \gt 5`$ is a limit" holds below $`\omega\cdot 2`$ and not
  below $`\omega`$. Its premise is withdrawn; its conclusion stands. (b) If the criterion of [CW12b] Prop 7.4 (one copy for all extensions) held at every $`\lt_2`$-pair of $`R_2^C`$ below $`\kappa_C`$,
  then (E) would follow (proved; the local form needs $`b \lt \kappa_C`$, m2). The referee: this restates an earlier result in general form, and with (d) it is a reformulation of (E), not a step
  toward it (m5); it is not counted. (c) LOAD$`^*`$: the criterion holds at every pair with right end at most $`Z^\Gamma`$ (proved from the cited pair proofs, with one citation corrected, m7). (d) In
  $`R_2^S`$ the uniform test cannot give (E): at the first difference the pair is not a pair of $`R_2^S`$ (proved).
- **Type F** (proved). F-REDUCE: if $`d`$ is the largest $`\le_1`$-predecessor of $`\beta_0`$ and $`d \le_2^C \beta_0`$, then $`(d, \beta_0)`$ is itself an extra pair, of type N. The referee: above $`x_F^C`$ this pair can
  be of a third subtype (N0), in which $`d`$ is itself a fan apex of $`R_2^C`$, so "only pure fans remain" is false as written; what remains above $`x_F^C`$ is pure fans and (N0) (m1). F-CRIT-LOW: at
  a fan pair the criterion holds for every set below $`d`$ once it holds at $`(\alpha, d)`$; only the sets that meet $`[d, \beta_0)`$ remain.
- Other minor points: $`\nu_3`$ as a point of $`R_2^C`$ is a conjecture, so the chain of bounds should use $`T_3^C`$ (m8); one check label (m9).
- **Not proved.** (E): open; the exact gap is clause-2 rigidity at every cap from $`Z^\Gamma`$ on. The uniform test (T2U, LIFT$`_n`$) as a general argument: open. Type F at $`x_F^C`$: open; $`\beta_0 \ge x_F^C`$:
  conjecture. The induction along $`\zeta`$ up to the first fixed point of $`\zeta \mapsto L(\Omega_2\cdot\zeta)`$: outline.

### 3.3 Native codes: finite readings, index-coded levels, and where the nested pairs stop

Notation as in §1.3.

- **The repairs of the review of §2.3** (m1–m6; the referee checked them). FIN-READ (proved): the reading of every value $`z`$ with $`\Omega_\omega \le z \lt \psi_{I_0}(0)`$ in a closure is a finite tree (by the
  frames of §2.3; the referee checked every case). SUCC is proved again by the subterm cycle; one citation there assumed what is proved and is replaced (m1). NESTS (proved): for every $`d`$ a
  stage with scope depth $`d`$ exists below $`\Omega_{\omega\cdot 2}`$, so every stage set from $`\Omega_{\omega\cdot 2}`$ on has every depth.
- **Index-coded levels** (KEY, HIGH$`^G`$, NEXT-HOST$`^G`$, MERGED-LEX$`^G`$, UNIV-P, NO-END; proved). KEY: the atoms in $`(\Omega_\omega, \psi_{I_0}(0))`$ are ordered by index, then kind, then argument.
  Objects carry an index marker $`u \le_1 u + (\text{the index})`$ instead of a multiplicity, and the host lemmas hold for every index, towers of $`\Omega`$ included. UNIV-P: one pair source hosts every
  index-coded scope, at any depth and index, siblings that refer to each other included (one list in the proof should name the partial sums, m4). NO-END: in a merge of two scopes of the same key
  every fresh position has a host position above it.
- **What is hosted** (proved for layout A only). With the codes inside the unit pair and the objects above it (layout A): guests of smaller key, the top, and the merges of the same key without the
  case F1 below. **Blocking point B-1** (layout B, with the objects and the pair source inside the unit pair): a fresh code larger than every host code can be placed only by the general rule, which
  gives a copy below the right end of the pair but not below a chosen point, so it may land above the host objects; then the placement of UNIV-P and the order "codes below every object" fail.
  So the paper's claims "the chain number is not the obstruction" and "chain number 4 with layout B" are not proved; layout A needs the chain number 5.
- **F1 and the depth** (open, remark). The open case F1: a fresh collapse with a non-empty inner scope whose next host has a larger key; its inner scope must be copied inside that host's object.
  Remark: hosts whose strength is a well-founded capacity give only bounded depth, while every stage set past $`\Omega_{\omega\cdot 2}`$ has every depth. So the nested-pair scheme of §2.3 is not proved,
  and its conjecture (chain number 5 up to $`\psi_{\Omega_1}(\Omega_{\Omega_1})`$) is withdrawn. The paper's conditional result through a hosting hypothesis F1$`^\infty`$ is void: the referee shows by
  isominimality that F1$`^\infty`$ is false for every finite configuration, and for fixed shapes the remark on capacity is then a theorem (m3). The sentence "the stage route stops at
  $`\psi_{\Omega_1}(\Omega_{\omega\cdot 2})`$ for every chain number" rests on that remark only (m6); one "analysis" is a remark (m2).
- **Native bounds.** No new bound, and none is lost: $`\iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\Omega_{\omega\cdot 2})`$, so $`\iota(\mathrm{CH}_5)`$ and $`m_F`$ are above $`\psi_{\Omega_1}(\Omega_{\omega\cdot 2})`$. $`\theta_0`$, the tower of
  $`\Omega`$'s and "the first fan needs an inaccessible": open.

### 3.4 Status after the thirty-seventh round

Superseded by [SHIFT10.md](SHIFT10.md) §3.4.

- Wilken's claim in $`R_2^C`$: both halves hold on $`[0, X_4]`$ without FRAG, and **on $`[0, L(\theta'_2\cdot(\omega+1)+G''(\omega+1)\cdot\omega)]`$ given FRAG, with
  $`L(\theta'_2\cdot(\omega+1)+G''(\omega+1)\cdot\omega) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+1} + \theta'_2 + \omega^{G''(\omega+1)+1})`$** (the review counts up to $`L(\Omega_2+\Phi^{P'}\cdot\omega)`$ as in §2.4;
  from there to $`Z^\Gamma = L(\Omega_2\cdot(\omega+1)+\Phi^{P'}_{\omega+1}\cdot\omega+\omega^2)`$ with 2 reviews, two proofs, §3.1, §3.2; from $`Z^\Gamma`$ to the frontier with 1 review, §3.1).
- Wilken's claim in $`R_2^S`$: on $`[0, Z^\Gamma)`$ given FRAG (§3.2); without FRAG up to $`\upsilon_{\omega^3}`$.
- $`R_2^S`$ against $`R_2^C`$: the two agree on every relation with right end at most the frontier (given FRAG); $`\beta_0 \ge \sigma_S`$, and $`\sigma_S \ge Z^\Gamma`$ given FRAG; the criterion of [CW12b]
  holds at every pair with right end at most $`Z^\Gamma`$; (E) is open, and $`\beta_0`$ is not located.
- Reaches (given FRAG): exact for every restart below the frontier.
- **LOW: false, given FRAG**; **LOW$`^\infty`$: true, given FRAG** (1 review each; no change). The steps PIN and LOW of Conjecture CORE-2: undecided (no change).
- The lower-bound program below $`\theta_0`$: native bounds as in §2.4 (no change); the nested-pair scheme past $`\Omega_{\omega\cdot 2}`$ is not proved (B-1 and F1, §3.3). The step below SRO: no change
  (every $`n`$ on all 3,166 sample matrices; the general statement for all standard matrices below SRO is open).

### 3.5 Checks of the thirty-seventh round

Each run was under 60 seconds; none is a proof.

- §3.1. 18 runs: the tier maps for tiers 0 and 1 both ways (0 order and normal-form mismatches), the domain on 39,938 indices (0 mismatches), the targets of the lower bounds (165 of 165 found; a
  first search found 156 of 167, a limit of that search), the chain of names; Lean green, identical to Python. The referee: the tier maps both ways at tiers 0, 1, 2, $`\omega`$, $`\omega+1`$ with separate
  code (260 codes and 33,670 pairs per tier forward, 400 codes per tier backward, including absorbed atoms), 0 failures; the domain on 3,000 adversarial indices, 0 mismatches; 1,200 samples for m1,
  0 violations; the literal frontier and the chain of names; the author's runs and the Lean file rerun, identical.
- §3.2. 11 runs, no counterexample; Lean green, identical to Python. The referee: the domain on 26,299 tests (11,875 not in the domain), 0 mismatches; 480 samples of the empty intervals, none in the
  domain; 275 checks of the $`\Gamma`$ tier; the down map on 200 nested codes; the base chain at the last bases; the author's runs and the Lean file rerun, identical. $`R_2^S`$, $`R_2^C`$, reaches and $`f`$
  cannot be computed.
- §3.3. The nesting program on 2 seeds and 28 patterns, 0 failures. Certificates (replayed): 3 of 3 forward toys found, 0 of 2 reverse. The referee: the runs rerun, identical; KEY with separate
  code on 300 atoms per seed (89,700 ordered pairs, towers of $`\Omega`$'s and limit indices included), 0 violations; NESTS rebuilt from the text for $`d = 1, \dots, 6`$; the four order cases of KEY in
  Lean. The toys test layout A only (m5).

### 3.6 Open

Superseded by [SHIFT10.md](SHIFT10.md) §3.6.

- The claim above $`L(\theta'_2\cdot(\omega+1)+G''(\omega+1)\cdot\omega)`$ given FRAG (above $`X_4`$ without FRAG). Next: the codes from $`G''(\omega+1)`$ on (outline up to $`G''(\omega+1)\cdot\omega`$), the window rule one
  step up, the blocks $`j \ge 1`$, the long restarts from the code $`G''(\omega^2)`$ and their landing calculus, the codes below $`P_3`$, and $`\nu_3`$. In $`R_2^S`$: the claim above
  $`Z^\Gamma = L(\Omega_2\cdot(\omega+1)+\Phi^{P'}_{\omega+1}\cdot\omega+\omega^2)`$; $`o_k = \omega`$ for the levels above $`\nu`$ without FRAG.
- The crossing at $`m^*`$ across two levels as its own step with its audit row (minor m5 of [SHIFT8.md](SHIFT8.md) §1.2).
- $`R_2^S = R_2^C`$ above the frontier: (E), that is, clause-2 rigidity at every cap from $`Z^\Gamma`$ on (§3.2); the uniform finite-set test; and $`\beta_0`$ itself (conjecture: $`\beta_0 \ge x_F^C`$; type F is not
  excluded, and above $`x_F^C`$ the pure fans and the subtype (N0) remain); the converse for $`\le_1`$ at successor stages above $`\kappa_C`$.
- Bounds for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$, $`f_0`$, $`m_3`$, $`c_0`$, and an upper bound for $`\iota(\mathrm{CH}_3)`$.
- The first inaccessible: chain number 3 past $`\varepsilon_{\Omega_\omega+1}`$; past $`\Omega_{\omega\cdot 2}`$, the hosting case F1 and the placement of fresh codes in layout B (or codes in a separate pair, at the
  cost of one more link); then the tower of $`\Omega`$'s up to $`\theta_0`$; $`\mathrm{CH}_2`$ past $`\Theta_1`$; the step for all standard matrices below SRO.
- Names: $`R(\Theta_{d\omega})`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$; an InaccPsi formula for the reach in terms of the code; names above $`\nu`$ for the points that are not
  $`\upsilon`$-points; the rest of [COVER.md](COVER.md) §9.
