[← Back](README.md) | [English](SHIFT9.md) | [Japanese](SHIFT9-ja.md)

# $`R_2^+`$, the thirty-fifth round: the reaches of the skeleton up to $`L(G_2)`$, the first gap of $`\mathrm{Core}(R_2^S)`$, and the stage route toward $`\theta_0`$

This page continues [SHIFT8.md](SHIFT8.md) (§2 there is the thirty-fourth round); §1 is the thirty-fifth round. The status words are those of [README.md](README.md) §3: **proved** means that
an independent referee found the result proved with no fatal or blocking point. A statement with a blocking point against it is listed under **Not proved**.
A certificate counts only when it was replayed. A result that the referee calls only a restatement of something known is not counted as progress.

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
  should read "$`n \ge 1`$", and PIN-R uses a bound on the reach of the left ends that should be stated there (m3). The author's own slip of procedure (a stray directory change that failed and
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
- **Not proved: STAGE$`^G`$** (blocking point B-1, probably repairable). The general stage lemma, which joins these lemmas to the stage systems, uses a family that must be cofinal among all
  earlier stages. At the level of the labels of $`T`$ it is not: the referee gives a counterexample with an $`\varepsilon`$-number label of level 1. At higher levels it is not shown cofinal among the
  earlier stages that are not good there, which the earlier rounds got from explicit chains. Likely repair: a larger closure bound and a lemma BUMP (every earlier stage lies below an earlier
  stage whose multiple is in that closure). So PUSH$`^G`$, "the ordinal side is complete up to $`\theta_0`$" and the two bounds below are not proved.
- **Tree units and pair-free objects** (the hosting lemmas proved, the referee checked every hypothesis of R1 and every case of NEXT-HOST by hand; REGION and SHAPE proved by transfer). One unit
  for each hereditary position value and one code for each leaf value, both ordered by value; a fresh guest is copied by R1 at the next host unit above it. For the atoms above $`\Omega'`$ in the high
  parts (Veblen atoms over $`\Omega'`$ and collapses by $`\psi_{\Omega_{\omega+2}}`$): objects with several additive principal points and no pair (multiplicities 2 and 3); the next host position is an atom
  that can be copied (NEXT-HOST, by $`\varepsilon`$-closure); the $`\Omega'`$ unit gets a universal source without a pair above $`y`$. Every code keeps chain number 3. Minor: one copy must be placed above
  a given point (m3); one closure needs a point above the labels (m4).
- **Not proved: the bounds** (they rest on STAGE$`^G`$). Natively, with $`\mathrm{CH}_4`$,

```math
\iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\varepsilon_{\Omega_{\omega+1}+1}) \quad\text{(Conjecture TREE)},\qquad \iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\Omega_{\omega+2}),
```

  and RED-TOWER with $`\mathrm{CH}_4`$ up to $`\psi_{\Omega_1}(\Omega_{\omega+2})`$. The proved native bound stays $`\iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\Omega'^2 + \psi'(\Omega'^2))`$ ([SHIFT8.md](SHIFT8.md) §2.3). Giving each object its own pair also works,
  with chain number 4, so $`\mathrm{CH}_5`$ (a remark).
- **Further** (not proved). Conjecture MULT$`^n`$: $`\iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\Omega_{\omega+n})`$ for every $`n`$, so RED-TOWER with $`\mathrm{CH}_4`$ up to $`\psi_{\Omega_1}(\Omega_{\omega\cdot 2})`$; a variant with stacked pairs and
  chain number $`n+3`$: outline; $`\Omega`$ units indexed by their argument codes: outline. Remark: past $`\Omega_{\omega\cdot 2+1}`$ the stage sets contain nested collapses of every depth (checked up to
  depth 4), so both schemes would need a top of unbounded depth. $`\theta_0`$ and "the first fan needs an inaccessible": open.

### 1.4 Status after the thirty-fifth round

- Wilken's claim in $`R_2^C`$: both halves hold on $`[0, X_4]`$ without FRAG, and **on $`[0, L(G_2)]`$ given FRAG, with $`L(G_2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+G_2})`$** ($`[0, X_{21}]`$ with 2 reviews; up to
  $`\nu_C = \nu_S = L(\omega+1)`$ with 1 review and an audit; from $`\nu_C`$ to $`L(\omega^2)`$ with 2 reviews; from $`L(\omega^2)`$ to $`L(\Omega_1\cdot\omega)`$ with 1 review; from $`L(\Omega_1\cdot\omega)`$ to $`Z^+`$ with 2 reviews; from $`Z^+`$
  to $`L(\varepsilon_{\Phi_\Omega+1})`$ with 1 review, [SHIFT8.md](SHIFT8.md) §2; from $`L(\varepsilon_{\Phi_\Omega+1})`$ to $`L(\varepsilon_{\Phi_\Omega+1}+\omega^2)`$ with 2 reviews, two proofs, §1.1, §1.2; from there to $`L(G_2)`$ with 1 review, §1.1).
- Wilken's claim in $`R_2^S`$: on $`[0, L(\varepsilon_{\Phi_\Omega+1}+\omega^2))`$ given FRAG (§1.2); without FRAG up to $`\upsilon_{\omega^3}`$.
- $`R_2^S`$ against $`R_2^C`$: the two agree on every relation with right end at most $`L(G_2)`$ (given FRAG); $`\beta_0 \ge \sigma_S`$, and $`\sigma_S`$ is additively principal and in $`[\rho(\beta_0), \beta_0]`$; (E) is
  equivalent to "the two cores are equal", and does not follow from the hypotheses of [C11] with MIN and CC alone. $`\beta_0`$ is not located.
- Reaches (given FRAG): exact for every restart below $`L(G_2)`$.
- **LOW: false, given FRAG**; **LOW$`^\infty`$: true, given FRAG** (1 review each; no change). The steps PIN and LOW of Conjecture CORE-2: undecided (no change).
- The lower-bound program below $`\theta_0`$: native bounds $`\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\varepsilon_{\Omega_\omega+1})`$ and $`\iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\Omega_{\omega+1}^2 + \sigma_2)`$ (1 review each; no change: the bounds of
  §1.3 wait for STAGE$`^G`$). The step below SRO: no change (every $`n`$ on all 3,166 sample matrices; the general statement for all standard matrices below SRO is open).

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

- The claim above $`L(G_2)`$ given FRAG (above $`X_4`$ without FRAG). Next: the codes from $`G_2`$ on (the relative far pin through the whole gap, then the window rule one step up), the long
  restarts of the skeleton and their landing calculus, the codes below $`P_3`$, and $`\nu_3`$. In $`R_2^S`$: the claim above $`L(\varepsilon_{\Phi_\Omega+1}+\omega^2)`$; $`o_k = \omega`$ for the levels above $`\nu`$ without
  FRAG.
- The crossing at $`m^*`$ across two levels as its own step with its audit row (minor m5 of [SHIFT8.md](SHIFT8.md) §1.2).
- $`R_2^S = R_2^C`$ above $`L(G_2)`$: (E), that is, clause-2 rigidity at every cap below the core of $`R_2^C`$ (§1.2), and $`\beta_0`$ itself (conjecture: $`\beta_0 \ge x_F^C`$); the converse for $`\le_1`$ at
  successor stages above $`\kappa_C`$.
- Bounds for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$, $`f_0`$, $`m_3`$, $`c_0`$, and an upper bound for $`\iota(\mathrm{CH}_3)`$.
- The first inaccessible: chain number 3 past $`\varepsilon_{\Omega_\omega+1}`$; the lemma BUMP (the repair of B-1 of §1.3), which would give $`\iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\Omega_{\omega+2})`$; then MULT$`^n`$ up to $`\Omega_{\omega\cdot 2}`$,
  $`\Omega`$ units indexed by their argument codes, $`\Omega_{\Omega_1}`$ and the tower of $`\Omega`$'s up to $`\theta_0`$; $`\mathrm{CH}_2`$ past $`\Theta_1`$; the step for all standard matrices below SRO.
- Names: $`R(\Theta_{d\omega})`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$; an InaccPsi formula for the reach in terms of the code; names above $`\nu`$ for the points that are not
  $`\upsilon`$-points; the rest of [COVER.md](COVER.md) §9.
