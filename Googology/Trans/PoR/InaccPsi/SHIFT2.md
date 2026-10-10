[← Back](README.md) | [English](SHIFT2.md) | [Japanese](SHIFT2-ja.md)

# $`R_2^+`$, the eighteenth to twentieth rounds: $`\nu_C \ge X_9`$, $`X_{11}`$ and $`X_{12}`$ given FRAG, reaches across index fixed points, exact caps by order type, flat and nested codes, HOST$`_k`$, SYM-Q, GRN and MIN-EXACT

This page continues [SHIFT.md](SHIFT.md) (§9 there is the seventeenth round); §1 is the eighteenth round, §2 the nineteenth and §3 the twentieth. The twenty-first and twenty-second rounds are on [SHIFT3.md](SHIFT3.md), the twenty-third and twenty-fourth on [SHIFT4.md](SHIFT4.md), the twenty-fifth and twenty-sixth on [SHIFT5.md](SHIFT5.md), the twenty-seventh to twenty-ninth on [SHIFT6.md](SHIFT6.md), the thirtieth to thirty-second on [SHIFT7.md](SHIFT7.md), the thirty-third and thirty-fourth on [SHIFT8.md](SHIFT8.md), the thirty-fifth on [SHIFT9.md](SHIFT9.md). The status words are those of [README.md](README.md) §3: **proved** means that
an independent referee found the result proved with no fatal or blocking point. A statement with a blocking point against it is listed under **Not proved**.
A certificate counts only when it was replayed. A result that the referee calls only a restatement of something known is not counted as progress.

§1: four papers (2026-10), each refereed once, so a result in §1 has 1 review unless a count is given. **2 reviews** means that the referee of the
seventeenth round proposed the repair (or checked the result) and the referee of this round checked it again as written out. None of the papers uses
Wilken, JSL 72 (2007), Carlson, AML 38 (1999), Wilken, AML 45 (2006), or the equivalence that Carlson 2009, p. 97, announces. No Lean file was added:
one paper (§1) checked a Lean test file of named points with leanman (green, and green with the same output in the referee's rerun); it only compares
terms (`#eval`, no theorem), so it counts as a check. Levels are renumbered as in [SHIFT.md](SHIFT.md) (the papers' $`U^1`$ is $`U_2`$ here).

## 1. The eighteenth round

### 1.1 $`\nu_C \ge X_9`$ given FRAG; (P) and (Q′) still open

Notation of [SHIFT.md](SHIFT.md) §1, §8.1 and §9.1: $`H(\eta) = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$, $`G(\zeta) = \psi_{\Omega_2}(\Omega_\omega + \theta_2\cdot\zeta)`$, $`G_2 = G(\omega^2)`$, $`\upsilon_{\lambda+x}`$ is the $`\upsilon`$-point at
index distance $`x`$ from the restart $`\lambda`$. New: $`x`$ is an **index fixed point** of $`\lambda`$ if $`\upsilon_{\lambda+x} = x`$. $`\Gamma^{G_2}_\beta`$ is the $`\beta`$-th strongly critical ordinal above $`G_2`$,
and $`\Phi'`$ is the least $`\gamma \gt G_2`$ with $`\Gamma^{G_2}_\gamma = \gamma`$; then $`\Phi' = \psi_{\Omega_2}(\Omega_\omega + \omega^{\theta_2+2} + \Omega_2)`$.

- **The minor points of the seventeenth-round review are applied** (bookkeeping, proved): "$`Ta_i`$ countable" in FAR-PIN, the hypothesis $`\rho_\lambda \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$
  everywhere, the hypothesis of LONG-ALL, CEIL relabelled FRAG-free, the bound for $`r(L(n))`$ relabelled outline, and the clause of XA on $`\lt_2`$ for restarts
  (restarts below $`\nu_S`$ are not left ends). The obstruction point $`\delta_{\mu+\omega^2} + \rho_{\mu+\omega^2}`$ of [SHIFT.md](SHIFT.md) §9.1 is now passed (RL-UP-D below), as that referee expected.
- **OFF-INF** (proved, no FRAG). Let $`\rho_\lambda \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ and let $`x`$ be countable with no index fixed point $`x' \le x`$. Then $`\eta_\lambda + x \in D'`$ and
  $`\upsilon_{\lambda+x} = H(\eta_\lambda + x)`$. No $`x \lt \upsilon_{\lambda+\rho_\lambda}`$ is an index fixed point. This replaces OFF ($`z \lt \varepsilon_{N_\lambda+1}`$); the proof is a short induction on $`x`$.
- **MULTI-RC\*** (proved, given FRAG; now a full proof, not a transfer). H-RC over every region of $`\lambda`$ at an index distance below a fixed $`\varepsilon`$-number
  $`\kappa \lt \rho_\lambda`$: for every finite $`F`$ there is a finite pattern $`P^*(F)`$ such that every copy $`h`$ with $`h(\rho_\lambda) = \rho_\mu`$ has $`h(y) \ge T^*_\mu(y)`$ on $`F`$. Here $`T^*_\mu`$ fixes the
  ordinals below $`\kappa`$, sends $`\upsilon_{\lambda+\xi}`$ to $`\upsilon_{\mu+\xi}`$, and is a substitution on each segment. The proof uses PIN-IDX at the restarts, INDEX with moved lower
  points at the other $`\upsilon`$-points, and PIN-S with moved lower parameters on every segment. The referee: the second step is literally a copy of the kind INDEX
  needs, so INDEX applies as written; $`\rho_\lambda`$ should be listed in $`P^*(F)`$. Its case on the segment of $`N_\lambda = \rho_{\lambda+\omega^2}`$, the only case that $`X_8`$ uses, has **2 reviews**.
- **Codes below $`G(\Omega_1)`$** (proved, no FRAG). GCONT: $`G`$ is continuous, and $`[\theta, G(\Omega_1))`$ is the disjoint union of the intervals $`[G(\zeta), G(\zeta+1))`$, $`\zeta`$ countable.
  SLOW$`_\zeta`$ and SSTEP$`_\zeta`$ of [THETA.md](THETA.md) §9.1 hold for every $`\zeta \lt \Omega_2`$ with $`\zeta \lt G(\zeta)`$ (the referee checked line by line where $`\zeta`$ enters).
  PHI\*: the code map $`\Phi_\lambda`$ is defined on all codes $`m \lt G(\Omega_1)`$. The Veblen and $`\Gamma`$ tier, in closed form: $`\psi_{\Omega_2}(\Omega_\omega + \omega^{\theta_2+2} + \xi) = \Gamma^{G_2}_{-1+\xi}`$
  while $`-1+\xi \lt \Phi'`$, and $`= \Phi'`$ for $`\xi \in [\Phi', \Omega_2]`$ (PSI2-G, PSI2-G′), with COMP-G′, UNIF-G′, EXACT-GS and PHI$`^V`$.
- **Theorem R-CAP-FAR\*** (proved, given FRAG). Let $`\lambda`$ be a restart with $`\rho_\lambda \lt \min(\nu_S, \psi_{\Omega_1}(\Omega_\omega\cdot 2))`$ and $`G_2 \le m_\lambda \lt G(\Omega_1)`$, write $`m_\lambda = G_2\cdot D + m_0`$
  with $`m_0 \lt G_2`$, and let $`\nu`$ be the restart at index distance $`\omega^2\cdot\Phi_\lambda(D)`$. Then $`r(\lambda) \lt \rho_{\nu+\omega^2}`$ whenever $`\rho_{\nu+\omega^2} \le \nu_S`$. Three tiers: V
  ($`D \lt \Phi'`$) and S ($`D \lt G(\omega^2+1)`$) use MULTI-RC\* only on the segment of $`N_\lambda`$; the full tier ($`D \lt G(\Omega_1)`$) uses it on the regions up to index distance $`\zeta + 2`$.
  R-CAP-FAR of [SHIFT.md](SHIFT.md) §9.1 is the case $`D \lt \varepsilon_{G_2+1}`$, so **$`\nu_C \ge X_8`$ given FRAG now has 2 reviews**.
- **CEIL\*** (proved, no FRAG): a code $`m_u \ge G(\zeta)`$ forces $`\eta_u \ge \theta_2\cdot\zeta`$, and $`m_u \ge \Phi'`$ forces $`\eta_u \ge \theta_2\cdot\omega^2 + \Omega_2`$.
- **Theorem X9** (proved, given FRAG). The three tiers give

```math
\begin{aligned}
\nu_C \ge X_9^\Gamma &= \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \Omega_2 + \omega^{\Phi'+1} + \omega^{G_2+1}),\cr
\nu_C \ge X_9^S &= \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{\theta_2} + \omega^{G(\omega^2+1)+1} + \omega^{G_2+1}),\cr
\nu_C \ge X_9 &= \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+\Omega_1} + \omega^{G(\Omega_1)+1} + \omega^{G_2+1}),\qquad G(\Omega_1) = \psi_{\Omega_2}(\Omega_\omega + \omega^{\theta_2+\Omega_1}).
\end{aligned}
```

So **Wilken's claim holds in $`R_2^C`$ on $`[0, X_9]`$, both halves, given FRAG** (on $`[0, X_9^S]`$ for a reader who accepts MULTI-RC\* only on the segment of $`N_\lambda`$;
without FRAG the range stays $`[0, X_4]`$). Also $`\nu_S \ge X_9`$, and every pair with (P) and (Q) has $`b \ge X_9`$ (P-LOW).
The next step, moved index distances, is an outline; it would give the conjecture
$`\nu_C \ge X_{10} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+\Omega_2} + \omega^{\hat G+1} + \omega^{G_2+1})`$ with $`\hat G = \psi_{\Omega_2}(\Omega_\omega + \omega^{\theta_2+\Omega_2})`$ (only the name is checked).

- **Lower bounds across regions** (proved, given FRAG).
  LONG-RS\*\*: the reflection rule (L′) holds across every countable index distance, also when the index distance moves (the referee: apply FRAG2 to the
  finite set of the reflected points, not to the larger set of block tops and caps; the same wording is in LONG-RS of the seventeenth round).
  RL-UP-D: the lower bounds of RL-UP go on past $`\delta_{\mu+\omega^2} + \rho_{\mu+\omega^2}`$, up to $`\delta_{\mu+\omega^2} + \rho_{\mu+\omega^2}^2`$ with codes below $`G_2^2`$.
  Lemma C\*\*: a class of codes, closed under "a code is an index", with a map $`c_\mu`$ from the codes below $`G(\mathrm{Rz}(\zeta))`$ onto $`[0, \upsilon_{\mu+1+c_\mu(\zeta)})`$, for countable and for
  uncountable $`\zeta`$ (for example $`c_\mu(\Omega_1) = \rho_\mu`$); here $`\mathrm{Rz}`$ turns a code into an index exponent. RL-UNC: every such code $`m`$ has a restart $`\mu`$ with $`r(\mu) \ge \delta_\mu + c_\mu(m)`$.
  **CROSS**: $`m_\mu \ge G(\mathrm{Rz}(\zeta))`$ gives $`r(\mu) \ge \upsilon_{\mu+1+c_\mu(\zeta)}`$; for countable $`\zeta`$, $`m_\mu \ge G(\zeta)`$ gives $`r(\mu) \ge \rho_{\mu+\zeta}`$ (when $`\rho_{\mu+\zeta} \lt \nu_S`$; trivial for finite $`\zeta`$).
  This is the converse of the conjecture of [SHIFT.md](SHIFT.md) §9.1 ("crossing at index distance $`\zeta`$ needs $`m \ge G(\zeta)`$"); the conjecture itself stays open.
  **RL-2**: the codes of the second region are read relative to $`\mu + \omega^2`$ (the base $`G_2`$ is changed to $`\rho_{\mu+\omega^2}`$), and by CROSS a restart crosses the whole second
  region when $`m_\mu \ge G(\omega^2\cdot 2)`$. Both were open in [SHIFT.md](SHIFT.md) §9.1. Realizers now exist at index distance $`c_\mu(D)`$ for every code $`D`$, also $`D \ge \Omega_1`$ ($`D = \Omega_1`$ gives $`\rho_\mu`$).
  (The referee's minor points: the base $`\kappa`$ of the moved transport must lie above the parameters of the code; $`G(\Omega_1)`$ itself is not a code of this class.)
- **Q′-RED** (the referee: proved, but only a restatement of the proof of CPB-LOC; not counted as progress): given (P), (Q′) at $`(a, b)`$ gives $`a \lt_2 v`$ for some $`v \le b`$.
  So the route through (Q′) is not easier than finding such a pair directly.
- **Not proved** (the referee: blocking point against the leaf, not against a stated result): an InaccPsi upper bound for $`\nu_C`$; (P) and (Q′) at
  $`(L(\omega), L(\omega+1))`$. Every bound above concerns index distances below the first index fixed point, and $`L(\omega+1)`$ lies beyond it. Missing for (P):
  (V1) upper bounds for the reaches of the crossed restarts with exponent $`e \ge \Omega_1\cdot 2`$ and of the long crossed restarts (now only RL-UNC $`\le r \le`$ R-CAP-FAR\*);
  (V2) codes for index distances at or past an index fixed point. (Q′) needs an isominimal pattern of $`L(\omega)`$, which no tool computes.

### 1.2 Native codes: one flat row of $`\le_1`$-items, and $`\iota(\mathrm{CH}_2) \ge Z^+`$

Notation of [SHIFT.md](SHIFT.md) §9.2. $`Z_\Delta`$ is the least fixed point of $`\theta_\Delta`$. $`\vartheta^3`$ is the collapsing hierarchy of [SHIFT.md](SHIFT.md) §9.2 one level up (over $`\Omega_2`$, with indices
below $`\varepsilon_{\Omega_3+1}`$), $`\Psi = \vartheta^3_{\Omega_3\cdot\omega}(0)`$, and $`\Xi_2^+ = \vartheta_\Psi(0)`$.

- **The minor points of the seventeenth-round review are applied** ("15 of 23", the restated last clause of SHAPE-U, the split of one case of the
  host lemma, the remark on the variant with one more bottom element labelled outline). So the restated **SHAPE-U has 2 reviews**.
- **NEST-UN** (proved). For $`D \ge \Omega_2`$ every copy of an upper nest $`\mathrm{UN}(D)`$ already contains the block of the old top. This is why the upper nests of
  [SHIFT.md](SHIFT.md) §9.2 have no finite top: each level of a tower of exponents costs one nested reach. (The rest of the diagnosis is a remark.)
- **Flat codes** (proved). One merged row of $`\le_1`$-items above the pair: one item for each distinct term $`\Omega_2^E\cdot d`$ of the whole term tree (equal subterms share
  one item), sorted by value, each item $`h`$ with $`h \le_1 h + V_2(E) + q(d) \lt h\cdot 2`$. SHAPE-F, SUM-CMP, VAL, MAX-ITEM, LARGEST-EPS, and the comparison lemma **ROW2**: a code of $`D`$
  hosts the code of every $`D' \lt D`$, and each new item is made by R1 directly below the next item of the host (the referee checked every case). ATOM-HOST-F: the
  $`\vartheta`$-atoms host every code of a smaller ordinal. **TOP-HOST-2**: the block $`[r, x \lt_2 y, c \le_1 c\cdot 2]`$ hosts every flat code. PURE=HYBRID: the index system without
  $`\varphi`$-atoms has the same $`\theta_\Delta`$.
- **Theorem IDX-F** (proved). The module of $`\theta_{\Xi_2}(0)`$ is $`\mathrm{TOP2}(0) = [r, x \lt_2 y, c \le_1 c\cdot 2]`$, and $`\iota(\mathrm{CH}_2) \ge Z_{\Xi_2} \gt \theta_{\Xi_2}(0)`$.
- **The ternary system** (proved). $`\vartheta^3`$ has the properties of §9.2 one level up (CLUB3, NF3, T1-3, NO-HIGH-3, VEB3, $`\vartheta^3_{\Omega_3}(0) = \Gamma_{\Omega_2+1}`$). The terms below $`\Psi`$
  satisfy the conditions of §9.2, so $`\vartheta_D`$ is defined for $`D \le \Psi`$ and $`\theta_\Delta`$ for $`\Delta \le \Xi_2^+`$, and it agrees with the old one up to $`\Xi_2`$ (AGREE+). Natively, an
  $`\varepsilon`$-number $`\vartheta^3_{\Omega_3\cdot m+\alpha}(\beta)`$ below $`\Omega_3`$ is an atom block $`b \lt k`$ with $`k \le_1 k + b\cdot m + V_2(\alpha)`$ and $`b \le_1 k + b\cdot(m+1) + V_2(\beta)`$ inside the row; ROW2 covers
  these blocks, and TOP-HOST-B: the block $`[c \lt d, c \le_1 d\cdot 2, d \le_1 d\cdot 2]`$ hosts every code.
- **Theorem IDX-3** (proved). Natively,

```math
\iota(\mathrm{CH}_2) \ge Z^+ = Z_{\Xi_2^+} \gt \theta_{\Xi_2^+}(0) \gt Z_{\Xi_2} \gt \theta_{\Xi_2}(0).
```

- Conjectured names: $`\vartheta^3_{\Omega_3\cdot m+\alpha}(\beta)`$ is the ternary Veblen function over $`\Omega_2`$; $`\Psi`$ is the least ordinal above $`\Omega_2`$ closed under it with a finite first
  argument; $`Z^+ = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Xi_2^+ + \Omega_1})`$.
- The referee's minor points: the count is "28 of 28" (27 by one search, 1 by another); one subscript reads $`E_{(1+d)+1}`$; one case of the module lemma
  should cite NO-HIGH-R; TOP-HOST-2 also uses GEN and R1 at $`r`$; the blocks that conv prints have a different shape from these atom blocks.
- **Open**: $`\iota(\mathrm{CH}_2) \ge \theta_0`$. Next: indices $`\ge \Omega_3\cdot\omega`$ of $`\vartheta^3`$ (a block inside the reach of a block, and a comparison lemma for it; conv's prints suggest that
  such blocks stand for much more than $`\Omega_3\cdot m`$), then the levels $`\Omega_n`$ towards $`\Theta_1`$, then the structure at the level of $`\Omega`$ up to SRO.

### 1.3 The shapes of $`\Phi_3`$: 2,843 of 3,166

Notation of [SHIFT.md](SHIFT.md) §3, §8.3 and §9.3.

- **The blocking point of the seventeenth round is repaired** (proved, 2 reviews). The search program for GR+ is replaced by the referee's repaired version
  (with two minor fixes); the rerun proves all 107 matrices of M2–M5 (M2 63, M3 28, M4 14, M5 2) with the same maps as the referee's rerun. So the 7 matrices
  of M3 count now: $`2{,}690 + 7 = 2{,}697`$. The minor points are applied: the M3 example now describes the printed covering; $`|V(A[n])|`$ grows at a constant rate only from
  $`n = 3`$ on; SELF-CHAIN-C′ is stated for the empty set of extra points only.
- **SYM-Q**, a symbol with two parameters (REGION, KEY-C1, KEY-UP proved; BASE, HOOK, KEY-C2, SEQ-Q, PERIOD-I, BISIM and the meta-lemma accepted). For $`t = 1`$ the maps
  of the program go down through every level of the periodic part. An image chain is the image of one source chain level by level; its column word is
  periodic with a period that itself contains whole copies of the periodic part. The comparison has two jumps: inside two copies of the periodic part,
  and over whole periods of one image chain. All positions are affine in the level $`j`$ and a count $`k`$, and each decision is made on a whole polyhedral region of $`(j, k)`$.
- **FAM-Q, SHAPE-Q** (the nest family $`Q_k`$, whose reach ends at $`Q_k + Q_{k-2}`$, read as templates counted from the bottom, and its shape): **not proved as general
  theorems** (blocking point). The program does not check four conditions that the proofs need: an alias identity outside the checked region, a condition on
  the bottom members, monotonicity with a negative threshold, and the case of templates at several positions. The referee checked all four on the 146
  matrices that use these theorems: they do not occur, or (one alias identity) hold, checked symbolically. So the 146 count.
- **DER-Q, GR-UNIF** (accepted): GR+ with forced groups at two levels with the same slot rule carries over to every level.
- **Proved for every $`n`$**: 146 new matrices with $`t = 1`$ (III 111, I 16, SUM 17, ROOT 2).
- **M5** (13): new rewrites remove the old obstruction; all 13 then stop at a family of witnesses, one for each position of a run. Open.
- **The tally** (checked; $`2{,}843 = 2{,}697 + 146`$):

| class | matrices | proved for every $`n`$ | given a condition checked for small $`n`$ | $`t = 2`$, given a shape checked for small $`n`$ | open |
|---|---|---|---|---|---|
| I | 581 | 556 | 0 | 0 | 25 |
| SUM | 603 | 575 | 2 | 0 | 26 |
| ROOT | 635 | 624 | 0 | 0 | 11 |
| III | 1,347 | 1,088 | 0 | 24 | 235 |
| all | 3,166 | 2,843 | 2 | 24 | 297 |

- **Left** (323): $`t = 0`$: M5 13; $`t = 1`$: III 197, I 17, SUM 7, ROOT 10; $`t = 2`$: III 49, ROOT 1, I 8, SUM 21. Of the 197, 155 have a shape but no derivation was found
  (the search stopped at its limit, or found no covering; that none exists is not shown), and 42 have no shape yet.

### 1.4 $`\nu_C = \nu_S`$: the plan without the anchor copy

Notation of [SHIFT.md](SHIFT.md) §4, §8.4 and §9.4. A **span** is a pair $`(u, L)`$ where the top restart $`u`$ reaches into the region of a later restart $`L`$; it is **shallow** if the index
distance from $`u`$ to $`L`$ is below $`\rho_u`$, and **deep** otherwise. "Given FRAG" here is at the outline level of the earlier lemmas LT, HEAD-TAIL and REFL-ξ, as the referees
state it.

- **GAP-CE** (proved, given FRAG). There is a gap $`(x^\#, K)`$, $`K`$ a long restart, in which the tails are exactly $`[0, x + u_m]`$: every $`u_n`$, $`x`$ and $`u_m\cdot 2`$ is a tail, but $`x\cdot 2`$ is not.
  So the third case (W-res-3) of (E1) in [SHIFT.md](SHIFT.md) §9.4 is not a property of a gap. NO-LOC (proved, trivial): Carlson 2009, Def 5.3, clause 2, at $`x \lt_2 \nu`$ places
  configurations only cofinally below $`\nu`$, never inside a given gap. (The paper's conclusion that (W-res-3) cannot be proved for the ceiling of the anchor copy is only a remark.)
- **DOUBLE-FAR, ROOM-FAR, W-EQ-FAR** (proved, given FRAG). Cofinally below $`\nu`$ there are long restarts $`l'`$ with $`\mathrm{lh}(l') \ge \rho_{l'\cdot(k+1)}`$ for each $`k \lt \omega`$, and with $`\mathrm{lh}(l') \ge \rho_{l'\cdot\omega}`$.
  So far heads have room below $`\nu`$, and W-EQ holds for them. This repairs the blocking point of NEAR-BLOCK in [SHIFT.md](SHIFT.md) §9.4: its target exists, so **NEAR-BLOCK is proved**.
- **CAP-VIS, FREE-OFFSET** (proved, given FRAG, for restarts and skeleton points; for other points an outline). Index distances are seen in the structure only through
  the caps $`\delta + (-1 + \mathrm{logend}\,\varepsilon)`$ of the restarts. So a shallow span gets its target index distances by choice (the referee: this uses that the region restart is recorded; otherwise no atom sees the distance and it is free anyway), $`\eta'_i = \omega^N\cdot i + \omega^{1+l'_i}`$, and no map $`T`$ on the top
  ordinals is needed. This covers NEAR-BLOCK and the shallow far configurations (F1).
- **RE-PLACE** (proved, given FRAG, with the referee's two repairs). The reduction RED-TF needs only some map on the top points, not the anchor copy $`\mu`$. So every top point
  is placed in increasing order by its own rule: W-EQ under the ceiling $`\nu`$, FREE-OFFSET, the region skeleton, or the rule for points that are not $`\varepsilon`$-numbers. No ceiling
  is left, so (E1) in all three cases, the room failures and the shallow far configurations are no longer obstructions. (Outline: heads of a general form, HEAD-GEN, and the bookkeeping.)
  The repairs: small restarts are placed directly by KV0 and FRESH, and the rule for points that are not $`\varepsilon`$-numbers takes a larger exponent, because the paper's rule can map
  two points to one value.
- **Correction** (the referee; an error inherited from LT of the sixteenth round): W-EQ and HEAD-TAIL fail for the head $`h = \delta_1`$ and tail $`t = 1`$. The least restart that is a limit of
  restarts has reach $`\delta + 2`$, not $`\delta + 1`$; the proof applies TOP-REG⁺ at $`y = \delta_1`$, which TOP-REG⁺ excludes. Nothing else used this case; successor restarts (logend 2) are now placed
  by KV0 and FRESH.
- **DEEP-UNC** (proved): every span over a recorded long restart has an uncountable offset of the index exponent, so it is deep (the referee: the second claim is for
  the restarts of $`(u, L]`$; at $`u`$ itself the offset is 0).
- **Not proved**: $`\nu_C = \nu_S`$, and $`\nu_C \lt \nu_S`$. The paper's list of what is left (RES-ALL) is incomplete (blocking point). Its items: (D1) deep spans, with countable offset
  $`\ge \rho_u`$ (upper half by TOP-REG-FAR; lower half needs REFL-MOV, an outline) or uncountable offset (open; the same missing tool as for (P) in §1.1); (D2) spans whose reach has
  Cantor-normal-form terms in $`[u, L)`$; (D3) reaches inside the own region in $`[\delta_j\cdot\omega, \upsilon_{a+\omega j+2})`$, and zero tails; (D4) top points that are $`\varepsilon`$-numbers but not $`\upsilon`$-points,
  and two bookkeeping conditions; and (E4), sets that meet $`[x^\#, \nu)`$. Missing from the list: shallow spans whose far landing lies in $`[\delta^L_j\cdot\omega, \upsilon_{L+\omega j+2})`$, whose far head
  has a term that is not a $`\upsilon`$-point, or whose far reach has tail 0. The proposed ghost test P_NEST for the deep spans is ill-formed as written.

### 1.5 Status after the eighteenth round

The nineteenth and twentieth rounds changed this status; see §2.5, §3.5.

- Wilken's claim in $`R_2^C`$: both halves hold on $`[0, X_4]`$ without FRAG, and on $`[0, X_9]`$ given FRAG (on $`[0, X_9^S]`$ if MULTI-RC\* is accepted only on one segment); the core
  half holds on $`[0, \nu_C]`$. No InaccPsi upper bound for $`\nu_C`$: (P) and (Q′) at a named pair stay open.
- The lower-bound program below $`\theta_0`$: the step below SRO holds for every $`n`$ on 2,843 of the 3,166 sample matrices; natively $`\iota(\mathrm{CH}_2) \ge Z^+`$.
- Upper bounds: still none by an InaccPsi term for $`\iota(\mathrm{CH}_k)`$, $`m_F`$, $`x_F`$, $`C^*_3`$ or $`\nu_C`$.
- $`\nu_C = \nu_S`$: the copying plan no longer needs the anchor copy, so room under ceilings is no obstruction; left: deep spans, three kinds of shallow spans,
  (D2)–(D4) and (E4) of §1.4.

### 1.6 Checks of the eighteenth round

Each run was under 60 seconds; none is a proof.

- §1.1. The indices of $`X_9^\Gamma`$, $`X_9^S`$, $`X_9`$ are in $`D'`$, the names are normal forms, and $`X_8 \lt X_9^\Gamma \lt X_9^S \lt X_9 \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$: Python and Lean agree (the
  referee's Lean rerun is green with the same output). The maps at the bases $`G(\omega^2)`$, $`G(\omega^2+1)`$, $`G(\omega^3)`$, $`G(\Omega_1)`$; UNIF-G′ on 185,745 pairs. The referee: OFF-INF on 800 samples,
  PSI2-G on 7 values, GCONT on 600 random normal forms, CEIL\* and the name of $`X_9`$; no counterexample.
- §1.2. 26 blocks are patterns, RF, fan-free and L1p-free; the referee: 51 more (38 with the coefficient points inside the pair). Certificates, all replayed:
  28 of 28 in the predicted direction, 0 of 26 in the reverse direction; the referee: 8 of 8 forward, 0 of 8 reverse. "Not found" is weak evidence.
- §1.3. The shapes against the concrete build for 3 levels per class (266 of the 308 matrices of $`t = 1`$ class III); the repaired GR+ on $`\mathrm{conv}(A[n])`$ for $`n \le 7`$
  on all 107. The referee: all 377 matrices with $`t = 1`$ left after the seventeenth round, for three start values, with 0 differences; the 146 at four higher levels, 0 failures.
- §1.4. No run by the paper. The referee: the offset arithmetic of FREE-OFFSET on 584 cases (0 bad); the collision of the paper's rule and the case $`h = \delta_1`$, $`t = 1`$
  on a finite model.

### 1.7 Open

The nineteenth and twentieth rounds changed this list; the current list is §3.7.

- Upper bounds: (P) and (Q′) at one named pair for $`\nu_C`$; (P) needs upper bounds for reaches across an uncountable exponent and codes past the first index fixed
  point, (Q′) the isominimal patterns of $`L(\omega)`$; bounds for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$, $`f_0`$, $`m_3`$, $`c_0`$.
- The claim above $`X_9`$ given FRAG: moved index distances (outline; Conjecture $`X_{10}`$).
- The first inaccessible: $`H_m`$, through $`\iota(\mathrm{CH}_2) \ge \theta_0`$ (from $`Z^+`$ on: indices $`\ge \Omega_3\cdot\omega`$ of $`\vartheta^3`$, then the levels $`\Omega_n`$); UNIF-FS below SRO on the 323
  matrices of §1.3 (first the 155 of $`t = 1`$ class III with a shape, which seem to need a rule for batches over two levels).
- $`\nu_C = \nu_S`$: the residue of §1.4 with the three missing kinds of shallow spans; HEAD-GEN; REFL-MOV.
- Names: $`R(\Theta_{d\omega})`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$; the exact reaches of the long restarts (now between the lower bound RL-UNC and the upper
  bound R-CAP-FAR\*); names beyond $`X_9`$; the rest of [COVER.md](COVER.md) §9.

## 2. The nineteenth round

Four papers (2026-10), each refereed once, so a result in this section has 1 review unless a count is given. **2 reviews** means that the referee of
the eighteenth round checked the result (or proposed the repair) and the referee of this round checked it again as written out. None of the papers uses
Wilken, JSL 72 (2007), Carlson, AML 38 (1999), Wilken, AML 45 (2006), or the equivalence that Carlson 2009, p. 97, announces. No Lean file was added:
one paper (§2.1) again checked a Lean test file of named points with leanman (green, and green with the same output in the referee's rerun); it only
compares terms (`#eval`, no theorem), so it counts as a check. The minor points of the eighteenth-round reviews are applied, in §1 and below.

### 2.1 Past the first index fixed point: $`\nu_C \ge X_{11}`$ given FRAG; (P) still open

Notation of §1.1. $`\Phi_\Omega = \psi_{\Omega_2}(\Omega_2)`$ is the least fixed point of $`\alpha \mapsto \Gamma_\alpha`$ above $`\Omega_1`$, $`\Phi_2 = \psi_{\Omega_3}(\Omega_3)`$, $`\hat G = G(\Omega_2)`$ and $`\mathbb{G} = G(\Phi_2)`$.
For a restart $`\lambda`$, $`F_\lambda = H(\eta_\lambda + \Omega_1)`$. An **η-offset** of $`\eta \in D'`$ is an ordinal $`\xi \lt \theta`$ with $`\eta + \xi \in D'`$; every ordinal is written $`\xi = \xi_u + \xi_c`$
with $`\xi_u`$ a multiple of $`\Omega_1`$ and $`\xi_c`$ countable. A **multiplier** is a $`\zeta \lt \Phi_2`$ in its Veblen and $`\Gamma`$ normal form over $`\Omega_2`$; it is **normal** if its constants lie below $`G(\zeta)`$.

- **The minor points of the eighteenth-round review are applied** (bookkeeping, proved): FRAG2 on the finite set of reflected points in LONG-RS\*\*, the
  base $`\kappa`$ above the parameters of the code, $`\rho_{\mu+\zeta} \lt \nu_S`$ strictly in CROSS, $`\rho_\lambda`$ listed in $`P^*(F)`$, and the wording points (all listed in §1.1).
- **D′-UNC** (proved, no FRAG). For $`\eta \in D'`$ and a normal form $`\xi \lt \theta`$, also an uncountable one: $`\eta + \xi \in D'`$ iff the countable maximal subterms of $`\xi`$ lie below $`H(\eta + \xi)`$.
- **FIX, DICT** (proved, no FRAG). $`F_\lambda`$ is the first index fixed point of $`\lambda`$, and the countable η-offsets are exactly $`[0, F_\lambda)`$. The η-offset $`\xi_u + \xi_c`$ with $`\xi_u \gt 0`$
  has index distance $`H(\eta_\lambda + \xi_u) + \xi_c`$. So η-offsets name the index distances at and past every index fixed point: this is the tool (V2) of §1.1, for
  η-offsets below $`\Phi_\Omega`$. **T$`^U`$** (proved): a transport of η-offsets that moves the constants and keeps the uncountable part; it keeps the order, sums, logend and DICT.
- **Theorem EXACT-V** (proved; "$`\le`$" without FRAG, "$`\ge`$" given FRAG). Every restart $`\nu`$ with $`\rho_{\nu+\omega^2} \le \nu_S`$ and $`\tau_\nu = -1 + e_\nu \lt \Phi_\Omega`$ has
  $`r(\nu) = \delta_\nu + \Theta_\nu(\tau_\nu)`$, where $`\Theta_\nu(\tau)`$ is the Veblen and $`\Gamma`$ normal form of $`\tau`$ with $`\Omega_1`$ replaced by $`\rho_\nu`$. EXACT-C (countable $`e`$) and EXACT-W
  ($`e \in [\Omega_1, \Omega_1\cdot 2)`$) are cases; now the caps are exact also for $`e \in [\Omega_1\cdot 2, \Phi_\Omega)`$. This is the tool (V1) of §1.1 for the short crossed restarts.
- **FAR-PIN$`^U`$, MULTI-RC$`^U`$, TOP-REG-FAR$`^U`$** (proved, given FRAG): the pins, H-RC and the far upper-bound rule across every η-offset below $`\Phi_\Omega`$, uncountable ones
  included, with the transport T$`^U`$. (The referee: the finite pattern must also contain the closures of the constants of the η-offsets.)
- **Codes past the first index fixed point** (proved, no FRAG). PSI2-3: $`\psi_{\Omega_3}(\beta) = \Gamma_{\Omega_2+1+\beta}`$ for $`\beta \lt \Phi_2`$. GHAT: $`\hat G`$ is the least fixed point of $`G`$ (the name that §1.1
  conjectured). COVER: $`[\theta, \mathbb{G})`$ is the disjoint union of the intervals $`[G(\zeta), G(\zeta+1))`$ over the normal multipliers $`\zeta`$. SLOW and SSTEP hold at every normal
  multiplier. PHI$`^U`$: the code map $`\Phi_\lambda`$ is defined on all codes below $`\mathbb{G}`$; it reads the base $`G(\zeta)`$ as the $`\upsilon`$-point $`H(\eta_\lambda + 1 + R_\lambda(\zeta))`$ at an η-offset, which is
  uncountable when $`\zeta \ge \Omega_2`$. For example $`\Phi_\lambda(\hat G) = F_\lambda`$ and $`\Phi_\lambda(G(\Omega_2\cdot k)) = H(\eta_\lambda + \Omega_1\cdot k)`$. (The referee: one bound in the proof of GHAT is off; the conclusion holds.)
- **Theorem R-CAP$`^U`$** (proved, given FRAG): the upper bound of R-CAP-FAR\* for every restart with $`G_2 \le m_\lambda \lt \mathbb{G}`$. Its case $`m_\lambda \lt G(\Omega_1)`$ is R-CAP-FAR\*, which
  this referee derived again, so **$`\nu_C \ge X_9`$ given FRAG now has 2 reviews**.
- **Lower bounds** (proved, given FRAG). CROSS-F: $`m_\mu \ge \hat G`$ gives $`r(\mu) \ge F_\mu`$, the first reach across an uncountable η-offset. The codes for realizers (O$`^U`$, Lemma C$`^U`$, B-PAR$`^U`$),
  LONG-RS$`^U`$, RL-U and CROSS-U carry the realizers past $`F_\mu`$. (The referee: these three need the added hypothesis $`\rho_{R+\omega^2} \le \nu_S`$ for the restarts $`R`$ below the target, and a
  multiplier code needs its constants below its base; neither point touches CROSS-SHARP or X11.)
- **Theorem CROSS-SHARP** (proved, given FRAG). Let $`M`$ be a multiple of $`\Omega_2`$ with no constants, $`\Omega_2 \le M \le \Phi_2`$, and let $`M'`$ be $`M`$ with $`\Omega_2`$ replaced by $`\Omega_1`$ (read $`\Phi_\Omega`$
  at $`M = \Phi_2`$). For every restart $`\lambda`$ with $`\rho_\lambda \lt \min(\nu_S, \psi_{\Omega_1}(\Omega_\omega\cdot 2))`$ and $`H(\eta_\lambda + M') \le \nu_S`$: $`r(\lambda) \ge H(\eta_\lambda + M')`$ iff $`m_\lambda \ge G(M)`$.
  In particular $`\lambda`$ reaches its first index fixed point iff $`m_\lambda \ge \hat G`$. So the conjecture of [SHIFT.md](SHIFT.md) §9.1 holds, in both directions, at every index fixed point of this range.
- **CEIL$`^U`$** (proved, no FRAG): $`m_u \ge \mathbb{G}`$ gives $`\eta_u \ge \theta_2\cdot\Phi_2`$.
- **Theorem X11** (proved, given FRAG). With R-CAP$`^U`$, CEIL$`^U`$, CEIL\* and TAIL (no lower-bound lemma is used):

```math
\begin{aligned}
\nu_C \ge X_{10} &= \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+\Omega_2} + \omega^{\hat G+1} + \omega^{G_2+1}),\cr
\nu_C \ge X_{11} &= \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+\Phi_2} + \omega^{\mathbb{G}+1} + \omega^{G_2+1}),\qquad \mathbb{G} = \psi_{\Omega_2}(\Omega_\omega + \omega^{\theta_2+\Phi_2}),\quad \Phi_2 = \psi_{\Omega_3}(\Omega_3).
\end{aligned}
```

So the conjecture $`X_{10}`$ of §1.1 is proved, and **Wilken's claim holds in $`R_2^C`$ on $`[0, X_{11}]`$, both halves, given FRAG**. A reader who accepts PSI2-3 only at $`\beta = 0`$
gets $`[0, X_{11}^V]`$, where $`X_{11}^V`$ is $`X_{11}`$ with $`\Phi_2`$ replaced by $`\psi_{\Omega_3}(0)`$; $`X_{10} \lt X_{11}^V \lt X_{11}`$. Without FRAG the range stays $`[0, X_4]`$. Also (P-LOW$`^U`$) every
restart $`a`$ with (P) has $`e_a \ge \mathbb{G} + 1`$.

- **Labelled as open, correctly**: Conjecture EXACT-PHI (exact caps for $`\tau \in [\Phi_\Omega, G_2)`$; refuted in the twentieth round, §3.1); (D1b) of §2.4 for spans over short restarts with offset below $`\Phi_\Omega`$ (an outline).
- **Not proved** (the referee: blocking point against the leaf only): (P) and (Q′) at $`(L(\omega), L(\omega+1))`$ or at any named pair, and so an InaccPsi upper bound for $`\nu_C`$.
  Every new result is a lower bound for $`\nu_C`$, a cap for reaches with codes below $`\mathbb{G}`$, or a realizer. Missing: (V1′) exact caps for the crossed restarts with
  $`\tau \in [\Phi_\Omega, G_2)`$ and for the long crossed restarts (only CROSS-U $`\le r \le`$ R-CAP$`^U`$, and nothing for codes $`\ge \mathbb{G}`$); (V2′) η-offsets at or above $`\Phi_\Omega`$ (multipliers $`\ge \Phi_2`$).

### 2.2 Native codes: $`\iota(\mathrm{CH}_2) \ge Z_\omega`$

Notation of §1.2. For $`n \ge 2`$ the $`n`$-ary system has collapsing hierarchies $`\vartheta^2, \dots, \vartheta^n`$: $`\vartheta^j`$ is the hierarchy of [SHIFT.md](SHIFT.md) §9.2 moved up to the pair
$`(\Omega_{j-1}, \Omega_j)`$, and its indices are terms of the next level. $`P_j = \vartheta^j_{P_{j+1}}(0)`$ (downward from the top level), $`\Xi_n = P_2`$, and $`Z_n`$ is the least fixed point of $`\theta_{\Xi_n}`$.
For $`n = 2`$ this is $`\Xi_2`$ of §1.2.

- **The minor points of the eighteenth-round review** are remarks; they are applied in §1.2.
- **The $`n`$-ary system** (proved): the terms of each level, $`\vartheta^j`$ with CLUB-j, NF-j, DOM-j, T1-j, NO-HIGH-j and VEB-j. AGREE-n: the $`(n+1)`$-system extends the $`n`$-system,
  $`\Xi_n \lt \Xi_{n+1}`$ and $`Z_n \lt \theta_{\Xi_{n+1}}(0) \lt Z_{n+1}`$; also $`\Xi_2^+ \lt \Xi_3`$. (The referee: the two systems have the same $`\vartheta_D`$ and $`\theta_\Delta`$, but their sets of constants differ
  by finite ordinals, so "restriction" is too strong.)
- **Nested rows** (proved). Inside the block of each $`\varepsilon`$-number $`e = \vartheta^{j+1}_D(\beta)`$ below $`\Omega_j`$ there is a sorted row of $`\le_1`$-items for the index $`D`$, between $`b_e`$ and $`k_e`$,
  with $`k_e \le_1 k_e + V_{j+1}(D)`$ and $`b_e \le_1 k_e + V_{j+1}(D) + b_e + V_j(\beta)`$; an item $`h`$ for a term $`(E, c)`$ has $`h \le_1 h + V_{j+1}(E) + V_j(c)`$. This replaces the coefficient $`b\cdot m`$ of §1.2.
  SHAPE-N, SUM-CMP$`_j`$, the items of every level (VAL$`_j`$, MAX-ITEM$`_j`$, LARGEST-EPS$`_j`$), and the comparison lemma **ROW$`_j`$** for all levels at once: a new atom is built inside the
  block of the host atom by ROW$`_{j+1}`$, then by R1 at $`k_e`$, then moved below the head by R1 at $`b_e`$ (the referee checked every case). ATOM-HOST-N, TOP-MAKE$`_j`$ and
  **TOP-HOST$`_n`$**: the block $`\mathrm{TOP}_n`$, with points $`c_2 \lt \dots \lt c_n`$ and $`c_j \le_1 c_n\cdot 2`$ for every $`j`$, hosts every code of the $`n`$-ary system.
- **Theorem IDX-n** (proved). For every $`n \ge 2`$, natively,

```math
\iota(\mathrm{CH}_2) \ge Z_n \gt \theta_{\Xi_n}(0) \gt Z_{n-1},\qquad\text{so}\qquad \iota(\mathrm{CH}_2) \ge Z_\omega = \sup_n Z_n.
```

- Conjectured names: $`\sup_n \Xi_n = \theta`$, so $`Z_\omega = H(\theta) = \Theta_1`$.
- **Lemma V-COND** (proved, but it gives no route; the referee): a block of the shape that conv prints would host every $`\mathrm{TOP}_n`$ if pairs $`u \lt_2 w`$ with $`u \le_1 x`$ were
  cofinal below its left end $`x`$. But such a pair together with $`x \lt_2 y`$ is a copy of $`\mathrm{CH}_2`$ with point $`u`$, so it never exists below $`\iota(\mathrm{CH}_2)`$.
- The referee's other minor points: the constants of a level are defined by recursion on the value inside the level (an index can be larger than its atom);
  in ROW$`_j`$ only sums below $`b_e`$ may be added in the first step; $`\mathrm{TOP}_2, \dots, \mathrm{TOP}_5`$ have 7 to 10 nodes (the codes have 15 to 28).
- **Open** (TOP-ω): one finite pattern, RF, fan-free and without L1p, that hosts every $`\mathrm{TOP}_n`$ (the module of $`Z_\omega`$). conv prints the upper block of $`\mathrm{TOP}_n`$ as the matrix
  $`(0,0,0)(1,1,0)\dots(n-1,n-1,0)`$, and their limit $`(0,0,0)(1,1,1)`$ as a $`\le_2`$-pair, which above $`y`$ is the configuration L1p. Then $`\iota(\mathrm{CH}_2) \ge \theta_0`$ needs the region $`H(D)`$
  for $`D \gt \theta`$, and then the structure at the level of $`\Omega`$ up to SRO.

### 2.3 The shapes of $`\Phi_3`$: 3,050 of 3,166

Notation of §1.3.

- **The blocking point of the eighteenth round is repaired** (proved). The program now checks the four conditions itself: the alias identities outside the
  checked region, the condition on the bottom members, the two missing comparisons of the monotonicity, and Step 4 for each template. The referee read the code
  against the case split. All 146 matrices of §1.3 are proved again with these checks, so **FAM-Q and SHAPE-Q are proved as general theorems** (at the level of the
  program), and **the 146 have 2 reviews**. The tag comparison that the eighteenth-round referee questioned only misses caches: this referee logged all 47,944
  such calls on the 353 matrices with $`t = 1`$.
- **SHAPE-Q2** (proved): relations with a positive count shift and landing nodes, repeated explicit nodes, bottom instances inside a family, explicit nodes inside a
  family, and Step 4 for members that can be left ends of $`\le_2`$. 39 of the 42 matrices of §1.3 without a shape now have one.
- **Lemma GRN** (proved): GR+ with nested copies of any depth (copies made inside copies), with one reach rule for every depth. This is the rule for batches over
  two levels that §1.3 asked for; depth 3 occurs in 6 classes. (The referee: "the search is complete" holds only inside the slots that the program tries.)
- **DER-Q2, GR-UNIF2** (accepted, like GR-UNIF): slot rules with free top members, and units of members that share one batch.
- **Proved for every $`n`$**: 207 new matrices (III 177, I 15, SUM 7, ROOT 8). The referee ran the final program again on all 353 matrices with $`t = 1`$: all 353 proved. (The
  paper's outputs were made before the last change of the program, so the paper must cite this run.)
- **M5** (13): the family of witnesses is a binomial tree: the $`i`$-th witness has $`i`$ witnesses of its own (checked; the referee: recursively, with no node twice). The size of
  $`\mathrm{conv}(A[n])`$ grows like $`c_A\cdot 2^n`$ (the paper's single formula $`c\cdot 2^{n+1} + 7`$ holds for only 3 of the 13). No family of the present kind describes this. Open.
- **The tally** (checked; $`3{,}050 = 2{,}843 + 207`$):

| class | matrices | proved for every $`n`$ | given a condition checked for small $`n`$ | $`t = 2`$, given a shape checked for small $`n`$ | open |
|---|---|---|---|---|---|
| I | 581 | 571 | 0 | 0 | 10 |
| SUM | 603 | 582 | 1 | 0 | 20 |
| ROOT | 635 | 632 | 0 | 0 | 3 |
| III | 1,347 | 1,265 | 0 | 24 | 58 |
| all | 3,166 | 3,050 | 1 | 24 | 91 |

- **Left** (116): $`t = 0`$: M5 13; $`t = 1`$: 24 (III 20, I 2, ROOT 2; of the 20, 9 were proved by an earlier version of the program but not again within 60 seconds,
  3 have no shape, and 8 have a shape but no slot rule was found); $`t = 2`$: III 49, ROOT 1, I 8, SUM 21.

### 2.4 $`\nu_C = \nu_S`$: every span below the first index fixed point is placed

Notation of §1.4.

- **The blocking point of the eighteenth round is repaired** (proved, given FRAG). One placement rule replaces the list of cases. **MIN-EXACT**: if a TOP-REG theorem holds for
  a transport and $`M = \{a \in (c, \nu) : r(a) \ge y(a)\}`$ is not empty, the least $`a' \in M`$ has $`r(a') = y(a')`$ exactly (the lower bound because $`a' \in M`$, the upper bound because no smaller
  restart is in $`M`$, which is the hypothesis of TOP-REG). **SEGCL**: every reach is closed under the reaches of its components, so TOP-REG holds also on $`[\delta_j\cdot\omega, \upsilon_{a+\omega j+2})`$
  (TOP-REG$`^{\mathrm{seg}}`$, no FRAG). The three kinds of shallow spans missing from the list of §1.4 are instances. The minor points of the review are applied (among them the
  forced exponent rule and the case $`h = \delta_1`$, $`t = 1`$ of §1.4).
- **PHI-EXT, COMP, block maps** (proved): an increasing map on the $`\varepsilon`$-leaves of the hereditary closure extends in exactly one way to a map that keeps $`+`$ and $`\omega^x`$, and
  the transports of regions compose. So the bookkeeping conditions are closed, and **HEAD-GEN** (heads of a general form) is proved.
- **FAR-PIN$`^\iota`$, MULTI-RC$`^\iota`$, TOP-REG$`^\iota`$, SPAN-PLACE** (proved, given FRAG): the pins in index form, from the cap formula $`-1 + \mathrm{logend}`$ at every index that is not a fixed point
  (instead of EXACT-C); H-RC over every region of a span below the first index fixed point; and the far TOP-REG at every landing of such a span. So every span below
  the first index fixed point has an exact twisted target. This closes (D1a), (D2), (D3) and (D4) of §1.4.
- **REFL-MOV**: it holds only under the hypotheses of LONG-RS\*\*, and it is no longer needed (MIN-EXACT gives the lower half).
- **RE-PLACE\*, RES-ALL\*** (proved, given FRAG): if ET fails, every realization contains a deep span over an uncountable offset ((D1b)). So on the copying side **the only
  obstruction left is (D1b)**, next to (E4).
- **Not proved**: the reduction "$`\nu_C = \nu_S`$ follows from FRAG, a tool for (D1b) and (E4)" (blocking point; it is an outline). The tool must also give room for the targets
  of (D1b) past the η-offset $`\omega^{G_2}`$, a TOP-REG past the first index fixed point (the caps used below it stop there), and the bookkeeping of the transports past index
  fixed points, where the present induction is circular. $`\nu_C = \nu_S`$ and $`\nu_C \lt \nu_S`$: neither is proved; no ghost was found. The ghost test P_NEST for (D1b) is now
  well formed; it is open.
- The referee's other minor points: the $`\upsilon`$-fixed points are a proper subclass of the $`\varepsilon`$-numbers (only the inclusion is used); room below $`\omega^{G_2}`$ also needs the
  hypotheses of LONG-CLASS; two of the paper's finite checks test only the arithmetic.

### 2.5 Status after the nineteenth round

The twentieth round changed this status; see §3.5.

- Wilken's claim in $`R_2^C`$: both halves hold on $`[0, X_4]`$ without FRAG, and on $`[0, X_{11}]`$ given FRAG ($`[0, X_9]`$ with 2 reviews); the core half holds on $`[0, \nu_C]`$.
  No InaccPsi upper bound for $`\nu_C`$: (P) at a named pair stays open.
- The lower-bound program below $`\theta_0`$: the step below SRO holds for every $`n`$ on 3,050 of the 3,166 sample matrices; natively $`\iota(\mathrm{CH}_2) \ge Z_\omega`$.
- Upper bounds: still none by an InaccPsi term for $`\iota(\mathrm{CH}_k)`$, $`m_F`$, $`x_F`$, $`C^*_3`$ or $`\nu_C`$.
- $`\nu_C = \nu_S`$: every span below the first index fixed point is placed; left: the deep spans over an uncountable offset (D1b), and (E4).

### 2.6 Checks of the nineteenth round

Each run was under 60 seconds; none is a proof.

- §2.1. Names, normal forms, $`D'`$ and the order $`X_9 \lt X_{10} \lt X_{11}^V \lt X_{11} \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$: Python and Lean agree (the referee's Lean rerun is green with the same
  output). D′-UNC on 716 η-offsets with 0 disagreements (the 89 offsets outside $`D'`$ are no evidence); COVER on 530 top atoms with 0 violations. The referee: 500 random
  multipliers below $`\hat G`$, all normal; 56 η-offsets near the boundary of $`D'`$, 0 disagreements; the code maps at 5 new bases, about 231,000 pairs, 0 failures.
- §2.2. 18 blocks (14 codes and $`\mathrm{TOP}_2, \dots, \mathrm{TOP}_5`$) are patterns, RF, fan-free and without L1p. Certificates, all replayed: 20 of 20 in the predicted direction, 0 of 20 in the
  reverse direction. The referee: 11 more blocks with deeper nesting (up to a code of the 5-ary system), 0 failures; 9 of 11 forward found and replayed, 0 of 11 reverse.
- §2.3. The same slot pattern at two more levels for all 353 matrices with $`t = 1`$ (paper); the shape equals the concrete build at two further levels, 353 of 353 (referee).
  The sizes of M5 for $`n \le 7`$.
- §2.4. Children below the reach (1,586), closures (1,050), PHI-EXT (2,400 pairs), least multiples, and MIN-EXACT on a finite model (1,400): 0 violations. The referee: PHI-EXT
  in an encoding of their own (2,000 triples) and the arithmetic of the cap lemmas (1,687 cases): 0 violations.

### 2.7 Open

The twentieth round changed this list; the current list is §3.7.

- Upper bounds: (P) and (Q′) at one named pair for $`\nu_C`$; (P) needs (V1′) and (V2′) of §2.1, and (Q′) the isominimal patterns of $`L(\omega)`$; bounds for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$, $`f_0`$,
  $`m_3`$, $`c_0`$.
- The claim above $`X_{11}`$ given FRAG: η-offsets at or above $`\Phi_\Omega`$, and Conjecture EXACT-PHI.
- The first inaccessible: $`H_m`$, through $`\iota(\mathrm{CH}_2) \ge \theta_0`$ (from $`Z_\omega`$ on: one finite top for all $`\mathrm{TOP}_n`$, then the region $`H(D)`$ for $`D \gt \theta`$, then the levels of $`\Omega`$ up
  to SRO); UNIF-FS below SRO on the 116 matrices of §2.3 (M5 needs a family shaped like a tree).
- $`\nu_C = \nu_S`$: (D1b), which needs the same tools as (P) and room past $`\omega^{G_2}`$; (E4).
- Names: $`R(\Theta_{d\omega})`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$; the exact reaches of the long crossed restarts (between CROSS-U and R-CAP$`^U`$); names beyond
  $`X_{11}`$; the rest of [COVER.md](COVER.md) §9.

## 3. The twentieth round

Four papers (2026-10), each refereed once, so a result in this section has 1 review unless a count is given. **2 reviews** means that the referee of
the nineteenth round proposed the repair (or checked the result) and the referee of this round checked it again as written out. None of the papers uses
Wilken, JSL 72 (2007), Carlson, AML 38 (1999), Wilken, AML 45 (2006), or the equivalence that Carlson 2009, p. 97, announces. New papers cited here:
Carlson–Wilken, "Tracking chains of Σ₂-elementarity", APAL 163 (2012) ([link](https://www.sciencedirect.com/science/article/pii/S0168007211001199)), Wilken, "Pure patterns of order 2"
([arXiv:1608.08421](https://arxiv.org/abs/1608.08421)) and Wilken, "Tracking chains revisited" ([arXiv:1611.04348](https://arxiv.org/abs/1611.04348)). No Lean file was added: one paper (§3.1)
checked a Lean test file of named points with leanman, and one referee (§3.4) wrote a Lean file for two small lemmas (both green); they are counted as
checks. The minor points of the nineteenth-round reviews are applied, in §2 and below.

### 3.1 Exact caps by order type: EXACT-PHI is false, $`\nu_C \ge X_{12}`$ given FRAG; (P) still open

Notation of §2.1. $`\chi_0 = \Gamma`$ enumerates the strongly critical ordinals, and for $`d \gt 0`$, $`\chi_d`$ enumerates the common fixed points of all $`\chi_{d'}`$, $`d' \lt d`$
(the Veblen hierarchy over $`\Gamma`$). An ordinal $`\gamma`$ is **χ-critical** if it is in the range of every $`\chi_d`$, $`d \lt \gamma`$. $`\Phi^\chi_X`$ is the least χ-critical ordinal above $`X`$; $`\Phi^\chi_\Omega = \Phi^\chi_{\Omega_1}`$,
$`\Phi^\chi_2 = \Phi^\chi_{\Omega_2}`$ and $`\mathbb{G}^\chi = G(\Phi^\chi_2)`$. For a restart $`\nu`$, $`\mathrm{Dom}_\nu`$ is the set of normal-form values below $`\Omega_2`$ whose countable maximal
subterms are below $`\rho_\nu`$, and $`o_\nu(\tau)`$ is the order type of $`\mathrm{Dom}_\nu \cap \tau`$. $`\Phi^\rho`$ is the least fixed point of $`\alpha \mapsto \Gamma_\alpha`$ above $`\rho`$.

- **The minor points of the nineteenth-round review are applied** (proved, **2 reviews** for the repaired statements): LONG-RS$`^U`$, RL-U and CROSS-U get the hypothesis
  $`\rho_{R+\omega^2} \le \nu_S`$ for the crossed restarts $`R`$ (automatic when the target is an index fixed point, so CROSS-SHARP and X11 are unchanged); a multiplier code has its
  constants below its base; the bound in the proof of GHAT; the closures of the constants of the η-offsets in the finite pattern of MULTI-RC$`^U`$; EXACT-V is for $`e \lt \Phi_\Omega`$.
- **NO-PHI** (proved; it uses EXACT-V). **Conjecture EXACT-PHI of §2.1 ($`r(\nu) = \delta_\nu + \Phi_\nu(\tau_\nu)`$ with the code map $`\Phi_\nu`$ of §1.1) is false.** At a restart with $`\tau_\nu = \Gamma_{\Omega_1\cdot 2}`$ (inside
  the range of EXACT-V) the reach is $`\delta_\nu + \Gamma_{\rho\cdot 2}`$, below $`\delta_\nu + \Phi^\rho`$, while $`\Phi_\nu(\tau_\nu) \gt \Phi^\rho`$. At $`\tau_\nu = \Phi_\Omega`$ the reach is $`\delta_\nu + \Phi^\rho`$, again below
  $`\delta_\nu + \Phi_\nu(\tau_\nu)`$, and the continuity test that the paper of §2.1 proposed fails there. The cause: $`\Phi_\nu`$ goes through Wilken's embedding into his own terms,
  which is strictly increasing but not onto.
  (The referee: the two example restarts in the paper have $`\tau`$ one too large; correct examples exist, and the refutation does not depend on them; the correct examples are in [SHIFT3.md](SHIFT3.md) §1.1.)
- **BRACKET-O, RED-O** (proved). The lower bounds by realizers are at most $`o_\nu(\tau)`$, and $`o_\nu(\tau) \le \Phi_\nu(\tau)`$. A term language that is unique, the same over every
  base, and onto gives exact reaches $`r(\nu) = \delta_\nu + o_\nu(\tau_\nu)`$.
- **The Veblen hierarchy over $`\Gamma`$ on both sides** (proved; the referee re-derived the main lemmas by hand). Wilken's side: a strongly critical $`\alpha`$ in a segment of his system has
  level at least $`\Omega_1^2 + \Omega_1\cdot d`$ iff $`\alpha`$ is in the range of $`\chi_d`$, it is χ-critical iff its level is at least $`\Omega_1^2\cdot 2`$, every $`\upsilon`$-point is χ-critical, and his base
  change commutes with the χ-terms. InaccPsi side (PSI2-χ): for an admissible $`\beta = \beta^- + \Omega_2^v\cdot c \lt \Omega_2^{\Phi^\chi_\Omega}`$ (base-$`\Omega_2`$ Cantor normal form),
  $`\psi_{\Omega_2}(\beta)`$ is the $`c`$-th element of the range of $`\chi_v`$ above $`\psi_{\Omega_2}(\beta^-)`$ (above $`\Omega_1`$ if $`\beta^- = 0`$). So
  $`\Phi^\chi_\Omega = \psi_{\Omega_2}(\Omega_2^{\Omega_2})`$, and one level up $`\Phi^\chi_2 = \psi_{\Omega_3}(\Omega_3^{\Omega_3})`$.
- **Theorem EXACT-O** (proved; "$`\le`$" without FRAG, "$`\ge`$" given FRAG). Every restart $`\nu`$ with $`\rho_{\nu+\omega^2} \le \nu_S`$ and $`\tau_\nu \le \Phi^\chi_\Omega + 1`$ has
  $`r(\nu) = \delta_\nu + \Theta_\nu(\tau_\nu) = \delta_\nu + o_\nu(\tau_\nu)`$, where $`\Theta_\nu`$ reads the χ-term of $`\tau_\nu`$ at the base $`\rho_\nu`$. EXACT-V is the case $`\tau_\nu \lt \Phi_\Omega`$. For example
  $`\tau_\nu = \Phi_\Omega`$ gives $`\delta_\nu + \Phi^\rho`$. Conjecture: the same holds for $`\tau_\nu \lt G\cdot\omega`$.
- **Long restarts** (proved, given FRAG). Let $`m_\lambda = G_2\cdot D + m_0`$ with $`1 \le D \lt \Phi^\chi_\Omega`$, $`m_0 \lt G_2`$, and let $`\nu`$ be the restart at index distance $`\omega^2\cdot o_\lambda(D)`$.
  R-CAP$`^O`$ and LB bound $`r(\lambda)`$ inside the region of $`\nu`$, and **EXACT-LONG**: if $`m_0 \lt \Phi^\chi_\Omega`$, then $`r(\lambda) = r(\nu) + o_\nu(m_0)`$. This includes the exact reach of the
  least long restarts found earlier, and $`m = G_2 + n`$ gives $`\delta + 1 + n`$, as was conjectured. **CROSS-O**: for $`1 \le x \le \Phi^\chi_{\rho_\lambda}`$, $`r(\lambda) \ge \upsilon_{\lambda+\omega^2\cdot x}`$ iff
  $`m_\lambda \ge G_2\cdot D_x`$, where $`o_\lambda(D_x) = x`$; so crossing is sharp at every such index distance, not only at index fixed points. (The referee: EXACT-LONG uses the far
  upper-bound rule TOP-REG-FAR in a case its refereed proof does not state; the same proof works, but it should be a lemma of its own; one line is missing in LB. Both are repaired in [SHIFT3.md](SHIFT3.md) §1.1, with 2 reviews.)
- **The χ-tier of η-offsets and multipliers** (proved, given FRAG, as a list of substitutions into the proofs of §2.1): the transport, pins, H-RC and the far rule across every
  η-offset below $`\Phi^\chi_\Omega`$; multipliers below $`\Phi^\chi_2`$; **R-CAP$`^\chi`$** for every code $`G_2 \le m \lt \mathbb{G}^\chi`$; **CEIL$`^\chi`$** (no FRAG): $`m_u \ge \mathbb{G}^\chi`$ gives
  $`\eta_u \ge \theta_2\cdot\Phi^\chi_2`$; **CROSS-SHARP$`^\chi`$** for the constant-free multiples $`M`$ of $`\Omega_2`$ up to $`\Phi^\chi_2`$. (The referee: a hull lemma one level up is used but
  not stated (now proved, [SHIFT3.md](SHIFT3.md) §1.1); one example threshold is wrong, the right one is $`G(\Omega_2^2) = \psi_{\Omega_2}(\Omega_\omega + \omega^{\theta_2+\Omega_2\cdot 2})`$.)
- **Theorem X12** (proved, given FRAG). As X11, with R-CAP$`^\chi`$ and CEIL$`^\chi`$:

```math
\nu_C \ge X_{12} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+\Phi^\chi_2} + \omega^{\mathbb{G}^\chi+1} + \omega^{G_2+1}),\qquad \mathbb{G}^\chi = \psi_{\Omega_2}(\Omega_\omega + \omega^{\theta_2+\Phi^\chi_2}),\quad \Phi^\chi_2 = \psi_{\Omega_3}(\Omega_3^{\Omega_3}).
```

So **Wilken's claim holds in $`R_2^C`$ on $`[0, X_{12}]`$, both halves, given FRAG**, and $`X_{11} \lt X_{12} \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$. Without FRAG the range stays $`[0, X_4]`$. Also
(P-LOW$`^\chi`$) every restart $`a`$ with (P) has $`e_a \ge \mathbb{G}^\chi + 1`$.

- **Not proved** (open, as the paper says): (P) and (Q′) at $`(L(\omega), L(\omega+1))`$ or at any named pair, and so an InaccPsi upper bound for $`\nu_C`$. Missing:
  (V1″) exact caps for short restarts with $`\tau \in (\Phi^\chi_\Omega + 1, G_2)`$, and for long restarts with $`D \ge \Phi^\chi_\Omega`$ or $`m_0 \ge \Phi^\chi_\Omega`$ (for codes $`\ge \mathbb{G}^\chi`$, where the
  predecessors in (P) are, there is no upper bound at all); (V2″) η-offsets at or above $`\Phi^\chi_\Omega`$. Next (outline): redo the three parts above (levels on Wilken's side, the values
  of $`\psi_{\Omega_2}`$, base change) with the collapsing hierarchies $`\vartheta_D`$ of §1.2 and §2.2 in place of $`\chi_v`$.
- Remark: the formulas have the shape of the tracking chains of Carlson–Wilken 2012, Thm 7.9 (the reach of a long restart is the reach of a later restart plus an offset read
  there); there the description is exact because the coding is onto, as here below $`\Phi^\chi_\Omega`$.

### 3.2 Native codes for $`\mathrm{CH}_3`$: HOST$`_k`$ and the top TOP$`_\omega`$

Notation of §2.2. The **chain number** $`\mathrm{cn}(P)`$ of a pattern is the largest $`m`$ with pairs $`x_1 \lt_2 y_1, \dots, x_m \lt_2 y_m`$, $`y_i \lt x_{i+1}`$ and $`x_i \le_1 x_{i+1}`$. So $`\mathrm{cn}(P) \le 1`$
iff $`P`$ has no L1p configuration, and $`\mathrm{cn}(\mathrm{CH}_k) = k`$. $`Z'_\omega`$ is the least fixed point of $`\theta_{\Xi_\omega}`$ with $`\Xi_\omega = \sup_n \Xi_n`$, and $`Z''_\omega`$ the least fixed point of
$`\theta_{\Xi'_\omega}`$, where $`\Xi'_\omega`$ is the least fixed point of $`\vartheta^2_{P}`$ with $`P = \sup_n P_3^{(n)}`$ (the $`P_3`$ of the $`n`$-ary systems).

- **Theorem HOST$`_k`$** (proved). For $`k \ge 1`$, every RF fan-free pattern $`P`$ with $`\mathrm{cn}(P) \le k-1`$ lies in $`C(u_1)`$ of every copy of $`\mathrm{CH}_k`$, so $`\max P^* \lt \iota(\mathrm{CH}_k)`$. This is
  sharp. $`k = 2`$ is HOST2 ([FANFREE.md](FANFREE.md) §7.2); the proof is the same, except that the part above the first pair is mapped, by the case $`k-1`$, into the copy of $`\mathrm{CH}_{k-1}`$ with the same top.
- **MODULE-RED$`_k`$** (proved): the module reduction with "$`\mathrm{cn} \le k-1`$" and $`\mathrm{CH}_k`$. **RED-TOWER** (proved, a reduction): the statement $`H_m`$, so "the first fan needs an
  inaccessible", already follows if every $`t \lt \theta_0`$ has some $`k`$ and a module system with $`\mathrm{cn} \le k-1`$ above $`t`$; one fixed $`k`$ is not needed.
- **TOP$`_\omega`$, Theorem IDX-ω** (proved). The block $`[r \lt x \lt_2 y \lt a \lt_2 b,\ a \le_1 b,\ r, x \le_1 b + E(\beta)]`$ has chain number 2 and hosts every $`\mathrm{TOP}_n`$ (the levels are roots of $`a`$).
  So $`\iota(\mathrm{CH}_3) \ge Z'_\omega`$. This settles the open item TOP-ω of §2.2 for $`\mathrm{CH}_3`$ (for $`\mathrm{CH}_2`$ it stays open, since this block has an L1p configuration).
- **Theorem IDX-ω⁺** (proved). The atom $`\vartheta^2_P(\alpha)`$ is coded by a pair placed like the block of an atom, with its own top. So, natively, $`\iota(\mathrm{CH}_3) \ge Z''_\omega \gt Z'_\omega`$.
  Conjectured names: $`\Xi'_\omega = \psi_{\Omega_2}(\Omega_\omega + \Omega_2)`$ (relativized to $`\Omega_1`$) and $`Z''_\omega = H(\Xi'_\omega + \Omega_1)`$ (the first is false: $`\Xi'_\omega = \psi_{\Omega_2}(\Omega_\omega + \omega^{\theta_2+\Omega_2})`$, [SHIFT4.md](SHIFT4.md) §1.2). This is still far below the known bound
  $`\iota(\mathrm{CH}_3) \gt \iota(\mathrm{CH}_2) \gt \nu_C \ge X_{12}`$ given FRAG.
- **The normal-form template of Wilken's "Pure patterns of order 2"** (for pure $`R_2`$): a closure of a point under its needs, module parameters, layer bases and items gives a native
  pattern $`N(\gamma)`$. Proved: the closure is finite, and $`\iota(N(\gamma)) \ge \gamma`$ (the lower half of his Thm 4.4). Open: base minimization, the upper half of Thm 4.4 (it needs an
  $`R_2^C`$ form of Cor 5.8 of "Tracking chains revisited"), least cardinality. (The referee: the paper's other "transfers" are only a dictionary, so they are remarks.)
- The referee's other minor points: the checked shape of one atom code differs from the one in the proof; three wording points. (Applied in [SHIFT3.md](SHIFT3.md) §1.2.)
- **Open**: the atom item for indices $`\ge P + 1`$ (outline), the same one cardinal higher, then $`\Omega_{\omega\cdot 2}`$ (chain number 3, or a comparison lemma for pairs nested in a pair).

### 3.3 The shapes of $`\Phi_3`$: 3,071 of 3,166

Notation of §2.3.

- **The minor points of the nineteenth-round review are applied**: the program version of each run is stated, the size formula of M5 is now
  $`|E_0 \cdots E_n| = (g+f)\cdot 2^n - f`$ (**2 reviews**; the referee re-derived it), "the search is complete" is limited to the slots that the program tries, and one reason is corrected.
- **9 proofs re-confirmed** (proved): the 9 matrices with $`t = 1`$ that the earlier version proved but not again within 60 seconds are re-proved by the same derivation cut into
  tasks of less than 60 seconds; the added hints only change the search order.
- **12 more with $`t = 1`$** (III 8, ROOT 2, I 2; proved, accepted at the same level as GR-UNIF2): members of a unit may be made in copies nested inside the unit's batch (GR-UNIF3).
- **M5** (13): BIN-SHAPE, checked for $`n \le 9`$: $`\mathrm{conv}(A[n])`$ is a fixed skeleton plus a binomial segment $`E_1 \cdots E_n`$ inside one $`\le_2`$-pair, with $`E_j = F[E_0 \cdots E_{j-1}]`$ for a frame $`F`$.
  BIN-F and BIN-INS (proved) turn one covering of the skeleton into coverings for every $`n`$ with that shape, and such coverings exist for all 13. So the step is proved for $`n \le 9`$, and
  for every $`n`$ given BIN-SHAPE. BIN-SHAPE for every $`n`$ is open, so M5 is not counted.
- **The tally** (checked; $`3{,}071 = 3{,}050 + 21`$):

| class | matrices | proved for every $`n`$ | given BIN-SHAPE | given a condition checked for small $`n`$ | $`t = 2`$, given a shape checked for small $`n`$ | open |
|---|---|---|---|---|---|---|
| I | 581 | 573 | 0 | 0 | 0 | 8 |
| SUM | 603 | 582 | 0 | 1 | 0 | 20 |
| ROOT | 635 | 634 | 0 | 0 | 0 | 1 |
| III | 1,347 | 1,282 | 13 | 0 | 24 | 28 |
| all | 3,166 | 3,071 | 13 | 1 | 24 | 57 |

- **Left** (95): $`t = 0`$: M5 13; $`t = 1`$: 3 of class III with no shape; $`t = 2`$: III 49, ROOT 1, I 8, SUM 21.
- The referee's minor points: BIN-F uses two facts it does not state; three points in BIN-INS that the 13 coverings do not use; one remark is informal; one old program
  version is no longer kept (the referee's fresh reruns used the current one). (Applied in [SHIFT3.md](SHIFT3.md) §1.3.)

### 3.4 $`\nu_C = \nu_S`$ and the converse in Carlson–Wilken 2012

Notation of §2.4. Carlson–Wilken 2012, Thm 7.9 (b), says for pure $`R_2`$ that a uniform finite-set criterion (one copy for all sizes) holds at every pair $`\gamma \lt_2 \alpha`$. The paper asks
whether this carries over to $`R_2^+`$ at the pair $`(x, \nu)`$.

- **How the converse is proved there** (proved, as a reading of the proof): it is carried in the induction hypothesis; every pair is made by a direct check, by an interval isomorphism
  from an earlier pair, or by suprema, and the list is complete. (The referee: the list omits two cases, both covered by suprema.)
- **TR-FAIL, FORCED** (proved): with $`+`$, a translation over an additive principal $`u`$ is not an isomorphism once $`u\cdot 2`$ is in its interval, and a map that is the identity below
  $`u_n`$ and sends $`u_n`$ to $`x`$ sends sums to sums. (The referee: that such maps must be base changes is not forced, since $`\omega^a`$ is not in the language.)
- **COMMON, NEC$`^C`$ ⇒ GOAL, NEC$`^S`$** (proved): in $`R_2^C`$ the uniform criterion at $`(x, \nu)`$ implies $`\nu_C = \nu_S`$, so it is at least as hard as the goal; in $`R_2^S`$ it adds nothing.
  **LOAD** (proved): every $`\lt_2`$-pair with right end below $`\nu_S`$ (in $`R_2^S`$) or below $`\nu_C`$ (in $`R_2^C`$) meets the uniform criterion. **XT** (proved): every admissible copy sends $`x`$ to some $`u_m`$.
- **Not proved** (blocking point, against the paper's location claim): that $`(x, \nu)`$ is the case of the 2012 proof that uses one interval isomorphism. The two intervals have different
  order types ($`u_{n+1}`$ against $`\nu`$), and the level of the copy must grow with the extension: for $`X = \{u_{n-1}\}`$ and $`Y = \{x, x + u_{n+1}\}`$ no copy at level $`u_n`$ works. So no case of
  the 2012 proof fits literally. What survives: the reaches of the restarts must commute with a base change adapted to the extension.
- Not counted: the test ET is only $`\Sigma_2`$-elementarity written with finite diagrams (a restatement); "no general converse" is a remark; the claim that no choice of copies removes
  (D1b) rests on unrefereed parts.
- **Open**: $`\nu_C = \nu_S`$ and $`\nu_C \lt \nu_S`$. Missing: reaches that commute with base change for the long restarts and on $`[x^\#, \nu)`$, that is (D1b) and (E4). §3.1 gives such caps for
  short restarts with $`\tau \le \Phi^\chi_\Omega + 1`$ and long ones with $`D, m_0 \lt \Phi^\chi_\Omega`$; their use for (D1b) is an outline.

### 3.5 Status after the twentieth round

The twenty-first to thirty-fifth rounds changed this status; see [SHIFT3.md](SHIFT3.md) §1.5, §2.5, [SHIFT4.md](SHIFT4.md) §1.5, §2.5, [SHIFT5.md](SHIFT5.md) §1.4, §2.4, [SHIFT6.md](SHIFT6.md) §1.4, §2.4, §3.4 , [SHIFT7.md](SHIFT7.md) §1.4, §2.4, §3.4, [SHIFT8.md](SHIFT8.md) §1.4, §2.4 and [SHIFT9.md](SHIFT9.md) §1.4.

- Wilken's claim in $`R_2^C`$: both halves hold on $`[0, X_4]`$ without FRAG, and on $`[0, X_{12}]`$ given FRAG ($`[0, X_9]`$ with 2 reviews); the core half holds on $`[0, \nu_C]`$.
  No InaccPsi upper bound for $`\nu_C`$: (P) at a named pair stays open.
- The lower-bound program below $`\theta_0`$: the step below SRO holds for every $`n`$ on 3,071 of the 3,166 sample matrices; natively $`\iota(\mathrm{CH}_2) \ge Z_\omega`$ and $`\iota(\mathrm{CH}_3) \ge Z''_\omega`$.
- Upper bounds: still none by an InaccPsi term for $`\iota(\mathrm{CH}_k)`$, $`m_F`$, $`x_F`$, $`C^*_3`$ or $`\nu_C`$.
- $`\nu_C = \nu_S`$: left: (D1b) and (E4); the converse of Carlson–Wilken 2012 does not give it.

### 3.6 Checks of the twentieth round

Each run was under 60 seconds; none is a proof.

- §3.1. Names, normal forms, $`D'`$ and $`X_{11} \lt X_{12} \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$: Python and Lean agree (the Lean file only compares terms; green, and green in the referee's rerun). 56 predicted
  normal-form results at the boundaries of PSI2-χ (all as predicted); the level shift on 51,200 term pairs (order and normal forms kept); the counterexamples to EXACT-PHI in
  Wilken's terms. The referee: 23 more boundary predictions and 889 sampled exponents, all as predicted.
- §3.2. All new blocks are patterns, RF and fan-free with the stated chain number. Certificates, all replayed: 20 of 21 in the predicted direction (the missing one follows
  from two found ones); in the reverse direction only one, which is true. The referee: three patterns with chain number 2 are below $`\mathrm{CH}_3`$; a control with chain number 3 is not found.
- §3.3. The referee: 13 of 13 M5 derivations rerun; BIN-SHAPE at $`n = 10`$ for 8 of 13 (the other 5 hit the size or time limit); 5 fresh reruns of $`t = 1`$ proofs, all proved; the slot
  rule at four far levels, the same.
- §3.4. No run by the paper. The referee: the order types at the conjectured names for $`n \le 4`$, and a Lean file with the core of TR-FAIL and the order-type mismatch (green).

### 3.7 Open

The twenty-first to thirty-fifth rounds changed this list; the current list is [SHIFT9.md](SHIFT9.md) §1.6.

- Upper bounds: (P) and (Q′) at one named pair for $`\nu_C`$; (P) needs (V1″) and (V2″) of §3.1, and (Q′) the isominimal patterns of $`L(\omega)`$; bounds for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$, $`f_0`$,
  $`m_3`$, $`c_0`$.
- The claim above $`X_{12}`$ given FRAG: the same three parts with the hierarchies $`\vartheta_D`$ (EXACT-O past $`\Phi^\chi_\Omega`$, η-offsets at or above $`\Phi^\chi_\Omega`$).
- The first inaccessible: $`H_m`$, through $`\iota(\mathrm{CH}_2) \ge \theta_0`$ or, by RED-TOWER, through native codes with a growing chain number (next: the atom item for indices
  $`\ge P + 1`$, then $`\Omega_{\omega\cdot 2}`$); UNIF-FS below SRO on the 95 matrices of §3.3 (M5 needs BIN-SHAPE for every $`n`$).
- $`\nu_C = \nu_S`$: (D1b), which needs the same tools as (P), room past $`\omega^{G_2}`$ and caps that commute with base change; (E4).
- Names: $`R(\Theta_{d\omega})`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$; the exact reaches of the long restarts with $`D \ge \Phi^\chi_\Omega`$ or $`m_0 \ge \Phi^\chi_\Omega`$; names beyond
  $`X_{12}`$; the rest of [COVER.md](COVER.md) §9.
