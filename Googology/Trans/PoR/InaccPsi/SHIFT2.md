[← Back](README.md) | [English](SHIFT2.md) | [Japanese](SHIFT2-ja.md)

# $`R_2^+`$, the eighteenth and nineteenth rounds: $`\nu_C \ge X_9`$ and $`X_{11}`$ given FRAG, reaches across index fixed points, flat and nested codes, SYM-Q, GRN and MIN-EXACT

This page continues [SHIFT.md](SHIFT.md) (§9 there is the seventeenth round); §1 is the eighteenth round and §2 the nineteenth. The status words are those of [README.md](README.md) §3: **proved** means that
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

The nineteenth round changed this status; see §2.5.

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

The nineteenth round changed this list; the current list is §2.7.

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

- **Labelled as open, correctly**: Conjecture EXACT-PHI (exact caps for $`\tau \in [\Phi_\Omega, G_2)`$); (D1b) of §2.4 for spans over short restarts with offset below $`\Phi_\Omega`$ (an outline).
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

- Upper bounds: (P) and (Q′) at one named pair for $`\nu_C`$; (P) needs (V1′) and (V2′) of §2.1, and (Q′) the isominimal patterns of $`L(\omega)`$; bounds for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$, $`f_0`$,
  $`m_3`$, $`c_0`$.
- The claim above $`X_{11}`$ given FRAG: η-offsets at or above $`\Phi_\Omega`$, and Conjecture EXACT-PHI.
- The first inaccessible: $`H_m`$, through $`\iota(\mathrm{CH}_2) \ge \theta_0`$ (from $`Z_\omega`$ on: one finite top for all $`\mathrm{TOP}_n`$, then the region $`H(D)`$ for $`D \gt \theta`$, then the levels of $`\Omega`$ up
  to SRO); UNIF-FS below SRO on the 116 matrices of §2.3 (M5 needs a family shaped like a tree).
- $`\nu_C = \nu_S`$: (D1b), which needs the same tools as (P) and room past $`\omega^{G_2}`$; (E4).
- Names: $`R(\Theta_{d\omega})`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$; the exact reaches of the long crossed restarts (between CROSS-U and R-CAP$`^U`$); names beyond
  $`X_{11}`$; the rest of [COVER.md](COVER.md) §9.
