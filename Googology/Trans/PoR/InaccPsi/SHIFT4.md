[← Back](README.md) | [English](SHIFT4.md) | [Japanese](SHIFT4-ja.md)

# $`R_2^+`$, the twenty-third and twenty-fourth rounds: $`\nu_C \ge X_{18}`$ given FRAG, closed and exact reaches, the plateaus at $`\Omega_k`$, the shapes of $`\Phi_3`$, and native codes past $`\psi_{\Omega_1}(\Omega_\omega\cdot\omega)`$

This page continues [SHIFT3.md](SHIFT3.md) (§2 there is the twenty-second round); §1 is the twenty-third round and §2 the twenty-fourth. The twenty-fifth and twenty-sixth rounds are on [SHIFT5.md](SHIFT5.md), the twenty-seventh to twenty-ninth on [SHIFT6.md](SHIFT6.md), the thirtieth to thirty-second on [SHIFT7.md](SHIFT7.md), the thirty-third and thirty-fourth on [SHIFT8.md](SHIFT8.md), the thirty-fifth to thirty-seventh on [SHIFT9.md](SHIFT9.md). The status words are those of [README.md](README.md) §3: **proved** means that
an independent referee found the result proved with no fatal or blocking point. A statement with a blocking point against it is listed under **Not proved**.
A certificate counts only when it was replayed. A result that the referee calls only a restatement of something known is not counted as progress.

## 1. The twenty-third round

Four papers (2026-10), each refereed once, so a result in this section has 1 review unless a count is given. **2 reviews** means that a referee of the
twenty-second round proposed the repair (or checked the result) and the referee of this round checked it again as written out. None of the papers uses
Wilken, JSL 72 (2007), Carlson, AML 38 (1999), Wilken, AML 45 (2006), or the equivalence that Carlson 2009, p. 97, announces. Papers cited here: Wilken,
"Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) (below [W07a]; Def 3.1, Thm 3.23, Def 4.11, Def 7.5, Cor 7.6, the proof of L.8.1), and Wilken,
"Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) (below [W07b]; L.2.1, Thm 2.2, Def 4.1, L.4.2, Cor 5.10). No Lean file was added: two papers (§1.2, §1.4)
checked a Lean file that only compares terms (`#eval`, no theorem; green, and green in the referees' reruns), so these count as checks. The minor points of the
twenty-second-round reviews are applied, in [SHIFT3.md](SHIFT3.md) §2 and below. Levels are numbered as in [SHIFT.md](SHIFT.md) (one higher than in the papers).

New names of this round ($`G(\zeta) = \psi_{\Omega_2}(\Omega_\omega + \theta_2\cdot\zeta)`$ and $`Z = \psi_{\Omega_2}(\Omega_\omega + \Omega_2)`$ as in [SHIFT3.md](SHIFT3.md) §2):

```math
\zeta^* = \psi_{\Omega_3}(\Omega_\omega + \Omega_3),\qquad G(\Omega_3) = \psi_{\Omega_2}(\Omega_\omega + \Omega_3),\qquad G(\Omega_3 + 1) = \psi_{\Omega_2}(\Omega_\omega + \Omega_3 + \theta_2).
```

### 1.1 Closed reaches, exact caps with the lh-shift, and the tier below $`\zeta^*`$: $`\nu_C \ge X_{15}`$ given FRAG

Notation of [SHIFT3.md](SHIFT3.md) §2.1. For a restart $`\lambda`$ the blocks of its region are $`(\delta_j, \delta_{j+1}]`$; for a $`\upsilon`$-point $`b`$, $`\mathrm{seg}(b) = [b, b^\infty)`$, where $`b^\infty`$ is the next
$`\upsilon`$-point; $`\mathrm{lh}_1`$ is Wilken's reach in $`R_1^+`$. A point $`y`$ of $`\mathrm{seg}(\delta_j)`$ is **closed** if $`\mathrm{lh}_1(\alpha) \le y`$ for every additive principal $`\alpha \in (\delta_j, y]`$, and $`\mathrm{LC}^S(y)`$ is the
least closed point $`\ge y`$ there ($`\delta_{j+1}`$ if there is none). The **lh-shift** $`\mathrm{LHF}`$ is the identity below $`\delta_j\cdot\omega`$ and replaces the leading Cantor normal form term $`x`$
of $`y`$ by $`\mathrm{lh}_1(x)`$ above it.

- **The minor points of the twenty-second-round review are applied** (proved, **2 reviews**). Wilken's side is run in the system $`T^{\Omega_m}`$ ([W07a] Def 3.1 with $`\tau = \Omega_m`$), where
  Thm 3.23 makes every ordinal below $`\Omega_{m+1}`$ a term. The two asserted steps of PSI-n get their arguments (the candidates of type high base; an induction on the size of terms).
  The reading $`\Theta_\nu`$ is onto only below $`\pi_{\eta_\nu}`$, and the upper bound uses the reading of the forms. The source of $`\upsilon_{a+1} = \upsilon_a^\infty`$ is [W07b] Cor 5.10.
- **CLOSED-REACH** (proved, no FRAG). Every reach is closed in $`R_2`$ (SKEL⁺). Inside a block $`(\delta_j, \delta_{j+1}]`$ ($`j \ge 1`$) the closed points are the closed points of $`\mathrm{seg}(\delta_j)`$
  and $`\delta_{j+1}`$, so no reach lies in $`[\delta_j^\infty, \delta_{j+1})`$.
- **TOP-REG$`^\omega`$** (proved, no FRAG). If $`y \in [\delta_j, \delta_{j+1})`$, $`y \gt \delta_1`$, is not reflected, then $`r(\lambda) \le y`$ or $`r(\lambda) = \mathrm{LC}^S(y)`$. **The literal rule $`r(\lambda) \le y`$, which
  [SHIFT3.md](SHIFT3.md) §2.1 named as the missing lemma, is false** (given FRAG): at $`\tau_\nu = \omega^{G(\omega+1)+\omega}`$ and $`y = \omega^{\delta_\nu+\omega}`$, $`r(\nu) = y + 1`$ (NO-NAIVE; such restarts exist below $`X_{14}`$).
  **REACH$`^{\mathrm{full}}`$**: $`r(\lambda) = \mathrm{LC}^S(y_0)`$ for every short restart, where $`y_0`$ is the least point above $`\delta`$ that is not reflected ("$`\le`$" without FRAG, "$`=`$" given FRAG).
- **Closed points** (ROOT, LOCAL, TRANS-E; proved). Below $`\varphi(\omega, \delta_j + 1)`$ every principal $`\alpha`$ has $`\mathrm{lh}_1(\alpha) \lt \alpha\cdot\omega`$ (for example $`\mathrm{lh}_1(\omega^a) = \omega^a + \mathrm{logend}(a)`$ when $`\omega^a`$ is
  not an $`\varepsilon`$-number), the lh-shift enumerates the closed points there, and it commutes with base change.
- **Theorem EXACT-CL** (proved; "$`\le`$" without FRAG, "$`=`$" given FRAG). Every restart $`\nu`$ with $`\rho_{\nu+\omega^2} \le \nu_S`$ and $`\tau_\nu \lt \varphi(\omega, G(\omega+1)+1)`$ has
  $`r(\nu) = \mathrm{LHF}(\delta_\nu + o_\nu(\tau_\nu))`$. So $`r(\nu) = \delta_\nu + o_\nu(\tau_\nu)`$ holds exactly for $`\tau_\nu \lt \omega^{G(\omega+1)+\omega}`$ (before: up to $`G(\omega+1)\cdot\omega`$). (The referee: the identity that
  fixes the range, $`\Theta_\nu(\varphi(\omega, G(\omega+1)+1)) = \varphi(\omega, \delta_\nu+1)`$, is stated without proof; it is proved in §2.1, PHI-COMM.) **Conditional, not counted**: the same formula in the blocks $`j \ge 2`$, given the open
  statements GAP$`_i`$, $`i \lt j`$.
- **Long restarts** (proved, given FRAG). R-CAP$`^O`$, LB, EXACT-LONG, CROSS-O and LONG-CLASS for $`m_\lambda = G_2\cdot D + m_0`$ with $`D \lt G_2`$ (before: $`D \lt \theta`$), and EXACT-LONG with the lh-shift for
  $`m_0 \lt \varphi(\omega, G(\omega+1)+1)`$. The pin lemma they use is a case of MULTI-RC\* ([SHIFT2.md](SHIFT2.md) §1.1), as the referee notes, so it is not counted on its own; the obstacle
  named in [SHIFT3.md](SHIFT3.md) §2.1 for $`D \ge \theta`$ was only in the wording.
- **The tier of multipliers below $`\zeta^*`$** (proved, given FRAG, as a list of substitutions; the referee checked the substituted inputs at every place found, and asks that the places
  be listed). D′-UNC for η-offsets below $`G_2`$ at bases $`\ge \theta_2\cdot\omega^2`$ (no FRAG); the counting rule PSI-θ one level up (multipliers $`\psi_{\Omega_3}(\Omega_\omega + \delta)`$, high base $`\theta_2`$); the
  transport, the pins and the far rule across η-offsets below $`Z`$ (their prefix restarts have $`\tau \lt Z \lt G(1)`$, where EXACT-O$`^\theta`$ applies); **R-CAP** for every code $`G_2 \le m \lt G(\Omega_3)`$;
  CROSS-SHARP for the constant-free multiples $`M`$ of $`\Omega_2`$ with $`\theta_2 \le M \lt \zeta^*`$; **CEIL** (no FRAG): $`m_u \ge G(\Omega_3)`$ gives $`\eta_u \ge \Omega_3`$. Here $`G(\zeta) \lt G(\Omega_3)`$ for $`\zeta \lt \zeta^*`$, and
  $`G(\Omega_3)`$ is their supremum.
- **Theorem X15** (proved, given FRAG; it rests on the R-CAP above):

```math
\nu_C \ge X_{15} = \psi_{\Omega_1}(\Omega_\omega + \Omega_3 + \omega^{G(\Omega_3)+1} + \omega^{G_2+1}),\qquad G(\Omega_3) = \psi_{\Omega_2}(\Omega_\omega + \Omega_3).
```

So **Wilken's claim holds in $`R_2^C`$ on $`[0, X_{15}]`$, both halves, given FRAG**, $`\nu_S \ge X_{15}`$, and $`X_{14} \lt \psi_{\Omega_1}(\Omega_\omega + \Omega_3) \lt X_{15} \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$. Also (P-LOW) every
restart $`a`$ with (P) has $`m_a \ge G(\Omega_3)`$ and $`\eta_a \ge \Omega_3 + \omega^{G(\Omega_3)+1}`$. §1.4 goes further, to $`X_{16}`$.

- **Open** (GAP$`_j`$, ROOT-CL and EXACT-CL\* are proved in §2.1): GAP$`_j`$ ($`r(\nu) \lt \delta_{j+1}`$ for $`\tau_\nu \in [\varphi(\omega, G(\omega j+1)+1), G(\omega j+2))`$) and ROOT-CL (for a principal $`x`$, the least principal $`\alpha \gt \delta_j`$ with $`\alpha \le_1 x`$ lies in the closure of $`x`$),
  which would give exact reaches on all of $`[\theta, G_2)`$ (conjecture EXACT-CL\*: $`r(\nu)`$ is the $`o_\nu(\tau_\nu)`$-th closed point above $`\delta_\nu`$); $`D`$ or $`m_0`$ in those gaps; the codes past §1.4;
  (P), (Q′), and an InaccPsi upper bound for $`\nu_C`$.
- The referee's other minor points (applied in §2.1): "the literal rule is false" must say "given FRAG"; one step of CEIL is only checked (the referee gives a two-line proof); one line of P-LOW
  is missing; closedness in a far region needs more than in the own region (only the safe direction is used); two names clash; one witness was checked one point too low.

### 1.2 Native codes past $`\upsilon^*`$

Notation of [SHIFT3.md](SHIFT3.md) §2.2 and [SHIFT2.md](SHIFT2.md) §3.2: $`\Xi_\omega = \sup_n \Xi_n`$; $`\Xi'_\omega`$ is the least fixed point of $`\vartheta^2_P`$ with $`P = \sup_n P_3^{(n)}`$; $`Z''_\omega`$ is the least fixed point of
$`\theta_{\Xi'_\omega}`$; $`\hat G = G(\Omega_2) = \psi_{\Omega_2}(\Omega_\omega + \omega^{\theta_2+\Omega_2})`$.

- **The blocking point of the twenty-second-round review is repaired** (proved, **2 reviews**). The system of $`\Xi'_\omega`$ agrees below $`\Xi_2`$ with the pure system, and the control of the
  parameters holds for the pure parameters (CNST-PURE; the one new case is written out). The map $`f(\eta) = 1 + \eta`$ covers both parts at once, so nothing has to be glued: EMB
  along this map holds iff (E1) $`D \subset \Xi'_\omega`$ and (E2′) the parameters of every uncountable $`\eta \in D`$ are below $`H(\eta)`$.
- **Theorem EN=EX** (proved; the referee derived it again case by case; no numeric test is possible). The $`n`$-ary systems of [SHIFT2.md](SHIFT2.md) §2.2 (enumeration pairs) and those of
  [SHIFT3.md](SHIFT3.md) §2.1 (exact-level pairs) have the same hierarchies and the same end points $`\Xi_n`$ and $`P_3^{(n)}`$; their parameters agree at the thresholds of level $`\ge 2`$, and one way at
  countable $`\varepsilon`$-numbers. With Lemma G1 ($`\zeta \lt G(\zeta) \lt \hat G`$ for $`\zeta \lt \hat G`$): $`\Xi_n = \psi_{\Omega_2}(\varepsilon_{\Omega_n+1})`$ (the question left open in [SHIFT3.md](SHIFT3.md) §2.1), $`\Xi_\omega = \theta`$,
  $`\sup_n P_3^{(n)} = \theta_2`$, $`\vartheta^2_{\theta_2}(\zeta) = G(\zeta)`$ for $`\zeta \lt \hat G`$, and $`\Xi'_\omega = \hat G`$. **The conjectured name $`\Xi'_\omega = \psi_{\Omega_2}(\Omega_\omega + \Omega_2)`$ of [SHIFT2.md](SHIFT2.md) §3.2 is false**, since $`Z \lt G(1) \lt \hat G`$.
- **(E1), (E2′) and EMB on all of $`D`$** (proved). So, natively,

```math
\upsilon^* \le \theta_{\Xi'_\omega}(0) \lt Z''_\omega \le \iota(\mathrm{CH}_3),\qquad \iota(\mathrm{CH}_2) \ge Z_\omega \ge \Theta_1 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta\cdot 2}).
```

The first is **the first native bound past $`\upsilon^*`$** (asked in [SHIFT3.md](SHIFT3.md) §2.2); the second is the lower half of the conjecture $`Z_\omega = \Theta_1`$ ([SHIFT2.md](SHIFT2.md) §2.2).

- **PUSH** (proved by transfer: it uses RED-DICT on $`D'`$, which rests on GEN⁺ in transferred form). With the map $`g \mapsto \psi_{\Omega_2}(\Omega_\omega + \theta\cdot g)`$, natively
  $`\iota(\mathrm{CH}_3) \gt \theta_{\Xi'_\omega}(0) \ge \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+\Omega_2}) \gt \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\theta_2) \gt \upsilon^*`$.
- The named bounds here ($`\upsilon^*`$, $`\Theta_1`$, $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+\Omega_2})`$) lie below the known non-native $`\iota(\mathrm{CH}_2) \gt \nu_C \ge X_{14}`$ (checked), so as ordinal bounds they add nothing; their value is that native module systems reach them, as
  RED-TOWER needs.
- **Open** (PSI$`^W`$, EN=EX for the stage systems and CNST$`^W`$ are proved in §2.4): PSI$`^W`$ (the counting rule over the base $`\Omega_\omega`$ at every level; checked on $`4 \times 11{,}990`$ pairs), EN=EX for the stage systems of [SHIFT3.md](SHIFT3.md) §1.2, and CNST$`^W`$;
  given the three, natively $`\iota(\mathrm{CH}_3) \gt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ (conditional, not counted). Also open: $`\mathrm{CH}_2`$ past $`\Theta_1`$, and whether $`\theta_{\Xi'_\omega}(0) \gt \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+\Omega_2})`$.
- The referee's minor points (applied in §2.4): the forms and CNST$`^\theta`$ are used up to $`\hat G`$, past the range where they were stated (valid, but it should be said); one test did not stop because a
  program recursed forever, not because of the time limit; the proof of EN=EX is too short in three places; PUSH must be labelled a transfer; two small points.

### 1.3 The shapes of $`\Phi_3`$: 3,163 of 3,166

Notation of [SHIFT3.md](SHIFT3.md) §2.3.

- **The minor points of the twenty-second-round review are applied** (**2 reviews**): the one-line repair of BASE-PHI-G; the input check for the core $`(0,0,0)(1,1,1)(1,0,0)(2,1,1)`$ is
  run, so T2-G holds for it (it is not in the sample, so it is not counted); the search limit of the probes is stated; one dictionary of the program is covered; comments.
- **Side-kid staircases** (15 matrices; proved). The engine of CHN-OPQ with a staircase marker and five hook lemmas; the family lemma FAM-S, by one generic step with the prefix left
  unknown; the derivation lemma **REFL**: BASE-PHI-G with one block, first covered inside the reach of a node by T-nodes and an inner chain of roots, then moved below by R1;
  TRANSFER-R carries it along the family.
- **Deep staircases** (8; proved). A path marker; the nested family FAM-DS (4 nodes per level); **NEST-C**: the nested family lies in $`C(x)`$ of every pair $`x \lt_2 y`$ with $`x \le_1 y\cdot 2`$; NEST and
  TRANSFER-N.
- **ROOT** (1; proved). The same with side kids on the path; the family has 9 nodes per level, one of them substituted into itself.
- **The tally** (checked; $`3{,}163 = 3{,}139 + 15 + 8 + 1`$):

| class | matrices | proved for every $`n`$ | open |
|---|---|---|---|
| I | 581 | 581 | 0 |
| SUM | 603 | 603 | 0 |
| ROOT | 635 | 635 | 0 |
| III | 1,347 | 1,344 | 3 |
| all | 3,166 | 3,163 | 3 |

- **Left** (3, class III, $`t = 1`$; open; proved in §2.3). The input grows by a chain with the constant label $`(2,0)`$; $`\mathrm{conv}(A[n])`$ has about $`n/2`$ nested members, each the last kid of the next, with a split
  between even and odd $`n`$. Needed: a chain marker whose hook uses two chain nodes per nesting, a recursive symbol for the members, a family lemma, and a derivation for a chain of
  sums of a node with itself (outline). REFL works at $`n \le 4`$ for 2 of the 3 (checked) and fails at $`n = 5, 6`$.
- The referee's minor points (applied in §2.3): FAM-S is proved up to the member $`K-2`$, and the member $`K-1`$ is one direct computation; one wording point in REFL; one citation; one note on a checksum
  file; one count needs a sentence; the transfers need "no reach of the template points at a member of the family", true for all templates but to be stated.

### 1.4 $`\nu_C = \nu_S`$: the first test case of CAP-0, the plateau at $`\Omega_3`$, and $`\nu_C \ge X_{16}`$ given FRAG

Notation of [SHIFT3.md](SHIFT3.md) §2.2 and §2.4 ($`H(\eta) = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$). $`u = H(\Omega_3) = \psi_{\Omega_1}(\Omega_\omega + \Omega_3)`$ is the first test case of CAP-0 named there; its code is $`G(\Omega_3)`$. $`f(x) = \psi_{\Omega_2}(\Omega_\omega + x)`$, and $`M_n`$ is the
$`n`$-th iterate of $`x \mapsto \psi_{\Omega_3}(\Omega_\omega + x)`$ from $`\theta_2`$.

- **PLATEAU** (proved, no FRAG). $`G`$ is constant on $`[\zeta^*, \Omega_3]`$, with value $`G(\Omega_3) = \sup_{\zeta \lt \zeta^*} G(\zeta)`$, and $`D'`$ has no point in $`[\zeta^*, \Omega_3)`$. So every restart below $`u`$ has
  $`\eta \lt \zeta^*`$ and code below $`G(\Omega_3)`$; a code $`\ge G(\Omega_3)`$ needs $`\eta \ge \Omega_3`$, and a code $`\ge G(\Omega_3+1)`$ needs $`\eta \ge \Omega_3 + \theta_2`$. The same plateau is at every $`\Omega_k`$, $`k \ge 3`$; at $`\Omega_2`$
  the point $`H(\Omega_2) = \upsilon^*`$ has the short code $`Z`$.
- **FIX-Z, D-UNC$`^Z`$** (proved, no FRAG). $`Z = \sup_n f^n(\theta)`$ and $`f = Z`$ on $`[Z, \Omega_2]`$; $`\zeta^* = \sup_n M_n`$ and $`\mathrm{Sh}(M_n) = f^n(\theta)`$. D-UNC holds for every η-offset below $`Z`$ at every
  base, and $`\eta + Z \in D'`$ iff $`\eta \ge \Omega_2`$.
- **TOP-REG at the offset $`Z`$, DICHOTOMY, LB-U** (proved, given FRAG). Either $`r(u) \le r(H(\Omega_3 + Z))`$, where $`H(\Omega_3 + Z) = \psi_{\Omega_1}(\Omega_\omega + \Omega_3 + Z)`$, or restarts below $`u`$ with codes in $`[G(\theta_2), G(\Omega_3))`$ reach
  across the offset $`Z`$ cofinally often. Also $`r(u) \ge r(H(\Omega_3 + \theta))`$.
- **The θ⁺ tier** (proved by transfer, given FRAG; the referee checked every input that depends on the multiplier or the offset but did not rewrite the substitution lists, the
  standard under which the tier of [SHIFT3.md](SHIFT3.md) §2.1 was accepted). Multipliers in $`[\theta_2, \zeta^*)`$ are read by $`\mathrm{Sh}`$, with values in $`[\theta, Z)`$, and the plateau top $`\Omega_3`$ is read as
  $`Z`$, the supremum. **R-CAP** for every code $`G_2 \le m \lt G(\Omega_3 + 1)`$; CROSS-SHARP at every $`M_n`$; **PLAT-SHARP**: $`r(\lambda) \ge H(\eta_\lambda + Z)`$ iff $`m_\lambda \ge G(\Omega_3)`$. This contains the R-CAP of
  §1.1 for the codes below $`G(\Omega_3)`$, which was proved there independently.
- **Theorem R-U** (proved, given FRAG, with the θ⁺ tier). $`r(u) = r(H(\Omega_3 + Z))`$, so $`r(u) \lt H(\Omega_3 + Z + \omega^2)`$: **CAP-0 holds at $`u`$**, and $`u`$ is not
  self-crossing. The prediction $`r(u) \ge H(\Omega_3 + \Omega_2)`$, read from CROSS-SHARP past its range ([SHIFT3.md](SHIFT3.md) §2.4), is false: the multipliers in $`[\zeta^*, \Omega_3)`$ are not
  normal, so the crossing argument stops at $`Z`$. (The referee: this is the exact analogue of the earlier pair GHAT and CROSS-F, [SHIFT2.md](SHIFT2.md) §2.1.) Also EXACT-G: every restart with
  code $`G(\Omega_3)`$ reaches exactly as far as the restart at its offset $`Z`$.
- **CAP-0 for every code below $`G(\Omega_3 + 1)`$** (proved, with the θ⁺ tier). So LOW$`_x`$ needs self-crossing long restarts with codes in $`[G(\Omega_3+1), P')`$ and $`\eta \ge \Omega_3 + \theta_2`$, each with
  a cofinal tail of codes $`\ge G(\Omega_3+1)`$ that cross the offset $`\omega^{Z+1}`$ (LOW-RED⁺, SC-PROP).
- **LOW is not decided.** (§2.2 proves READ on the ordinal side, and its caps below $`G(\hat\zeta_2)`$.) Conjecture READ (a cap reading of the code segment of every normal multiplier below $`\Omega_\omega`$, with the supremum at each plateau top) would give CAP-0
  for every code below $`P'`$, hence not-LOW, and would make $`P'`$ the first self-crossing code, as the conjectured names of the fan program say. (The referee: the closed form proposed
  for READ is wrong below $`\Omega_3`$ and must be restricted to $`\zeta \ge \Omega_3`$; the paper's "evidence for not-LOW" is a remark.)
- **Theorem X16** (proved, given FRAG, with the θ⁺ tier):

```math
\nu_C \ge X_{16} = \psi_{\Omega_1}(\Omega_\omega + \Omega_3 + \theta_2 + \omega^{G(\Omega_3+1)+1}\cdot 2),\qquad G(\Omega_3+1) = \psi_{\Omega_2}(\Omega_\omega + \Omega_3 + \theta_2).
```

So **Wilken's claim holds in $`R_2^C`$ on $`[0, X_{16}]`$, both halves, given FRAG**, $`\nu_S \ge X_{16}`$, the whole region of $`u`$ is in the core, and $`X_{15} \lt X_{16} \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$. Also (P-LOW) every
restart $`a`$ with (P) has $`e_a \ge G(\Omega_3+1) + 1`$ and $`\eta_a \ge \Omega_3 + \theta_2 + \omega^{G(\Omega_3+1)+1}`$. Without the θ⁺ tier the paper proves
$`\nu_C \ge X_{14}^+ = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2\cdot 2} + \omega^{G(\theta_2)+1}\cdot 2)`$ (given FRAG).

- **Conditional, not counted.** CAP-1 at the restart $`\psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{G(\Omega_3)+1})`$ of level 2 needs $`\nu_S \gt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ (for example not-LOW). Under not-LOW:
  $`\nu_C \ge \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{G(\theta_2)+1})`$, and with the θ⁺ tier $`\nu_C \ge \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{G(\Omega_3+1)+1})`$ (this raises $`Y_1`$ of [SHIFT3.md](SHIFT3.md) §2.4).
- **Open**: LOW, that is CAP-0 at codes in $`[G(\Omega_3+1), P')`$ (READ needs multiplier forms with $`\Omega_3`$ as a unit, the reading at each plateau top, and pins at exponents $`\ge G_2`$); (P) at
  $`(L(\omega), L(\omega+1))`$, which needs a lower bound at code $`P'`$; (P1), (D1b), (E4); $`\nu_C = \nu_S`$.
- The referee's minor points (applied in §2.1): the onto statement of the reading is misstated (the one used is an earlier one); the inventory of the tools at level 2 must add the θ-tier and the θ⁺
  tier; the analogue at level 2 must be labelled conditional; the hull lemma's hypothesis holds for every $`g`$ and should be said; the pin at the exponent $`Z`$ needs the region
  transport; the use of LEVEL-SHIFT and UNIF past their earlier range needs the rebasing written out; one cosmetic point.

### 1.5 Status after the twenty-third round

The twenty-fourth to thirty-seventh rounds changed this status; see §2.5, [SHIFT5.md](SHIFT5.md) §1.4, §2.4, [SHIFT6.md](SHIFT6.md) §1.4, §2.4, §3.4 , [SHIFT7.md](SHIFT7.md) §1.4, §2.4, §3.4, [SHIFT8.md](SHIFT8.md) §1.4, §2.4, [SHIFT9.md](SHIFT9.md) §1.4, §2.4 and §3.4.

- Wilken's claim in $`R_2^C`$: both halves hold on $`[0, X_4]`$ without FRAG, and on $`[0, X_{16}]`$ given FRAG ($`[0, X_9]`$ with 2 reviews; $`X_{15}`$ and $`X_{16}`$ rest on tiers proved as lists of
  substitutions); the core half holds on $`[0, \nu_C]`$. No InaccPsi upper bound for $`\nu_C`$: (P) at a named pair stays open.
- Reaches: every reach is closed, and the reach of a short restart is the least closed point above its least non-reflected point; exact for $`\tau \lt \varphi(\omega, G(\omega+1)+1)`$ by the lh-shift,
  and for long restarts with $`D \lt G_2`$.
- The lower-bound program below $`\theta_0`$: the step below SRO holds for every $`n`$ on 3,163 of the 3,166 sample matrices; natively $`\iota(\mathrm{CH}_2) \ge Z_\omega \ge \Theta_1`$,
  $`\iota(\mathrm{CH}_3) \ge Z''_\omega \gt \upsilon^*`$ (and $`\gt \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+\Omega_2})`$ by transfer), $`\iota(\mathrm{CH}_3) \ge \theta_{\Xi[\omega]}(0)`$, $`\iota(\mathrm{CH}_4) \ge Z^{(3)}`$.
- Upper bounds: still none by an InaccPsi term for $`\iota(\mathrm{CH}_k)`$, $`m_F`$, $`x_F`$, $`C^*_3`$ or $`\nu_C`$.
- $`\nu_C = \nu_S`$: LOW is not decided; CAP-0 holds at its first test case and for every code below $`G(\Omega_3+1)`$. Left: (P1), (D1b), (E4).

### 1.6 Checks of the twenty-third round

Each run was under 60 seconds; none is a proof.

- §1.1. Names, normal forms, membership in $`D'`$ and the order $`X_{14} \lt \psi_{\Omega_1}(\Omega_\omega + \Omega_3) \lt X_{15} \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$; a restart with $`\tau = \omega^{G(\omega+1)+\omega}`$ below $`X_{14}`$; the algebra
  of closed points on $`3 \times 4{,}000`$ samples (0 failures); PSI-θ one level up against the InaccPsi order on $`3 \times 25{,}440`$ pairs (0 mismatches). No Lean check. The referee: the
  covering lemma of the tier with constants (about 6,900 top atoms), no $`\eta \in [\zeta^*, \Omega_3)`$ in $`D'`$, and the region of the example restart below $`X_{14}`$: 0 violations.
- §1.2. Names, normal forms and order in Python and Lean (green); samples of $`D'`$, the collapse map, the parameters and monotonicity (0 failures); PSI$`^W`$ on $`4 \times 11{,}990`$ pairs
  (0 mismatches). The referee: the reruns give the same output; the rule PSI-θ on codes up to $`\hat G`$ on $`2 \times 35{,}910`$ pairs, CNST$`^\theta`$ in 1,120 tests, 168 plateau terms, 1,096 pairs for the
  parameters: 0 failures.
- §1.3. The templates agree with the program at $`n = 6, \dots, 9, 12, 16`$; hook values compared 1,125 times; an independent checker confirms 228 solutions; 0 false successes on 474 pairs.
  The referee: the templates at far levels (up to $`n = 13`$); the moved solutions pass (24 of 24); a checker written from the lemma texts accepts all 24 matrices at 10 levels and
  rejects all 427 broken solutions; the family lemmas on 2,230 prefixes not in the sample; 0 successes on 322 pairs that must fail.
- §1.4. Names, normal forms, membership in $`D`$ and the order chains in Python and Lean (green); the plateau on 328 terms, D-UNC$`^Z`$ on 1,422 offsets, the reading on 70 multipliers (0
  mismatches). The referee: eight runs with constants (the covering lemma on 441 codes, the plateaus at $`k = 2, 3, 4`$, membership in $`D`$ on $`[Z, Z + \Omega_1)`$ with 231 negative cases): 0 violations;
  the Lean rerun is green with the same output.

### 1.7 Open

The twenty-fourth to thirty-seventh rounds changed this list; the current list is [SHIFT9.md](SHIFT9.md) §3.6.

- Upper bounds: (P) and (Q′) at one named pair for $`\nu_C`$. (P) needs the caps past §1.1 and §1.4 and a lower bound at code $`P'`$; (Q′) needs the isominimal patterns of $`L(\omega)`$.
  Bounds for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$, $`f_0`$, $`m_3`$, $`c_0`$.
- The claim above $`X_{16}`$ given FRAG: GAP$`_j`$ and ROOT-CL (exact reaches on $`[\theta, G_2)`$); long restarts with $`D \ge G_2`$; the tier with $`\eta \ge \Omega_3`$ and codes $`\ge G(\Omega_3+1)`$ (multiplier
  forms with $`\Omega_3`$ as a unit, the reading at each plateau top, pins at exponents $`\ge G_2`$).
- The first inaccessible: native codes past $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+\Omega_2})`$ (PSI$`^W`$, EN=EX for the stage systems, CNST$`^W`$); $`\mathrm{CH}_2`$ past $`\Theta_1`$; stages $`\ge \omega^\omega`$, uncountable
  stage indices, $`\Omega_{\omega+1}`$; UNIF-FS below SRO on the 3 matrices of §1.3.
- $`\nu_C = \nu_S`$: LOW (CAP-0 at codes in $`[G(\Omega_3+1), P')`$, conjecture READ), LOW$`^\omega`$, (P1), TC⁺ for long restarts at offsets $`\ge P'`$, (D1b), (E4).
- Names: $`R(\Theta_{d\omega})`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$; the exact reaches of the long restarts with $`D \ge G_2`$; names beyond $`X_{16}`$; the rest of
  [COVER.md](COVER.md) §9.

## 2. The twenty-fourth round

Four papers (2026-10), each refereed once, so a result in this section has 1 review unless a count is given. **2 reviews** means that a referee of the
twenty-third round proposed the repair (or checked the result) and the referee of this round checked it again as written out. None of the papers uses
Wilken, JSL 72 (2007), Carlson, AML 38 (1999), Wilken, AML 45 (2006), or the equivalence that Carlson 2009, p. 97, announces. Papers cited here: [W07a]
(Def 3.28, L.3.30, Conv 4.1, Def 4.6, L.4.7) and [W07b] (L.2.1, Thm 2.2, L.4.2, the proof of Thm 5.3, Cor 5.10), as in §1. No Lean file was added: three papers (§2.1, §2.2,
§2.4) checked a Lean file that only compares terms (`#eval`, no theorem; green, and green in the referees' reruns), so these count as checks. All minor points of the
twenty-third-round reviews are applied, by the papers of this round, and checked again by its referees (**2 reviews**). Levels are numbered as in [SHIFT.md](SHIFT.md) (one higher than in the papers).

New names of this round ($`G`$, $`Z`$, $`\zeta^*`$ and $`f(x) = \psi_{\Omega_2}(\Omega_\omega + x)`$ as in §1; $`\zeta^*_1 = \zeta^*`$ and $`\bar Z_1 = Z`$):

```math
\zeta^*_a = \psi_{\Omega_3}(\Omega_\omega + \Omega_3\cdot a),\qquad \bar Z_a = \psi_{\Omega_2}(\Omega_\omega + \Omega_2\cdot a)\ (1 \le a \le \omega),\qquad \theta_3 = \psi_{\Omega_4}(\Omega_\omega),\qquad \tau_{\mathrm{LH}} = \varphi(\omega, G(\omega+1)+1).
```

### 2.1 The closed points of a segment, exact reaches below $`G_2`$, and the tier up to $`\Omega_3\cdot\omega`$: $`\nu_C \ge X_{17}`$ given FRAG

Notation of §1.1. For an additive principal $`x \in \mathrm{seg}(b)`$, its **root** $`\alpha_x`$ is the least additive principal $`\alpha \in (b, x]`$ with $`\alpha \le_1 x`$; $`\mathrm{lt}(c)`$ is the leading Cantor normal form term of $`c`$.

- **The minor points of the twenty-third-round reviews of §1.1 and §1.4 are applied** (proved, **2 reviews**). Among them, **PHI-COMM** (proved, 1 review): a substitution, and the
  reading $`\Theta_\nu`$, commute with $`\omega^x`$ and with $`\varphi`$ on normal Veblen terms; so $`\Theta_\nu(\tau_{\mathrm{LH}}) = \varphi(\omega, \delta_\nu + 1)`$, the identity that fixes the range of EXACT-CL (§1.1). (The referee: in the proof the
  enumeration of the non-fixed points must count from the base; the commutation still holds.) Also: the two-line proof that $`D'`$ has no point in $`[\zeta^*, \Omega_3)`$, the missing line of P-LOW,
  one pin lemma for all exponents below $`G(1)`$ with the region transport, and the reduction of the forms on $`[\theta_2, \zeta^*)`$ to the counting rule, written out.
- **ROOT-LOC** (proved, no FRAG). The root $`\alpha_x`$ lies in the $`b`$-localization of $`x`$ ([W07a] Def 4.6, L.4.7, L.3.30; the referee: it is the argument of [W07b] in the proof of Thm 5.3,
  claim (1)). So every transport $`S`$ has $`S(\alpha_x) = \alpha_{Sx}`$. This is ROOT-CL of §1.1 in the form that is used.
- **ENUM, COUNT** (proved, no FRAG; the referee redid every case by hand). The map $`e_b(c) = \mathrm{lh}_1(\alpha_{\mathrm{lt}(c)}) + (-\alpha_{\mathrm{lt}(c)} + c)`$ ($`e_b(c) = c`$ below $`b\cdot\omega`$) is an order isomorphism of
  $`\mathrm{seg}(b)`$ onto its closed points; $`\mathrm{LC}^S(y) = \max(y, \mathrm{lh}_1(\alpha_{\mathrm{lt}(y)}))`$; $`e_b`$ is the lh-shift below $`\varphi(\omega, b+1)`$, and it commutes with every transport.
- **Theorem EXACT-CL\*** (proved; "$`\le`$" without FRAG, "$`=`$" given FRAG). Every restart $`\nu`$ with $`\rho_{\nu+\omega^2} \le \nu_S`$ and $`\tau_\nu \lt G_2`$ has $`r(\nu) = e_{\delta_j}(c_\nu(\tau_\nu))`$, where
  $`\tau_\nu \in [G(\omega(j-1)+2), G(\omega j+2))`$ and $`c_\nu(\tau_\nu) = \delta_j + (-\delta_{j-1}^\infty + \Theta_\nu(\tau_\nu))`$ ($`\delta_0^\infty = 0`$). So the conjecture EXACT-CL\* of §1.1 holds, **GAP$`_j`$ holds for every $`j`$** (no FRAG), and for
  example $`r(\nu) = \varphi(\omega, \delta_\nu+1)\cdot\omega`$ at $`\tau_\nu = \tau_{\mathrm{LH}}`$. The same for long restarts with $`D, m_0 \lt G_2`$ (EXACT-LONG-CL\*), and pins at every exponent below $`G_2`$ (given FRAG).
  (The referee: the induction must start from EXACT-O$`^\vartheta`$, since $`\tau_\nu`$ can be $`0`$; one sentence about the onto part uses "$`=`$", so it is given FRAG.) (The referee of the twenty-sixth round: the rule that a tail stays in its segment needs the start of the tail
  above $`H(z_0)`$, as the proof chooses; as worded, $`\nu = H(\omega^\omega + \omega^2)`$ is a counterexample. [SHIFT5.md](SHIFT5.md) §2.2.)
- **The tiers of §1.1 and §1.4 written out** (proved by transfer, given FRAG, **2 reviews**). The tier below $`\zeta^*`$ of §1.1 is the θ⁺ tier of §1.4 below its top, and the θ⁺ tier is now
  written as 20 steps, each with its changed input, the proof of that input and the places where it enters, as the referee of §1.1 asked. So $`X_{15}`$ and $`X_{16}`$ have
  2 reviews. (The referee: the steps of the lower-bound side are sketches; they are not used for $`X_{15}`$, $`X_{16}`$ or $`X_{17}`$.)
- **The tier of the multipliers $`\Omega_3\cdot a + \zeta_L`$ ($`a \lt \omega`$) and $`\Omega_3\cdot\omega`$** (the lemmas without FRAG proved; the rest proved by transfer, given FRAG). PLATEAU-SEG: $`G`$ is constant on
  $`[\Omega_3\cdot a + \zeta^*_{a+1}, \Omega_3\cdot(a+1)]`$, and $`D'`$ has no point there; FIX-SEG: $`\bar Z_{a+1} = \sup_n f_a^n(0)`$ for $`f_a(x) = \psi_{\Omega_2}(\Omega_\omega + \Omega_2\cdot a + x)`$; D-UNC$`^{\mathrm{SEG}}`$: D-UNC for offsets below $`\bar Z_\omega + \Omega_1`$ at bases
  $`\eta \ge \Omega_3`$ or $`\eta \gt \Omega_2\cdot\omega`$; the reading $`R(\Omega_3\cdot a + \zeta_L) = \bar Z_a + R^{(a)}(\zeta_L)`$ and $`R(\Omega_3\cdot\omega) = \bar Z_\omega`$. With these inputs: **R-CAP for every code $`G(\Omega_3+1) \le m \lt G(\Omega_3\cdot\omega+1)`$**,
  CAP-0 for every code below $`G(\Omega_3\cdot\omega+1)`$, and $`r(H(\Omega_3\cdot a)) \le r(H(\Omega_3\cdot a + \bar Z_a))`$ for $`2 \le a \le \omega`$. (The referee: one case of D-UNC, bases in $`[\Omega_2\cdot a, \Omega_2\cdot\omega]`$, is used and not stated;
  it is true and checked. One successor step of the reading must name the clause of PSI-n it uses.)
- **Theorem X17** (proved, given FRAG):

```math
\nu_C \ge X_{17} = \psi_{\Omega_1}(\Omega_\omega + \Omega_3\cdot\omega + \theta_2 + \omega^{G(\Omega_3\cdot\omega+1)+1}\cdot 2),\qquad G(\Omega_3\cdot\omega+1) = \psi_{\Omega_2}(\Omega_\omega + \Omega_3\cdot\omega + \theta_2).
```

So Wilken's claim holds in $`R_2^C`$ on $`[0, X_{17}]`$, both halves, given FRAG, and $`X_{16} \lt X_{17} \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$. §2.2 goes further, to $`X_{18}`$.

- **Open**: the lower-bound side of this tier ($`r(H(\Omega_3\cdot a)) \ge H(\Omega_3\cdot a + \bar Z_a)`$ for $`a \ge 2`$); an InaccPsi formula for the reach in terms of the code.
- The referee's other minor points: cite [W07b] Thm 5.3; drop "with +" from the notation $`\mathrm{lh}_1`$; one header calls a list of inputs "full proofs".

### 2.2 The reading READ: proved on the ordinal side at every $`\Omega_k`$; caps below the code $`G(\hat\zeta_2)`$; $`\nu_C \ge X_{18}`$ given FRAG

$`\mathrm{Sh}`$ is the level shift ($`\Omega_k \mapsto \Omega_{k-1}`$, $`\psi_{\Omega_k} \mapsto \psi_{\Omega_{k-1}}`$); a multiplier $`\zeta`$ is normal if $`G(\zeta)`$ is a normal form; $`\zeta_H`$ is the part of the Cantor normal form of $`\zeta`$ at or above $`\Omega_3`$,
and $`\zeta_L \lt \Omega_3`$ the rest. With $`\gamma = \psi_{\Omega_3}(\Omega_\omega + \theta_3\cdot(\omega+1))`$:

```math
\hat\zeta_0 = \theta_3\cdot(\omega+1) + \gamma\cdot\omega,\qquad \hat\zeta_1 = \theta_3\cdot(\omega+1) + \varphi(\omega, \gamma+1),\qquad \hat\zeta_2 = \theta_3\cdot(\omega+1) + \varphi(\omega, \gamma+1)\cdot\omega,
```

with readings $`G(\omega+1)\cdot\omega`$, $`\tau_{\mathrm{LH}}`$, $`\tau_{\mathrm{LH}}\cdot\omega`$, and $`\Omega_3 + 1 \lt \theta_3 \lt \hat\zeta_0 \lt \hat\zeta_1 \lt \hat\zeta_2 \lt \Omega_4`$ (checked).

- **READ restated** (statement; the referee's correction of §1.4 applied, **2 reviews**). On constant-free normal multipliers, $`R(\zeta) = \mathrm{Sh}(\zeta)`$ for $`\zeta \lt \Omega_3`$, and $`R(\zeta) = f(\mathrm{Sh}\,\zeta_H) + \mathrm{Sh}(\zeta_L)`$ for $`\zeta \ge \Omega_3`$.
- **The ordinal side, at every $`\Omega_k`$ and at $`\Omega_\omega`$** (proved, no FRAG; the referee re-derived every proof and tested 1,273 offsets above $`G(\Omega_5)`$, a range the paper did not sample).
  $`\zeta`$ is normal iff $`\mathrm{Sh}(\zeta) \in D'`$ (ALIGN); $`R`$ is strictly increasing and maps the constant-free normal multipliers in $`[\theta_2, \Omega_\omega)`$ onto the constant-free offsets in $`[P, P')`$; $`R(\Omega_3) = Z`$
  and $`R(\Omega_k) = G(\Omega_{k-1})`$ ($`k \ge 4`$), each the supremum of the readings below it; $`R(\zeta) \lt G(\Omega_k) \le G(\zeta)`$ for normal $`\zeta \in [\Omega_k, \Omega_{k+1})`$; and $`R(\Omega_\omega) = G(\Omega_\omega) = P'`$. So the reading stays below the code
  at every $`\zeta \lt \Omega_\omega`$ and meets it at $`P'`$. Also $`G`$ is constant on $`[\psi_{\Omega_k}(\Omega_\omega + \Omega_k), \Omega_k]`$ ($`k \ge 3`$), and D-UNC holds for offsets below $`G(\Omega_k)`$ at bases $`\ge \Omega_k`$.
- **The caps** (proved by transfer, given FRAG). A cap for the segment of $`\zeta`$ follows from the caps of the earlier segments and pins at the exponents of the Cantor normal form of
  $`R(\zeta)`$; pins exist at every exponent $`\le \tau_{\mathrm{LH}}`$ (a new separation lemma at $`\tau_{\mathrm{LH}}`$ itself). So **R-CAP for every code $`G(\Omega_3+1) \le m \lt G(\hat\zeta_2)`$, and CAP-0 for every code below $`G(\hat\zeta_2)`$**.
  From $`\hat\zeta_0`$ on this uses the identity of PHI-COMM (§2.1), which the paper cites as the open review item of §1.1.
- **Theorem X18** (proved, given FRAG; with PHI-COMM of §2.1, 1 review each):

```math
\nu_C \ge X_{18} = \psi_{\Omega_1}(\Omega_\omega + \hat\zeta_2 + \omega^{G(\hat\zeta_2)+1}\cdot 2),\qquad G(\hat\zeta_2) = \psi_{\Omega_2}(\Omega_\omega + \hat\zeta_2).
```

So **Wilken's claim holds in $`R_2^C`$ on $`[0, X_{18}]`$, both halves, given FRAG**, $`\nu_S \ge X_{18}`$, and $`X_{17} \lt X_{18} \lt \psi_{\Omega_1}(\Omega_\omega + \Omega_4) \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ ($`X_{17} \lt X_{18}`$ since $`\hat\zeta_0 \gt \theta_3 \gt \Omega_3\cdot\omega\cdot 2`$). Without PHI-COMM the paper
proves $`\nu_C \ge \psi_{\Omega_1}(\Omega_\omega + \hat\zeta_0 + \omega^{G(\hat\zeta_0)+1}\cdot 2)`$, also above $`X_{17}`$. LOW now needs self-crossing long restarts with codes in $`[G(\hat\zeta_2), P')`$ and $`\eta \ge \hat\zeta_2`$. **Conditional, not counted**: under
not-LOW, $`\nu_C \ge \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{G(\hat\zeta_2)+1})`$ (this raises $`Y_1`$ again).

- **Not proved** (the referee's blocking points; none is on the line to $`X_{18}`$; the twenty-fifth round proves the restricted sharp form, makes the second point exact and repairs the third, [SHIFT5.md](SHIFT5.md) §1.1):
  - The sharp form for $`\Omega_3 \le M \le \hat\zeta_1`$, "$`r(\lambda) \ge H(\eta_\lambda + R(M))`$ iff $`m_\lambda \ge G(M)`$", is **false** at $`M = \Omega_3 + 1`$ (given FRAG): $`u = H(\Omega_3)`$ has the code $`G(\Omega_3) \lt G(\Omega_3+1)`$, but
    $`r(u) \gt H(\Omega_3 + Z + 1)`$ by R-U (§1.4). The direction "if" holds; "only if" holds when $`R(M)`$ is a multiple of $`\Omega_1`$.
  - "Pins at every code below $`P'`$ give READ at every $`\Omega_k`$". For an exponent above $`G_2`$ the separation in the needed form is false (a restart with code $`G_2`$ is long and reaches
    past its own region), and such exponents occur from $`\theta_3\cdot\omega^2`$ on. So past $`\theta_3\cdot\omega^2`$ READ needs a new upper-bound rule with a target in a far region.
  - The dichotomy at $`H(\Omega_4)`$ (CAP-0 there, or cofinally many crossings below it). The lower bound $`r(H(\Omega_4)) \ge H(\Omega_4 + \tau_{\mathrm{LH}})`$ holds.
- **Where it stops**: $`\hat\zeta_2`$ needs a pin at the exponent $`\tau_{\mathrm{LH}} + 1`$, and the known lower bounds at the codes $`\tau_{\mathrm{LH}}`$ and $`\tau_{\mathrm{LH}} + 1`$ coincide. (The referee: what is missing is an
  upper bound for the reach at $`\tau_{\mathrm{LH}}`$. EXACT-CL\* of §2.1 now gives it, $`r = \varphi(\omega, \delta+1)\cdot\omega`$; no paper derives the pin at $`\tau_{\mathrm{LH}} + 1`$ from it yet.) (The referee of the twenty-fifth round: the coincidence of the lower bounds is only a remark, valid for targets up to $`\mathrm{lh}_1(\varphi(\omega, \delta+1))`$; the pin exists, [SHIFT5.md](SHIFT5.md) §1.1.)
- The referee's minor points: one case split in the proof of X18 is wrong, and the conclusion holds by a least-multiple argument; the tail bases need $`\kappa \ge H(\Omega_3)`$; the pins at
  points of the lh-shift need H-RC there; two suprema at gap tops with constants are asserted by analogy; wording; sampling.

### 2.3 The shapes of $`\Phi_3`$: all 3,166

Notation of §1.3.

- **The minor points of the twenty-third-round review are applied** (**2 reviews**).
- **The last 3 (class III, $`t = 1`$; proved).** The input grows by a chain of $`n+1`$ nodes with the label $`(2,0)`$ (INPUT-CC); each chain node becomes one layer $`\Phi(t)`$ of the program,
  and lh steps down two layers at a time, so the members are the $`\Phi^k(\mathrm{core})`$ with $`k \equiv n`$ (mod 2): this is the split between even and odd $`n`$ of §1.3. Tools: an engine with a chain marker and a
  nest marker of unknown depth (CC-OPQ; five hook lemmas, each checked by hand against the program); the family lemma FAM-T, $`\mathrm{lh}(\Phi^k) = \Phi^k + \Phi^{k-2}`$ for $`k \ge 3`$; the shape theorem
  CC-SHAPE (for $`n \ge 9`$, a fixed template of 14–16 nodes plus the member block); the derivation lemma **SSC-G**: members $`w_k`$ with $`w_k \le_1 w_k + w_{k-1}`$, built below $`\zeta(g)`$ by R1 at
  $`\zeta(g) \le_1 \zeta(g)\cdot 2`$ again and again, which needs only one T-node $`g`$ with $`g + g \le \mathrm{reach}_T(g)`$ (REFL needed about $`n/2`$ of them); TRANSFER-SSC.
- **The tally** (checked; $`3{,}166 = 3{,}163 + 3`$):

| class | matrices | proved for every $`n`$ | open |
|---|---|---|---|
| I | 581 | 581 | 0 |
| SUM | 603 | 603 | 0 |
| ROOT | 635 | 635 | 0 |
| III | 1,347 | 1,347 | 0 |
| all | 3,166 | 3,166 | 0 |

- **UNIF-FS on the sample** (proved, given the accepted tallies): $`\iota(\mathrm{conv}\,A[n]) \lt \iota(\mathrm{conv}\,A)`$ for every sample matrix $`A`$ and every $`n`$.
- **Open**: the step for all standard trio matrices below SRO. It needs a classification with engines uniform in $`A`$, markers for growth patterns not in the sample (a chain over a chain,
  nests of nests, period $`\gt 2`$), and a rule that builds the derivation from the shape (now the data are found by search); for the lower bound also MU$`_{\mathrm{SRO}}`$. The route through fundamental
  sequences of InaccPsi is not available.
- The referee's minor points: TRANSFER-SSC needs the fixed nodes and the final segment to stay the same for all $`n`$ (true, checked, to be stated); two remarks read as proved impossibility
  results (only the search failed); out-of-date line numbers in comments; one note on a checksum file.

### 2.4 Native codes past $`\psi_{\Omega_1}(\Omega_\omega\cdot\omega)`$

Notation of [SHIFT3.md](SHIFT3.md) §1.2 (stages $`T \lt \omega^\omega`$, $`\Xi[k]`$, $`Z[k]`$) and §1.2. $`\Xi^T`$ is the end point of the stage $`T`$, and $`Z^{[1,M]}`$ is the bound of IDX$`^p`$ for the stages $`1, \dots, M`$.

- **The minor points of the twenty-third-round review are applied** (**2 reviews**): the counting rule PSI-θ covers every normal argument below $`\Omega_\omega + \Omega_2^{\theta_2+1}`$, so the forms and CNST$`^\vartheta`$ up to
  $`\hat G`$ follow (they are not extrapolations); the CNST test now runs; the three short places of EN=EX are written out; PUSH cites GEN-EXT ([BREAK.md](BREAK.md) §2) in place of GEN⁺.
- **Theorems PSI$`^T`$, CNST$`^T`$, EN=EX$`^T`$** (proved, at the standard of substitution lists under which PSI-n was accepted; EN=EX$`^T`$ cannot be checked numerically). For every stage $`T \lt \omega^\omega`$ the
  stage-$`T`$ systems are the systems of PSI-n with a new top unit $`\Omega_{n+1}`$, which carries the indices of the stages below $`T`$ and the constant-free index $`\psi_{\Omega_{n+2}}(\Omega_\omega\cdot T)`$. The counting rule
  computes every $`\psi_{\Omega_j}(\beta)`$ with $`\beta \lt \Omega_\omega\cdot T + \Omega_{n+1}^{\psi_{\Omega_{n+2}}(\Omega_\omega\cdot T)+1}`$, the parameters are read from the term, and the enumeration-pair and exact-level systems agree. The case
  $`T = 1`$ is PSI$`^W`$, CNST$`^W`$ and EN=EX for the stage systems, open in §1.2.
- **Names** (proved): $`\Xi^T = \psi_{\Omega_2}(\Omega_\omega\cdot(T+1))`$, and $`\Xi[\omega] = \psi_{\Omega_2}(\Omega_\omega\cdot\omega^\omega)`$, the conjectured name of [SHIFT3.md](SHIFT3.md) §1.2. The other conjectured name there,
  $`\theta_{\Xi[\omega]}(0) = H(\Xi[\omega])`$, is **false**.
- **The native bounds** (proved; chain length 3; resting on GEN-EXT). The map $`\eta \mapsto \psi_{\Omega_2}(\Omega_\omega + \theta\cdot\eta)`$ is admissible on every $`\eta \lt \Omega_\omega\cdot\omega`$ with $`\eta \in C_\eta`$, so natively

```math
\iota(\mathrm{CH}_3) \ge Z^{[1,M]} \gt \theta_{\Xi^M}(0) \ge \psi_{\Omega_1}(\Omega_\omega\cdot(M+1))\ (1 \le M \lt \omega),\qquad \iota(\mathrm{CH}_3) \ge Z[0] \gt \theta_{\Xi[0]}(0) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\omega).
```

$`M = 1`$ is the bound past $`\psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ asked in §1.2. **These are the first native bounds above the known non-native ones** ($`\iota(\mathrm{CH}_3) \gt \nu_C \ge X_{18}`$ given FRAG, and
$`X_{18} \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$).

- **Labels** (the referee's point). GEN-EXT was proved by running the proof of GEN on a larger domain, the kind of proof that gave GEN⁺ the label "transfer" ([THETA.md](THETA.md) §1).
  These pages count GEN-EXT as proved (1 review, [BREAK.md](BREAK.md) §2) and GEN⁺ as its case ([README.md](README.md) §4), so the bounds above are counted as proved, and PUSH of §1.2 is proved.
- **Conditional, not counted** (now proved, [SHIFT5.md](SHIFT5.md) §1.3): given GEN past $`\Omega_\omega\cdot\omega`$, natively $`\iota(\mathrm{CH}_3) \ge \theta_{\Xi[\omega]}(0) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\omega^\omega)`$.
- **Open**: GEN past $`\Omega_\omega\cdot\omega`$ (the extraction step of GEN-EXT seemed to fail once $`\Omega_\omega`$ is absorbed into $`P\cdot\eta`$; it does not, and GEN holds for every η, [SHIFT5.md](SHIFT5.md) §1.3); native stages $`\ge \omega^\omega`$ and uncountable stage indices; $`\mathrm{CH}_2`$ past $`\Theta_1`$.
- The referee's minor points: one side claim (a parameter set is $`\{1\}`$, not empty) is false and harmless; at a limit stage one case of the proof is empty and closes directly;
  the paper's own test never reached limit stages (the referee's does); two reasons are stated loosely. (The referee of the twenty-fifth round: the proof of PUSH uses $`P\cdot\Omega_k = \Omega_k`$, false for $`k = 1`$; harmless, $`k \ge 2`$ suffices.)

### 2.5 Status after the twenty-fourth round

The twenty-fifth to thirty-seventh rounds changed this status; see [SHIFT5.md](SHIFT5.md) §1.4, §2.4, [SHIFT6.md](SHIFT6.md) §1.4, §2.4, §3.4 , [SHIFT7.md](SHIFT7.md) §1.4, §2.4, §3.4, [SHIFT8.md](SHIFT8.md) §1.4, §2.4, [SHIFT9.md](SHIFT9.md) §1.4, §2.4 and §3.4.

- Wilken's claim in $`R_2^C`$: both halves hold on $`[0, X_4]`$ without FRAG, and on $`[0, X_{18}]`$ given FRAG ($`[0, X_{16}]`$ with 2 reviews); the core half holds on $`[0, \nu_C]`$. No InaccPsi upper
  bound for $`\nu_C`$: (P) at a named pair stays open.
- Reaches: exact (given FRAG) for every short restart with $`\tau \lt G_2`$ and every long restart with $`D, m_0 \lt G_2`$, as the $`c`$-th closed point of a block; GAP$`_j`$ for every $`j`$.
- The lower-bound program below $`\theta_0`$: the step below SRO holds for every $`n`$ on all 3,166 sample matrices; natively $`\iota(\mathrm{CH}_3) \gt \psi_{\Omega_1}(\Omega_\omega\cdot\omega)`$, above every known
  non-native bound, and $`\iota(\mathrm{CH}_2) \ge \Theta_1`$.
- Upper bounds: still none by an InaccPsi term for $`\iota(\mathrm{CH}_k)`$, $`m_F`$, $`x_F`$, $`C^*_3`$ or $`\nu_C`$.
- $`\nu_C = \nu_S`$: LOW is not decided; CAP-0 holds for every code below $`G(\hat\zeta_2)`$ (given FRAG). Left: (P1), (D1b), (E4).

### 2.6 Checks of the twenty-fourth round

Each run was under 60 seconds; none is a proof.

- §2.1. Names, normal forms, membership in $`D'`$ and the order $`X_{15} \lt X_{16} \lt X_{17} \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ in Python and Lean (green); the plateaus, the reading, the covering lemma and
  D-UNC$`^{\mathrm{SEG}}`$ on 792 offsets; ENUM in an abstract model (a variant without the root fails 2,153 times): 0 violations. The referee: D-UNC at 7 bases below $`\Omega_3`$ on 645 offsets,
  FIX-SEG on 579 terms, ENUM in an independent model on 12,000 samples: 0 violations; the Lean rerun is green with the same output.
- §2.2. ALIGN, the margin and the order on 1,054 normal multipliers, ONTO on 691 offsets, D-UNC on 703 cases (268 negative), the covering on 187 codes: 0 failures; Lean green.
  The referee: own generators with arbitrary arguments (the shift on 490,000 pairs, ONTO on 1,515 offsets, the covering with constants on 2,680 codes, the exponents below $`\hat\zeta_2`$): 0 failures;
  an own Lean file and a rerun of the paper's, both green.
- §2.3. The templates agree with the program up to $`n = 24, 25`$; 324 hook values; an independent checker accepts all 48 solutions; 1,008 mutated solutions are rejected; 0 successes on 598 false
  pairs. The referee: the templates for $`n = 17, \dots, 71`$ (165 of 165), a third checker written from the statement (126 levels), 1,808 mutants rejected, 62 false pairs, FAM-T on 3,000 random
  cases: 0 failures. No Lean file.
- §2.4. The rule against the InaccPsi order at the stages 1, 2 ($`12 \times 11{,}990 + 4 \times 183{,}612`$ pairs) and CNST$`^T`$ in 10,560 tests: 0 mismatches; Lean green. The referee: the limit stages
  $`\omega`$, $`\omega+1`$, $`\omega\cdot 2`$, $`\omega^2`$ ($`4 \times 11{,}990`$ pairs, $`4 \times 1{,}120`$ CNST tests) and the inputs of the native bounds on 120 samples (4,920 tests): 0 failures; the Lean rerun is green.

### 2.7 Open

The twenty-fifth to thirty-seventh rounds changed this list; the current list is [SHIFT9.md](SHIFT9.md) §3.6.

- Upper bounds: (P) and (Q′) at one named pair for $`\nu_C`$. (P) needs the caps past $`G(\hat\zeta_2)`$ and a lower bound at code $`P'`$; (Q′) needs the isominimal patterns of $`L(\omega)`$.
  Bounds for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$, $`f_0`$, $`m_3`$, $`c_0`$.
- The claim above $`X_{18}`$ given FRAG: the pin at the exponent $`\tau_{\mathrm{LH}} + 1`$; past $`\theta_3\cdot\omega^2`$ an upper-bound rule with a far target; the lower-bound side of the tiers above $`\Omega_3`$;
  READ past $`\hat\zeta_2`$ (the plateau at $`\Omega_4`$); long restarts with $`D \ge G_2`$.
- The first inaccessible: GEN past $`\Omega_\omega\cdot\omega`$; native stages $`\ge \omega^\omega`$, uncountable stage indices, $`\Omega_{\omega+1}`$; $`\mathrm{CH}_2`$ past $`\Theta_1`$; the step for all standard matrices below SRO.
- $`\nu_C = \nu_S`$: LOW (CAP-0 at codes in $`[G(\hat\zeta_2), P')`$), LOW$`^\omega`$, (P1), TC⁺ for long restarts at offsets $`\ge P'`$, (D1b), (E4).
- Names: $`R(\Theta_{d\omega})`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$; an InaccPsi formula for the reach in terms of the code; names beyond $`X_{18}`$; the rest of
  [COVER.md](COVER.md) §9.
