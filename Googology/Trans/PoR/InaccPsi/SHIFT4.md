[← Back](README.md) | [English](SHIFT4.md) | [Japanese](SHIFT4-ja.md)

# $`R_2^+`$, the twenty-third round: $`\nu_C \ge X_{16}`$ given FRAG, closed reaches, the plateau at $`\Omega_3`$, the shapes of $`\Phi_3`$, and native codes past $`\upsilon^*`$

This page continues [SHIFT3.md](SHIFT3.md) (§2 there is the twenty-second round); §1 is the twenty-third round. The status words are those of [README.md](README.md) §3: **proved** means that
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
  fixes the range, $`\Theta_\nu(\varphi(\omega, G(\omega+1)+1)) = \varphi(\omega, \delta_\nu+1)`$, is stated without proof.) **Conditional, not counted**: the same formula in the blocks $`j \ge 2`$, given the open
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

- **Open**: GAP$`_j`$ ($`r(\nu) \lt \delta_{j+1}`$ for $`\tau_\nu \in [\varphi(\omega, G(\omega j+1)+1), G(\omega j+2))`$) and ROOT-CL (for a principal $`x`$, the least principal $`\alpha \gt \delta_j`$ with $`\alpha \le_1 x`$ lies in the closure of $`x`$),
  which would give exact reaches on all of $`[\theta, G_2)`$ (conjecture EXACT-CL\*: $`r(\nu)`$ is the $`o_\nu(\tau_\nu)`$-th closed point above $`\delta_\nu`$); $`D`$ or $`m_0`$ in those gaps; the codes past §1.4;
  (P), (Q′), and an InaccPsi upper bound for $`\nu_C`$.
- The referee's other minor points: "the literal rule is false" must say "given FRAG"; one step of CEIL is only checked (the referee gives a two-line proof); one line of P-LOW
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
- **Open**: PSI$`^W`$ (the counting rule over the base $`\Omega_\omega`$ at every level; checked on $`4 \times 11{,}990`$ pairs), EN=EX for the stage systems of [SHIFT3.md](SHIFT3.md) §1.2, and CNST$`^W`$;
  given the three, natively $`\iota(\mathrm{CH}_3) \gt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ (conditional, not counted). Also open: $`\mathrm{CH}_2`$ past $`\Theta_1`$, and whether $`\theta_{\Xi'_\omega}(0) \gt \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+\Omega_2})`$.
- The referee's minor points: the forms and CNST$`^\theta`$ are used up to $`\hat G`$, past the range where they were stated (valid, but it should be said); one test did not stop because a
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

- **Left** (3, class III, $`t = 1`$; open). The input grows by a chain with the constant label $`(2,0)`$; $`\mathrm{conv}(A[n])`$ has about $`n/2`$ nested members, each the last kid of the next, with a split
  between even and odd $`n`$. Needed: a chain marker whose hook uses two chain nodes per nesting, a recursive symbol for the members, a family lemma, and a derivation for a chain of
  sums of a node with itself (outline). REFL works at $`n \le 4`$ for 2 of the 3 (checked) and fails at $`n = 5, 6`$.
- The referee's minor points: FAM-S is proved up to the member $`K-2`$, and the member $`K-1`$ is one direct computation; one wording point in REFL; one citation; one note on a checksum
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
- **LOW is not decided.** Conjecture READ (a cap reading of the code segment of every normal multiplier below $`\Omega_\omega`$, with the supremum at each plateau top) would give CAP-0
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
- The referee's minor points: the onto statement of the reading is misstated (the one used is an earlier one); the inventory of the tools at level 2 must add the θ-tier and the θ⁺
  tier; the analogue at level 2 must be labelled conditional; the hull lemma's hypothesis holds for every $`g`$ and should be said; the pin at the exponent $`Z`$ needs the region
  transport; the use of LEVEL-SHIFT and UNIF past their earlier range needs the rebasing written out; one cosmetic point.

### 1.5 Status after the twenty-third round

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

- Upper bounds: (P) and (Q′) at one named pair for $`\nu_C`$. (P) needs the caps past §1.1 and §1.4 and a lower bound at code $`P'`$; (Q′) needs the isominimal patterns of $`L(\omega)`$.
  Bounds for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$, $`f_0`$, $`m_3`$, $`c_0`$.
- The claim above $`X_{16}`$ given FRAG: GAP$`_j`$ and ROOT-CL (exact reaches on $`[\theta, G_2)`$); long restarts with $`D \ge G_2`$; the tier with $`\eta \ge \Omega_3`$ and codes $`\ge G(\Omega_3+1)`$ (multiplier
  forms with $`\Omega_3`$ as a unit, the reading at each plateau top, pins at exponents $`\ge G_2`$).
- The first inaccessible: native codes past $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+\Omega_2})`$ (PSI$`^W`$, EN=EX for the stage systems, CNST$`^W`$); $`\mathrm{CH}_2`$ past $`\Theta_1`$; stages $`\ge \omega^\omega`$, uncountable
  stage indices, $`\Omega_{\omega+1}`$; UNIF-FS below SRO on the 3 matrices of §1.3.
- $`\nu_C = \nu_S`$: LOW (CAP-0 at codes in $`[G(\Omega_3+1), P')`$, conjecture READ), LOW$`^\omega`$, (P1), TC⁺ for long restarts at offsets $`\ge P'`$, (D1b), (E4).
- Names: $`R(\Theta_{d\omega})`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$; the exact reaches of the long restarts with $`D \ge G_2`$; names beyond $`X_{16}`$; the rest of
  [COVER.md](COVER.md) §9.
