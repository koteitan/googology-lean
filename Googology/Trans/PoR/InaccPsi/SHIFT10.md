[← Back](README.md) | [English](SHIFT10.md) | [Japanese](SHIFT10-ja.md)

# $`R_2^+`$, the thirty-eighth to fortieth rounds: the window rule one step up, the first long restarts of the skeleton, the criterion as an induction, marked sources, the exact long reaches (a fatal point and a partial repair), capacities per unit, and FRAG in Lean

This page continues [SHIFT9.md](SHIFT9.md) (§3 there is the thirty-seventh round); §1 is the thirty-eighth round, §2 the thirty-ninth and §3 the fortieth. The status words are those of [README.md](README.md) §3: **proved** means that
an independent referee found the result proved with no fatal or blocking point. A statement with a fatal or blocking point against it is listed under **Not proved**.
A certificate counts only when it was replayed. A result that the referee calls only a restatement of something known, or of the target, is not counted as progress.

**Later (the fortieth round, §3):** the frontiers of §1 and §2 ($`Z^\varepsilon`$, $`Z^\Lambda`$, and $`[0, Z^\varepsilon)`$ in $`R_2^S`$) rest on $`\nu_C = \nu_S = L(\omega+1)`$, which is **not proved as written** (the chain to it uses exact long reaches at codes where the old value is false); so are they. Their parts that use no reach (the code side, the schemata of §1.2 and §2.2, the native codes of §1.3 and §2.3) stand. Given FRAG, the claim is proved in $`R_2^C`$ on $`[0, X_{21}]`$ (§3.4).

## 1. The thirty-eighth round

Three papers (2026-10), each refereed once: a paper on the window rule one step up and the first long restarts of the skeleton (§1.1), a paper on (E), the segment of $`\delta''_1`$ and
the criterion as an induction (§1.2), and a paper on native codes (§1.3). A result in this section has 1 review unless a count is given. The step of the claim from
$`L(\theta'_2\cdot(\omega+1)+G''(\omega+1)\cdot\omega)`$ to $`Z^\varepsilon`$ (defined below) is proved in the first two papers independently, by two different readings of the codes above $`G''(\omega+1)`$, so it has
**2 reviews**; so does the step of the claim in $`R_2^S`$ from $`Z^\Gamma`$ to $`Z^\varepsilon`$. The minor points of the reviews of [SHIFT9.md](SHIFT9.md) §3.1, §3.2 and §3.3 are applied by the three papers, and their
referees checked each repair (**2 reviews**, except where a new point is noted). None of the papers uses Wilken, JSL 72 (2007), Carlson, AML 38 (1999), or Wilken, AML 45 (2006) (the
referees checked this). Papers cited: in §1.1 Wilken, "Σ₁-elementarity and Skolem hull operators" (APAL 145, 2007; L.2.1, Def 4.1, Thm 2.2), Carlson 2009 (Def 5.3, L.5.5, L.5.7) and Wilken's "A glimpse of
Σ₃-elementarity" (L.21.10), besides refereed stages; in §1.2 Carlson–Wilken, "Tracking chains of Σ₂-elementarity" [CW12b], https://www.sciencedirect.com/science/article/pii/S0168007211001199 (Prop 7.1,
Prop 7.4, the remark after it, L.7.5, and the proof of Thm 7.9 read as a pattern), and Carlson 2009 (Def 5.3, Def 5.4, L.5.5, L.5.7); no paper in a proved step of §1.3, which does not use FRAG. No
Lean file was added: the ordinal inputs of §1.1 and §1.2 were checked with Lean files that only compare terms (`#eval`, no theorem; green, identical to Python, and identical in the referees'
rechecks), and the referee of §1.3 checked the repaired descent of PER-KIND with a separate Lean file (green, only the standard axioms, no `sorry`); these count as checks. Levels are numbered as
in [SHIFT8.md](SHIFT8.md) (one higher than in the papers). "Given FRAG" is as there.

Notation (as in [SHIFT9.md](SHIFT9.md) §3): $`L(e) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + P'\cdot e)`$, $`\theta'_2 = \psi_{\Omega_3}(\Omega_\omega\cdot 2)`$, $`G''(\zeta) = \psi_{\Omega_2}(\Omega_\omega\cdot 2 + \theta'_2\cdot\zeta)`$, now for every ordinal $`\zeta`$ (with
$`\theta'_2\cdot\zeta`$ the sum of the $`\omega^{\theta'_2+a}`$ over the Cantor normal form summands $`\omega^a`$ of $`\zeta`$), so $`G''(\omega^2) = \psi_{\Omega_2}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+2})`$. For a restart $`b = L(\lambda'')`$
of the skeleton: $`\tau''_j = L(\lambda''+\omega\cdot j)`$, $`\delta''_j = L(\lambda''+\omega\cdot j+1)`$; its blocks are $`(b, \delta''_1]`$ and $`(\delta''_j, \delta''_{j+1}]`$, and the gap of $`\delta''_j`$ is $`[\delta''_j, L(\lambda''+\omega\cdot j+2))`$.
The two frontiers of this round are

```math
Z^{\mathrm{LL}} = L(\theta'_2\cdot\omega^2+\omega^{G''(\omega^2)^2}) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+2} + \omega^{\omega^{G''(\omega^2)\cdot 2}}),
```

```math
Z^\varepsilon = \varphi(\omega, \delta^\varepsilon+1),\qquad \delta^\varepsilon = L(\theta'_2\cdot(\omega+1)+\varepsilon_{G''(\omega+1)+\omega}+\omega+1) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+1} + \theta'_2 + \varepsilon_{G''(\omega+1)+\omega} + \omega^{P'+1} + P').
```

Here $`\delta^\varepsilon`$ is the point $`\delta''_1`$ of the restart $`L(\theta'_2\cdot(\omega+1)+\varepsilon_{G''(\omega+1)+\omega})`$, whose code is $`\varepsilon_{G''(\omega+1)+\omega}`$, and $`Z^\varepsilon \lt L(\theta'_2\cdot\omega^2) \lt Z^{\mathrm{LL}}`$. After the thirty-ninth round the step from $`L(\theta'_2\cdot\omega^2)`$ to $`Z^{\mathrm{LL}}`$ is not proved as written (§2.1).

### 1.1 The window rule one step up and the first long restarts: the claim up to $`Z^{\mathrm{LL}}`$, given FRAG

- **The repairs of the review of [SHIFT9.md](SHIFT9.md) §3.1** (m1–m6; **2 reviews**), and the notation $`\Phi^W_0 := \Omega_1`$ of the review of §3.2 there (m4): with it the down map of §3.2 there is the
  tier map $`\mathrm{Tr}_0`$ restricted to the $`\Gamma`$ tier. The referee: the general form of m1 (TAIL-DOM, "the constants of the code lie in the domain at every tail") is false at the tails below a
  countable constant of the code (a counterexample), and true at the tails above them, which is what every proof uses (new minor point m2; 1 review).
- **TIER$`_\zeta`$ and READ″$`_\zeta`$** (proved, no FRAG; the reading by transfer). The tier map with $`\theta'_2\cdot n`$ replaced by $`\theta'_2\cdot\zeta`$ is an order isomorphism of the codes in $`[\Omega_1, P')`$ onto the
  codes in $`[G''(\zeta), G''(\zeta+1))`$ for every countable $`\zeta`$ and for $`\zeta = \Omega_1`$. The referee: "for every ordinal $`\zeta`$" is false; for $`\zeta = P_3 = \psi_{\Omega_2}(\Omega_\omega\cdot 3)`$ and some other
  uncountable $`\zeta`$ the term $`G''(\zeta)`$ is not a normal form (m1); only countable $`\zeta`$ and $`\Omega_1`$ are used. At every point $`b = L(\lambda'')`$ and for every countable $`\zeta \lt b`$: $`o_b(G''(\zeta)) = L(\lambda''+1+\zeta)`$,
  the countable $`\zeta`$ with $`G''(\zeta)`$ in the domain at $`b`$ are exactly those below $`b`$, and $`G''(\Omega_1)`$ reads $`L(\lambda''+b)`$. The domain criterion of [SHIFT9.md](SHIFT9.md) §3.1 holds up to the index of $`Z^{\mathrm{LL}}`$.
- **The closed points of a whole gap** (ROOT″, LC-FORM″, ENUM″, ROOT-LOC″, TRANS-K″; proved by transfer, no FRAG). For $`d = \delta''_j = L(e)`$, call $`y \in [d, L(e+1))`$ closed relative to $`d`$ if every
  $`\alpha \in (d, y]`$ has $`\mathrm{lh}(\alpha) \le y`$ ($`\mathrm{lh}`$ the reach in $`R_2^S`$). Let $`\alpha_x`$ be the least $`\alpha \in (d, x]`$ with $`\alpha \le_1 x`$. Then

```math
E''_d(c) = c\ \ (c \lt d\cdot\omega),\qquad E''_d(c) = \mathrm{lh}(\alpha_{\mathrm{lt}(c)}) + (-\alpha_{\mathrm{lt}(c)} + c)\ \ (c \ge d\cdot\omega)
```

  is an order isomorphism of $`[d, L(e+1))`$ onto these closed points. This is ENUM of [SHIFT4.md](SHIFT4.md) §2.1 on a whole gap instead of one segment; the referee: its proof uses only the
  interval and persistency properties of $`\le_1`$, which hold on the gap. The roots $`\alpha_x`$ are prefix points of the last $`\upsilon`$-point below $`x`$ or lie in its localization (ROOT-LOC″), so every
  base change on the gap commutes with $`E''_d`$ (TRANS-K″).
- **Pins over a whole region** (INDEX″, L-PIN″, FAR-PIN″$`^{\mathrm{reg}}`$, PAT-CL″, BLOCK″$`^b`$; proved by transfer, given FRAG). The author corrected a first draft of INDEX″ (the images of a long restart
  that crosses regions need not stay in its own region); the restated form is proved. The referee: L-PIN″ and FAR-PIN″ need the next block in the pattern when the set meets the gap of a point
  $`L`$ of the last block met, so they are not proved as stated there; every use avoids that case (m3).
- **Theorem EXACT-CL″\*, the window rule one step up** (proved by transfer, given FRAG; with $`\kappa_0`$ chosen above the countable constants of the code, m2). Let $`I''_1 = [0, G''(\omega+2))`$,
  $`I''_j = [G''(\omega\cdot(j-1)+2), G''(\omega\cdot j+2))`$ for $`j \ge 2`$, $`\mathrm{Lo}_1 = 0`$, $`\mathrm{Lo}_j = L(\lambda''+\omega\cdot(j-1)+2)`$. Every restart $`L(\lambda'')`$ of the skeleton whose code (or π-code) $`c`$ lies in $`I''_j`$ has

```math
r(L(\lambda'')) = E''_{\delta''_j}(\delta''_j + (-\mathrm{Lo}_j + o_b(c))).
```

  So every code below $`G''(\omega^2)`$ has an exact reach, inside the gap of $`\delta''_j`$; the code $`G''(\omega+2)`$ reaches $`\delta''_2`$. **NO-NAIVE″**: at the code $`\omega^{G''(\omega+1)+\omega}`$ the reach is
  $`\omega^{\delta''_1+\omega}+1`$, not $`\delta''_1 + o_b(c)`$. The outline of [SHIFT9.md](SHIFT9.md) §3.1 (codes up to $`G''(\omega+1)\cdot\omega`$) is the case $`j = 1`$ with $`c \lt G''(\omega+1)\cdot\omega`$. Theorem C$`^\Lambda`$: the
  claim holds in $`R_2^C`$ on $`[0, L(\theta'_2\cdot\omega^2)]`$, $`L(\theta'_2\cdot\omega^2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+2})`$, both halves.
- **The first long restarts** (LONG″-$`G''(\omega^2)`$, PIN-ALL″, TOP-REG-FAR″, LB″, EXACT-LONG-CL″\*, CROSSED″; proved by transfer, given FRAG). The first long restart $`L(\theta'_2\cdot\omega^2)`$, with
  code $`G''(\omega^2)`$, reaches $`\delta''_1(\lambda''+\omega^2)+1`$:

```math
r(L(\theta'_2\cdot\omega^2)) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+2} + \omega^{P'+2} + \omega^{P'+1} + P') + 1.
```

  For a code $`c = G''(\omega^2)\cdot D + m_0`$ with $`D, m_0 \lt G''(\omega^2)`$ and $`\nu = L(\lambda''+\omega^2\cdot o_b(D))`$: $`r(L(\lambda'')) = r(\nu) + o_\nu(m_0)`$ if $`m_0 \lt P'`$, and the window rule at $`\nu`$ if
  $`m_0 \ge P'`$. So every code below $`G''(\omega^2)^2`$ has an exact reach. CROSSED″: the regions crossed by a long reach keep their skeleton. The referee: one citation is used outside its
  hypothesis, and the conclusion holds by the other parts of the same lemma (m4); the proofs of EXACT-LONG-CL″\* and CROSSED″ depend on each other across positions, so the induction must run
  along the right bound, not along the codes, as in an earlier refereed proof; run that way it closes (m5). **Later (§2.1): the value $`r(\nu) + o_\nu(m_0)`$ is false for some $`m_0`$ (fatal point F-1 of the second review).**
- **Theorem C$`^{\mathrm{LL}}`$ and the new frontier** (proved by transfer, given FRAG). Below $`Z^{\mathrm{LL}}`$ every restart has an exact reach, and there is no fan apex and no triple nest; so $`\beta_0 \gt Z^{\mathrm{LL}}`$,
  $`T_3^C \gt Z^{\mathrm{LL}}`$, **Wilken's claim holds in $`R_2^C`$ on $`[0, Z^{\mathrm{LL}}]`$**, both halves, and **$`[0, Z^{\mathrm{LL}}) \subseteq \mathrm{Core}(R_2^S)`$, so the claim holds in $`R_2^S`$ on $`[0, Z^{\mathrm{LL}})`$**
  (by the argument of NO-GAP, [SHIFT9.md](SHIFT9.md) §3.2). This passes the frontier $`Z^\Gamma`$ of $`R_2^S`$. One sentence ("the rigidity list holds verbatim") is not checked and not needed: a remark (m6).
  CODES‴ (proved): every restart of the skeleton below $`\psi_{\Omega_1}(\Omega_\omega\cdot 3)`$ has a code below $`\Omega_2`$ or a π-code below $`P_3`$. Wording (m7). **Later (§2.1): Theorem C$`^{\mathrm{LL}}`$ is not proved as written (blocking point B-1 of the second review); Theorem C$`^\Lambda`$ stands.**
- **Not proved.** CROSS″ (the lower bound $`r(b) \ge L(\lambda''+\zeta)`$ for codes $`\ge G''(\zeta)`$, $`\omega^2 \le \zeta \lt b`$): outline (proved in §2.1). Open: exact reaches for codes $`\ge G''(\omega^2)^2`$, the tiers $`G''(\zeta)`$ past
  $`\omega^2`$ as long codes, the codes from $`G''(\Omega_1)`$ on, the landing calculus one level up, CAP-0 and NOT-LOW one level up (first test case $`L(\Omega_3)`$), and CROSS-LIM, FRAG and SHIFT one
  level up for $`\nu_3`$; $`T_3 \le \nu_3`$ is not claimed. Known: $`T_3^C \gt Z^{\mathrm{LL}}`$.

### 1.2 (E): the segment of $`\delta''_1`$, the criterion as an induction, and type F

Words as in [SHIFT9.md](SHIFT9.md) §1.2, §2.2 and §3.2. "Pred₁(α)" is the set of $`\le_1`$-predecessors of $`\alpha`$; "the criterion" is that of [CW12b] Prop 7.4.

- **The repairs of the review of [SHIFT9.md](SHIFT9.md) §3.2** (m1–m9; **2 reviews**). F-REDUCE now says type N, subtype (N0), (N1) or (N2) (m1); the conclusion of the general criterion lemma is
  $`\beta_0 \gt \min(b, \kappa_C)`$ (m2); the Lean file now also covers $`Z^\Gamma`$ (m3); $`\Phi^W_0 := \Omega_1`$ (m4); "the criterion is strictly more than (E)" is withdrawn and the lemma is labelled a restatement
  (m5); the citations of m6, m7 are corrected; the chain of bounds uses $`T_3^C`$, not $`\nu_3`$ (m8); one label (m9).
- **NO-GAP$`^R`$** (proved by transfer, given FRAG). $`\beta_0 \gt Z_R`$ and $`[0, Z_R) \subseteq \mathrm{Core}(R_2^S)`$ with $`f`$ the identity there, where $`Z_R = L(\theta'_2\cdot(\omega+1)+G''(\omega+1)\cdot\omega)`$.
- **SEG-GAP** (proved by transfer, no FRAG). At every base point $`b = L(\lambda'')`$ of the calculus with the first block known, and $`d = \delta''_1(\lambda'')`$, no point of $`(d, \varphi(\omega, d+1)]`$ has a cofinal
  Pred₁, so no $`\lt_2`$-pair has an end there, and $`\beta_0`$ and $`T_3^C`$ are above $`\varphi(\omega, d+1)`$. The referee: correct but short of what the cited results give, namely the same up to the next
  $`\upsilon`$-point of limit index above $`d`$ (m1; the referee's remark, not counted).
- **The segment of $`\delta''_1`$** (READ″$`^\varepsilon`$, LH″, CLOSED″, TOP-REG″$`^{\mathrm{seg}}`$; proved, the readings by transfer). On $`(d, \varepsilon_{d+\omega})`$ the reach in $`R_2^S`$ equals Wilken's reach in $`R_1^+`$, and
  $`\mathrm{lh}(\varepsilon_{d+\omega}) = \varepsilon_{d+\omega}\cdot 2 + 1`$. The referee: the first part is already cited from SKEL$`^\infty`$ ([COVER.md](COVER.md) §5.1), for the whole segment of $`d`$ (m2); a remark labelled
  "not used" is used, and holds (m3).
- **Theorem EXACT-CL″$`^\varepsilon`$** (proved by transfer, given FRAG). Write $`\sigma_b`$ for the reading of the codes over the atom $`G''(\omega+1)`$ ($`G''(\omega+1) \mapsto \delta''_1`$,
  $`\varepsilon_{G''(\omega+1)+k} \mapsto \varepsilon_{\delta''_1+k}`$, constants $`k \mapsto o_b(k)`$) and $`\mathrm{LHF}''(y) = \mathrm{lh}(\mathrm{lt}(y)) + (-\mathrm{lt}(y) + y)`$ (the lh-shift of [SHIFT4.md](SHIFT4.md) §1.1, one level up). Every restart
  whose code $`c`$ lies in $`[G''(\omega+1), \varepsilon_{G''(\omega+1)+\omega})`$ has $`r(L(\lambda'')) = \mathrm{LHF}''(\delta''_1 + \sigma_b(c))`$; for example the code $`G''(\omega+1)\cdot\omega`$ reaches $`\delta''_1\cdot\omega`$, the code
  $`G''(\omega+1)^2`$ reaches $`\omega^{\delta''_1\cdot 2} + \delta''_1`$, and the code $`\varepsilon_{G''(\omega+1)+1}`$ reaches $`\varepsilon_{\delta''_1+1}\cdot 2`$. The code $`\varepsilon_{G''(\omega+1)+\omega}`$ reaches $`\varepsilon_{\delta''_1+\omega}\cdot 2 + 1`$. These
  reaches agree with §1.1 (NO-NAIVE″ included), so they have two proofs. The referee: one case split in a step is wrong, but the argument does not use it (m4).
- **Theorem C$`^E`$** (proved by transfer, given FRAG). Wilken's claim holds in $`R_2^C`$ on $`[0, Z^\varepsilon]`$ and in $`R_2^S`$ on $`[0, Z^\varepsilon)`$, and $`\beta_0 \gt Z^\varepsilon`$, $`T_3^C \gt Z^\varepsilon`$. With §1.1 this step has
  **2 reviews**. The referee: the paper's own description of the region gives more (plausibly up to the end of that region, not proved there; m6).
- **The criterion as an induction** (CRIT-CALCULUS, LOAD, CRIT-IND, LOAD$`^E`$; proved). The criterion is closed under transitivity, suprema, $`\le_1`$-restriction of the right end, and SHIFT (CC1–CC6;
  the remark after [CW12b] Prop 7.4 states two of these without proof). LOAD is the abstract form of the loading step of the proof of [CW12b] Thm 7.9. **CRIT-IND**: if every $`\lt_2`$-pair of $`R_2^C`$ with
  right end below $`b`$ is a SHIFT pair, a loaded pair or a supremum of pairs, then $`\beta_0 \ge \min(b, \kappa_C)`$, the criterion holds at those pairs with right end at most $`\beta_0`$ (m5: in $`R_2^C`$
  the copies used are $`R_2^S`$ facts), and the uniform finite-set test is necessary there. It is a sufficient condition about embeddings and $`\Sigma_1`$-types only, not a reformulation of (E) (the
  referee agrees). **LOAD$`^E`$** (given FRAG): every pair with right end at most $`Z^\varepsilon`$ is a SHIFT pair, so the criterion and the necessity of the uniform test hold there. "LIFT$`_n`$ for every $`n`$"
  is a reformulation of (E): a remark, not counted.
- **Type F** (FAN-UNIFORM, NO-SELF-LOAD; proved). For the left end $`a`$ of an extra pair, the $`R_2^S`$-successors of $`a`$ below $`\beta_0`$ have a largest one $`\delta^*`$ (or none); every separating $`\Sigma_2`$
  witness meets $`[\delta^*, \beta_0)`$; F-CRIT-LOW holds in general; (N0) and type F are the cases with successors, $`\le_1`$-disconnected in (N0) and connected at $`d`$ in type F. NO-SELF-LOAD: a fan
  pair cannot be loaded through its own lower pair (the referee: through any lower pair whose right end is a successor of $`a`$, m7). FAN-LOAD: conjecture.
- **Not proved: where the induction stops** (fatal point F-1 of the review, against one location claim only; no theorem depends on it). The paper said that the first point above $`\delta^\varepsilon`$
  with a cofinal Pred₁ may lie in the segment of $`\delta^\varepsilon`$, and that the first missing input is the reach of $`R_2^S`$ on that segment. False: by NOBAD and INC1 ([BREAK.md](BREAK.md) §1) such a point is a
  $`\upsilon_\lambda`$ with $`\lambda`$ a limit, and the segment has none; and $`R_2^S`$ equals $`R_1^+`$ there by SKEL$`^\infty`$. What the induction still needs (the referee): SHIFT data at the new pairs of the
  regions whose codes are at least $`\varepsilon_{G''(\omega+1)+\omega}+1`$ (the first such restart is $`L(\theta'_2\cdot(\omega+1)+\varepsilon_{G''(\omega+1)+\omega}\cdot\omega)`$), and, for (E), the exclusion of the extra
  pairs (N0), type F, (N1) and (N2) at fan apexes and caps.
- **Open.** (E); type F and (N0) above $`x_F^C`$; $`\beta_0 \ge x_F^C`$: conjecture.

### 1.3 Native codes: marked sources, capacities, and the stage-route barrier

Notation as in [SHIFT9.md](SHIFT9.md) §1.3 and §3.3 (units, objects, sources, keys, layouts A and B, the hosting case F1, the chain number $`k`$).

- **The repairs of the review of [SHIFT9.md](SHIFT9.md) §3.3** (m1–m6; the referee checked them). SUCC is proved again without assuming the atom property at the stage (m1); one argument is
  labelled a remark (m2). **NO-FIX** (m3; proved once two hypotheses are added, convexity and closure of the fixed part over the parameters): no fixed finite configuration hosts the patterns that
  contain it below its root; so the conditional result of [SHIFT9.md](SHIFT9.md) §3.3 is withdrawn.
- **Marked sources** (layout A; UNIV-P$`^m`$, F1$`^m`$, COR HOST$`^m`$, SHAPE$`^m`$; proved). Every object and every unit carries a source $`x' \lt_2 y' \lt s' \lt h'`$ with $`s' \le_1 s'\cdot 2`$ and $`x', h' \le_1 h'\cdot 4 + m`$,
  where the marker $`m`$ is a sum of code points below. UNIV-P$`^m`$: such a source hosts every index-coded scope, at any depth and index, whose own sources have smaller markers. F1$`^m`$: **the
  case F1 is hosted** inside the host's object when the markers of the guest's inner scope are below the marker of the host's source. So every merge, F1 included, is hosted when the markers
  as placed satisfy three order conditions (C1)–(C3) (a conditional lemma); 2 per unit and chain 4, so chain number 5 at every depth and index. Minor: one list (m4) and one bound (m5).
- **Capacities** (KEYCAP, WIT, PER-KIND, STACK; proved). KEYCAP: the weight of a unit satisfies (C1)–(C3), so ordinal capacities exist. PER-KIND: no capacity that depends only on the value and
  depth of an object satisfies (C1); the witness family WIT has a case F1 at every depth inside every stage set from $`\Omega_{\omega\cdot 2}`$ on. The referee: the proof needs WIT for more than one size,
  repaired by a window descent (checked in Lean) or by WIT for every larger size (m2). With NO-FIX and STACK (a chain number growing with the depth does not help in one module system): the stage route
  stops at $`\psi_{\Omega_1}(\Omega_{\omega\cdot 2})`$ for fixed shapes, for capacities graded by depth, and for chain numbers growing with depth.
- **(REP$`^\rho`$) and REP-RANK** (proved with m6, m7). (REP$`^\rho`$): a code inside each unit $`H`$ that orders the hosting relation. With the hosting rank $`\rho(H)`$ (countable, for the generated stages): any such code has
  value at least $`\rho(H)`$, and codes of $`\rho`$ give (REP$`^\rho`$). **Not proved** (m1): "(REP$`^\rho`$) holds exactly when $`\rho(H)`$ has a code inside $`H`$" (one direction only), "the barrier is equivalent to the failure
  of (REP$`^\rho`$)" (neither direction), and "the stage route stops" beyond the definitions of the earlier architecture. MARKER-SELF (the markers as the module system's own codes of $`\rho`$): conjecture.
  Conditional (outline): (REP$`^\rho`$) for the stage sets $`[1, u_m]`$ would give chain number 5 up to $`\theta_0`$, so $`\iota(\mathrm{CH}_5) \ge \theta_0`$ and the first fan needs an inaccessible.
- **B-1** (layout B): not repaired; codes in a nested pair cost one link, so chain number 5 again (remark).
- **Native bounds.** No new bound, and none is lost: chain number 3 below $`\psi_{\Omega_1}(\varepsilon_{\Omega_\omega+1})`$, 4 below $`\psi_{\Omega_1}(\Omega_{\omega\cdot 2})`$, and $`\iota(\mathrm{CH}_5)`$, $`m_F`$ above $`\psi_{\Omega_1}(\Omega_{\omega\cdot 2})`$.
  Open: (REP$`^\rho`$), B-1, any native bound in $`[\psi_{\Omega_1}(\Omega_{\omega\cdot 2}), \theta_0)`$, $`H_m`$, and "the first fan needs an inaccessible".

### 1.4 Status after the thirty-eighth round

Superseded by §3.4.

### 1.5 Checks of the thirty-eighth round

Each run was under 60 seconds; none is a proof.

- §1.1. 11 runs: the tier maps forward at the tiers $`\omega\cdot 3+2`$, $`\omega^2`$, $`\omega^2+1`$, $`\omega^3`$, $`\varepsilon_0`$ (220 codes and 24,090 pairs per tier) and backward (350 codes per tier), 0 mismatches; the domain on
  20,388 indices (9,335 not in the domain), 0 mismatches; the chain of names up to $`Z^{\mathrm{LL}}`$ and its literal form; the window chains at 4 bases; 44 of 44 far indices and 24 of 24 targets of long codes.
  Three errors of the test harness were found and fixed, and the paper says so. Lean green, identical to Python. The referee: own tests, no counterexample to a reach formula; the tier at
  uncountable $`\zeta`$ (m1); 5,930 tails (0 failures of the π-bound) and the counterexample of m2; the code ranges of 15,421 restarts, 0 failures; the domain on 3,611 adversarial indices, 0
  mismatches; 24 far indices (m4); the author's runs and the Lean file rerun, identical.
- §1.2. 14 runs: the domain on 12,601, 14,265 and 9,670 indices (8,740 not in the domain), 0 mismatches; 225 of 225 targets; the chains at the bases up to $`Z^\varepsilon`$; Lean green (now with $`Z^\Gamma`$),
  identical to Python. The referee: two runs rerun, identical; own checks of the constants, the order of the points up to the next restart, and the codes (m4); the Lean file rerun, green.
  $`R_2^S`$, $`R_2^C`$, reaches, copies and the criterion cannot be computed.
- §1.3. The witness family on 80 cases ($`D \le 5`$), 0 failures. The referee: the run rerun, identical; own code on 504 cases with larger sizes, 0 failures; the repaired descent of PER-KIND in Lean.
  The run does not compute the host positions directly (m8).

### 1.6 Open

Superseded by §3.6.

## 2. The thirty-ninth round

Three papers (2026-10), each refereed once: a paper on the long restarts of the skeleton up to the first index fixed point (§2.1), a paper on (E): one lemma per kind of pair, and the
fans (§2.2), and a paper on native codes (§2.3). A result in this section has 1 review unless a count is given. The minor points of the reviews of §1.1, §1.2 and §1.3 are applied by the
three papers, and their referees checked each repair (**2 reviews**). **The frontier of the claim moves down.** The referee of §2.1 found a fatal point against the exact value of the long
reaches of §1.1 (EXACT-LONG-CL″\*) and a blocking point against Theorem C$`^{\mathrm{LL}}`$, whose induction uses those values; this is the second review of both. So, given FRAG, the claim is
proved in $`R_2^C`$ on $`[0, Z^\Lambda]`$ (Theorem C$`^\Lambda`$ of §1.1; 1 review, and up to $`Z^\varepsilon`$ 2 reviews) and in $`R_2^S`$ on $`[0, Z^\varepsilon)`$ (2 reviews), where

```math
Z^\Lambda = L(\theta'_2\cdot\omega^2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+2}).
```

The referee expects the claim on $`[0, Z^{\mathrm{LL}}]`$ and above to survive the repair; the repair is not written. Papers cited: in §2.1 Wilken, "Σ₁-elementarity and Skolem hull operators"
(APAL 145, 2007; L.2.1, Def 4.1, Thm 2.2, Cor 5.10), Carlson 2009 (Def 5.3, L.5.5, L.5.7) and Wilken's "A glimpse of Σ₃-elementarity" (L.21.10, Thm 21.13), besides refereed stages; in §2.2
Carlson 2009 (clause 2 of Def 5.3, Def 5.4, L.5.5, L.5.7), [CW12b] (Prop 7.4 and the proof of Thm 7.9, read as a pattern) and Wilken, "Tracking chains revisited" [W17t],
https://arxiv.org/abs/1611.04348 (Cor 5.8, as an analogy only); no paper in a proved step of §2.3, which does not use FRAG. None of the papers uses Wilken, JSL 72 (2007), Carlson, AML 38 (1999),
or Wilken, AML 45 (2006). No Lean file was added: the ordinal inputs of §2.1 and §2.2 were checked with Lean files that only compare terms (`#eval`, no theorem; green, identical to Python,
and identical in the referees' rechecks), and the referee of §2.3 checked three steps with a separate Lean file (green); these count as checks. Levels are numbered as in
[SHIFT8.md](SHIFT8.md). "Given FRAG" is as there.

Notation as in §1. New: $`\hat G'' = G''(\Omega_2) = \psi_{\Omega_2}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+\Omega_2})`$, the least fixed point of $`\zeta \mapsto G''(\zeta)`$; for a restart $`b = L(\lambda'')`$ of the skeleton,
$`F''_b = L(\lambda''+\Omega_1)`$, its first index fixed point; $`\lambda^{\mathrm{LL}} = \theta'_2\cdot\omega^2+\omega^{G''(\omega^2)^2}`$, so $`Z^{\mathrm{LL}} = L(\lambda^{\mathrm{LL}})`$.

### 2.1 The long restarts up to the first index fixed point, and a fatal point against the exact long reaches

- **The repairs of the review of §1.1** (m1–m7; **2 reviews**). All reach statements are now proved by one induction along the right bound (m5). The restart named in the fatal point of §1.2,
  $`L(\theta'_2\cdot(\omega+1)+\varepsilon_{G''(\omega+1)+\omega}\cdot\omega)`$, lies below $`Z^\Lambda`$, and by the window rule it reaches $`\varepsilon_{\delta''_1+\omega}\cdot 2+2`$.
- **The code side** (GHAT″, EMPTY″, TIER$`_\zeta`$, OFF″, FIX″, THETA″$`^G`$; proved, no FRAG; the reading by transfer). $`\hat G''`$ is the least fixed point of $`G''`$, and no index in
  $`[\theta'_2\cdot\hat G'', \theta'_2\cdot\Omega_2)`$ is in the domain of $`L`$. The tier map works for every normal form $`\zeta \lt \hat G''`$ (for $`\zeta \in [\hat G'', \Omega_2)`$ the term $`G''(\zeta)`$ is not a normal form).
  For a countable $`x \ge 1`$, $`\lambda''+x`$ is in the domain exactly when $`x \lt L(\lambda''+x)`$, exactly when $`x \lt F''_b`$. The reading is $`o_b(G''(\zeta)) = L(\lambda''+1+o_b(\zeta))`$, and $`o_b`$ maps the
  codes below $`\hat G''`$ that are in the domain at $`b`$ onto $`[0, F''_b)`$. For countable $`\zeta`$ this is READ″$`_\zeta`$ of §1.1, which now has **2 reviews**.
- **The far pins one level up** (T$`^F`$, MULTI-RC″$`^F`$, PIN-ALL″$`^F`$, SEP″$`(\Omega_1)`$, TOP-REG-FAR″$`^F`$, LONG-RS″$`^F`$, CROSSED″$`^F`$; proved by transfer, given FRAG). A far transport over every
  countable index distance below $`F''_b`$ and over the one offset $`\Omega_1`$, pins at every far position, and crossings over index distances up to $`\Omega_1+\omega^2`$ keep the skeleton.
- **CROSS″** (proved by transfer, given FRAG; an outline in §1.1): a code $`\ge G''(\zeta)`$ reaches at least $`L(\lambda''+\omega^2\cdot L(\lambda''+1+o_b(\zeta))) \ge L(\lambda''+\zeta)`$. Also LB″$`^G`$, R-CAP″$`^G`$,
  CROSS-O″ and CROSS-F″ (codes $`\ge \hat G''`$ reach $`F''_b`$): proved; they use only $`m_0 = 0`$ or the reading of $`D`$.
- **Fatal point F-1: the exact long reaches are false for some codes.** For a long code $`c = G''(\omega^2)\cdot D + m_0`$ the value $`r(L(\lambda'')) = r(\nu) + o_\nu(m_0)`$ of §1.1 (EXACT-LONG-CL″\*), and
  its extensions in this paper (EXACT-LONG″$`^G`$ for $`D \lt \hat G''`$, EXACT-F″ for $`D = \hat G''`$, and the single value of AGREE″), read $`m_0`$ at the landing point $`\nu`$; it must be read over the
  codes whose constants lie below $`b`$. Counterexample: the restart $`b`$ with index $`\theta'_2\cdot\omega^2+\omega^{G''(\omega^2)+\Omega_1}`$ (code $`G''(\omega^2)+\Omega_1`$, below $`Z^{\mathrm{LL}}`$) has
  $`r(b) = r(\nu) + b`$, not $`r(\nu) + \nu`$: "$`\le`$" by the far pin with the target $`r(\nu)+b`$ (it uses the addition of $`R_2^+`$), "$`\ge`$" by the realizers. The same happens at the code $`\hat G''+\Omega_1`$.
  Affected are the $`m_0`$ such as $`\Omega_1`$, $`\Omega_1\cdot k`$ and $`\omega^{\Omega_1\cdot 2}`$, for which the smaller codes with constants below $`b`$ are not cofinal; $`m_0 = 0, 1, P'`$ are not affected. The
  "$`\le`$" halves stay true as upper bounds. **The same defect is in the exact long reaches of the first skeleton**, from EXACT-LONG of [SHIFT2.md](SHIFT2.md) §3.1 on (its later forms in
  [SHIFT3.md](SHIFT3.md)–[SHIFT6.md](SHIFT6.md)); the earlier lower bound RL-UP ([SHIFT.md](SHIFT.md) §9.1) reads $`m_0`$ at the restart and agrees with the corrected value. A corrected formula (the least
  closed point of the block of $`m_0`$ at $`\nu`$ above the values of the smaller codes with constants below $`b`$) is proposed and not checked. Which later results use the exact value at such $`m_0`$
  is not yet checked.
- **Blocking point B-1: Theorem C$`^{\mathrm{LL}}`$ and the new frontier are not proved as written.** Theorem C$`^{\mathrm{FP}}`$ (the claim in $`R_2^C`$ on $`[0, Z^{\mathrm{FP}}]`$ and in $`R_2^S`$ on $`[0, Z^{\mathrm{FP}})`$, with
  $`Z^{\mathrm{FP}} = L(\theta'_2\cdot\Omega_2+\omega^{\hat G''+G''(\omega^2)}) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+\Omega_2} + \omega^{\hat G''+G''(\omega^2)})`$, and the frontiers $`L(\theta'_2\cdot\Omega_1)`$ and $`L(\theta'_2\cdot\Omega_2)`$ on the way)
  and Theorem C$`^{\mathrm{LL}}`$ of §1.1 run their induction with the values of F-1. Every corrected value lies in the same block as the claimed one, so the upper bounds, the caps, and the absence of
  reaches across the frontier are not affected (RANGE$`^{\mathrm{FP}}`$: proved), and **CAP-0″ below $`Z^{\mathrm{FP}}`$** (no restart below $`Z^{\mathrm{FP}}`$ crosses itself; it uses only upper bounds) is proved.
  The referee expects both theorems to survive the repair.
- **The point $`\nu_3`$** (blocking point B-2). With $`L_3(e) = \psi_{\Omega_1}(\Omega_\omega\cdot 3 + P_3\cdot e)`$ and $`\nu_3 = L_3(\omega+1) = \psi_{\Omega_1}(\Omega_\omega\cdot 3 + \omega^{P_3+1} + P_3)`$: the codes
  $`c_k = G''(\theta'_{k+1}\cdot\omega^2)`$, $`\theta'_k = \psi_{\Omega_{k+1}}(\Omega_\omega\cdot 2)`$, increase to $`P_3`$ (proved). The paper's criterion SHIFT$`_3`$ (three hypotheses on $`[0, \nu_3)`$ give
  $`L_3(\omega) \lt_2^S L_3(\omega+1)`$ and $`T_3^S = \nu_3`$) is vacuous: the first hypothesis (the skeleton below $`\nu_3`$) contradicts what the other two give, since they give $`L_3(1) \le_1 L_3(\omega)`$. So the
  reduction of $`\nu_3`$ to the three hypotheses does not work; the route that works is the one used for $`\nu_C`$: CAP-0 and CAP-1 one level up and an analogue of NU-CT. Minor: the region bound of
  the second hypothesis is false at the code 1 (m1); one index (m2); instances with $`m_0`$ like $`\Omega_1`$ (m3); the $`R_2^S`$ side depends on B-1 (m4).
- **Not proved.** EXACT-LONG″ (F-1); Theorems C$`^{\mathrm{LL}}`$, C$`^{\mathrm{FP}}`$ and the frontiers on the way (B-1); SHIFT$`_3`$ and the reduction of $`\nu_3`$ (B-2). Open: the codes from $`\hat G''+G''(\omega^2)`$ on
  (the family after the landing at $`F''_b`$), the tiers $`G''(\zeta)`$ for $`\zeta \ge \Omega_2`$, the landing calculus at depth 2 and more, CAP-0 below $`P_3`$ and NOT-LOW one level up (outlines), and the
  hull cap READ$`^\sharp`$ one level up (conjecture).

### 2.2 (E): one lemma per kind of pair, and the least fan

Words as in §1.2.

- **The repairs of the review of §1.2** (F-1 and m1–m7; **2 reviews**). The location claim is withdrawn and replaced by the referee's statement: no point of the segment of a $`\upsilon`$-point $`d`$ other
  than $`d`$ has a cofinal Pred₁ (NOBAD and INC1, [BREAK.md](BREAK.md) §1). SEG-GAP⁺ (proved): at a base point of the calculus with the first block known, no point between $`\delta''_1`$ and the next
  $`\upsilon`$-point of limit index has a cofinal Pred₁, and $`\beta_0`$ and $`T_3^C`$ are at least that point (the referee's remark m1 of §1.2, now proved).
- **One lemma per kind of pair** (K01, K2; proved; K01 without FRAG and at every $`\upsilon`$-point, K2 by transfer, given FRAG). For a left end $`t`$ with a cofinal Pred₁, a lemma that uses only clause 2 of
  Carlson 2009, Def 5.3 shows that the successors of $`t`$ in $`R_2^C`$ below $`\beta_0`$ are among its successors in $`R_2^S`$: for a $`\upsilon`$-point $`t`$ whose reach is the next $`\upsilon`$-point (kind K01), and for
  $`\tau''_j`$ in a region with the skeleton of §1.1 (kind K2). With the pair proofs (PAIR, relativized PAIR, SHIFT) each kind satisfies the criterion. The referee: K01 must be defined as a $`\tau`$-point of
  the description SKEL$`^\infty`$ ([COVER.md](COVER.md) §5.1) (m3).
- **CRIT-IND$`^K`$** (proved). If every $`\alpha \lt b`$ with a cofinal Pred₁ is of kind K01 or K2, and $`R_2^S`$ has no triple nest below $`b`$, then $`\beta_0 \ge b`$, $`T_3^C \ge b`$, and every pair with right end below
  $`b`$ satisfies the criterion, where the uniform finite-set test is also necessary. So the hypothesis of CRIT-IND (§1.2) is proved there, not assumed.
- **CAP-PERSIST, SKEL″$`^x`$, UPPER″, PRED1″ and UNIFORM-A** (proved; by transfer, given FRAG). The pair skeleton of a region needs only the skeleton below it, upper bounds of reaches, and no restart
  with a cofinal Pred₁; no exact reach. UNIFORM-A is a schema: if every restart below $`Z'`$ has its reach given by the calculus or reaches $`Z'`$, and none has a cofinal Pred₁, then $`\beta_0 \ge Z'`$,
  $`T_3^C \ge Z'`$, the uniform test is necessary below $`Z'`$, and the claim holds in $`R_2^C`$ on $`[0, Z')`$. The referee: a region where a crosser with a computed reach lands needs CROSSED″ of §1.1 (m4);
  wording (m6).
- **Results that rest on Theorem C$`^{\mathrm{LL}}`$** (their referee found them proved, given FRAG, but they use Theorem C$`^{\mathrm{LL}}`$, against which §2.1 found B-1, so they are **not counted** until B-1 is
  repaired): LOAD$`^{\mathrm{LL}}`$ (every pair with right end at most $`Z^{\mathrm{LL}}`$ is of kind K01 or K2 and satisfies the criterion); C$`^{\mathrm{LL}\sharp}`$ ($`\beta_0 \gt Z^{\mathrm{LL}\sharp}`$ and the claim in $`R_2^C`$ on
  $`[0, Z^{\mathrm{LL}\sharp}]`$); C$`^{\mathrm{LX}}`$ ($`\beta_0 \gt Z^{\mathrm{LX}}`$ and the claim in $`R_2^C`$ on $`[0, Z^{\mathrm{LX}}]`$; the referee: the write-up is circular, repairable by one induction along the right bound, m1;
  the exact reach at the end point is not proved, m2), where

```math
Z^{\mathrm{LL}\sharp} = L(\lambda^{\mathrm{LL}}+\omega^2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+2} + \omega^{\omega^{G''(\omega^2)\cdot 2}} + \omega^{P'+2}),\qquad Z^{\mathrm{LX}} = L(\lambda^{\mathrm{LL}}+\omega^2\cdot Z^{\mathrm{LL}\sharp}).
```

  Conditional (outline): $`\beta_0 \ge L(\theta'_2\cdot\omega^2+\omega^{G''(\omega^2)^2+1})`$, given an open statement on where the reaches of the restarts with code $`G''(\omega^2)^2`$ land.
- **Fans** (FAN-SHAPES, LEAST-FAN; proved). The subtype (N0) happens exactly when the fan of $`R_2^C`$ at the left end is open (its lower successor is not $`\le_1`$ to $`\beta_0`$); type F needs a closed fan,
  so its left end is at least the least closed-fan apex $`f_0^C`$, which is above $`x_F^C`$. At the least fan $`x_F^C`$ only two first differences are possible: $`\beta_0 = y_1`$ (type N) or (N0) with $`\beta_0 = y_2`$; type F is
  impossible there, and (N0) there would put the least fan top of $`R_2^S`$ above that of $`R_2^C`$. CI-EXTRA: at an extra pair no shift, loading or supremum data exist (the first sentence proved; the
  sentence "consequently …" not proved, m5).
- **Blocking point B-1 against LOAD-SHAPE.** The claim that a loading of the least fan cannot use its own apex is not proved: long pairs exist inside the apex's own gap (a $`\Pi_2`$ sentence goes up from
  below), and a loading may run through them, as in the proof of [CW12b] Thm 7.9. So the list of routes to FAN-LOAD is incomplete; for (E) nothing is lost, since NO-SELF-LOAD (§1.2) still holds for the
  separating sets. FAN-LOAD: conjecture. The paper's list of the first places where CRIT-IND can fail is a remark: its completeness is not proved (m7).
- **Open.** (E); FAN-LOAD; $`\beta_0 \ge x_F^C`$ (conjecture).

### 2.3 Native codes: capacities per unit, and the first bound past $`\psi_{\Omega_1}(\Omega_{\omega\cdot 2})`$

- **The repairs of the review of §1.3** (m1–m8; the referee checked them). REP-RANK keeps only its parts (i)–(iii); "(REP$`^\rho`$) exactly when $`\rho(H)`$ has a code inside $`H`$" and "the barrier is equivalent to
  the failure of (REP$`^\rho`$)" are withdrawn (m1); PER-KIND uses the window descent (m2); NO-FIX has its two hypotheses (m3).
- **LEX-CAP, MARK$`^{\mathrm{lex}}`$, UNIT-SUP$`^{\mathrm{lex}}`$** (proved). A capacity for each unit $`U`$, compared in dictionary order: (index, kind, $`\alpha(U)`$, $`n(U)`$ minus the depth). It satisfies (C1)–(C3) for every pair
  of units when $`n(U)`$ is at least the source depth of $`U`$ and $`(\alpha, n)`$ does not decrease within one index class; the depth term gives the strict step. Such capacities are realized by markers, so
  the hosting lemma of §1.3 applies. PER-KIND is not contradicted: the capacity depends on the unit, not only on value and depth.
- **ALPHA-LOW, REDUCTION** (proved): $`\alpha`$ must jump at every unit with unbounded source depths just below it. **RHO-LEAF** (proved as stated): the hosting rank $`\rho`$ of
  $`\psi_{\Omega_{\omega+1}}(\Omega_{\omega+5} + \omega^{\Omega_{\omega+3}+b})`$ is at least $`b`$ for every $`b \lt \Gamma_0`$, below $`\Omega_{\omega\cdot 2}`$. The referee: this does not show that one marker per unit asks too much,
  since the unit already holds the code of $`b`$ (m1). MARKER-SELF is set aside, not refuted.
- **Instances** (LEVEL-BOUND, LEX$`[\Omega_{\omega\cdot 2}]`$, UNITS, SC-MAX, LEX$`[S_*]`$; proved). On the stage sets up to $`\Omega_{\omega\cdot 2}`$, $`\alpha = 0`$ works; up to $`S_*`$ (below), $`\alpha \lt \omega^{\omega+1}`$ works, with
  finite digits. ALPHA-LOW$`^\Gamma`$ (proved): further up there is a unit where every such capacity has $`\alpha \ge \Gamma_0`$. "Finite digits stop at $`S_*`$" is not proved (a remark, m2).
- **A new native bound** (REGION, SHAPE, IDX on the stage sets up to $`S_*`$; proved by transfer):

```math
\iota(\mathrm{CH}_5) \ge \psi_{\Omega_1}(S_*),\qquad S_* = e_* + \psi_{\Omega_{\omega+1}}(e_*),\quad e_* = \Omega_{\omega\cdot 2} + \psi_{\Omega_{\omega+2}}(\Omega_{\omega\cdot 2})\cdot\omega^\omega,
```

  with $`\psi_{\Omega_1}(\Omega_{\omega\cdot 2}) \lt \psi_{\Omega_1}(S_*) \lt \psi_{\Omega_1}(\Omega_{\omega\cdot 2}\cdot 2)`$; so RED-TOWER holds with chain number 5 below $`\psi_{\Omega_1}(S_*)`$, and $`m_F \gt \psi_{\Omega_1}(S_*)`$. This is the first native
  bound past $`\psi_{\Omega_1}(\Omega_{\omega\cdot 2})`$: the statement "for a fixed chain number the stage route stops at $`\psi_{\Omega_1}(\Omega_{\omega\cdot 2})`$" is false for chain number 5, and the barrier of §1.3
  holds only for the capacity forms named there. Whether $`\psi_{\Omega_1}(S_*)`$ is above $`\iota(\mathrm{CH}_4)`$ is not known (m7). Minor: one reason in UNITS (m3), one bound (m4), one condition in the header (m5),
  the scope of a section (m6) and of the checks (m8).
- **Open.** LEX-SELF ($`\alpha`$ read off each unit's own boundary codes): conjecture; with it (outline) $`\psi_{\Omega_1}(\Omega_{\omega\cdot 2+1})`$, $`\theta_0`$, $`H_m`$ and "the first fan needs an inaccessible"; layout B
  (B-1), and whether chain number 4 passes $`\psi_{\Omega_1}(\Omega_{\omega\cdot 2})`$.

### 2.4 Status after the thirty-ninth round

Superseded by §3.4.

### 2.5 Checks of the thirty-ninth round

Each run was under 60 seconds; none is a proof.

- §2.1. 9 runs (the fixed point, the tiers below $`\hat G''`$, the domain of the offsets, the reading, the far transport, the chain of names, the codes $`c_k`$), 0 mismatches; four errors of the test
  harness were found and fixed, and the paper says so. Lean green, identical to Python. The referee: 100 general countable offsets at 4 bases, 0 mismatches; 337 indices in the domain, 0
  violations of the code bounds; the counterexamples of F-1 and m1, and the points of B-2; the author's Lean file rerun, identical.
- §2.2. 4 runs (the codes and points of the region of $`Z^{\mathrm{LL}}`$, the restarts with unknown reach, the shape of the least fan), 0 failures; Lean green, identical to Python. The referee: the runs rerun,
  identical; 600 random indices, of which the 147 between $`Z^{\mathrm{LL}}`$ and $`Z^{\mathrm{LX}}`$ all have the predicted form; the Lean file rerun, green. $`R_2^S`$, $`R_2^C`$, reaches, copies and the criterion cannot be
  computed.
- §2.3. The two conditions of LEX-CAP on 380 random arguments per seed, 2 seeds (about 71,700 ordered pairs, depths up to 6), and $`S_*`$, RHO-LEAF, the witness family and ALPHA-LOW$`^\Gamma`$: 0 failures. The
  referee: both seeds rerun, identical; own depth reader on 2 seeds (about 51,000 pairs per seed, deeper nests, more classes), 0 failures; a Lean file for the strict step of (C1), ALPHA-LOW and
  REDUCTION, green. The checks cover one class of arguments only (m8).

### 2.6 Open

Superseded by §3.6.

## 3. The fortieth round

Three papers (2026-10): a paper that repairs the exact long reaches (§3.1) and an audit of which recorded results use the false value (§3.2), each refereed once, and the first Lean stage
for $`R_2^C`$ (§3.3), whose audit checked the axioms and the definitions (Lean checks the proofs). A result in this section has 1 review unless a count is given. The minor points of the reviews
of §2.1, §2.2 and §2.3 are already in the record of §2.

**The frontier of the claim moves down, and the milestone is no longer proved.** Both referees found that the chain to $`\nu_C = \nu_S = L(\omega+1)`$ ([SHIFT7.md](SHIFT7.md) §2.1) and every
frontier above $`X_{21}`$ use exact long reaches at codes where the old value is false. So **$`\nu_C = \nu_S = L(\omega+1)`$, Wilken's claim on $`[0, \nu_C]`$, not-LOW, and every range above $`X_{21}`$ (up to
$`Z^\Lambda`$) are not proved as written.** Given FRAG, the claim is proved in $`R_2^C`$ on $`[0, X_{21}]`$ (the repaired proof, 1 review; up to the point $`X_{19}^{\mathrm{lin}}`$ of §3.2 two proofs, 2 reviews),
and in $`R_2^S`$ only up to $`\upsilon_{\omega^3}`$, as without FRAG. Here

```math
X_{21} = \psi_{\Omega_1}(\Omega_\omega + \hat\zeta_H + \omega^{G(\hat\zeta_H)+1}\cdot 2),\quad \hat\zeta_H = \theta_3\cdot\Omega_3 + \omega^{\hat g_3+g_3},\quad \theta_3 = \psi_{\Omega_4}(\Omega_\omega),
```

with $`\hat g_3 = \psi_{\Omega_3}(\Omega_\omega + \theta_3\cdot\Omega_3)`$ and $`g_3 = \psi_{\Omega_3}(\Omega_\omega + \theta_3\cdot\omega^2)`$ ([SHIFT5.md](SHIFT5.md) §2.1). FRAG itself is now proved in Lean from 20 cited facts of two
papers (§3.3, [LEAN.md](LEAN.md)).

Papers cited: in §3.1 and §3.2 Wilken, "Σ₁-elementarity and Skolem hull operators" [W07b] (APAL 145, 2007; L.2.1), Wilken, "Ordinal arithmetic based on Skolem hulling" [W07a] (APAL 145, 2007),
Wilken's "A glimpse of Σ₃-elementarity" (Prop 21.6) and Carlson 2009, besides refereed stages; in §3.3 Carlson 2009 (Def 2.1, 2.3, 2.6, 5.2–5.4, for the definitions only) and [W07a], [W07b] (the
cited facts, listed in [LEAN.md](LEAN.md)). None uses Wilken, JSL 72 (2007), Carlson, AML 38 (1999), or Wilken, AML 45 (2006); the statements of [W07b] L.2.1 and Thm 2.2 are taken from [W07b] §2.
Levels are numbered as in [SHIFT8.md](SHIFT8.md).

Notation: for a restart $`\lambda`$, $`R_1 = \rho_{\lambda+\omega^2}`$ is the next restart, $`\delta_R`$ is the first block top of a restart $`R`$ ([REACHES.md](REACHES.md)), $`\Theta_\lambda = o_\lambda`$ reads a code at $`\lambda`$
(the order type of the smaller codes whose constants lie below $`\rho_\lambda`$), $`\hat G = G(\Omega_2)`$, and $`F_\lambda = H(\eta_\lambda + \Omega_1)`$ is the first index fixed point above $`\lambda`$. A long code is
$`m = G_2\cdot D + m_0`$ with $`D \ge 1`$, $`m_0 \lt G_2`$.

### 3.1 The exact long reaches repaired below $`\hat G + G_2`$, and the frontier $`X_{21}`$

- **The error is wider than F-1** (the referee confirmed the diagnosis on its own). A realizer of a restart $`\lambda`$ lies below $`\rho_\lambda`$, so its code has only constants below $`\rho_\lambda`$. The old
  proofs of the long lower bounds (from EXACT-LONG and CROSS-O of [SHIFT2.md](SHIFT2.md) §3.1 on) let codes with constants up to the landing point $`\rho_\nu`$ act as realizer codes. This breaks the part
  $`m_0`$ (F-1 of §2.1) and also the crossing by the part $`D`$. The whole code must be read at $`\lambda`$ by $`\Theta_\lambda`$, and the landing restart is the largest restart point $`\le \Theta_\lambda(m)`$, not
  $`\upsilon_{\lambda+\omega^2\cdot\Theta(D)}`$.
- **Counterexamples** (proved by transfer, given FRAG; at restarts below $`X_6`$, where every hypothesis holds; the witnesses checked). For a code $`G_2 + x`$ with $`x \lt G_2`$:
  $`r(\lambda) = \delta_{R_1} + 1 + \Theta_\lambda(x)`$. So $`G_2 + \Omega_1`$ reaches $`\delta_{R_1} + \rho_\lambda`$; $`G_2 + \Omega_1 + 1`$ reaches $`\delta_{R_1} + \rho_\lambda + 1`$, so the repair proposed in §2.1 is false;
  $`G_2 + \varepsilon_{\Omega_1+1}`$ reaches $`\delta_{R_1} + \varepsilon_{\rho_\lambda+1}`$, so the list of codes that §2.1 calls unaffected is wrong. **NO-CROSS**: the code $`G_2\cdot 2`$ reaches
  $`\delta_{R_1} + R_1 \lt \rho_{\lambda+\omega^2\cdot 2}`$, so CROSS-O is false at $`x = 2`$ and the old landing is wrong for every $`2 \le D \lt \hat G`$; a witness is the restart
  $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{G_2\cdot 2})`$. The refereed bounds of the seventeenth round (RL-UP and the cap of codes below $`G_2\cdot 2`$, [SHIFT.md](SHIFT.md) §9.1) agree with
  these values.
- **Theorem TRANSLATION** (proved by transfer, given FRAG). Let $`K_\lambda`$ be the set of the points $`y \ge \delta_\lambda`$ such that every $`\alpha \in (\rho_\lambda, y]`$ has $`\mathrm{lh}(\alpha) \le y`$ (the points that can be
  the reach of $`\lambda`$), and $`k_\lambda`$ its increasing enumeration. For every long restart $`\lambda`$ below $`\nu_S`$ and $`\psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ whose code (or π-code) $`m`$ has
  $`G_2 \le m \lt \hat G + G_2`$:

```math
r(\lambda) = k_\lambda(\Theta_\lambda(m)) = F(\nu, \tau_\nu + x),\qquad \rho_\nu = \text{the largest restart point} \le \Theta_\lambda(m),\quad x = \Theta_\nu^{-1}(-\rho_\nu + \Theta_\lambda(m)),
```

  with $`F`$ the value of a short code at $`\nu`$ ([SHIFT6.md](SHIFT6.md) §3.1). "$`\ge`$" by realizers with constants below $`\rho_\lambda`$; "$`\le`$" by the far pin with the addition of $`R_2^+`$ and pins on
  every component of the target. Also MONO♯ (the value increases with the code), TF5♯ (it commutes with every far transport, also with moved constants) and BC♯ (base changes); the same in the
  region $`[m^*, \psi_{\Omega_1}(\Omega_\omega\cdot 3))`$. The referee's minor points: the domain of the codes must be the refereed hull, and a choice of the bound $`\kappa_0`$ removes the π-code tails (m1);
  one transport must be the relative one (m2); BC♯ needs the finite closedness criterion (m3; not used below); "the new value is at most the old one" was taken from the unrefereed audit, and
  the referee gives a direct proof (m4).
- **SHARP-CROSS** (proved). Below $`F_\lambda`$: $`r(\lambda) \ge \upsilon_{\lambda+\zeta}`$ exactly when $`m_\lambda \ge G(\zeta)`$, for every countable multiple $`\zeta \ge \omega^2`$ of $`\omega^2`$ below $`\rho_\lambda`$. This was a
  conjecture of the seventeenth round.
- **FAR-PIN$`^{L\sharp}`$** (proved by transfer, given FRAG): the far pin of [SHIFT5.md](SHIFT5.md) §1.1 with the corrected value as its exact atom, for every long prefix code below $`\hat G + G_2`$. So the
  landing caps LAND-CAP, LAND-CAP$`^G`$, LAND-CAP$`^F`$, CAP$`^\sharp`$ and READ$`^\sharp`$ below $`\hat\zeta_H`$ ([SHIFT5.md](SHIFT5.md) §1.1, §2.1) stand, and with them $`X_{19}`$, $`X_{20}`$, $`X_{21}`$.
- **Theorem X21 again** (proved by transfer, given FRAG): $`\nu_C \ge X_{21}`$, $`\nu_S \ge X_{21}`$, and **Wilken's claim in $`R_2^C`$ on $`[0, X_{21}]`$, both halves**. The proof meets long prefix atoms only at
  codes below $`\hat G + G_2`$ (this bound is checked on 889 multipliers, as before) and uses no lower bound from the part $`D`$. The repaired form has 1 review (m6).
- **Not proved.** Above $`X_{21}`$: $`X_{22}`$, $`X_{23}`$ ([SHIFT6.md](SHIFT6.md)), CAP-0 below $`P'`$, CAP-1, $`\nu_C \ge L(\omega+1)`$ ([SHIFT7.md](SHIFT7.md) §1.1) and every later step, since they use atoms or
  crossings at codes $`\ge \hat G + G_2`$. The value for every code below $`P'`$ is conjecture ENUM-REACH: past $`\hat G + G_2`$ the reach crosses long restarts, and the landing calculus must be done
  again with the new landings. **One level up** (an outline, not counted; blocking point B-1 of the review): TRANSLATION″ below $`\hat G'' + G''(\omega^2)`$ and Theorems C$`^{\mathrm{LL}\sharp}`$, C$`^{\mathrm{FP}\sharp}`$ (the
  claim in $`R_2^C`$ on $`[0, Z^{\mathrm{FP}}]`$), all under (H0) = ENUM-REACH below $`P'`$ with the chain to $`\nu_C`$ proved again on it; the proof of TRANSLATION″ only lists its tools. In the outline the
  code $`G''(\omega^2)\cdot 2`$ does not reach $`L(\lambda''+\omega^2\cdot 2)`$, so the first inequality of CROSS″ in §2.1 is withdrawn; its weak form $`r \ge L(\lambda''+\zeta)`$ is kept as part of the outline.

### 3.2 The audit: which results use the false value

- **The corrected value in the simplest cases** (proved, given FRAG). UB: the "$`\le`$" halves of the old proofs stand by themselves. BRACKET: the two readings differ at every $`m_0 \ge \Omega_1`$.
  **CV-LIN**: for $`D = 1`$ and $`m_0 = \Omega_1\cdot k + c`$ with $`c \lt \rho_\lambda`$, $`r(\lambda) = r(\nu) + \rho_\lambda\cdot k + c`$ (the referee redid the step at $`m_0 = \Omega_1`$ by hand; it agrees with RL-UP and
  with §3.1). FALSE-ω: at $`m_0 = \Omega_1\cdot\omega`$ the reach is at most $`r(\nu) + \rho_\nu`$, below the old value. PIN-LIN: the far pin works with the corrected atom for these codes. LB-CORR
  ($`r(\lambda) \ge r(\nu) + \Theta_\lambda(m_0)`$ at the old landing $`\nu`$): its referee found it proved for small $`m_0`$ and not proved above (blocking point B-1: the step needs the invariance of the
  corrected value under transports, which is open); by NO-CROSS of §3.1 its old landing is wrong for $`2 \le D \lt \hat G`$, so it is counted only for $`D = 1`$.
- **Where the affected codes first occur** (proved, checked). With $`\zeta_1 = \hat\zeta_3 + \omega^{g_3+\Omega_2}`$ ($`\hat\zeta_3 = \theta_3\cdot\omega^2`$), below $`G(\zeta_1)`$ no landing prefix has $`m_0 \ge \Omega_1`$, and $`\zeta_1`$
  gives the first prefix with $`m_0 = \Omega_1`$, inside the range of the landing cap of $`X_{19}`$. The referee: the countable rest can be $`\omega`$, $`\varepsilon_0`$, $`\varphi(2,1)`$, not only finite (m4); the
  conclusion stands, and its search found 0 counterexamples among 2,512 normal multipliers.
- **$`X_{19}^{\mathrm{lin}}`$** (proved, given FRAG). With $`\zeta_{\mathrm{lin}} = \hat\zeta_3 + \omega^{g_3+\Omega_2\cdot\omega}`$: $`\nu_C \ge X_{19}^{\mathrm{lin}} = \psi_{\Omega_1}(\Omega_\omega + \zeta_{\mathrm{lin}} + \omega^{G(\zeta_{\mathrm{lin}})+1}\cdot 2)`$, $`\nu_S \ge X_{19}^{\mathrm{lin}}`$,
  and the claim holds in $`R_2^C`$ on $`[0, X_{19}^{\mathrm{lin}}]`$; also $`X_{19}^\flat`$ with $`\zeta_1`$ in place of $`\zeta_{\mathrm{lin}}`$, with no new lemma, and $`X_{18} \lt X_{19}^\flat \lt X_{19}^{\mathrm{lin}} \lt X_{19} \lt X_{21}`$. It uses only
  codes with $`D = 1`$, so neither B-1 nor §3.1 touches it. With §3.1 this is a second proof of the claim below $`X_{19}^{\mathrm{lin}}`$: **2 reviews**.
- **The milestone is not proved as written** (the referee confirmed). CROSS-LIM ([SHIFT7.md](SHIFT7.md) §2.1) crosses a restart of code $`G_2 + P`$, whose reach is only bracketed, and the long-restart
  step needs its exact value and its invariance under the transport. So CROSS-LIM, the hypotheses (C1)–(C3) of the shift criterion, PAIR, UP, NU, NU-NAME and LOW$`^\infty`$ are not proved as
  written, nor are not-LOW, CAP-0 below $`P'`$ and CAP-1, which need caps at every code in $`[G_2, P')`$. They stand: the criterion SHIFT itself, the core half $`[0, \nu_C] \subseteq \mathrm{Core}(R_2^C)`$,
  the code inequalities of LC-STRICT, and the transport lemmas. The audit expects the milestone to come back with the corrected value (a conjecture). The sentence "no shorter route exists" is a
  remark, not proved (m5).
- **The table** (on [AUDIT.md](AUDIT.md)). $`X_9`$ to $`X_{18}`$ stand (no exact long value at an affected code). The exact long formulas at $`m_0 \ge \Omega_1`$ (EXACT-LONG of [SHIFT2.md](SHIFT2.md) §3.1, its
  forms on [SHIFT3.md](SHIFT3.md)–[SHIFT6.md](SHIFT6.md), EXACT-LONG-CL\* of [SHIFT4.md](SHIFT4.md) §2.1, LAND$`^\omega`$ of [SHIFT7.md](SHIFT7.md) §1.1) are false as stated; their upper bounds stand. Everything recorded above
  $`X_{21}`$ is not proved as written: $`X_{22}`$, $`X_{23}`$, $`L(\omega+1)`$, $`\nu_C = \nu_S`$, $`X_A`$, $`L(\omega^2)`$, $`L(\Omega_1\cdot\omega)`$, $`L(\varepsilon_{\Phi_\Omega+1})`$, $`L(G_2)`$, $`L(\Omega_2+\Phi^{P'}\cdot\omega)`$,
  $`L(\theta'_2\cdot(\omega+1)+G''(\omega+1)\cdot\omega)`$, $`Z^\Gamma`$, $`Z^\varepsilon`$, $`Z^\Lambda`$, and in $`R_2^S`$ the range $`[0, Z^\varepsilon)`$. The audit also had $`X_{19}`$ to $`X_{21}`$ as not proved; §3.1 repairs them.
- **Blocking points of the review against the inventory** (B-2, B-3). The lower-bound step (b) of [SHIFT2.md](SHIFT2.md) §3.1 has the same defect even when restricted, and so has the lower end of the
  bracket there. Further exact long formulas at affected codes are on [SHIFT3.md](SHIFT3.md) §1.1, §2.1 (the forms of EXACT-LONG), [SHIFT4.md](SHIFT4.md) §1.1 (EXACT-LONG-CL), [SHIFT5.md](SHIFT5.md) §2.2 (the
  level-2 form) and [SHIFT6.md](SHIFT6.md) §1.2 (EXACT-LONG$`^e`$); they are false as stated too. The ranges up to $`X_{15}`$ are not affected, since they lie below $`X_{21}`$, which is proved again.
- **Not counted.** The table's verdicts "survives with the corrected value" (they rest on the open conjecture CV, its invariance and its pin), and the list of what must be proved again; that list
  is the plan of §3.6.

### 3.3 Lean, stage 1: $`R_2^C`$, the core, and FRAG

- **$`R_2^C`$ is defined in Lean, not assumed.** $`\le_1`$ and $`\le_2`$ follow Carlson 2009, Def 5.3–5.4, by recursion on the right end (with Def 2.1, 2.3, 5.2). No axiom mentions $`R_2^C`$, so a misreading of
  the paper could only make the Lean $`R_2^C`$ differ from Carlson's; it cannot make the axioms contradict each other. With no axiom beyond Lean's standard three, Lean proves: the recursion
  equations; $`\le_1`$ and $`\le_2`$ are reflexive, transitive and inside $`\le`$; the interval and limit properties; Carlson 2009, L.5.5 (1), (3)–(6); the reach $`\mathrm{lh}(x)`$ exists unless $`x \le_1`$ every larger
  ordinal; isominimal sets and the core (Def 2.6) for any interpretation; Lemma LOC and its corollary.
- **Theorem FRAG in Lean**, for any number of countable bases (its domain contains the one of the paper proof, so the Lean statement is stronger), with Lemma ST, FRAG with one base on the whole
  domain, and Theorem FRAG2 for the Lean $`R_2^C`$ (which uses only the constant $`\le_1`$ of $`R_1^+`$). They use 27 axioms in one file: 7 constants ($`\le_1`$ of $`R_1^+`$, Wilken's term systems $`T^\tau`$, their
  parameters, the base change $`\pi_{\sigma,\tau}`$, heights, two families of terms) and 20 facts cited from [W07a] and [W07b].
- **The audit**: every axiom faithful to the paper (8 of them join 2–3 cited clauses; each join checked), every definition right, every main theorem Lean-proved; no fatal or blocking point. Minor
  points: three facts on $`R_1^+`$ are proved in a paper we do not have, and their statements are in [W07b] §2 (m1); FRAG needs countable bases (m4); the modules were built only as one bundle (m5;
  in the repository they now build as modules); the doc comments named local files (m6; replaced); the Lean $`\upsilon`$ is not yet shown to be Wilken's $`\upsilon`$ (m7); no link yet between $`\le_1`$ of $`R_1^+`$
  and $`\le_1`$ of $`R_2^C`$ (m9).
- So "given FRAG" now means "given 20 cited facts of two papers"; the paper proof of FRAG no longer needs a review. The files, the axioms with their sources and the theorems are on
  [LEAN.md](LEAN.md).

### 3.4 Status after the fortieth round

- **Wilken's claim in $`R_2^C`$**: both halves hold on $`[0, X_4]`$ without FRAG, and **on $`[0, X_{21}]`$ given FRAG** ($`[0, X_{18}]`$ with 2 reviews as before; up to $`X_{19}^{\mathrm{lin}}`$ with 2 reviews, two proofs,
  §3.1, §3.2; from $`X_{19}^{\mathrm{lin}}`$ to $`X_{21}`$ with 1 review of the repaired proof). The core half holds on $`[0, \nu_C]`$, and $`\nu_C \ge X_{21}`$ given FRAG. **Not proved as written**: $`\nu_C = \nu_S = L(\omega+1)`$,
  the claim on $`[0, \nu_C]`$, and every range above $`X_{21}`$ recorded in [SHIFT6.md](SHIFT6.md)–[SHIFT9.md](SHIFT9.md) and in §1, §2 here.
- **Wilken's claim in $`R_2^S`$**: proved only up to $`\upsilon_{\omega^3}`$ (with or without FRAG); $`\nu_S \ge X_{21}`$ given FRAG. The agreement of $`R_2^S`$ and $`R_2^C`$ above $`\nu_C`$, $`\sigma_S \ge Z^\varepsilon`$, and
  the criterion up to $`Z^\varepsilon`$ rested on the milestone and are not proved as written. Results without reaches stand: Carlson's categoricity [C11] with MIN$`^S`$, and the schemata K01, K2,
  CRIT-IND$`^K`$, UNIFORM-A (§2.2). (E) is open, and $`\beta_0`$ is not located.
- **Reaches** (given FRAG): exact for every restart below $`X_{21}`$, and for every long code below $`\hat G + G_2`$ (TRANSLATION). The old exact long formulas are false as stated at $`m_0 \ge \Omega_1`$ and at
  $`2 \le D \lt \hat G`$; their upper bounds stand.
- **LOW and LOW$`^\infty`$: undecided again** (not-LOW and LOW$`^\infty`$ rested on the chain to $`\nu_C`$). The steps PIN and LOW of Conjecture CORE-2: undecided.
- **Lean**: $`R_2^C`$, isominimal sets, the core, LOC, FRAG and FRAG2 (§3.3).
- The lower-bound program below $`\theta_0`$: no change ($`\iota(\mathrm{CH}_5) \ge \psi_{\Omega_1}(S_*)`$, §2.3). The step below SRO: no change (every $`n`$ on all 3,166 sample matrices; the general statement for
  all standard matrices below SRO is open).

### 3.5 Checks of the fortieth round

Each run was under 60 seconds; none is a proof.

- §3.1. One run: the witness restarts (membership in the domain, normal forms, order below $`X_6`$), 0 failures. The referee ran no search: the weakest steps are pins, transports and counts, which a
  short search cannot test.
- §3.2. Six runs (the corrected value at small codes, the boundary $`\zeta_1`$, the witnesses, the names and the order $`X_{18} \lt X_{19}^\flat \lt X_{19}^{\mathrm{lin}} \lt X_{19}`$), 0 failures. The referee: a search
  over 2,512 normal multipliers in $`[\hat\zeta_3, \zeta_{\mathrm{lin}})`$ with two seeds, 0 counterexamples to the boundary.
- §3.3. Lean (no `#eval`): the bundle of the nine files green, and the two files that import only Mathlib green on their own; the audit rebuilt the bundle (identical) and printed the axioms of
  38 theorems, as claimed. In the repository the nine files build as modules with the whole library (green, no `sorry`).
- The author of §3.1 disclosed one stray shell command (no effect).

### 3.6 Open

- The milestone again, in this order: ENUM-REACH (the corrected value for every code below $`P'`$), its invariance under the transports and its far pin; then CAP-0 below $`P'`$, not-LOW, CAP-1,
  CROSS-LIM, TC⁺$`^\omega`$, EMB, ONTO-FIN, PAIR, UP and $`\nu_C = \nu_S = L(\omega+1)`$; then the frontiers above $`\nu_C`$ ($`X_A`$ to $`Z^\Lambda`$) and the $`R_2^S`$ side; then one level up (Theorems C$`^{\mathrm{LL}}`$,
  C$`^{\mathrm{FP}}`$, $`\nu_3`$).
- The claim above $`X_{21}`$ given FRAG in $`R_2^C`$ (above $`X_4`$ without FRAG), and above $`\upsilon_{\omega^3}`$ in $`R_2^S`$.
- Lean: the link of $`\le_1`$ of $`R_2^C`$ with $`R_1^+`$ (INC1), Carlson 2009, Thm 14.10 and 14.14, that the Lean $`\upsilon`$ is Wilken's; then the blocks below $`\upsilon_{\omega^3}`$, the restart blocks, SKEL⁺, CAP,
  LIFT-0, O$`^C`$ and NU-CT ([LEAN.md](LEAN.md)).
- $`R_2^S = R_2^C`$: (E), $`\beta_0`$ (conjecture: $`\beta_0 \ge x_F^C`$), FAN-LOAD, and the converse for $`\le_1`$ at successor stages above $`\kappa_C`$.
- Bounds for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$, $`f_0`$, $`m_3`$, $`c_0`$, and an upper bound for $`\iota(\mathrm{CH}_3)`$.
- The first inaccessible: chain number 3 past $`\varepsilon_{\Omega_\omega+1}`$; past $`S_*`$, capacities with $`\alpha \ge \Gamma_0`$ (conjecture LEX-SELF) or another way; then the tower of $`\Omega`$'s up to $`\theta_0`$;
  $`\mathrm{CH}_2`$ past $`\Theta_1`$; the step for all standard matrices below SRO.
- Names: $`R(\Theta_{d\omega})`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$; an InaccPsi formula for the reach in terms of the code; the rest of [COVER.md](COVER.md) §9.
